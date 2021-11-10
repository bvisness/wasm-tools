//! This mutator selects a random `if` construction in a function and swap its branches.
//! Since this mutator preserves the original semantic of the input Wasm,
//! before the mutated if structure is encoded, a "negation" of the previous operand
//! in the stack is written. The "negation" is encoded with a `i32.eqz` operator.
use std::{cell::Cell, collections::HashMap, slice::Iter};

use rand::prelude::SliceRandom;
use wasm_encoder::{Function, Instruction, ValType};
use wasmparser::{Operator, TypeOrFuncType};

use crate::{
    module::map_block_type,
    mutators::{
        codemotion::{
            ir::{
                parse_context::{Ast, Node},
                AstWriter,
            },
            AstMutator,
        },
        OperatorAndByteOffset,
    },
};

pub struct LoopUnrollMutator;

#[derive(Default)]
struct LoopUnrollWriter {
    loop_to_mutate: usize,
    mutated: Cell<bool>,
}

impl LoopUnrollWriter {
    fn write_and_fix_loop_body<'a>(
        &self,
        chunk: Iter<OperatorAndByteOffset>,
        to_fix: &HashMap<usize, Instruction>,
        newfunc: &mut Function,
        input_wasm: &'a [u8],
    ) -> crate::Result<()> {
        for (idx, ((_, curr_offset), (_, next_offset))) in
            chunk.clone().zip(chunk.skip(1)).enumerate()
        {
            if to_fix.contains_key(&idx) {
                newfunc.instruction(&to_fix[&idx]);
            } else {
                let piece = &input_wasm[*curr_offset..*next_offset];
                newfunc.raw(piece.to_vec());
            }
        }
        Ok(())
    }

    fn unroll_loop<'a>(
        &self,
        ast: &Ast,
        nodeidx: usize,
        newfunc: &mut Function,
        operators: &Vec<OperatorAndByteOffset>,
        input_wasm: &'a [u8],
    ) -> crate::Result<()> {
        // Do not write as it is
        // Increase the current AST with the custom nodes

        // Create outer block
        self.mutated.set(true);
        let nodes = ast.get_nodes();

        enum State {
            Loop,
            Block,
            If,
            Else,
        }

        let mut current_depth = 0;
        let mut stack = vec![];
        let mut to_fix = HashMap::new();

        match &nodes[nodeidx] {
            Node::Loop { body: _, ty, range } => {
                let chunk = &operators[range.start + 1 /* skip the loop instruction */..range.end];
                newfunc.instruction(&Instruction::Block(map_block_type(*ty)?));
                for (idx, (op, _)) in chunk.iter().enumerate() {
                    match op {
                        Operator::Block { .. } => {
                            stack.push(State::Block);
                            current_depth += 1;
                        }
                        Operator::Loop { .. } => {
                            stack.push(State::Loop);
                            current_depth += 1;
                        }
                        Operator::If { .. } => {
                            stack.push(State::If);
                            current_depth += 1;
                        }
                        Operator::Else { .. } => {
                            stack.pop().expect("Invalid stack state");
                            stack.push(State::Else);
                        }
                        Operator::End { .. } => {
                            let _ = stack.pop().expect("Invalid stack state");
                            current_depth -= 1;
                        }
                        Operator::Br { relative_depth } => {
                            if *relative_depth > current_depth {
                                // Out jump...annotate for fixing
                                to_fix.insert(idx, Instruction::Br(relative_depth + 1));
                            }
                        }
                        Operator::BrIf { relative_depth } => {
                            if *relative_depth > current_depth {
                                // Out jump...annotate for fixing
                                to_fix.insert(idx, Instruction::BrIf(relative_depth + 1));
                            }
                        }
                        Operator::BrTable { table } => {
                            let mut jmpfix = vec![];
                            for i in table.targets() {
                                let d = i?;
                                if d > current_depth {
                                    // Out jump...annotate for fixing
                                    jmpfix.push(d + 1)
                                } else {
                                    jmpfix.push(d)
                                }
                            }

                            let mut def = table.default();
                            if def > current_depth {
                                def += 1;
                            }

                            to_fix.insert(idx, Instruction::BrTable(jmpfix.into(), def));
                        }
                        _ => {}
                    }
                }

                // Write the unroll
                newfunc.instruction(&Instruction::Block(map_block_type(*ty)?));
                // Write A' br B'
                let including_chunk =
                    operators[range.start + 1 /* skip the loop instruction */..range.end + 1]
                        .iter();
                self.write_and_fix_loop_body(including_chunk, &to_fix, newfunc, input_wasm)?;

                // Write A' br B'
                newfunc.instruction(&Instruction::Br(1));
                newfunc.instruction(&Instruction::End);
                // Write the Loop
                newfunc.instruction(&Instruction::Loop(map_block_type(*ty)?));

                // Write A' br B'
                let including_chunk =
                    operators[range.start + 1 /* skip the loop instruction */..range.end + 1]
                        .iter();
                self.write_and_fix_loop_body(including_chunk, &to_fix, newfunc, input_wasm)?;

                // Closing loop
                newfunc.instruction(&Instruction::End);

                // Closing end
                newfunc.instruction(&Instruction::End);
            }
            _ => unreachable!("Invalid node passed as a loop to unroll"),
        }
        Ok(())
    }
}

impl AstWriter for LoopUnrollWriter {
    fn write_loop<'a>(
        &self,
        ast: &Ast,
        nodeidx: usize,
        body: &[usize],
        newfunc: &mut Function,
        operators: &Vec<OperatorAndByteOffset>,
        input_wasm: &'a [u8],
        ty: &wasmparser::TypeOrFuncType,
    ) -> crate::Result<()> {
        if self.loop_to_mutate == nodeidx && !self.mutated.get() {
            self.unroll_loop(ast, nodeidx, newfunc, operators, input_wasm)?;
        } else {
            self.write_loop_default(ast, nodeidx, body, newfunc, operators, input_wasm, ty)?;
        }
        Ok(())
    }
}

impl LoopUnrollMutator {
    pub fn get_empty_returning_loops<'a>(&self, ast: &'a Ast) -> Vec<usize> {
        let nodes = ast.get_nodes();
        let mut loops = vec![];
        for idx in ast.get_loops() {
            let n = &nodes[*idx];
            match n {
                Node::Loop {
                    ty,
                    range: _,
                    body: _,
                } => {
                    if let TypeOrFuncType::Type(wasmparser::Type::EmptyBlockType) = ty {
                        loops.push(*idx)
                    }
                }
                _ => unreachable!("Invalid loop node"),
            }
        }
        loops
    }
}

impl AstMutator for LoopUnrollMutator {
    fn can_mutate<'a>(&self, _: &'a crate::WasmMutate, _: &crate::ModuleInfo, ast: &Ast) -> bool {
        let empty_returning_loops = self.get_empty_returning_loops(ast);
        !empty_returning_loops.is_empty()
    }

    fn mutate<'a>(
        &self,
        _: &'a crate::WasmMutate,
        _: &crate::ModuleInfo,
        rnd: &mut rand::prelude::SmallRng,
        ast: &Ast,
        locals: &[(u32, ValType)],
        operators: &Vec<OperatorAndByteOffset>,
        input_wasm: &'a [u8],
    ) -> crate::Result<Function> {
        // Select the if index
        let mut newfunc = Function::new(locals.to_vec());
        let empty_retuurning_loops = self.get_empty_returning_loops(ast);
        let loop_index = empty_retuurning_loops
            .choose(rnd)
            .expect("This mutator should check first if the AST contains at least one loop node");
        let writer = LoopUnrollWriter {
            loop_to_mutate: *loop_index,
            mutated: Cell::new(false),
        };
        writer.write(ast, ast.get_root(), &mut newfunc, operators, input_wasm)?;
        Ok(newfunc)
    }
}
