use super::{Print, Printer, State};
use anyhow::{anyhow, bail, Result};
use wasmparser::{BlockType, BrTable, Catch, MemArg, Ordering, RefType, TryTable, VisitOperator};

pub struct PrintOperator<'printer, 'state, 'a, 'b> {
    pub(super) printer: &'printer mut Printer<'a, 'b>,
    pub(super) op_offset: usize,
    nesting_start: u32,
    state: &'state mut State,
    label: u32,
    label_indices: Vec<u32>,
    sep: OperatorSeparator,
}

pub enum OperatorSeparator {
    Newline,
    None,
}

impl<'printer, 'state, 'a, 'b> PrintOperator<'printer, 'state, 'a, 'b> {
    pub(super) fn new(
        printer: &'printer mut Printer<'a, 'b>,
        state: &'state mut State,
        sep: OperatorSeparator,
    ) -> Self {
        PrintOperator {
            nesting_start: printer.nesting,
            op_offset: 0,
            printer,
            state,
            label: 0,
            label_indices: Vec::new(),
            sep,
        }
    }

    fn push_str(&mut self, s: &str) -> Result<()> {
        self.printer.result.write_str(s)?;
        Ok(())
    }

    fn result(&mut self) -> &mut dyn Print {
        self.printer.result
    }

    fn separator(&mut self) -> Result<()> {
        match self.sep {
            OperatorSeparator::Newline => self.printer.newline(self.op_offset),
            OperatorSeparator::None => Ok(()),
        }
    }

    /// Called just before an instruction that introduces a block such as
    /// `block`, `if`, `loop`, etc.
    fn block_start(&mut self) -> Result<()> {
        self.separator()?;
        self.printer.nesting += 1;
        self.label_indices.push(self.label);
        Ok(())
    }

    /// Used for `else` and `delegate`
    fn block_mid(&mut self) -> Result<()> {
        self.printer.nesting -= 1;
        self.separator()?;
        self.printer.nesting += 1;
        Ok(())
    }

    /// Used for `end` to terminate the prior block.
    fn block_end(&mut self) -> Result<()> {
        if self.printer.nesting > self.nesting_start {
            self.printer.nesting -= 1;
        }
        self.separator()?;
        Ok(())
    }

    fn blockty(&mut self, ty: BlockType) -> Result<()> {
        let has_name = self.blockty_without_label_comment(ty)?;
        self.maybe_blockty_label_comment(has_name)
    }

    fn blockty_without_label_comment(&mut self, ty: BlockType) -> Result<bool> {
        let key = (self.state.core.funcs, self.label);
        let has_name = match self.state.core.label_names.index_to_name.get(&key) {
            Some(name) => {
                write!(self.printer.result, " ")?;
                name.write(self.printer)?;
                true
            }
            None if self.printer.config.name_unnamed => {
                // Subtract one from the depth here because the label was
                // already pushed onto our stack when the instruction was
                // entered so its own label is one less.
                let depth = self.cur_depth() - 1;
                write!(self.result(), " $#label{depth}")?;
                true
            }
            None => false,
        };
        match ty {
            BlockType::Empty => {}
            BlockType::Type(t) => {
                self.push_str(" ")?;
                self.printer.start_group("result ")?;
                self.printer.print_valtype(self.state, t)?;
                self.printer.end_group()?;
            }
            BlockType::FuncType(idx) => {
                self.push_str(" ")?;
                self.printer
                    .print_core_functype_idx(self.state, idx, None)?;
            }
        }
        Ok(has_name)
    }

    fn maybe_blockty_label_comment(&mut self, has_name: bool) -> Result<()> {
        if !has_name {
            let depth = self.cur_depth();
            self.push_str(" ")?;
            self.result().start_comment()?;
            write!(self.result(), ";; label = @{}", depth)?;
            self.result().reset_color()?;
        }

        self.label += 1;
        Ok(())
    }

    fn cur_depth(&self) -> u32 {
        self.printer.nesting - self.nesting_start
    }

    fn tag_index(&mut self, index: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.tag_names, index)?;
        Ok(())
    }

    fn relative_depth(&mut self, depth: u32) -> Result<()> {
        self.push_str(" ")?;
        match self.cur_depth().checked_sub(depth) {
            // If this relative depth is in-range relative to the current depth,
            // then try to print a name for this label. Label names are tracked
            // as a stack where the depth matches `cur_depth` roughly, but label
            // names don't account for the function name so offset by one more
            // here.
            Some(i) => {
                let name = i
                    .checked_sub(1)
                    .and_then(|idx| self.label_indices.get(idx as usize).copied())
                    .and_then(|label_idx| {
                        let key = (self.state.core.funcs, label_idx);
                        self.state.core.label_names.index_to_name.get(&key)
                    });

                // This is a bit tricky, but if there's a shallower label than
                // this target which shares the same name then we can't print
                // the name-based version. Names resolve to the nearest label
                // in the case of shadowing, which would be the wrong behavior
                // here. All that can be done is to print the index down below
                // instead.
                let name_conflict = name.is_some()
                    && self.label_indices[i as usize..].iter().any(|other_label| {
                        let key = (self.state.core.funcs, *other_label);
                        if let Some(other) = self.state.core.label_names.index_to_name.get(&key) {
                            if name.unwrap().name == other.name {
                                return true;
                            }
                        }
                        false
                    });

                match name {
                    // Only print the name if one is found and there's also no
                    // name conflict.
                    Some(name) if !name_conflict => name.write(self.printer)?,

                    // If there's no name conflict, and we're synthesizing
                    // names, and this isn't targetting the function itself then
                    // print a synthesized names.
                    //
                    // Note that synthesized label names don't handle the
                    // function itself, so i==0, branching to a function label,
                    // is not supported and otherwise labels are offset by 1.
                    None if !name_conflict && self.printer.config.name_unnamed && i > 0 => {
                        self.result().start_name()?;
                        write!(self.result(), "$#label{}", i - 1)?;
                        self.result().reset_color()?;
                    }

                    _ => {
                        // Last-ditch resort, we gotta print the index.
                        self.result().start_name()?;
                        write!(self.result(), "{depth}")?;
                        self.result().reset_color()?;

                        // Unnamed labels have helpful `@N` labels printed for
                        // them so also try to print where this index is going
                        // (label-wise). Don't do this for a name conflict
                        // though because we wouldn't have printed the numbered
                        // label, and also don't do it for the function itself
                        // since the function has no label we can synthesize.
                        if !name_conflict && i > 0 {
                            self.result().start_comment()?;
                            write!(self.result(), " (;@{i};)")?;
                            self.result().reset_color()?;
                        }
                    }
                }
            }

            // This branch is out of range. Print the raw integer and then leave
            // a hopefully-helpful comment indicating that it's going nowhere.
            None => write!(self.result(), "{depth} (; INVALID ;)")?,
        }
        Ok(())
    }

    fn targets(&mut self, targets: BrTable<'_>) -> Result<()> {
        for item in targets.targets().chain([Ok(targets.default())]) {
            self.relative_depth(item?)?;
        }
        Ok(())
    }

    fn function_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.func_names, idx)
    }

    fn local_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer
            .print_local_idx(self.state, self.state.core.funcs, idx)
    }

    fn global_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.global_names, idx)
    }

    fn table_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.table_names, idx)
    }

    fn table(&mut self, idx: u32) -> Result<()> {
        self.table_index(idx)
    }

    fn memory_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.memory_names, idx)
    }

    fn type_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_core_type_ref(self.state, idx)
    }

    fn array_type_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.type_names, idx)
    }

    fn array_type_index_dst(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.type_names, idx)
    }

    fn array_type_index_src(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.type_names, idx)
    }

    fn array_size(&mut self, array_size: u32) -> Result<()> {
        write!(&mut self.printer.result, " {array_size}")?;
        Ok(())
    }

    fn struct_type_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.type_names, idx)
    }

    fn from_ref_type(&mut self, ref_ty: RefType) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_reftype(self.state, ref_ty)
    }

    fn to_ref_type(&mut self, ref_ty: RefType) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_reftype(self.state, ref_ty)
    }

    fn data_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.data_names, idx)
    }

    fn array_data_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.data_names, idx)
    }

    fn elem_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.element_names, idx)
    }

    fn array_elem_index(&mut self, idx: u32) -> Result<()> {
        self.push_str(" ")?;
        self.printer.print_idx(&self.state.core.element_names, idx)
    }

    fn lane(&mut self, lane: u8) -> Result<()> {
        write!(self.result(), " {lane}")?;
        Ok(())
    }

    fn lanes(&mut self, lanes: [u8; 16]) -> Result<()> {
        for lane in lanes.iter() {
            write!(self.result(), " {lane}")?;
        }
        Ok(())
    }

    fn memarg(&mut self, memarg: MemArg) -> Result<()> {
        if memarg.memory != 0 {
            self.memory_index(memarg.memory)?;
        }
        if memarg.offset != 0 {
            write!(self.result(), " offset={}", memarg.offset)?;
        }
        if memarg.align != memarg.max_align {
            if memarg.align >= 32 {
                bail!("alignment in memarg too large");
            }
            let align = 1 << memarg.align;
            write!(self.result(), " align={}", align)?;
        }
        Ok(())
    }

    fn ordering(&mut self, ordering: Ordering) -> Result<()> {
        write!(
            self.result(),
            " {}",
            match ordering {
                Ordering::SeqCst => "seq_cst",
                Ordering::AcqRel => "acq_rel",
            }
        )?;
        Ok(())
    }

    fn try_table(&mut self, table: TryTable) -> Result<()> {
        let has_name = self.blockty_without_label_comment(table.ty)?;

        // Nesting has already been incremented but labels for catch start above
        // this `try_table` not at the `try_table`. Temporarily decrement this
        // nesting count and increase it below after printing catch clauses.
        self.printer.nesting -= 2;
        let try_table_label = self.label_indices.pop().unwrap();

        for catch in table.catches {
            self.result().write_str(" ")?;
            match catch {
                Catch::One { tag, label } => {
                    self.printer.start_group("catch")?;
                    self.tag_index(tag)?;
                    self.relative_depth(label)?;
                    self.printer.end_group()?;
                }
                Catch::OneRef { tag, label } => {
                    self.printer.start_group("catch_ref")?;
                    self.tag_index(tag)?;
                    self.relative_depth(label)?;
                    self.printer.end_group()?;
                }
                Catch::All { label } => {
                    self.printer.start_group("catch_all")?;
                    self.relative_depth(label)?;
                    self.printer.end_group()?;
                }
                Catch::AllRef { label } => {
                    self.printer.start_group("catch_all_ref")?;
                    self.relative_depth(label)?;
                    self.printer.end_group()?;
                }
            }
        }
        self.label_indices.push(try_table_label);
        self.printer.nesting += 2;
        self.maybe_blockty_label_comment(has_name)?;
        Ok(())
    }
}

macro_rules! define_visit {
    // General structure of all the operator printer methods:
    //
    // * Print the name of the insruction as defined in this macro
    // * Print any payload, as necessary
    ($(@$proposal:ident $op:ident $({ $($arg:ident: $argty:ty),* })? => $visit:ident )*) => ($(
        fn $visit(&mut self $( , $($arg: $argty),* )?) -> Self::Output {
            define_visit!(before_op self $op);
            self.push_str(operator_name!($op))?;
            $(
                define_visit!(payload self $op $($arg)*);
            )?

            define_visit!(after_op self $op);
            Ok(())
        }
    )*);

    // Control-flow related opcodes have special handling to manage nested
    // depth as well as the stack of labels.
    //
    // The catch-all for "before an op" is "print an newline"
    (before_op $self:ident Loop) => ($self.block_start()?;);
    (before_op $self:ident Block) => ($self.block_start()?;);
    (before_op $self:ident If) => ($self.block_start()?;);
    (before_op $self:ident Try) => ($self.block_start()?;);
    (before_op $self:ident TryTable) => ($self.block_start()?;);
    (before_op $self:ident Catch) => ($self.block_mid()?;);
    (before_op $self:ident CatchAll) => ($self.block_mid()?;);
    (before_op $self:ident Delegate) => ($self.block_end()?;);
    (before_op $self:ident Else) => ($self.block_mid()?;);
    (before_op $self:ident End) => ($self.block_end()?;);
    (before_op $self:ident $op:ident) => ($self.separator()?;);

    // After some opcodes the label stack is popped.
    // (after_op $self:ident Delegate) => ($self.label_indices.pop(););
    (after_op $self:ident End) => ($self.label_indices.pop(););
    (after_op $self:ident $op:ident) => ();

    // How to print the payload of an instruction. There are a number of
    // instructions that have special cases such as avoiding printing anything
    // when an index is 0 or similar. The final case in this list is the
    // catch-all which prints each payload individually based on the name of the
    // payload field.
    (payload $self:ident CallIndirect $ty:ident $table:ident) => (
        if $table != 0 {
            $self.table_index($table)?;
        }
        $self.type_index($ty)?;
    );
    (payload $self:ident ReturnCallIndirect $ty:ident $table:ident) => (
        if $table != 0 {
            $self.table_index($table)?;
        }
        $self.type_index($ty)?;
    );
    (payload $self:ident CallRef $ty:ident) => (
        $self.push_str(" ")?;
        $self.printer.print_idx(&$self.state.core.type_names, $ty)?;
    );
    (payload $self:ident ReturnCallRef $ty:ident) => (
        $self.push_str(" ")?;
        $self.printer.print_idx(&$self.state.core.type_names, $ty)?;
    );
    (payload $self:ident TypedSelect $ty:ident) => (
        $self.push_str(" ")?;
        $self.printer.start_group("result ")?;
        $self.printer.print_valtype($self.state, $ty)?;
        $self.printer.end_group()?;
    );
    (payload $self:ident RefNull $hty:ident) => (
        $self.push_str(" ")?;
        $self.printer.print_heaptype($self.state, $hty)?;
    );
    (payload $self:ident TableInit $segment:ident $table:ident) => (
        if $table != 0 {
            $self.table_index($table)?;
        }
        $self.elem_index($segment)?;
    );
    (payload $self:ident TableCopy $dst:ident $src:ident) => (
        if $src != 0 || $dst != 0 {
            $self.table_index($dst)?;
            $self.table_index($src)?;
        }
    );
    (payload $self:ident MemoryGrow $mem:ident) => (
        if $mem != 0 {
            $self.memory_index($mem)?;
        }
    );
    (payload $self:ident MemorySize $mem:ident) => (
        if $mem != 0 {
            $self.memory_index($mem)?;
        }
    );
    (payload $self:ident MemoryInit $segment:ident $mem:ident) => (
        if $mem != 0 {
            $self.memory_index($mem)?;
        }
        $self.data_index($segment)?;
    );
    (payload $self:ident MemoryCopy $dst:ident $src:ident) => (
        if $src != 0 || $dst != 0 {
            $self.memory_index($dst)?;
            $self.memory_index($src)?;
        }
    );
    (payload $self:ident MemoryFill $mem:ident) => (
        if $mem != 0 {
            $self.memory_index($mem)?;
        }
    );
    (payload $self:ident MemoryDiscard $mem:ident) => (
        if $mem != 0 {
            $self.memory_index($mem)?;
        }
    );
    (payload $self:ident I32Const $val:ident) => (
        $self.result().start_literal()?;
        write!($self.result(), " {}", $val)?;
        $self.result().reset_color()?;
    );
    (payload $self:ident I64Const $val:ident) => (
        $self.result().start_literal()?;
        write!($self.result(), " {}", $val)?;
        $self.result().reset_color()?;
    );
    (payload $self:ident F32Const $val:ident) => (
        $self.push_str(" ")?;
        $self.printer.print_f32($val.bits())?;
    );
    (payload $self:ident F64Const $val:ident) => (
        $self.push_str(" ")?;
        $self.printer.print_f64($val.bits())?;
    );
    (payload $self:ident V128Const $val:ident) => (
        $self.printer.print_type_keyword(" i32x4")?;
        $self.result().start_literal()?;
        for chunk in $val.bytes().chunks(4) {
            write!(
                $self.result(),
                " 0x{:02x}{:02x}{:02x}{:02x}",
                chunk[3],
                chunk[2],
                chunk[1],
                chunk[0],
            )?;
        }
        $self.result().reset_color()?;
    );
    (payload $self:ident RefTestNonNull $hty:ident) => (
        $self.push_str(" ")?;
        let rty = RefType::new(false, $hty)
            .ok_or_else(|| anyhow!("implementation limit: type index too large"))?;
        $self.printer.print_reftype($self.state, rty)?;
    );
    (payload $self:ident RefTestNullable $hty:ident) => (
        $self.push_str(" ")?;
        let rty = RefType::new(true, $hty)
            .ok_or_else(|| anyhow!("implementation limit: type index too large"))?;
        $self.printer.print_reftype($self.state, rty)?;
    );
    (payload $self:ident RefCastNonNull $hty:ident) => (
        $self.push_str(" ")?;
        let rty = RefType::new(false, $hty)
            .ok_or_else(|| anyhow!("implementation limit: type index too large"))?;
        $self.printer.print_reftype($self.state, rty)?;
    );
    (payload $self:ident RefCastNullable $hty:ident) => (
        $self.push_str(" ")?;
        let rty = RefType::new(true, $hty)
            .ok_or_else(|| anyhow!("implementation limit: type index too large"))?;
        $self.printer.print_reftype($self.state, rty)?;
    );
    (payload $self:ident StructGet $ty:ident $field:ident) => (
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructGetS $ty:ident $field:ident) => (
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructGetU $ty:ident $field:ident) => (
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructSet $ty:ident $field:ident) => (
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicGet $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicGetS $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicGetU $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicSet $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicSet $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwAdd $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwSub $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwAnd $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwOr $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwXor $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwXchg $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident StructAtomicRmwCmpxchg $order:ident $ty:ident $field:ident) => (
        $self.ordering($order)?;
        $self.struct_type_index($ty)?;
        $self.push_str(" ")?;
        $self.printer.print_field_idx($self.state, $ty, $field)?;
    );
    (payload $self:ident $op:ident $($arg:ident)*) => (
        $($self.$arg($arg)?;)*
    );
}

/// TODO: DOCS
#[macro_export]
macro_rules! operator_name {
    (Block) => ("block");
    (If) => ("if");
    (Else) => ("else");
    (Loop) => ("loop");
    (End) => ("end");
    (Unreachable) => ("unreachable");
    (Nop) => ("nop");
    (Br) => ("br");
    (BrIf) => ("br_if");
    (BrOnNull) => ("br_on_null");
    (BrOnNonNull) => ("br_on_non_null");
    (BrTable) => ("br_table");
    (Return) => ("return");
    (Call) => ("call");
    (CallIndirect) => ("call_indirect");
    (CallRef) => ("call_ref");
    (ReturnCall) => ("return_call");
    (ReturnCallIndirect) => ("return_call_indirect");
    (ReturnCallRef) => ("return_call_ref");
    (Drop) => ("drop");
    (Select) => ("select");
    (TypedSelect) => ("select");
    (LocalGet) => ("local.get");
    (LocalSet) => ("local.set");
    (LocalTee) => ("local.tee");
    (GlobalGet) => ("global.get");
    (GlobalSet) => ("global.set");
    (TableGet) => ("table.get");
    (TableSet) => ("table.set");
    (I32Load) => ("i32.load");
    (I64Load) => ("i64.load");
    (F32Load) => ("f32.load");
    (F64Load) => ("f64.load");
    (I32Load8S) => ("i32.load8_s");
    (I32Load8U) => ("i32.load8_u");
    (I32Load16S) => ("i32.load16_s");
    (I32Load16U) => ("i32.load16_u");
    (I64Load8S) => ("i64.load8_s");
    (I64Load8U) => ("i64.load8_u");
    (I64Load16S) => ("i64.load16_s");
    (I64Load16U) => ("i64.load16_u");
    (I64Load32S) => ("i64.load32_s");
    (I64Load32U) => ("i64.load32_u");
    (I32Store) => ("i32.store");
    (I64Store) => ("i64.store");
    (F32Store) => ("f32.store");
    (F64Store) => ("f64.store");
    (I32Store8) => ("i32.store8");
    (I32Store16) => ("i32.store16");
    (I64Store8) => ("i64.store8");
    (I64Store16) => ("i64.store16");
    (I64Store32) => ("i64.store32");
    (MemorySize) => ("memory.size");
    (MemoryGrow) => ("memory.grow");
    (MemoryInit) => ("memory.init");
    (MemoryCopy) => ("memory.copy");
    (MemoryFill) => ("memory.fill");
    (MemoryDiscard) => ("memory.discard");
    (DataDrop) => ("data.drop");
    (ElemDrop) => ("elem.drop");
    (TableInit) => ("table.init");
    (TableCopy) => ("table.copy");
    (TableFill) => ("table.fill");
    (TableSize) => ("table.size");
    (TableGrow) => ("table.grow");
    (RefAsNonNull) => ("ref.as_non_null");
    (RefNull) => ("ref.null");
    (RefEq) => ("ref.eq");
    (RefIsNull) => ("ref.is_null");
    (RefFunc) => ("ref.func");
    (I32Const) => ("i32.const");
    (I64Const) => ("i64.const");
    (F32Const) => ("f32.const");
    (F64Const) => ("f64.const");
    (I32Clz) => ("i32.clz");
    (I32Ctz) => ("i32.ctz");
    (I32Popcnt) => ("i32.popcnt");
    (I32Add) => ("i32.add");
    (I32Sub) => ("i32.sub");
    (I32Mul) => ("i32.mul");
    (I32DivS) => ("i32.div_s");
    (I32DivU) => ("i32.div_u");
    (I32RemS) => ("i32.rem_s");
    (I32RemU) => ("i32.rem_u");
    (I32And) => ("i32.and");
    (I32Or) => ("i32.or");
    (I32Xor) => ("i32.xor");
    (I32Shl) => ("i32.shl");
    (I32ShrS) => ("i32.shr_s");
    (I32ShrU) => ("i32.shr_u");
    (I32Rotl) => ("i32.rotl");
    (I32Rotr) => ("i32.rotr");
    (I64Clz) => ("i64.clz");
    (I64Ctz) => ("i64.ctz");
    (I64Popcnt) => ("i64.popcnt");
    (I64Add) => ("i64.add");
    (I64Sub) => ("i64.sub");
    (I64Mul) => ("i64.mul");
    (I64DivS) => ("i64.div_s");
    (I64DivU) => ("i64.div_u");
    (I64RemS) => ("i64.rem_s");
    (I64RemU) => ("i64.rem_u");
    (I64And) => ("i64.and");
    (I64Or) => ("i64.or");
    (I64Xor) => ("i64.xor");
    (I64Shl) => ("i64.shl");
    (I64ShrS) => ("i64.shr_s");
    (I64ShrU) => ("i64.shr_u");
    (I64Rotl) => ("i64.rotl");
    (I64Rotr) => ("i64.rotr");
    (F32Abs) => ("f32.abs");
    (F32Neg) => ("f32.neg");
    (F32Ceil) => ("f32.ceil");
    (F32Floor) => ("f32.floor");
    (F32Trunc) => ("f32.trunc");
    (F32Nearest) => ("f32.nearest");
    (F32Sqrt) => ("f32.sqrt");
    (F32Add) => ("f32.add");
    (F32Sub) => ("f32.sub");
    (F32Mul) => ("f32.mul");
    (F32Div) => ("f32.div");
    (F32Min) => ("f32.min");
    (F32Max) => ("f32.max");
    (F32Copysign) => ("f32.copysign");
    (F64Abs) => ("f64.abs");
    (F64Neg) => ("f64.neg");
    (F64Ceil) => ("f64.ceil");
    (F64Floor) => ("f64.floor");
    (F64Trunc) => ("f64.trunc");
    (F64Nearest) => ("f64.nearest");
    (F64Sqrt) => ("f64.sqrt");
    (F64Add) => ("f64.add");
    (F64Sub) => ("f64.sub");
    (F64Mul) => ("f64.mul");
    (F64Div) => ("f64.div");
    (F64Min) => ("f64.min");
    (F64Max) => ("f64.max");
    (F64Copysign) => ("f64.copysign");
    (I32Eqz) => ("i32.eqz");
    (I32Eq) => ("i32.eq");
    (I32Ne) => ("i32.ne");
    (I32LtS) => ("i32.lt_s");
    (I32LtU) => ("i32.lt_u");
    (I32GtS) => ("i32.gt_s");
    (I32GtU) => ("i32.gt_u");
    (I32LeS) => ("i32.le_s");
    (I32LeU) => ("i32.le_u");
    (I32GeS) => ("i32.ge_s");
    (I32GeU) => ("i32.ge_u");
    (I64Eqz) => ("i64.eqz");
    (I64Eq) => ("i64.eq");
    (I64Ne) => ("i64.ne");
    (I64LtS) => ("i64.lt_s");
    (I64LtU) => ("i64.lt_u");
    (I64GtS) => ("i64.gt_s");
    (I64GtU) => ("i64.gt_u");
    (I64LeS) => ("i64.le_s");
    (I64LeU) => ("i64.le_u");
    (I64GeS) => ("i64.ge_s");
    (I64GeU) => ("i64.ge_u");
    (F32Eq) => ("f32.eq");
    (F32Ne) => ("f32.ne");
    (F32Lt) => ("f32.lt");
    (F32Gt) => ("f32.gt");
    (F32Le) => ("f32.le");
    (F32Ge) => ("f32.ge");
    (F64Eq) => ("f64.eq");
    (F64Ne) => ("f64.ne");
    (F64Lt) => ("f64.lt");
    (F64Gt) => ("f64.gt");
    (F64Le) => ("f64.le");
    (F64Ge) => ("f64.ge");
    (I32WrapI64) => ("i32.wrap_i64");
    (I32TruncF32S) => ("i32.trunc_f32_s");
    (I32TruncF32U) => ("i32.trunc_f32_u");
    (I32TruncF64S) => ("i32.trunc_f64_s");
    (I32TruncF64U) => ("i32.trunc_f64_u");
    (I64ExtendI32S) => ("i64.extend_i32_s");
    (I64ExtendI32U) => ("i64.extend_i32_u");
    (I64TruncF32S) => ("i64.trunc_f32_s");
    (I64TruncF32U) => ("i64.trunc_f32_u");
    (I64TruncF64S) => ("i64.trunc_f64_s");
    (I64TruncF64U) => ("i64.trunc_f64_u");
    (F32ConvertI32S) => ("f32.convert_i32_s");
    (F32ConvertI32U) => ("f32.convert_i32_u");
    (F32ConvertI64S) => ("f32.convert_i64_s");
    (F32ConvertI64U) => ("f32.convert_i64_u");
    (F32DemoteF64) => ("f32.demote_f64");
    (F64ConvertI32S) => ("f64.convert_i32_s");
    (F64ConvertI32U) => ("f64.convert_i32_u");
    (F64ConvertI64S) => ("f64.convert_i64_s");
    (F64ConvertI64U) => ("f64.convert_i64_u");
    (F64PromoteF32) => ("f64.promote_f32");
    (I32ReinterpretF32) => ("i32.reinterpret_f32");
    (I64ReinterpretF64) => ("i64.reinterpret_f64");
    (F32ReinterpretI32) => ("f32.reinterpret_i32");
    (F64ReinterpretI64) => ("f64.reinterpret_i64");
    (I32TruncSatF32S) => ("i32.trunc_sat_f32_s");
    (I32TruncSatF32U) => ("i32.trunc_sat_f32_u");
    (I32TruncSatF64S) => ("i32.trunc_sat_f64_s");
    (I32TruncSatF64U) => ("i32.trunc_sat_f64_u");
    (I64TruncSatF32S) => ("i64.trunc_sat_f32_s");
    (I64TruncSatF32U) => ("i64.trunc_sat_f32_u");
    (I64TruncSatF64S) => ("i64.trunc_sat_f64_s");
    (I64TruncSatF64U) => ("i64.trunc_sat_f64_u");
    (I32Extend8S) => ("i32.extend8_s");
    (I32Extend16S) => ("i32.extend16_s");
    (I64Extend8S) => ("i64.extend8_s");
    (I64Extend16S) => ("i64.extend16_s");
    (I64Extend32S) => ("i64.extend32_s");
    (MemoryAtomicNotify) => ("memory.atomic.notify");
    (MemoryAtomicWait32) => ("memory.atomic.wait32");
    (MemoryAtomicWait64) => ("memory.atomic.wait64");
    (AtomicFence) => ("atomic.fence");
    (I32AtomicLoad) => ("i32.atomic.load");
    (I64AtomicLoad) => ("i64.atomic.load");
    (I32AtomicLoad8U) => ("i32.atomic.load8_u");
    (I32AtomicLoad16U) => ("i32.atomic.load16_u");
    (I64AtomicLoad8U) => ("i64.atomic.load8_u");
    (I64AtomicLoad16U) => ("i64.atomic.load16_u");
    (I64AtomicLoad32U) => ("i64.atomic.load32_u");
    (I32AtomicStore) => ("i32.atomic.store");
    (I64AtomicStore) => ("i64.atomic.store");
    (I32AtomicStore8) => ("i32.atomic.store8");
    (I32AtomicStore16) => ("i32.atomic.store16");
    (I64AtomicStore8) => ("i64.atomic.store8");
    (I64AtomicStore16) => ("i64.atomic.store16");
    (I64AtomicStore32) => ("i64.atomic.store32");
    (I32AtomicRmwAdd) => ("i32.atomic.rmw.add");
    (I64AtomicRmwAdd) => ("i64.atomic.rmw.add");
    (I32AtomicRmw8AddU) => ("i32.atomic.rmw8.add_u");
    (I32AtomicRmw16AddU) => ("i32.atomic.rmw16.add_u");
    (I64AtomicRmw8AddU) => ("i64.atomic.rmw8.add_u");
    (I64AtomicRmw16AddU) => ("i64.atomic.rmw16.add_u");
    (I64AtomicRmw32AddU) => ("i64.atomic.rmw32.add_u");
    (I32AtomicRmwSub) => ("i32.atomic.rmw.sub");
    (I64AtomicRmwSub) => ("i64.atomic.rmw.sub");
    (I32AtomicRmw8SubU) => ("i32.atomic.rmw8.sub_u");
    (I32AtomicRmw16SubU) => ("i32.atomic.rmw16.sub_u");
    (I64AtomicRmw8SubU) => ("i64.atomic.rmw8.sub_u");
    (I64AtomicRmw16SubU) => ("i64.atomic.rmw16.sub_u");
    (I64AtomicRmw32SubU) => ("i64.atomic.rmw32.sub_u");
    (I32AtomicRmwAnd) => ("i32.atomic.rmw.and");
    (I64AtomicRmwAnd) => ("i64.atomic.rmw.and");
    (I32AtomicRmw8AndU) => ("i32.atomic.rmw8.and_u");
    (I32AtomicRmw16AndU) => ("i32.atomic.rmw16.and_u");
    (I64AtomicRmw8AndU) => ("i64.atomic.rmw8.and_u");
    (I64AtomicRmw16AndU) => ("i64.atomic.rmw16.and_u");
    (I64AtomicRmw32AndU) => ("i64.atomic.rmw32.and_u");
    (I32AtomicRmwOr) => ("i32.atomic.rmw.or");
    (I64AtomicRmwOr) => ("i64.atomic.rmw.or");
    (I32AtomicRmw8OrU) => ("i32.atomic.rmw8.or_u");
    (I32AtomicRmw16OrU) => ("i32.atomic.rmw16.or_u");
    (I64AtomicRmw8OrU) => ("i64.atomic.rmw8.or_u");
    (I64AtomicRmw16OrU) => ("i64.atomic.rmw16.or_u");
    (I64AtomicRmw32OrU) => ("i64.atomic.rmw32.or_u");
    (I32AtomicRmwXor) => ("i32.atomic.rmw.xor");
    (I64AtomicRmwXor) => ("i64.atomic.rmw.xor");
    (I32AtomicRmw8XorU) => ("i32.atomic.rmw8.xor_u");
    (I32AtomicRmw16XorU) => ("i32.atomic.rmw16.xor_u");
    (I64AtomicRmw8XorU) => ("i64.atomic.rmw8.xor_u");
    (I64AtomicRmw16XorU) => ("i64.atomic.rmw16.xor_u");
    (I64AtomicRmw32XorU) => ("i64.atomic.rmw32.xor_u");
    (I32AtomicRmwXchg) => ("i32.atomic.rmw.xchg");
    (I64AtomicRmwXchg) => ("i64.atomic.rmw.xchg");
    (I32AtomicRmw8XchgU) => ("i32.atomic.rmw8.xchg_u");
    (I32AtomicRmw16XchgU) => ("i32.atomic.rmw16.xchg_u");
    (I64AtomicRmw8XchgU) => ("i64.atomic.rmw8.xchg_u");
    (I64AtomicRmw16XchgU) => ("i64.atomic.rmw16.xchg_u");
    (I64AtomicRmw32XchgU) => ("i64.atomic.rmw32.xchg_u");
    (I32AtomicRmwCmpxchg) => ("i32.atomic.rmw.cmpxchg");
    (I64AtomicRmwCmpxchg) => ("i64.atomic.rmw.cmpxchg");
    (I32AtomicRmw8CmpxchgU) => ("i32.atomic.rmw8.cmpxchg_u");
    (I32AtomicRmw16CmpxchgU) => ("i32.atomic.rmw16.cmpxchg_u");
    (I64AtomicRmw8CmpxchgU) => ("i64.atomic.rmw8.cmpxchg_u");
    (I64AtomicRmw16CmpxchgU) => ("i64.atomic.rmw16.cmpxchg_u");
    (I64AtomicRmw32CmpxchgU) => ("i64.atomic.rmw32.cmpxchg_u");
    (V128Load) => ("v128.load");
    (V128Load8x8S) => ("v128.load8x8_s");
    (V128Load8x8U) => ("v128.load8x8_u");
    (V128Load16x4S) => ("v128.load16x4_s");
    (V128Load16x4U) => ("v128.load16x4_u");
    (V128Load32x2S) => ("v128.load32x2_s");
    (V128Load32x2U) => ("v128.load32x2_u");
    (V128Load8Splat) => ("v128.load8_splat");
    (V128Load16Splat) => ("v128.load16_splat");
    (V128Load32Splat) => ("v128.load32_splat");
    (V128Load64Splat) => ("v128.load64_splat");
    (V128Load32Zero) => ("v128.load32_zero");
    (V128Load64Zero) => ("v128.load64_zero");
    (V128Store) => ("v128.store");
    (V128Load8Lane) => ("v128.load8_lane");
    (V128Load16Lane) => ("v128.load16_lane");
    (V128Load32Lane) => ("v128.load32_lane");
    (V128Load64Lane) => ("v128.load64_lane");
    (V128Store8Lane) => ("v128.store8_lane");
    (V128Store16Lane) => ("v128.store16_lane");
    (V128Store32Lane) => ("v128.store32_lane");
    (V128Store64Lane) => ("v128.store64_lane");
    (V128Const) => ("v128.const");
    (I8x16Shuffle) => ("i8x16.shuffle");
    (I8x16ExtractLaneS) => ("i8x16.extract_lane_s");
    (I8x16ExtractLaneU) => ("i8x16.extract_lane_u");
    (I8x16ReplaceLane) => ("i8x16.replace_lane");
    (I16x8ExtractLaneS) => ("i16x8.extract_lane_s");
    (I16x8ExtractLaneU) => ("i16x8.extract_lane_u");
    (I16x8ReplaceLane) => ("i16x8.replace_lane");
    (I32x4ExtractLane) => ("i32x4.extract_lane");
    (I32x4ReplaceLane) => ("i32x4.replace_lane");
    (I64x2ExtractLane) => ("i64x2.extract_lane");
    (I64x2ReplaceLane) => ("i64x2.replace_lane");
    (F32x4ExtractLane) => ("f32x4.extract_lane");
    (F32x4ReplaceLane) => ("f32x4.replace_lane");
    (F64x2ExtractLane) => ("f64x2.extract_lane");
    (F64x2ReplaceLane) => ("f64x2.replace_lane");
    (I8x16Swizzle) => ("i8x16.swizzle");
    (I8x16Splat) => ("i8x16.splat");
    (I16x8Splat) => ("i16x8.splat");
    (I32x4Splat) => ("i32x4.splat");
    (I64x2Splat) => ("i64x2.splat");
    (F32x4Splat) => ("f32x4.splat");
    (F64x2Splat) => ("f64x2.splat");
    (I8x16Eq) => ("i8x16.eq");
    (I8x16Ne) => ("i8x16.ne");
    (I8x16LtS) => ("i8x16.lt_s");
    (I8x16LtU) => ("i8x16.lt_u");
    (I8x16GtS) => ("i8x16.gt_s");
    (I8x16GtU) => ("i8x16.gt_u");
    (I8x16LeS) => ("i8x16.le_s");
    (I8x16LeU) => ("i8x16.le_u");
    (I8x16GeS) => ("i8x16.ge_s");
    (I8x16GeU) => ("i8x16.ge_u");
    (I16x8Eq) => ("i16x8.eq");
    (I16x8Ne) => ("i16x8.ne");
    (I16x8LtS) => ("i16x8.lt_s");
    (I16x8LtU) => ("i16x8.lt_u");
    (I16x8GtS) => ("i16x8.gt_s");
    (I16x8GtU) => ("i16x8.gt_u");
    (I16x8LeS) => ("i16x8.le_s");
    (I16x8LeU) => ("i16x8.le_u");
    (I16x8GeS) => ("i16x8.ge_s");
    (I16x8GeU) => ("i16x8.ge_u");
    (I32x4Eq) => ("i32x4.eq");
    (I32x4Ne) => ("i32x4.ne");
    (I32x4LtS) => ("i32x4.lt_s");
    (I32x4LtU) => ("i32x4.lt_u");
    (I32x4GtS) => ("i32x4.gt_s");
    (I32x4GtU) => ("i32x4.gt_u");
    (I32x4LeS) => ("i32x4.le_s");
    (I32x4LeU) => ("i32x4.le_u");
    (I32x4GeS) => ("i32x4.ge_s");
    (I32x4GeU) => ("i32x4.ge_u");
    (I64x2Eq) => ("i64x2.eq");
    (I64x2Ne) => ("i64x2.ne");
    (I64x2LtS) => ("i64x2.lt_s");
    (I64x2GtS) => ("i64x2.gt_s");
    (I64x2LeS) => ("i64x2.le_s");
    (I64x2GeS) => ("i64x2.ge_s");
    (F32x4Eq) => ("f32x4.eq");
    (F32x4Ne) => ("f32x4.ne");
    (F32x4Lt) => ("f32x4.lt");
    (F32x4Gt) => ("f32x4.gt");
    (F32x4Le) => ("f32x4.le");
    (F32x4Ge) => ("f32x4.ge");
    (F64x2Eq) => ("f64x2.eq");
    (F64x2Ne) => ("f64x2.ne");
    (F64x2Lt) => ("f64x2.lt");
    (F64x2Gt) => ("f64x2.gt");
    (F64x2Le) => ("f64x2.le");
    (F64x2Ge) => ("f64x2.ge");
    (V128Not) => ("v128.not");
    (V128And) => ("v128.and");
    (V128AndNot) => ("v128.andnot");
    (V128Or) => ("v128.or");
    (V128Xor) => ("v128.xor");
    (V128Bitselect) => ("v128.bitselect");
    (V128AnyTrue) => ("v128.any_true");
    (I8x16Abs) => ("i8x16.abs");
    (I8x16Neg) => ("i8x16.neg");
    (I8x16Popcnt) => ("i8x16.popcnt");
    (I8x16AllTrue) => ("i8x16.all_true");
    (I8x16Bitmask) => ("i8x16.bitmask");
    (I8x16NarrowI16x8S) => ("i8x16.narrow_i16x8_s");
    (I8x16NarrowI16x8U) => ("i8x16.narrow_i16x8_u");
    (I8x16Shl) => ("i8x16.shl");
    (I8x16ShrS) => ("i8x16.shr_s");
    (I8x16ShrU) => ("i8x16.shr_u");
    (I8x16Add) => ("i8x16.add");
    (I8x16AddSatS) => ("i8x16.add_sat_s");
    (I8x16AddSatU) => ("i8x16.add_sat_u");
    (I8x16Sub) => ("i8x16.sub");
    (I8x16SubSatS) => ("i8x16.sub_sat_s");
    (I8x16SubSatU) => ("i8x16.sub_sat_u");
    (I8x16MinS) => ("i8x16.min_s");
    (I8x16MinU) => ("i8x16.min_u");
    (I8x16MaxS) => ("i8x16.max_s");
    (I8x16MaxU) => ("i8x16.max_u");
    (I8x16AvgrU) => ("i8x16.avgr_u");
    (I16x8ExtAddPairwiseI8x16S) => ("i16x8.extadd_pairwise_i8x16_s");
    (I16x8ExtAddPairwiseI8x16U) => ("i16x8.extadd_pairwise_i8x16_u");
    (I16x8Abs) => ("i16x8.abs");
    (I16x8Neg) => ("i16x8.neg");
    (I16x8Q15MulrSatS) => ("i16x8.q15mulr_sat_s");
    (I16x8AllTrue) => ("i16x8.all_true");
    (I16x8Bitmask) => ("i16x8.bitmask");
    (I16x8NarrowI32x4S) => ("i16x8.narrow_i32x4_s");
    (I16x8NarrowI32x4U) => ("i16x8.narrow_i32x4_u");
    (I16x8ExtendLowI8x16S) => ("i16x8.extend_low_i8x16_s");
    (I16x8ExtendHighI8x16S) => ("i16x8.extend_high_i8x16_s");
    (I16x8ExtendLowI8x16U) => ("i16x8.extend_low_i8x16_u");
    (I16x8ExtendHighI8x16U) => ("i16x8.extend_high_i8x16_u");
    (I16x8Shl) => ("i16x8.shl");
    (I16x8ShrS) => ("i16x8.shr_s");
    (I16x8ShrU) => ("i16x8.shr_u");
    (I16x8Add) => ("i16x8.add");
    (I16x8AddSatS) => ("i16x8.add_sat_s");
    (I16x8AddSatU) => ("i16x8.add_sat_u");
    (I16x8Sub) => ("i16x8.sub");
    (I16x8SubSatS) => ("i16x8.sub_sat_s");
    (I16x8SubSatU) => ("i16x8.sub_sat_u");
    (I16x8Mul) => ("i16x8.mul");
    (I16x8MinS) => ("i16x8.min_s");
    (I16x8MinU) => ("i16x8.min_u");
    (I16x8MaxS) => ("i16x8.max_s");
    (I16x8MaxU) => ("i16x8.max_u");
    (I16x8AvgrU) => ("i16x8.avgr_u");
    (I16x8ExtMulLowI8x16S) => ("i16x8.extmul_low_i8x16_s");
    (I16x8ExtMulHighI8x16S) => ("i16x8.extmul_high_i8x16_s");
    (I16x8ExtMulLowI8x16U) => ("i16x8.extmul_low_i8x16_u");
    (I16x8ExtMulHighI8x16U) => ("i16x8.extmul_high_i8x16_u");
    (I32x4ExtAddPairwiseI16x8S) => ("i32x4.extadd_pairwise_i16x8_s");
    (I32x4ExtAddPairwiseI16x8U) => ("i32x4.extadd_pairwise_i16x8_u");
    (I32x4Abs) => ("i32x4.abs");
    (I32x4Neg) => ("i32x4.neg");
    (I32x4AllTrue) => ("i32x4.all_true");
    (I32x4Bitmask) => ("i32x4.bitmask");
    (I32x4ExtendLowI16x8S) => ("i32x4.extend_low_i16x8_s");
    (I32x4ExtendHighI16x8S) => ("i32x4.extend_high_i16x8_s");
    (I32x4ExtendLowI16x8U) => ("i32x4.extend_low_i16x8_u");
    (I32x4ExtendHighI16x8U) => ("i32x4.extend_high_i16x8_u");
    (I32x4Shl) => ("i32x4.shl");
    (I32x4ShrS) => ("i32x4.shr_s");
    (I32x4ShrU) => ("i32x4.shr_u");
    (I32x4Add) => ("i32x4.add");
    (I32x4Sub) => ("i32x4.sub");
    (I32x4Mul) => ("i32x4.mul");
    (I32x4MinS) => ("i32x4.min_s");
    (I32x4MinU) => ("i32x4.min_u");
    (I32x4MaxS) => ("i32x4.max_s");
    (I32x4MaxU) => ("i32x4.max_u");
    (I32x4DotI16x8S) => ("i32x4.dot_i16x8_s");
    (I32x4ExtMulLowI16x8S) => ("i32x4.extmul_low_i16x8_s");
    (I32x4ExtMulHighI16x8S) => ("i32x4.extmul_high_i16x8_s");
    (I32x4ExtMulLowI16x8U) => ("i32x4.extmul_low_i16x8_u");
    (I32x4ExtMulHighI16x8U) => ("i32x4.extmul_high_i16x8_u");
    (I64x2Abs) => ("i64x2.abs");
    (I64x2Neg) => ("i64x2.neg");
    (I64x2AllTrue) => ("i64x2.all_true");
    (I64x2Bitmask) => ("i64x2.bitmask");
    (I64x2ExtendLowI32x4S) => ("i64x2.extend_low_i32x4_s");
    (I64x2ExtendHighI32x4S) => ("i64x2.extend_high_i32x4_s");
    (I64x2ExtendLowI32x4U) => ("i64x2.extend_low_i32x4_u");
    (I64x2ExtendHighI32x4U) => ("i64x2.extend_high_i32x4_u");
    (I64x2Shl) => ("i64x2.shl");
    (I64x2ShrS) => ("i64x2.shr_s");
    (I64x2ShrU) => ("i64x2.shr_u");
    (I64x2Add) => ("i64x2.add");
    (I64x2Sub) => ("i64x2.sub");
    (I64x2Mul) => ("i64x2.mul");
    (I64x2ExtMulLowI32x4S) => ("i64x2.extmul_low_i32x4_s");
    (I64x2ExtMulHighI32x4S) => ("i64x2.extmul_high_i32x4_s");
    (I64x2ExtMulLowI32x4U) => ("i64x2.extmul_low_i32x4_u");
    (I64x2ExtMulHighI32x4U) => ("i64x2.extmul_high_i32x4_u");
    (F32x4Ceil) => ("f32x4.ceil");
    (F32x4Floor) => ("f32x4.floor");
    (F32x4Trunc) => ("f32x4.trunc");
    (F32x4Nearest) => ("f32x4.nearest");
    (F32x4Abs) => ("f32x4.abs");
    (F32x4Neg) => ("f32x4.neg");
    (F32x4Sqrt) => ("f32x4.sqrt");
    (F32x4Add) => ("f32x4.add");
    (F32x4Sub) => ("f32x4.sub");
    (F32x4Mul) => ("f32x4.mul");
    (F32x4Div) => ("f32x4.div");
    (F32x4Min) => ("f32x4.min");
    (F32x4Max) => ("f32x4.max");
    (F32x4PMin) => ("f32x4.pmin");
    (F32x4PMax) => ("f32x4.pmax");
    (F64x2Ceil) => ("f64x2.ceil");
    (F64x2Floor) => ("f64x2.floor");
    (F64x2Trunc) => ("f64x2.trunc");
    (F64x2Nearest) => ("f64x2.nearest");
    (F64x2Abs) => ("f64x2.abs");
    (F64x2Neg) => ("f64x2.neg");
    (F64x2Sqrt) => ("f64x2.sqrt");
    (F64x2Add) => ("f64x2.add");
    (F64x2Sub) => ("f64x2.sub");
    (F64x2Mul) => ("f64x2.mul");
    (F64x2Div) => ("f64x2.div");
    (F64x2Min) => ("f64x2.min");
    (F64x2Max) => ("f64x2.max");
    (F64x2PMin) => ("f64x2.pmin");
    (F64x2PMax) => ("f64x2.pmax");
    (I32x4TruncSatF32x4S) => ("i32x4.trunc_sat_f32x4_s");
    (I32x4TruncSatF32x4U) => ("i32x4.trunc_sat_f32x4_u");
    (F32x4ConvertI32x4S) => ("f32x4.convert_i32x4_s");
    (F32x4ConvertI32x4U) => ("f32x4.convert_i32x4_u");
    (I32x4TruncSatF64x2SZero) => ("i32x4.trunc_sat_f64x2_s_zero");
    (I32x4TruncSatF64x2UZero) => ("i32x4.trunc_sat_f64x2_u_zero");
    (F64x2ConvertLowI32x4S) => ("f64x2.convert_low_i32x4_s");
    (F64x2ConvertLowI32x4U) => ("f64x2.convert_low_i32x4_u");
    (F32x4DemoteF64x2Zero) => ("f32x4.demote_f64x2_zero");
    (F64x2PromoteLowF32x4) => ("f64x2.promote_low_f32x4");
    (I8x16RelaxedSwizzle) => ("i8x16.relaxed_swizzle");
    (I32x4RelaxedTruncF32x4S) => ("i32x4.relaxed_trunc_f32x4_s");
    (I32x4RelaxedTruncF32x4U) => ("i32x4.relaxed_trunc_f32x4_u");
    (I32x4RelaxedTruncF64x2SZero) => ("i32x4.relaxed_trunc_f64x2_s_zero");
    (I32x4RelaxedTruncF64x2UZero) => ("i32x4.relaxed_trunc_f64x2_u_zero");
    (F32x4RelaxedMadd) => ("f32x4.relaxed_madd");
    (F32x4RelaxedNmadd) => ("f32x4.relaxed_nmadd");
    (F64x2RelaxedMadd) => ("f64x2.relaxed_madd");
    (F64x2RelaxedNmadd) => ("f64x2.relaxed_nmadd");
    (I8x16RelaxedLaneselect) => ("i8x16.relaxed_laneselect");
    (I16x8RelaxedLaneselect) => ("i16x8.relaxed_laneselect");
    (I32x4RelaxedLaneselect) => ("i32x4.relaxed_laneselect");
    (I64x2RelaxedLaneselect) => ("i64x2.relaxed_laneselect");
    (F32x4RelaxedMin) => ("f32x4.relaxed_min");
    (F32x4RelaxedMax) => ("f32x4.relaxed_max");
    (F64x2RelaxedMin) => ("f64x2.relaxed_min");
    (F64x2RelaxedMax) => ("f64x2.relaxed_max");
    (I16x8RelaxedQ15mulrS) => ("i16x8.relaxed_q15mulr_s");
    (I16x8RelaxedDotI8x16I7x16S) => ("i16x8.relaxed_dot_i8x16_i7x16_s");
    (I32x4RelaxedDotI8x16I7x16AddS) => ("i32x4.relaxed_dot_i8x16_i7x16_add_s");
    (StructNew) => ("struct.new");
    (StructNewDefault) => ("struct.new_default");
    (StructGet) => ("struct.get");
    (StructGetS) => ("struct.get_s");
    (StructGetU) => ("struct.get_u");
    (StructSet) => ("struct.set");
    (ArrayNew) => ("array.new");
    (ArrayNewDefault) => ("array.new_default");
    (ArrayNewFixed) => ("array.new_fixed");
    (ArrayNewData) => ("array.new_data");
    (ArrayNewElem) => ("array.new_elem");
    (ArrayGet) => ("array.get");
    (ArrayGetS) => ("array.get_s");
    (ArrayGetU) => ("array.get_u");
    (ArraySet) => ("array.set");
    (ArrayLen) => ("array.len");
    (ArrayFill) => ("array.fill");
    (ArrayCopy) => ("array.copy");
    (ArrayInitData) => ("array.init_data");
    (ArrayInitElem) => ("array.init_elem");
    (AnyConvertExtern) => ("any.convert_extern");
    (ExternConvertAny) => ("extern.convert_any");
    (RefTestNonNull) => ("ref.test");
    (RefTestNullable) => ("ref.test");
    (RefCastNonNull) => ("ref.cast");
    (RefCastNullable) => ("ref.cast");
    (BrOnCast) => ("br_on_cast");
    (BrOnCastFail) => ("br_on_cast_fail");
    (RefI31) => ("ref.i31");
    (I31GetS) => ("i31.get_s");
    (I31GetU) => ("i31.get_u");
    (TryTable) => ("try_table");
    (Throw) => ("throw");
    (ThrowRef) => ("throw_ref");
    (Rethrow) => ("rethrow");
    (Try) => ("try");
    (Catch) => ("catch");
    (CatchAll) => ("catch_all");
    (Delegate) => ("delegate");
    (GlobalAtomicGet) => ("global.atomic.get");
    (GlobalAtomicSet) => ("global.atomic.set");
    (GlobalAtomicRmwAdd) => ("global.atomic.rmw.add");
    (GlobalAtomicRmwSub) => ("global.atomic.rmw.sub");
    (GlobalAtomicRmwAnd) => ("global.atomic.rmw.and");
    (GlobalAtomicRmwOr) => ("global.atomic.rmw.or");
    (GlobalAtomicRmwXor) => ("global.atomic.rmw.xor");
    (GlobalAtomicRmwXchg) => ("global.atomic.rmw.xchg");
    (GlobalAtomicRmwCmpxchg) => ("global.atomic.rmw.cmpxchg");
    (TableAtomicGet) => ("table.atomic.get");
    (TableAtomicSet) => ("table.atomic.set");
    (TableAtomicRmwXchg) => ("table.atomic.rmw.xchg");
    (TableAtomicRmwCmpxchg) => ("table.atomic.rmw.cmpxchg");
    (StructAtomicGet) => ("struct.atomic.get");
    (StructAtomicGetS) => ("struct.atomic.get_s");
    (StructAtomicGetU) => ("struct.atomic.get_u");
    (StructAtomicSet) => ("struct.atomic.set");
    (StructAtomicRmwAdd) => ("struct.atomic.rmw.add");
    (StructAtomicRmwSub) => ("struct.atomic.rmw.sub");
    (StructAtomicRmwAnd) => ("struct.atomic.rmw.and");
    (StructAtomicRmwOr) => ("struct.atomic.rmw.or");
    (StructAtomicRmwXor) => ("struct.atomic.rmw.xor");
    (StructAtomicRmwXchg) => ("struct.atomic.rmw.xchg");
    (StructAtomicRmwCmpxchg) => ("struct.atomic.rmw.cmpxchg");
    (ArrayAtomicGet) => ("array.atomic.get");
    (ArrayAtomicGetS) => ("array.atomic.get_s");
    (ArrayAtomicGetU) => ("array.atomic.get_u");
    (ArrayAtomicSet) => ("array.atomic.set");
    (ArrayAtomicRmwAdd) => ("array.atomic.rmw.add");
    (ArrayAtomicRmwSub) => ("array.atomic.rmw.sub");
    (ArrayAtomicRmwAnd) => ("array.atomic.rmw.and");
    (ArrayAtomicRmwOr) => ("array.atomic.rmw.or");
    (ArrayAtomicRmwXor) => ("array.atomic.rmw.xor");
    (ArrayAtomicRmwXchg) => ("array.atomic.rmw.xchg");
    (ArrayAtomicRmwCmpxchg) => ("array.atomic.rmw.cmpxchg");
    (RefI31Shared) => ("ref.i31_shared")
}

impl<'a> VisitOperator<'a> for PrintOperator<'_, '_, '_, '_> {
    type Output = Result<()>;

    wasmparser::for_each_operator!(define_visit);
}
