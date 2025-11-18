pub mod vm {
    pub mod interpreter {
        use std::{
            alloc::{self, Layout},
            marker::PhantomData, mem, str::FromStr,
        };
        use ark_ff::{AdditiveGroup, BigInt, Field as _, Fp, PrimeField as _};
        use tracing::instrument;
        use crate::{
            compiler::{Field, r1cs_gen::{ConstraintsLayout, WitnessLayout}},
            vm::{
                array::BoxedValue,
                bytecode::{self, AllocationInstrumenter, AllocationType, OpCode, VM},
            },
        };
        pub type Handler = fn(*const u64, Frame, &mut VM);
        #[inline(always)]
        pub fn dispatch(pc: *const u64, frame: Frame, vm: &mut VM) {
            let opcode: Handler = unsafe { mem::transmute(*pc) };
            opcode(pc, frame, vm);
        }
        pub struct Frame {
            pub data: *mut u64,
        }
        #[automatically_derived]
        impl ::core::fmt::Debug for Frame {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                ::core::fmt::Formatter::debug_struct_field1_finish(
                    f,
                    "Frame",
                    "data",
                    &&self.data,
                )
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Frame {}
        #[automatically_derived]
        impl ::core::clone::Clone for Frame {
            #[inline]
            fn clone(&self) -> Frame {
                let _: ::core::clone::AssertParamIsClone<*mut u64>;
                *self
            }
        }
        impl Frame {
            pub fn push(size: u64, parent: Frame, vm: &mut VM) -> Self {
                unsafe {
                    let layout = Layout::array::<u64>(size as usize + 2).unwrap();
                    let data = alloc::alloc(layout) as *mut u64;
                    *data = size;
                    *data.offset(1) = parent.data as u64;
                    let data = data.offset(2);
                    vm.allocation_instrumenter
                        .alloc(AllocationType::Stack, size as usize + 2);
                    Frame { data }
                }
            }
            #[inline(always)]
            pub fn pop(self, vm: &mut VM) -> Frame {
                unsafe {
                    let real_data = self.data.offset(-2);
                    let parent_data = *real_data.offset(1) as *mut u64;
                    let size = *real_data;
                    alloc::dealloc(
                        real_data as *mut u8,
                        Layout::array::<u64>(size as usize + 2).unwrap(),
                    );
                    vm.allocation_instrumenter
                        .free(AllocationType::Stack, size as usize + 2);
                    Frame { data: parent_data }
                }
            }
            #[inline(always)]
            pub fn read_field(&self, offset: isize) -> Field {
                let a0 = unsafe { *self.data.offset(offset) };
                let a1 = unsafe { *self.data.offset(offset + 1) };
                let a2 = unsafe { *self.data.offset(offset + 2) };
                let a3 = unsafe { *self.data.offset(offset + 3) };
                Fp(BigInt([a0, a1, a2, a3]), PhantomData)
            }
            #[inline(always)]
            pub fn read_field_mut(&self, offset: isize) -> *mut Field {
                unsafe { self.data.offset(offset) as *mut Field }
            }
            #[inline(always)]
            pub fn read_u64_mut(&self, offset: isize) -> *mut u64 {
                unsafe { self.data.offset(offset) }
            }
            #[inline(always)]
            pub fn read_u64(&self, offset: isize) -> u64 {
                unsafe { *self.data.offset(offset) }
            }
            #[inline(always)]
            pub fn read_bool(&self, offset: isize) -> bool {
                let a0 = unsafe { *self.data.offset(offset) };
                a0 != 0
            }
            #[inline(always)]
            pub fn read_ptr<A>(&self, offset: isize) -> *mut A {
                unsafe { *self.data.offset(offset) as *mut A }
            }
            #[inline(always)]
            pub fn read_array(&self, offset: isize) -> BoxedValue {
                unsafe { *self.read_array_mut(offset) }
            }
            #[inline(always)]
            pub fn read_array_mut(&self, offset: isize) -> *mut BoxedValue {
                unsafe { self.data.offset(offset) as *mut BoxedValue }
            }
            #[inline(always)]
            pub fn write_u64(&self, offset: isize, value: u64) {
                unsafe {
                    *self.data.offset(offset) = value;
                };
            }
            #[inline(always)]
            pub fn write_field(&self, offset: isize, field: Field) {
                let a0 = field.0.0[0];
                let a1 = field.0.0[1];
                let a2 = field.0.0[2];
                let a3 = field.0.0[3];
                unsafe {
                    *self.data.offset(offset) = a0;
                    *self.data.offset(offset + 1) = a1;
                    *self.data.offset(offset + 2) = a2;
                    *self.data.offset(offset + 3) = a3;
                }
            }
            #[inline(always)]
            pub fn memcpy(&self, dest: isize, src: isize, size: usize) {
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        self.data.offset(src),
                        self.data.offset(dest),
                        size,
                    );
                }
            }
            #[inline(always)]
            pub fn write_to(&self, dst: *mut u64, src: isize, size: usize) {
                unsafe {
                    std::ptr::copy_nonoverlapping(self.data.offset(src), dst, size);
                }
            }
        }
        fn prepare_dispatch(program: &mut [u64]) {
            let mut current_offset = 0;
            while current_offset < program.len() {
                let opcode = program[current_offset];
                if opcode == u64::MAX {
                    current_offset += 2;
                    continue;
                }
                let next = OpCode::next_opcode(program, current_offset);
                program[current_offset] = bytecode::DISPATCH[opcode as usize] as u64;
                current_offset = next;
            }
        }
        pub struct WitgenResult {
            pub out_wit_pre_comm: Vec<Field>,
            pub out_wit_post_comm: Vec<Field>,
            pub out_a: Vec<Field>,
            pub out_b: Vec<Field>,
            pub out_c: Vec<Field>,
            pub instrumenter: AllocationInstrumenter,
        }
        fn fix_multiplicities_section(wit: &mut [Field], witness_layout: WitnessLayout) {
            for i in witness_layout
                .multiplicities_start()..witness_layout.multiplicities_end()
            {
                wit[i] = Field::from(wit[i].0.0[0]);
            }
        }
        pub fn run(
            program: &[u64],
            witness_layout: WitnessLayout,
            constraints_layout: ConstraintsLayout,
            inputs: &[Field],
        ) -> WitgenResult {
            {}
            #[allow(clippy::suspicious_else_formatting)]
            {
                let __tracing_attr_span;
                let __tracing_attr_guard;
                if ::tracing::Level::INFO <= ::tracing::level_filters::STATIC_MAX_LEVEL
                    && ::tracing::Level::INFO
                        <= ::tracing::level_filters::LevelFilter::current() || { false }
                {
                    __tracing_attr_span = {
                        use ::tracing::__macro_support::Callsite as _;
                        static __CALLSITE: ::tracing::callsite::DefaultCallsite = {
                            static META: ::tracing::Metadata<'static> = {
                                ::tracing_core::metadata::Metadata::new(
                                    "Interpreter::run",
                                    "spartan_vm::vm::interpreter",
                                    ::tracing::Level::INFO,
                                    ::tracing_core::__macro_support::Option::Some(
                                        "src/vm/interpreter.rs",
                                    ),
                                    ::tracing_core::__macro_support::Option::Some(176u32),
                                    ::tracing_core::__macro_support::Option::Some(
                                        "spartan_vm::vm::interpreter",
                                    ),
                                    ::tracing_core::field::FieldSet::new(
                                        &[],
                                        ::tracing_core::callsite::Identifier(&__CALLSITE),
                                    ),
                                    ::tracing::metadata::Kind::SPAN,
                                )
                            };
                            ::tracing::callsite::DefaultCallsite::new(&META)
                        };
                        let mut interest = ::tracing::subscriber::Interest::never();
                        if ::tracing::Level::INFO
                            <= ::tracing::level_filters::STATIC_MAX_LEVEL
                            && ::tracing::Level::INFO
                                <= ::tracing::level_filters::LevelFilter::current()
                            && {
                                interest = __CALLSITE.interest();
                                !interest.is_never()
                            }
                            && ::tracing::__macro_support::__is_enabled(
                                __CALLSITE.metadata(),
                                interest,
                            )
                        {
                            let meta = __CALLSITE.metadata();
                            ::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
                        } else {
                            let span = ::tracing::__macro_support::__disabled_span(
                                __CALLSITE.metadata(),
                            );
                            {};
                            span
                        }
                    };
                    __tracing_attr_guard = __tracing_attr_span.enter();
                }
                #[warn(clippy::suspicious_else_formatting)]
                {
                    #[allow(
                        unknown_lints,
                        unreachable_code,
                        clippy::diverging_sub_expression,
                        clippy::empty_loop,
                        clippy::let_unit_value,
                        clippy::let_with_type_underscore,
                        clippy::needless_return,
                        clippy::unreachable
                    )]
                    if false {
                        let __tracing_attr_fake_return: WitgenResult = loop {};
                        return __tracing_attr_fake_return;
                    }
                    {
                        let mut out_a = ::alloc::vec::from_elem(
                            Field::ZERO,
                            constraints_layout.size(),
                        );
                        let mut out_b = ::alloc::vec::from_elem(
                            Field::ZERO,
                            constraints_layout.size(),
                        );
                        let mut out_c = ::alloc::vec::from_elem(
                            Field::ZERO,
                            constraints_layout.size(),
                        );
                        let mut out_wit_pre_comm = ::alloc::vec::from_elem(
                            Field::ZERO,
                            witness_layout.pre_commitment_size(),
                        );
                        out_wit_pre_comm[0] = Field::ONE;
                        for i in 0..inputs.len() {
                            out_wit_pre_comm[1 + i] = inputs[i];
                        }
                        let mut out_wit_post_comm = ::alloc::vec::from_elem(
                            Field::ZERO,
                            witness_layout.post_commitment_size(),
                        );
                        let mut vm = VM::new_witgen(
                            out_a.as_mut_ptr(),
                            out_b.as_mut_ptr(),
                            out_c.as_mut_ptr(),
                            unsafe {
                                out_wit_pre_comm
                                    .as_mut_ptr()
                                    .offset(1 + inputs.len() as isize)
                            },
                            unsafe {
                                out_wit_pre_comm
                                    .as_mut_ptr()
                                    .offset(witness_layout.multiplicities_start() as isize)
                            },
                            unsafe {
                                out_a
                                    .as_mut_ptr()
                                    .offset(constraints_layout.lookups_data_start() as isize)
                            },
                            unsafe {
                                out_b
                                    .as_mut_ptr()
                                    .offset(constraints_layout.lookups_data_start() as isize)
                            },
                            constraints_layout.tables_data_start(),
                            witness_layout.tables_data_start()
                                - witness_layout.challenges_start(),
                        );
                        let frame = Frame::push(
                            program[1],
                            Frame {
                                data: std::ptr::null_mut(),
                            },
                            &mut vm,
                        );
                        {
                            ::std::io::_print(
                                format_args!("Frame data address {0:?}\n", frame.data),
                            );
                        };
                        for (i, el) in inputs.iter().enumerate() {
                            frame.write_field(2 + (i as isize) * 4, *el);
                        }
                        let mut program = program.to_vec();
                        prepare_dispatch(&mut program);
                        {
                            ::std::io::_print(format_args!("Program {0:?}\n", program));
                        };
                        let pc = unsafe { program.as_mut_ptr().offset(2) };
                        dispatch(pc, frame, &mut vm);
                        fix_multiplicities_section(
                            &mut out_wit_pre_comm,
                            witness_layout,
                        );
                        let mut random = Field::from_bigint(
                                BigInt::from_str("18765435241434657586764563434227903")
                                    .unwrap(),
                            )
                            .unwrap();
                        for i in 0..witness_layout.challenges_size {
                            out_wit_post_comm[i] = random;
                            random = (random + Field::from(17)) * random;
                        }
                        let mut running_prod = Field::from(1);
                        for tbl in vm.tables.iter() {
                            if tbl.num_indices != 1 || tbl.num_values != 0 {
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "not yet implemented: {0}",
                                            format_args!("wide tables"),
                                        ),
                                    );
                                };
                            }
                            let alpha = out_wit_post_comm[0];
                            for i in 0..tbl.length {
                                let multiplicity = unsafe {
                                    *tbl.multiplicities_wit.offset(i as isize)
                                };
                                let denom = alpha - Field::from(i as u64);
                                out_b[tbl.elem_inverses_constraint_section_offset + i] = denom;
                                out_c[tbl.elem_inverses_constraint_section_offset + i] = multiplicity;
                                if multiplicity != Field::ZERO {
                                    out_a[tbl.elem_inverses_constraint_section_offset + i] = running_prod;
                                    running_prod *= denom;
                                }
                            }
                        }
                        let mut running_inv = running_prod.inverse().unwrap();
                        for tbl in vm.tables.iter().rev() {
                            if tbl.num_indices != 1 || tbl.num_values != 0 {
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "not yet implemented: {0}",
                                            format_args!("wide tables"),
                                        ),
                                    );
                                };
                            }
                            for i in (0..tbl.length).rev() {
                                let multiplicity = out_c[tbl
                                    .elem_inverses_constraint_section_offset + i];
                                let denom = out_b[tbl
                                    .elem_inverses_constraint_section_offset + i];
                                let running_prod = out_a[tbl
                                    .elem_inverses_constraint_section_offset + i];
                                if multiplicity != Field::ZERO {
                                    let elem = running_prod * running_inv;
                                    out_a[tbl.elem_inverses_constraint_section_offset + i] = elem;
                                    running_inv *= denom;
                                }
                            }
                        }
                        let mut current_lookup_off = 0;
                        while current_lookup_off < constraints_layout.lookups_data_size {
                            let cnst_off = constraints_layout.lookups_data_start()
                                + current_lookup_off;
                            let wit_off = witness_layout.lookups_data_start()
                                - witness_layout.challenges_start() + current_lookup_off;
                            let table_ix = out_a[cnst_off].0.0[0];
                            let table = &vm.tables[table_ix as usize];
                            if table.num_indices != 1 || table.num_values != 0 {
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "not yet implemented: {0}",
                                            format_args!("wide tables"),
                                        ),
                                    );
                                };
                            }
                            let ix_in_table = out_b[cnst_off].0.0[0];
                            out_a[cnst_off] = out_a[table
                                .elem_inverses_constraint_section_offset
                                + ix_in_table as usize];
                            out_b[cnst_off] = out_b[table
                                .elem_inverses_constraint_section_offset
                                + ix_in_table as usize];
                            out_c[cnst_off] = Field::ONE;
                            out_wit_post_comm[wit_off] = out_a[cnst_off];
                            out_c[table.elem_inverses_constraint_section_offset
                                + table.length] += out_a[cnst_off];
                            current_lookup_off += 1;
                        }
                        for tbl in vm.tables.iter() {
                            if tbl.num_indices != 1 || tbl.num_values != 0 {
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "not yet implemented: {0}",
                                            format_args!("wide tables"),
                                        ),
                                    );
                                };
                            }
                            for i in 0..tbl.length {
                                let multiplicity = out_c[tbl
                                    .elem_inverses_constraint_section_offset + i];
                                if multiplicity != Field::ZERO {
                                    let elem = out_a[tbl.elem_inverses_constraint_section_offset
                                        + i] * multiplicity;
                                    out_a[tbl.elem_inverses_constraint_section_offset + i] = elem;
                                    out_wit_post_comm[tbl.elem_inverses_witness_section_offset
                                        + i] = elem;
                                    out_a[tbl.elem_inverses_constraint_section_offset
                                        + tbl.length] += elem;
                                }
                            }
                            out_b[tbl.elem_inverses_constraint_section_offset
                                + tbl.length] = Field::ONE;
                        }
                        let result = WitgenResult {
                            out_wit_pre_comm,
                            out_wit_post_comm,
                            out_a,
                            out_b,
                            out_c,
                            instrumenter: vm.allocation_instrumenter,
                        };
                        result
                    }
                }
            }
        }
        pub fn run_ad(
            program: &[u64],
            coeffs: &[Field],
            witness_layout: WitnessLayout,
            constraints_layout: ConstraintsLayout,
        ) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {
            {}
            #[allow(clippy::suspicious_else_formatting)]
            {
                let __tracing_attr_span;
                let __tracing_attr_guard;
                if ::tracing::Level::INFO <= ::tracing::level_filters::STATIC_MAX_LEVEL
                    && ::tracing::Level::INFO
                        <= ::tracing::level_filters::LevelFilter::current() || { false }
                {
                    __tracing_attr_span = {
                        use ::tracing::__macro_support::Callsite as _;
                        static __CALLSITE: ::tracing::callsite::DefaultCallsite = {
                            static META: ::tracing::Metadata<'static> = {
                                ::tracing_core::metadata::Metadata::new(
                                    "Interpreter::run_ad",
                                    "spartan_vm::vm::interpreter",
                                    ::tracing::Level::INFO,
                                    ::tracing_core::__macro_support::Option::Some(
                                        "src/vm/interpreter.rs",
                                    ),
                                    ::tracing_core::__macro_support::Option::Some(347u32),
                                    ::tracing_core::__macro_support::Option::Some(
                                        "spartan_vm::vm::interpreter",
                                    ),
                                    ::tracing_core::field::FieldSet::new(
                                        &[],
                                        ::tracing_core::callsite::Identifier(&__CALLSITE),
                                    ),
                                    ::tracing::metadata::Kind::SPAN,
                                )
                            };
                            ::tracing::callsite::DefaultCallsite::new(&META)
                        };
                        let mut interest = ::tracing::subscriber::Interest::never();
                        if ::tracing::Level::INFO
                            <= ::tracing::level_filters::STATIC_MAX_LEVEL
                            && ::tracing::Level::INFO
                                <= ::tracing::level_filters::LevelFilter::current()
                            && {
                                interest = __CALLSITE.interest();
                                !interest.is_never()
                            }
                            && ::tracing::__macro_support::__is_enabled(
                                __CALLSITE.metadata(),
                                interest,
                            )
                        {
                            let meta = __CALLSITE.metadata();
                            ::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
                        } else {
                            let span = ::tracing::__macro_support::__disabled_span(
                                __CALLSITE.metadata(),
                            );
                            {};
                            span
                        }
                    };
                    __tracing_attr_guard = __tracing_attr_span.enter();
                }
                #[warn(clippy::suspicious_else_formatting)]
                {
                    #[allow(
                        unknown_lints,
                        unreachable_code,
                        clippy::diverging_sub_expression,
                        clippy::empty_loop,
                        clippy::let_unit_value,
                        clippy::let_with_type_underscore,
                        clippy::needless_return,
                        clippy::unreachable
                    )]
                    if false {
                        let __tracing_attr_fake_return: (
                            Vec<Field>,
                            Vec<Field>,
                            Vec<Field>,
                            AllocationInstrumenter,
                        ) = loop {};
                        return __tracing_attr_fake_return;
                    }
                    {
                        let mut out_da = ::alloc::vec::from_elem(
                            Field::ZERO,
                            witness_layout.size(),
                        );
                        let mut out_db = ::alloc::vec::from_elem(
                            Field::ZERO,
                            witness_layout.size(),
                        );
                        let mut out_dc = ::alloc::vec::from_elem(
                            Field::ZERO,
                            witness_layout.size(),
                        );
                        let mut vm = VM::new_ad(
                            out_da.as_mut_ptr(),
                            out_db.as_mut_ptr(),
                            out_dc.as_mut_ptr(),
                            coeffs.as_ptr(),
                            witness_layout,
                            constraints_layout,
                        );
                        let frame = Frame::push(
                            program[1],
                            Frame {
                                data: std::ptr::null_mut(),
                            },
                            &mut vm,
                        );
                        let mut program = program.to_vec();
                        prepare_dispatch(&mut program);
                        let pc = unsafe { program.as_mut_ptr().offset(2) };
                        dispatch(pc, frame, &mut vm);
                        (out_da, out_db, out_dc, vm.allocation_instrumenter)
                    }
                }
            }
        }
    }
    pub mod bytecode {
        #![allow(unused_variables)]
        use crate::compiler::r1cs_gen::{ConstraintsLayout, WitnessLayout};
        use crate::vm::interpreter::dispatch;
        use ark_ff::{AdditiveGroup as _, BigInteger as _};
        use opcode_gen::interpreter;
        use crate::vm::array::{BoxedLayout, BoxedValue};
        use crate::{compiler::Field, vm::interpreter::{Frame, Handler}};
        use crate::vm::array::DataType;
        use plotters::prelude::*;
        use std::fmt::Display;
        use std::path::Path;
        use std::ptr;
        pub const LIMBS: usize = 4;
        pub struct FramePosition(pub usize);
        impl FramePosition {
            pub fn offset(&self, offset: isize) -> FramePosition {
                FramePosition(self.0.checked_add_signed(offset).unwrap())
            }
            pub fn return_data_ptr() -> FramePosition {
                FramePosition(0)
            }
            pub fn return_address_ptr() -> FramePosition {
                FramePosition(1)
            }
        }
        pub struct JumpTarget(pub isize);
        pub enum AllocationType {
            Stack,
            Heap,
        }
        pub enum AlocationEvent {
            Alloc(AllocationType, usize),
            Free(AllocationType, usize),
        }
        pub struct AllocationInstrumenter {
            pub events: Vec<AlocationEvent>,
        }
        impl AllocationInstrumenter {
            pub fn new() -> Self {
                Self {
                    events: ::alloc::vec::Vec::new(),
                }
            }
            pub fn alloc(&mut self, ty: AllocationType, size: usize) {
                self.events.push(AlocationEvent::Alloc(ty, size));
            }
            pub fn free(&mut self, ty: AllocationType, size: usize) {
                self.events.push(AlocationEvent::Free(ty, size));
            }
            pub fn plot(&self, path: &Path) -> usize {
                let mut stack_usage = Vec::new();
                let mut heap_usage = Vec::new();
                let mut current_stack = 0usize;
                let mut current_heap = 0usize;
                for event in &self.events {
                    match event {
                        AlocationEvent::Alloc(AllocationType::Stack, size) => {
                            current_stack += size * 8;
                        }
                        AlocationEvent::Alloc(AllocationType::Heap, size) => {
                            current_heap += size * 8;
                        }
                        AlocationEvent::Free(AllocationType::Stack, size) => {
                            current_stack = current_stack.saturating_sub(*size * 8);
                        }
                        AlocationEvent::Free(AllocationType::Heap, size) => {
                            current_heap = current_heap.saturating_sub(*size * 8);
                        }
                    }
                    stack_usage.push(current_stack);
                    heap_usage.push(current_heap);
                }
                if stack_usage.is_empty() {
                    return 0;
                }
                let total_usage: Vec<usize> = stack_usage
                    .iter()
                    .zip(heap_usage.iter())
                    .map(|(s, h)| s + h)
                    .collect();
                let max_stack = *stack_usage.iter().max().unwrap_or(&1);
                let max_heap = *heap_usage.iter().max().unwrap_or(&1);
                let max_total = *total_usage.iter().max().unwrap_or(&1);
                let root = BitMapBackend::new(path, (2400, 800)).into_drawing_area();
                root.fill(&WHITE).unwrap();
                let (left, rest) = root.split_horizontally(800);
                let (middle, right) = rest.split_horizontally(800);
                let common_max = max_total.max(max_stack).max(max_heap);
                let (unit, divisor, y_label) = if common_max >= 2 * 1024 * 1024 {
                    ("MB", 1024 * 1024, "Memory Size (MB)".to_string())
                } else if common_max >= 2 * 1024 {
                    ("KB", 1024, "Memory Size (KB)".to_string())
                } else {
                    ("B", 1, "Memory Size (bytes)".to_string())
                };
                let total_data: Vec<(usize, f64)> = total_usage
                    .iter()
                    .enumerate()
                    .map(|(i, &size)| (i, size as f64 / divisor as f64))
                    .collect();
                let stack_data: Vec<(usize, f64)> = stack_usage
                    .iter()
                    .enumerate()
                    .map(|(i, &size)| (i, size as f64 / divisor as f64))
                    .collect();
                let heap_data: Vec<(usize, f64)> = heap_usage
                    .iter()
                    .enumerate()
                    .map(|(i, &size)| (i, size as f64 / divisor as f64))
                    .collect();
                let y_max = common_max as f64 / divisor as f64;
                let mut chart1 = ChartBuilder::on(&left)
                    .caption("Total Memory Usage", ("sans-serif", 20))
                    .margin(5)
                    .x_label_area_size(30)
                    .y_label_area_size(50)
                    .build_cartesian_2d(0..total_usage.len(), 0.0..y_max)
                    .unwrap();
                chart1
                    .configure_mesh()
                    .x_labels(5)
                    .y_labels(5)
                    .x_desc("Event Number")
                    .y_desc(y_label.clone())
                    .draw()
                    .unwrap();
                chart1
                    .draw_series(
                        total_data
                            .iter()
                            .map(|&(x, y)| Rectangle::new(
                                [(x, 0.0), (x + 1, y)],
                                GREEN.filled(),
                            )),
                    )
                    .unwrap()
                    .label("Total Memory")
                    .legend(|(x, y)| PathElement::new(
                        <[_]>::into_vec(::alloc::boxed::box_new([(x, y), (x + 20, y)])),
                        GREEN,
                    ));
                chart1
                    .configure_series_labels()
                    .background_style(&WHITE.mix(0.8))
                    .border_style(&BLACK)
                    .draw()
                    .unwrap();
                let mut chart2 = ChartBuilder::on(&middle)
                    .caption("Stack Memory Usage", ("sans-serif", 20))
                    .margin(5)
                    .x_label_area_size(30)
                    .y_label_area_size(50)
                    .build_cartesian_2d(0..stack_usage.len(), 0.0..y_max)
                    .unwrap();
                chart2
                    .configure_mesh()
                    .x_labels(5)
                    .y_labels(5)
                    .x_desc("Event Number")
                    .y_desc(y_label.clone())
                    .draw()
                    .unwrap();
                chart2
                    .draw_series(
                        stack_data
                            .iter()
                            .map(|&(x, y)| Rectangle::new(
                                [(x, 0.0), (x + 1, y)],
                                BLUE.filled(),
                            )),
                    )
                    .unwrap()
                    .label("Stack Memory")
                    .legend(|(x, y)| PathElement::new(
                        <[_]>::into_vec(::alloc::boxed::box_new([(x, y), (x + 20, y)])),
                        BLUE,
                    ));
                chart2
                    .configure_series_labels()
                    .background_style(&WHITE.mix(0.8))
                    .border_style(&BLACK)
                    .draw()
                    .unwrap();
                let mut chart3 = ChartBuilder::on(&right)
                    .caption("Heap Memory Usage", ("sans-serif", 20))
                    .margin(5)
                    .x_label_area_size(30)
                    .y_label_area_size(50)
                    .build_cartesian_2d(0..heap_usage.len(), 0.0..y_max)
                    .unwrap();
                chart3
                    .configure_mesh()
                    .x_labels(5)
                    .y_labels(5)
                    .x_desc("Event Number")
                    .y_desc(y_label.clone())
                    .draw()
                    .unwrap();
                chart3
                    .draw_series(
                        heap_data
                            .iter()
                            .map(|&(x, y)| Rectangle::new(
                                [(x, 0.0), (x + 1, y)],
                                RED.filled(),
                            )),
                    )
                    .unwrap()
                    .label("Heap Memory")
                    .legend(|(x, y)| PathElement::new(
                        <[_]>::into_vec(::alloc::boxed::box_new([(x, y), (x + 20, y)])),
                        RED,
                    ));
                chart3
                    .configure_series_labels()
                    .background_style(&WHITE.mix(0.8))
                    .border_style(&BLACK)
                    .draw()
                    .unwrap();
                root.present().unwrap();
                *stack_usage.last().unwrap() + *heap_usage.last().unwrap()
            }
        }
        pub struct TableInfo {
            pub multiplicities_wit: *mut Field,
            pub num_indices: usize,
            pub num_values: usize,
            pub length: usize,
            pub elem_inverses_witness_section_offset: usize,
            pub elem_inverses_constraint_section_offset: usize,
        }
        pub struct FwdArrays {
            pub out_a: *mut Field,
            pub out_b: *mut Field,
            pub out_c: *mut Field,
            pub algebraic_witness: *mut Field,
            pub multiplicities_witness: *mut Field,
            pub lookups_a: *mut Field,
            pub lookups_b: *mut Field,
            pub elem_inverses_constraint_section_offset: usize,
            pub elem_inverses_witness_section_offset: usize,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for FwdArrays {}
        #[automatically_derived]
        impl ::core::clone::Clone for FwdArrays {
            #[inline]
            fn clone(&self) -> FwdArrays {
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
        pub struct AdArrays {
            pub out_da: *mut Field,
            pub out_db: *mut Field,
            pub out_dc: *mut Field,
            pub ad_coeffs: *const Field,
            pub current_wit_off: usize,
            pub logup_wit_challenge_off: usize,
            pub current_wit_multiplicities_off: usize,
            pub current_wit_tables_off: usize,
            pub current_wit_lookups_off: usize,
            pub current_cnst_off: usize,
            pub current_cnst_tables_off: usize,
            pub current_cnst_lookups_off: usize,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for AdArrays {}
        #[automatically_derived]
        impl ::core::clone::Clone for AdArrays {
            #[inline]
            fn clone(&self) -> AdArrays {
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*mut Field>;
                let _: ::core::clone::AssertParamIsClone<*const Field>;
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
        pub union Arrays {
            pub as_forward: FwdArrays,
            pub as_ad: AdArrays,
        }
        pub struct VM {
            pub data: Arrays,
            pub allocation_instrumenter: AllocationInstrumenter,
            pub tables: Vec<TableInfo>,
            pub rgchk_8: Option<usize>,
        }
        impl VM {
            pub fn new_witgen(
                out_a: *mut Field,
                out_b: *mut Field,
                out_c: *mut Field,
                algebraic_witness: *mut Field,
                multiplicities_witness: *mut Field,
                lookups_a: *mut Field,
                lookups_b: *mut Field,
                elem_inverses_constraint_section_offset: usize,
                elem_inverses_witness_section_offset: usize,
            ) -> Self {
                Self {
                    data: Arrays {
                        as_forward: FwdArrays {
                            out_a,
                            out_b,
                            out_c,
                            algebraic_witness,
                            multiplicities_witness,
                            lookups_b,
                            lookups_a,
                            elem_inverses_constraint_section_offset,
                            elem_inverses_witness_section_offset,
                        },
                    },
                    allocation_instrumenter: AllocationInstrumenter::new(),
                    tables: ::alloc::vec::Vec::new(),
                    rgchk_8: None,
                }
            }
            pub fn new_ad(
                out_da: *mut Field,
                out_db: *mut Field,
                out_dc: *mut Field,
                ad_coeffs: *const Field,
                witness_layout: WitnessLayout,
                constraints_layout: ConstraintsLayout,
            ) -> Self {
                Self {
                    data: Arrays {
                        as_ad: AdArrays {
                            out_da,
                            out_db,
                            out_dc,
                            ad_coeffs,
                            current_wit_off: 1,
                            logup_wit_challenge_off: witness_layout.challenges_start(),
                            current_wit_multiplicities_off: witness_layout
                                .multiplicities_start(),
                            current_wit_tables_off: witness_layout.tables_data_start(),
                            current_wit_lookups_off: witness_layout.lookups_data_start(),
                            current_cnst_off: 0,
                            current_cnst_tables_off: constraints_layout
                                .tables_data_start(),
                            current_cnst_lookups_off: constraints_layout
                                .lookups_data_start(),
                        },
                    },
                    allocation_instrumenter: AllocationInstrumenter::new(),
                    tables: ::alloc::vec::Vec::new(),
                    rgchk_8: None,
                }
            }
        }
        #[inline(always)]
        fn jmp(pc: *const u64, frame: Frame, vm: &mut VM, target: JumpTarget) {
            let pc = unsafe { pc.offset(target.0) };
            dispatch(pc, frame, vm);
        }
        #[inline(always)]
        fn jmp_if(
            pc: *const u64,
            frame: Frame,
            vm: &mut VM,
            cond: u64,
            if_t: JumpTarget,
            if_f: JumpTarget,
        ) {
            let target = if cond != 0 { if_t } else { if_f };
            let pc = unsafe { pc.offset(target.0) };
            dispatch(pc, frame, vm);
        }
        #[inline(always)]
        fn call(
            pc: *const u64,
            frame: Frame,
            vm: &mut VM,
            func: JumpTarget,
            args: &[(usize, FramePosition)],
            ret: FramePosition,
        ) {
            let func_pc = unsafe { pc.offset(func.0) };
            let func_frame_size = unsafe { *func_pc.offset(-1) };
            let new_frame = Frame::push(func_frame_size, frame, vm);
            let ret_data_ptr = unsafe { frame.data.offset(ret.0 as isize) };
            let ret_pc = unsafe { pc.offset(4 + 2 * args.len() as isize) };
            unsafe {
                *new_frame.data = ret_data_ptr as u64;
                *new_frame.data.offset(1) = ret_pc as u64;
            };
            let mut current_child = unsafe { new_frame.data.offset(2) };
            for (i, (arg_size, arg_pos)) in args.iter().enumerate() {
                frame.write_to(current_child, arg_pos.0 as isize, *arg_size);
                current_child = unsafe { current_child.offset(*arg_size as isize) };
            }
            dispatch(func_pc, new_frame, vm);
        }
        #[inline(always)]
        fn ret(_pc: *const u64, frame: Frame, vm: &mut VM) {
            let ret_address = unsafe { *frame.data.offset(1) } as *mut u64;
            let new_frame = frame.pop(vm);
            if new_frame.data.is_null() {
                return;
            }
            dispatch(ret_address, new_frame, vm);
        }
        #[inline(always)]
        fn r1c(pc: *const u64, frame: Frame, vm: &mut VM, a: Field, b: Field, c: Field) {
            unsafe {
                *vm.data.as_forward.out_a = a;
                *vm.data.as_forward.out_b = b;
                *vm.data.as_forward.out_c = c;
            }
            unsafe {
                vm.data.as_forward.out_a = vm.data.as_forward.out_a.offset(1);
                vm.data.as_forward.out_b = vm.data.as_forward.out_b.offset(1);
                vm.data.as_forward.out_c = vm.data.as_forward.out_c.offset(1);
            };
            let pc = unsafe { pc.offset(4) };
            dispatch(pc, frame, vm);
        }
        #[inline(always)]
        fn write_witness(pc: *const u64, frame: Frame, vm: &mut VM, val: Field) {
            unsafe {
                *vm.data.as_forward.algebraic_witness = val;
                vm.data.as_forward.algebraic_witness = vm
                    .data
                    .as_forward
                    .algebraic_witness
                    .offset(1);
            };
            let pc = unsafe { pc.offset(2) };
            dispatch(pc, frame, vm);
        }
        #[inline(always)]
        fn nop() {}
        #[inline(always)]
        fn mov_const(res: *mut u64, val: u64) {
            unsafe {
                *res = val;
            }
        }
        #[inline(always)]
        fn mov_frame(
            frame: Frame,
            target: FramePosition,
            source: FramePosition,
            size: usize,
        ) {
            frame.memcpy(target.0 as isize, source.0 as isize, size);
        }
        #[inline(always)]
        fn write_ptr(
            frame: Frame,
            ptr: *mut u64,
            offset: isize,
            src: FramePosition,
            size: usize,
        ) {
            let ptr = unsafe { ptr.offset(offset) };
            frame.write_to(ptr, src.0 as isize, size);
        }
        #[inline(always)]
        fn add_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = a + b;
            }
        }
        #[inline(always)]
        fn sub_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = a - b;
            }
        }
        #[inline(always)]
        fn div_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = a / b;
            }
        }
        #[inline(always)]
        fn mul_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = a * b;
            }
        }
        #[inline(always)]
        fn and_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = a & b;
            }
        }
        #[inline(always)]
        fn not_u64(res: *mut u64, a: u64) {
            unsafe {
                *res = !a;
            }
        }
        #[inline(always)]
        fn eq_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = (a == b) as u64;
            }
        }
        #[inline(always)]
        fn lt_u64(res: *mut u64, a: u64, b: u64) {
            unsafe {
                *res = (a < b) as u64;
            }
        }
        #[inline(always)]
        fn truncate_u64(res: *mut u64, a: u64, to_bits: u64) {
            unsafe {
                *res = a & ((1 << to_bits) - 1);
            }
        }
        #[inline(always)]
        fn truncate_f_to_u(res: *mut Field, a: Field, to_bits: u64) {
            unsafe {
                *res = From::from(
                    ark_ff::PrimeField::into_bigint(a).0[0] & ((1 << to_bits) - 1),
                );
            }
        }
        #[inline(always)]
        fn add_field(res: *mut Field, a: Field, b: Field) {
            unsafe {
                *res = a + b;
            }
        }
        #[inline(always)]
        fn sub_field(res: *mut Field, a: Field, b: Field) {
            unsafe {
                *res = a - b;
            }
        }
        #[inline(always)]
        fn div_field(res: *mut Field, a: Field, b: Field) {
            unsafe {
                *res = a / b;
            }
        }
        #[inline(always)]
        fn mul_field(res: *mut Field, a: Field, b: Field) {
            unsafe {
                *res = a * b;
            }
        }
        #[inline(always)]
        fn cast_field_to_u64(res: *mut u64, a: Field) {
            unsafe {
                *res = ark_ff::PrimeField::into_bigint(a).0[0];
            }
        }
        #[inline(always)]
        fn cast_u64_to_field(res: *mut Field, a: u64) {
            unsafe {
                *res = From::from(a);
            }
        }
        #[inline(always)]
        fn array_alloc(
            res: *mut BoxedValue,
            stride: usize,
            meta: BoxedLayout,
            items: &[FramePosition],
            frame: Frame,
            vm: &mut VM,
        ) {
            let array = BoxedValue::alloc(meta, vm);
            for (i, item) in items.iter().enumerate() {
                let tgt = array.array_idx(i, stride);
                frame.write_to(tgt, item.0 as isize, stride);
            }
            unsafe {
                *res = array;
            }
        }
        #[inline(always)]
        fn array_get(
            res: *mut u64,
            array: BoxedValue,
            index: u64,
            stride: usize,
            vm: &mut VM,
        ) {
            let src = array.array_idx(index as usize, stride);
            unsafe {
                ptr::copy_nonoverlapping(src, res, stride);
            }
        }
        #[inline(never)]
        fn array_set(
            res: *mut BoxedValue,
            array: BoxedValue,
            index: u64,
            source: FramePosition,
            stride: usize,
            frame: Frame,
            vm: &mut VM,
        ) {
            let new_array = array.copy_if_reused(vm);
            let target = new_array.array_idx(index as usize, stride);
            if new_array.layout().data_type() == DataType::BoxedArray {
                if new_array.0 == array.0 {
                    let old_elem = unsafe { *(target as *mut BoxedValue) };
                    old_elem.dec_rc(vm);
                } else {
                    for i in 0..new_array.layout().array_size() {
                        if i != index as usize {
                            let elem = unsafe {
                                *(new_array.array_idx(i, stride) as *mut BoxedValue)
                            };
                            elem.inc_rc(1);
                        }
                    }
                }
            }
            frame.write_to(target, source.0 as isize, stride);
            unsafe {
                *res = new_array;
            }
        }
        #[inline(always)]
        fn inc_rc(array: BoxedValue, amount: u64) {
            array.inc_rc(amount);
        }
        #[inline(never)]
        fn dec_rc(array: BoxedValue, vm: &mut VM) {
            array.dec_rc(vm);
        }
        #[inline(always)]
        fn boxed_field_alloc(res: *mut BoxedValue, data: Field, vm: &mut VM) {
            let val = BoxedValue::alloc(BoxedLayout::ad_const(), vm);
            let d = val.as_ad_const();
            unsafe {
                (*d).value = data;
                *res = val;
            };
        }
        #[inline(always)]
        fn bump_da(v: BoxedValue, coeff: Field, vm: &mut VM) {
            v.bump_da(coeff, vm);
        }
        #[inline(always)]
        fn bump_db(v: BoxedValue, coeff: Field, vm: &mut VM) {
            v.bump_db(coeff, vm);
        }
        #[inline(always)]
        fn bump_dc(v: BoxedValue, coeff: Field, vm: &mut VM) {
            v.bump_dc(coeff, vm);
        }
        #[inline(always)]
        fn next_d_coeff(v: *mut Field, vm: &mut VM) {
            unsafe {
                *v = *vm
                    .data
                    .as_ad
                    .ad_coeffs
                    .offset(vm.data.as_ad.current_cnst_off as isize);
                vm.data.as_ad.current_cnst_off += 1;
            };
        }
        #[inline(always)]
        fn fresh_witness(res: *mut BoxedValue, vm: &mut VM) {
            let index = unsafe { vm.data.as_ad.current_wit_off as u64 };
            unsafe { vm.data.as_ad.current_wit_off += 1 };
            let val = BoxedValue::alloc(BoxedLayout::ad_witness(), vm);
            let d = val.as_ad_witness();
            unsafe {
                (*d).index = index;
                *res = val;
            }
        }
        #[inline(always)]
        fn box_field(res: *mut BoxedValue, v: Field, vm: &mut VM) {
            let val = BoxedValue::alloc(BoxedLayout::ad_const(), vm);
            let d = val.as_ad_const();
            unsafe {
                (*d).value = v;
                *res = val;
            }
        }
        #[inline(always)]
        fn unbox_field(res: *mut Field, v: BoxedValue) {
            let d = v.as_ad_const();
            unsafe {
                *res = (*d).value;
            }
        }
        #[inline(always)]
        fn mul_const(res: *mut BoxedValue, coeff: Field, v: BoxedValue, vm: &mut VM) {
            let val = BoxedValue::alloc(BoxedLayout::mul_const(), vm);
            let d = val.as_mul_const();
            unsafe {
                (*d).coeff = coeff;
                (*d).value = v;
                (*d).da = Field::ZERO;
                (*d).db = Field::ZERO;
                (*d).dc = Field::ZERO;
                *res = val;
            }
        }
        #[inline(always)]
        fn add_boxed(res: *mut BoxedValue, a: BoxedValue, b: BoxedValue, vm: &mut VM) {
            let val = BoxedValue::alloc(BoxedLayout::ad_sum(), vm);
            let d = val.as_ad_sum();
            unsafe {
                (*d).a = a;
                (*d).b = b;
                (*d).da = Field::ZERO;
                (*d).db = Field::ZERO;
                (*d).dc = Field::ZERO;
                *res = val;
            }
        }
        #[inline(never)]
        fn rangecheck(val: Field, max_bits: usize) {
            let bigint = ark_ff::PrimeField::into_bigint(val);
            let check = bigint.to_bits_le().iter().skip(max_bits).all(|b| !b);
            if !check {
                ::core::panicking::panic("assertion failed: check")
            }
        }
        #[inline(always)]
        fn to_bytes_be_lt_8(val: Field, count: u64, res: *mut BoxedValue, vm: &mut VM) {
            let val = ark_ff::PrimeField::into_bigint(val);
            let low = val.0[0];
            let r = BoxedValue::alloc(BoxedLayout::array(count as usize, false), vm);
            unsafe {
                for i in 0..count {
                    *r.array_idx((count - i - 1) as usize, 1) = (low >> (i * 8)) & 0xFF;
                }
                *res = r;
            }
        }
        #[inline(always)]
        fn to_bits_le(res: *mut BoxedValue, val: Field, count: u64, vm: &mut VM) {
            {
                ::core::panicking::panic_fmt(
                    format_args!("to_bits_be_lt_8 not implemented"),
                );
            };
        }
        #[inline(always)]
        fn rngchk_8_field(val: Field, vm: &mut VM) {
            if vm.rgchk_8.is_none() {
                let table_info = TableInfo {
                    multiplicities_wit: unsafe {
                        vm.data.as_forward.multiplicities_witness
                    },
                    num_indices: 1,
                    num_values: 0,
                    length: 256,
                    elem_inverses_constraint_section_offset: unsafe {
                        vm.data.as_forward.elem_inverses_constraint_section_offset
                    },
                    elem_inverses_witness_section_offset: unsafe {
                        vm.data.as_forward.elem_inverses_witness_section_offset
                    },
                };
                vm.rgchk_8 = Some(vm.tables.len());
                vm.tables.push(table_info);
                unsafe {
                    vm.data.as_forward.multiplicities_witness = vm
                        .data
                        .as_forward
                        .multiplicities_witness
                        .offset(256);
                    vm.data.as_forward.elem_inverses_constraint_section_offset += 257;
                    vm.data.as_forward.elem_inverses_witness_section_offset += 256;
                }
            }
            let table_idx = *vm.rgchk_8.as_ref().unwrap();
            let table_info = &vm.tables[table_idx];
            let val_u64 = ark_ff::PrimeField::into_bigint(val).0[0];
            unsafe {
                let ptr = table_info.multiplicities_wit.offset(val_u64 as isize);
                *(ptr as *mut u64) += 1;
                *(vm.data.as_forward.lookups_a as *mut u64) = table_idx as u64;
                vm.data.as_forward.lookups_a = vm.data.as_forward.lookups_a.offset(1);
                *(vm.data.as_forward.lookups_b as *mut u64) = val_u64;
                vm.data.as_forward.lookups_b = vm.data.as_forward.lookups_b.offset(1);
            }
        }
        #[inline(always)]
        fn drngchk_8_field(val: BoxedValue, vm: &mut VM) {
            if vm.rgchk_8.is_none() {
                let inverses_constraint_section_offset = unsafe {
                    vm.data.as_ad.current_cnst_tables_off
                };
                let inverses_witness_section_offset = unsafe {
                    vm.data.as_ad.current_wit_tables_off
                };
                let multiplicities_wit_offset = unsafe {
                    vm.data.as_ad.current_wit_multiplicities_off
                };
                let table_info = TableInfo {
                    multiplicities_wit: ptr::null_mut(),
                    num_indices: 1,
                    num_values: 0,
                    length: 256,
                    elem_inverses_witness_section_offset: inverses_witness_section_offset,
                    elem_inverses_constraint_section_offset: inverses_constraint_section_offset,
                };
                vm.rgchk_8 = Some(vm.tables.len());
                vm.tables.push(table_info);
                unsafe {
                    vm.data.as_ad.current_wit_multiplicities_off += 256;
                    vm.data.as_ad.current_wit_tables_off += 256;
                    vm.data.as_ad.current_cnst_tables_off += 257;
                }
                let inv_sum_coeff = unsafe {
                    *vm
                        .data
                        .as_ad
                        .ad_coeffs
                        .offset(inverses_constraint_section_offset as isize + 256)
                };
                for i in 0..256 {
                    let coeff = unsafe {
                        *vm
                            .data
                            .as_ad
                            .ad_coeffs
                            .offset(inverses_constraint_section_offset as isize + i)
                    };
                    unsafe {
                        *vm
                            .data
                            .as_ad
                            .out_da
                            .offset(inverses_witness_section_offset as isize + i)
                            += coeff;
                        *vm
                            .data
                            .as_ad
                            .out_db
                            .offset(vm.data.as_ad.logup_wit_challenge_off as isize)
                            += coeff;
                        *vm.data.as_ad.out_db -= coeff * Field::from(i as u64);
                        *vm
                            .data
                            .as_ad
                            .out_dc
                            .offset(multiplicities_wit_offset as isize + i) += coeff;
                    }
                    unsafe {
                        *vm
                            .data
                            .as_ad
                            .out_da
                            .offset(inverses_witness_section_offset as isize + i)
                            += inv_sum_coeff;
                    }
                }
                unsafe {
                    *vm.data.as_ad.out_db += inv_sum_coeff;
                }
            }
            let table_idx = *vm.rgchk_8.as_ref().unwrap();
            let table_info = &vm.tables[table_idx];
            let inv_coeff = unsafe {
                let r = *vm
                    .data
                    .as_ad
                    .ad_coeffs
                    .offset(vm.data.as_ad.current_cnst_lookups_off as isize);
                vm.data.as_ad.current_cnst_lookups_off += 1;
                r
            };
            let inv_sum_coeff = unsafe {
                *vm
                    .data
                    .as_ad
                    .ad_coeffs
                    .offset(
                        table_info.elem_inverses_constraint_section_offset as isize + 256,
                    )
            };
            let current_inv_wit_offset = unsafe {
                let r = vm.data.as_ad.current_wit_lookups_off;
                vm.data.as_ad.current_wit_lookups_off += 1;
                r
            };
            unsafe {
                *vm.data.as_ad.out_dc.offset(current_inv_wit_offset as isize)
                    += inv_sum_coeff;
                *vm.data.as_ad.out_da.offset(current_inv_wit_offset as isize)
                    += inv_coeff;
                *vm
                    .data
                    .as_ad
                    .out_db
                    .offset(vm.data.as_ad.logup_wit_challenge_off as isize) += inv_coeff;
                val.bump_db(-inv_coeff, vm);
                *vm.data.as_ad.out_dc += inv_coeff;
            }
        }
        pub fn jmp_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let target = unsafe {
                let r = JumpTarget(*pc.offset(current_field_offset) as isize);
                current_field_offset += 1;
                r
            };
            jmp(pc, frame, vm, target);
        }
        pub fn jmp_if_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let cond = unsafe {
                frame.read_u64(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "jmp_if",
                            cond,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let if_t = unsafe {
                let r = JumpTarget(*pc.offset(current_field_offset) as isize);
                current_field_offset += 1;
                r
            };
            let if_f = unsafe {
                let r = JumpTarget(*pc.offset(current_field_offset) as isize);
                current_field_offset += 1;
                r
            };
            jmp_if(pc, frame, vm, cond, if_t, if_f);
        }
        pub fn call_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let func = unsafe {
                let r = JumpTarget(*pc.offset(current_field_offset) as isize);
                current_field_offset += 1;
                r
            };
            let args = unsafe {
                let len = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                let r = std::slice::from_raw_parts(
                    pc.offset(current_field_offset) as *const _,
                    len,
                );
                current_field_offset += len as isize * 2isize;
                r
            };
            let ret = unsafe {
                let r = FramePosition(*pc.offset(current_field_offset) as usize);
                current_field_offset += 1;
                r
            };
            call(pc, frame, vm, func, args, ret);
        }
        pub fn ret_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            ret(pc, frame, vm);
        }
        pub fn r1c_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "r1c",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "r1c",
                            b,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let c = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "r1c",
                            c,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            r1c(pc, frame, vm, a, b, c);
        }
        pub fn write_witness_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let val = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "write_witness",
                            val,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            write_witness(pc, frame, vm, val);
        }
        pub fn nop_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            nop();
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn mov_const_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mov_const",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let val = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            mov_const(res, val);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn mov_frame_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let target = unsafe {
                let r = FramePosition(*pc.offset(current_field_offset) as usize);
                current_field_offset += 1;
                r
            };
            let source = unsafe {
                let r = FramePosition(*pc.offset(current_field_offset) as usize);
                current_field_offset += 1;
                r
            };
            let size = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            mov_frame(frame, target, source, size);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn write_ptr_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let ptr = unsafe {
                frame.read_ptr(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "write_ptr",
                            ptr,
                            "read_ptr",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let offset = unsafe {
                let r = *pc.offset(current_field_offset) as isize;
                current_field_offset += 1;
                r
            };
            let src = unsafe {
                let r = FramePosition(*pc.offset(current_field_offset) as usize);
                current_field_offset += 1;
                r
            };
            let size = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            write_ptr(frame, ptr, offset, src, size);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn add_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            add_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn sub_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            sub_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn div_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            div_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn mul_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            mul_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn and_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "and_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "and_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "and_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            and_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn not_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "not_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "not_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            not_u64(res, a);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn eq_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "eq_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "eq_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "eq_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            eq_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn lt_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "lt_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "lt_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "lt_u64",
                            b,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            lt_u64(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn truncate_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "truncate_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "truncate_u64",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let to_bits = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            truncate_u64(res, a, to_bits);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn truncate_f_to_u_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "truncate_f_to_u",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "truncate_f_to_u",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let to_bits = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            truncate_f_to_u(res, a, to_bits);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn add_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_field",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_field",
                            b,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            add_field(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn sub_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_field",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "sub_field",
                            b,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            sub_field(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn div_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_field",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "div_field",
                            b,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            div_field(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn mul_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_field",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_field",
                            b,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            mul_field(res, a, b);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn cast_field_to_u64_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "cast_field_to_u64",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "cast_field_to_u64",
                            a,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            cast_field_to_u64(res, a);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn cast_u64_to_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "cast_u64_to_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe { frame.read_u64(*pc.offset(current_field_offset) as isize) };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "cast_u64_to_field",
                            a,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            cast_u64_to_field(res, a);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn array_alloc_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_alloc",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let stride = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            let meta = unsafe {
                let r = BoxedLayout(*pc.offset(current_field_offset));
                current_field_offset += 1;
                r
            };
            let items = unsafe {
                let len = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                let r = std::slice::from_raw_parts(
                    pc.offset(current_field_offset) as *const _,
                    len,
                );
                current_field_offset += len as isize * 1isize;
                r
            };
            array_alloc(res, stride, meta, items, frame, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn array_get_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_u64_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_get",
                            res,
                            "read_u64_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let array = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_get",
                            array,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let index = unsafe {
                frame.read_u64(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_get",
                            index,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let stride = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            array_get(res, array, index, stride, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn array_set_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_set",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let array = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_set",
                            array,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let index = unsafe {
                frame.read_u64(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "array_set",
                            index,
                            "read_u64",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let source = unsafe {
                let r = FramePosition(*pc.offset(current_field_offset) as usize);
                current_field_offset += 1;
                r
            };
            let stride = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            array_set(res, array, index, source, stride, frame, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn inc_rc_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let array = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "inc_rc",
                            array,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let amount = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            inc_rc(array, amount);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn dec_rc_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let array = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "dec_rc",
                            array,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            dec_rc(array, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn boxed_field_alloc_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "boxed_field_alloc",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let data = unsafe {
                let r0 = *pc.offset(current_field_offset);
                let r1 = *pc.offset(current_field_offset + 1);
                let r2 = *pc.offset(current_field_offset + 2);
                let r3 = *pc.offset(current_field_offset + 3);
                current_field_offset += 4;
                ark_ff::Fp(ark_ff::BigInt([r0, r1, r2, r3]), std::marker::PhantomData)
            };
            boxed_field_alloc(res, data, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn bump_da_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let v = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_da",
                            v,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let coeff = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_da",
                            coeff,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            bump_da(v, coeff, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn bump_db_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let v = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_db",
                            v,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let coeff = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_db",
                            coeff,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            bump_db(v, coeff, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn bump_dc_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let v = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_dc",
                            v,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let coeff = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "bump_dc",
                            coeff,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            bump_dc(v, coeff, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn next_d_coeff_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let v = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "next_d_coeff",
                            v,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            next_d_coeff(v, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn fresh_witness_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "fresh_witness",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            fresh_witness(res, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn box_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "box_field",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let v = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "box_field",
                            v,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            box_field(res, v, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn unbox_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_field_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "unbox_field",
                            res,
                            "read_field_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let v = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "unbox_field",
                            v,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            unbox_field(res, v);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn mul_const_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_const",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let coeff = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_const",
                            coeff,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let v = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "mul_const",
                            v,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            mul_const(res, coeff, v, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn add_boxed_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_boxed",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let a = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_boxed",
                            a,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let b = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "add_boxed",
                            b,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            add_boxed(res, a, b, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn rangecheck_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let val = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "rangecheck",
                            val,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let max_bits = unsafe {
                let r = *pc.offset(current_field_offset) as usize;
                current_field_offset += 1;
                r
            };
            rangecheck(val, max_bits);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn to_bytes_be_lt_8_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let val = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "to_bytes_be_lt_8",
                            val,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let count = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "to_bytes_be_lt_8",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            to_bytes_be_lt_8(val, count, res, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn to_bits_le_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let res = unsafe {
                frame.read_array_mut(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "to_bits_le",
                            res,
                            "read_array_mut",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let val = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "to_bits_le",
                            val,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            let count = unsafe {
                let r = *pc.offset(current_field_offset);
                current_field_offset += 1;
                r
            };
            to_bits_le(res, val, count, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn rngchk_8_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let val = unsafe {
                frame.read_field(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "rngchk_8_field",
                            val,
                            "read_field",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            rngchk_8_field(val, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub fn drngchk_8_field_handler(pc: *const u64, frame: Frame, vm: &mut VM) {
            let mut current_field_offset = 1isize;
            let val = unsafe {
                frame.read_array(*pc.offset(current_field_offset) as isize)
            };
            unsafe {
                {
                    ::std::io::_print(
                        format_args!(
                            "{0:?} {1:?} {2:?} {3:?} {4:?}\n",
                            "drngchk_8_field",
                            val,
                            "read_array",
                            *pc.offset(current_field_offset),
                            current_field_offset,
                        ),
                    );
                }
            };
            current_field_offset += 1;
            drngchk_8_field(val, vm);
            let pc = unsafe { pc.offset(current_field_offset) };
            dispatch(pc, frame, vm)
        }
        pub enum OpCode {
            Jmp { target: JumpTarget },
            JmpIf { cond: FramePosition, if_t: JumpTarget, if_f: JumpTarget },
            Call {
                func: JumpTarget,
                args: Vec<(usize, FramePosition)>,
                ret: FramePosition,
            },
            Ret {},
            R1C { a: FramePosition, b: FramePosition, c: FramePosition },
            WriteWitness { val: FramePosition },
            Nop {},
            MovConst { res: FramePosition, val: u64 },
            MovFrame { target: FramePosition, source: FramePosition, size: usize },
            WritePtr {
                ptr: FramePosition,
                offset: isize,
                src: FramePosition,
                size: usize,
            },
            AddU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            SubU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            DivU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            MulU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            AndU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            NotU64 { res: FramePosition, a: FramePosition },
            EqU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            LtU64 { res: FramePosition, a: FramePosition, b: FramePosition },
            TruncateU64 { res: FramePosition, a: FramePosition, to_bits: u64 },
            TruncateFToU { res: FramePosition, a: FramePosition, to_bits: u64 },
            AddField { res: FramePosition, a: FramePosition, b: FramePosition },
            SubField { res: FramePosition, a: FramePosition, b: FramePosition },
            DivField { res: FramePosition, a: FramePosition, b: FramePosition },
            MulField { res: FramePosition, a: FramePosition, b: FramePosition },
            CastFieldToU64 { res: FramePosition, a: FramePosition },
            CastU64ToField { res: FramePosition, a: FramePosition },
            ArrayAlloc {
                res: FramePosition,
                stride: usize,
                meta: BoxedLayout,
                items: Vec<FramePosition>,
            },
            ArrayGet {
                res: FramePosition,
                array: FramePosition,
                index: FramePosition,
                stride: usize,
            },
            ArraySet {
                res: FramePosition,
                array: FramePosition,
                index: FramePosition,
                source: FramePosition,
                stride: usize,
            },
            IncRc { array: FramePosition, amount: u64 },
            DecRc { array: FramePosition },
            BoxedFieldAlloc { res: FramePosition, data: Field },
            BumpDa { v: FramePosition, coeff: FramePosition },
            BumpDb { v: FramePosition, coeff: FramePosition },
            BumpDc { v: FramePosition, coeff: FramePosition },
            NextDCoeff { v: FramePosition },
            FreshWitness { res: FramePosition },
            BoxField { res: FramePosition, v: FramePosition },
            UnboxField { res: FramePosition, v: FramePosition },
            MulConst { res: FramePosition, coeff: FramePosition, v: FramePosition },
            AddBoxed { res: FramePosition, a: FramePosition, b: FramePosition },
            Rangecheck { val: FramePosition, max_bits: usize },
            ToBytesBeLt8 { val: FramePosition, count: u64, res: FramePosition },
            ToBitsLe { res: FramePosition, val: FramePosition, count: u64 },
            Rngchk8Field { val: FramePosition },
            Drngchk8Field { val: FramePosition },
        }
        impl OpCode {
            pub fn to_binary(
                &self,
                binary: &mut Vec<u64>,
                jumps_to_fix: &mut Vec<(usize, isize)>,
            ) {
                match self {
                    Self::Jmp { target } => {
                        binary.push(0u64);
                        let mut init_offset = -1isize;
                        jumps_to_fix.push((binary.len(), init_offset));
                        binary.push(target.0 as u64);
                        init_offset -= 1;
                    }
                    Self::JmpIf { cond, if_t, if_f } => {
                        binary.push(1u64);
                        let mut init_offset = -1isize;
                        binary.push(cond.0 as u64);
                        init_offset -= 1;
                        jumps_to_fix.push((binary.len(), init_offset));
                        binary.push(if_t.0 as u64);
                        init_offset -= 1;
                        jumps_to_fix.push((binary.len(), init_offset));
                        binary.push(if_f.0 as u64);
                        init_offset -= 1;
                    }
                    Self::Call { func, args, ret } => {
                        binary.push(2u64);
                        let mut init_offset = -1isize;
                        jumps_to_fix.push((binary.len(), init_offset));
                        binary.push(func.0 as u64);
                        init_offset -= 1;
                        binary.push(args.len() as u64);
                        init_offset -= 1;
                        for elem in args {
                            binary.push(elem.0 as u64);
                            init_offset -= 1;
                            binary.push(elem.1.0 as u64);
                            init_offset -= 1;
                        }
                        binary.push(ret.0 as u64);
                        init_offset -= 1;
                    }
                    Self::Ret {} => {
                        binary.push(3u64);
                        let mut init_offset = -1isize;
                    }
                    Self::R1C { a, b, c } => {
                        binary.push(4u64);
                        let mut init_offset = -1isize;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                        binary.push(c.0 as u64);
                        init_offset -= 1;
                    }
                    Self::WriteWitness { val } => {
                        binary.push(5u64);
                        let mut init_offset = -1isize;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                    }
                    Self::Nop {} => {
                        binary.push(6u64);
                        let mut init_offset = -1isize;
                    }
                    Self::MovConst { res, val } => {
                        binary.push(7u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(*val);
                        init_offset -= 1;
                    }
                    Self::MovFrame { target, source, size } => {
                        binary.push(8u64);
                        let mut init_offset = -1isize;
                        binary.push(target.0 as u64);
                        init_offset -= 1;
                        binary.push(source.0 as u64);
                        init_offset -= 1;
                        binary.push(*size as u64);
                        init_offset -= 1;
                    }
                    Self::WritePtr { ptr, offset, src, size } => {
                        binary.push(9u64);
                        let mut init_offset = -1isize;
                        binary.push(ptr.0 as u64);
                        init_offset -= 1;
                        binary.push(*offset as u64);
                        init_offset -= 1;
                        binary.push(src.0 as u64);
                        init_offset -= 1;
                        binary.push(*size as u64);
                        init_offset -= 1;
                    }
                    Self::AddU64 { res, a, b } => {
                        binary.push(10u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::SubU64 { res, a, b } => {
                        binary.push(11u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::DivU64 { res, a, b } => {
                        binary.push(12u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::MulU64 { res, a, b } => {
                        binary.push(13u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::AndU64 { res, a, b } => {
                        binary.push(14u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::NotU64 { res, a } => {
                        binary.push(15u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                    }
                    Self::EqU64 { res, a, b } => {
                        binary.push(16u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::LtU64 { res, a, b } => {
                        binary.push(17u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::TruncateU64 { res, a, to_bits } => {
                        binary.push(18u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(*to_bits);
                        init_offset -= 1;
                    }
                    Self::TruncateFToU { res, a, to_bits } => {
                        binary.push(19u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(*to_bits);
                        init_offset -= 1;
                    }
                    Self::AddField { res, a, b } => {
                        binary.push(20u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::SubField { res, a, b } => {
                        binary.push(21u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::DivField { res, a, b } => {
                        binary.push(22u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::MulField { res, a, b } => {
                        binary.push(23u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::CastFieldToU64 { res, a } => {
                        binary.push(24u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                    }
                    Self::CastU64ToField { res, a } => {
                        binary.push(25u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                    }
                    Self::ArrayAlloc { res, stride, meta, items } => {
                        binary.push(26u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(*stride as u64);
                        init_offset -= 1;
                        binary.push(meta.0);
                        init_offset -= 1;
                        binary.push(items.len() as u64);
                        init_offset -= 1;
                        for elem in items {
                            binary.push(elem.0 as u64);
                            init_offset -= 1;
                        }
                    }
                    Self::ArrayGet { res, array, index, stride } => {
                        binary.push(27u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(array.0 as u64);
                        init_offset -= 1;
                        binary.push(index.0 as u64);
                        init_offset -= 1;
                        binary.push(*stride as u64);
                        init_offset -= 1;
                    }
                    Self::ArraySet { res, array, index, source, stride } => {
                        binary.push(28u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(array.0 as u64);
                        init_offset -= 1;
                        binary.push(index.0 as u64);
                        init_offset -= 1;
                        binary.push(source.0 as u64);
                        init_offset -= 1;
                        binary.push(*stride as u64);
                        init_offset -= 1;
                    }
                    Self::IncRc { array, amount } => {
                        binary.push(29u64);
                        let mut init_offset = -1isize;
                        binary.push(array.0 as u64);
                        init_offset -= 1;
                        binary.push(*amount);
                        init_offset -= 1;
                    }
                    Self::DecRc { array } => {
                        binary.push(30u64);
                        let mut init_offset = -1isize;
                        binary.push(array.0 as u64);
                        init_offset -= 1;
                    }
                    Self::BoxedFieldAlloc { res, data } => {
                        binary.push(31u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(data.0.0[0] as u64);
                        binary.push(data.0.0[1] as u64);
                        binary.push(data.0.0[2] as u64);
                        binary.push(data.0.0[3] as u64);
                        init_offset -= 1;
                    }
                    Self::BumpDa { v, coeff } => {
                        binary.push(32u64);
                        let mut init_offset = -1isize;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                        binary.push(coeff.0 as u64);
                        init_offset -= 1;
                    }
                    Self::BumpDb { v, coeff } => {
                        binary.push(33u64);
                        let mut init_offset = -1isize;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                        binary.push(coeff.0 as u64);
                        init_offset -= 1;
                    }
                    Self::BumpDc { v, coeff } => {
                        binary.push(34u64);
                        let mut init_offset = -1isize;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                        binary.push(coeff.0 as u64);
                        init_offset -= 1;
                    }
                    Self::NextDCoeff { v } => {
                        binary.push(35u64);
                        let mut init_offset = -1isize;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                    }
                    Self::FreshWitness { res } => {
                        binary.push(36u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                    }
                    Self::BoxField { res, v } => {
                        binary.push(37u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                    }
                    Self::UnboxField { res, v } => {
                        binary.push(38u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                    }
                    Self::MulConst { res, coeff, v } => {
                        binary.push(39u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(coeff.0 as u64);
                        init_offset -= 1;
                        binary.push(v.0 as u64);
                        init_offset -= 1;
                    }
                    Self::AddBoxed { res, a, b } => {
                        binary.push(40u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(a.0 as u64);
                        init_offset -= 1;
                        binary.push(b.0 as u64);
                        init_offset -= 1;
                    }
                    Self::Rangecheck { val, max_bits } => {
                        binary.push(41u64);
                        let mut init_offset = -1isize;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                        binary.push(*max_bits as u64);
                        init_offset -= 1;
                    }
                    Self::ToBytesBeLt8 { val, count, res } => {
                        binary.push(42u64);
                        let mut init_offset = -1isize;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                        binary.push(*count);
                        init_offset -= 1;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                    }
                    Self::ToBitsLe { res, val, count } => {
                        binary.push(43u64);
                        let mut init_offset = -1isize;
                        binary.push(res.0 as u64);
                        init_offset -= 1;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                        binary.push(*count);
                        init_offset -= 1;
                    }
                    Self::Rngchk8Field { val } => {
                        binary.push(44u64);
                        let mut init_offset = -1isize;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                    }
                    Self::Drngchk8Field { val } => {
                        binary.push(45u64);
                        let mut init_offset = -1isize;
                        binary.push(val.0 as u64);
                        init_offset -= 1;
                    }
                }
            }
            pub fn next_opcode(binary: &[u64], mut ix: usize) -> usize {
                let op_code = binary[ix];
                ix += 1;
                match op_code {
                    0u64 => {
                        ix += 1;
                    }
                    1u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    2u64 => {
                        ix += 1;
                        {
                            let len = binary[ix] as usize;
                            ix += 1;
                            ix += len * 2usize;
                        };
                        ix += 1;
                    }
                    3u64 => {}
                    4u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    5u64 => {
                        ix += 1;
                    }
                    6u64 => {}
                    7u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    8u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    9u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    10u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    11u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    12u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    13u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    14u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    15u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    16u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    17u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    18u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    19u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    20u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    21u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    22u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    23u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    24u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    25u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    26u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                        {
                            let len = binary[ix] as usize;
                            ix += 1;
                            ix += len * 1usize;
                        };
                    }
                    27u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    28u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    29u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    30u64 => {
                        ix += 1;
                    }
                    31u64 => {
                        ix += 1;
                        ix += 4;
                    }
                    32u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    33u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    34u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    35u64 => {
                        ix += 1;
                    }
                    36u64 => {
                        ix += 1;
                    }
                    37u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    38u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    39u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    40u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    41u64 => {
                        ix += 1;
                        ix += 1;
                    }
                    42u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    43u64 => {
                        ix += 1;
                        ix += 1;
                        ix += 1;
                    }
                    44u64 => {
                        ix += 1;
                    }
                    45u64 => {
                        ix += 1;
                    }
                    _ => {
                        ::core::panicking::panic_fmt(format_args!("unknown opcode"));
                    }
                }
                ix
            }
        }
        impl std::fmt::Display for OpCode {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    OpCode::Jmp { target } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1}", fields, target.0),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "jmp", fields)).unwrap();
                    }
                    OpCode::JmpIf { cond, if_t, if_f } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, cond.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, if_t.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, if_f.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "jmp_if", fields)).unwrap();
                    }
                    OpCode::Call { func, args, ret } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, func.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} _", fields))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, ret.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "call", fields)).unwrap();
                    }
                    OpCode::Ret {} => {
                        let mut fields = String::new();
                        f.write_fmt(format_args!("{0}{1}", "ret", fields)).unwrap();
                    }
                    OpCode::R1C { a, b, c } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, c.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "r1c", fields)).unwrap();
                    }
                    OpCode::WriteWitness { val } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "write_witness", fields))
                            .unwrap();
                    }
                    OpCode::Nop {} => {
                        let mut fields = String::new();
                        f.write_fmt(format_args!("{0}{1}", "nop", fields)).unwrap();
                    }
                    OpCode::MovConst { res, val } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, val))
                        });
                        f.write_fmt(format_args!("{0}{1}", "mov_const", fields))
                            .unwrap();
                    }
                    OpCode::MovFrame { target, source, size } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, target.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, source.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, size))
                        });
                        f.write_fmt(format_args!("{0}{1}", "mov_frame", fields))
                            .unwrap();
                    }
                    OpCode::WritePtr { ptr, offset, src, size } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, ptr.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, offset))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, src.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, size))
                        });
                        f.write_fmt(format_args!("{0}{1}", "write_ptr", fields))
                            .unwrap();
                    }
                    OpCode::AddU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "add_u64", fields)).unwrap();
                    }
                    OpCode::SubU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "sub_u64", fields)).unwrap();
                    }
                    OpCode::DivU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "div_u64", fields)).unwrap();
                    }
                    OpCode::MulU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "mul_u64", fields)).unwrap();
                    }
                    OpCode::AndU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "and_u64", fields)).unwrap();
                    }
                    OpCode::NotU64 { res, a } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "not_u64", fields)).unwrap();
                    }
                    OpCode::EqU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "eq_u64", fields)).unwrap();
                    }
                    OpCode::LtU64 { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "lt_u64", fields)).unwrap();
                    }
                    OpCode::TruncateU64 { res, a, to_bits } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1}", fields, to_bits),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "truncate_u64", fields))
                            .unwrap();
                    }
                    OpCode::TruncateFToU { res, a, to_bits } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1}", fields, to_bits),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "truncate_f_to_u", fields))
                            .unwrap();
                    }
                    OpCode::AddField { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "add_field", fields))
                            .unwrap();
                    }
                    OpCode::SubField { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "sub_field", fields))
                            .unwrap();
                    }
                    OpCode::DivField { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "div_field", fields))
                            .unwrap();
                    }
                    OpCode::MulField { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "mul_field", fields))
                            .unwrap();
                    }
                    OpCode::CastFieldToU64 { res, a } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "cast_field_to_u64", fields))
                            .unwrap();
                    }
                    OpCode::CastU64ToField { res, a } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "cast_u64_to_field", fields))
                            .unwrap();
                    }
                    OpCode::ArrayAlloc { res, stride, meta, items } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, stride))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} _", fields))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} _", fields))
                        });
                        f.write_fmt(format_args!("{0}{1}", "array_alloc", fields))
                            .unwrap();
                    }
                    OpCode::ArrayGet { res, array, index, stride } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, array.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, index.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, stride))
                        });
                        f.write_fmt(format_args!("{0}{1}", "array_get", fields))
                            .unwrap();
                    }
                    OpCode::ArraySet { res, array, index, source, stride } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, array.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, index.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, source.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, stride))
                        });
                        f.write_fmt(format_args!("{0}{1}", "array_set", fields))
                            .unwrap();
                    }
                    OpCode::IncRc { array, amount } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, array.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, amount))
                        });
                        f.write_fmt(format_args!("{0}{1}", "inc_rc", fields)).unwrap();
                    }
                    OpCode::DecRc { array } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, array.0),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "dec_rc", fields)).unwrap();
                    }
                    OpCode::BoxedFieldAlloc { res, data } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, data))
                        });
                        f.write_fmt(format_args!("{0}{1}", "boxed_field_alloc", fields))
                            .unwrap();
                    }
                    OpCode::BumpDa { v, coeff } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, coeff.0),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "bump_da", fields)).unwrap();
                    }
                    OpCode::BumpDb { v, coeff } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, coeff.0),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "bump_db", fields)).unwrap();
                    }
                    OpCode::BumpDc { v, coeff } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, coeff.0),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "bump_dc", fields)).unwrap();
                    }
                    OpCode::NextDCoeff { v } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "next_d_coeff", fields))
                            .unwrap();
                    }
                    OpCode::FreshWitness { res } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "fresh_witness", fields))
                            .unwrap();
                    }
                    OpCode::BoxField { res, v } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "box_field", fields))
                            .unwrap();
                    }
                    OpCode::UnboxField { res, v } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "unbox_field", fields))
                            .unwrap();
                    }
                    OpCode::MulConst { res, coeff, v } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} %{1}", fields, coeff.0),
                            )
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, v.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "mul_const", fields))
                            .unwrap();
                    }
                    OpCode::AddBoxed { res, a, b } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, a.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, b.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "add_boxed", fields))
                            .unwrap();
                    }
                    OpCode::Rangecheck { val, max_bits } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1}", fields, max_bits),
                            )
                        });
                        f.write_fmt(format_args!("{0}{1}", "rangecheck", fields))
                            .unwrap();
                    }
                    OpCode::ToBytesBeLt8 { val, count, res } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, count))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "to_bytes_be_lt_8", fields))
                            .unwrap();
                    }
                    OpCode::ToBitsLe { res, val, count } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, res.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} {1}", fields, count))
                        });
                        f.write_fmt(format_args!("{0}{1}", "to_bits_le", fields))
                            .unwrap();
                    }
                    OpCode::Rngchk8Field { val } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "rngchk_8_field", fields))
                            .unwrap();
                    }
                    OpCode::Drngchk8Field { val } => {
                        let mut fields = String::new();
                        fields = ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} %{1}", fields, val.0))
                        });
                        f.write_fmt(format_args!("{0}{1}", "drngchk_8_field", fields))
                            .unwrap();
                    }
                }
                Ok(())
            }
        }
        pub const DISPATCH: [Handler; 46usize] = [
            jmp_handler,
            jmp_if_handler,
            call_handler,
            ret_handler,
            r1c_handler,
            write_witness_handler,
            nop_handler,
            mov_const_handler,
            mov_frame_handler,
            write_ptr_handler,
            add_u64_handler,
            sub_u64_handler,
            div_u64_handler,
            mul_u64_handler,
            and_u64_handler,
            not_u64_handler,
            eq_u64_handler,
            lt_u64_handler,
            truncate_u64_handler,
            truncate_f_to_u_handler,
            add_field_handler,
            sub_field_handler,
            div_field_handler,
            mul_field_handler,
            cast_field_to_u64_handler,
            cast_u64_to_field_handler,
            array_alloc_handler,
            array_get_handler,
            array_set_handler,
            inc_rc_handler,
            dec_rc_handler,
            boxed_field_alloc_handler,
            bump_da_handler,
            bump_db_handler,
            bump_dc_handler,
            next_d_coeff_handler,
            fresh_witness_handler,
            box_field_handler,
            unbox_field_handler,
            mul_const_handler,
            add_boxed_handler,
            rangecheck_handler,
            to_bytes_be_lt_8_handler,
            to_bits_le_handler,
            rngchk_8_field_handler,
            drngchk_8_field_handler,
        ];
        pub struct Function {
            pub name: String,
            pub frame_size: usize,
            pub code: Vec<OpCode>,
        }
        impl Display for Function {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_fmt(
                    format_args!(
                        "fn {0} (frame_size = {1}):\n",
                        self.name,
                        self.frame_size,
                    ),
                )?;
                for op in &self.code {
                    f.write_fmt(format_args!("  {0}\n", op))?;
                }
                Ok(())
            }
        }
        pub struct Program {
            pub functions: Vec<Function>,
        }
        impl Display for Program {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let max_line_number: usize = self
                    .functions
                    .iter()
                    .map(|f| f.code.len())
                    .sum::<usize>() - 1;
                let max_line_number_digits = max_line_number.to_string().len();
                let max_function_idx = self.functions.len().to_string().len() - 1;
                let max_function_idx_digits = max_function_idx.to_string().len();
                let mut line = 0;
                for (i, function) in self.functions.iter().enumerate() {
                    f.write_fmt(
                        format_args!(
                            "{0: >3$}: fn {1} (frame_size = {2})\n",
                            i,
                            function.name,
                            function.frame_size,
                            max_function_idx_digits,
                        ),
                    )?;
                    for op in &function.code {
                        f.write_fmt(
                            format_args!(
                                "  {0: >2$}: {1}\n",
                                line,
                                op,
                                max_line_number_digits,
                            ),
                        )?;
                        line += 1;
                    }
                }
                Ok(())
            }
        }
        impl Program {
            pub fn to_binary(&self) -> Vec<u64> {
                let mut binary = Vec::new();
                let mut positions = ::alloc::vec::Vec::new();
                let mut jumps_to_fix: Vec<(usize, isize)> = ::alloc::vec::Vec::new();
                for function in &self.functions {
                    binary.push(u64::MAX);
                    binary.push(function.frame_size as u64);
                    for op in &function.code {
                        positions.push(binary.len());
                        op.to_binary(&mut binary, &mut jumps_to_fix);
                    }
                }
                for (jump_position, add_offset) in jumps_to_fix {
                    let target = binary[jump_position];
                    let target_pos = positions[target as usize];
                    binary[jump_position] = (target_pos as isize
                        - (jump_position as isize + add_offset)) as u64;
                }
                binary
            }
        }
    }
    pub mod array {
        use std::{
            alloc::{self, Layout},
            collections::VecDeque, ptr,
        };
        use crate::{compiler::Field, vm::bytecode::{AllocationType, VM}};
        pub struct BoxedLayout(pub u64);
        #[automatically_derived]
        impl ::core::fmt::Debug for BoxedLayout {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                ::core::fmt::Formatter::debug_tuple_field1_finish(
                    f,
                    "BoxedLayout",
                    &&self.0,
                )
            }
        }
        #[automatically_derived]
        impl ::core::clone::Clone for BoxedLayout {
            #[inline]
            fn clone(&self) -> BoxedLayout {
                let _: ::core::clone::AssertParamIsClone<u64>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for BoxedLayout {}
        pub enum DataType {
            PrimArray = 0,
            BoxedArray = 1,
            ADConst = 2,
            ADWitness = 3,
            ADSum = 4,
            ADMulConst = 5,
        }
        #[automatically_derived]
        impl ::core::fmt::Debug for DataType {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                ::core::fmt::Formatter::write_str(
                    f,
                    match self {
                        DataType::PrimArray => "PrimArray",
                        DataType::BoxedArray => "BoxedArray",
                        DataType::ADConst => "ADConst",
                        DataType::ADWitness => "ADWitness",
                        DataType::ADSum => "ADSum",
                        DataType::ADMulConst => "ADMulConst",
                    },
                )
            }
        }
        #[automatically_derived]
        impl ::core::clone::Clone for DataType {
            #[inline]
            fn clone(&self) -> DataType {
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataType {}
        #[automatically_derived]
        impl ::core::cmp::Eq for DataType {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for DataType {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for DataType {
            #[inline]
            fn eq(&self, other: &DataType) -> bool {
                let __self_discr = ::core::intrinsics::discriminant_value(self);
                let __arg1_discr = ::core::intrinsics::discriminant_value(other);
                __self_discr == __arg1_discr
            }
        }
        impl BoxedLayout {
            fn new_sized(data_type: DataType, size: usize) -> Self {
                if !(size < (1 << 56)) {
                    ::core::panicking::panic("assertion failed: size < (1 << 56)")
                }
                Self(data_type as u64 | ((size as u64) << 8))
            }
            fn new(data_type: DataType) -> Self {
                Self(data_type as u64)
            }
            pub fn array(size: usize, ptr_elems: bool) -> Self {
                if !(size < (1 << 56)) {
                    ::core::panicking::panic("assertion failed: size < (1 << 56)")
                }
                if ptr_elems {
                    Self::new_sized(DataType::BoxedArray, size)
                } else {
                    Self::new_sized(DataType::PrimArray, size)
                }
            }
            pub fn ad_const() -> Self {
                Self::new(DataType::ADConst)
            }
            pub fn ad_witness() -> Self {
                Self::new(DataType::ADWitness)
            }
            pub fn mul_const() -> Self {
                Self::new(DataType::ADMulConst)
            }
            pub fn ad_sum() -> Self {
                Self::new(DataType::ADSum)
            }
            pub fn data_type(&self) -> DataType {
                let disciminator = self.0 as u8;
                unsafe { std::mem::transmute(disciminator) }
            }
            pub fn array_size(&self) -> usize {
                self.0 as usize >> 8
            }
            pub fn is_boxed_array(&self) -> bool {
                self.data_type() == DataType::BoxedArray
            }
            pub fn is_prim_array(&self) -> bool {
                self.data_type() == DataType::PrimArray
            }
            pub fn underlying_array_size(&self) -> usize {
                let base_byte_size = match self.data_type() {
                    DataType::ADConst => size_of::<ADConst>(),
                    DataType::ADWitness => size_of::<ADWitness>(),
                    DataType::ADMulConst => size_of::<ADMulConst>(),
                    DataType::ADSum => size_of::<ADSum>(),
                    DataType::BoxedArray | DataType::PrimArray => 8 * self.array_size(),
                };
                let arr_size = ((base_byte_size + 7) / 8) + 2;
                arr_size
            }
        }
        pub struct ADConst {
            pub value: Field,
        }
        #[automatically_derived]
        impl ::core::clone::Clone for ADConst {
            #[inline]
            fn clone(&self) -> ADConst {
                let _: ::core::clone::AssertParamIsClone<Field>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ADConst {}
        pub struct ADWitness {
            pub index: u64,
        }
        #[automatically_derived]
        impl ::core::clone::Clone for ADWitness {
            #[inline]
            fn clone(&self) -> ADWitness {
                let _: ::core::clone::AssertParamIsClone<u64>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ADWitness {}
        pub struct ADMulConst {
            pub coeff: Field,
            pub value: BoxedValue,
            pub da: Field,
            pub db: Field,
            pub dc: Field,
        }
        #[automatically_derived]
        impl ::core::clone::Clone for ADMulConst {
            #[inline]
            fn clone(&self) -> ADMulConst {
                let _: ::core::clone::AssertParamIsClone<Field>;
                let _: ::core::clone::AssertParamIsClone<BoxedValue>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ADMulConst {}
        pub struct ADSum {
            pub a: BoxedValue,
            pub b: BoxedValue,
            pub da: Field,
            pub db: Field,
            pub dc: Field,
        }
        #[automatically_derived]
        impl ::core::clone::Clone for ADSum {
            #[inline]
            fn clone(&self) -> ADSum {
                let _: ::core::clone::AssertParamIsClone<BoxedValue>;
                let _: ::core::clone::AssertParamIsClone<Field>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ADSum {}
        pub struct BoxedValue(pub *mut u64);
        #[automatically_derived]
        impl ::core::clone::Clone for BoxedValue {
            #[inline]
            fn clone(&self) -> BoxedValue {
                let _: ::core::clone::AssertParamIsClone<*mut u64>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for BoxedValue {}
        #[automatically_derived]
        impl ::core::fmt::Debug for BoxedValue {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                ::core::fmt::Formatter::debug_tuple_field1_finish(
                    f,
                    "BoxedValue",
                    &&self.0,
                )
            }
        }
        impl BoxedValue {
            pub fn alloc(layout: BoxedLayout, vm: &mut VM) -> Self {
                let arr_size = layout.underlying_array_size();
                let ptr = unsafe {
                    alloc::alloc(Layout::array::<u64>(arr_size).unwrap())
                } as *mut u64;
                vm.allocation_instrumenter.alloc(AllocationType::Heap, arr_size);
                unsafe {
                    *ptr = layout.0;
                    *ptr.offset(1) = 1;
                }
                Self(ptr)
            }
            fn rc(&self) -> *mut u64 {
                unsafe { self.0.offset(1) }
            }
            pub fn layout(&self) -> BoxedLayout {
                unsafe { *(self.0 as *mut BoxedLayout) }
            }
            fn data(&self) -> *mut u64 {
                unsafe { self.0.offset(2) }
            }
            pub fn as_ad_const(&self) -> *mut ADConst {
                self.data() as *mut ADConst
            }
            pub fn as_ad_witness(&self) -> *mut ADWitness {
                self.data() as *mut ADWitness
            }
            pub fn as_mul_const(&self) -> *mut ADMulConst {
                self.data() as *mut ADMulConst
            }
            pub fn as_ad_sum(&self) -> *mut ADSum {
                self.data() as *mut ADSum
            }
            #[inline(always)]
            pub fn bump_da(&self, amount: Field, vm: &mut VM) {
                match self.layout().data_type() {
                    DataType::ADConst => {
                        unsafe {
                            *vm.data.as_ad.out_da += amount * (*self.as_ad_const()).value
                        }
                    }
                    DataType::ADWitness => {
                        unsafe {
                            *vm
                                .data
                                .as_ad
                                .out_da
                                .offset((*self.as_ad_witness()).index as isize) += amount
                        }
                    }
                    DataType::ADSum => {
                        unsafe {
                            let ad_sum = self.as_ad_sum();
                            (*ad_sum).da += amount;
                        }
                    }
                    DataType::ADMulConst => {
                        unsafe {
                            let ad_mul_const = self.as_mul_const();
                            (*ad_mul_const).da += amount;
                        }
                    }
                    DataType::PrimArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_da for PrimArray"),
                        );
                    }
                    DataType::BoxedArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_da for BoxedArray"),
                        );
                    }
                }
            }
            #[inline(always)]
            pub fn bump_db(&self, amount: Field, vm: &mut VM) {
                match self.layout().data_type() {
                    DataType::ADConst => {
                        unsafe {
                            *vm.data.as_ad.out_db += amount * (*self.as_ad_const()).value
                        }
                    }
                    DataType::ADWitness => {
                        unsafe {
                            *vm
                                .data
                                .as_ad
                                .out_db
                                .offset((*self.as_ad_witness()).index as isize) += amount
                        }
                    }
                    DataType::ADSum => {
                        unsafe {
                            let ad_sum = self.as_ad_sum();
                            (*ad_sum).db += amount;
                        }
                    }
                    DataType::ADMulConst => {
                        unsafe {
                            let ad_mul_const = self.as_mul_const();
                            (*ad_mul_const).db += amount;
                        }
                    }
                    DataType::PrimArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_db for PrimArray"),
                        );
                    }
                    DataType::BoxedArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_da for BoxedArray"),
                        );
                    }
                }
            }
            #[inline(always)]
            pub fn bump_dc(&self, amount: Field, vm: &mut VM) {
                match self.layout().data_type() {
                    DataType::ADConst => {
                        unsafe {
                            *vm.data.as_ad.out_dc += amount * (*self.as_ad_const()).value
                        }
                    }
                    DataType::ADWitness => {
                        unsafe {
                            *vm
                                .data
                                .as_ad
                                .out_dc
                                .offset((*self.as_ad_witness()).index as isize) += amount
                        }
                    }
                    DataType::ADSum => {
                        unsafe {
                            let ad_sum = self.as_ad_sum();
                            (*ad_sum).dc += amount;
                        }
                    }
                    DataType::ADMulConst => {
                        unsafe {
                            let ad_mul_const = self.as_mul_const();
                            (*ad_mul_const).dc += amount;
                        }
                    }
                    DataType::PrimArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_dc for PrimArray"),
                        );
                    }
                    DataType::BoxedArray => {
                        ::core::panicking::panic_fmt(
                            format_args!("bump_dc for BoxedArray"),
                        );
                    }
                }
            }
            pub fn array_idx(&self, idx: usize, stride: usize) -> *mut u64 {
                unsafe { self.data().offset(idx as isize * stride as isize) }
            }
            pub fn inc_rc(&self, by: u64) {
                let rc = self.rc();
                unsafe {
                    *rc += by;
                }
            }
            fn free(&self, vm: &mut VM) {
                let arr_size = self.layout().underlying_array_size();
                unsafe {
                    alloc::dealloc(
                        self.0 as *mut u8,
                        Layout::array::<u64>(arr_size).unwrap(),
                    );
                    vm.allocation_instrumenter.free(AllocationType::Heap, arr_size);
                }
            }
            pub fn dec_rc(&self, vm: &mut VM) {
                let mut queue = VecDeque::<BoxedValue>::new();
                queue.push_back(*self);
                while let Some(item) = queue.pop_front() {
                    let rc = item.rc();
                    let rc_val = unsafe { *rc };
                    if rc_val == 1 {
                        let layout = item.layout();
                        match layout.data_type() {
                            DataType::PrimArray => item.free(vm),
                            DataType::BoxedArray => {
                                for i in 0..layout.array_size() {
                                    let elem = unsafe {
                                        *(item.array_idx(i, 1) as *mut BoxedValue)
                                    };
                                    queue.push_back(elem);
                                }
                                item.free(vm);
                            }
                            DataType::ADConst => {
                                item.free(vm);
                            }
                            DataType::ADWitness => {
                                item.free(vm);
                            }
                            DataType::ADSum => {
                                let ad_sum = unsafe { *item.as_ad_sum() };
                                ad_sum.a.bump_da(ad_sum.da, vm);
                                ad_sum.a.bump_db(ad_sum.db, vm);
                                ad_sum.a.bump_dc(ad_sum.dc, vm);
                                ad_sum.b.bump_da(ad_sum.da, vm);
                                ad_sum.b.bump_db(ad_sum.db, vm);
                                ad_sum.b.bump_dc(ad_sum.dc, vm);
                                queue.push_back(ad_sum.a);
                                queue.push_back(ad_sum.b);
                                item.free(vm);
                            }
                            DataType::ADMulConst => {
                                let ad_mul_const = unsafe { *item.as_mul_const() };
                                ad_mul_const
                                    .value
                                    .bump_da(ad_mul_const.da * ad_mul_const.coeff, vm);
                                ad_mul_const
                                    .value
                                    .bump_db(ad_mul_const.db * ad_mul_const.coeff, vm);
                                ad_mul_const
                                    .value
                                    .bump_dc(ad_mul_const.dc * ad_mul_const.coeff, vm);
                                queue.push_back(ad_mul_const.value);
                                item.free(vm);
                            }
                        }
                    } else {
                        unsafe {
                            *rc -= 1;
                        }
                    }
                }
            }
            pub fn copy_if_reused(&self, vm: &mut VM) -> Self {
                let rc = self.rc();
                let rc_val = unsafe { *rc };
                if rc_val == 1 {
                    *self
                } else {
                    let layout = self.layout();
                    let new_array = BoxedValue::alloc(layout, vm);
                    unsafe {
                        ptr::copy_nonoverlapping(
                            self.data(),
                            new_array.data(),
                            layout.array_size(),
                        );
                    }
                    new_array
                }
            }
        }
    }
}
