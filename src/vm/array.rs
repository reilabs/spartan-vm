use std::{
    alloc::{self, Layout},
    ptr,
};

use crate::vm::bytecode::{AllocationType, VM};

#[derive(Debug, Clone, Copy)]
pub struct ArrayMeta(pub u64);

impl ArrayMeta {
    pub fn new(size: usize, ptr_elems: bool) -> Self {
        Self(size as u64 | ((ptr_elems as u64) << 63))
    }

    pub fn size(&self) -> usize {
        self.0 as usize & !(1 << 63)
    }

    pub fn ptr_elems(&self) -> bool {
        (self.0 as usize >> 63) == 1
    }
}

#[derive(Clone, Copy)]
pub struct Array(pub *mut u64);

impl Array {
    pub fn alloc(meta: ArrayMeta, vm: &mut VM) -> Self {
        let ptr =
            unsafe { alloc::alloc(Layout::array::<u64>(meta.size() + 2).unwrap()) } as *mut u64;
        vm.allocation_instrumenter
            .alloc(AllocationType::Heap, meta.size() + 2);
        unsafe {
            *ptr = meta.0;
            *ptr.offset(1) = 1;
        }
        Self(ptr)
    }

    fn rc(&self) -> *mut u64 {
        unsafe { self.0.offset(1) }
    }

    fn meta(&self) -> *mut ArrayMeta {
        self.0 as *mut ArrayMeta
    }

    fn size(&self) -> usize {
        unsafe { *self.meta() }.size()
    }

    pub fn idx(&self, idx: usize, stride: usize) -> *mut u64 {
        unsafe { self.0.offset(2 + (idx as isize * stride as isize)) }
    }

    pub fn inc_rc(&self, by: u64) {
        let rc = self.rc();
        // println!(
        //     "inc_array_rc from {} by {} at {:?}",
        //     unsafe { *rc },
        //     by,
        //     self.0
        // );
        unsafe {
            *rc += by;
        }
    }

    pub fn dec_rc(&self, vm: &mut VM) {
        let rc = self.rc();
        let rc_val = unsafe { *rc };
        // println!("dec_array_rc from {} at {:?}", unsafe { *rc }, self.0);
        if rc_val - 1 == 0 {
            // println!("Array @{:?} needs to be freed", self.0);
            let meta = unsafe { *self.meta() };
            if meta.ptr_elems() {
                // println!("Array has ptr elements, dropping");
                for i in 0..meta.size() {
                    let elem = unsafe { *(self.idx(i, 1) as *mut Array) };
                    elem.dec_rc(vm);
                }
            }
            unsafe {
                alloc::dealloc(
                    self.0 as *mut u8,
                    Layout::array::<u64>(meta.size() + 2).unwrap(),
                );
                vm.allocation_instrumenter
                    .free(AllocationType::Heap, meta.size() + 2);
            }
        } else {
            unsafe {
                *rc -= 1;
            }
        }
    }

    pub fn copy_if_reused(&self, vm: &mut VM) -> Self {
        let rc = self.rc();
        let rc_val = unsafe { *rc };

        if rc_val == 1 {
            // println!("Array @{:?} is dying, move instead of copy", self.0);
            *self
        } else {
            // println!("Array @{:?} is not dying, copy", self.0);
            let new_array = Array::alloc(unsafe { *self.meta() }, vm);

            unsafe {
                ptr::copy_nonoverlapping(self.0, new_array.0, self.size() + 2);
                *new_array.rc() = 1;
            }
            new_array
        }
    }
}
