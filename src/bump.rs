use std::{alloc::Layout, cell::RefCell, marker::PhantomData, mem, ops::Index, ptr::NonNull};

use crate::handle::TypedHandle;

pub struct BumpRef<T> {
    offset: u32,
    spooky: PhantomData<T>,
}

impl<T> Clone for BumpRef<T> {
    fn clone(&self) -> Self {
        Self {
            offset: self.offset,
            spooky: PhantomData,
        }
    }
}
impl<T> Copy for BumpRef<T> {}

pub struct BumpSlice<T> {
    offset: u32,
    len: u32,
    spooky: PhantomData<T>,
}

impl<T> BumpSlice<T> {
    fn len(self) -> usize {
        self.len as usize
    }
    fn iter(
        self,
    ) -> impl Iterator<Item = BumpRef<T>> + Clone + ExactSizeIterator + DoubleEndedIterator {
        (0..self.len).map(move |i| BumpRef {
            offset: self.offset + i * (std::mem::size_of::<T>() as u32),
            spooky: PhantomData,
        })
    }
}

impl<T> Default for BumpSlice<T> {
    fn default() -> Self {
        Self {
            offset: 0,
            len: 0,
            spooky: PhantomData,
        }
    }
}

impl<T> Clone for BumpSlice<T> {
    fn clone(&self) -> Self {
        Self {
            offset: self.offset,
            len: self.len,
            spooky: PhantomData,
        }
    }
}
impl<T> Copy for BumpSlice<T> {}

const BUMP_ALIGN: usize = 8;
const BUMP_START_ALLOC: usize = 512;

pub struct InnerBumpVec {
    start: NonNull<u8>,
    offset: usize,
    cap: usize,
}

impl InnerBumpVec {
    const fn new() -> Self {
        Self {
            // making the pointer have the value of the alignment
            // makes it properly aligned, same trick as in `std::ptr::NonNull::dangling()`
            // TODO use std::ptr::invalid_mut when it stabilises  because this probably messes with miri
            start: unsafe { NonNull::new_unchecked(BUMP_ALIGN as *mut u8) },
            offset: 0,
            cap: 0,
        }
    }

    /// This will move the whole allocation upon resize!! You can't keep the returned pointer!!
    unsafe fn alloc(&mut self, layout: Layout) -> *mut u8 {
        // we can't depend on the alignment of the allocation being more tha we've requested
        let size = layout.size();
        let align = layout.align();

        assert!(align <= BUMP_ALIGN);

        // (0110 + 0111) & 1000 -> 1101 & 1000 -> 1000
        let aligned_offset = (self.offset + (align - 1)) & !(align - 1);
        self.offset = aligned_offset + size;
        self.ensure_capacity(self.offset);

        return self.start.as_ptr().add(aligned_offset);
    }

    unsafe fn ensure_capacity(&mut self, min_cap: usize) {
        if min_cap > self.cap {
            let new_cap = min_cap.max(BUMP_START_ALLOC).next_power_of_two();

            let old_layout = Layout::from_size_align(self.cap, BUMP_ALIGN).unwrap();
            let new_start = std::alloc::realloc(self.start.as_ptr(), old_layout, new_cap);

            self.start = NonNull::new(new_start).unwrap();
            self.cap = new_cap;
        }
    }

    /// This will move the whole allocation upon resize!! You can't keep the returned pointer!!
    unsafe fn realloc(&mut self, offset: usize, layout: Layout, new_size: usize) -> *mut u8 {
        let old_end = offset + layout.size();
        debug_assert!(old_end <= self.offset);

        if old_end == self.offset {
            self.offset = offset + new_size;
            self.ensure_capacity(self.offset);

            self.start.as_ptr().add(offset)
        } else {
            self.alloc(Layout::from_size_align(new_size, layout.align()).unwrap())
        }
    }
}

pub struct BumpAlloc {
    inner: InnerBumpVec,
}

impl BumpAlloc {
    pub fn new() -> Self {
        Self {
            inner: InnerBumpVec::new(),
        }
    }

    pub fn alloc<T>(&mut self, val: T) -> BumpRef<T> {
        let inner = &mut self.inner;
        // safety: we never return the pointer, we instead convert it to an offset relative to the allocation
        let ptr = unsafe { inner.alloc(Layout::new::<T>()) };
        // safety: pointer should be aligned and sized properly
        //  no other allocations have been made since creating the pointer so it is still valid
        unsafe { ptr.cast::<T>().write(val) };
        // safety: yes; see previous comments
        let offset: u32 = unsafe { ptr.offset_from(inner.start.as_ptr()).try_into().unwrap() };

        BumpRef {
            offset,
            spooky: PhantomData,
        }
    }

    pub fn alloc_slice<T: Copy>(&mut self, vals: &[T]) -> BumpSlice<T> {
        let inner = &mut self.inner;
        // safety: we never return the pointer, we instead convert it to an offset relative to the allocation
        let ptr = unsafe { inner.alloc(Layout::array::<T>(vals.len()).unwrap()) };
        for (i, val) in vals.iter().copied().enumerate() {
            // safety: pointer should be aligned and sized properly
            //  no other allocations have been made since creating the pointer so it is still valid
            unsafe {
                *ptr.cast::<T>().add(i) = val;
            }
        }
        // safety: yes; see previous comments
        let offset: u32 = unsafe { ptr.offset_from(inner.start.as_ptr()).try_into().unwrap() };

        BumpSlice {
            offset,
            len: vals.len().try_into().unwrap(),
            spooky: PhantomData,
        }
    }

    pub fn alloc_slice_take<T: Default>(&self, vals: &mut [T]) -> BumpSlice<T> {
        let inner = &mut self.inner;
        // safety: we never return the pointer, we instead convert it to an offset relative to the allocation
        let ptr = unsafe { inner.alloc(Layout::array::<T>(vals.len()).unwrap()) };
        for (i, val) in vals.iter_mut().enumerate() {
            // safety: pointer should be aligned and sized properly
            //  no other allocations have been made since creating the pointer so it is still valid
            unsafe {
                *ptr.cast::<T>().add(i) = mem::take(val);
            }
        }
        // safety: yes; see previous comments
        let offset: u32 = unsafe { ptr.offset_from(inner.start.as_ptr()).try_into().unwrap() };

        BumpSlice {
            offset,
            len: vals.len().try_into().unwrap(),
            spooky: PhantomData,
        }
    }

    pub fn build_slice<T>(&mut self) -> SliceBuilder<'_, T> {
        SliceBuilder {
            bump: self,
            start_offset: self.inner.offset,
            len: 0,
            spooky: PhantomData,
        }
    }

    // pub fn alloc_slice_push<T>(&mut self, slice: BumpSlice<T>, val: T) -> BumpSlice<T> {
    //     let inner = &mut self.inner;
    //     // safety: we never return the pointer, we instead convert it to an offset relative to the allocation
    //     let ptr = unsafe {
    //         inner.realloc(
    //             slice.offset as usize,
    //             Layout::array::<T>(slice.len as usize).unwrap(),
    //             mem::size_of::<T>() * (slice.len as usize + 1),
    //         )
    //     };
    //     // safety: pointer should be aligned and sized properly
    //     //  no other allocations have been made since creating the pointer so it is still valid
    //     unsafe {
    //         *ptr.cast::<T>().add(slice.len as usize) = val;
    //     }
    //     // safety: yes; see previous comments
    //     let offset: u32 = unsafe { ptr.offset_from(inner.start.as_ptr()).try_into().unwrap() };

    //     BumpSlice {
    //         offset,
    //         len: slice.len + 1,
    //         spooky: PhantomData,
    //     }
    // }

    unsafe fn get_raw<T>(&self, offset: usize) -> *mut T {
        let inner = &self.inner;
        debug_assert!(offset + mem::size_of::<T>() <= inner.cap);

        let ptr = unsafe { inner.start.as_ptr().add(offset) };
        debug_assert!(ptr.align_offset(mem::align_of::<T>()) == 0);

        ptr.cast()
    }

    pub fn get<T>(&self, offset: BumpRef<T>) -> &T {
        unsafe { &*self.get_raw(offset.offset as usize) }
    }

    pub fn get_mut<T>(&mut self, offset: BumpRef<T>) -> &mut T {
        unsafe { &mut *self.get_raw(offset.offset as usize) }
    }

    pub fn get_slice<T>(&self, offset: BumpSlice<T>) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(self.get_raw(offset.offset as usize), offset.len as usize)
        }
    }

    pub fn get_slice_mut<T>(&mut self, offset: BumpSlice<T>) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(
                self.get_raw(offset.offset as usize),
                offset.len as usize,
            )
        }
    }
}

pub struct SliceBuilder<'a, T> {
    bump: &'a mut BumpAlloc,
    start_offset: usize,
    len: usize,
    spooky: PhantomData<T>,
}

impl<'a, T> SliceBuilder<'a, T> {
    fn reserve(&mut self, additional: usize) {
        let inner = &mut self.bump.inner;
        unsafe {
            inner.ensure_capacity(inner.offset + (additional as usize * mem::size_of::<T>()));
        }
    }
    fn push(&mut self, val: T) {
        self.reserve(1);
        let inner = &mut self.bump.inner;

        let ptr = unsafe {
            inner
                .start
                .as_ptr()
                .add(self.start_offset + self.len * mem::size_of::<T>())
        };
        debug_assert!(ptr.align_offset(mem::align_of::<T>()) == 0);

        unsafe {
            *(ptr.cast::<T>()) = val;
        }
    }
    fn finish(self) -> BumpSlice<T> {
        BumpSlice {
            offset: self.start_offset.try_into().unwrap(),
            len: self.len.try_into().unwrap(),
            spooky: PhantomData,
        }
    }
}

// pub struct HandleBumpSlice<H, T>(BumpSlice<T>, PhantomData<H>);

// impl<H, T> Default for HandleBumpSlice<H, T> {
//     fn default() -> Self {
//         Self(BumpSlice::default(), PhantomData)
//     }
// }

// impl<H: TypedHandle, T> HandleBumpSlice<H, T> {
//     pub fn with_capacity(capacity: usize) -> Self {
//         HandleBumpSlice(Vec::with_capacity(capacity), PhantomData)
//     }
//     pub fn len(&self) -> usize {
//         self.0.len()
//     }
//     pub fn push(&mut self, value: T) -> H {
//         let len = self.0.len();
//         self.0.push(value);
//         H::new(len)
//     }
//     pub fn get(&self, index: H) -> Option<&T> {
//         self.0.get(index.index())
//     }
//     pub fn iter(&self) -> std::slice::Iter<'_, T> {
//         self.0.iter()
//     }
//     pub fn iter_kv(
//         &self,
//     ) -> impl Iterator<Item = (H, &T)> + Clone + ExactSizeIterator + DoubleEndedIterator {
//         self.0.iter().enumerate().map(|(i, t)| (H::new(i), t))
//     }
//     pub fn iter_keys(
//         &self,
//     ) -> impl Iterator<Item = H> + Clone + ExactSizeIterator + DoubleEndedIterator {
//         (0..self.len()).map(H::new)
//     }
// }

// impl<H: TypedHandle, T> Index<H> for HandleBumpSlice<H, T> {
//     type Output = BumpRef<T>;
//     fn index(&self, index: H) -> &Self::Output {
//         &self.0[index.index()]
//     }
// }
