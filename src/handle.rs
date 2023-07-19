use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

pub trait TypedHandle {
    fn new(index: usize) -> Self;
    fn index(self) -> usize;
}

#[macro_export]
macro_rules! simple_handle {
    ($($visibility:vis $name:ident),+) => {
        $(
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #[repr(transparent)]
            $visibility struct $name(u32);
            #[allow(unused)]
            impl $crate::handle::TypedHandle for $name {
                fn new(index: usize) -> Self {
                    assert!(index <= u32::MAX as usize);
                    Self(index as u32)
                }
                #[inline]
                fn index(self) -> usize {
                    self.0 as usize
                }
            }
        )+
    };
}
pub use simple_handle;

pub struct HandleVec<H, T>(Vec<T>, PhantomData<H>);

impl<H, T> Default for HandleVec<H, T> {
    fn default() -> Self {
        Self(Vec::default(), PhantomData)
    }
}

impl<H: TypedHandle, T> HandleVec<H, T> {
    pub fn new() -> Self {
        HandleVec(Vec::new(), PhantomData)
    }
    pub fn with_capacity(capacity: usize) -> Self {
        HandleVec(Vec::with_capacity(capacity), PhantomData)
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn push(&mut self, value: T) -> H {
        let len = self.0.len();
        self.0.push(value);
        H::new(len)
    }
    pub fn get(&self, index: H) -> Option<&T> {
        self.0.get(index.index())
    }
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }
    pub fn iter_kv(
        &self,
    ) -> impl Iterator<Item = (H, &T)> + Clone + ExactSizeIterator + DoubleEndedIterator {
        self.0.iter().enumerate().map(|(i, t)| (H::new(i), t))
    }
    pub fn iter_keys(
        &self,
    ) -> impl Iterator<Item = H> + Clone + ExactSizeIterator + DoubleEndedIterator {
        (0..self.len()).map(H::new)
    }
}

impl<H, Ty> Extend<Ty> for HandleVec<H, Ty> {
    fn extend<T: IntoIterator<Item = Ty>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<H: TypedHandle, T> Index<H> for HandleVec<H, T> {
    type Output = T;
    fn index(&self, index: H) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl<H: TypedHandle, T> IndexMut<H> for HandleVec<H, T> {
    fn index_mut(&mut self, index: H) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

impl<H, T: Debug> Debug for HandleVec<H, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}
