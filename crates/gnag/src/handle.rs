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
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
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

pub struct HandleCounter<H>(usize, PhantomData<H>);

impl<H: TypedHandle> HandleCounter<H> {
    pub fn new() -> Self {
        Self(0, PhantomData)
    }
    pub fn next(&mut self) -> H {
        let next = H::new(self.0);
        self.0 += 1;
        next
    }
    pub fn reset(&mut self) {
        self.0 = 0;
    }
}

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
    pub fn map<A>(self, fun: impl FnMut(T) -> A) -> HandleVec<H, A> {
        HandleVec(self.0.into_iter().map(fun).collect(), PhantomData)
    }
    pub fn map_ref<A>(&self, fun: impl FnMut(&T) -> A) -> HandleVec<H, A> {
        HandleVec(self.0.iter().map(fun).collect(), PhantomData)
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
    pub fn as_slice(&self) -> &[T] {
        &self.0
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

impl<H, T> Extend<T> for HandleVec<H, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<H, T> FromIterator<T> for HandleVec<H, T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        HandleVec(Vec::from_iter(iter), PhantomData)
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

impl<H, T> IntoIterator for HandleVec<H, T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, H, T> IntoIterator for &'a HandleVec<H, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

pub struct SecondaryVec<H, T>(Vec<Option<T>>, PhantomData<H>);

impl<H, T> Default for SecondaryVec<H, T> {
    fn default() -> Self {
        Self(Vec::default(), PhantomData)
    }
}

impl<H: TypedHandle, T> SecondaryVec<H, T> {
    pub fn new() -> Self {
        SecondaryVec(Vec::new(), PhantomData)
    }
    pub fn map<A>(self, mut fun: impl FnMut(T) -> A) -> SecondaryVec<H, A> {
        SecondaryVec(
            self.0
                .into_iter()
                .map(|option| match option {
                    Some(some) => Some(fun(some)),
                    None => None,
                })
                .collect(),
            PhantomData,
        )
    }
    pub fn map_ref<A>(&self, mut fun: impl FnMut(&T) -> A) -> SecondaryVec<H, A> {
        SecondaryVec(
            self.0
                .iter()
                .map(|option| match option {
                    Some(some) => Some(fun(some)),
                    None => None,
                })
                .collect(),
            PhantomData,
        )
    }
    pub fn with_capacity(capacity: usize) -> Self {
        SecondaryVec(Vec::with_capacity(capacity), PhantomData)
    }
    pub fn insert(&mut self, at: H, value: T) -> Option<T> {
        let index = at.index();
        if index >= self.0.len() {
            let add = self.0.len()..=index;
            self.0.extend(add.map(|_| None));
        }

        let old = std::mem::replace(&mut self.0[index], Some(value));
        return old;
    }
    pub fn get(&self, index: H) -> Option<&T> {
        let get = self.0.get(index.index());
        match get {
            Some(some) => some.as_ref(),
            None => None,
        }
    }
    pub fn get_mut(&mut self, index: H) -> Option<&mut T> {
        let get = self.0.get_mut(index.index());
        match get {
            Some(some) => some.as_mut(),
            None => None,
        }
    }
    pub fn entry(&mut self, index: H) -> &mut Option<T> {
        let index = index.index();
        if index >= self.0.len() {
            let add = self.0.len()..=index;
            self.0.extend(add.map(|_| None));
        }

        &mut self.0[index]
    }
    pub fn iter(&self) -> std::iter::Flatten<std::slice::Iter<'_, Option<T>>> {
        self.0.iter().flatten()
    }
    pub fn iter_kv(&self) -> impl Iterator<Item = (H, &T)> + Clone + DoubleEndedIterator {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.as_ref().map(|t| (H::new(i), t)))
    }
    pub fn iter_keys(&self) -> impl Iterator<Item = H> + Clone + DoubleEndedIterator + '_ {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.is_some().then_some(H::new(i)))
    }
}

impl<H: TypedHandle, T> Index<H> for SecondaryVec<H, T> {
    type Output = T;
    fn index(&self, index: H) -> &Self::Output {
        self.0[index.index()].as_ref().unwrap()
    }
}

impl<H: TypedHandle, T> IndexMut<H> for SecondaryVec<H, T> {
    fn index_mut(&mut self, index: H) -> &mut Self::Output {
        self.0[index.index()].as_mut().unwrap()
    }
}

impl<H: TypedHandle + Debug, T: Debug> Debug for SecondaryVec<H, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter_kv()).finish()
    }
}

impl<H, T> IntoIterator for SecondaryVec<H, T> {
    type Item = T;
    type IntoIter = std::iter::Flatten<std::vec::IntoIter<Option<T>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().flatten()
    }
}

impl<'a, H, T> IntoIterator for &'a SecondaryVec<H, T> {
    type Item = &'a T;
    type IntoIter = std::iter::Flatten<std::slice::Iter<'a, Option<T>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().flatten()
    }
}

impl<H: TypedHandle, T> Extend<(H, T)> for SecondaryVec<H, T> {
    fn extend<I: IntoIterator<Item = (H, T)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<H: TypedHandle, T> FromIterator<(H, T)> for SecondaryVec<H, T> {
    fn from_iter<I: IntoIterator<Item = (H, T)>>(iter: I) -> Self {
        let mut vec = SecondaryVec::new();
        vec.extend(iter);
        vec
    }
}
