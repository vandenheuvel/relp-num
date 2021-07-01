use std::mem;

use smallvec::SmallVec;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Ubig<const S: usize>(SmallVec<[usize; S]>);
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct NonZeroUbig<const S: usize>(SmallVec<[usize; S]>);

pub mod creation;
pub mod ops;
pub mod properties;

impl<const S: usize> Ubig<S> {
    pub(crate) unsafe fn is_well_formed(&self) -> bool {
        match self.0.last() {
            None => true,
            Some(&value) => value != 0,
        }
    }
    pub(crate) fn inner(&self) -> &SmallVec<[usize; S]> {
        &self.0
    }
    pub(crate) unsafe fn inner_mut(&mut self) -> &mut SmallVec<[usize; S]> {
        &mut self.0
    }
    pub(crate) fn into_inner(self) -> SmallVec<[usize; S]> {
        self.0
    }
}

impl<const S: usize> NonZeroUbig<S> {
    pub(crate) unsafe fn is_well_formed(&self) -> bool {
        match self.0.last() {
            None => false,
            Some(&value) => value != 0,
        }
    }
    pub(crate) fn inner(&self) -> &SmallVec<[usize; S]> {
        &self.0
    }
    pub(crate) unsafe fn inner_mut(&mut self) -> &mut SmallVec<[usize; S]> {
        &mut self.0
    }
    pub(crate) fn first(&self) -> &usize {
        unsafe {
            self.0.get_unchecked(0)
        }
    }
    pub(crate) unsafe fn first_mut(&mut self) -> &mut usize {
        self.0.get_unchecked_mut(0)
    }
    pub(crate) fn into_inner(self) -> SmallVec<[usize; S]> {
        self.0
    }
}

pub const BITS_PER_WORD: u32 = (mem::size_of::<usize>() * 8) as u32;
