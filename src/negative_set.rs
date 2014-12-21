use std::iter::Range;
use std::collections::BTreeSet;

pub struct Test {}

pub struct NegativeSet<T: Ord + Int> {
  lower: T,
  upper: T,
  missing: BTreeSet<T>
}

impl NegativeSet<T> {
  fn new() -> NegativeSet {
    NegativeSet { lower: T::zero(), upper: T::zero(), BTreeSet::new() }
  }
}
