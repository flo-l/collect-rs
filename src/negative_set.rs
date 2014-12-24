use std::num::
  {Int, ToPrimitive};
use std::iter::
  {range, range_inclusive};
use std::collections::BTreeSet;

#[deriving(PartialEq, Show)]
pub struct NegativeSet<T> {
  lower: T,
  upper: T,
  missing: BTreeSet<T>
}

impl<T: Int + ToPrimitive> NegativeSet<T> {
  fn new() -> NegativeSet<T> {
    let missing: BTreeSet<T> = [Int::zero()].iter().map(|&x| x).collect();

    NegativeSet { lower: Int::zero(), upper: Int::zero(), missing: missing }
  }

  fn insert(&mut self, elem: T) -> bool {
    if self.contains(&elem) {
      return false;
    }

    //special case: empty set
    if self.is_empty() {
      self.upper = elem;
      self.lower = elem;
      self.missing.clear();
    }

    // elem is not inbetween self's lower and upper bounds
    if self.lower > elem {
      let diff = self.lower - elem;

      // elem is not the precedor of self.lower
      if diff > Int::one() {
        self.missing.extend(range(elem+Int::one(), self.lower));
      }

      self.lower = elem;
    } else if self.upper < elem {
      let diff = elem - self.upper;

      // elem is not the successor of self.upper
      if diff > Int::one() {
        self.missing.extend(range(self.upper+Int::one(), elem));
      }

      self.upper = elem;
    // elem is inbetween self's bounds
    } else {
      self.missing.remove(&elem);
    }

    true
  }

  fn remove(&mut self, elem: &T) -> bool {
    if !self.contains(elem) { return false; }

    // special case: set becoming empty
    if self.len() == 1 {
      self.clear();

    //special cases: elem is one of self's bounds
    } else if *elem == self.lower {
      let new_lower = self.iter().take(2).last().unwrap();

      for x in range_inclusive(self.lower + Int::one(), new_lower) {
        self.missing.remove(&x);
      }

      self.lower = new_lower;

    } else if *elem == self.upper {
      let new_upper = self.upper - Int::one();
      self.missing.remove(&new_upper);
      self.upper = new_upper;

    // normal case
    } else {
      self.missing.insert(*elem);
    }

    true
  }

  fn clear(&mut self) {
    *self = NegativeSet::new();
  }

  fn len(&self) -> uint {
    if self.upper == self.lower {
      if self.missing.is_empty() {
        1
      } else {
        0
      }
    } else {
      (self.upper - self.lower).to_uint().expect("length is bigger than uint") - self.missing.len()
    }
  }

  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  fn contains(&self, k: &T) -> bool {
    self.lower <= *k && self.upper >= *k && ! self.missing.contains(k)
  }

  fn is_disjoint(&self, other: &NegativeSet<T>) -> bool {
    self.lower > other.upper ||
    other.lower > self.upper ||
    other.iter().all(|x| self .missing.contains(&x)) ||
    self .iter().all(|x| other.missing.contains(&x))
  }

  fn iter<'a>(&'a self) -> Items<'a, T> {
    let mut iter_front = self.missing.iter();
    let mut iter_back  = self.missing.iter();

    let next_missing_front = iter_front.next()     .map(|&x| x);
    let next_missing_back  = iter_back .next_back().map(|&x| x);

    Items { next: self.lower,
            last: self.upper,
            missing_front: iter_front,
            missing_back:  iter_back,
            next_missing_front: next_missing_front,
            next_missing_back:  next_missing_back
          }
  }
}

impl<T: Int + ToPrimitive> FromIterator<T> for NegativeSet<T> {
    fn from_iter<Iter: Iterator<T>>(iter: Iter) -> NegativeSet<T> {
        let mut set = NegativeSet::new();
        set.extend(iter);
        set
    }
}

impl<T: Int + ToPrimitive> Extend<T> for NegativeSet<T> {
    fn extend<Iter: Iterator<T>>(&mut self, mut iter: Iter) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

struct Items<'a, T: 'a + Int> {
  next: T,
  last: T,
  missing_front: std::collections::btree_set::Items<'a, T>,
  missing_back:  std::collections::btree_set::Items<'a, T>,
  next_missing_front: Option<T>,
  next_missing_back:  Option<T>
}

impl<'a, T: Int + 'a> Iterator<T> for Items<'a, T> {
  fn next(&mut self) -> Option<T> {
    let ret = self.next;

    //compute self.next value
    loop {
      self.next = self.next + Int::one();

      if self.next_missing_front.is_some() && self.next == self.next_missing_front.unwrap() {
        // this missing value was passed, pop off the next one
        self.next_missing_front = self.missing_front.next().map(|&x| x);

      } else {
        break
      }
    }

    // return ret unless it's bigger than self.last
    if ret > self.last {
      None
    } else {
      Some(ret)
    }
  }
}

// Tests
#[cfg(test)]
mod test {
  use super::NegativeSet;

  #[test]
  fn test_len_is_empty() {
    let mut s: NegativeSet<u8> = NegativeSet::new();

    assert!(s.len() == 0);
    assert!(s.is_empty());

    s.insert(0);
    assert!(s.len() == 1);
    assert!(! s.is_empty());
  }

  #[test]
  fn test_insert_contains_and_remove() {
    let mut s: NegativeSet<i8> = NegativeSet::new();
    assert!(s.insert(0));

    // insert directly at bounds +/- 1
    assert!(s.insert(1));
    assert!(s.insert(-1));

    //insert at bounds +/- more than 1
    assert!(s.insert(5));
    assert!(s.insert(-5));

    // insert inbetween the bounds
    assert!(s.insert(3));
    assert!(s.insert(-3));

    //insert already inserted element
    assert!(! s.insert(0));

    //check if everything is inside
    assert!(s.contains(&-5i8));
    assert!(s.contains(&-3i8));
    assert!(s.contains(&-1i8));
    assert!(s.contains(& 0i8));
    assert!(s.contains(& 1i8));
    assert!(s.contains(& 3i8));
    assert!(s.contains(& 5i8));

    //check if nothing else is inside
    let v: Vec<i8> = s.iter().collect();
    assert_eq!(v, [-5i8,-3,-1,0,1,3,5]);

    //test remove:
    //remove from the middle
    assert!(s.remove(&0));

    //remove nonexistent entry
    assert!( !s.remove(&0));

    //remove from upper and lower bounds
    assert!(s.remove(&-5));
    assert!(s.remove(&5));

    println!("\n{}", s);

    // test content
    let v: Vec<i8> = s.iter().collect();
    assert_eq!(v, [-3i8,-1,1,3]);

    // remove from set with len == 1
    s.clear();
    s.insert(1);
    assert!(s.remove(&1));
    assert!(s.is_empty());
  }

  #[test]
  fn test_clear() {
    let mut s: NegativeSet<i8> = NegativeSet::new();
    s.insert(0);
    s.clear();
    assert!(s.is_empty());
  }

  #[test]
  fn test_is_disjoint() {
    let mut a: NegativeSet<u8> = NegativeSet::new();
    let mut b: NegativeSet<u8> = NegativeSet::new();
    let mut c: NegativeSet<u8> = NegativeSet::new();

    a.insert(0);
    a.insert(2);

    b.insert(3);
    b.insert(4);
    b.insert(5);

    c.insert(2);
    c.insert(6);

    assert!(a.is_disjoint(&b));
    assert!(b.is_disjoint(&a));

    assert!( !a.is_disjoint(&c));
    assert!( !c.is_disjoint(&a));

    assert!(b.is_disjoint(&c));
    assert!(c.is_disjoint(&b));
  }
}
