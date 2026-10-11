use core::fmt::Debug;

use astd::heapless::Vec as ArrayVec;

use super::MemoryRange;

/// A map of memory regions.
#[derive(Debug, Clone)]
pub struct MemoryMap<T: Clone + Debug + PartialEq> {
    pub regions: ArrayVec<(MemoryRange, T), 100>,
}

impl<T: Clone + Debug + PartialEq> MemoryMap<T> {
    pub const fn empty() -> Self {
        Self {
            regions: ArrayVec::new(),
        }
    }

    pub fn new<I>(regions: I) -> Self
    where
        I: IntoIterator<Item = (MemoryRange, T)>,
    {
        let regions = ArrayVec::from_iter(regions);
        Self { regions }
    }

    pub fn add(&mut self, region: MemoryRange, label: T) {
        self.regions.push((region, label)).unwrap();
    }

    pub fn relabel(&mut self, range: MemoryRange, label: T) {
        let mut new_regions: ArrayVec<(MemoryRange, T), 100> = ArrayVec::new();

        for (region, cur_label) in self.regions.iter_mut() {
            if region == &range {
                *cur_label = label;
                break;
            }

            if !region.intersects(&range) {
                // disjoint
                continue;
            }

            if range.fully_contains(region) {
                *cur_label = label.clone();
                continue;
            }

            // [left][relabeled][right]
            if range.base() > region.base() {
                new_regions
                    .push((
                        MemoryRange::new(region.base(), range.base() - region.base()),
                        cur_label.clone(),
                    ))
                    .unwrap();
            }

            if range.end_inclusive() < region.end_inclusive() {
                new_regions
                    .push((
                        MemoryRange::new(
                            range.end_inclusive() + 1,
                            region.end_inclusive() - range.end_inclusive(),
                        ),
                        cur_label.clone(),
                    ))
                    .unwrap();
            }

            let relabeled_base = core::cmp::max(range.base(), region.base());
            let relabeled_end = core::cmp::min(range.end_inclusive(), region.end_inclusive());

            *cur_label = label.clone();
            *region = MemoryRange::new(relabeled_base, relabeled_end - relabeled_base + 1);
        }

        self.regions.extend(new_regions);
    }

    pub fn sort(&mut self) {
        if self.regions.is_empty() {
            return;
        }

        self.regions
            .sort_unstable_by(|a, b| a.0.base().cmp(&b.0.base()));

        let mut curidx = 0;
        let mut cur = self.regions[curidx].clone();

        for i in 1..self.regions.len() {
            if cur.0.end_inclusive() + 1 == self.regions[i].0.base() && &cur.1 == &self.regions[i].1
            {
                // consecutive
                cur.0.set_size(cur.0.size() + self.regions[i].0.size());
            } else {
                self.regions[curidx] = cur;
                cur = self.regions[i].clone();
                curidx += 1;
            }
        }

        self.regions[curidx] = cur;
        curidx += 1;

        self.regions.truncate(curidx);
    }
}
