//! Here we test everything we can, use all out public types in all the ways we can think of
//! to hopefully cover a great range of behaviors and paths in the whole code.
//! Some sort of fuzzing, except it is not really fuzzing I don't know.

use std::fmt::Debug;

use palette_vec::{OutAccessOptimizer, OutPalVec, PalVec, ViewToOwned};

/// Make it possible to write testing code once and run it on both a PalVec and a OutPalVec.
enum PalVecMaybeOut<T>
where
    T: Debug + Clone + Eq,
{
    PalVec(PalVec<T>),
    OutPalVec(OutPalVec<T>),
}

impl<T> PalVecMaybeOut<T>
where
    T: Debug + Clone + Eq,
{
    fn assert_invariants(&self) {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.check_invariants().unwrap(),
            PalVecMaybeOut::OutPalVec(pv) => pv.check_invariants().unwrap(),
        }
    }

    fn set(
        &mut self,
        index: usize,
        element: impl ViewToOwned<T>,
        access: Option<&mut OutAccessOptimizer>,
    ) {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.set(index, element),
            PalVecMaybeOut::OutPalVec(pv) => pv.set(index, element, access),
        }
    }

    fn push(&mut self, element: impl ViewToOwned<T>, how_many: usize) {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.push(element, how_many),
            PalVecMaybeOut::OutPalVec(pv) => pv.push(element, how_many),
        }
    }

    fn get(&mut self, index: usize, access: Option<&mut OutAccessOptimizer>) -> Option<&T> {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.get(index),
            PalVecMaybeOut::OutPalVec(pv) => pv.get(index, access),
        }
    }

    fn keys_size(&self) -> usize {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.keys_size(),
            PalVecMaybeOut::OutPalVec(pv) => pv.keys_size(),
        }
    }

    fn len(&mut self) -> usize {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.len(),
            PalVecMaybeOut::OutPalVec(pv) => pv.len(),
        }
    }

    fn number_of_instances(&self, element: &impl ViewToOwned<T>) -> usize {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.number_of_instances(element),
            PalVecMaybeOut::OutPalVec(pv) => pv.number_of_instances(element),
        }
    }

    fn perform_memory_opimization(&mut self) {
        match self {
            PalVecMaybeOut::PalVec(pv) => pv.perform_memory_opimization(),
            PalVecMaybeOut::OutPalVec(pv) => pv.perform_memory_opimization(),
        }
    }
}

#[test]
fn try_everything_on_u32_palvec() {
    try_everything(PalVecMaybeOut::PalVec(PalVec::<u32>::new()), None, 0..);
}

#[test]
fn try_everything_on_string_palvec() {
    try_everything(
        PalVecMaybeOut::PalVec(PalVec::<String>::new()),
        None,
        (0..).map(|i| format!("uwu-{i}")),
    );
}

#[test]
fn try_everything_on_u32_outpalvec() {
    try_everything(
        PalVecMaybeOut::OutPalVec(OutPalVec::<u32>::new()),
        None,
        0..,
    );
}

#[test]
fn try_everything_on_string_outpalvec() {
    try_everything(
        PalVecMaybeOut::OutPalVec(OutPalVec::<String>::new()),
        None,
        (0..).map(|i| format!("uwu-{i}")),
    );
}

#[test]
fn try_everything_on_u32_outpalvec_with_access_hint() {
    try_everything(
        PalVecMaybeOut::OutPalVec(OutPalVec::<u32>::new()),
        Some(OutAccessOptimizer::new()),
        0..,
    );
}

#[test]
fn try_everything_on_string_outpalvec_with_access_hint() {
    try_everything(
        PalVecMaybeOut::OutPalVec(OutPalVec::<String>::new()),
        Some(OutAccessOptimizer::new()),
        (0..).map(|i| format!("uwu-{i}")),
    );
}

fn try_everything<T>(
    mut pv: PalVecMaybeOut<T>,
    mut access: Option<OutAccessOptimizer>,
    mut element_values: impl Iterator<Item = T>,
) where
    T: Debug + Clone + Eq,
{
    // Get some elements that will be added in many instances.
    let mut some_element_values: Vec<T> = vec![];
    for _ in 0..7 {
        some_element_values.push(element_values.next().unwrap());
    }
    let some_element_values: [T; 7] = some_element_values.try_into().unwrap();

    // Get more elements that will be added in few instances.
    let mut more_element_values: Vec<T> = vec![];
    for _ in 0..57 {
        more_element_values.push(element_values.next().unwrap());
    }
    let more_element_values: [T; 57] = more_element_values.try_into().unwrap();

    // Add the elements in many instances and check stuff.
    let mut expected_len = 0;
    #[allow(clippy::needless_range_loop)]
    for i in 0..some_element_values.len() {
        let element = &some_element_values[i];
        let how_many = (i + 1) * 20000;
        pv.push(element, how_many);
        expected_len += how_many;
    }
    assert_eq!(pv.len(), expected_len);
    assert_eq!(pv.keys_size(), 3);
    #[allow(clippy::needless_range_loop)]
    for i in 0..some_element_values.len() {
        let element = &some_element_values[i];
        let how_many = (i + 1) * 20000;
        assert_eq!(pv.number_of_instances(&element), how_many);
    }
    pv.assert_invariants();

    // Check that memory optimization does not break here.
    // It can't do much so it should be fine.
    pv.perform_memory_opimization();
    assert_eq!(pv.keys_size(), 3);
    pv.assert_invariants();

    // Pepper in more elements in few instances and check stuff.
    #[allow(clippy::needless_range_loop)]
    for i in 0..16 {
        pv.set(i, &more_element_values[i], access.as_mut());
        pv.push(&more_element_values[i], 1);
    }
    for i in 0..(more_element_values.len() - 16) {
        for j in 0..((i + 1) * 3) {
            pv.set(
                16 + i * 200 + j,
                &more_element_values[i + 16],
                access.as_mut(),
            );
            pv.push(&more_element_values[i + 16], 1);
        }
    }
    #[allow(clippy::needless_range_loop)]
    for i in 0..16 {
        assert_eq!(*pv.get(i, access.as_mut()).unwrap(), more_element_values[i]);
    }
    for i in 0..(more_element_values.len() - 16) {
        for j in 0..((i + 1) * 3) {
            assert_eq!(
                *pv.get(16 + i * 200 + j, access.as_mut()).unwrap(),
                more_element_values[i + 16]
            );
        }
    }
    #[allow(clippy::needless_range_loop)]
    for i in 0..16 {
        let element = &more_element_values[i];
        let how_many = 2;
        assert_eq!(pv.number_of_instances(&element), how_many);
    }
    for i in 0..(more_element_values.len() - 16) {
        let element = &more_element_values[i + 16];
        let how_many = (i + 1) * 3 * 2;
        assert_eq!(pv.number_of_instances(&element), how_many);
    }
    assert_eq!(pv.keys_size(), 6);
    pv.assert_invariants();

    // Check that memory optimization does not break here.
    // While the `PalVec` still can't do much,
    // the `OutPalVec` can put all the elements with few instances in its outlier palette
    // and so is expected to get its `keys_size` down a few bits!
    pv.perform_memory_opimization();
    match pv {
        PalVecMaybeOut::PalVec(_) => assert_eq!(pv.keys_size(), 6),
        PalVecMaybeOut::OutPalVec(_) => assert_eq!(pv.keys_size(), 3),
    }
    pv.assert_invariants();
}
