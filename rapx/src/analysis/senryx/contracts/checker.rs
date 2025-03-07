use super::abstract_state::*;
use super::contract::*;
use core::mem;
use std::collections::HashMap;
use std::marker::PhantomData;

pub trait Checker {
    fn variable_contracts(&self) -> &HashMap<usize, Vec<Contract>>;
}

pub struct SliceFromRawPartsChecker<T> {
    pub variable_contracts: HashMap<usize, Vec<Contract>>,
    _marker: PhantomData<T>,
}

impl<T> Checker for SliceFromRawPartsChecker<T> {
    fn variable_contracts(&self) -> &HashMap<usize, Vec<Contract>> {
        &self.variable_contracts
    }
}

impl<T> SliceFromRawPartsChecker<T> {
    pub fn new() -> Self {
        let mut map = HashMap::new();
        map.insert(
            0,
            vec![
                // Contract::StateCheck {
                //     op: Op::GE,
                //     state: StateType::AllocatedState(AllocatedState::Alloc),
                // },
                Contract::StateCheck {
                    op: Op::GT,
                    state: StateType::AlignState(AlignState::Unaligned),
                },
            ],
        );
        map.insert(
            1,
            vec![Contract::ValueCheck {
                op: Op::LE,
                value: Value::Usize((isize::MAX as usize) / mem::size_of::<T>()),
            }],
        );
        Self {
            variable_contracts: map,
            _marker: PhantomData,
        }
    }
}
