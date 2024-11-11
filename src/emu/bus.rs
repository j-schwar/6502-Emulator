use std::{fmt::Display, rc::Rc};
use with_ref::{ScopedRefCell, WithRef};

use crate::emu::Ptr;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum BusDir {
    #[default]
    Read,
    #[expect(unused)]
    Write,
}

impl Display for BusDir {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            BusDir::Read => write!(f, "R"),
            BusDir::Write => write!(f, "W"),
        }
    }
}

#[derive(Default, Clone)]
pub struct Bus {
    pub data: u8,
    pub address: Ptr,
    pub dir: BusDir,
}

/// A shared pointer to a [`Bus`] instance.
///
/// This type contains convenience methods for interacting with specific parts of the bus.
#[derive(Default, Clone)]
pub struct SharedBus(Rc<ScopedRefCell<Bus>>);

impl SharedBus {
    /// Returns the value of the address bus.
    #[expect(unused)]
    pub fn address(&self) -> Ptr {
        self.with_ref(|bus| bus.address)
    }

    /// Sets the value on the address bus along with the direction.
    pub fn set_address(&self, ptr: Ptr, dir: BusDir) {
        self.with_mut_ref(|bus| {
            bus.address = ptr;
            bus.dir = dir;
        });
    }

    /// Returns the value on the data bus.
    pub fn data(&self) -> u8 {
        self.with_ref(|bus| bus.data)
    }

    /// Sets the value on the data bus.
    #[expect(unused)]
    pub fn set_data(&self, value: u8) {
        self.with_mut_ref(|bus| bus.data = value);
    }
}

impl WithRef for SharedBus {
    type Inner = Bus;

    fn with_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Self::Inner) -> T,
    {
        self.0.with_ref(f)
    }

    fn with_mut_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut Self::Inner) -> T,
    {
        self.0.with_mut_ref(f)
    }
}
