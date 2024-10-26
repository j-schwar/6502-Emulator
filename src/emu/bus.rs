use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::emu::Ptr;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum BusDir {
    #[default]
    Read,
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
pub struct SharedBus(Rc<RefCell<Bus>>);

impl SharedBus {
    /// Executes a closure while holding a reference to the shared bus.
    pub fn with_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Bus) -> T,
    {
        f(&self.0.borrow())
    }

    /// Executes a closure while holding a mutable reference to the shared bus.
    pub fn with_mut_ref<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Bus) -> T,
    {
        f(&mut self.0.as_ref().borrow_mut())
    }

    /// Returns the value of the address bus.
    pub fn address(&self) -> Ptr {
        self.with_ref(|bus| bus.address)
    }

    /// Sets the value on the address bus along with the direction.
    pub fn set_address(&mut self, ptr: Ptr, dir: BusDir) {
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
    pub fn set_data(&mut self, value: u8) {
        self.with_mut_ref(|bus| bus.data = value);
    }
}
