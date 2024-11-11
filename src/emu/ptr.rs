use std::{fmt::Display, str::FromStr};

use crate::emu::EmulationError;

/// A 16-bit pointer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ptr(u16);

impl Ptr {
    /// The `NULL` pointer.
    pub const ZERO: Ptr = Ptr(0x0000);

    /// Pointer to the non-maskable interrupt vector.
    ///
    /// The interrupt request vector is a 16-bit word which holds the location that execution
    /// should jump to when a non-maskable interrupt is received.
    pub const NMI: Ptr = Ptr(0xFFFA);

    /// Pointer to the reset vector.
    ///
    /// The reset vector is a 16-bit word which holds the location that execution should begin at
    /// when the CPU is reset.
    pub const RES: Ptr = Ptr(0xFFFC);

    /// Pointer to the interrupt request vector.
    ///
    /// The interrupt request vector is a 16-bit word which holds the location that execution
    /// should jump to when an interrupt is received.
    pub const IRQ: Ptr = Ptr(0xFFFE);

    /// Gets the raw value of this pointer.
    #[inline(always)]
    pub fn raw(self) -> u16 {
        self.0
    }

    /// Wapping pointer arithmetic. Computes `self + rhs` wrapping on overflow.
    pub const fn wrapping_add(self, rhs: u16) -> Ptr {
        Ptr(self.0.wrapping_add(rhs))
    }
}

impl From<u16> for Ptr {
    #[inline(always)]
    fn from(value: u16) -> Self {
        Ptr(value)
    }
}

impl From<Ptr> for u16 {
    #[inline(always)]
    fn from(value: Ptr) -> Self {
        value.0
    }
}

impl FromStr for Ptr {
    type Err = EmulationError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        if s.len() > 4 || !s.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(EmulationError::InvalidPtr);
        }

        let addr = u16::from_str_radix(s, 16).unwrap();
        Ok(Ptr(addr))
    }
}

impl Display for Ptr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#06x}", self.0)
    }
}
