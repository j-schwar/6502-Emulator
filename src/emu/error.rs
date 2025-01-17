//! Types for emulation error handling.

use std::fmt::Display;

/// Errors return by emulation operations.
#[derive(Debug, PartialEq, Eq)]
pub enum EmulationError {
    InvalidPtr,
    InvalidInstruction { opcode: u8, address: u16 },
    Decode,
    Halt,
}

impl Display for EmulationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmulationError::InvalidPtr => write!(f, "invalid pointer"),
            EmulationError::InvalidInstruction { .. } => write!(f, "invalid instruction"),
            EmulationError::Decode => write!(f, "decode error"),
            EmulationError::Halt => write!(f, "halt"),
        }
    }
}

pub type Result<T> = std::result::Result<T, EmulationError>;

impl std::error::Error for EmulationError {}
