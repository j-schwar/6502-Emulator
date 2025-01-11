//! Memory components.

use std::cell::RefCell;

use with_ref::WithRef;

use super::emu::{self, BusDir, SharedBus};

/// Read-only memory component which listens on the bus in the 2-byte reset vector location.
///
/// This component is intended as a convenience component for testing or in cases where the whole
/// address space for RAM/ROM doesn't include the reset vector.
pub struct ResetVector {
    bus: SharedBus,
    vector: u16,
}

impl ResetVector {
    /// Constructs a new reset vector component.
    ///
    /// `addr` is the 2-byte value located at 0xfffc.
    pub fn new(bus: SharedBus, addr: u16) -> Self {
        ResetVector { bus, vector: addr }
    }

    /// Main loop for this component.
    pub async fn run(&self) -> emu::Result<()> {
        loop {
            self.bus.with_mut_ref(|bus| match bus.address {
                0xfffc => {
                    bus.data = (self.vector & 0x00ff) as u8;
                    log::debug!(target: "reset_vector", "{:#06x} R {:02x}", bus.address, bus.data);
                }
                0xfffd => {
                    bus.data = (self.vector >> 8) as u8;
                    log::debug!(target: "reset_vector", "{:#06x} R {:02x}", bus.address, bus.data);
                }
                _ => {}
            });

            emu::wait_for_next_cycle().await;
        }
    }
}

/// Emulation component modeling a consecutive chunk of readonly or read-write memory.
///
/// Multiple components of this type can be used within the same executor to model different memory
/// regions.
pub struct Memory {
    bus: SharedBus,
    readonly: bool,
    start_addr: usize,
    memory: RefCell<Box<[u8]>>,
}

impl Memory {
    pub fn from_zeroed(bus: SharedBus, start_addr: u16, size: usize) -> Self {
        let memory = vec![0; size];
        Memory {
            bus,
            readonly: false,
            start_addr: start_addr as usize,
            memory: RefCell::new(memory.into()),
        }
    }

    pub fn from_readonly_data(bus: SharedBus, start_addr: u16, data: impl Into<Box<[u8]>>) -> Self {
        Memory {
            bus,
            readonly: true,
            start_addr: start_addr as usize,
            memory: RefCell::new(data.into()),
        }
    }

    /// Takes ownership of the internal buffer used by this object.
    #[cfg(test)]
    pub fn into_data(self) -> Box<[u8]> {
        self.memory.take()
    }

    /// Writes a textual dump of a range of this memory component to a given writer.
    #[cfg(test)]
    pub fn dump<W>(&self, w: &mut W, start: u16, end: u16) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        debug_assert!(start <= end);

        let memory = self.memory.borrow();
        let bytes_per_line = 16;
        let start = start.saturating_sub(start % bytes_per_line);
        let end = end.saturating_add(bytes_per_line - end % bytes_per_line);

        for i in start..end {
            if i % bytes_per_line == 0 {
                if i != start {
                    writeln!(w)?;
                }

                write!(w, "{:#06x} ", i)?;
            }

            if let Some(index) = (i as usize).checked_sub(self.start_addr) {
                if let Some(value) = memory.get(index) {
                    write!(w, "{:02x} ", value)?;
                } else {
                    write!(w, ".. ")?;
                }
            } else {
                write!(w, ".. ")?;
            }
        }

        w.flush()?;
        Ok(())
    }

    /// Writes a textual dump of a region of memory around a given address from this memory
    /// component to a given writer.
    #[cfg(test)]
    pub fn dump_around<W>(&self, w: &mut W, address: u16) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        let start = address.saturating_sub(16);
        let end = address.saturating_add(16);
        self.dump(w, start, end)
    }

    fn is_address_applicable(&self, address: u16) -> bool {
        let memory = self.memory.borrow();
        let address = address as usize;
        address >= self.start_addr && address < (self.start_addr + memory.len())
    }

    pub async fn run(&self) -> emu::Result<()> {
        loop {
            let address = self.bus.address();

            if self.is_address_applicable(address) {
                let address = address as usize;
                let index = address - self.start_addr;

                if self.bus.dir() == BusDir::Read {
                    let memory = self.memory.borrow();
                    let value = memory[index];
                    self.bus.set_data(value);
                    log::debug!(target: "memory", "{:#06x} R {:02x}", address, value);
                } else if self.bus.dir() == BusDir::Write && !self.readonly {
                    let mut memory = self.memory.borrow_mut();
                    let value = self.bus.data();
                    memory[index] = value;
                    log::debug!(target: "memory", "{:#06x} W {:02x}", address, value);
                }
            }

            emu::wait_for_next_cycle().await;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::emu::*;

    #[test]
    fn memory_read_write() {
        let bus = SharedBus::default();
        let mem = Memory::from_zeroed(bus.clone(), 0x2000, 0x1000);
        let mut executor = Executor::default();
        executor.add_task(mem.run());

        bus.set_address(0x2abc, BusDir::Write);
        bus.set_data(0x42);
        executor.poll().unwrap();

        // Clobber data bus with another write to ensure that reading works correctly.
        bus.set_address(0x2000, BusDir::Write);
        bus.set_data(0xff);
        executor.poll().unwrap();

        bus.set_address(0x2abc, BusDir::Read);
        executor.poll().unwrap();

        assert_eq!(0x42, bus.data());
    }

    #[test]
    fn rom_sets_data_bus() {
        let bus = SharedBus::default();
        // let rom = Rom::from_data(bus.clone(), 0, vec![0, 1, 2, 3]);
        let rom = Memory::from_readonly_data(bus.clone(), 0, vec![0, 1, 2, 3]);

        let mut executor = Executor::default();
        executor.add_task(rom.run());

        bus.set_address(0x0001, BusDir::Read);
        executor.poll().unwrap();
        assert_eq!(1, bus.data());

        bus.set_address(0x0002, BusDir::Read);
        executor.poll().unwrap();
        assert_eq!(2, bus.data());

        bus.set_address(0x0003, BusDir::Read);
        executor.poll().unwrap();
        assert_eq!(3, bus.data());
    }
}
