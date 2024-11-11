//! Memory components.

use with_ref::WithRef;

use super::emu::{self, BusDir, Result, SharedBus};

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
                    log::debug!(target: "reset_vector", "{} R {:02x}", bus.address, bus.data);
                }
                0xfffd => {
                    bus.data = (self.vector >> 8) as u8;
                    log::debug!(target: "reset_vector", "{} R {:02x}", bus.address, bus.data);
                }
                _ => {}
            });

            emu::wait_for_next_cycle().await;
        }
    }
}

pub struct Rom {
    bus: SharedBus,
    start_addr: usize,
    memory: Box<[u8]>,
}

impl Rom {
    pub fn from_data(bus: SharedBus, start_addr: u16, data: impl Into<Box<[u8]>>) -> Self {
        Self {
            bus,
            start_addr: start_addr as usize,
            memory: data.into(),
        }
    }
}

impl Rom {
    fn cycle(&self) {
        self.bus.with_mut_ref(|bus| {
            if bus.dir == BusDir::Read {
                let addr = bus.address as usize;
                if addr >= self.start_addr && addr < (self.start_addr + self.memory.len()) {
                    let index = addr - self.start_addr;
                    let value = self.memory[index];
                    bus.data = value;

                    log::debug!(target: "rom", "{} R {:02x}", bus.address, value);
                }
            }
        });
    }

    pub async fn run(&self) -> Result<()> {
        loop {
            self.cycle();
            emu::wait_for_next_cycle().await;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::emu::*;

    #[test]
    fn rom_sets_data_bus() {
        let bus = SharedBus::default();
        let rom = Rom::from_data(bus.clone(), 0, vec![0, 1, 2, 3]);

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
