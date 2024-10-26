//! 6502 CPU Emulator

use with_ref::WithRef;

use crate::emu::{self, BusDir, EmulationError, Ptr, SharedBus};

/// Models CPU state.
#[derive(Clone, Copy, Debug, Default)]
struct Registers {
    /// Program counter register.
    pub pc: u16,
    /// Accumulator register.
    pub ac: u8,
    /// General purpose X register.
    pub x: u8,
    /// General purpose Y register.
    pub y: u8,
    /// Status register.
    pub sr: u8,
    /// Stack pointer.
    pub sp: u8,
}

pub struct Cpu {
    bus: SharedBus,
    registers: Registers,
}

impl Cpu {
    /// Constructs a new [`Cpu`] instance which will use the given data and address busses.
    pub fn new(bus: SharedBus) -> Self {
        Self {
            bus,
            registers: Default::default(),
        }
    }

    /// Signals the end of the CPU cycle.
    ///
    /// Along with calling [`core::wait_for_next_cycle`], this function performs additional logging
    /// of the bus and register state for debugging.
    async fn end_cycle(&self) {
        log::trace!(
            target: "reg",
            "PC: {:04x}, A: {:02x}, X: {:02x}, Y: {:02x}, SR: {:02x}, SP: {:02x}",
            self.registers.pc,
            self.registers.ac,
            self.registers.x,
            self.registers.y,
            self.registers.sr,
            self.registers.sp,
        );

        self.bus.with_ref(
            |bus| log::trace!(target: "bus", "{} {} {:02x}", bus.address, bus.dir, bus.data),
        );
        emu::wait_for_next_cycle().await;
    }
    /// Reads a single byte from the bus at a given address.
    ///
    /// This operation takes a single clock cycle.
    async fn read_u8(&mut self, addr: Ptr) -> u8 {
        self.bus.set_address(addr, BusDir::Read);
        self.end_cycle().await;
        self.bus.data()
    }

    /// Reads a 16-bit word (little endian) from the bus at a given address.
    ///
    /// This operation performs two reads and takes 2 clock cycles.
    async fn read_u16(&mut self, addr: Ptr) -> u16 {
        let mut word = 0u16;
        word |= self.read_u8(addr).await as u16;
        word |= (self.read_u8(addr.wrapping_add(1)).await as u16) << 8;
        word
    }

    /// Invokes the processor's reset sequence.
    ///
    /// All registers are zeroed, and the program counter is set to the reset vector located at
    /// address 0xfffc.
    async fn reset(&mut self) {
        // The spec states that there is a 7-cycle initialization period for the processor before it
        // actually does anything. We'll skip emulating this since idk what it's actually doing for
        // those cycles.

        // Reset registers.
        self.registers = Default::default();

        // Load reset vector into program counter.
        self.registers.pc = self.read_u16(Ptr::RES).await;
    }

    async fn fetch_and_execute(&mut self) -> emu::Result<()> {
        let opcode = self.read_u8(Ptr::from(self.registers.pc)).await;

        let instruction_size = match opcode {
            // NOP
            0xea => {
                log::debug!(target: "instr", "NOP");
                self.end_cycle().await;
                self.end_cycle().await;
                1
            }

            _ => return Err(EmulationError::InvalidInstruction),
        };

        self.registers.pc = self.registers.pc.wrapping_add(instruction_size);
        Ok(())
    }

    pub async fn run(&mut self) -> emu::Result<()> {
        self.reset().await;
        loop {
            self.fetch_and_execute().await?;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::emu::Executor;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn reset() {
        init();
        let mut bus = SharedBus::default();
        let mut cpu = Cpu::new(bus.clone());

        {
            let mut executor = Executor::default();
            executor.add_task(cpu.run());

            // Data bus should not be clobbered, set to noop instruction.
            bus.set_data(0xea);
            executor.poll_n(3).unwrap();
        }

        assert_eq!(cpu.registers.pc, 0xeaea);
    }
}
