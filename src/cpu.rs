//! 6502 CPU Emulator

use with_ref::{ScopedRefCell, WithRef};

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

macro_rules! set_bit {
    ($receiver:expr, $bit:literal, $value:expr) => {
        if $value {
            $receiver |= $bit;
        } else {
            const MASK: u8 = 0xFF ^ $bit;
            $receiver &= MASK;
        }
    };
}

impl Registers {
    /// Sets the negative (N) flag in the status register.
    fn set_negative_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x80, value);
    }

    /// Sets the overflow (V) flag in the status register.
    fn set_overflow_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x40, value);
    }

    /// Sets the break flag (B) in the status register.
    fn set_break_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x10, value);
    }

    /// Sets the decimal flag (D) in the status register.
    fn set_decimal_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x08, value);
    }

    /// Sets the interrupt disable flag (I) in the status register.
    fn set_interrupt_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x04, value);
    }

    /// Sets the zero flag (Z) in the status register.
    fn set_zero_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x02, value);
    }

    /// Sets the carry flag (C) in the status register.
    fn set_carry_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x01, value);
    }
}

pub struct Cpu {
    bus: SharedBus,
    registers: ScopedRefCell<Registers>,
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
        // self.registers.with_ref(|r| {
        //     log::trace!(
        //         target: "reg",
        //         "PC: {:04x}, A: {:02x}, X: {:02x}, Y: {:02x}, SR: {:02x}, SP: {:02x}",
        //         r.pc,
        //         r.ac,
        //         r.x,
        //         r.y,
        //         r.sr,
        //         r.sp,
        //     );
        // });

        // self.bus.with_ref(
        //     |bus| log::trace!(target: "bus", "{} {} {:02x}", bus.address, bus.dir, bus.data),
        // );
        emu::wait_for_next_cycle().await;
    }
    /// Reads a single byte from the bus at a given address.
    ///
    /// This operation takes a single clock cycle.
    async fn read_u8(&self, addr: Ptr) -> u8 {
        self.bus.set_address(addr, BusDir::Read);
        self.end_cycle().await;
        self.bus.data()
    }

    /// Reads a 16-bit word (little endian) from the bus at a given address.
    ///
    /// This operation performs two reads and takes 2 clock cycles.
    async fn read_u16(&self, addr: Ptr) -> u16 {
        let mut word: u16 = 0u16;
        word |= self.read_u8(addr).await as u16;
        word |= (self.read_u8(addr.wrapping_add(1)).await as u16) << 8;
        word
    }

    /// Reads a single byte from the bus at the address pointed to by the program counter. After
    /// which, the program counter is then incremented by 1.
    ///
    /// This operation takes a single clock cycle.
    async fn read_and_adv_pc(&self) -> u8 {
        let pc = self.registers.with_ref(|r| r.pc);
        let value = self.read_u8(Ptr::from(pc)).await;
        self.registers.with_mut_ref(|r| r.pc = r.pc.wrapping_add(1));
        value
    }

    /// Invokes the processor's reset sequence.
    ///
    /// All registers are zeroed, and the program counter is set to the reset vector located at
    /// address 0xfffc.
    async fn reset(&self) {
        // The spec states that there is a 7-cycle initialization period for the processor before it
        // actually does anything. We'll skip emulating this since idk what it's actually doing for
        // those cycles.

        // Reset registers.
        self.registers.with_mut_ref(|r| *r = Default::default());

        // Load reset vector into program counter.
        let addr = self.read_u16(Ptr::RES).await;
        self.registers.with_mut_ref(|r| r.pc = addr);
    }

    /// Fetches and executes a single instruction.
    ///
    /// Returns an [`EmulationError::InvalidInstruction`] error if an unknown instruction was
    /// encountered. Lovely reference documentation can be found at
    /// https://www.masswerk.at/6502/6502_instruction_set.html
    async fn fetch_and_execute(&self) -> emu::Result<()> {
        log::trace!(target: "instr", "begin instruction");
        let opcode = self.read_and_adv_pc().await; // Cycle 1

        match opcode {
            // BRK
            0x00 => {
                // TODO: Trigger software interrupt.
                // TODO: Push return address (PC + 2) onto the stack.
                // TODO: Push SR onto stack with break flag set to 1.
            }

            // ORA X,ind
            0x01 => {
                log::trace!(target: "instr", "decoded: ORA X,ind");
                let ind = self.read_and_adv_pc().await; // Cycle 2

                // With zero-page addressing, the effective address will wrap around in the
                // zero-page instead of flowing into the next page.
                //
                // Cycle 3
                let effective_addr = self
                    .registers
                    .with_ref(|r| Ptr::from(r.x.wrapping_add(ind) as u16));
                self.end_cycle().await;

                // Cycle 4
                let value = self.read_u8(effective_addr).await;

                // Cycle 5
                let ac = self.registers.with_ref(|r| r.ac | value);
                self.end_cycle().await;

                // Cycle 6
                self.registers.with_mut_ref(|r| {
                    r.ac = ac;
                    r.set_negative_flag(ac & 0x80 != 0);
                    r.set_zero_flag(ac == 0);
                });
                self.end_cycle().await;

                log::debug!(target: "instr", "ORA X,${:02x}", ind);
            }

            // JAM
            0x02 => {
                log::warn!(target: "instr", "invalid instruction - halting");
                return Err(EmulationError::Halt);
            }

            // NOP
            0xea => {
                log::trace!(target: "instr", "NOP - begin");
                self.end_cycle().await; // Cycle 2
                log::debug!(target: "instr", "NOP");
            }

            _ => return Err(EmulationError::InvalidInstruction),
        };

        Ok(())
    }

    pub async fn run(&self) -> emu::Result<()> {
        self.reset().await;
        loop {
            self.fetch_and_execute().await?;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Executor, Rom};

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn instr_test<F>(data: &[u8], f: F)
    where
        F: FnOnce(SharedBus, Cpu, &mut Executor),
    {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());

        let mut executor = Executor::default();
        executor.add_task(cpu.run());

        for byte in data {
            bus.set_data(*byte);
            executor.poll().unwrap();
        }
    }

    #[test]
    fn reset() {
        init();
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());

        let mut executor = Executor::default();
        executor.add_task(cpu.run());

        // Data bus should not be clobbered, set to noop instruction.
        bus.set_data(0xea);
        executor.poll_n(3).unwrap();

        assert_eq!(cpu.registers.with_ref(|r| r.pc), 0xeaea);
    }

    #[test]
    fn ora_zero_page_x() -> emu::Result<()> {
        init();
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let rom_0 = Rom::from_data(bus.clone(), 0x0000, [0x42]);
        let rom_1 = Rom::from_data(
            bus.clone(),
            0xf000,
            [
                0x01, 0x00, // ORA $00,X
                0x02, // Halt
            ],
        );
        let rom_2 = Rom::from_data(
            bus.clone(),
            0xfffc,
            [
                0x00, 0xf0, // reset vector
                0x00, 0x00, // interrupt vector
            ],
        );

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(rom_0.run());
        executor.add_task(rom_1.run());
        executor.add_task(rom_2.run());
        executor.poll_until_halt()?;

        cpu.registers.with_ref(|r| {
            assert_eq!(0x42, r.ac);
        });
        Ok(())
    }
}
