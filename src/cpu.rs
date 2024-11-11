//! 6502 CPU Emulator

use with_ref::{ScopedRefCell, WithRef};

use crate::emu::{self, BusDir, EmulationError, Ptr, SharedBus};

/// Models CPU state.
#[derive(Clone, Copy, Debug, Default)]
pub struct Registers {
    /// Program counter register.
    pub pc: u16,
    /// Accumulator register.
    pub ac: u8,
    /// General purpose X register.
    #[expect(unused)]
    pub x: u8,
    /// General purpose Y register.
    #[expect(unused)]
    pub y: u8,
    /// Status register.
    pub sr: u8,
    /// Stack pointer.
    #[expect(unused)]
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
    #[expect(unused)]
    fn set_overflow_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x40, value);
    }

    /// Sets the break flag (B) in the status register.
    #[expect(unused)]
    fn set_break_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x10, value);
    }

    /// Sets the decimal flag (D) in the status register.
    #[expect(unused)]
    fn set_decimal_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x08, value);
    }

    /// Sets the interrupt disable flag (I) in the status register.
    #[expect(unused)]
    fn set_interrupt_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x04, value);
    }

    /// Sets the zero flag (Z) in the status register.
    fn set_zero_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x02, value);
    }

    /// Sets the carry flag (C) in the status register.
    #[expect(unused)]
    fn set_carry_flag(&mut self, value: bool) {
        set_bit!(self.sr, 0x01, value);
    }
}

pub struct Cpu {
    bus: SharedBus,
    pub registers: ScopedRefCell<Registers>,
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
        self.bus.set_address(Ptr::from(addr), BusDir::Read);

        log::debug!(target: "cpu", "reset complete - pc = {}", Ptr::from(addr));
        self.end_cycle().await;
    }

    /// Reads from the data bus and increments the program counter.
    ///
    /// Specifically, this function does the following in order:
    /// 1. Reads from the data bus.
    /// 2. Increments the program counter register.
    /// 3. Loads the program counter register onto the address bus.
    ///
    /// The address being read from is determine by whatever was on the address bus at the end of
    /// the previous cycle.
    fn read_and_inc_pc(&self) -> u8 {
        let data = self.bus.data();
        self.registers.with_mut_ref(|r| {
            r.pc = r.pc.wrapping_add(1);
            self.bus.set_address(Ptr::from(r.pc), BusDir::Read);
        });

        data
    }

    /// Sets the accumulator register to the result of a given closure. Arithmetic flags (N, Z) are
    /// set based on the new accumulator value.
    fn set_ac_and_arithmetic_flags(&self, f: impl FnOnce(&Registers) -> u8) {
        self.registers.with_mut_ref(|r| {
            r.ac = f(r);
            r.set_negative_flag(r.ac & 0x80 != 0);
            r.set_zero_flag(r.ac == 0);
        });
    }

    /// Fetches and executes a single instruction.
    ///
    /// Returns an [`EmulationError::InvalidInstruction`] error if an unknown instruction was
    /// encountered. Lovely reference documentation can be found at
    /// https://www.masswerk.at/6502/6502_instruction_set.html
    async fn fetch_and_execute(&self) -> emu::Result<()> {
        let instruction_addr = Ptr::from(self.registers.with_ref(|r| r.pc));

        // Cycle 0 - Fetch opcode off of the data bus.
        let opcode = self.read_and_inc_pc();
        self.end_cycle().await;

        match opcode {
            // JAM
            0x02 => {
                return Err(EmulationError::Halt);
            }

            // ORA #oper
            0x09 => {
                // Cycle 1 - Fetch operand.
                let data = self.read_and_inc_pc();
                log::info!(target: "instr", "{} ORA #{:02x}", instruction_addr, data);
                self.end_cycle().await;

                // Next Cycle - Execute instruction.
                self.set_ac_and_arithmetic_flags(|r| r.ac | data);
            }

            // NOP
            0xea => {
                // Cycle 1 - Do nothing.
                self.end_cycle().await;

                // Log after as this instruction should take 2 cycles.
                log::info!(target: "instr", "{} NOP", instruction_addr);
            }

            _ => return Err(EmulationError::InvalidInstruction),
        }

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
    use crate::emu::Executor;
    use crate::mem::Rom;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    // #[test]
    // fn reset() {
    //     init();
    //     let bus = SharedBus::default();
    //     let cpu = Cpu::new(bus.clone());

    //     let mut executor = Executor::default();
    //     executor.add_task(cpu.run());

    //     // Data bus should not be clobbered, set to noop instruction.
    //     bus.set_data(0xea);
    //     executor.poll_n(3).unwrap();

    //     assert_eq!(cpu.registers.with_ref(|r| r.pc), 0xeaea);
    // }

    #[test]
    fn ora_immediate() -> emu::Result<()> {
        init();
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let instructions = Rom::from_data(
            bus.clone(),
            0xf000,
            [
                0x09, 0x42, // ORA #01
                0x02, // Halt
            ],
        );
        let res_vector = Rom::from_data(bus.clone(), 0xfffc, [0x00, 0xf0]);

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(instructions.run());
        executor.add_task(res_vector.run());
        executor.poll_until_halt()?;

        cpu.registers.with_ref(|r| {
            assert_eq!(0x42, r.ac);
        });
        Ok(())
    }
}
