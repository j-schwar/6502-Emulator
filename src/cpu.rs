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
    pub x: u8,
    /// General purpose Y register.
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

    fn set_ac_with_flags(&mut self, value: u8) {
        self.ac = value;
        self.set_negative_flag(self.ac & 0x80 != 0);
        self.set_zero_flag(self.ac == 0);
    }

    fn set_x_with_flags(&mut self, value: u8) {
        self.x = value;
        self.set_negative_flag(self.x & 0x80 != 0);
        self.set_zero_flag(self.x == 0);
    }

    fn set_y_with_flags(&mut self, value: u8) {
        self.y = value;
        self.set_negative_flag(self.y & 0x80 != 0);
        self.set_zero_flag(self.y == 0);
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
        self.bus.set_address(addr.raw(), BusDir::Read);
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
        self.bus.set_address(addr, BusDir::Read);

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
            self.bus.set_address(r.pc, BusDir::Read);
        });

        data
    }

    fn set_pc(&self, f: impl FnOnce(u16) -> u16) {
        self.registers.with_mut_ref(|r| r.pc = f(r.pc));
    }

    fn load_pc_onto_bus(&self) {
        self.registers.with_ref(|r| {
            self.bus.set_address(r.pc, BusDir::Read);
        });
    }

    /// Fetches and executes a single instruction.
    ///
    /// Returns an [`EmulationError::InvalidInstruction`] error if an unknown instruction was
    /// encountered. Lovely reference documentation can be found at
    /// https://www.masswerk.at/6502/6502_instruction_set.html
    async fn fetch_and_execute(&self) -> emu::Result<()> {
        let instruction_addr = Ptr::from(self.registers.with_ref(|r| r.pc));

        /// Expands to the execution steps for a 2-cycle immediate addressing mode instruction.
        macro_rules! immediate_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch operand.
                    let data = self.read_and_inc_pc();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, data);
                    self.end_cycle().await;

                    // Next Cycle - Execute instruction.
                    const BODY: fn(&mut Registers, u8) = $body;
                    self.registers.with_mut_ref(|r| BODY(r, data));
                }
            };
        }

        /// Expands to the execution steps for a 3-cycle zero-page addressing mode instruction.
        macro_rules! zero_page_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch ADL, compute and load effective address onto bus.
                    let adl = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));

                    let effective_address = adl as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 2 - Fetch data from effective address, load PC+2 onto bus.
                    let data = self.bus.data();
                    self.load_pc_onto_bus();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, adl);
                    self.end_cycle().await;

                    // Next Cycle - Execute instruction.
                    const BODY: fn(&mut Registers, u8) = $body;
                    self.registers.with_mut_ref(|r| BODY(r, data));
                }
            };
        }

        /// Expands to the execution steps for a 4-cycle zero-page X addressing mode instruction.
        macro_rules! zero_page_x_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch base address (BAL), load partial effective address onto bus.
                    let bal = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    let effective_address = bal as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 2 - Load actual effective address onto bus.
                    let effective_address = self
                        .registers
                        .with_ref(|r| effective_address.wrapping_add(r.x as u16) & 0x00ff);
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 3 - Fetch data from effective address, load PC+2 onto bus.
                    let data = self.bus.data();
                    self.load_pc_onto_bus();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, bal);
                    self.end_cycle().await;

                    // Next Cycle - Execute instruction.
                    const BODY: fn(&mut Registers, u8) = $body;
                    self.registers.with_mut_ref(|r| BODY(r, data));
                }
            };
        }

        /// Expands to the execution steps for a 4-cycle absolute addressing mode instruction.
        macro_rules! absolute_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch low order effective address byte.
                    let adl = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    self.load_pc_onto_bus();
                    self.end_cycle().await;

                    // Cycle 2 - Fetch high order effective address byte.
                    let adh = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    let effective_address = ((adh as u16) << 8) | adl as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 3 - Fetch data from effective address, load PC+3 onto bus.
                    let data = self.bus.data();
                    self.load_pc_onto_bus();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, effective_address);
                    self.end_cycle().await;

                    // Next Cycle - Execute instruction.
                    const BODY: fn(&mut Registers, u8) = $body;
                    self.registers.with_mut_ref(|r| BODY(r, data));
                }
            };
        }

        // Cycle 0 - Fetch opcode off of the data bus.
        let opcode = self.bus.data();
        self.set_pc(|pc| pc.wrapping_add(1));
        self.load_pc_onto_bus();
        self.end_cycle().await;

        match opcode {
            // JAM
            0x02 => return Err(EmulationError::Halt),

            0x09 => immediate_instr!("ORA #${:02x}", |r, imm| r.set_ac_with_flags(r.ac | imm)),

            0x29 => immediate_instr!("AND #${:02x}", |r, imm| r.set_ac_with_flags(r.ac & imm)),

            0xa0 => immediate_instr!("LDY #${:02x}", |r, imm| r.set_y_with_flags(imm)),

            0xa2 => immediate_instr!("LDX #${:02x}", |r, imm| r.set_x_with_flags(imm)),

            0xa4 => zero_page_instr!("LDY ${:02x}", |r, data| r.set_y_with_flags(data)),

            0xa5 => zero_page_instr!("LDA ${:02x}", |r, data| r.set_ac_with_flags(data)),

            0xa6 => zero_page_instr!("LDX ${:02x}", |r, data| r.set_x_with_flags(data)),

            0xa9 => immediate_instr!("LDA #${:02x}", |r, imm| r.set_ac_with_flags(imm)),

            0xad => absolute_instr!("LDA ${:04x}", |r, data| r.set_ac_with_flags(data)),

            0xb5 => zero_page_x_instr!("LDA ${:02x},X", |r, data| r.set_ac_with_flags(data)),

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
    use crate::mem::{ResetVector, Rom};

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    /// Executes given machine code until the CPU halts, where it then returns the state of the CPU
    /// registers.
    fn exec(machine_code: impl AsRef<[u8]>) -> emu::Result<Registers> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let rom = Rom::from_data(bus.clone(), 0xf000, machine_code.as_ref());
        let res = ResetVector::new(bus.clone(), 0xf000);

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(rom.run());
        executor.add_task(res.run());
        executor.poll_until_halt()?;

        Ok(cpu.registers.with_ref(|r| *r))
    }

    fn exec_with_mem(
        start_addr: u16,
        mem: impl AsRef<[u8]>,
        machine_code: impl AsRef<[u8]>,
    ) -> emu::Result<Registers> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let zero_page = Rom::from_data(bus.clone(), start_addr, mem.as_ref());
        let rom = Rom::from_data(bus.clone(), 0xf000, machine_code.as_ref());
        let res = ResetVector::new(bus.clone(), 0xf000);

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(zero_page.run());
        executor.add_task(rom.run());
        executor.add_task(res.run());
        executor.poll_until_halt()?;

        Ok(cpu.registers.with_ref(|r| *r))
    }

    fn exec_with_zero_page(
        zero_page: impl AsRef<[u8]>,
        machine_code: impl AsRef<[u8]>,
    ) -> emu::Result<Registers> {
        exec_with_mem(0x0000, zero_page, machine_code)
    }

    #[test]
    fn lda_immediate() -> emu::Result<()> {
        init();
        let r = exec([
            0xa9, 0x01, // LDA #$01
            0x02, // Halt
        ])?;
        assert_eq!(0x01, r.ac);
        Ok(())
    }

    #[test]
    fn lda_zero_page() -> emu::Result<()> {
        init();
        let zp = [0x00, 0x00, 0x42, 0x00, 0x00, 0x00];

        let r = exec_with_zero_page(
            zp,
            [
                0xa5, 0x02, // LDA $02
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.ac);
        Ok(())
    }

    #[test]
    fn lda_zero_page_x() -> emu::Result<()> {
        init();
        let zp = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05];

        let r = exec_with_zero_page(
            zp,
            [
                0xa2, 0x01, // LDX #$01
                0xb5, 0x04, // LDA $04,X
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x05, r.ac);
        Ok(())
    }

    #[test]
    fn zero_page_x_overflow_behavior() -> emu::Result<()> {
        init();
        let zp = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05];

        let r = exec_with_zero_page(
            zp,
            [
                0xa2, 0x03, // LDX #$03
                0xb5, 0xff, // LDA $ff,X
                0x02, // Halt
            ],
        )?;

        // Overflow behavior for zero-page X addressing mode should wrap around to the start of the
        // zero page instead of going into the next page.
        assert_eq!(0x02, r.ac);
        Ok(())
    }

    #[test]
    fn lda_absolute() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05],
            [
                0xad, 0x03, 0x20, // LDA $2003
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x03, r.ac);
        Ok(())
    }

    #[test]
    fn ldx_immediate() -> emu::Result<()> {
        init();
        let r = exec([
            0xa2, 0x01, // LDX #$01
            0x02, // Halt
        ])?;
        assert_eq!(0x01, r.x);
        Ok(())
    }

    #[test]
    fn ldx_zero_page() -> emu::Result<()> {
        init();
        let zp = [0x00, 0x00, 0x42, 0x00, 0x00, 0x00];

        let r = exec_with_zero_page(
            zp,
            [
                0xa6, 0x02, // LDX $02
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.x);
        Ok(())
    }

    #[test]
    fn ldy_zero_page() -> emu::Result<()> {
        init();
        let zp = [0x00, 0x00, 0x42, 0x00, 0x00, 0x00];

        let r = exec_with_zero_page(
            zp,
            [
                0xa4, 0x02, // LDY $02
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.y);
        Ok(())
    }

    #[test]
    fn ldy_immediate() -> emu::Result<()> {
        init();
        let r = exec([
            0xa0, 0x01, // LDY #$01,
            0x02, // Halt
        ])?;
        assert_eq!(0x01, r.y);
        Ok(())
    }

    #[test]
    fn ora_immediate() -> emu::Result<()> {
        init();
        let r = exec([
            0xa9, 0x01, // LDA #$01,
            0x09, 0x02, // ORA #$02,
            0x02, // Halt
        ])?;
        assert_eq!(0x03, r.ac);
        Ok(())
    }

    #[test]
    fn and_immediate() -> emu::Result<()> {
        init();
        let r = exec([
            0xa9, 0x0f, // LDA #$0f,
            0x29, 0x8a, // AND #$8a,
            0x02, // Halt
        ])?;
        assert_eq!(0x0a, r.ac);
        Ok(())
    }
}
