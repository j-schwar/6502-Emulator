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
    /// encountered.
    ///
    /// Reference for instructions: https://www.masswerk.at/6502/6502_instruction_set.html
    /// Reference for cycle timings: https://web.archive.org/web/20120227142944if_/http://archive.6502.org:80/datasheets/synertek_hardware_manual.pdf
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
        /// In addition to the format string and expression body, the offset register must also be
        /// supplied to this macro.
        macro_rules! zero_page_offset_instr {
            ($fmt:literal, $reg:ident, $body:expr) => {
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
                        .with_ref(|r| effective_address.wrapping_add(r.$reg as u16) & 0x00ff);
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

        /// Expands to the execution steps for a 4 or 5-cycle absolute with offset addressing mode
        /// instruction. In addition to the format string and expression body, the offset register
        /// must also be supplied to this macro.
        macro_rules! absolute_offset_instr {
            ($fmt:literal, $reg:ident, $body:expr) => {
                {
                    // Cycle 1 - Fetch low order effective address byte.
                    let adl = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    self.load_pc_onto_bus();
                    self.end_cycle().await;

                    // Cycle 2 - Fetch high order effective address byte.
                    let adh = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    let (adl, carry) = self.registers.with_mut_ref(|r| {
                        let (value, carry) = adl.overflowing_add(r.$reg);
                        r.set_carry_flag(carry);
                        (value, carry)
                    });
                    let effective_address = ((adh as u16) << 8) | adl as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 3 - Fetch data or recompute effective address depending on if page boundary
                    // was crossed (i.e., the carry bit was set via the previous computation).
                    let data = if !carry {
                        self.bus.data()
                    } else {
                        let effective_address = ((adh.wrapping_add(1) as u16) << 8) | adl as u16;
                        self.bus.set_address(effective_address, BusDir::Read);
                        self.end_cycle().await;

                        // Cycle 4 - Fetch data.
                        self.bus.data()
                    };
                    self.load_pc_onto_bus();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, effective_address);
                    self.end_cycle().await;

                    // Next Cycle - Execute instruction.
                    const BODY: fn(&mut Registers, u8) = $body;
                    self.registers.with_mut_ref(|r| BODY(r, data));
                }
            };
        }

        /// Expands to the execution steps for a 6-cycle indirect X addressing mode instruction.
        macro_rules! indirect_x_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch base address (BAL), load partial effective address onto bus.
                    let bal = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    let effective_address = bal as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 2 - Load actual effective address onto bus.
                    let x = self.registers.with_ref(|r| r.x);
                    let effective_address = bal.wrapping_add(x) as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 3 - Fetch low order byte of indirect address.
                    let adl = self.bus.data();
                    let effective_address = bal.wrapping_add(x).wrapping_add(1) as u16;
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 4 - Fetch high order byte of indirect address.
                    let adh = self.bus.data();
                    let indirect_address = u16::from_le_bytes([adl, adh]);
                    self.bus.set_address(indirect_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 5 - Fetch data.
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

        /// Expands to the execution steps for a 5 or 6-cycle indirect Y addressing mode instruction.
        macro_rules! indirect_y_instr {
            ($fmt:literal, $body:expr) => {
                {
                    // Cycle 1 - Fetch zero page indirect address.
                    let ial = self.bus.data();
                    self.set_pc(|pc| pc.wrapping_add(1));
                    let indirect_address = ial as u16;
                    self.bus.set_address(indirect_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 2 - Fetch low order byte of base address.
                    let bal = self.bus.data();
                    let indirect_address = ial.wrapping_add(1) as u16;
                    self.bus.set_address(indirect_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 3 - Fetch high order byte of base address.
                    let bah = self.bus.data();
                    let (adl, carry) = self.registers.with_mut_ref(|r| {
                        let (value, carry) = bal.overflowing_add(r.y);
                        r.set_carry_flag(carry);
                        (value, carry)
                    });
                    let effective_address = u16::from_le_bytes([adl, bah]);
                    self.bus.set_address(effective_address, BusDir::Read);
                    self.end_cycle().await;

                    // Cycle 4 - Fetch data or recompute address if carry flag is set.
                    let data = if !carry {
                        self.bus.data()
                    } else {
                        let adh = bah.wrapping_add(1);
                        let effective_address = u16::from_le_bytes([adl, adh]);
                        self.bus.set_address(effective_address, BusDir::Read);
                        self.end_cycle().await;

                        // Cycle 5 - Fetch data.
                        self.bus.data()
                    };
                    self.load_pc_onto_bus();
                    log::info!(target: "instr", concat!("{} ", $fmt), instruction_addr, ial);
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

            0xa1 => indirect_x_instr!("LDA (${:02x},X)", |r, data| r.set_ac_with_flags(data)),

            0xa2 => immediate_instr!("LDX #${:02x}", |r, imm| r.set_x_with_flags(imm)),

            0xa4 => zero_page_instr!("LDY ${:02x}", |r, data| r.set_y_with_flags(data)),

            0xa5 => zero_page_instr!("LDA ${:02x}", |r, data| r.set_ac_with_flags(data)),

            0xa6 => zero_page_instr!("LDX ${:02x}", |r, data| r.set_x_with_flags(data)),

            0xa9 => immediate_instr!("LDA #${:02x}", |r, imm| r.set_ac_with_flags(imm)),

            0xac => absolute_instr!("LDY ${:04x}", |r, data| r.set_y_with_flags(data)),

            0xad => absolute_instr!("LDA ${:04x}", |r, data| r.set_ac_with_flags(data)),

            0xae => absolute_instr!("LDX ${:04x}", |r, data| r.set_x_with_flags(data)),

            0xb1 => indirect_y_instr!("LDA (${:02x}),Y", |r, data| r.set_ac_with_flags(data)),

            0xb4 => zero_page_offset_instr!("LDY ${:02},X", x, |r, data| r.set_y_with_flags(data)),

            0xb5 => {
                zero_page_offset_instr!("LDA ${:02x},X", x, |r, data| r.set_ac_with_flags(data))
            }

            0xb6 => zero_page_offset_instr!("LDX ${:02x},Y", y, |r, data| r.set_x_with_flags(data)),

            0xb9 => absolute_offset_instr!("LDA ${:04x},Y", y, |r, data| r.set_ac_with_flags(data)),

            0xbc => absolute_offset_instr!("LDY ${:04x},X", x, |r, data| r.set_y_with_flags(data)),

            0xbd => absolute_offset_instr!("LDA ${:04x},X", x, |r, data| r.set_ac_with_flags(data)),

            0xbe => absolute_offset_instr!("LDX ${:04x},Y", y, |r, data| r.set_x_with_flags(data)),

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

    /// Executes given machine code until the CPU halts, where it then returns the state of the CPU
    /// registers. An additional chunk of memory with a specified state location along with the
    /// zero-page is also provided to the emulator.
    fn exec_with_zero_page_and_mem(
        zero_page: impl AsRef<[u8]>,
        start_addr: u16,
        mem: impl AsRef<[u8]>,
        machine_code: impl AsRef<[u8]>,
    ) -> emu::Result<Registers> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let zero_page = Rom::from_data(bus.clone(), 0x0000, zero_page.as_ref());
        let mem = Rom::from_data(bus.clone(), start_addr, mem.as_ref());
        let rom = Rom::from_data(bus.clone(), 0xf000, machine_code.as_ref());
        let res = ResetVector::new(bus.clone(), 0xf000);

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(zero_page.run());
        executor.add_task(mem.run());
        executor.add_task(rom.run());
        executor.add_task(res.run());
        executor.poll_until_halt()?;

        Ok(cpu.registers.with_ref(|r| *r))
    }

    /// Executes given machine code until the CPU halts, where it then returns the state of the CPU
    /// registers. An additional chunk of memory with a specified state location is also provided to
    /// the emulator.
    fn exec_with_mem(
        start_addr: u16,
        mem: impl AsRef<[u8]>,
        machine_code: impl AsRef<[u8]>,
    ) -> emu::Result<Registers> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let mem = Rom::from_data(bus.clone(), start_addr, mem.as_ref());
        let rom = Rom::from_data(bus.clone(), 0xf000, machine_code.as_ref());
        let res = ResetVector::new(bus.clone(), 0xf000);

        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(mem.run());
        executor.add_task(rom.run());
        executor.add_task(res.run());
        executor.poll_until_halt()?;

        Ok(cpu.registers.with_ref(|r| *r))
    }

    /// Executes given machine code until the CPU halts, where it then returns the state of the CPU
    /// registers. The zero-page chunk of memory is also provided to the emulator.
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
    fn lda_ldx_ldy_absolute() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05],
            [
                0xac, 0x02, 0x20, // LDY $2002
                0xad, 0x03, 0x20, // LDA $2003
                0xae, 0x04, 0x20, // LDX $2004
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x02, r.y);
        assert_eq!(0x03, r.ac);
        assert_eq!(0x04, r.x);
        Ok(())
    }

    #[test]
    fn lda_absolute_offset_x() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05],
            [
                0xa2, 0x03, // LDX #$03
                0xbd, 0x00, 0x20, // LDA $2000,X
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x03, r.ac);
        Ok(())
    }

    #[test]
    fn lda_absolute_offset_y() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05],
            [
                0xa0, 0x03, // LDY #$03
                0xb9, 0x00, 0x20, // LDA $2000,Y
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x03, r.ac);
        Ok(())
    }

    #[test]
    fn lda_indirect_x() -> emu::Result<()> {
        init();

        let r = exec_with_zero_page_and_mem(
            [
                0x02, 0x20, // $0000
                0x03, 0x20, // $0002
                0x04, 0x20, // $0004
            ],
            0x2000,
            [
                0xde, 0xae, // $2000
                0xdb, 0xea, // $2002
                0x42, 0xff, // $2004
            ],
            [
                0xa2, 0x02, // LDX #$02
                0xa1, 0x02, // LDA ($02,X)
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.ac);
        Ok(())
    }

    #[test]
    fn lda_indirect_y() -> emu::Result<()> {
        init();

        let r = exec_with_zero_page_and_mem(
            [
                0x02, 0x20, // $0000
                0x03, 0x20, // $0002
                0x04, 0x20, // $0004
            ],
            0x2000,
            [
                0xde, 0xae, // $2000
                0xdb, 0xea, // $2002
                0x42, 0xff, // $2004
            ],
            [
                0xa0, 0x01, // LDY #$01
                0xb1, 0x02, // LDA ($02),Y
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.ac);
        Ok(())
    }

    #[test]
    fn lda_indirect_y_with_page_overflow() -> emu::Result<()> {
        init();

        let r = exec_with_zero_page_and_mem(
            [
                0x02, 0x20, // $0000
                0xf4, 0x1f, // $0002
                0x04, 0x20, // $0004
            ],
            0x2000,
            [
                0xde, 0xae, // $2000
                0xdb, 0xea, // $2002
                0x42, 0xff, // $2004
            ],
            [
                0xa0, 0x10, // LDY #$10
                0xb1, 0x02, // LDA ($02),Y
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x42, r.ac);
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
    fn ldx_zero_page_y() -> emu::Result<()> {
        init();
        let r = exec_with_zero_page(
            [
                0x00, 0x01, // $0000
                0x02, 0x03, // $0002
                0x04, 0x05, // $0004
            ],
            [
                0xa0, 0x01, // LDY #$01
                0xb6, 0x04, // LDX $04,Y
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x05, r.x);
        Ok(())
    }

    #[test]
    fn ldy_zero_page_x() -> emu::Result<()> {
        init();
        let r = exec_with_zero_page(
            [
                0x00, 0x01, // $0000
                0x02, 0x03, // $0002
                0x04, 0x05, // $0004
            ],
            [
                0xa2, 0x01, // LDX #$01
                0xb4, 0x04, // LDY $04,X
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x05, r.y);
        Ok(())
    }

    #[test]
    fn ldx_absolute_y() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [
                0x00, 0x01, // $2000
                0x02, 0x03, // $2002
                0x04, 0x05, // $2004
            ],
            [
                0xa0, 0x01, // LDY #$01
                0xbe, 0x04, 0x20, // LDX $2004,Y
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x05, r.x);
        Ok(())
    }

    #[test]
    fn ldy_absolute_x() -> emu::Result<()> {
        init();
        let r = exec_with_mem(
            0x2000,
            [
                0x00, 0x01, // $2000
                0x02, 0x03, // $2002
                0x04, 0x05, // $2004
            ],
            [
                0xa2, 0x01, // LDX #$01
                0xbc, 0x04, 0x20, // LDY $2004,X
                0x02, // Halt
            ],
        )?;

        assert_eq!(0x05, r.y);
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
