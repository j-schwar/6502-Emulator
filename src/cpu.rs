//! 6502 CPU Emulator

use with_ref::{ScopedRefCell, WithRef};

use crate::emu::{self, BusDir, EmulationError, Ptr, SharedBus};

/// A collection of flags which make up the processor's status register.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StatusRegister(u8);

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

macro_rules! get_bit {
    ($receiver:expr, $bit:literal) => {
        $receiver & $bit != 0
    };
}

impl StatusRegister {
    /// Sets the negative (N) flag in the status register.
    pub fn set_negative_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x80, value);
    }

    /// Sets the overflow (V) flag in the status register.
    #[expect(unused)]
    pub fn set_overflow_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x40, value);
    }

    /// Sets the break flag (B) in the status register.
    #[expect(unused)]
    pub fn set_break_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x10, value);
    }

    /// Sets the decimal flag (D) in the status register.
    #[expect(unused)]
    pub fn set_decimal_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x08, value);
    }

    /// Sets the interrupt disable flag (I) in the status register.
    #[expect(unused)]
    pub fn set_interrupt_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x04, value);
    }

    /// Sets the zero flag (Z) in the status register.
    pub fn set_zero_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x02, value);
    }

    /// Sets the carry flag (C) in the status register.
    pub fn set_carry_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x01, value);
    }

    /// Gets the carry flag (C) in the status register.
    pub fn carry_flag(&self) -> bool {
        get_bit!(self.0, 0x01)
    }

    /// Gets the zero flag (Z) in the status register.
    pub fn zero_flag(&self) -> bool {
        get_bit!(self.0, 0x02)
    }

    /// Gets the negative flag (N) in the status register.
    pub fn negative_flag(&self) -> bool {
        get_bit!(self.0, 0x80)
    }
}

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
    pub sr: StatusRegister,
    /// Stack pointer.
    #[expect(unused)]
    pub sp: u8,
}

impl Registers {
    /// Sets the Accumulator register along with the Negative and Zero flags.
    fn set_ac_with_flags(&mut self, value: u8) {
        self.ac = value;
        self.sr.set_negative_flag(self.ac & 0x80 != 0);
        self.sr.set_zero_flag(self.ac == 0);
    }

    /// Sets the X register along with the Negative and Zero flags.
    fn set_x_with_flags(&mut self, value: u8) {
        self.x = value;
        self.sr.set_negative_flag(self.x & 0x80 != 0);
        self.sr.set_zero_flag(self.x == 0);
    }

    /// Sets the Y register along with the Negative and Zero flags.
    fn set_y_with_flags(&mut self, value: u8) {
        self.y = value;
        self.sr.set_negative_flag(self.y & 0x80 != 0);
        self.sr.set_zero_flag(self.y == 0);
    }
}

struct ExecCtx<'a> {
    address: u16,
    cpu: &'a Cpu,
}

impl<'a> ExecCtx<'a> {
    /// Returns the value of the `X` register.
    fn reg_x(&self) -> u8 {
        self.cpu.registers.with_ref(|r| r.x)
    }

    /// Returns the value of the `Y` register.
    fn reg_y(&self) -> u8 {
        self.cpu.registers.with_ref(|r| r.y)
    }

    /// Returns the value of the accumulator register.
    #[expect(dead_code)]
    fn reg_ac(&self) -> u8 {
        self.cpu.registers.with_ref(|r| r.ac)
    }

    /// Executes a single cycle instruction.
    ///
    /// This function takes 1 cycle to complete. It's implied that the first cycle for fetching the
    /// opcode has already passed before this function is called.
    async fn single_cycle(&self, mnemonic: &str, body: fn(&mut Registers)) {
        self.cpu.registers.with_mut_ref(|r| body(r));

        log::info!(target: "instr", "{:#06x} {}", self.address, mnemonic);
        self.cpu.end_cycle().await;
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with immediate addressing.
    ///
    /// The total duration of instructions of this type is 2 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_immediate(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        // Cycle 1 - Fetch operand.
        let data = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} #${:02x}", self.address, mnemonic, data);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with zero-page addressing.
    ///
    /// The total duration of instructions of this type is 3 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_zero_page(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        // Cycle 1 - Fetch ADL, compute and load effective address onto bus.
        let adl = self.cpu.read_and_inc_pc();
        let effective_address = adl as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch data from effective address, load PC+2 onto bus.
        let data = self.cpu.bus.data();
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} ${:02x}", self.address, mnemonic, adl);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with zero-page offset addressing.
    async fn iem_zero_page_with_offset(
        &self,
        offset: u8,
        offset_register: char,
        mnemonic: &str,
        body: fn(&mut Registers, u8),
    ) {
        // Cycle 1 - Fetch base address (BAL), load partial effective address onto bus.
        let bal = self.cpu.read_and_inc_pc();
        let effective_address = bal as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Load actual effective address onto bus.
        let effective_address = effective_address.wrapping_add(offset as u16) & 0x00ff;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch data from effective address, load PC+2 onto bus.
        let data = self.cpu.bus.data();
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} ${:02x},{}", self.address, mnemonic, bal, offset_register);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with zero-page X addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_zero_page_x(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        let x = self.cpu.registers.with_ref(|r| r.x);
        self.iem_zero_page_with_offset(x, 'X', mnemonic, body).await;
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with zero-page Y addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_zero_page_y(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        let y = self.cpu.registers.with_ref(|r| r.y);
        self.iem_zero_page_with_offset(y, 'Y', mnemonic, body).await;
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with absolute addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_absolute(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        // Cycle 1 - Fetch low order effective address byte.
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order effective address byte.
        let adh = self.cpu.read_and_inc_pc();
        let effective_address = ((adh as u16) << 8) | adl as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch data from effective address, load PC+3 onto bus.
        let data = self.cpu.bus.data();
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} ${:04x}", self.address, mnemonic, effective_address);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with absolute offset addressing.
    async fn iem_absolute_with_offset(
        &self,
        offset: u8,
        offset_register: char,
        mnemonic: &str,
        body: fn(&mut Registers, u8),
    ) {
        // Cycle 1 - Fetch low order effective address byte.
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order effective address byte.
        let adh = self.cpu.read_and_inc_pc();
        let (adl, carry) = self.cpu.registers.with_mut_ref(|r| {
            let (value, carry) = adl.overflowing_add(offset);
            r.sr.set_carry_flag(carry);
            (value, carry)
        });
        let effective_address = ((adh as u16) << 8) | adl as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch data or recompute effective address depending on if page boundary
        // was crossed (i.e., the carry bit was set via the previous computation).
        let data = if !carry {
            self.cpu.bus.data()
        } else {
            let effective_address = ((adh.wrapping_add(1) as u16) << 8) | adl as u16;
            self.cpu.bus.set_address(effective_address, BusDir::Read);
            self.cpu.end_cycle().await;

            // Cycle 4 - Fetch data.
            self.cpu.bus.data()
        };
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} ${:04x},{}", self.address, mnemonic, effective_address, offset_register);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with absolute X addressing.
    ///
    /// The total duration of instructions of this type is 4 or 5 cycles depending on whether a page
    /// boundary is crossed when computing the effective address. It's implied that the first cycle
    /// for fetching the instruction opcode has already passed before this function is called. As
    /// with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_absolute_x(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        let offset = self.cpu.registers.with_ref(|r| r.x);
        self.iem_absolute_with_offset(offset, 'X', mnemonic, body)
            .await
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with absolute Y addressing.
    ///
    /// The total duration of instructions of this type is 4 or 5 cycles depending on whether a page
    /// boundary is crossed when computing the effective address. It's implied that the first cycle
    /// for fetching the instruction opcode has already passed before this function is called. As
    /// with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_absolute_y(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        let offset = self.cpu.registers.with_ref(|r| r.y);
        self.iem_absolute_with_offset(offset, 'Y', mnemonic, body)
            .await
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with indirect X addressing.
    ///
    /// The total duration of instructions of this type is 6 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    /// As with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_indirect_x(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        // Cycle 1 - Fetch base address (BAL), load partial effective address onto bus.
        let bal = self.cpu.read_and_inc_pc();
        let effective_address = bal as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Load actual effective address onto bus.
        let x = self.cpu.registers.with_ref(|r| r.x);
        let effective_address = bal.wrapping_add(x) as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch low order byte of indirect address.
        let adl = self.cpu.bus.data();
        let effective_address = bal.wrapping_add(x).wrapping_add(1) as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 4 - Fetch high order byte of indirect address.
        let adh = self.cpu.bus.data();
        let indirect_address = u16::from_le_bytes([adl, adh]);
        self.cpu.bus.set_address(indirect_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 5 - Fetch data.
        let data = self.cpu.bus.data();
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} (${:02x},X)", self.address, mnemonic, bal);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes an Internal Execution on Memory (IEM) instruction with indirect Y addressing.
    ///
    /// The total duration of instructions of this type is 5 or 6 cycles depending on whether a page
    /// boundary is crossed when computing the effective address. It's implied that the first cycle
    /// for fetching the instruction opcode has already passed before this function is called. As
    /// with all IEM instructions, the actual execution of the instruction takes place during the
    /// fetching and decoding of the next instruction.
    async fn iem_indirect_y(&self, mnemonic: &str, body: fn(&mut Registers, u8)) {
        // Cycle 1 - Fetch zero page indirect address.
        let ial = self.cpu.read_and_inc_pc();
        let indirect_address = ial as u16;
        self.cpu.bus.set_address(indirect_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch low order byte of base address.
        let bal = self.cpu.bus.data();
        let indirect_address = ial.wrapping_add(1) as u16;
        self.cpu.bus.set_address(indirect_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch high order byte of base address.
        let bah = self.cpu.bus.data();
        let (adl, carry) = self.cpu.registers.with_mut_ref(|r| {
            let (value, carry) = bal.overflowing_add(r.y);
            r.sr.set_carry_flag(carry);
            (value, carry)
        });
        let effective_address = u16::from_le_bytes([adl, bah]);
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 4 - Fetch data or recompute address if carry flag is set.
        let data = if !carry {
            self.cpu.bus.data()
        } else {
            let adh = bah.wrapping_add(1);
            let effective_address = u16::from_le_bytes([adl, adh]);
            self.cpu.bus.set_address(effective_address, BusDir::Read);
            self.cpu.end_cycle().await;

            // Cycle 5 - Fetch data.
            self.cpu.bus.data()
        };
        self.cpu.load_pc_onto_bus();
        log::info!(target: "instr", "{:#06x} {} (${:02x}),Y", self.address, mnemonic, ial);
        self.cpu.end_cycle().await;

        // Next Cycle - Execute instruction.
        self.cpu.registers.with_mut_ref(|r| body(r, data));
    }

    /// Executes a store instruction with zero page addressing.
    ///
    /// The total duration of instructions of this type is 3 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_zero_page(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        // Cycle 1 - Compute effective address and write data to bus.
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        let effective_address = self.cpu.bus.data() as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        let value = self.cpu.registers.with_ref(|r| body(r));
        self.cpu.bus.set_data(value);
        log::info!(target: "instr", "{:#06x} {} ${:02x}", self.address, mnemonic, effective_address);
        self.cpu.end_cycle().await;

        // Cycle 2
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a store instruction with zero page offset addressing.
    async fn store_zero_page_offset(
        &self,
        offset: u8,
        offset_register: char,
        mnemonic: &str,
        body: fn(&Registers) -> u8,
    ) {
        // Cycle 1 - Fetch zero page base address
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        let base_address = self.cpu.bus.data();
        self.cpu.bus.set_address(base_address as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Compute effective address
        let effective_address = base_address.wrapping_add(offset) as u16;
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(self.cpu.registers.with_ref(body));
        log::info!(target: "instr", "{:#06x} {} ${:02x},{}", self.address, mnemonic, base_address, offset_register);
        self.cpu.end_cycle().await;

        // Cycle 3
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a store instruction with zero page X addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_zero_page_x(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        let offset = self.cpu.registers.with_ref(|r| r.x);
        self.store_zero_page_offset(offset, 'X', mnemonic, body)
            .await;
    }

    /// Executes a store instruction with zero page Y addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_zero_page_y(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        let offset = self.cpu.registers.with_ref(|r| r.y);
        self.store_zero_page_offset(offset, 'Y', mnemonic, body)
            .await;
    }

    /// Executes a store instruction with absolute addressing.
    ///
    /// The total duration of instructions of this type is 4 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_absolute(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        // Cycle 1 - Fetch low order byte of address
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order by of address
        let adh = self.cpu.read_and_inc_pc();
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(self.cpu.registers.with_ref(body));
        log::info!(target: "instr", "{:#06x} {} ${:04x}", self.address, mnemonic, effective_address);
        self.cpu.end_cycle().await;

        // Cycle 3
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a store instruction with absolute offset addressing.
    async fn store_absolute_offset(
        &self,
        offset: u8,
        offset_register: char,
        mnemonic: &str,
        body: fn(&Registers) -> u8,
    ) {
        // Cycle 1 - Fetch low order byte of address
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order by of address
        let adh = self.cpu.bus.data();
        let (adl, carry) = self.cpu.registers.with_mut_ref(|r| {
            let (value, carry) = adl.overflowing_add(offset);
            r.sr.set_carry_flag(carry);
            (value, carry)
        });
        let adh = adh.wrapping_add(if carry { 1 } else { 0 });
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Store data
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(self.cpu.registers.with_ref(body));
        log::info!(target: "instr", "{:#06x} {} ${:04x},{}", self.address, mnemonic, effective_address, offset_register);
        self.cpu.end_cycle().await;

        // Cycle 4
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a store instruction with absolute X addressing.
    ///
    /// The total duration of instructions of this type is 5 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_absolute_x(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        let offset = self.cpu.registers.with_ref(|r| r.x);
        self.store_absolute_offset(offset, 'X', mnemonic, body)
            .await;
    }

    /// Executes a store instruction with absolute Y addressing.
    ///
    /// The total duration of instructions of this type is 5 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_absolute_y(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        let offset = self.cpu.registers.with_ref(|r| r.y);
        self.store_absolute_offset(offset, 'Y', mnemonic, body)
            .await;
    }

    /// Executes a store instruction with indirect X addressing.
    ///
    /// The total duration of instructions of this type is 6 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_indirect_x(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        // Cycle 1 - Grab low byte of base address
        let bal = self.cpu.read_and_inc_pc();
        self.cpu.bus.set_address(bal as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Load indirect address onto bus
        let bal = bal.wrapping_add(self.reg_x());
        self.cpu.bus.set_address(bal as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Read low byte of effective address from bus
        let adl = self.cpu.bus.data();
        let bal = bal.wrapping_add(1);
        self.cpu.bus.set_address(bal as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 4 - Read high byte of effective address from bus
        let adh = self.cpu.bus.data();
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(self.cpu.registers.with_ref(body));
        log::info!(target: "instr", "{:#06x} {} (${:02x},X)", self.address, mnemonic, bal);
        self.cpu.end_cycle().await;

        // Cycle 5
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a store instruction with indirect Y addressing.
    ///
    /// The total duration of instructions of this type is 6 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn store_indirect_y(&self, mnemonic: &str, body: fn(&Registers) -> u8) {
        // Cycle 1 - Fetch indirect address from zero page
        let ial = self.cpu.read_and_inc_pc();
        self.cpu.bus.set_address(ial as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch low byte of effective address
        let bal = self.cpu.bus.data();
        let ial = ial.wrapping_add(1);
        self.cpu.bus.set_address(ial as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch high byte of effective address
        let bah = self.cpu.bus.data();
        let adl = bal.wrapping_add(self.reg_y());
        let adh = bah;
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 4 - Write data
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(self.cpu.registers.with_ref(body));
        log::info!(target: "instr", "{:#06x} {} (${:02x}),Y", self.address, mnemonic, ial);
        self.cpu.end_cycle().await;

        // Cycle 5
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a read, modify, write instruction with zero page addressing.
    ///
    /// The total duration of instructions of this type is 5 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn rmw_zero_page(&self, mnemonic: &str, body: fn(&mut Registers, u8) -> u8) {
        // Cycle 1 - Fetch zero page effective address
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.bus.set_address(adl as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch data
        let data = self.cpu.bus.data();
        self.cpu.bus.set_address(adl as u16, BusDir::Write);
        self.cpu.end_cycle().await;

        // Cycle 3 - Modify and write data
        let modified_data = self.cpu.registers.with_mut_ref(|r| body(r, data));
        self.cpu.bus.set_address(adl as u16, BusDir::Write);
        self.cpu.bus.set_data(modified_data);
        log::info!(target: "instr", "{:#06x} {} ${:02x}", self.address, mnemonic, adl);
        self.cpu.end_cycle().await;

        // Cycle 4
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a read, modify, write instruction with zero page X addressing.
    ///
    /// The total duration of instructions of this type is 6 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn rmw_zero_page_x(&self, mnemonic: &str, body: fn(&mut Registers, u8) -> u8) {
        // Cycle 1 - Fetch zero page base address
        let bal = self.cpu.read_and_inc_pc();
        self.cpu.bus.set_address(bal as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 2 - Compute effective address
        let adl = bal.wrapping_add(self.reg_x()); // No carry
        self.cpu.bus.set_address(adl as u16, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Load data
        let data = self.cpu.bus.data();
        self.cpu.bus.set_address(adl as u16, BusDir::Write);
        self.cpu.end_cycle().await;

        // Cycle 4 - Modify data and write back
        let modified_data = self.cpu.registers.with_mut_ref(|r| body(r, data));
        self.cpu.bus.set_address(adl as u16, BusDir::Write);
        self.cpu.bus.set_data(modified_data);
        log::info!(target: "instr", "{:#06x} {} ${:02x},X", self.address, mnemonic, bal);
        self.cpu.end_cycle().await;

        // Cycle 5
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a read, modify, write instruction with absolute addressing.
    ///
    /// The total duration of instructions of this type is 6 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn rmw_absolute(&self, mnemonic: &str, body: fn(&mut Registers, u8) -> u8) {
        // Cycle 1 - Fetch low byte of effective address
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high byte of effective address
        let adh = self.cpu.read_and_inc_pc();
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Fetch data
        let data = self.cpu.bus.data();
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.end_cycle().await;

        // Cycle 4 - Modify and write data
        let modified_data = self.cpu.registers.with_mut_ref(|r| body(r, data));
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(modified_data);
        log::info!(target: "instr", "{:#06x} {} ${:04x}", self.address, mnemonic, effective_address);
        self.cpu.end_cycle().await;

        // Cycle 5
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
    }

    /// Executes a read, modify, write instruction with absolute X addressing.
    ///
    /// The total duration of instructions of this type is 7 cycles. It's implied that the first
    /// cycle for fetching the instruction opcode has already passed before this function is called.
    async fn rmw_absolute_x(&self, mnemonic: &str, body: fn(&mut Registers, u8) -> u8) {
        // Cycle 1 - Fetch low byte of effective address
        let adl = self.cpu.read_and_inc_pc();
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high byte of effective address
        let adh = self.cpu.read_and_inc_pc();
        let base_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(base_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 3 - Compute actual effective address
        let (adl, carry) = adl.overflowing_add(self.reg_x());
        let adh = adh.wrapping_add(if carry { 1 } else { 0 });
        let effective_address = u16::from_be_bytes([adh, adl]);
        self.cpu.bus.set_address(effective_address, BusDir::Read);
        self.cpu.end_cycle().await;

        // Cycle 4 - Fetch data
        let data = self.cpu.bus.data();
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.end_cycle().await;

        // Cycle 5 - Modify and write data
        let modified_data = self.cpu.registers.with_mut_ref(|r| body(r, data));
        self.cpu.bus.set_address(effective_address, BusDir::Write);
        self.cpu.bus.set_data(modified_data);
        log::info!(target: "instr", "{:#06x} {} ${:04x},X", self.address, mnemonic, base_address);
        self.cpu.end_cycle().await;

        // Cycle 6
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;
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

    fn new_ctx(&self, address: u16) -> ExecCtx<'_> {
        ExecCtx { address, cpu: self }
    }

    /// Signals the end of the CPU cycle.
    ///
    /// Along with calling [`core::wait_for_next_cycle`], this function performs additional logging
    /// of the bus and register state for debugging.
    async fn end_cycle(&self) {
        self.registers.with_ref(|r| {
            log::debug!(
                target: "cpu",
                "registers AC:{:02x} X:{:02x} Y:{:02x}",
                r.ac,
                r.x,
                r.y,
            );

            log::debug!(
                target: "cpu",
                "flags     N:{} Z:{} C:{} I:{} D:{} V:{}",
                r.sr.negative_flag() as i32,
                r.sr.zero_flag() as i32,
                r.sr.carry_flag() as i32,
                0, // TODO: implement getter
                0, // TODO: implement getter
                0, // TODO: implement getter
            );
        });
        log::debug!(target: "cpu", "end cycle");
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
    ///
    /// The address being read from is determine by whatever was on the address bus at the end of
    /// the previous cycle.
    fn read_and_inc_pc(&self) -> u8 {
        let data = self.bus.data();
        self.set_pc(|pc| pc.wrapping_add(1));
        data
    }

    /// Sets the program counter to the result of a given callback which receives the current
    /// program counter value as a parameter.
    fn set_pc(&self, f: impl FnOnce(u16) -> u16) {
        self.registers.with_mut_ref(|r| r.pc = f(r.pc));
    }

    /// Loads the program counter onto the address bus setting the bus direction to [`BusDir::Read`].
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
    /// Reference for cycle timings:
    /// https://web.archive.org/web/20120227142944if_/http://archive.6502.org:80/datasheets/synertek_hardware_manual.pdf
    async fn fetch_and_execute(&self) -> emu::Result<()> {
        let instruction_addr = self.registers.with_ref(|r| r.pc);
        let ctx = self.new_ctx(instruction_addr);

        // Cycle 0 - Fetch opcode off of the data bus.
        let opcode = self.bus.data();
        self.set_pc(|pc| pc.wrapping_add(1));
        self.load_pc_onto_bus();
        self.end_cycle().await;

        match opcode {
            // JAM
            0x02 => {
                log::warn!(target: "instr", "{instruction_addr:#06x} halt ({opcode:#04x})");
                return Err(EmulationError::Halt);
            }

            0x09 => {
                ctx.iem_immediate("ORA", |r, data| r.set_ac_with_flags(r.ac | data))
                    .await
            }

            0x06 => ctx.rmw_zero_page("ASL", asl).await,

            0x0a => ctx.single_cycle("ASL", |r| r.ac = asl(r, r.ac)).await,

            0x0e => ctx.rmw_absolute("ASL", asl).await,

            0x16 => ctx.rmw_zero_page_x("ASL", asl).await,

            0x1e => ctx.rmw_absolute_x("ASL", asl).await,

            0x26 => ctx.rmw_zero_page("ROL", rol).await,

            0x29 => {
                ctx.iem_immediate("AND", |r, data| r.set_ac_with_flags(r.ac & data))
                    .await
            }

            0x2a => ctx.single_cycle("ROL", |r| r.ac = rol(r, r.ac)).await,

            0x2e => ctx.rmw_absolute("ROL", rol).await,

            0x36 => ctx.rmw_zero_page_x("ROL", rol).await,

            0x3e => ctx.rmw_absolute_x("ROL", rol).await,

            0x46 => ctx.rmw_zero_page("LSR", lsr).await,

            0x4a => ctx.single_cycle("LSR", |r| r.ac = lsr(r, r.ac)).await,

            0x4e => ctx.rmw_absolute("LSR", lsr).await,

            0x56 => ctx.rmw_zero_page_x("LSR", lsr).await,

            0x5e => ctx.rmw_absolute_x("LSR", lsr).await,

            0x66 => ctx.rmw_zero_page("ROR", ror).await,

            0x6a => ctx.single_cycle("ROR", |r| r.ac = ror(r, r.ac)).await,

            0x6e => ctx.rmw_absolute("ROR", ror).await,

            0x76 => ctx.rmw_zero_page_x("ROR", ror).await,

            0x7e => ctx.rmw_absolute_x("ROR", ror).await,

            0x81 => ctx.store_indirect_x("STA", |r| r.ac).await,

            0x84 => ctx.store_zero_page("STY", |r| r.y).await,

            0x85 => ctx.store_zero_page("STA", |r| r.ac).await,

            0x86 => ctx.store_zero_page("STX", |r| r.x).await,

            0x8c => ctx.store_absolute("STY", |r| r.y).await,

            0x8d => ctx.store_absolute("STA", |r| r.ac).await,

            0x8e => ctx.store_absolute("STX", |r| r.x).await,

            0x91 => ctx.store_indirect_y("STA", |r| r.ac).await,

            0x94 => ctx.store_zero_page_x("STY", |r| r.y).await,

            0x95 => ctx.store_zero_page_x("STA", |r| r.ac).await,

            0x96 => ctx.store_zero_page_y("STX", |r| r.x).await,

            0x99 => ctx.store_absolute_y("STA", |r| r.ac).await,

            0x9d => ctx.store_absolute_x("STA", |r| r.ac).await,

            0xa0 => {
                ctx.iem_immediate("LDY", |r, data| r.set_y_with_flags(data))
                    .await
            }

            0xa1 => {
                ctx.iem_indirect_x("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xa2 => {
                ctx.iem_immediate("LDX", |r, data| r.set_x_with_flags(data))
                    .await
            }

            0xa4 => {
                ctx.iem_zero_page("LDY", |r, data| r.set_y_with_flags(data))
                    .await
            }

            0xa5 => {
                ctx.iem_zero_page("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xa6 => {
                ctx.iem_zero_page("LDX", |r, data| r.set_x_with_flags(data))
                    .await
            }

            0xa9 => {
                ctx.iem_immediate("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xac => {
                ctx.iem_absolute("LDY", |r, data| r.set_y_with_flags(data))
                    .await
            }

            0xad => {
                ctx.iem_absolute("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xae => {
                ctx.iem_absolute("LDX", |r, data| r.set_x_with_flags(data))
                    .await
            }

            0xb1 => {
                ctx.iem_indirect_y("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xb4 => {
                ctx.iem_zero_page_x("LDY", |r, data| r.set_y_with_flags(data))
                    .await
            }

            0xb5 => {
                ctx.iem_zero_page_x("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xb6 => {
                ctx.iem_zero_page_y("LDX", |r, data| r.set_x_with_flags(data))
                    .await
            }

            0xb9 => {
                ctx.iem_absolute_y("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xbc => {
                ctx.iem_absolute_x("LDY", |r, data| r.set_y_with_flags(data))
                    .await
            }

            0xbd => {
                ctx.iem_absolute_x("LDA", |r, data| r.set_ac_with_flags(data))
                    .await
            }

            0xbe => {
                ctx.iem_absolute_y("LDX", |r, data| r.set_x_with_flags(data))
                    .await
            }

            0xc6 => ctx.rmw_zero_page("DEC", dec).await,

            0xce => ctx.rmw_absolute("DEC", dec).await,

            0xd6 => ctx.rmw_zero_page_x("DEC", dec).await,

            0xde => ctx.rmw_absolute_x("DEC", dec).await,

            // NOP
            0xea => {
                // Cycle 1 - Do nothing.
                self.end_cycle().await;

                // Log after as this instruction should take 2 cycles.
                log::info!(target: "instr", "{} NOP", instruction_addr);
            }

            0xe6 => ctx.rmw_zero_page("INC", inc).await,

            0xee => ctx.rmw_absolute("INC", inc).await,

            0xf6 => ctx.rmw_zero_page_x("INC", inc).await,

            0xfe => ctx.rmw_absolute_x("INC", inc).await,

            _ => {
                log::error!(
                    target: "instr",
                    "{:#06x} invalid instruction - opcode = {:02x}",
                    instruction_addr,
                    opcode
                );

                return Err(EmulationError::InvalidInstruction {
                    opcode,
                    address: instruction_addr,
                });
            }
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

/// Implements the arithmatic left shift (ASL) operation.
///
/// The carry, zero, and negative flags are set in the provided [`Registers`] reference based on
/// the result of this operation.
fn asl(r: &mut Registers, data: u8) -> u8 {
    let result = data.wrapping_shl(1);
    r.sr.set_carry_flag(data & 0x80 != 0);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(result & 0x80 != 0);
    log::debug!(target: "instr", "ASL {:02x} -> {:02x}", data, result);
    result
}

/// Implements the logical right shift (LSR) operation.
///
/// The carry, zero, and negative flags are set in the provided [`Registers`] reference based on
/// the result of this operation.
fn lsr(r: &mut Registers, data: u8) -> u8 {
    let result = data.wrapping_shr(1);
    r.sr.set_carry_flag(data & 0x01 != 0);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(false);
    log::debug!(target: "instr", "LSR {:02x} -> {:02x}", data, result);
    result
}

/// Implements the decrement (DEC) operation.
///
/// The zero and negative flags are set in the provided [`Registers`] reference based on the result
/// of this operation.
fn dec(r: &mut Registers, data: u8) -> u8 {
    let result = data.wrapping_sub(1);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(result & 0x80 != 0);
    log::debug!(target: "instr", "DEC {:02x} -> {:02x}", data, result);
    result
}

/// Implements the increment (INC) operation.
///
/// The zero and negative flags are set in the provided [`Registers`] reference based on the result
/// of this operation.
fn inc(r: &mut Registers, data: u8) -> u8 {
    let result = data.wrapping_add(1);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(result & 0x80 != 0);
    log::debug!(target: "instr", "DEC {:02x} -> {:02x}", data, result);
    result
}

/// Implements the rotate left (ROL) operation.
///
/// The carry, zero, and negative flags are set in the provided [`Registers`] reference based on
/// the result of this operation.
fn rol(r: &mut Registers, data: u8) -> u8 {
    let result = data.rotate_left(1);
    r.sr.set_carry_flag(data & 0x80 != 0);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(result & 0x80 != 0);
    log::debug!(target: "instr", "ROL {:02x} -> {:02x}", data, result);
    result
}

/// Implements the rotate right (ROR) operation.
///
/// The carry, zero, and negative flags are set in the provided [`Registers`] reference based on
/// the result of this operation.
fn ror(r: &mut Registers, data: u8) -> u8 {
    let result = data.rotate_right(1);
    r.sr.set_carry_flag(data & 0x01 != 0);
    r.sr.set_zero_flag(result == 0);
    r.sr.set_negative_flag(result & 0x80 != 0);
    log::debug!(target: "instr", "ROL {:02x} -> {:02x}", data, result);
    result
}
