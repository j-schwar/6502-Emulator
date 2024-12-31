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
    fn set_negative_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x80, value);
    }

    /// Sets the overflow (V) flag in the status register.
    #[expect(unused)]
    fn set_overflow_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x40, value);
    }

    /// Sets the break flag (B) in the status register.
    #[expect(unused)]
    fn set_break_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x10, value);
    }

    /// Sets the decimal flag (D) in the status register.
    #[expect(unused)]
    fn set_decimal_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x08, value);
    }

    /// Sets the interrupt disable flag (I) in the status register.
    #[expect(unused)]
    fn set_interrupt_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x04, value);
    }

    /// Sets the zero flag (Z) in the status register.
    fn set_zero_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x02, value);
    }

    /// Sets the carry flag (C) in the status register.
    fn set_carry_flag(&mut self, value: bool) {
        set_bit!(self.0, 0x01, value);
    }

    /// Gets the carry flag (C) in the status register.
    fn carry_flag(&self) -> bool {
        get_bit!(self.0, 0x01)
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
        let adl = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));

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
        let bal = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let adl = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order effective address byte.
        let adh = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let adl = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order effective address byte.
        let adh = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let bal = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let ial = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let adl = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
        self.cpu.load_pc_onto_bus();
        self.cpu.end_cycle().await;

        // Cycle 2 - Fetch high order by of address
        let adh = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
        let adl = self.cpu.bus.data();
        self.cpu.set_pc(|pc| pc.wrapping_add(1));
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
            0x02 => return Err(EmulationError::Halt),

            0x09 => {
                ctx.iem_immediate("ORA", |r, data| r.set_ac_with_flags(r.ac | data))
                    .await
            }

            0x0a => {
                ctx.single_cycle("ASL", |r| {
                    let carry = r.ac & 0x80 != 0;
                    let value = r.ac.wrapping_shl(1);
                    log::warn!("value = {:02x}, carry = {}", value, carry);
                    r.set_ac_with_flags(value);
                    r.sr.set_carry_flag(carry);
                })
                .await
            }

            0x29 => {
                ctx.iem_immediate("AND", |r, data| r.set_ac_with_flags(r.ac & data))
                    .await
            }

            0x84 => ctx.store_zero_page("STY", |r| r.y).await,

            0x85 => ctx.store_zero_page("STA", |r| r.ac).await,

            0x86 => ctx.store_zero_page("STX", |r| r.x).await,

            0x8c => ctx.store_absolute("STY", |r| r.y).await,

            0x8d => ctx.store_absolute("STA", |r| r.ac).await,

            0x8e => ctx.store_absolute("STX", |r| r.x).await,

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

            // 0xb4 => zero_page_offset_instr!("LDY ${:02},X", x, |r, data| r.set_y_with_flags(data)),
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

            // NOP
            0xea => {
                // Cycle 1 - Do nothing.
                self.end_cycle().await;

                // Log after as this instruction should take 2 cycles.
                log::info!(target: "instr", "{} NOP", instruction_addr);
            }

            _ => {
                log::error!(target: "instr", "invalid instruction - opcode = {:02x}", opcode);
                return Err(EmulationError::InvalidInstruction);
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::emu::Executor;
    use crate::mem::{Memory, ResetVector};

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    /// Executes given machine code until the CPU halts, where it then returns the state of the CPU
    /// registers.
    fn exec(machine_code: impl AsRef<[u8]>) -> emu::Result<Registers> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let rom = Memory::from_readonly_data(bus.clone(), 0xf000, machine_code.as_ref());
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
        let zero_page = Memory::from_readonly_data(bus.clone(), 0x0000, zero_page.as_ref());
        let mem = Memory::from_readonly_data(bus.clone(), start_addr, mem.as_ref());
        let rom = Memory::from_readonly_data(bus.clone(), 0xf000, machine_code.as_ref());
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
        let mem = Memory::from_readonly_data(bus.clone(), start_addr, mem.as_ref());
        let rom = Memory::from_readonly_data(bus.clone(), 0xf000, machine_code.as_ref());
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

    fn exec_with_memory(machine_code: impl AsRef<[u8]>) -> emu::Result<(Registers, Box<[u8]>)> {
        let bus = SharedBus::default();
        let cpu = Cpu::new(bus.clone());
        let mem = Memory::from_zeroed(bus.clone(), 0x0000, 0xf000);
        let rom = Memory::from_readonly_data(bus.clone(), 0xf000, machine_code.as_ref());
        let res = ResetVector::new(bus.clone(), 0xf000);

        {
            let mut executor = Executor::default();
            executor.add_task(cpu.run());
            executor.add_task(mem.run());
            executor.add_task(rom.run());
            executor.add_task(res.run());
            executor.poll_until_halt()?;
        }

        Ok((cpu.registers.with_ref(|r| *r), mem.into_data()))
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

    #[test]
    fn asl_accumulator() -> emu::Result<()> {
        init();
        let r = exec([
            0xa9, 0x81, // LDA #$81,
            0x0a, // ASL,
            0x02, // Halt
        ])?;
        assert_eq!(0x02, r.ac);
        assert!(r.sr.carry_flag());
        Ok(())
    }

    #[test]
    fn store_zero_page() -> emu::Result<()> {
        init();
        let (_, m) = exec_with_memory([
            0xa0, 0x01, // LDY #$01
            0xa2, 0x02, // LDX #$02
            0xa9, 0x03, // LDA #$03
            0x84, 0x01, // STY $01
            0x86, 0x02, // STX $02
            0x85, 0x03, // STA $03
            0x02, // Halt
        ])?;

        assert_eq!(0x01, m[1]);
        assert_eq!(0x02, m[2]);
        assert_eq!(0x03, m[3]);
        Ok(())
    }

    #[test]
    fn store_zero_page_offset() -> emu::Result<()> {
        init();
        let (_, m) = exec_with_memory([
            0xa0, 0x01, // LDY #$01
            0xa2, 0x02, // LDX #$02
            0xa9, 0x03, // LDA #$03
            0x94, 0x00, // STY $00,X ; store 1 -> $02
            0x95, 0x01, // STA $01,X ; store 3 -> $03
            0x96, 0x00, // STX $00,Y ; store 2 -> $01
            0x02, // Halt
        ])?;

        assert_eq!(0x01, m[2]);
        assert_eq!(0x03, m[3]);
        assert_eq!(0x02, m[1]);
        Ok(())
    }

    #[test]
    fn store_absolute() -> emu::Result<()> {
        init();
        let (_, m) = exec_with_memory([
            0xa0, 0x01, // LDY #$01
            0xa9, 0x02, // LDA #$02
            0xa2, 0x03, // LDX #$03
            0x8c, 0x01, 0x10, // STY $1001
            0x8d, 0x02, 0x10, // STA $1002
            0x8e, 0x03, 0x10, // STX $1003
            0x02, // Halt
        ])?;

        assert_eq!(0x01, m[0x1001]);
        assert_eq!(0x02, m[0x1002]);
        assert_eq!(0x03, m[0x1003]);
        Ok(())
    }

    #[test]
    fn store_absolute_offset() -> emu::Result<()> {
        init();
        let (_, m) = exec_with_memory([
            0xa9, 0xaa, // LDA #$aa
            0xa0, 0x01, // LDY #$01
            0xa2, 0x02, // LDX #$02
            0x99, 0x00, 0x10, // STA $1000,Y
            0x9d, 0x00, 0x10, // STA $1000,X
            0x02, // Halt
        ])?;

        assert_eq!(0xaa, m[0x1001]);
        assert_eq!(0xaa, m[0x1002]);
        Ok(())
    }
}
