//! 6502 CPU Emulator

#![expect(unused)] // FIXME: Remove after all instructions have been implemented

use std::{fmt::Display, rc::Rc, sync::Mutex};

use super::core::{Bus, SharedBus, EmulationError, Ptr};

/// Operand types for [`Instruction`].
#[derive(Clone, Copy, Debug)]
pub enum Operand {
    Accumulator,
    Immediate(u8),
    Absolute(Ptr),
    AbsoluteX(Ptr),
    AbsoluteY(Ptr),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
    Indirect(Ptr),
    PreIndexedIndirect(u8),
    PostIndexedIndirect(u8),
    Relative(i8),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Operand::*;

        match &self {
            Accumulator => write!(f, "A"),
            Immediate(operand) => write!(f, "#{:02X}", operand),
            Absolute(operand) => write!(f, "${}", operand),
            AbsoluteX(operand) => write!(f, "${},X", operand),
            AbsoluteY(operand) => write!(f, "${},Y", operand),
            ZeroPage(operand) => write!(f, "${:02X}", operand),
            ZeroPageX(operand) => write!(f, "${:02X},X", operand),
            ZeroPageY(operand) => write!(f, "${:02X},Y", operand),
            Indirect(operand) => write!(f, "(${})", operand),
            PreIndexedIndirect(operand) => write!(f, "(${:02X},X)", operand),
            PostIndexedIndirect(operand) => write!(f, "(${:02X}),Y", operand),
            Relative(operand) => write!(f, "rel({:02X})", operand),
        }
    }
}

/// 6502 Instructions
#[derive(Clone, Copy, Debug)]
pub enum Instruction {
    /// Add memory to accumulator with carry.
    ADC(Operand),
    /// And memory with accumulator.
    AND(Operand),
    /// Shift left one bit.
    ASL(Operand),
    /// Branch on carry clear.
    BCC(Operand),
    /// Branch on carry set.
    BCS(Operand),
    /// Branch on result zero.
    BEQ(Operand),
    /// Test bits in memory with accumulator.
    BIT(Operand),
    /// Branch on result minus.
    BMI(Operand),
    /// Branch on result not zero.
    BNE(Operand),
    /// Branch on result plus.
    BPL(Operand),
    /// Force break.
    BRK,
    /// Branch on overflow clear.
    BVC(Operand),
    /// Branch on overflow set.
    BVS(Operand),
    /// Clear carry flag.
    CLS,
    /// Clear decimal mode.
    CLD,
    /// Clear interrupt disable bit.
    CLI,
    /// Clear overflow flag.
    CLV,
    /// Compare memory with accumulator.
    CMP(Operand),
    /// Compare memory and index X.
    CPX(Operand),
    /// Compare memory and index Y.
    CPY(Operand),
    /// Decrement memory by one.
    DEC(Operand),
    /// Decrement X by one.
    DEX,
    /// Decrement Y by one.
    DEY,
    /// XOR memory with accumulator.
    EOR(Operand),
    /// Increment memory by one.
    INC(Operand),
    /// Increment X by one.
    INX,
    /// Increment Y by one.
    INY,
    /// Jump to new location.
    JMP(Operand),
    /// Load accumulator with memory.
    LDA(Operand),
    /// Load index X with memory.
    LDX(Operand),
    /// Load index Y with memory.
    LDY(Operand),
    /// Shift one bit right.
    LSR(Operand),
    /// No operation.
    NOP,
    /// OR memory with accumulator.
    ORA(Operand),
    /// Push accumulator onto stack.
    PHA,
    /// Push processor status onto stack.
    PHP,
    /// Pull accumulator from stack.
    PLA,
    /// Pull processor status from stack.
    PLP,
    /// Rotate one bit left.
    ROL(Operand),
    /// Return from interrupt.
    RTI,
    /// Return from subroutine.
    RTS,
    /// Subtract memory from accumulator with borrow.
    SBC(Operand),
    /// Set carry flag.
    SEC,
    /// Set decimal flag.
    SED,
    /// Set interrupt disable status.
    SEI,
    /// Store accumulator in memory.
    STA(Operand),
    /// Store index X in memory.
    STX(Operand),
    /// Store index Y in memory.
    STY(Operand),
    /// Transfer accumulator to index X.
    TAX,
    /// Transfer accumulator to index Y.
    TAY,
    /// Transfer stack pointer to index X,
    TSX,
    /// Transfer index X to accumulator.
    TXA,
    /// Transfer index X to stack register.
    TXS,
    /// Transfer index Y to accumulator.
    TYA,
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instruction::*;

        match &self {
            ADC(operand) => write!(f, "ADC {}", operand),
            AND(operand) => write!(f, "AND {operand}"),
            ASL(operand) => write!(f, "ASL {operand}"),
            BCC(operand) => write!(f, "BCC {operand}"),
            BCS(operand) => write!(f, "BCS {operand}"),
            BEQ(operand) => write!(f, "BEQ {operand}"),
            BIT(operand) => write!(f, "BIT {operand}"),
            BMI(operand) => write!(f, "BMI {operand}"),
            BNE(operand) => write!(f, "BNE {operand}"),
            BPL(operand) => write!(f, "BPL {operand}"),
            BRK => write!(f, "BRK"),
            BVC(operand) => write!(f, "BVC {operand}"),
            BVS(operand) => write!(f, "BVS {operand}"),
            CLS => write!(f, "CLS"),
            CLD => write!(f, "CLD"),
            CLI => write!(f, "CLI"),
            CLV => write!(f, "CLV"),
            CMP(operand) => write!(f, "CMP {operand}"),
            CPX(operand) => write!(f, "CPX {operand}"),
            CPY(operand) => write!(f, "CPY {operand}"),
            DEC(operand) => write!(f, "DEC {operand}"),
            DEX => write!(f, "DEX"),
            DEY => write!(f, "DEY"),
            EOR(operand) => write!(f, "EOR {operand}"),
            INC(operand) => write!(f, "INC {operand}"),
            INX => write!(f, "INX"),
            INY => write!(f, "INY"),
            JMP(operand) => write!(f, "JMP {operand}"),
            LDA(operand) => write!(f, "LDA {operand}"),
            LDX(operand) => write!(f, "LDX {operand}"),
            LDY(operand) => write!(f, "LDY {operand}"),
            LSR(operand) => write!(f, "LSR {operand}"),
            NOP => write!(f, "NOP"),
            ORA(operand) => write!(f, "ORA {operand}"),
            PHA => write!(f, "PHA"),
            PHP => write!(f, "PHP"),
            PLA => write!(f, "PLA"),
            PLP => write!(f, "PLP"),
            ROL(operand) => write!(f, "ROL {operand}"),
            RTI => write!(f, "RTI"),
            RTS => write!(f, "RTS"),
            SBC(operand) => write!(f, "SBC {operand}"),
            SEC => write!(f, "SEC"),
            SED => write!(f, "SED"),
            SEI => write!(f, "SEI"),
            STA(operand) => write!(f, "STA {operand}"),
            STX(operand) => write!(f, "STX {operand}"),
            STY(operand) => write!(f, "STY {operand}"),
            TAX => write!(f, "TAX"),
            TAY => write!(f, "TAY"),
            TSX => write!(f, "TSX"),
            TXA => write!(f, "TXA"),
            TXS => write!(f, "TXS"),
            TYA => write!(f, "TYA"),
        }
    }
}

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
}
