use with_ref::WithRef;

use crate::cpu::*;
use crate::emu::{self, EmulationError, Executor};
use crate::mem::{Memory, ResetVector};
use crate::SharedBus;

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

    let result = {
        let mut executor = Executor::default();
        executor.add_task(cpu.run());
        executor.add_task(mem.run());
        executor.add_task(rom.run());
        executor.add_task(res.run());
        executor.poll_until_halt()
    };

    match result {
        Ok(_) => Ok((cpu.registers.with_ref(|r| *r), mem.into_data())),

        Err(EmulationError::InvalidInstruction { opcode, address }) => {
            let mut buf = Vec::new();
            rom.dump_around(&mut buf, address).unwrap();
            let s = String::from_utf8_lossy(buf.as_slice());
            for line in s.lines() {
                log::error!(target: "dump", "{line}");
            }
            Err(EmulationError::InvalidInstruction { opcode, address })
        }

        Err(err) => Err(err),
    }
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

#[test]
fn store_indirect_x() -> emu::Result<()> {
    init();

    // Store #$aa at $1000, $1000 is read from the zero page at $01 and $02.
    let (_, m) = exec_with_memory([
        0xa9, 0x00, // LDA #$00
        0x85, 0x01, // STA $01
        0xa9, 0x10, // LDA #$10
        0x85, 0x02, // STA $02
        0xa2, 0x01, // LDX #$01
        0xa9, 0xaa, // LDA #$aa
        0x81, 0x00, // STA ($00,X)
        0x02, // Halt
    ])?;

    assert_eq!(0xaa, m[0x1000]);
    Ok(())
}

#[test]
fn store_indirect_y() -> emu::Result<()> {
    init();

    // Store #$aa at $1001, $1000 is read from the zero page at $00 and $01.
    let (_, m) = exec_with_memory([
        0xa9, 0x00, // LDA #$00
        0x85, 0x00, // STA $01
        0xa9, 0x10, // LDA #$10
        0x85, 0x01, // STA $02
        0xa0, 0x01, // LDY #$01
        0xa9, 0xaa, // LDA #$aa
        0x91, 0x00, // STA ($00),Y
        0x02, // Halt
    ])?;

    assert_eq!(0xaa, m[0x1001]);
    Ok(())
}

#[derive(Clone, Copy, Default)]
struct Opcodes {
    _implicit: Option<u8>,
    accumulator: Option<u8>,
    zero_page: Option<u8>,
    zero_page_x: Option<u8>,
    _zero_page_y: Option<u8>,
    absolute: Option<u8>,
    absolute_x: Option<u8>,
    _absolute_y: Option<u8>,
    _indirect_x: Option<u8>,
    _indirect_y: Option<u8>,
}

/// Tests a read, modify, write instruction through all possible addressing modes.
fn test_rmw(
    opcodes: Opcodes,
    initial: u8,
    expected: u8,
    expect_carry: Option<bool>,
) -> emu::Result<()> {
    let assert_flags = |r: &Registers| {
        if let Some(expect_carry) = expect_carry {
            assert_eq!(expect_carry, r.sr.carry_flag(), "carry flag");
        }

        assert_eq!(expected == 0, r.sr.zero_flag(), "zero flag");
        assert_eq!(expected & 0x80 != 0, r.sr.negative_flag(), "negative flag");
    };

    init();

    // Accumulator
    log::info!(target: "test", "starting rmw accumulator");
    if let Some(opcode) = opcodes.accumulator {
        let (r, _) = exec_with_memory([0xa9, initial, opcode, 0x02])?;
        assert_eq!(expected, r.ac);
        assert_flags(&r);
    }

    // Zero Page
    log::info!(target: "test", "starting rmw zero page");
    if let Some(opcode) = opcodes.zero_page {
        let (r, m) = exec_with_memory([
            0xa9, initial, // LDA <initial>
            0x85, 0x00, // STA $00
            opcode, 0x00, // <opcode> $00
            0x02, // Halt
        ])?;
        assert_eq!(expected, m[0x00]);
        assert_flags(&r);
    }

    // Zero Page X
    log::info!(target: "test", "starting rmw zero page x");
    if let Some(opcode) = opcodes.zero_page_x {
        let (r, m) = exec_with_memory([
            0xa9, initial, // LDA <initial>
            0x85, 0x01, // STA $01
            0xa2, 0x01, // LDX #$01
            opcode, 0x00, // <opcode> $00,X
            0x02, // Halt
        ])?;
        assert_eq!(expected, m[0x01]);
        assert_flags(&r);
    }

    // Absolute
    log::info!(target: "test", "starting rmw absolute");
    if let Some(opcode) = opcodes.absolute {
        let (r, m) = exec_with_memory([
            0xa9, initial, // LDA <initial>
            0x8d, 0x00, 0x10, // STA $1000
            opcode, 0x00, 0x10, // <opcode> $1000
            0x02, // Halt
        ])?;
        assert_eq!(expected, m[0x1000]);
        assert_flags(&r);
    }

    // Absolute X
    log::info!(target: "test", "starting rmw absolute x");
    if let Some(opcode) = opcodes.absolute_x {
        let (r, m) = exec_with_memory([
            0xa9, initial, // LDA <initial>
            0xa2, 0x01, // LDX #$01
            0x8d, 0x01, 0x10, // STA $1001
            opcode, 0x00, 0x10, // <opcode> $1000,X
            0x02, // Halt
        ])?;
        assert_eq!(expected, m[0x1001]);
        assert_flags(&r);
    }

    Ok(())
}

#[test]
fn asl() -> emu::Result<()> {
    let opcodes = Opcodes {
        accumulator: Some(0x0a),
        zero_page: Some(0x06),
        zero_page_x: Some(0x16),
        absolute: Some(0x0e),
        absolute_x: Some(0x1e),
        ..Default::default()
    };

    test_rmw(opcodes, 0x81, 0x02, Some(true))?;
    test_rmw(opcodes, 0x80, 0x00, Some(true))?;
    test_rmw(opcodes, 0x7f, 0xfe, Some(false))?;
    Ok(())
}

#[test]
fn lsr() -> emu::Result<()> {
    let opcodes = Opcodes {
        accumulator: Some(0x4a),
        zero_page: Some(0x46),
        zero_page_x: Some(0x56),
        absolute: Some(0x4e),
        absolute_x: Some(0x5e),
        ..Default::default()
    };

    test_rmw(opcodes, 0x81, 0x40, Some(true))?;
    test_rmw(opcodes, 0x80, 0x40, Some(false))?;
    test_rmw(opcodes, 0x7f, 0x3f, Some(true))?;
    Ok(())
}

#[test]
fn dec() -> emu::Result<()> {
    let opcodes = Opcodes {
        zero_page: Some(0xc6),
        zero_page_x: Some(0xd6),
        absolute: Some(0xce),
        absolute_x: Some(0xde),
        ..Default::default()
    };

    test_rmw(opcodes, 0x00, 0xff, None)?;
    test_rmw(opcodes, 0x01, 0x00, None)?;
    test_rmw(opcodes, 0x80, 0x7f, None)?;
    Ok(())
}

#[test]
fn inc() -> emu::Result<()> {
    let opcodes = Opcodes {
        zero_page: Some(0xe6),
        zero_page_x: Some(0xf6),
        absolute: Some(0xee),
        absolute_x: Some(0xfe),
        ..Default::default()
    };

    test_rmw(opcodes, 0x00, 0x01, None)?;
    test_rmw(opcodes, 0xff, 0x00, None)?;
    test_rmw(opcodes, 0x7f, 0x80, None)?;
    Ok(())
}

#[test]
fn rol() -> emu::Result<()> {
    let opcodes = Opcodes {
        accumulator: Some(0x2a),
        zero_page: Some(0x26),
        zero_page_x: Some(0x36),
        absolute: Some(0x2e),
        absolute_x: Some(0x3e),
        ..Default::default()
    };

    test_rmw(opcodes, 0x00, 0x00, Some(false))?;
    test_rmw(opcodes, 0x01, 0x02, Some(false))?;
    test_rmw(opcodes, 0x80, 0x01, Some(true))?;
    Ok(())
}

#[test]
fn ror() -> emu::Result<()> {
    let opcodes = Opcodes {
        accumulator: Some(0x6a),
        zero_page: Some(0x66),
        zero_page_x: Some(0x76),
        absolute: Some(0x6e),
        absolute_x: Some(0x7e),
        ..Default::default()
    };

    test_rmw(opcodes, 0x00, 0x00, Some(false))?;
    test_rmw(opcodes, 0x01, 0x80, Some(true))?;
    test_rmw(opcodes, 0x80, 0x40, Some(false))?;
    Ok(())
}
