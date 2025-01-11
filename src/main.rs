use cpu::Cpu;
use emu::{Executor, SharedBus};
use mem::{Memory, ResetVector};
use with_ref::WithRef;

mod cpu;
mod emu;
mod mem;

#[cfg(test)]
mod cpu_tests;

fn main() -> emu::Result<()> {
    env_logger::init();

    let bus = SharedBus::default();
    let cpu = Cpu::new(bus.clone());
    let res = ResetVector::new(bus.clone(), 0xf000);
    let ram = Memory::from_zeroed(bus.clone(), 0x0000, 0x1fff);
    let rom = Memory::from_readonly_data(
        bus.clone(),
        0xf000,
        [
            0x09, 0x01, // ORA #01
            0xea, // NOP
            0xea, // NOP
            0x09, 0x02, // ORA #02
            0x02, // Halt
        ],
    );

    let mut executor = Executor::default();
    executor.add_task(cpu.run());
    executor.add_task(ram.run());
    executor.add_task(rom.run());
    executor.add_task(res.run());
    executor.poll_until_halt()?;

    println!("accumulator = {:02x}", cpu.registers.with_ref(|r| r.ac));
    Ok(())
}
