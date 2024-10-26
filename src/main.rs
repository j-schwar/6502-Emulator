use crate::emu::{Executor, SharedBus};
use crate::mem::Rom;

mod cpu;
mod emu;
mod mem;

fn main() {
    env_logger::init();

    let bus = SharedBus::default();
    let mut rom = Rom::from_data(bus.clone(), 0, vec![0, 1, 2, 3]);

    let mut executor = Executor::default();
    executor.add_task(rom.run());
}
