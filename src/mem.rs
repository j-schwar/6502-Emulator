//! Memory components.

use super::core::{self, BusDir, BusPtr, EmulationComponent};

pub struct Rom {
    bus: BusPtr,
    start_addr: usize,
    memory: Box<[u8]>,
}

impl Rom {
    pub fn from_data(bus: BusPtr, start_addr: u16, data: impl Into<Box<[u8]>>) -> Self {
        Self {
            bus,
            start_addr: start_addr as usize,
            memory: data.into(),
        }
    }
}

impl Rom {
    fn cycle(&mut self) {
        let mut bus = self.bus.borrow_mut();

        if bus.dir == BusDir::Read {
            let addr = bus.address.raw() as usize;
            if addr >= self.start_addr && addr < (self.start_addr + self.memory.len()) {
                let index = (addr - self.start_addr) as usize;
                let value = self.memory[index];
                bus.data = value;
            }
        }
    }
}

impl EmulationComponent for Rom {
    async fn run(&mut self) {
        loop {
            self.cycle();
            core::wait_for_next_cycle().await;
        }
    }
}

#[cfg(test)]
mod test {
    use super::{core::*, *};

    #[test]
    fn rom_sets_data_bus() {
        let bus = BusPtr::default();
        let mut rom = Rom::from_data(bus.clone(), 0, vec![0, 1, 2, 3]);

        let mut executor = Executor::default();
        executor.push_component_ref(&mut rom);

        bus.borrow_mut().address = Ptr::from(0x0001);
        executor.poll_once();
        assert_eq!(1, bus.borrow().data);

        bus.borrow_mut().address = Ptr::from(0x0002);
        executor.poll_once();
        assert_eq!(2, bus.borrow().data);

        bus.borrow_mut().address = Ptr::from(0x0003);
        executor.poll_once();
        assert_eq!(3, bus.borrow().data);
    }
}
