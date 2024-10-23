//! Core emulation components.

use std::{
    cell::RefCell,
    fmt::Display,
    future::Future,
    pin::Pin,
    rc::Rc,
    str::FromStr,
    task::{Context, Poll},
};

use noop_waker::noop_waker;

/// Errors return by emulation operations.
#[derive(Debug)]
pub enum EmulationError {
    InvalidPtr,
    InvalidInstruction,
    Decode,
}

impl Display for EmulationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmulationError::InvalidPtr => write!(f, "invalid pointer"),
            EmulationError::InvalidInstruction => write!(f, "invalid instruction"),
            EmulationError::Decode => write!(f, "decode error"),
        }
    }
}

impl std::error::Error for EmulationError {}

/// A 16-bit pointer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ptr(u16);

impl Ptr {
    /// The `NULL` pointer.
    pub const ZERO: Ptr = Ptr(0x0000);

    /// Pointer to the non-maskable interrupt vector.
    ///
    /// The interrupt request vector is a 16-bit word which holds the location that execution
    /// should jump to when a non-maskable interrupt is received.
    pub const NMI: Ptr = Ptr(0xFFFA);

    /// Pointer to the reset vector.
    ///
    /// The reset vector is a 16-bit word which holds the location that execution should begin at
    /// when the CPU is reset.
    pub const RES: Ptr = Ptr(0xFFFC);

    /// Pointer to the interrupt request vector.
    ///
    /// The interrupt request vector is a 16-bit word which holds the location that execution
    /// should jump to when an interrupt is received.
    pub const IRQ: Ptr = Ptr(0xFFFE);

    /// Gets the raw value of this pointer.
    #[inline(always)]
    pub fn raw(self) -> u16 {
        self.0
    }
}

impl From<u16> for Ptr {
    #[inline(always)]
    fn from(value: u16) -> Self {
        Ptr(value)
    }
}

impl From<Ptr> for u16 {
    #[inline(always)]
    fn from(value: Ptr) -> Self {
        value.0
    }
}

impl FromStr for Ptr {
    type Err = EmulationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() > 4 || !s.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(EmulationError::InvalidPtr);
        }

        let addr = u16::from_str_radix(s, 16).unwrap();
        Ok(Ptr(addr))
    }
}

impl Display for Ptr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:04x}", self.0)
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum BusDir {
    #[default]
    Read,
    Write,
}

#[derive(Default, Clone)]
pub struct Bus {
    pub data: u8,
    pub address: Ptr,
    pub dir: BusDir,
}

/// A shared pointer to a [`Bus`] instance.
///
/// This type contains convenience methods for interacting with specific parts of the bus.
#[derive(Default, Clone)]
pub struct SharedBus(Rc<RefCell<Bus>>);

impl SharedBus {
    /// Executes a closure while holding a reference to the shared bus.
    pub fn with_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Bus) -> T,
    {
        f(&self.0.borrow())
    }

    /// Executes a closure while holding a mutable reference to the shared bus.
    pub fn with_mut_ref<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Bus) -> T,
    {
        f(&mut self.0.as_ref().borrow_mut())
    }

    /// Returns the value of the address bus.
    pub fn address(&self) -> Ptr {
        self.with_ref(|bus| bus.address)
    }

    /// Sets the value on the address bus.
    pub fn set_address(&mut self, ptr: Ptr) {
        self.with_mut_ref(|bus| bus.address = ptr)
    }

    /// Returns the value on the data bus.
    pub fn data(&self) -> u8 {
        self.with_ref(|bus| bus.data)
    }

    /// Sets the value on the data bus.
    pub fn set_data(&mut self, value: u8) {
        self.with_mut_ref(|bus| bus.data = value)
    }
}

/// Trait for emulation components.
pub trait EmulationComponent {
    async fn run(&mut self);
}

#[derive(Default)]
pub struct Executor<'a> {
    queue: Vec<Pin<Box<dyn Future<Output = ()> + 'a>>>,
}

impl<'a> Executor<'a> {
    /// Adds a reference to an [`EmulationComponent`] to this executor. Components are polled in the
    /// order they're added.
    pub fn push_component_ref<C>(&mut self, c: &'a mut C)
    where
        C: EmulationComponent,
    {
        self.queue.push(Box::pin(c.run()));
    }

    /// Polls all components in this executor once.
    pub fn poll_once(&mut self) {
        for future in self.queue.as_mut_slice() {
            let waker = noop_waker();
            let mut cx = Context::from_waker(&waker);
            let _ = future.as_mut().poll(&mut cx);
        }
    }
}

struct CycleFuture {
    remaining_cycles: u32,
}

impl CycleFuture {
    fn idle_cycles(n: u32) -> Self {
        Self {
            remaining_cycles: n,
        }
    }
}

impl Future for CycleFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.remaining_cycles == 0 {
            return Poll::Ready(());
        }

        self.remaining_cycles -= 1;
        Poll::Pending
    }
}

/// Returns a future that waits for `n` clock cycles to pass before completing.
///
/// Within the context of [`Executor`], polling this future is equivalent to a clock cycle passing.
pub fn idle_cycles(n: u32) -> impl Future<Output = ()> {
    CycleFuture::idle_cycles(n)
}

/// Returns a future that waits until the next clock cycle before returning.
///
/// Within the context of [`Executor`], polling this future is equivalent to a clock cycle passing.
pub fn wait_for_next_cycle() -> impl Future<Output = ()> {
    idle_cycles(1)
}
