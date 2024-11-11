use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

use crate::emu;

use super::EmulationError;

struct CycleFuture {
    remaining_cycles: u32,
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
    CycleFuture {
        remaining_cycles: n,
    }
}

/// Returns a future that waits until the next clock cycle before returning.
///
/// Within the context of [`Executor`], polling this future is equivalent to a clock cycle passing.
pub fn wait_for_next_cycle() -> impl Future<Output = ()> {
    idle_cycles(1)
}

#[derive(Default)]
pub struct Executor<'a> {
    futures: Vec<Pin<Box<dyn Future<Output = emu::Result<()>> + 'a>>>,
}

impl<'a> Executor<'a> {
    /// Adds a future (usually the result of a call to [`EmulationComponent::run`]) to this
    /// executor. Futures are polled in the order their added.
    pub fn add_task<F>(&mut self, f: F)
    where
        F: Future<Output = emu::Result<()>> + 'a,
    {
        self.futures.push(Box::pin(f));
    }

    /// Polls all futures in this executor once.
    pub fn poll(&mut self) -> emu::Result<()> {
        for future in self.futures.as_mut_slice() {
            let waker = noop_waker::noop_waker();
            let mut cx = Context::from_waker(&waker);
            match future.as_mut().poll(&mut cx) {
                Poll::Ready(Err(err)) => return Err(err),
                _ => {}
            }
        }

        Ok(())
    }

    /// Polls all futures `n` times.
    pub fn poll_n(&mut self, n: u32) -> emu::Result<()> {
        for _ in 0..n {
            self.poll()?;
        }

        Ok(())
    }

    /// Continuously polls this executor until [`EmulationError::Halt`] is signaled or another error
    /// is thrown.
    pub fn poll_until_halt(&mut self) -> emu::Result<()> {
        loop {
            if let Err(err) = self.poll() {
                if err == EmulationError::Halt {
                    return Ok(());
                } else {
                    return Err(err);
                }
            }
        }
    }
}
