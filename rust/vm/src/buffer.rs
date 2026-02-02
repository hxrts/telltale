//! Bounded buffers with backpressure.
//!
//! Matches the Lean `BoundedBuffer` from `runtime.md §6`.
//! Ring buffer with configurable mode and backpressure policy.

use serde::{Deserialize, Serialize};

use crate::coroutine::Value;

/// Buffer delivery mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BufferMode {
    /// First-in, first-out. All messages delivered in order.
    Fifo,
    /// Only the latest value is retained. Overwrites on enqueue.
    LatestValue,
}

/// Policy when a buffer is full.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BackpressurePolicy {
    /// Block the sender until space is available.
    Block,
    /// Drop the message silently.
    Drop,
    /// Return an error to the sender.
    Error,
    /// Resize the buffer up to a maximum capacity.
    Resize {
        /// Upper bound on buffer capacity.
        max_capacity: usize,
    },
}

/// Configuration for a buffer.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BufferConfig {
    /// Delivery mode.
    pub mode: BufferMode,
    /// Initial capacity.
    pub initial_capacity: usize,
    /// Backpressure policy.
    pub policy: BackpressurePolicy,
}

impl Default for BufferConfig {
    fn default() -> Self {
        Self {
            mode: BufferMode::Fifo,
            initial_capacity: 64,
            policy: BackpressurePolicy::Block,
        }
    }
}

/// Bounded ring buffer for inter-role message passing.
#[derive(Debug, Clone)]
pub struct BoundedBuffer {
    data: Vec<Option<Value>>,
    head: usize,
    tail: usize,
    capacity: usize,
    count: usize,
    epoch: usize,
    mode: BufferMode,
    policy: BackpressurePolicy,
}

/// Result of attempting to enqueue a value.
#[derive(Debug)]
pub enum EnqueueResult {
    /// Value was enqueued successfully.
    Ok,
    /// Buffer is full; sender should block.
    WouldBlock,
    /// Value was dropped per policy.
    Dropped,
    /// Buffer full and policy is Error.
    Full,
}

impl BoundedBuffer {
    /// Create a new buffer with the given configuration.
    #[must_use]
    pub fn new(config: &BufferConfig) -> Self {
        let capacity = config.initial_capacity.max(1);
        Self {
            data: vec![None; capacity],
            head: 0,
            tail: 0,
            capacity,
            count: 0,
            epoch: 0,
            mode: config.mode,
            policy: config.policy,
        }
    }

    /// Try to enqueue a value.
    pub fn enqueue(&mut self, v: Value) -> EnqueueResult {
        match self.mode {
            BufferMode::LatestValue => {
                // Overwrite the single slot.
                self.data[0] = Some(v);
                self.count = 1;
                EnqueueResult::Ok
            }
            BufferMode::Fifo => {
                if self.count >= self.capacity {
                    match self.policy {
                        BackpressurePolicy::Block => EnqueueResult::WouldBlock,
                        BackpressurePolicy::Drop => EnqueueResult::Dropped,
                        BackpressurePolicy::Error => EnqueueResult::Full,
                        BackpressurePolicy::Resize { max_capacity } => {
                            if self.capacity < max_capacity {
                                self.grow();
                                self.enqueue_fifo(v);
                                EnqueueResult::Ok
                            } else {
                                EnqueueResult::Full
                            }
                        }
                    }
                } else {
                    self.enqueue_fifo(v);
                    EnqueueResult::Ok
                }
            }
        }
    }

    /// Dequeue a value, if available.
    pub fn dequeue(&mut self) -> Option<Value> {
        match self.mode {
            BufferMode::LatestValue => {
                if self.count > 0 {
                    self.count = 0;
                    self.data[0].take()
                } else {
                    None
                }
            }
            BufferMode::Fifo => {
                if self.count == 0 {
                    return None;
                }
                let val = self.data[self.head].take();
                self.head = (self.head + 1) % self.capacity;
                self.count -= 1;
                val
            }
        }
    }

    /// Whether the buffer is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Whether the buffer is full (FIFO mode only).
    #[must_use]
    pub fn is_full(&self) -> bool {
        self.count >= self.capacity
    }

    /// Current number of buffered values.
    #[must_use]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Current epoch.
    #[must_use]
    pub fn epoch(&self) -> usize {
        self.epoch
    }

    /// Advance the epoch (used during session draining).
    pub fn advance_epoch(&mut self) {
        self.epoch += 1;
    }

    fn enqueue_fifo(&mut self, v: Value) {
        self.data[self.tail] = Some(v);
        self.tail = (self.tail + 1) % self.capacity;
        self.count += 1;
    }

    fn grow(&mut self) {
        let new_cap = self.capacity * 2;
        let mut new_data = vec![None; new_cap];

        // Copy existing elements in order.
        for (i, slot) in new_data.iter_mut().enumerate().take(self.count) {
            let idx = (self.head + i) % self.capacity;
            *slot = self.data[idx].take();
        }

        self.data = new_data;
        self.head = 0;
        self.tail = self.count;
        self.capacity = new_cap;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fifo_basic() {
        let mut buf = BoundedBuffer::new(&BufferConfig::default());
        buf.enqueue(Value::Int(1));
        buf.enqueue(Value::Int(2));
        assert_eq!(buf.len(), 2);
        assert_eq!(buf.dequeue(), Some(Value::Int(1)));
        assert_eq!(buf.dequeue(), Some(Value::Int(2)));
        assert!(buf.is_empty());
    }

    #[test]
    fn test_fifo_wraparound() {
        let config = BufferConfig {
            initial_capacity: 3,
            ..Default::default()
        };
        let mut buf = BoundedBuffer::new(&config);

        buf.enqueue(Value::Int(1));
        buf.enqueue(Value::Int(2));
        buf.dequeue(); // remove 1
        buf.enqueue(Value::Int(3));
        buf.enqueue(Value::Int(4));

        assert_eq!(buf.dequeue(), Some(Value::Int(2)));
        assert_eq!(buf.dequeue(), Some(Value::Int(3)));
        assert_eq!(buf.dequeue(), Some(Value::Int(4)));
        assert!(buf.is_empty());
    }

    #[test]
    fn test_latest_value_overwrites() {
        let config = BufferConfig {
            mode: BufferMode::LatestValue,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        };
        let mut buf = BoundedBuffer::new(&config);

        buf.enqueue(Value::Int(1));
        buf.enqueue(Value::Int(2));
        buf.enqueue(Value::Int(3));

        assert_eq!(buf.dequeue(), Some(Value::Int(3)));
        assert!(buf.is_empty());
    }

    #[test]
    fn test_backpressure_block() {
        let config = BufferConfig {
            initial_capacity: 2,
            policy: BackpressurePolicy::Block,
            ..Default::default()
        };
        let mut buf = BoundedBuffer::new(&config);
        buf.enqueue(Value::Int(1));
        buf.enqueue(Value::Int(2));
        assert!(matches!(buf.enqueue(Value::Int(3)), EnqueueResult::WouldBlock));
    }

    #[test]
    fn test_backpressure_resize() {
        let config = BufferConfig {
            initial_capacity: 2,
            policy: BackpressurePolicy::Resize { max_capacity: 8 },
            ..Default::default()
        };
        let mut buf = BoundedBuffer::new(&config);
        buf.enqueue(Value::Int(1));
        buf.enqueue(Value::Int(2));
        assert!(matches!(buf.enqueue(Value::Int(3)), EnqueueResult::Ok));
        assert_eq!(buf.len(), 3);
    }
}
