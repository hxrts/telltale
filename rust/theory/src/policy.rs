//! Scheduler policies for work-queue based algorithms.
//!
//! This is a stub module used to prepare for the work-budget refactor.

use std::collections::VecDeque;

/// A pluggable policy for ordering work in a queue.
pub trait SchedulerPolicy<State> {
    /// Pop the next state from the frontier.
    fn pop(&mut self, frontier: &mut VecDeque<State>) -> Option<State>;

    /// Push a new state into the frontier.
    fn push(&mut self, frontier: &mut VecDeque<State>, state: State);
}

/// FIFO policy (breadth-first).
#[derive(Debug, Default, Clone, Copy)]
pub struct BreadthFirst;

impl<State> SchedulerPolicy<State> for BreadthFirst {
    fn pop(&mut self, frontier: &mut VecDeque<State>) -> Option<State> {
        frontier.pop_front()
    }

    fn push(&mut self, frontier: &mut VecDeque<State>, state: State) {
        frontier.push_back(state);
    }
}

/// LIFO policy (depth-first).
#[derive(Debug, Default, Clone, Copy)]
pub struct DepthFirst;

impl<State> SchedulerPolicy<State> for DepthFirst {
    fn pop(&mut self, frontier: &mut VecDeque<State>) -> Option<State> {
        frontier.pop_back()
    }

    fn push(&mut self, frontier: &mut VecDeque<State>, state: State) {
        frontier.push_back(state);
    }
}

/// Round-robin policy (front-of-queue rotation).
#[derive(Debug, Default, Clone, Copy)]
pub struct RoundRobin;

impl<State> SchedulerPolicy<State> for RoundRobin {
    fn pop(&mut self, frontier: &mut VecDeque<State>) -> Option<State> {
        frontier.pop_front()
    }

    fn push(&mut self, frontier: &mut VecDeque<State>, state: State) {
        frontier.push_back(state);
    }
}
