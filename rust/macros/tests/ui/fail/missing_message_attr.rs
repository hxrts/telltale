//! Compile-fail: Role derive missing #[message] attribute.
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use telltale::{
    channel::Bidirectional,
    Role,
};

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Role)]
struct Alice(#[route(Bob)] Channel);

enum Label {
    Ping,
}

struct Bob;

fn main() {}
