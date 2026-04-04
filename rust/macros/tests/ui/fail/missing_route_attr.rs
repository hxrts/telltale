//! Compile-fail: Role derive missing #[route] attribute.
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use telltale::{
    channel::Bidirectional,
    Message, Role,
};

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Role)]
#[message(Label)]
struct Alice(Channel);

#[derive(Message)]
enum Label {
    Ping(Ping),
}

struct Bob;
struct Ping(u8);

fn main() {}
