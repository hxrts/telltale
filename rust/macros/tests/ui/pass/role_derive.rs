use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use telltale::{
    channel::Bidirectional,
    Message, Role, Route,
};

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Role)]
#[message(Label)]
struct Alice(#[route(Bob)] Channel);

#[derive(Role)]
#[message(Label)]
struct Bob(#[route(Alice)] Channel);

#[derive(Message)]
enum Label {
    Ping(Ping),
}

struct Ping(u8);

fn main() {
    let _: fn(&mut Alice) -> &mut Channel = <Alice as Route<Bob>>::route;
}
