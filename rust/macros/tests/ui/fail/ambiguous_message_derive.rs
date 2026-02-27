use telltale_macros::Message;

#[derive(Message)]
enum Bad {
    First(u64),
    Second(u64),
}

fn main() {}
