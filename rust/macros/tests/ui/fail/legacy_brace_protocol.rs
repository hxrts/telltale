use telltale_macros::tell;

tell! {
    protocol PingPong {
        roles Alice, Bob;
        Alice -> Bob: Ping;
        Bob -> Alice: Pong;
    }
}

fn main() {}
