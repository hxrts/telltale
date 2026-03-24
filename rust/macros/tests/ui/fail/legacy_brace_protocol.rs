use telltale_macros::choreography;

choreography! {
    protocol PingPong {
        roles Alice, Bob;
        Alice -> Bob: Ping;
        Bob -> Alice: Pong;
    }
}

fn main() {}
