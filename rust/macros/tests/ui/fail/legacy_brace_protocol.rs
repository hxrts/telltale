//! Compile-fail: legacy brace-delimited protocol syntax.
use telltale_macros::tell;

tell! {
    protocol PingPong {
        roles Alice, Bob;
        Alice -> Bob: Ping;
        Bob -> Alice: Pong;
    }
}

fn main() {}
