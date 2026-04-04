//! Compile-fail: string literal passed to tell! macro.
use telltale_macros::tell;

tell!(r#"
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#);

fn main() {}
