//! Compile-fail: undefined role used in send statement.
use telltale_macros::tell;

tell! {
    protocol Bad =
      roles A, B
      A -> C : Ping
}

fn main() {}
