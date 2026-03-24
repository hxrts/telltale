use telltale_macros::tell;

tell! {
    protocol Bad =
      roles A, A
      A -> A : Ping
}

fn main() {}
