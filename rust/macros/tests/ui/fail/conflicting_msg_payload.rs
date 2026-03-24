use telltale_macros::tell;

tell! {
    protocol Bad =
      roles A, B
      A -> B : Msg
      A -> B : Msg(u64)
}

fn main() {}
