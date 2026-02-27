use telltale_macros::choreography;

choreography! {
    protocol Bad {
        roles A, B;
        A -> B: Msg;
        A -> B: Msg(u64);
    }
}

fn main() {}
