use telltale_macros::choreography;

choreography! {
    protocol Bad {
        roles A, B;
        A -> C: Ping;
    }
}

fn main() {}
