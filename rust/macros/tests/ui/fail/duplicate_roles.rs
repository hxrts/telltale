use telltale_macros::choreography;

choreography! {
    protocol Bad {
        roles A, A;
        A -> A: Ping;
    }
}

fn main() {}
