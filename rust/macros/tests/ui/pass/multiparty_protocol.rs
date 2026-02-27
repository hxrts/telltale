use telltale_macros::choreography;

choreography! {
    protocol Demo {
        roles A, B, C;
        A -> B: Ping;
        B -> C: Relay(u64);
        C -> A: Ack;
    }
}

fn main() {
    let _roles = setup();
}
