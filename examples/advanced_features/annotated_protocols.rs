//! Example demonstrating updated protocol syntax.
//!
//! Annotation syntax was removed from the DSL, so this example now focuses on
//! basic protocol flows using the new syntax.

use rumpsteak_aura_choreography_macros::choreography;

choreography! {
    protocol CostAwareProtocol = {
        roles Client, Server, Database
        Client -> Server : AuthRequest
        Server -> Database : UserQuery
        Database -> Server : UserData
        Server -> Client : AuthResponse
    }
}

choreography! {
    protocol MicroserviceOrchestration = {
        roles Gateway, Service, Database
        Gateway -> Service : WorkRequest
        Service -> Database : Query
        Database -> Service : QueryResult
        Service -> Gateway : WorkResult
    }
}

fn main() {
    println!("Updated protocol examples (annotation syntax removed).");
}
