//! Example demonstrating enhanced annotations in choreographic protocols
//!
//! This example shows how to use statement-level and role-specific annotations
//! for cost analysis, timeout management, and operational metadata.

use rumpsteak_aura_choreography_macros::choreography;

choreography! {
    #[namespace = "annotated_example"]
    CostAwareProtocol {
        roles: Client, Server, Database;

        // Statement-level annotations: apply to the entire interaction
        [@priority = "high", @cost = 100, @timeout = 2000]
        Client -> Server: AuthRequest;

        // Role-specific annotations: Server[@timeout] on sender, Database[@cost] on receiver
        Server[@timeout = 1000] -> Database[@cost = 50]: UserQuery;

        // Statement-level annotations: compression and buffering for the message
        [@compress = "gzip", @buffered]
        Database -> Server: UserData;

        // Statement-level annotations: critical operation with audit logging
        [@critical, @audit_log = "true", @cost = 200]
        Server -> Client: AuthResponse;

        choice Client {
            continue: {
                // Statement-level annotations: cost tracking and retry policy
                [@cost = 25, @retry = 3]
                Client -> Server: DataRequest;

                // Role-specific annotation: Server[@priority] on sender only
                Server[@priority = "medium"] -> Database: DataQuery;

                // Statement-level annotations: buffering and timeout for transfer
                [@buffered, @timeout = 5000]
                Database -> Server: DataResult;

                Server -> Client: DataResponse;
            }
            disconnect: {
                // Statement-level annotation: cost of cleanup
                [@cost = 10]
                Client -> Server: Disconnect;
            }
        }
    }
}

choreography! {
    #[namespace = "microservice_example"]
    MicroserviceOrchestration {
        roles: Gateway, Services[*], Database;

        // Statement-level annotations: load balancing strategy and timeout
        [@load_balance = "round_robin", @timeout = 1000]
        Gateway -> Services[*]: WorkRequest;

        // Role-specific annotations: Services[i][@priority] on sender, Database[@cost] on receiver
        Services[i][@priority = "low"] -> Database[@cost = 30]: Query;

        // Statement-level annotations: caching and compression hints
        [@cache_ttl = 300, @compress = "lz4"]
        Database -> Services[i]: QueryResult;

        // Statement-level annotations: retry policy and timeout for aggregation
        [@retry = 2, @timeout = 3000]
        Services[0..available] -> Gateway: WorkResult;
    }
}

fn main() {
    println!("Enhanced Annotations Example");
    println!("============================");
    println!();

    println!("CostAwareProtocol annotations:");
    println!("- @cost: Tracks execution cost for billing/optimization");
    println!("- @priority: Sets operation priority (high/medium/low)");
    println!("- @timeout: Specifies timeout in milliseconds");
    println!("- @critical: Marks operations requiring special handling");
    println!("- @audit_log: Enables audit logging for compliance");
    println!("- @compress: Specifies compression algorithm");
    println!("- @buffered: Enables message buffering");
    println!("- @retry: Sets retry count for fault tolerance");
    println!();

    println!("MicroserviceOrchestration annotations:");
    println!("- @load_balance: Specifies load balancing strategy");
    println!("- @cache_ttl: Sets cache time-to-live in seconds");
    println!("- Role-specific timeouts and costs for fine-grained control");
    println!();

    println!("These annotations can be used by:");
    println!("- Runtime systems for optimization and resource management");
    println!("- Monitoring tools for observability and alerting");
    println!("- Cost analysis tools for billing and budget planning");
    println!("- Compliance systems for audit trail generation");
}
