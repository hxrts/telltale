//! Example demonstrating enhanced annotations in choreographic protocols
//!
//! This example shows how to use statement-level and role-specific annotations
//! for cost analysis, timeout management, and operational metadata.

use rumpsteak_aura_choreography_macros::choreography;

choreography! {
    #[namespace = "annotated_example"]
    CostAwareProtocol {
        roles: Client, Server, Database;
        
        // High-priority authentication with cost tracking
        [@priority = "high", @cost = 100, @timeout = 2000]
        Client -> Server: AuthRequest;
        
        // Server queries database with cost and timeout constraints
        Server[@timeout = 1000] -> Database[@cost = 50]: UserQuery;
        
        // Database responds with compressed data
        [@compress = "gzip", @buffered]
        Database -> Server: UserData;
        
        // Critical operation with audit logging
        [@critical, @audit_log = "true", @cost = 200]
        Server -> Client: AuthResponse;
        
        choice Client {
            continue: {
                // Low-cost data request with retry capability
                [@cost = 25, @retry = 3]
                Client -> Server: DataRequest;
                
                // Server processes with medium priority
                Server[@priority = "medium"] -> Database: DataQuery;
                
                // Efficient data transfer
                [@buffered, @timeout = 5000]
                Database -> Server: DataResult;
                
                Server -> Client: DataResponse;
            }
            disconnect: {
                // Cleanup operation
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
        
        // Load-balanced request distribution
        [@load_balance = "round_robin", @timeout = 1000]
        Gateway -> Services[*]: WorkRequest;
        
        // Services process with different priorities
        Services[i][@priority = "low"] -> Database[@cost = 30]: Query;
        
        // Database responds with caching hints
        [@cache_ttl = 300, @compress = "lz4"]
        Database -> Services[i]: QueryResult;
        
        // Services aggregate with retry logic
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