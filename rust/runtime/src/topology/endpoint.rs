//! Validated network endpoint type.

use std::fmt;
use std::net::SocketAddr;
use std::str::FromStr;
use thiserror::Error;

/// Error parsing an endpoint.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EndpointParseError {
    /// The endpoint format is invalid.
    #[error("invalid endpoint format: {input}")]
    InvalidFormat {
        /// The input string that failed to parse.
        input: String,
    },

    /// Missing port in endpoint.
    #[error("missing port in endpoint: {input}")]
    MissingPort {
        /// The input string missing a port.
        input: String,
    },

    /// Invalid port number.
    #[error("invalid port '{port}' in endpoint")]
    InvalidPort {
        /// The invalid port string.
        port: String,
    },
}

/// A validated network endpoint.
///
/// Represents a host:port combination. The host can be either an IP address
/// or a hostname. Hostname resolution happens at connection time.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[must_use]
pub struct Endpoint {
    host: String,
    port: u16,
}

impl Endpoint {
    /// Create an endpoint from host and port components.
    pub fn new(host: impl Into<String>, port: u16) -> Self {
        Self {
            host: host.into(),
            port,
        }
    }

    /// Create an endpoint from a socket address.
    pub fn from_socket_addr(addr: SocketAddr) -> Self {
        Self {
            host: addr.ip().to_string(),
            port: addr.port(),
        }
    }

    /// Parse an endpoint from a string (e.g., "127.0.0.1:8080" or "localhost:8080").
    pub fn parse(s: &str) -> Result<Self, EndpointParseError> {
        let s = s.trim();
        if s.is_empty() {
            return Err(EndpointParseError::InvalidFormat {
                input: s.to_string(),
            });
        }

        // Handle IPv6 addresses like [::1]:8080
        if s.starts_with('[') {
            if let Some(bracket_end) = s.find(']') {
                let host = &s[1..bracket_end];
                let rest = &s[bracket_end + 1..];
                if let Some(port_str) = rest.strip_prefix(':') {
                    let port = port_str.parse::<u16>().map_err(|_| {
                        EndpointParseError::InvalidPort {
                            port: port_str.to_string(),
                        }
                    })?;
                    return Ok(Self {
                        host: host.to_string(),
                        port,
                    });
                }
            }
            return Err(EndpointParseError::InvalidFormat {
                input: s.to_string(),
            });
        }

        // Handle regular host:port format
        let colon_pos = s.rfind(':').ok_or_else(|| EndpointParseError::MissingPort {
            input: s.to_string(),
        })?;

        let host = &s[..colon_pos];
        let port_str = &s[colon_pos + 1..];

        if host.is_empty() {
            return Err(EndpointParseError::InvalidFormat {
                input: s.to_string(),
            });
        }

        let port = port_str
            .parse::<u16>()
            .map_err(|_| EndpointParseError::InvalidPort {
                port: port_str.to_string(),
            })?;

        Ok(Self {
            host: host.to_string(),
            port,
        })
    }

    /// Get the host (IP address or hostname).
    pub fn host(&self) -> &str {
        &self.host
    }

    /// Get the port.
    pub fn port(&self) -> u16 {
        self.port
    }

    /// Try to convert to a SocketAddr.
    ///
    /// Returns `Some` if the host is a valid IP address, `None` if it's a hostname.
    pub fn to_socket_addr(&self) -> Option<SocketAddr> {
        if self.host.contains(':') {
            format!("[{}]:{}", self.host, self.port).parse().ok()
        } else {
            format!("{}:{}", self.host, self.port).parse().ok()
        }
    }
}

impl fmt::Display for Endpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Handle IPv6 addresses
        if self.host.contains(':') {
            write!(f, "[{}]:{}", self.host, self.port)
        } else {
            write!(f, "{}:{}", self.host, self.port)
        }
    }
}

impl FromStr for Endpoint {
    type Err = EndpointParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl From<SocketAddr> for Endpoint {
    fn from(addr: SocketAddr) -> Self {
        Self::from_socket_addr(addr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr};

    #[test]
    fn test_endpoint_parse_ipv4() {
        let endpoint = Endpoint::parse("127.0.0.1:8080").unwrap();
        assert_eq!(endpoint.host(), "127.0.0.1");
        assert_eq!(endpoint.port(), 8080);
        assert!(endpoint.to_socket_addr().is_some());
    }

    #[test]
    fn test_endpoint_parse_ipv6() {
        let endpoint = Endpoint::parse("[::1]:9000").unwrap();
        assert_eq!(endpoint.host(), "::1");
        assert_eq!(endpoint.port(), 9000);
        assert!(endpoint.to_socket_addr().is_some());
    }

    #[test]
    fn test_endpoint_parse_hostname() {
        let endpoint = Endpoint::parse("localhost:8080").unwrap();
        assert_eq!(endpoint.host(), "localhost");
        assert_eq!(endpoint.port(), 8080);
        // hostname can't be directly converted to SocketAddr
        assert!(endpoint.to_socket_addr().is_none());
    }

    #[test]
    fn test_endpoint_parse_fqdn() {
        let endpoint = Endpoint::parse("alice.prod.internal:8080").unwrap();
        assert_eq!(endpoint.host(), "alice.prod.internal");
        assert_eq!(endpoint.port(), 8080);
    }

    #[test]
    fn test_endpoint_display() {
        let endpoint = Endpoint::parse("192.168.1.1:443").unwrap();
        assert_eq!(endpoint.to_string(), "192.168.1.1:443");

        let endpoint_v6 = Endpoint::parse("[::1]:9000").unwrap();
        assert_eq!(endpoint_v6.to_string(), "[::1]:9000");
    }

    #[test]
    fn test_endpoint_from_socket_addr() {
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)), 3000);
        let endpoint = Endpoint::from(addr);
        assert_eq!(endpoint.host(), "10.0.0.1");
        assert_eq!(endpoint.port(), 3000);
    }

    #[test]
    fn test_endpoint_new() {
        let endpoint = Endpoint::new("my-service", 8080);
        assert_eq!(endpoint.host(), "my-service");
        assert_eq!(endpoint.port(), 8080);
    }

    #[test]
    fn test_endpoint_from_str() {
        let endpoint: Endpoint = "127.0.0.1:80".parse().unwrap();
        assert_eq!(endpoint.port(), 80);
    }

    #[test]
    fn test_endpoint_parse_invalid() {
        assert!(Endpoint::parse("").is_err());
        assert!(Endpoint::parse("127.0.0.1").is_err()); // missing port
        assert!(Endpoint::parse(":8080").is_err()); // missing host
        assert!(Endpoint::parse("host:not_a_port").is_err());
    }

    #[test]
    fn test_endpoint_equality() {
        let e1 = Endpoint::parse("127.0.0.1:8080").unwrap();
        let e2 = Endpoint::parse("127.0.0.1:8080").unwrap();
        let e3 = Endpoint::parse("127.0.0.1:8081").unwrap();
        assert_eq!(e1, e2);
        assert_ne!(e1, e3);
    }

    #[test]
    fn test_endpoint_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(Endpoint::parse("127.0.0.1:8080").unwrap());
        assert!(set.contains(&Endpoint::parse("127.0.0.1:8080").unwrap()));
        assert!(!set.contains(&Endpoint::parse("127.0.0.1:8081").unwrap()));
    }
}
