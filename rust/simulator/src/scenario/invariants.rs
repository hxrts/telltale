use crate::property::Property;

pub(super) fn parse_invariant(name: &str) -> Result<Property, String> {
    match name {
        "no_faults" => Ok(Property::NoFaults),
        "simplex" => Ok(Property::Simplex),
        _ => parse_parameterized_invariant(name),
    }
}

fn parse_parameterized_invariant(name: &str) -> Result<Property, String> {
    if let Some((base, args)) = parse_call(name) {
        match base {
            "send_recv_liveness" => return parse_send_recv_liveness(&args),
            "buffer_bound" => return parse_buffer_bound(&args),
            "type_monotonicity" => return parse_type_monotonicity(&args),
            _ => {}
        }
    }
    Err(format!("unknown invariant: {name}"))
}

fn parse_send_recv_liveness(args: &[&str]) -> Result<Property, String> {
    if args.len() != 2 {
        return Err("send_recv_liveness requires (sid,bound)".into());
    }
    let sid = args[0]
        .parse::<usize>()
        .map_err(|_| "invalid session id".to_string())?;
    let bound = args[1]
        .parse::<usize>()
        .map_err(|_| "invalid bound".to_string())?;
    Ok(Property::SendRecvLiveness { sid, bound })
}

fn parse_buffer_bound(args: &[&str]) -> Result<Property, String> {
    if args.len() != 2 {
        return Err("buffer_bound requires (sid,max)".into());
    }
    let sid = args[0]
        .parse::<usize>()
        .map_err(|_| "invalid session id".to_string())?;
    let max = args[1]
        .parse::<usize>()
        .map_err(|_| "invalid max".to_string())?;
    Ok(Property::BufferBound { sid, max })
}

fn parse_type_monotonicity(args: &[&str]) -> Result<Property, String> {
    if args.len() != 1 {
        return Err("type_monotonicity requires (sid)".into());
    }
    let sid = args[0]
        .parse::<usize>()
        .map_err(|_| "invalid session id".to_string())?;
    Ok(Property::TypeMonotonicity { sid })
}

fn parse_call(expr: &str) -> Option<(&str, Vec<&str>)> {
    let expr = expr.trim();
    let expr = expr.strip_suffix(')')?;
    let (name, args) = expr.split_once('(')?;
    let args = args
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
    Some((name.trim(), args))
}
