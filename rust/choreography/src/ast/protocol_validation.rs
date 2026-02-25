use super::{Branch, NonEmptyVec, Protocol, Role, ValidationError};

fn is_declared_role(roles: &[Role], role: &Role) -> bool {
    roles.iter().any(|declared| role.matches_family(declared))
}

pub(super) fn ensure_declared_role(roles: &[Role], role: &Role) -> Result<(), ValidationError> {
    if is_declared_role(roles, role) {
        return Ok(());
    }
    Err(ValidationError::UndefinedRole(role.name().to_string()))
}

pub(super) fn validate_choice_branches(
    role: &Role,
    branches: &NonEmptyVec<Branch>,
) -> Result<(), ValidationError> {
    for branch in branches {
        if let Protocol::Send { from, .. } = &branch.protocol {
            if from == role {
                continue;
            }
        }
        return Err(ValidationError::InvalidChoice(role.name().to_string()));
    }
    Ok(())
}
