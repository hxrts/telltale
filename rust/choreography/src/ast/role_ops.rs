use super::*;

// Validation implementations for role types.
impl RoleParam {
    /// Validate role parameter for safety constraints.
    pub fn validate(&self) -> RoleValidationResult<()> {
        match self {
            RoleParam::Static(count) => {
                if *count > MAX_ROLE_COUNT {
                    return Err(RoleValidationError::CountOverflow {
                        count: *count,
                        max: MAX_ROLE_COUNT,
                    });
                }
                Ok(())
            }
            RoleParam::Symbolic(_) => Ok(()),
            RoleParam::Runtime => Ok(()),
        }
    }

    /// Validate role parameter in combination with an index.
    pub fn validate_with_index(&self, index: &RoleIndex) -> RoleValidationResult<()> {
        match (self, index) {
            (RoleParam::Static(count), RoleIndex::Concrete(idx)) => {
                if *idx >= *count {
                    return Err(RoleValidationError::IndexOverflow {
                        index: *idx,
                        max: *count - 1,
                    });
                }
                Ok(())
            }
            (RoleParam::Static(count), RoleIndex::Range(range)) => {
                if let (RangeExpr::Concrete(_), RangeExpr::Concrete(end)) =
                    (&range.start, &range.end)
                {
                    if *end > *count {
                        return Err(RoleValidationError::IndexOverflow {
                            index: *end,
                            max: *count,
                        });
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Create a safe static role parameter.
    pub fn safe_static(count: u32) -> RoleValidationResult<Self> {
        if count > MAX_ROLE_COUNT {
            return Err(RoleValidationError::CountOverflow {
                count,
                max: MAX_ROLE_COUNT,
            });
        }
        Ok(RoleParam::Static(count))
    }
}

impl RoleIndex {
    /// Validate role index for safety constraints.
    pub fn validate(&self) -> RoleValidationResult<()> {
        match self {
            RoleIndex::Concrete(index) => {
                if *index > MAX_ROLE_INDEX {
                    return Err(RoleValidationError::IndexOverflow {
                        index: *index,
                        max: MAX_ROLE_INDEX,
                    });
                }
                Ok(())
            }
            RoleIndex::Symbolic(_) | RoleIndex::Wildcard => Ok(()),
            RoleIndex::Range(range) => range.validate(),
        }
    }

    /// Create a safe concrete index.
    pub fn safe_concrete(index: u32) -> RoleValidationResult<Self> {
        if index > MAX_ROLE_INDEX {
            return Err(RoleValidationError::IndexOverflow {
                index,
                max: MAX_ROLE_INDEX,
            });
        }
        Ok(RoleIndex::Concrete(index))
    }
}

impl RoleRange {
    /// Validate role range for safety constraints.
    pub fn validate(&self) -> RoleValidationResult<()> {
        self.start.validate()?;
        self.end.validate()?;

        if let (RangeExpr::Concrete(start), RangeExpr::Concrete(end)) = (&self.start, &self.end) {
            if start >= end {
                return Err(RoleValidationError::InvalidRange {
                    start: *start,
                    end: *end,
                });
            }

            let range_size = end - start;
            if range_size > MAX_RANGE_COUNT {
                return Err(RoleValidationError::RangeSizeOverflow {
                    size: range_size,
                    max: MAX_RANGE_COUNT,
                });
            }
        }

        Ok(())
    }

    /// Create a safe concrete range.
    pub fn safe_concrete(start: u32, end: u32) -> RoleValidationResult<Self> {
        let range = RoleRange {
            start: RangeExpr::Concrete(start),
            end: RangeExpr::Concrete(end),
        };
        range.validate()?;
        Ok(range)
    }
}

impl RangeExpr {
    /// Validate range expression for safety constraints.
    pub fn validate(&self) -> RoleValidationResult<()> {
        match self {
            RangeExpr::Concrete(value) => {
                if *value > MAX_ROLE_INDEX {
                    return Err(RoleValidationError::IndexOverflow {
                        index: *value,
                        max: MAX_ROLE_INDEX,
                    });
                }
                Ok(())
            }
            RangeExpr::Symbolic(_) => Ok(()),
        }
    }
}

/// Runtime bounds checker for dynamic roles.
pub struct RoleBoundsChecker {
    max_count: u32,
    max_index: u32,
}

impl Default for RoleBoundsChecker {
    fn default() -> Self {
        Self {
            max_count: MAX_ROLE_COUNT,
            max_index: MAX_ROLE_INDEX,
        }
    }
}

impl RoleBoundsChecker {
    /// Create a new bounds checker with custom limits.
    pub fn new(max_count: u32, max_index: u32) -> Self {
        Self {
            max_count,
            max_index,
        }
    }

    /// Check if a runtime role count is within bounds.
    pub fn check_count(&self, count: u32) -> RoleValidationResult<()> {
        if count > self.max_count {
            return Err(RoleValidationError::CountOverflow {
                count,
                max: self.max_count,
            });
        }
        Ok(())
    }

    /// Check if a runtime role index is within bounds.
    pub fn check_index(&self, index: u32) -> RoleValidationResult<()> {
        if index > self.max_index {
            return Err(RoleValidationError::IndexOverflow {
                index,
                max: self.max_index,
            });
        }
        Ok(())
    }

    /// Check if a runtime range is within bounds.
    pub fn check_range(&self, start: u32, end: u32) -> RoleValidationResult<()> {
        if start >= end {
            return Err(RoleValidationError::InvalidRange { start, end });
        }

        if end > self.max_index {
            return Err(RoleValidationError::IndexOverflow {
                index: end,
                max: self.max_index,
            });
        }

        let range_size = end - start;
        if range_size > MAX_RANGE_COUNT {
            return Err(RoleValidationError::RangeSizeOverflow {
                size: range_size,
                max: MAX_RANGE_COUNT,
            });
        }

        Ok(())
    }
}

impl std::fmt::Display for RoleIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RoleIndex::Concrete(index) => write!(f, "{}", index),
            RoleIndex::Symbolic(name) => write!(f, "{}", name),
            RoleIndex::Wildcard => write!(f, "*"),
            RoleIndex::Range(range) => write!(f, "{}", range),
        }
    }
}

impl std::fmt::Display for RoleRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl std::fmt::Display for RangeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RangeExpr::Concrete(value) => write!(f, "{}", value),
            RangeExpr::Symbolic(name) => write!(f, "{}", name),
        }
    }
}

impl std::fmt::Display for RoleParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RoleParam::Static(count) => write!(f, "{}", count),
            RoleParam::Symbolic(name) => write!(f, "{}", name),
            RoleParam::Runtime => write!(f, "*"),
        }
    }
}
