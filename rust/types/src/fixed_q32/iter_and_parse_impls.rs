impl Sum for FixedQ32 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc.saturating_add(x))
    }
}

impl<'a> Sum<&'a FixedQ32> for FixedQ32 {
    fn sum<I: Iterator<Item = &'a FixedQ32>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc.saturating_add(*x))
    }
}

impl FromStr for FixedQ32 {
    type Err = FixedQ32Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_decimal_str(s)
    }
}
