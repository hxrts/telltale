set_option autoImplicit false

namespace Runtime.Simulation

abbrev Scalar := Rat

/-- Clamp a scalar to a closed interval. -/
def clamp (x lo hi : Scalar) : Scalar :=
  if x < lo then lo else if x > hi then hi else x

/-- Rational approximation used by the Rust fixed-point tanh implementation. -/
def tanhApprox (x : Scalar) : Scalar :=
  if x >= (3 : Scalar) then
    (1 : Scalar)
  else if x <= (-3 : Scalar) then
    (-1 : Scalar)
  else
    let x2 := x * x
    x * ((27 : Scalar) + x2) / ((27 : Scalar) + (9 : Scalar) * x2)

/-- Absolute-difference comparison in rational space. -/
def ratAbs (x : Scalar) : Scalar :=
  if x < 0 then -x else x

/-- Absolute-difference comparison in rational space. -/
def approxEq (eps a b : Scalar) : Bool :=
  ratAbs (a - b) <= eps

end Runtime.Simulation
