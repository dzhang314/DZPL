import DZPL.Ring
set_option autoImplicit false
set_option linter.all true
universe u

/-- A division ring is a ring (`Ring R`) in which every nonzero element has a
    multiplicative inverse (`Inv R`). -/
class DivisionRing (D : Type u) extends Ring D, Inv D where
  /-- Every nonzero element of a division ring has a multiplicative inverse. -/
  left_inverse_law (x : D) : (x = (0 : D)) ∨ (x⁻¹ * x = (1 : D))
  /-- In a division ring, the inverse of `0` is defined to be `0`. -/
  zero_inverse_law : (0 : D)⁻¹ = (0 : D)

namespace DivisionRing

open Ring
open Rng

variable {D : Type u} [DivisionRing D]

/-- The only element of a division ring whose inverse is `0` is `0` itself. -/
theorem inverse_zero_implies_zero {x : D} (H : x⁻¹ = (0 : D)) : x = (0 : D) :=
  match left_inverse_law x with
  | Or.inl (Hx : x = (0 : D)) => Hx
  | Or.inr (Hx : x⁻¹ * x = (1 : D)) => calc x
    _ = x * (1 : D)       := right_identity_law x |> Eq.symm
    _ = x * (x⁻¹ * x)     := Hx |> Eq.symm |> congrArg (x * ·)
    _ = x * ((0 : D) * x) := H |> congrArg (· * x) |> congrArg (x * ·)
    _ = x * (0 : D)       := mul_zero_left x |> congrArg (x * ·)
    _ = (0 : D)           := mul_zero_right x

/-- Every nonzero element of a division ring has a multiplicative inverse. -/
theorem right_inverse_law (x : D) : (x = (0 : D)) ∨ (x * x⁻¹ = (1 : D)) :=
  sorry

end DivisionRing
