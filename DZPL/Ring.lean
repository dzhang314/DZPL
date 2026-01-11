import DZPL.Rng
set_option autoImplicit false
set_option linter.all true
universe u

/-- A ring is a rng (`Rng R`) with a two-sided multiplicative identity element
    (`One R`). -/
class Ring (R : Type u) extends Rng R, One R where
  /-- Left multiplication by `1` leaves every element of a ring unchanged. -/
  left_identity_law (x : R) : 1 * x = x
  /-- Right multiplication by `1` leaves every element of a ring unchanged. -/
  right_identity_law (x : R) : x * 1 = x

namespace Ring

open Rng

variable {R : Type u} [Ring R]

/-- If `0 = 1` in a ring, then the ring collapses; `0` is its only element. -/
theorem collapse_law : (0 : R) = (1 : R) -> ∀ x : R, x = 0 :=
  fun H x => calc x
    _ = 1 * x := (left_identity_law x).symm
    _ = 0 * x := H.symm |> congrArg (· * x)
    _ = 0     := left_zero_mul_law x

end Ring
