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

/-- A zero ring is a ring with only one element, `0`. -/
def ZeroRing (R : Type u) [Ring R] : Prop := ∀ x : R, x = 0

namespace Ring

open Rng

variable {R : Type u} [Ring R]

/-- If `0 = 1` in a ring, then the ring is a zero ring. -/
theorem zero_ring_law : (0 : R) = (1 : R) -> ZeroRing R :=
  fun (H : 0 = 1) (x : R) => calc x
    _ = 1 * x := left_identity_law x |> Eq.symm
    _ = 0 * x := H |> Eq.symm |> congrArg (· * x)
    _ = 0     := mul_zero_left x

end Ring
