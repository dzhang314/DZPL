import DZPL.OrderedRng
import DZPL.Ring
set_option autoImplicit false
set_option linter.all true
universe u

/-- An ordered ring is an ordered rng (`OrderedRng R`) that is also a nonzero
    ring (`Ring R`). -/
class OrderedRing (R : Type u) extends OrderedRng R, Ring R where
  /-- The zero ring is not considered an ordered ring. -/
  nonzero_law : (0 : R) ≠ (1 : R)

namespace OrderedRing

open OrderedRng

variable {R : Type u} [OrderedRing R]

/-- In an ordered ring, zero is less than or equal to one. -/
theorem one_is_nonnegative : (0 : R) ≤ (1 : R) :=
  trans (square_is_nonnegative (1 : R)) (left_identity_law (1 : R))

/-- In an ordered ring, zero is strictly less than one. -/
theorem one_is_positive : (0 : R) < (1 : R) :=
  And.intro one_is_nonnegative nonzero_law

end OrderedRing
