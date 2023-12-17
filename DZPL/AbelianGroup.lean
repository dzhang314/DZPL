import DZPL.Notation
set_option autoImplicit false
universe u

class AbelianGroup (G : Type u) extends Add G, HasZero G, Neg G where
  commutative_law (x y : G) : x + y = y + x
  associative_law (x y z : G) : (x + y) + z = x + (y + z)
  identity_law (x : G) : x + 0 = x
  inverse_law (x : G) : x + -x = 0

namespace AbelianGroup

variable {G : Type u} [AbelianGroup G]

@[simp]
example (x : G) : x + 0 = x := identity_law x

@[simp]
example (x : G) : x + -x = 0 := inverse_law x

theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := calc x
  _ = x + 0        := by rw [identity_law]
  _ = x + (x + -x) := by rw [inverse_law]
  _ = (x + x) + -x := by rw [associative_law]
  _ = x + -x       := by rw [H]
  _ = 0            := by rw [inverse_law]

theorem sum_zero_implies_inverse {x y : G} (H : x + y = 0) : -x = y := calc -x
  _ = -x + 0       := by rw [identity_law]
  _ = -x + (x + y) := by rw [H]
  _ = (-x + x) + y := by rw [associative_law]
  _ = (x + -x) + y := by rw [commutative_law x]
  _ = 0 + y        := by rw [inverse_law]
  _ = y + 0        := by rw [commutative_law]
  _ = y            := by rw [identity_law]

@[simp]
theorem neg_is_involution (x : G) : -(-x) = x :=
  sum_zero_implies_inverse <| calc -x + x
    _ = x + -x := by rw [commutative_law]
    _ = 0      := by rw [inverse_law]

end AbelianGroup
