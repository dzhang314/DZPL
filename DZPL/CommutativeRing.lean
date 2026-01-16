import DZPL.AxiomFree
import DZPL.Ring
set_option autoImplicit false
set_option DZPL.axiomFree true
set_option linter.all true
universe u

/-- A commutative ring is a ring (`Ring R`) in which multiplication is
    commutative. -/
class CommutativeRing (R : Type u) extends Ring R where
  /-- Multiplication in a commutative ring is commutative. -/
  mul_commutative_law (x y : R) : x * y = y * x
