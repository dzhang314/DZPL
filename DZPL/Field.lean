import DZPL.DivisionRing
import DZPL.CommutativeRing
set_option autoImplicit false
set_option linter.all true
universe u

/-- A field is a division ring (`DivisionRing F`) in which multiplication is
    commutative (`CommutativeRing F`). -/
class Field (F : Type u) extends DivisionRing F, CommutativeRing F
