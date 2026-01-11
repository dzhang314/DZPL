import DZPL.CommutativeRing
set_option autoImplicit false
set_option linter.all true
universe u

/-- A field is a commutative ring (`CommutativeRing F`) in which every nonzero
    element has a multiplicative inverse (`Inv F`). -/
class Field (F : Type u) extends CommutativeRing F, Inv F where
  /-- Every nonzero element of a field has a multiplicative inverse. -/
  mul_inverse_law (x : F) : (x ≠ 0) -> x * x⁻¹ = 1
  /-- In a field, the inverse of `0` is defined to be `0`. -/
  zero_inverse_law : (0 : F)⁻¹ = 0
