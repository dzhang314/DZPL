set_option autoImplicit false
universe u

class HasZero (T : Type u) where
  zero : T

class HasOne (T : Type u) where
  one : T

class HasInv (T : Type u) where
  inv : T -> T

instance (T : Type u) [HasZero T] : OfNat T 0 where
  ofNat := HasZero.zero

instance (T : Type u) [HasOne T] : OfNat T 1 where
  ofNat := HasOne.one

postfix:max "⁻¹" => HasInv.inv
