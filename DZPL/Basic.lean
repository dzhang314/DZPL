set_option autoImplicit false

universe u

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

class Group (G : Type u) extends Mul G, HasOne G, HasInv G where
  associative_law (x y z : G) : (x * y) * z = x * (y * z)
  left_identity_law (x : G) : 1 * x = x
  left_inverse_law (x : G) : x⁻¹ * x = 1

--------------------------------------------------------------------------------

namespace Group

variable {G : Type u} [Group G]

theorem idempotent_is_identity {g : G} (H : g * g = g) : g = 1 := calc g
  _ = 1 * g         := by rw [left_identity_law]
  _ = (g⁻¹ * g) * g := by rw [left_inverse_law]
  _ = g⁻¹ * (g * g) := by rw [associative_law]
  _ = g⁻¹ * g       := by rw [H]
  _ = 1             := by rw [left_inverse_law]

theorem right_inverse_law (g : G) : g * g⁻¹ = 1 :=
  idempotent_is_identity <| calc (g * g⁻¹) * (g * g⁻¹)
    _ = g * (g⁻¹ * (g * g⁻¹)) := by rw [associative_law]
    _ = g * ((g⁻¹ * g) * g⁻¹) := by rw [associative_law]
    _ = g * (1 * g⁻¹)         := by rw [left_inverse_law]
    _ = g * g⁻¹               := by rw [left_identity_law]

theorem right_identity_law (g : G) : g * 1 = g := calc g * 1
  _ = g * (g⁻¹ * g) := by rw [left_inverse_law]
  _ = (g * g⁻¹) * g := by rw [associative_law]
  _ = 1 * g         := by rw [right_inverse_law]
  _ = g             := by rw [left_identity_law]

end Group

--------------------------------------------------------------------------------

class AbelianGroup (G : Type u) extends Add G, HasZero G, Neg G where
  commutative_law (x y : G) : x + y = y + x
  associative_law (x y z : G) : (x + y) + z = x + (y + z)
  identity_law (x : G) : x + 0 = x
  inverse_law (x : G) : x + -x = 0

--------------------------------------------------------------------------------

namespace AbelianGroup

variable {G : Type u} [AbelianGroup G]

theorem idempotent_is_identity {g : G} (H : g + g = g) : g = 0 := calc g
  _ = g + 0        := by rw [identity_law]
  _ = g + (g + -g) := by rw [inverse_law]
  _ = (g + g) + -g := by rw [associative_law]
  _ = g + -g       := by rw [H]
  _ = 0            := by rw [inverse_law]

end AbelianGroup

--------------------------------------------------------------------------------

class Rng (R : Type u) extends AbelianGroup R, Mul R where
  mul_associative_law (x y z : R) : (x * y) * z = x * (y * z)
  left_distributive_law (x y z : R) : x * (y + z) = x * y + x * z
  right_distributive_law (x y z : R) : (x + y) * z = x * z + y * z

class Ring (R : Type u) extends Rng R, HasOne R where
  left_identity_law (x : R) : 1 * x = x
  right_identity_law (x : R) : x * 1 = x

class CommutativeRing (R : Type u) extends Ring R where
  mul_commutative_law (x y : R) : x * y = y * x

class Field (F : Type u) extends CommutativeRing F, HasInv F where
  mul_inverse_law (x : F) : (x ≠ 0) -> x * x⁻¹ = 1
  inverse_zero_law : (0 : F)⁻¹ = 0

--------------------------------------------------------------------------------

class PartiallyOrdered (P : Type u) extends LE P where
  reflexive_law (x : P) : x <= x
  antisymmetry_law (x y : P) : x <= y -> y <= x -> x = y
  transitive_law (x y z : P) : x <= y -> y <= z -> x <= z

class TotallyOrdered (T : Type u) extends PartiallyOrdered T where
  totality_law (x y : T) : (x <= y) ∨ (y <= x)

class OrderedField (F : Type u) extends Field F, TotallyOrdered F where
  additive_law (x y z : F) : x <= y -> x + z <= y + z
  product_law (x y : F) : 0 <= x -> 0 <= y -> 0 <= x * y

--------------------------------------------------------------------------------

class DifferentialRing (R : Type u) extends Ring R where
  δ : R -> R
  additive_law (x y : R) : δ (x + y) = δ x + δ y
  product_law (x y : R) : δ (x * y) = δ x * y + x * δ y

--------------------------------------------------------------------------------

namespace DifferentialRing

open AbelianGroup
open Ring

variable {R : Type u} [DifferentialRing R]

def IsConstant (x : R) := δ x = 0

theorem zero_is_constant : IsConstant (0 : R) :=
  idempotent_is_identity <| calc δ (0 : R) + δ (0 : R)
    _ = δ ((0 : R) + (0 : R)) := by rw [additive_law]
    _ = δ (0 : R)             := by rw [identity_law]

theorem one_is_constant : IsConstant (1 : R) :=
  idempotent_is_identity <| calc δ (1 : R) + δ (1 : R)
    _ = δ (1 : R) * 1 + δ (1 : R)     := by rw [right_identity_law]
    _ = δ (1 : R) * 1 + 1 * δ (1 : R) := by rw [left_identity_law]
    _ = δ ((1 : R) * (1 : R))         := by rw [product_law]
    _ = δ (1 : R)                     := by rw [left_identity_law]

end DifferentialRing
