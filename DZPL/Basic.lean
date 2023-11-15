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

theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := calc x
  _ = x + 0        := by rw [identity_law]
  _ = x + (x + -x) := by rw [inverse_law]
  _ = (x + x) + -x := by rw [associative_law]
  _ = x + -x       := by rw [H]
  _ = 0            := by rw [inverse_law]

theorem sum_zero_implies_inverse {x y : G} (H : x + y = 0) : y = -x := calc y
  _ = y + 0        := by rw [identity_law]
  _ = y + (x + -x) := by rw [inverse_law]
  _ = (y + x) + -x := by rw [associative_law]
  _ = (x + y) + -x := by rw [commutative_law x y]
  _ = 0 + -x       := by rw [H]
  _ = -x + 0       := by rw [commutative_law]
  _ = -x           := by rw [identity_law]

theorem neg_is_involution (x : G) : -(-x) = x :=
  Eq.symm <| sum_zero_implies_inverse <| calc -x + x
    _ = x + -x := by rw [commutative_law]
    _ = 0 := by rw [inverse_law]

end AbelianGroup

--------------------------------------------------------------------------------

class Rng (R : Type u) extends AbelianGroup R, Mul R where
  mul_associative_law (x y z : R) : (x * y) * z = x * (y * z)
  left_distributive_law (x y z : R) : x * (y + z) = x * y + x * z
  right_distributive_law (x y z : R) : (x + y) * z = x * z + y * z

--------------------------------------------------------------------------------

namespace Rng

open AbelianGroup

variable {R : Type u} [Rng R]

theorem left_zero_mul_law (x : R) : 0 * x = 0 :=
  idempotent_is_zero <| calc 0 * x + 0 * x
    _ = (0 + 0) * x := by rw [right_distributive_law]
    _ = 0 * x       := by rw [identity_law]

theorem right_zero_mul_law (x : R) : x * 0 = 0 :=
  idempotent_is_zero <| calc x * 0 + x * 0
    _ = x * (0 + 0) := by rw [left_distributive_law]
    _ = x * 0       := by rw [identity_law]

theorem left_neg_mul_law (x y : R) : -x * y = -(x * y) :=
  sum_zero_implies_inverse <| calc x * y + -x * y
    _ = (x + -x) * y := by rw [right_distributive_law]
    _ = 0 * y        := by rw [inverse_law]
    _ = 0            := by rw [left_zero_mul_law]

theorem right_neg_mul_law (x y : R) : x * -y = -(x * y) :=
  sum_zero_implies_inverse <| calc x * y + x * -y
    _ = x * (y + -y) := by rw [left_distributive_law]
    _ = x * 0        := by rw [inverse_law]
    _ = 0            := by rw [right_zero_mul_law]

theorem neg_neg_mul_law (x y : R) : -x * -y = x * y := calc -x * -y
  _ = -(x * -y)  := by rw [left_neg_mul_law]
  _ = - -(x * y) := by rw [right_neg_mul_law]
  _ = x * y      := by rw [neg_is_involution]

end Rng

--------------------------------------------------------------------------------

class Ring (R : Type u) extends Rng R, HasOne R where
  left_identity_law (x : R) : 1 * x = x
  right_identity_law (x : R) : x * 1 = x

--------------------------------------------------------------------------------

namespace Ring

open Rng

variable {R : Type u} [Ring R]

theorem collapse_law : (0 : R) = (1 : R) -> ∀ x : R, x = 0 := by
  intro H x
  calc x
    _ = 1 * x := by rw [left_identity_law]
    _ = 0 * x := by rw [H]
    _ = 0     := by rw [left_zero_mul_law]

end Ring

--------------------------------------------------------------------------------

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
  add_order_law {x y : F} (H : x <= y) (z : F) : x + z <= y + z
  mul_order_law {x y : F} : 0 <= x -> 0 <= y -> 0 <= x * y

--------------------------------------------------------------------------------

namespace OrderedField

open AbelianGroup
open Rng
open Ring
open TotallyOrdered

variable {F : Type u} [OrderedField F]

theorem one_is_positive : (0 : F) <= (1 : F) := by
  cases totality_law (0 : F) (1 : F)
  . assumption
  . have H : (1 : F) <= (0 : F) := by assumption
    have lem1 : (-1 : F) * (-1 : F) = (1 : F) := by
      rw [neg_neg_mul_law, left_identity_law]
    have lem2 : (0 : F) <= (-1 : F) := calc (0 : F)
      _ = 1 + -1 := by rw [inverse_law]
      _ <= 0 + -1 := add_order_law H (-1)
      _ = -1 + 0 := by rw [commutative_law]
      _ = -1     := by rw [identity_law]
    rw [<- lem1]
    exact mul_order_law lem2 lem2

end OrderedField

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
  idempotent_is_zero <| calc δ (0 : R) + δ (0 : R)
    _ = δ ((0 : R) + (0 : R)) := by rw [additive_law]
    _ = δ (0 : R)             := by rw [identity_law]

theorem one_is_constant : IsConstant (1 : R) :=
  idempotent_is_zero <| calc δ (1 : R) + δ (1 : R)
    _ = δ (1 : R) * 1 + δ (1 : R)     := by rw [right_identity_law]
    _ = δ (1 : R) * 1 + 1 * δ (1 : R) := by rw [left_identity_law]
    _ = δ ((1 : R) * (1 : R))         := by rw [product_law]
    _ = δ (1 : R)                     := by rw [left_identity_law]

end DifferentialRing
