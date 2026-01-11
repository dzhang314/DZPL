import DZPL.AbelianGroup
set_option autoImplicit false
set_option linter.all true
universe u

--------------------------------------------------------------------------------

class Rng (R : Type u) extends AbelianGroup R, Mul R where
  mul_associative_law (x y z : R) : (x * y) * z = x * (y * z)
  left_distributive_law (x y z : R) : x * (y + z) = x * y + x * z
  right_distributive_law (x y z : R) : (x + y) * z = x * z + y * z

--------------------------------------------------------------------------------

namespace Rng

open AbelianGroup

variable {R : Type u} [Rng R]

@[simp]
theorem left_zero_mul_law (x : R) : 0 * x = 0 :=
  idempotent_is_zero <| calc 0 * x + 0 * x
    _ = (0 + 0) * x := by rw [right_distributive_law]
    _ = 0 * x       := by rw [zero_law]

@[simp]
theorem right_zero_mul_law (x : R) : x * 0 = 0 :=
  idempotent_is_zero <| calc x * 0 + x * 0
    _ = x * (0 + 0) := by rw [left_distributive_law]
    _ = x * 0       := by rw [zero_law]

@[simp]
theorem left_neg_mul_law (x y : R) : -x * y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + -x * y
    _ = (x + -x) * y := by rw [right_distributive_law]
    _ = 0 * y        := by rw [negative_law]
    _ = 0            := by rw [left_zero_mul_law]

@[simp]
theorem right_neg_mul_law (x y : R) : x * -y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + x * -y
    _ = x * (y + -y) := by rw [left_distributive_law]
    _ = x * 0        := by rw [negative_law]
    _ = 0            := by rw [right_zero_mul_law]

end Rng

--------------------------------------------------------------------------------

class Ring (R : Type u) extends Rng R, One R where
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

class Field (F : Type u) extends CommutativeRing F, Inv F where
  mul_inverse_law (x : F) : (x ≠ 0) -> x * x⁻¹ = 1
  inverse_zero_law : (0 : F)⁻¹ = 0

--------------------------------------------------------------------------------

class PartiallyOrdered (P : Type u) extends LE P where
  reflexive_law (x : P) : x <= x
  antisymmetry_law (x y : P) : (x <= y) -> (y <= x) -> (x = y)
  transitive_law (x y z : P) : (x <= y) -> (y <= z) -> (x <= z)

class TotallyOrdered (T : Type u) extends PartiallyOrdered T where
  totality_law (x y : T) : (x <= y) ∨ (y <= x)

class OrderedField (F : Type u) extends Field F, TotallyOrdered F where
  add_order_law {x y : F} (H : x <= y) (z : F) : x + z <= y + z
  mul_order_law {x y : F} : (0 <= x) -> (0 <= y) -> (0 <= x * y)

--------------------------------------------------------------------------------

namespace OrderedField

open AbelianGroup
open Rng
open Ring
open TotallyOrdered

variable {F : Type u} [OrderedField F]

-- theorem square_is_positive (x : F) : 0 <= x * x := by
--   cases totality_law 0 x
--   . have H : 0 <= x := by assumption
--     exact mul_order_law H H
--   . have H : x <= 0 := by assumption
--     have lem : 0 <= -x := calc (0 : F)
--       _ = x + -x  := by rw [inverse_law]
--       _ <= 0 + -x := add_order_law H (-x)
--       _ = -x + 0  := by rw [commutative_law]
--       _ = -x      := by rw [identity_law]
--     rw [<- neg_neg_mul_law]
--     exact mul_order_law lem lem

-- theorem one_is_positive : (0 : F) <= (1 : F) := by
--   rw [<- left_identity_law 1]
--   exact square_is_positive 1

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
    _ = δ (0 : R)             := by rw [zero_law]

theorem one_is_constant : IsConstant (1 : R) :=
  idempotent_is_zero <| calc δ (1 : R) + δ (1 : R)
    _ = δ (1 : R) * 1 + δ (1 : R)     := by rw [right_identity_law]
    _ = δ (1 : R) * 1 + 1 * δ (1 : R) := by rw [left_identity_law]
    _ = δ ((1 : R) * (1 : R))         := by rw [product_law]
    _ = δ (1 : R)                     := by rw [left_identity_law]

end DifferentialRing
