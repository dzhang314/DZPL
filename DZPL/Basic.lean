import DZPL.AbelianGroup
set_option autoImplicit false
set_option linter.all true
universe u

--------------------------------------------------------------------------------

/-- A rng is a type `R` with an addition operation (`Add R`) that forms an
    abelian group (`AbelianGroup R`) and a multiplication operation (`Mul R`)
    that is associative and distributes over addition. -/
class Rng (R : Type u) extends AbelianGroup R, Mul R where
  /-- Multiplication in a rng is associative. -/
  mul_associative_law (x y z : R) : (x * y) * z = x * (y * z)
  /-- Left multiplication in a rng distributes over addition. -/
  left_distributive_law (x y z : R) : x * (y + z) = x * y + x * z
  /-- Right multiplication in a rng distributes over addition. -/
  right_distributive_law (x y z : R) : (x + y) * z = x * z + y * z

--------------------------------------------------------------------------------

namespace Rng

open AbelianGroup

variable {R : Type u} [Rng R]

/-- In a rng, left multiplication by `0` yields `0`. -/
theorem left_zero_mul_law (x : R) : 0 * x = 0 :=
  idempotent_is_zero <| calc 0 * x + 0 * x
    _ = (0 + 0) * x := (right_distributive_law 0 0 x).symm
    _ = 0 * x       := zero_law 0 |> congrArg (· * x)

/-- In a rng, right multiplication by `0` yields `0`. -/
theorem right_zero_mul_law (x : R) : x * 0 = 0 :=
  idempotent_is_zero <| calc x * 0 + x * 0
    _ = x * (0 + 0) := (left_distributive_law x 0 0).symm
    _ = x * 0       := zero_law 0 |> congrArg (x * ·)

/-- In a rng, a product with a negative on the left is the negative of the
    product. -/
theorem left_neg_mul_law (x y : R) : -x * y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + -x * y
    _ = (x + -x) * y := (right_distributive_law x (-x) y).symm
    _ = 0 * y        := negative_law x |> congrArg (· * y)
    _ = 0            := left_zero_mul_law y

/-- In a rng, a product with a negative on the right is the negative of the
    product. -/
theorem right_neg_mul_law (x y : R) : x * -y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + x * -y
    _ = x * (y + -y) := (left_distributive_law x y (-y)).symm
    _ = x * 0        := negative_law y |> congrArg (x * ·)
    _ = 0            := right_zero_mul_law x

end Rng

--------------------------------------------------------------------------------

/-- A ring is a rng (`Rng R`) with a multiplicative identity (`One R`). -/
class Ring (R : Type u) extends Rng R, One R where
  /-- Left multiplication by `1` leaves every element of a ring unchanged. -/
  left_identity_law (x : R) : 1 * x = x
  /-- Right multiplication by `1` leaves every element of a ring unchanged. -/
  right_identity_law (x : R) : x * 1 = x

--------------------------------------------------------------------------------

namespace Ring

open Rng

variable {R : Type u} [Ring R]

/-- If `0 = 1` in a ring, then the ring collapses; every element equals `0`. -/
theorem collapse_law : (0 : R) = (1 : R) -> ∀ x : R, x = 0 :=
  fun H x => calc x
    _ = 1 * x := (left_identity_law x).symm
    _ = 0 * x := H.symm |> congrArg (· * x)
    _ = 0     := left_zero_mul_law x

end Ring

--------------------------------------------------------------------------------

/-- A commutative ring is a ring in which multiplication is commutative. -/
class CommutativeRing (R : Type u) extends Ring R where
  /-- Multiplication in a commutative ring is commutative. -/
  mul_commutative_law (x y : R) : x * y = y * x

/-- A field is a commutative ring in which every nonzero element has a
    multiplicative inverse. -/
class Field (F : Type u) extends CommutativeRing F, Inv F where
  /-- Every nonzero element of a field has a multiplicative inverse. -/
  mul_inverse_law (x : F) : (x ≠ 0) -> x * x⁻¹ = 1
  /-- In a field, the inverse of `0` is defined to be `0`. -/
  zero_inverse_law : (0 : F)⁻¹ = 0

--------------------------------------------------------------------------------

/-- A partial order on a type `P` is a binary relation `<=` on `P` (`LE P`)
    that is reflexive, antisymmetric, and transitive. -/
class PartiallyOrdered (P : Type u) extends LE P where
  /-- Every element of a partial order is less than or equal to itself. -/
  reflexive_law (x : P) : x <= x
  /-- If two elements of a partial order are mutually less than or equal to
      each other, then they must coincide. -/
  antisymmetry_law (x y : P) : (x <= y) -> (y <= x) -> (x = y)
  /-- Given three elements of a partial order, if the first two are comparable
      and the last two are comparable in the same direction, then the first and
      last must also be comparable in that direction. -/
  transitive_law (x y z : P) : (x <= y) -> (y <= z) -> (x <= z)

/-- A total order on a type `T` is a partial order (`PartiallyOrdered T`) in
    which any two elements are comparable. -/
class TotallyOrdered (T : Type u) extends PartiallyOrdered T where
  /-- Every pair of elements in a total order is comparable. -/
  totality_law (x y : T) : (x <= y) ∨ (y <= x)

/-- An ordered field is a field with a total order that is compatible with the
    field operations. -/
class OrderedField (F : Type u) extends Field F, TotallyOrdered F where
  /-- In an ordered field, order is preserved under addition. -/
  add_order_law {x y : F} (H : x <= y) (z : F) : x + z <= y + z
  /-- In an ordered field, the product of two nonnegative elements is always
      nonnegative. -/
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

/-- A differential rng is a rng (`Rng R`) with an additional operation called a
    derivation that models the algebraic properties of differentiation. -/
class DifferentialRng (R : Type u) extends Rng R where
  /-- The derivation in a differential rng is denoted by `δ`. -/
  δ : R -> R
  /-- The derivation in a differential rng is additive. -/
  additive_law (x y : R) : δ (x + y) = δ x + δ y
  /-- The derivation in a differential rng satisfies the Leibniz rule. -/
  leibniz_rule (x y : R) : δ (x * y) = δ x * y + x * δ y

namespace DifferentialRng

open AbelianGroup

variable {R : Type u} [DifferentialRng R]

/-- An element of a differential rng is a differential constant if its
    derivative is `0`. -/
def DifferentialConstant (x : R) := δ x = 0

/-- Zero is a differential constant. -/
theorem zero_is_constant : DifferentialConstant (0 : R) :=
  idempotent_is_zero <| calc δ (0 : R) + δ (0 : R)
    _ = δ (0 + 0) := (additive_law 0 0).symm
    _ = δ 0       := zero_law 0 |> congrArg δ

end DifferentialRng

--------------------------------------------------------------------------------

/-- A differential ring is a differential rng (`DifferentialRng R`) that is
    also a ring (`Ring R`). -/
class DifferentialRing (R : Type u) extends DifferentialRng R, Ring R

namespace DifferentialRing

open AbelianGroup
open DifferentialRng
open Ring

variable {R : Type u} [DifferentialRing R]

/-- One is a differential constant. -/
theorem one_is_constant : DifferentialConstant (1 : R) :=
  idempotent_is_zero <| calc δ (1 : R) + δ (1 : R)
    _ = δ 1 * 1 + δ 1     := (right_identity_law (δ 1)).symm
                             |> congrArg (· + δ 1)
    _ = δ 1 * 1 + 1 * δ 1 := (left_identity_law (δ 1)).symm
                             |> congrArg (δ 1 * 1 + ·)
    _ = δ (1 * 1)         := (leibniz_rule 1 1).symm
    _ = δ 1               := left_identity_law 1 |> congrArg δ

end DifferentialRing
