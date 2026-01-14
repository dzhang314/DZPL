import DZPL.Rng
import DZPL.TotallyOrdered
set_option autoImplicit false
set_option linter.all true
universe u

/-- An ordered rng is a rng (`Rng R`) with a total order (`TotallyOrdered R`)
    that is compatible with addition and multiplication. -/
class OrderedRng (R : Type u) extends Rng R, TotallyOrdered R where
  /-- An inequality in an ordered rng remains true when the same element is
      added to both sides. -/
  add_order_law {x y : R} (z : R) : (x ≤ y) -> (x + z ≤ y + z)
  /-- The product of two nonnegative elements in an ordered rng is itself
      nonnegative. -/
  mul_order_law {x y : R} : ((0 : R) ≤ x) -> ((0 : R) ≤ y) -> ((0 : R) ≤ x * y)

namespace OrderedRng

open AbelianGroup
open Rng
open TotallyOrdered

variable {R : Type u} [OrderedRng R]

/-- A strict inequality in an ordered rng remains true when the same element is
    added to both sides. -/
theorem strict_add_order_law {x y : R} (z : R) (H : x < y) : (x + z < y + z) :=
  -- To obtain `x + z < y + z`, we prove `x + z ≤ y + z` and `x + z ≠ y + z`.
  have le : x + z ≤ y + z := add_order_law z (And.left H)
  -- We assume `x + z = y + z` and derive a contradiction.
  have ne : x + z ≠ y + z := fun (Heq : x + z = y + z) =>
    have eq : x = y := calc x
      _ = x + (0 : R)  := zero_law x |> Eq.symm
      _ = x + (z + -z) := negative_law z |> Eq.symm |> congrArg (x + ·)
      _ = (x + z) + -z := associative_law x z (-z) |> Eq.symm
      _ = (y + z) + -z := Heq |> congrArg (· + -z)
      _ = y + (z + -z) := associative_law y z (-z)
      _ = y + (0 : R)  := negative_law z |> congrArg (y + ·)
      _ = y            := zero_law y
    (And.right H) eq
  And.intro le ne

/-- In an ordered rng, the square of any element is nonnegative. -/
theorem square_is_nonnegative (x : R) : (0 : R) ≤ x * x :=
  -- By totality, either `0 ≤ x` or `x ≤ 0`.
  match totality_law (0 : R) x with
  -- If `0 ≤ x`, apply `mul_order_law` directly.
  | Or.inl (H : (0 : R) ≤ x) => mul_order_law H H
  -- If `x ≤ 0`, apply `mul_order_law` with `product_of_negatives`.
  | Or.inr (H : x ≤ (0 : R)) =>
    have neg : (0 : R) ≤ -x := calc (0 : R)
      _ = x + -x       := negative_law x |> Eq.symm
      _ ≤ (0 : R) + -x := add_order_law (-x) H
      _ = -x + (0 : R) := commutative_law (0 : R) (-x)
      _ = -x           := zero_law (-x)
    product_of_negatives x x ▸ mul_order_law neg neg

end OrderedRng
