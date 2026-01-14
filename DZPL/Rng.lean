import DZPL.AbelianGroup
set_option autoImplicit false
set_option linter.all true
universe u

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

namespace Rng

open AbelianGroup

variable {R : Type u} [Rng R]

/-- In a rng, left multiplication by `0` yields `0`. -/
theorem mul_zero_left (x : R) : (0 : R) * x = (0 : R) :=
  idempotent_is_zero <| calc (0 : R) * x + (0 : R) * x
    _ = ((0 : R) + (0 : R)) * x := right_distributive_law (0 : R) (0 : R) x
                                   |> Eq.symm
    _ = (0 : R) * x             := zero_law (0 : R) |> congrArg (· * x)

/-- In a rng, right multiplication by `0` yields `0`. -/
theorem mul_zero_right (x : R) : x * (0 : R) = (0 : R) :=
  idempotent_is_zero <| calc x * (0 : R) + x * (0 : R)
    _ = x * ((0 : R) + (0 : R)) := left_distributive_law x (0 : R) (0 : R)
                                   |> Eq.symm
    _ = x * (0 : R)             := zero_law (0 : R) |> congrArg (x * ·)

/-- In a rng, a product with a negative on the left is the negative of the
    product. -/
theorem mul_neg_left (x y : R) : -x * y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + -x * y
    _ = (x + -x) * y := right_distributive_law x (-x) y |> Eq.symm
    _ = (0 : R) * y  := negative_law x |> congrArg (· * y)
    _ = (0 : R)      := mul_zero_left y

/-- In a rng, a product with a negative on the right is the negative of the
    product. -/
theorem mul_neg_right (x y : R) : x * -y = -(x * y) :=
  Eq.symm <| sum_zero_implies_negative <| calc x * y + x * -y
    _ = x * (y + -y) := left_distributive_law x y (-y) |> Eq.symm
    _ = x * (0 : R)  := negative_law y |> congrArg (x * ·)
    _ = (0 : R)      := mul_zero_right x

/-- In a rng, a product of two negatives is the product of the elements. -/
theorem product_of_negatives (x y : R) : (-x) * (-y) = x * y :=
  calc (-x) * (-y)
    _ = -(x * -y)   := mul_neg_left x (-y)
    _ = -(-(x * y)) := mul_neg_right x y |> congrArg (-·)
    _ = x * y       := negation_is_involution (x * y)

end Rng
