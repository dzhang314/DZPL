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

/-- In a rng, a product of two negatives is the product of the elements. -/
theorem neg_neg_mul_law (x y : R) : (-x) * (-y) = x * y := calc (-x) * (-y)
  _ = -(x * -y)   := left_neg_mul_law x (-y)
  _ = -(-(x * y)) := right_neg_mul_law x y |> congrArg (-·)
  _ = x * y       := negation_is_involution (x * y)

end Rng
