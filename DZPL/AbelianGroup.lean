set_option autoImplicit false
set_option linter.all true
universe u

/-- An abelian group is a type `G` with an addition operation (`Add G`) that is
    commutative, associative, has an identity (`Zero G`), and has inverses
    (`Neg G`). -/
class AbelianGroup (G : Type u) extends Add G, Zero G, Neg G where
  /-- Addition in an abelian group is commutative. -/
  commutative_law (x y : G) : x + y = y + x
  /-- Addition in an abelian group is associative. -/
  associative_law (x y z : G) : (x + y) + z = x + (y + z)
  /-- Every abelian group contains a special element, zero, denoted by `0`.
      Adding `0` leaves every element of an abelian group unchanged. -/
  zero_law (x : G) : x + 0 = x
  /-- Every element `x` of an abelian group has a negative, denoted by `-x`.
      Adding any element of an abelian group to its negative yields `0`. -/
  negative_law (x : G) : x + -x = 0

namespace AbelianGroup

variable {G : Type u} [AbelianGroup G]

/-- An element `x` of an abelian group is idempotent if `x + x = x`.
    The only idempotent element in any abelian group is `0`. -/
theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := calc x
  _ = x + 0        := (zero_law x).symm
  _ = x + (x + -x) := (negative_law x).symm |> congrArg (x + ·)
  _ = (x + x) + -x := (associative_law x x (-x)).symm
  _ = x + -x       := H |> congrArg (· + (-x))
  _ = 0            := negative_law x

theorem sum_zero_implies_negative {x y : G} (H : x + y = 0) : -x = y := calc -x
  _ = -x + 0       := (zero_law (-x)).symm
  _ = -x + (x + y) := H.symm |> congrArg (-x + ·)
  _ = (-x + x) + y := (associative_law (-x) x y).symm
  _ = (x + -x) + y := commutative_law (-x) x |> congrArg (· + y)
  _ = 0 + y        := negative_law x |> congrArg (· + y)
  _ = y + 0        := commutative_law 0 y
  _ = y            := zero_law y

/-- In an abelian group, negating twice yields the original element. -/
theorem negation_is_involution (x : G) : -(-x) = x :=
  sum_zero_implies_negative <| calc -x + x
    _ = x + -x := commutative_law (-x) x
    _ = 0      := negative_law x

/-- In an abelian group, the negative of a sum is the sum of the negatives. -/
theorem negative_of_sum (x y : G) : -(x + y) = -x + -y :=
  sum_zero_implies_negative <| calc (x + y) + (-x + -y)
    _ = x + (y + (-x + -y)) := associative_law x y (-x + -y)
    _ = x + (y + (-y + -x)) := commutative_law (-x) (-y)
                               |> congrArg (y + ·) |> congrArg (x + ·)
    _ = x + ((y + -y) + -x) := (associative_law y (-y) (-x)).symm
                               |> congrArg (x + ·)
    _ = x + (0 + -x)        := negative_law y
                               |> congrArg (· + -x) |> congrArg (x + ·)
    _ = x + (-x + 0)        := commutative_law 0 (-x) |> congrArg (x + ·)
    _ = x + -x              := zero_law (-x) |> congrArg (x + ·)
    _ = 0                   := negative_law x

end AbelianGroup
