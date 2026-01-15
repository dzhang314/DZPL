set_option autoImplicit false
set_option linter.all true
universe u

/-- A group is a type `G` with a multiplication operation (`Mul G`) that is
    associative, has an identity (`One G`), and admits inverses (`Inv G`). -/
class Group (G : Type u) extends Mul G, One G, Inv G where
  /-- Multiplication in a group is associative. -/
  associative_law (x y z : G) : (x * y) * z = x * (y * z)
  /-- Every group contains a special element, one, denoted by `1`.
      Left multiplication by `1` leaves every element of a group unchanged. -/
  left_identity_law (x : G) : (1 : G) * x = x
  /-- Every element `x` of a group has an inverse, denoted by `x⁻¹`.
      Left multiplying any element of a group by its inverse yields `1`. -/
  left_inverse_law (x : G) : x⁻¹ * x = (1 : G)

namespace Group

variable {G : Type u} [Group G]

/-- An element `x` of a group is idempotent if `x * x = x`.
    The only idempotent element in any group is `1 : G`. -/
theorem idempotent_is_identity {x : G} (H : x * x = x) : x = (1 : G) := calc x
  _ = (1 : G) * x   := left_identity_law x |> Eq.symm
  _ = (x⁻¹ * x) * x := left_inverse_law x |> Eq.symm |> congrArg (· * x)
  _ = x⁻¹ * (x * x) := associative_law x⁻¹ x x
  _ = x⁻¹ * x       := H |> congrArg (x⁻¹ * ·)
  _ = (1 : G)       := left_inverse_law x

/-- Right multiplying any element of a group by its inverse yields `1`. -/
theorem right_inverse_law (x : G) : x * x⁻¹ = (1 : G) :=
  idempotent_is_identity <| calc (x * x⁻¹) * (x * x⁻¹)
    _ = x * (x⁻¹ * (x * x⁻¹)) := associative_law x x⁻¹ (x * x⁻¹)
    _ = x * ((x⁻¹ * x) * x⁻¹) := associative_law x⁻¹ x x⁻¹ |> Eq.symm
                                 |> congrArg (x * ·)
    _ = x * ((1 : G) * x⁻¹)   := left_inverse_law x
                                 |> congrArg (· * x⁻¹) |> congrArg (x * ·)
    _ = x * x⁻¹               := left_identity_law x⁻¹ |> congrArg (x * ·)

/-- Right multiplication by `1` leaves every element of a group unchanged. -/
theorem right_identity_law (x : G) : x * (1 : G) = x := calc x * (1 : G)
  _ = x * (x⁻¹ * x) := left_inverse_law x |> Eq.symm |> congrArg (x * ·)
  _ = (x * x⁻¹) * x := associative_law x x⁻¹ x |> Eq.symm
  _ = (1 : G) * x   := right_inverse_law x |> congrArg (· * x)
  _ = x             := left_identity_law x

/-- In a group, if the product of two elements is `1 : G`, then one is the
    inverse of the other. -/
theorem product_one_implies_inverse {x y : G} (H : x * y = (1 : G)) : x⁻¹ = y :=
  calc x⁻¹
    _ = x⁻¹ * (1 : G) := right_identity_law x⁻¹ |> Eq.symm
    _ = x⁻¹ * (x * y) := H |> Eq.symm |> congrArg (x⁻¹ * ·)
    _ = (x⁻¹ * x) * y := associative_law x⁻¹ x y |> Eq.symm
    _ = (1 : G) * y   := left_inverse_law x |> congrArg (· * y)
    _ = y             := left_identity_law y

/-- In a group, inverting twice yields the original element. -/
theorem inversion_is_involution (x : G) : (x⁻¹)⁻¹ = x :=
  product_one_implies_inverse (left_inverse_law x)

/-- In a group, the inverse of a product is the product of the inverses in
    reverse order. -/
theorem inverse_of_product (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  product_one_implies_inverse <| calc (x * y) * (y⁻¹ * x⁻¹)
    _ = x * (y * (y⁻¹ * x⁻¹)) := associative_law x y (y⁻¹ * x⁻¹)
    _ = x * ((y * y⁻¹) * x⁻¹) := associative_law y y⁻¹ x⁻¹ |> Eq.symm
                                 |> congrArg (x * ·)
    _ = x * ((1 : G) * x⁻¹)   := right_inverse_law y
                                 |> congrArg (· * x⁻¹) |> congrArg (x * ·)
    _ = x * x⁻¹               := left_identity_law x⁻¹ |> congrArg (x * ·)
    _ = (1 : G)               := right_inverse_law x

end Group

namespace Group

/-- In a group, the inverse of `1 : G` is `1 : G`. --/
theorem inverse_of_one (G : Type u) [Group G] : (1 : G)⁻¹ = (1 : G) :=
  product_one_implies_inverse (left_identity_law (1 : G))

end Group
