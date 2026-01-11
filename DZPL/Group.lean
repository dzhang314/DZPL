set_option autoImplicit false
set_option linter.all true
universe u

/-- A group is a type `G` with a multiplication operation (`Mul G`) that is
    associative, has an identity (`One G`), and has inverses (`Inv G`). -/
class Group (G : Type u) extends Mul G, One G, Inv G where
  /-- Multiplication in a group is associative. -/
  associative_law (x y z : G) : (x * y) * z = x * (y * z)
  /-- Every group contains a special element, one, denoted by `1`.
      Left multiplication by `1` leaves every element of a group unchanged. -/
  left_identity_law (x : G) : 1 * x = x
  /-- Every element `x` of a group has an inverse, denoted by `x⁻¹`.
      Left multiplying any element of a group by its inverse yields `1`. -/
  left_inverse_law (x : G) : x⁻¹ * x = 1

namespace Group

variable {G : Type u} [Group G]

/-- An element `x` of a group is idempotent if `x * x = x`.
    The only idempotent element in any group is `1`. -/
theorem idempotent_is_identity {x : G} (H : x * x = x) : x = 1 := calc
  x = 1 * x         := (left_identity_law x).symm
  _ = (x⁻¹ * x) * x := congrArg (· * x) (left_inverse_law x).symm
  _ = x⁻¹ * (x * x) := associative_law x⁻¹ x x
  _ = x⁻¹ * x       := congrArg (x⁻¹ * ·) H
  _ = 1             := left_inverse_law x

/-- Right multiplying any element of a group by its inverse yields `1`. -/
theorem right_inverse_law (x : G) : x * x⁻¹ = 1 :=
  idempotent_is_identity <| calc (x * x⁻¹) * (x * x⁻¹)
    _ = x * (x⁻¹ * (x * x⁻¹)) := by rw [associative_law]
    _ = x * ((x⁻¹ * x) * x⁻¹) := by rw [associative_law]
    _ = x * (1 * x⁻¹)         := by rw [left_inverse_law]
    _ = x * x⁻¹               := congrArg (x * ·) (left_identity_law x⁻¹)

/-- Right multiplication by `1` leaves every element of a group unchanged. -/
theorem right_identity_law (x : G) : x * 1 = x := calc x * 1
  _ = x * (x⁻¹ * x) := by rw [left_inverse_law]
  _ = (x * x⁻¹) * x := by rw [associative_law]
  _ = 1 * x         := by rw [right_inverse_law]
  _ = x             := left_identity_law x

theorem product_one_implies_inverse {x y : G} (H : x * y = 1) : x⁻¹ = y :=
  calc x⁻¹
    _ = x⁻¹ * 1       := by rw [right_identity_law]
    _ = x⁻¹ * (x * y) := by rw [H]
    _ = (x⁻¹ * x) * y := by rw [associative_law]
    _ = 1 * y         := by rw [left_inverse_law]
    _ = y             := left_identity_law y

/-- In a group, inverting twice yields the original element. -/
theorem inversion_is_involution (x : G) : (x⁻¹)⁻¹ = x :=
  product_one_implies_inverse (left_inverse_law x)

/-- In a group, the inverse of a product is the product of the inverses in
    reverse order. -/
theorem inverse_of_product (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  product_one_implies_inverse <| calc (x * y) * (y⁻¹ * x⁻¹)
    _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [associative_law]
    _ = x * ((y * y⁻¹) * x⁻¹) := by rw [associative_law]
    _ = x * (1 * x⁻¹)         := by rw [right_inverse_law]
    _ = x * x⁻¹               := by rw [left_identity_law]
    _ = 1                     := right_inverse_law x

end Group
