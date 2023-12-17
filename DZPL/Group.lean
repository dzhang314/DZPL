import DZPL.Notation

set_option autoImplicit false

universe u

class Group (G : Type u) extends Mul G, HasOne G, HasInv G where
  associative_law (x y z : G) : (x * y) * z = x * (y * z)
  left_identity_law (x : G) : 1 * x = x
  left_inverse_law (x : G) : x⁻¹ * x = 1

namespace Group

variable {G : Type u} [Group G]

@[simp]
example (x : G) : 1 * x = x := left_identity_law x

@[simp]
example (x : G) : x⁻¹ * x = 1 := left_inverse_law x

theorem idempotent_is_identity {x : G} (H : x * x = x) : x = 1 := calc
  x = 1 * x         := by rw [left_identity_law]
  _ = (x⁻¹ * x) * x := by rw [left_inverse_law]
  _ = x⁻¹ * (x * x) := by rw [associative_law]
  _ = x⁻¹ * x       := by rw [H]
  _ = 1             := by rw [left_inverse_law]

@[simp]
theorem right_inverse_law (x : G) : x * x⁻¹ = 1 :=
  idempotent_is_identity <| calc (x * x⁻¹) * (x * x⁻¹)
    _ = x * (x⁻¹ * (x * x⁻¹)) := by rw [associative_law]
    _ = x * ((x⁻¹ * x) * x⁻¹) := by rw [associative_law]
    _ = x * (1 * x⁻¹)         := by rw [left_inverse_law]
    _ = x * x⁻¹               := by rw [left_identity_law]

@[simp]
theorem right_identity_law (x : G) : x * 1 = x := calc x * 1
  _ = x * (x⁻¹ * x) := by rw [left_inverse_law]
  _ = (x * x⁻¹) * x := by rw [associative_law]
  _ = 1 * x         := by rw [right_inverse_law]
  _ = x             := by rw [left_identity_law]

theorem product_one_implies_inverse {x y : G} (H : x * y = 1) : x⁻¹ = y :=
  calc x⁻¹
    _ = x⁻¹ * 1       := by rw [right_identity_law]
    _ = x⁻¹ * (x * y) := by rw [H]
    _ = (x⁻¹ * x) * y := by rw [associative_law]
    _ = 1 * y         := by rw [left_inverse_law]
    _ = y             := by rw [left_identity_law]

@[simp]
theorem inverse_of_product (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  product_one_implies_inverse <| calc (x * y) * (y⁻¹ * x⁻¹)
    _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [associative_law]
    _ = x * ((y * y⁻¹) * x⁻¹) := by rw [associative_law]
    _ = x * (1 * x⁻¹)         := by rw [right_inverse_law]
    _ = x * x⁻¹               := by rw [left_identity_law]
    _ = 1                     := by rw [right_inverse_law]

end Group
