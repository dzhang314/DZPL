import DZPL.Ring
set_option autoImplicit false
set_option linter.all true
universe u

/-- A division ring is a ring (`Ring R`) in which every nonzero element has a
    multiplicative inverse (`Inv R`). -/
class DivisionRing (D : Type u) extends Ring D, Inv D where
  /-- Every nonzero element of a division ring has a multiplicative inverse. -/
  left_inverse_law (x : D) : (x = (0 : D)) ∨ (x⁻¹ * x = (1 : D))
  /-- In a division ring, the inverse of `0` is defined to be `0`. -/
  zero_inverse_law : (0 : D)⁻¹ = (0 : D)

namespace DivisionRing

open Ring
open Rng

variable {D : Type u} [DivisionRing D]

/-- In a division ring, if a product is `0`, then a factor must be `0`. -/
theorem zero_product_law {x y : D} (H : x * y = (0 : D)) :
    (x = (0 : D)) ∨ (y = (0 : D)) :=
  match left_inverse_law x with
  | Or.inl (Hx : x = (0 : D))       => Or.inl Hx
  | Or.inr (Hx : x⁻¹ * x = (1 : D)) => Or.inr <| calc y
    _ = (1 : D) * y   := left_identity_law y |> Eq.symm
    _ = (x⁻¹ * x) * y := Hx |> Eq.symm |> congrArg (· * y)
    _ = x⁻¹ * (x * y) := mul_associative_law x⁻¹ x y
    _ = x⁻¹ * (0 : D) := H |> congrArg (x⁻¹ * ·)
    _ = (0 : D)       := mul_zero_right x⁻¹

private theorem zero_ring_lemma {x : D} (H : (0 : D) * x = (1 : D)) (y z : D) :
    y = z :=
  have zero_ring : ZeroRing D := zero_ring_law (mul_zero_left x ▸ H)
  zero_ring z ▸ zero_ring y

/-- The only element of a division ring whose inverse is `0` is `0` itself. -/
theorem inverse_zero_implies_zero {x : D} (H : x⁻¹ = (0 : D)) : x = (0 : D) :=
  match left_inverse_law x with
  | Or.inl (Hx : x = (0 : D)) => Hx
  | Or.inr (Hx : x⁻¹ * x = (1 : D)) => zero_ring_lemma (H ▸ Hx) x (0 : D)

/-- Every nonzero element of a division ring has a multiplicative inverse. -/
theorem right_inverse_law (x : D) : (x = (0 : D)) ∨ (x * x⁻¹ = (1 : D)) :=
  match left_inverse_law x, left_inverse_law x⁻¹ with
  | Or.inl Hx, _          => Or.inl Hx
  | _,         Or.inl Hxi => Or.inl (inverse_zero_implies_zero Hxi)
  | Or.inr Hx, Or.inr Hxi => Or.inr <| calc x * x⁻¹
    _ = (1 : D) * (x * x⁻¹)         := left_identity_law (x * x⁻¹) |> Eq.symm
    _ = ((x⁻¹)⁻¹ * x⁻¹) * (x * x⁻¹) := Hxi |> Eq.symm
                                       |> congrArg (· * (x * x⁻¹))
    _ = (x⁻¹)⁻¹ * (x⁻¹ * (x * x⁻¹)) := mul_associative_law (x⁻¹)⁻¹ x⁻¹ (x * x⁻¹)
    _ = (x⁻¹)⁻¹ * ((x⁻¹ * x) * x⁻¹) := mul_associative_law x⁻¹ x x⁻¹
                                       |> Eq.symm |> congrArg ((x⁻¹)⁻¹ * ·)
    _ = (x⁻¹)⁻¹ * ((1 : D) * x⁻¹)   := Hx |> congrArg (· * x⁻¹)
                                       |> congrArg ((x⁻¹)⁻¹ * ·)
    _ = (x⁻¹)⁻¹ * x⁻¹               := left_identity_law x⁻¹
                                       |> congrArg ((x⁻¹)⁻¹ * ·)
    _ = (1 : D)                     := Hxi

/-- In a division ring, if the product of two elements is `1 : D`, then one is
    the inverse of the other. -/
theorem product_one_implies_inverse {x y : D} (H : x * y = (1 : D)) : x⁻¹ = y :=
  match left_inverse_law x with
  | Or.inl (Hx : x = (0 : D)) => zero_ring_lemma (Hx ▸ H) x⁻¹ y
  | Or.inr (Hx : x⁻¹ * x = (1 : D)) => calc x⁻¹
    _ = x⁻¹ * (1 : D) := right_identity_law x⁻¹ |> Eq.symm
    _ = x⁻¹ * (x * y) := H |> Eq.symm |> congrArg (x⁻¹ * ·)
    _ = (x⁻¹ * x) * y := mul_associative_law x⁻¹ x y |> Eq.symm
    _ = (1 : D) * y   := Hx |> congrArg (· * y)
    _ = y             := left_identity_law y

/-- In a division ring, the inverse of a product is the product of the inverses
    in reverse order. -/
theorem inverse_of_product (x y : D) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  match right_inverse_law x, right_inverse_law y with
  | Or.inl Hx, _         => calc (x * y)⁻¹
    _ = ((0 : D) * y)⁻¹ := Hx |> congrArg (· * y) |> congrArg (·⁻¹)
    _ = (0 : D)⁻¹       := mul_zero_left y |> congrArg (·⁻¹)
    _ = (0 : D)         := zero_inverse_law
    _ = y⁻¹ * (0 : D)   := mul_zero_right y⁻¹ |> Eq.symm
    _ = y⁻¹ * (0 : D)⁻¹ := zero_inverse_law |> Eq.symm |> congrArg (y⁻¹ * ·)
    _ = y⁻¹ * x⁻¹       := Hx |> Eq.symm |> congrArg (y⁻¹ * ·⁻¹)
  | _,         Or.inl Hy => calc (x * y)⁻¹
    _ = (x * (0 : D))⁻¹ := Hy |> congrArg (x * ·) |> congrArg (·⁻¹)
    _ = (0 : D)⁻¹       := mul_zero_right x |> congrArg (·⁻¹)
    _ = (0 : D)         := zero_inverse_law
    _ = (0 : D) * x⁻¹   := mul_zero_left x⁻¹ |> Eq.symm
    _ = (0 : D)⁻¹ * x⁻¹ := zero_inverse_law |> Eq.symm |> congrArg (· * x⁻¹)
    _ = y⁻¹ * x⁻¹       := Hy |> Eq.symm |> congrArg (·⁻¹ * x⁻¹)
  | Or.inr Hx, Or.inr Hy =>
    product_one_implies_inverse <| calc (x * y) * (y⁻¹ * x⁻¹)
      _ = x * (y * (y⁻¹ * x⁻¹))   := mul_associative_law x y (y⁻¹ * x⁻¹)
      _ = x * ((y * y⁻¹) * x⁻¹)   := mul_associative_law y y⁻¹ x⁻¹
                                     |> Eq.symm |> congrArg (x * ·)
      _ = x * ((1 : D) * x⁻¹)     := Hy
                                     |> congrArg (· * x⁻¹) |> congrArg (x * ·)
      _ = x * x⁻¹                 := left_identity_law x⁻¹ |> congrArg (x * ·)
      _ = (1 : D)                 := Hx

end DivisionRing
