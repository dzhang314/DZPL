import DZPL.AxiomFree
import DZPL.Rng
set_option autoImplicit false
set_option DZPL.axiomFree true
set_option linter.all true
universe u

/-- A differential rng is a rng (`Rng R`) with an additional operation called a
    derivation that models the algebraic properties of differentiation. -/
class DifferentialRng (R : Type u) extends Rng R where
  /-- The derivation in a differential rng is denoted by `δ`. -/
  δ : R -> R
  /-- The derivation in a differential rng is additive. -/
  additive_law (x y : R) : δ (x + y) = δ x + δ y
  /-- The derivation in a differential rng satisfies the Leibniz rule. -/
  product_law (x y : R) : δ (x * y) = δ x * y + x * δ y

namespace DifferentialRng

open AbelianGroup

variable {R : Type u} [DifferentialRng R]

/-- An element of a differential rng is a constant if its derivative is `0`. -/
def Constant (x : R) := δ x = (0 : R)

/-- `0 : R` is a constant in every differential rng. -/
theorem zero_is_constant : Constant (0 : R) :=
  idempotent_is_zero <| calc δ (0 : R) + δ (0 : R)
    _ = δ ((0 : R) + (0 : R)) := additive_law (0 : R) (0 : R) |> Eq.symm
    _ = δ (0 : R)             := zero_law (0 : R) |> congrArg δ

end DifferentialRng
