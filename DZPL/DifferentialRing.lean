import DZPL.DifferentialRng
import DZPL.Ring
set_option autoImplicit false
set_option linter.all true
universe u

/-- A differential ring is a differential rng (`DifferentialRng R`) that is
    also a ring (`Ring R`), i.e., has a multiplicative identity element. -/
class DifferentialRing (R : Type u) extends DifferentialRng R, Ring R

namespace DifferentialRing

open AbelianGroup
open DifferentialRng
open Ring

variable {R : Type u} [DifferentialRing R]

/-- `1` is a constant in every differential ring. -/
theorem one_is_constant : Constant (1 : R) :=
  idempotent_is_zero <| calc δ (1 : R) + δ (1 : R)
    _ = δ 1 * 1 + δ 1     := right_identity_law (δ 1) |> Eq.symm
                             |> congrArg (· + δ 1)
    _ = δ 1 * 1 + 1 * δ 1 := left_identity_law (δ 1) |> Eq.symm
                             |> congrArg (δ 1 * 1 + ·)
    _ = δ (1 * 1)         := product_law 1 1 |> Eq.symm
    _ = δ 1               := left_identity_law 1 |> congrArg δ

end DifferentialRing
