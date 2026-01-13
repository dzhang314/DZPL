import DZPL.Rng
set_option autoImplicit false
set_option linter.all true
universe u

/-- A ring is a rng (`Rng R`) with a two-sided multiplicative identity element
    (`One R`). -/
class Ring (R : Type u) extends Rng R, One R where
  /-- Left multiplication by `1` leaves every element of a ring unchanged. -/
  left_identity_law (x : R) : 1 * x = x
  /-- Right multiplication by `1` leaves every element of a ring unchanged. -/
  right_identity_law (x : R) : x * 1 = x

/-- A zero ring is a ring in which `0 : R` is the only element. -/
def ZeroRing (R : Type u) [Ring R] : Prop := ∀ x : R, x = 0

namespace Ring

open Rng

variable {R : Type u} [Ring R]

/-- If `(0 : R) = (1 : R)` in a ring `R`, then `R` is a zero ring. -/
theorem zero_ring_law : (0 : R) = (1 : R) -> ZeroRing R :=
  fun (H : 0 = 1) (x : R) => calc x
    _ = 1 * x := left_identity_law x |> Eq.symm
    _ = 0 * x := H |> Eq.symm |> congrArg (· * x)
    _ = 0     := mul_zero_left x

end Ring

namespace Ring

open AbelianGroup
open Rng

/-- Embed a natural number into a ring `R` by repeatedly adding `1 : R`. -/
def embed_nat (R : Type u) [Ring R] : Nat → R
  | Nat.zero   => (0 : R)
  | Nat.succ n => (embed_nat R n) + (1 : R)

instance (priority := low) (R : Type u) [Ring R] (n : Nat) : OfNat R n where
  ofNat := embed_nat R n

/-- Embedding the natural number `0 : Nat` into a ring `R` yields `0 : R`. -/
theorem embed_nat_zero (R : Type u) [Ring R] : embed_nat R 0 = (0 : R) := rfl

/-- Embedding the natural number `1 : Nat` into a ring `R` yields `1 : R`. -/
theorem embed_nat_one (R : Type u) [Ring R] : embed_nat R 1 = (1 : R) :=
  calc embed_nat R 1
    _ = (0 : R) + (1 : R) := rfl
    _ = (1 : R) + (0 : R) := commutative_law (0 : R) (1 : R)
    _ = (1 : R)           := zero_law (1 : R)

/-- Embedding natural numbers into a ring preserves addition. -/
theorem embed_nat_add (R : Type u) [Ring R] (m n : Nat) :
  embed_nat R (m + n) = (embed_nat R m) + (embed_nat R n) :=
  Nat.recOn n
    (calc embed_nat R (m + 0)
      _ = embed_nat R m
          := rfl
      _ = embed_nat R m + (0 : R)
          := zero_law (embed_nat R m) |> Eq.symm
      _ = embed_nat R m + embed_nat R 0
          := rfl)
    (fun (k : Nat)
         (IH : embed_nat R (m + k) = embed_nat R m + embed_nat R k) =>
      calc embed_nat R (m + k + 1)
        _ = embed_nat R (m + k) + (1 : R)
            := rfl
        _ = (embed_nat R m + embed_nat R k) + (1 : R)
            := IH |> congrArg (· + (1 : R))
        _ = embed_nat R m + (embed_nat R k + (1 : R))
            := associative_law (embed_nat R m) (embed_nat R k) (1 : R)
        _ = embed_nat R m + embed_nat R (k + 1)
            := rfl)

/-- Embedding natural numbers into a ring preserves multiplication. --/
theorem embed_nat_mul (R : Type u) [Ring R] (m n : Nat) :
  embed_nat R (m * n) = embed_nat R m * embed_nat R n :=
  Nat.recOn n
    (calc embed_nat R (m * 0)
      _ = (0 : R)
          := rfl
      _ = embed_nat R m * (0 : R)
          := mul_zero_right (embed_nat R m) |> Eq.symm
      _ = embed_nat R m * embed_nat R 0
          := rfl)
    (fun (k : Nat)
         (IH : embed_nat R (m * k) = embed_nat R m * embed_nat R k) =>
      calc embed_nat R (m * (k + 1))
        _ = embed_nat R (m * k + m)
            := rfl
        _ = embed_nat R (m * k) + embed_nat R m
            := embed_nat_add R (m * k) m
        _ = embed_nat R m * embed_nat R k + embed_nat R m
            := IH |> congrArg (· + embed_nat R m)
        _ = embed_nat R m * embed_nat R k + embed_nat R m * (1 : R)
            := right_identity_law (embed_nat R m)
               |> Eq.symm |> congrArg (embed_nat R m * embed_nat R k + ·)
        _ = embed_nat R m * (embed_nat R k + (1 : R))
            := left_distributive_law (embed_nat R m) (embed_nat R k) (1 : R)
               |> Eq.symm
        _ = embed_nat R m * embed_nat R (k + 1)
            := rfl)

end Ring

namespace Ring

/-- Natural number `n` is the characteristic of ring `R` if `n` is the smallest
    positive natural number such that `embed_nat R n = 0`, or `n = 0` if no
    such positive natural number exists. -/
def HasCharacteristic (R : Type u) [Ring R] (n : Nat) : Prop :=
  (n = 0 ∧ ∀ m : Nat, m > 0 -> embed_nat R m ≠ 0) ∨
  (n > 0 ∧ embed_nat R n = 0 ∧ ∀ m : Nat, 0 < m ∧ m < n -> embed_nat R m ≠ 0)

end Ring
