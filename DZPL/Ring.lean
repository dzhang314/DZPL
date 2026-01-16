import DZPL.AxiomFree
import DZPL.Rng
set_option autoImplicit false
set_option DZPL.axiomFree true
set_option linter.all true
universe u

/-- A ring is a rng (`Rng R`) with a two-sided multiplicative identity element
    (`One R`). -/
class Ring (R : Type u) extends Rng R, One R where
  /-- Left multiplication by `1` leaves every element of a ring unchanged. -/
  left_identity_law (x : R) : (1 : R) * x = x
  /-- Right multiplication by `1` leaves every element of a ring unchanged. -/
  right_identity_law (x : R) : x * (1 : R) = x

/-- A zero ring is a ring in which `0 : R` is the only element. -/
def ZeroRing (R : Type u) [Ring R] : Prop := ∀ x : R, x = (0 : R)

namespace Ring

open Rng

variable {R : Type u} [Ring R]

/-- If `(0 : R) = (1 : R)` in a ring `R`, then `R` is a zero ring. -/
theorem zero_ring_law : (0 : R) = (1 : R) -> ZeroRing R :=
  fun (H : (0 : R) = (1 : R)) (x : R) => calc x
    _ = (1 : R) * x := left_identity_law x |> Eq.symm
    _ = (0 : R) * x := H |> Eq.symm |> congrArg (· * x)
    _ = (0 : R)     := mul_zero_left x

end Ring

namespace Ring

open Nat
open Int
open AbelianGroup
open Rng

/-- Embed a natural number into a ring `R` by repeatedly adding `1 : R`. -/
def embed_nat (R : Type u) [Ring R] : Nat -> R
  | zero   => (0 : R)
  | succ n => (embed_nat R n) + (1 : R)

instance (priority := low) (R : Type u) [Ring R] (n : Nat) : OfNat R n where
  ofNat := embed_nat R n

/-- Embedding the natural number `0` into a ring `R` yields `0 : R`. -/
theorem embed_nat_zero (R : Type u) [Ring R] : embed_nat R 0 = (0 : R) := rfl

/-- Embedding the natural number `1` into a ring `R` yields `1 : R`. -/
theorem embed_nat_one (R : Type u) [Ring R] : embed_nat R 1 = (1 : R) :=
  calc embed_nat R 1
    _ = (0 : R) + (1 : R) := rfl
    _ = (1 : R) + (0 : R) := commutative_law (0 : R) (1 : R)
    _ = (1 : R)           := zero_law (1 : R)

/-- Embedding natural numbers into a ring preserves addition. -/
theorem embed_nat_add (R : Type u) [Ring R] (m n : Nat) :
    embed_nat R (m + n) = embed_nat R m + embed_nat R n :=
  match n with
  | zero   => calc embed_nat R (m + zero)
    _ = embed_nat R m                    := rfl
    _ = embed_nat R m + (0 : R)          := zero_law (embed_nat R m) |> Eq.symm
    _ = embed_nat R m + embed_nat R zero := rfl
  | succ k => calc embed_nat R (m + (succ k))
    _ = embed_nat R (succ (m + k))
        := rfl
    _ = embed_nat R (m + k) + (1 : R)
        := rfl
    _ = (embed_nat R m + embed_nat R k) + (1 : R)
        := embed_nat_add R m k |> congrArg (· + (1 : R))
    _ = embed_nat R m + (embed_nat R k + (1 : R))
        := associative_law (embed_nat R m) (embed_nat R k) (1 : R)
    _ = embed_nat R m + embed_nat R (succ k)
        := rfl

private theorem embed_nat_sub_helper
    (R : Type u) [Ring R] {m n : Nat} (H : m ≤ n) :
    embed_nat R (n - m) + embed_nat R m = embed_nat R n :=
  match m, n with
  | zero,   n      => zero_law (embed_nat R n)
  | succ a, succ b => calc embed_nat R (succ b - succ a) + embed_nat R (succ a)
    _ = embed_nat R (b - a) + embed_nat R (succ a)
        := Nat.succ_sub_succ_eq_sub b a
           |> congrArg (embed_nat R) |> congrArg (· + embed_nat R (succ a))
    _ = embed_nat R (b - a) + (embed_nat R a + (1 : R))
        := rfl
    _ = (embed_nat R (b - a) + embed_nat R a) + (1 : R)
        := associative_law (embed_nat R (b - a)) (embed_nat R a) (1 : R)
           |> Eq.symm
    _ = embed_nat R b + (1 : R)
        := embed_nat_sub_helper R (Nat.le_of_succ_le_succ H)
           |> congrArg (· + (1 : R))
    _ = embed_nat R (succ b)
        := rfl

/-- Embedding natural numbers into a ring preserves subtraction. -/
theorem embed_nat_sub (R : Type u) [Ring R] {m n : Nat} (H : m ≤ n) :
    embed_nat R (n - m) = embed_nat R n + -(embed_nat R m) :=
  calc embed_nat R (n - m)
    _ = embed_nat R (n - m) + (0 : R)
        := zero_law (embed_nat R (n - m)) |> Eq.symm
    _ = embed_nat R (n - m) + (embed_nat R m + -(embed_nat R m))
        := negative_law (embed_nat R m)
           |> Eq.symm |> congrArg (embed_nat R (n - m) + ·)
    _ = (embed_nat R (n - m) + embed_nat R m) + -(embed_nat R m)
        := associative_law
             (embed_nat R (n - m)) (embed_nat R m) (-(embed_nat R m))
           |> Eq.symm
    _ = embed_nat R n + -(embed_nat R m)
        := embed_nat_sub_helper R H |> congrArg (· + -(embed_nat R m))

/-- Embedding natural numbers into a ring preserves multiplication. -/
theorem embed_nat_mul (R : Type u) [Ring R] (m n : Nat) :
    embed_nat R (m * n) = embed_nat R m * embed_nat R n :=
  match n with
  | zero   => calc embed_nat R (m * zero)
    _ = embed_nat R zero
        := rfl
    _ = (0 : R)
        := rfl
    _ = embed_nat R m * (0 : R)
        := mul_zero_right (embed_nat R m) |> Eq.symm
    _ = embed_nat R m * embed_nat R zero
        := rfl
  | succ k => calc embed_nat R (m * (succ k))
    _ = embed_nat R (m * k + m)
        := rfl
    _ = embed_nat R (m * k) + embed_nat R m
        := embed_nat_add R (m * k) m
    _ = embed_nat R m * embed_nat R k + embed_nat R m
        := embed_nat_mul R m k |> congrArg (· + embed_nat R m)
    _ = embed_nat R m * embed_nat R k + embed_nat R m * (1 : R)
        := right_identity_law (embed_nat R m)
           |> Eq.symm |> congrArg (embed_nat R m * embed_nat R k + ·)
    _ = embed_nat R m * (embed_nat R k + (1 : R))
        := left_distributive_law (embed_nat R m) (embed_nat R k) (1 : R)
           |> Eq.symm
    _ = embed_nat R m * embed_nat R (succ k)
        := rfl

/-- Embed an integer into a ring `R` by repeatedly adding `1 : R` and negating
    if necessary. -/
def embed_int (R : Type u) [Ring R] : Int -> R
  | ofNat n   => embed_nat R n
  | negSucc n => -(embed_nat R (succ n))

/-- Embedding the integer `0` into a ring `R` yields `0 : R`. -/
theorem embed_int_zero (R : Type u) [Ring R] : embed_int R 0 = (0 : R) := rfl

/-- Embedding the integer `1` into a ring `R` yields `1 : R`. -/
theorem embed_int_one (R : Type u) [Ring R] : embed_int R 1 = (1 : R) :=
  embed_nat_one R

/-- Embedding integers into a ring preserves negation. -/
theorem embed_int_negOfNat (R : Type u) [Ring R] (n : Nat) :
    embed_int R (negOfNat n) = -(embed_nat R n) :=
  match n with
  | zero   => negative_of_zero R |> Eq.symm
  | succ _ => rfl

/-- Embedding integers into a ring preserves negation. -/
theorem embed_int_neg (R : Type u) [Ring R] (x : Int) :
    embed_int R (-x) = -(embed_int R x) :=
  match x with
  | ofNat n   => embed_int_negOfNat R n
  | negSucc n => negation_is_involution (embed_nat R (succ n)) |> Eq.symm

/-- Embedding integers into a ring preserves subtraction. -/
theorem embed_int_subNatNat (R : Type u) [Ring R] (m n : Nat) :
    embed_int R (subNatNat m n) = embed_nat R m + -(embed_nat R n) := sorry

/-- Embedding integers into a ring preserves addition. -/
theorem embed_int_add (R : Type u) [Ring R] (x y : Int) :
    embed_int R (x + y) = embed_int R x + embed_int R y :=
  match x, y with
  | ofNat m,   ofNat n   => embed_nat_add R m n
  | ofNat m,   negSucc n => embed_int_subNatNat R m (succ n)
  | negSucc m, ofNat n   => embed_int_subNatNat R n (succ m) ▸
    commutative_law (embed_int R (ofNat n)) (embed_int R (negSucc m))
  | negSucc m, negSucc n => calc embed_int R (negSucc m + negSucc n)
    _ = embed_int R (negSucc (succ (m + n)))
        := rfl
    _ = -(embed_nat R (succ (m + succ n)))
        := rfl
    _ = -(embed_nat R (succ m + succ n))
        := Nat.succ_add m (succ n) |> Eq.symm
           |> congrArg (embed_nat R) |> congrArg (-·)
    _ = -(embed_nat R (succ m) + embed_nat R (succ n))
        := embed_nat_add R (succ m) (succ n) |> congrArg (-·)
    _ = -(embed_nat R (succ m)) + -(embed_nat R (succ n))
        := negative_of_sum (embed_nat R (succ m)) (embed_nat R (succ n))
    _ = embed_int R (negSucc m) + embed_int R (negSucc n)
        := rfl

/-- Embedding integers into a ring preserves multiplication. -/
theorem embed_int_mul (R : Type u) [Ring R] (x y : Int) :
    embed_int R (x * y) = embed_int R x * embed_int R y :=
  match x, y with
  | ofNat m,   ofNat n   => embed_nat_mul R m n
  | ofNat m,   negSucc n => calc embed_int R (ofNat m * negSucc n)
    _ = embed_int R (negOfNat (m * succ n))
        := rfl
    _ = -(embed_nat R (m * succ n))
        := embed_int_negOfNat R (m * succ n)
    _ = -(embed_nat R m * embed_nat R (succ n))
        := embed_nat_mul R m (succ n) |> congrArg (-·)
    _ = embed_nat R m * -(embed_nat R (succ n))
        := mul_neg_right (embed_nat R m) (embed_nat R (succ n)) |> Eq.symm
    _ = embed_int R (ofNat m) * embed_int R (negSucc n)
        := rfl
  | negSucc m, ofNat n   => calc embed_int R (negSucc m * ofNat n)
    _ = embed_int R (negOfNat (succ m * n))
        := rfl
    _ = -(embed_nat R (succ m * n))
        := embed_int_negOfNat R (succ m * n)
    _ = -(embed_nat R (succ m) * embed_nat R n)
        := embed_nat_mul R (succ m) n |> congrArg (-·)
    _ = -(embed_nat R (succ m)) * embed_nat R n
        := mul_neg_left (embed_nat R (succ m)) (embed_nat R n) |> Eq.symm
    _ = embed_int R (negSucc m) * embed_int R (ofNat n)
        := rfl
  | negSucc m, negSucc n => calc embed_int R (negSucc m * negSucc n)
    _ = embed_int R (ofNat (succ m * succ n))
        := rfl
    _ = embed_nat R (succ m * succ n)
        := rfl
    _ = embed_nat R (succ m) * embed_nat R (succ n)
        := embed_nat_mul R (succ m) (succ n)
    _ = -(embed_nat R (succ m)) * -(embed_nat R (succ n))
        := product_of_negatives (embed_nat R (succ m)) (embed_nat R (succ n))
           |> Eq.symm
    _ = embed_int R (negSucc m) * embed_int R (negSucc n)
        := rfl

end Ring
