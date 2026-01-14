# DZPL

DZPL (David Zhang's Proof Library) is a Lean 4 library of formal proofs written
in an unusual low-automation style. It intentionally violates standard Lean and
Mathlib conventions, favoring explicit proof terms over tactics and descriptive
names over terse identifiers.

## Core Requirements

IMPORTANT: All contributions to DZPL MUST adhere to the following guidelines.

### 1. No Mathlib

DZPL works exclusively from the Lean 4 Prelude and does **NOT** use Mathlib.
Do **NOT** add Mathlib as a dependency, reference results from Mathlib, or use
Mathlib naming conventions.

### 2. No Tactics

NEVER use tactics. Always write explicit proof terms using:
- **`calc`** blocks for explicit equational reasoning
- **`Eq.symm`** and **`congrArg`** with anonymous functions to apply equations
- **pipe operator `|>`** to combine proof steps

**Prefer:**
```lean
example {x : G} (H : x + x = x) : x = 0 := calc x
  _ = x + 0        := zero_law x |> Eq.symm
  _ = x + (x + -x) := negative_law x |> Eq.symm |> congrArg (x + ·)
  _ = (x + x) + -x := associative_law x x (-x) |> Eq.symm
  _ = x + -x       := H |> congrArg (· + -x)
  _ = 0            := negative_law x
```

**Avoid:**
```lean
example {x : G} (H : x + x = x) : x = 0 := by
  rw [← zero_law x, ← negative_law x, ← associative_law]
  simp [H, negative_law]
```

### 3. File Structure

Each file should begin with:
```lean
set_option autoImplicit false
set_option linter.all true
```

If universes are needed, the line `universe u` should immediately follow this
header. The number of universes should be minimized. So far, no file has needed
more than one universe.

### 4. Naming Conventions

Use descriptive names with `_law` suffix for axioms and fundamental properties:

| DZPL                | Mathlib                   |
|---------------------|---------------------------|
| `commutative_law`   | `add_comm` / `mul_comm`   |
| `associative_law`   | `add_assoc` / `mul_assoc` |
| `zero_law`          | `add_zero`                |
| `negative_law`      | `add_neg_cancel`          |
| `left_identity_law` | `one_mul`                 |
| `left_inverse_law`  | `inv_mul_cancel`          |

Theorem names should be descriptive phrases:
- `idempotent_is_zero`
- `sum_zero_implies_negative`
- `negation_is_involution`
- `inverse_of_product`

### 5. Documentation

Every named class, class field, definition, and theorem must have an attached
docstring explaining its meaning. Use `/-- ... -/` syntax. Anonymous instances
may lack documentation.

#### 5a. Class documentation

Describe what the class represents, the operations it provides, and its key
properties. Use the pattern "An X is a type `T` with ... that is/has ...".
Reference type class notation in backticks. Every `extends` member should be
referenced in the docstring.

```lean
/-- An abelian group is a type `G` with an addition operation (`Add G`) that is
    commutative, associative, has an identity (`Zero G`), and admits inverses
    (`Neg G`). -/
class AbelianGroup (G : Type u) extends Add G, Zero G, Neg G where
  ...

/-- A ring is a rng (`Rng R`) with a two-sided multiplicative identity element
    (`One R`). -/
class Ring (R : Type u) extends Rng R, One R where
  ...
```

#### 5b. Class field documentation

Describe the axiom or law concisely in a single declarative sentence. Make sure
to mention the name of the class structure in the docstring.

```lean
/-- Multiplication in a group is associative. -/
associative_law (x y z : G) : (x * y) * z = x * (y * z)

/-- An inequality in an ordered rng remains true when the same element is
    added to both sides. -/
add_order_law {x y : R} (z : R) : (x ≤ y) -> (x + z ≤ y + z)

/-- Every pair of elements in a total order is comparable. -/
totality_law (x y : T) : (x ≤ y) ∨ (y ≤ x)
```

#### 5c. Theorem documentation

Concisely state what the theorem proves and mention the name of the structure.

```lean
/-- In an abelian group, negating twice yields the original element. -/
theorem negation_is_involution (x : G) : -(-x) = x := ...

/-- In a rng, left multiplication by `0` yields `0`. -/
theorem mul_zero_left (x : R) : 0 * x = 0 := ...

/-- If `0 = 1` in a ring, then the ring is a zero ring. -/
theorem zero_ring_law : (0 : R) = (1 : R) -> ZeroRing R := ...
```

Named conditions can be defined in theorem documentation; they must be brief.

```lean
/-- An element `x` of an abelian group is idempotent if `x + x = x`.
    The only idempotent element in any abelian group is `0`. -/
theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := ...
```

#### 5d. Definition documentation

Briefly describe the concept captured by the definition. Again, make sure to
mention the name of the structure(s) to which the definition applies.

```lean
/-- An element of a differential rng is a constant if its derivative is `0`. -/
def Constant (x : R) := δ x = 0

/-- A zero ring is a ring with only one element, `0`. -/
def ZeroRing (R : Type u) [Ring R] : Prop := ∀ x : R, x = 0
```

## Proof Patterns

### Naming intermediate facts

Input hypothesis parameters should be named `H`:
```lean
theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := ...
```

When intermediate facts are needed (via `have`), use **descriptive names** that
indicate what the statement proves, not generic names like `H1` or `H2`. Always
include type annotations:
```lean
have le : x + z ≤ y + z := add_order_law z (And.left H)
have ne : x + z ≠ y + z := fun (Heq : x + z = y + z) => ...
```

Include brief explanatory comments before key proof steps:
```lean
-- To obtain `x + z < y + z`, we prove `x + z ≤ y + z` and `x + z ≠ y + z`.
have le : x + z ≤ y + z := ...
```

### Prefer `calc` over `have`

Whenever possible, use `calc` blocks instead of intermediate `have` statements:
```lean
-- Prefer: direct `calc` chain
theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 := calc x
  _ = x + 0        := zero_law x |> Eq.symm
  _ = x + (x + -x) := negative_law x |> Eq.symm |> congrArg (x + ·)
  _ = (x + x) + -x := associative_law x x (-x) |> Eq.symm
  _ = x + -x       := H |> congrArg (· + -x)
  _ = 0            := negative_law x

-- Avoid: unnecessary intermediate `have` statements
theorem idempotent_is_zero {x : G} (H : x + x = x) : x = 0 :=
  have step1 : x = x + 0 := zero_law x |> Eq.symm
  have step2 : x + 0 = x + (x + -x) := ...
  ...
```

### Applying an equality inside an expression

Use `congrArg` with an anonymous function:
```lean
-- To transform `x + 0` to `x + (y + -y)`:
negative_law y |> Eq.symm |> congrArg (x + ·)
```

### Chaining transformations

Use the pipe operator to chain multiple `congrArg` applications:
```lean
-- Transform deeply nested subexpression
some_equality |> congrArg (· + z) |> congrArg (x + ·)
```

Use the reverse pipe operator to chain outer proof steps with `calc` blocks:
```lean
theorem mul_zero_left (x : R) : 0 * x = 0 :=
  idempotent_is_zero <| calc 0 * x + 0 * x
    _ = (0 + 0) * x := right_distributive_law 0 0 x |> Eq.symm
    _ = 0 * x       := zero_law 0 |> congrArg (· * x)

theorem negation_is_involution (x : G) : -(-x) = x :=
  sum_zero_implies_negative <| calc -x + x
    _ = x + -x := commutative_law (-x) x
    _ = 0      := negative_law x
```
