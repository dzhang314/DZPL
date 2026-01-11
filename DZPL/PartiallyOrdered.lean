set_option autoImplicit false
set_option linter.all true
universe u

/-- A type `P` is partially ordered if it has a binary relation (`LE P`) that
    is reflexive, antisymmetric, and transitive. -/
class PartiallyOrdered (P : Type u) extends LE P where
  /-- Every element of a partial order is less than or equal to itself. -/
  reflexive_law (x : P) : x <= x
  /-- If two elements of a partial order are mutually less than or equal to
      each other, then they must coincide. -/
  antisymmetry_law (x y : P) : (x <= y) -> (y <= x) -> (x = y)
  /-- Given three elements of a partial order, if the first two are comparable
      and the last two are comparable in the same direction, then the first and
      last must also be comparable in that direction. -/
  transitive_law (x y z : P) : (x <= y) -> (y <= z) -> (x <= z)
