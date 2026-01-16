import DZPL.AxiomFree
import DZPL.PartiallyOrdered
set_option autoImplicit false
set_option DZPL.axiomFree true
set_option linter.all true
universe u

/-- A type `T` is totally ordered if it is partially ordered
    (`PartiallyOrdered T`) and every pair of elements is comparable. -/
class TotallyOrdered (T : Type u) extends PartiallyOrdered T where
  /-- Every pair of elements in a total order is comparable. -/
  totality_law (x y : T) : (x ≤ y) ∨ (y ≤ x)
