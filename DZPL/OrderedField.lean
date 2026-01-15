import DZPL.OrderedRing
import DZPL.Field
set_option autoImplicit false
set_option linter.all true
universe u

/-- An ordered field is an ordered ring (`OrderedRing F`) that is also a field
    (`Field F`). -/
class OrderedField (F : Type u) extends OrderedRing F, Field F
