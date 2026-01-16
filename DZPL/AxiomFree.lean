import Lean
set_option autoImplicit false

register_option DZPL.axiomFree : Bool := { defValue := false }

partial def findDeclId (stx : Lean.Syntax) : Option Lean.Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.declId then some stx
  else stx.getArgs.findSome? findDeclId

initialize Lean.Elab.Command.addLinter {
  name := `DZPL.axiomFree
  run := fun (stx : Lean.Syntax) => do
    let options : Lean.Options <- Lean.getOptions
    unless options.getBool `DZPL.axiomFree false do return
    unless stx.isOfKind ``Lean.Parser.Command.declaration do return
    let some (declId : Lean.Syntax) := findDeclId stx | return
    let scope : Lean.Elab.Command.Scope <- Lean.Elab.Command.getScope
    let name : Lean.Name := scope.currNamespace ++ declId[0].getId
    let axioms : Array Lean.Name <- Lean.collectAxioms name
    unless axioms.isEmpty do
      Lean.logError m!"'{name}' depends on axioms: {axioms}"
}
