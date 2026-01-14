import Lean
set_option autoImplicit false
set_option linter.all true

/-- Count the number of heartbeats used by a command. -/
elab "#count_heartbeats" cmd:command : command => do
  let initial <- IO.getNumHeartbeats
  Lean.Elab.Command.elabCommand (<-
    `(command| set_option maxHeartbeats 0 in $cmd))
  let final <- IO.getNumHeartbeats
  Lean.logInfo m!"Used {final - initial} heartbeats."
