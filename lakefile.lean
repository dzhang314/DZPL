import Lake
open Lake DSL

package «DZPL» where
  -- add package configuration options here

lean_lib «DZPL» where
  -- add library configuration options here

@[default_target]
lean_exe «dzpl» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
