-- Lake build definition for the Lean runner and library modules.
import Lake
open Lake DSL

package rumpsteakLean

lean_lib Rumpsteak

@[default_target]
lean_exe rumpsteak_runner {
  root := `Rumpsteak.Runner
  supportInterpreter := true
}
