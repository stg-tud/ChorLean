import Lake
open Lake DSL

package «chorlean» where
  -- add package configuration options here

lean_lib «Chorlean» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "bump/v4.10.0"
require socket from git
  "https://github.com/hargoniX/socket.lean" @ "main"

@[default_target]
lean_exe «chorlean» where
  root := `Main

lean_exe auth where
  root := `examples.sso_auth
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe merge where
  root := `examples.mergesort
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true


lean_exe books where
  root := `examples.bookseller
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe RPS where
  root := `examples.RockPaperScissors
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true
