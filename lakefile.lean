import Lake
open Lake DSL

package «chorlean» where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  -- add package configuration options here

lean_lib «Chorlean» where
  -- add library configuration options here

oreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "bump/v4.10.0"
require socket from git
  "https://github.com/hargoniX/socket.lean" @ "main"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.4.1"

@[default_target]
lean_exe «chorlean» where
  root := `Main

lean_exe auth where
  root := `Chorlean.examples.sso_auth
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe merge where
  root := `Chorlean.examples.mergesort_demo
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe db where
  root := `Chorlean.examples.database
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe books where
  root := `Chorlean.examples.bookseller1
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true
