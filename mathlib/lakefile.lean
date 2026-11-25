import Lake
open Lake DSL

package «alikhani-jafari-mathlib»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

lean_lib AJ

@[default_target]
lean_lib AlikhaniJafariMathlib
