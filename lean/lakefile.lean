import Lake
open Lake DSL

package alsomitraFixes where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib AlsomitraFixes
