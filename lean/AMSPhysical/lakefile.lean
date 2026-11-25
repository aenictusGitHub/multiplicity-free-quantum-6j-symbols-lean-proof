import Lake
open Lake DSL

package «ams-physical-components»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib AMSPhysical where
  roots := #[`AMSPhysical, `Audit]
  moreLeanArgs := #["-s", "65536"]
