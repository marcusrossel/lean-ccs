import Lake
open Lake DSL

package ccs

@[default_target]
lean_lib CCS

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
