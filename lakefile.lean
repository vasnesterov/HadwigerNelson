import Lake
open Lake DSL

package «HadwigerNelson» where

require LeanSAT from git
  "https://github.com/leanprover/leansat" @ "a1acc2d8339d385aff8064ada34aeec4620fdfea"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2024-07-11"

@[default_target]
lean_lib HadwigerNelson
