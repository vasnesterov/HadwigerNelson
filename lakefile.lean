import Lake
open Lake DSL

package «unit_graph_coloring» where

require LeanSAT from git
  "https://github.com/leanprover/leansat" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2024-07-03"


@[default_target]
lean_lib HadwigerNelson
