import Lake
open Lake DSL

package «unit_graph_coloring» where

require LeanSAT from git
  "https://github.com/leanprover/leansat" @ "d26e25db9fe9ab973526e5d70ae38fdc87d084a6"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2024-07-03"


@[default_target]
lean_lib HadwigerNelson
