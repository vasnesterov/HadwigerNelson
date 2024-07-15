# Hadwiger-Nelson Problem Formalization in Lean 4

## Description

This repository contains a formalized theorem stating that the plane cannot be colored such that no two points at distance 1 from each other have the same color. Specifically, we verify that the 510-vertex graph constructed by Marjin Heule is not 4-colorable.

## Installation

1. Install Lean 4 by following the instructions [here](https://leanprover-community.github.io/get_started.html).
2. Install CaDiCaL (SAT solver). You can use a different SAT solver capable of producing LRAT-proofs of unsatisfiability with:

   ```lean
   set_option sat.solver <YOUR_SAT_SOLVER_COMMAND>
   ```
3. Run `lake exe cache get` to load the Mathlib cache, then build the project with `lake build`. The building process requires more than 40GB of RAM and takes approximately 3 hours to complete. Alternatively, you can download oleans from [Dropbox](https://www.dropbox.com/scl/fi/f1gd4gi9dfuse8b1idvki/build.zip?rlkey=vtvfgkfyegzpgu6nhf17jic4e&st=zry5okw0&dl=0), put the content to the `.lake` directory and only then run `lake build`.

## Proof Overview

We formalize a standard approach to prove the statement:

1. Parse the `.vtx` file containing vertices of the non-4-colorable unit distance graph.
2. Find unit distance edges between its vertices and prove that they have exactly unit length using an automatic tactic.
3. Reduce the colorability of the finite graph to the satisfiability of some CNF, then use [LeanSAT](https://github.com/leanprover/leansat) along with an external SAT solver to prove that the graph is non-4-colorable.
4. Reduce the colorability of the plane to the colorability of finite unit distance graphs and complete the proof.

### Building Edges

To find edges of the graph, we cast vertex coordinates to `Float` and check whether the distance between two given points is close enough to 1. If so, we run the `build_edge` tactic that combines `norm_num`, `ring_nf`, and some extra rewriting of square roots.

Currently, the tactic successfully proves equalities involving numbers that are linear combinations of square roots of naturals over rationals. This is sufficient to build all edges of the 510-vertex Heule graph. Unfortunately, the smallest known non-4-colorable unit distance graph constructed by Jaan Parts is currently beyond the capabilities of `build_edge`, as it contains numbers like `Sqrt[(5*(7 + Sqrt[33]))/2]`.

## TODO
(PRs are welcome)
- Prove that the 509-vertex Parts graph is a non-4-colorable unit distance graph.
- Prove that the plane *is* 7-colorable.
- Construct the non-4-colorable graph *within* Lean to make the proof shorter and more independent.
- Optimize the tactic used to prove that edges have exactly unit length.
  
## References
- The 510-vertex graph by Marjin Heule was obtained from [this repository](https://github.com/marijnheule/CNP-SAT/).
- The 509-vertex graph by Jaan Parts was sourced from [this Polymath thread](https://dustingmixon.wordpress.com/2019/12/12/polymath16-fifteenth-thread-writing-the-paper-and-chasing-down-loose-ends/).
