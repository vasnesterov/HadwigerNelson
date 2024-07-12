# Hadwiger-Nelson problem formalization in Lean 4
**Now this work is in progress. I will finish it soon.**
## Description

This repo contains a formalized theorem stating that the plane can not be colored such that no two points at distance 1 from each other have the same color. In particular, we verify that 510-vertex graph constructed by Marjin Heule is non-4-colorable.

## Intallation
1. Install Lean 4, following the instructions [here](https://leanprover-community.github.io/get_started.html).
2. Install CaDiCaL (SAT solver).

## Usage
Run `lake exe cache get` to load Mathlib cache, then build the project with `lake build`. 
Note that it requires about 20GB RAM and 3 hours to build. I hope to speed up it in the future.

## Proof overview
We use a standard approach to prove the statement:
1. Parse `.vtx` file containing vertexes of the non-4-colorable unit distance graph.
2. Find unit distance edges in between its vertexes and prove that they have exactly unit length by some automatic tactic.
3. Reduce colorability of finite graph to satisfability of some CNF, then use LeanSAT along with CaDiCaL SAT-solver to prove that the graph above is non-4-colorable.
4. Reduce colorability of the plane to colorability of finite unit distance graphs and finish the proof.

## Building edges
To find edges of the graph we cast vertexes' coordinates to `Float` and check whether distance between two given point are close enough to 1. If so, we run the tactic `build_edge` that combines `norm_num`, `ring_nf` and some extra rewriting of square roots.

So far, the tactic succesfully proves equalities involving numbers which are linear combination of square roots of naturals over rationals. It it enough to build all edges of 510-vertex Heule's graph. Unfortunately, the smallest known non-4-colorable unit distance graph constructed by Jaan Parts is so far beyound of the `build_edge` abilities, because it contains numbers like `Sqrt[(5*(7 + Sqrt[33]))/2]`.

## TODO

* Prove that 509-vertex Parts graph is non-4-colorable unit distance graph.
* Prove that the plane *is* 7-colorable.
* Construct the non-4-colorable graph *inside* Lean to make the proof shorter and more independent.
* Speed up the tactic which we use to prove that edges have exactly unit length.
