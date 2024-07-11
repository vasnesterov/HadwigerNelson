# Hadwiger-Nelson problem formalization in Lean 4
**Now this work is in progress. I will finish it soon.**
## Description

This repo contains a formalized theorem stating that the plane can not be colored such that no two points at distance 1 from each other have the same color. In particular, we verify that 509-vertex graph constructed by Jaan Parts is non-4-colorable.

## Intallation
TODO

## Proof overview
We use a standard approach to prove the statement:
1. Parse `.vtx` file containing vertexes of the non-4-colorable unit distance graph.
2. Find unit distance edges in between its vertexes and prove that they have exactly unit length by some automatic tactic.
3. Reduce colorability of finite graph to satisfability of some CNF, then use LeanSAT along with CaDiCaL SAT-solver to prove that the graph above is non-4-colorable.
4. Reduce colorability of the plane to colorability of finite unit distance graphs and finish the proof.

## TODO

* Prove that the plane *is* 7-colorable.
* Construct the non-4-colorable graph *inside* Lean to make the proof shorter and more independent.
* Speed up the tactic which we use to prove that edges have exactly unit length.
