import HadwigerNelson.FromVtx

-- set_option trace.profiler true

-- set_option maxHeartbeats 0 in
noncomputable def triangle : UnitGraph := from_vtx "vtx/triangle.vtx"

open CompGraph UnitGraph in
example : ¬ planeColorable 2 := by
  intro h_p_col
  absurd graph_Colorable_of_planeColorable h_p_col triangle
  apply Noncolorable_from_unsat
  dsimp [triangle, toCompGraph, CompGraph.ColorablilityCNF]
  apply LitToNat_equisat _
  clear h_p_col
  unsat_native_decide
