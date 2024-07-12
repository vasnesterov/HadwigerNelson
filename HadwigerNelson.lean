import HadwigerNelson.BuildEdges

open CompGraph UnitGraph

example : ¬ planeColorable 3 := by
  let moser := from_vtx "vtx/moser.vtx"
  intro h_p_col
  absurd graph_Colorable_of_planeColorable h_p_col moser
  apply Noncolorable_from_unsat
  dsimp [moser, toCompGraph, CompGraph.ColorablilityCNF]
  apply LitToNat_equisat _
  unsat_native_decide

-- set_option maxHeartbeats 0 in
-- set_option maxRecDepth 32000 in
theorem plane_non_4_colorable : ¬ planeColorable 4 := by
  let heule := from_vtx "vtx/510_heule.vtx"
  intro h_p_col
  absurd graph_Colorable_of_planeColorable h_p_col heule
  apply Noncolorable_from_unsat
  dsimp [heule, toCompGraph, CompGraph.ColorablilityCNF]
  apply LitToNat_equisat _
  unsat_native_decide
