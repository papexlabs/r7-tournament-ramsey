import R7lean

/-! Run with `lake env lean CheckAxioms.lean` after `lake build`. -/

-- the main theorem: F2–F6 axioms of `R7lean/Facts.lean` and the CNF axioms of `R7lean/FactsCNF.lean`
#print axioms R7.every_tournament_46_has_TT7
-- milestone 1's route (semantic F7 axioms), for comparison
#print axioms R7.every_tournament_46_has_TT7_semantic
-- F7 from the CNF axioms
#print axioms R7.PivotFacts.ofCNF
-- kernel-checked parts of milestone 2
#print axioms R7.Enc.NMH.satisfiable_of_hasTTFreeCompletion
#print axioms R7.Enc.Tri.satisfiable_of_hasTTFreeCompletion
#print axioms R7.Enc.satisfiable_cnfOf
#print axioms R7.Enc.unsat_of_cover
#print axioms R7.nmh23_iso
#print axioms R7.isoST25_H6
#print axioms R7.isoST25_W7
-- milestone 1
#print axioms R7.Tournament.containsTT6_or_H6_or_W7
#print axioms R7.Tournament.hasTTFreeCompletion_of_embeddings
#print axioms R7.Tournament.hasTTFreeCompletion_congr
#print axioms R7.Tournament.containsTT_iff_exists_transitive
