import HPC.Moore.M19AB

-- Batch 140: `#print axioms` for every new theorem (`HPC/Moore/M19*.lean`, `M41*.lean`, `M43*.lean`). Output: `axioms-batch140.txt`.
-- `HPC/Moore/M19Defs.lean`
-- `HPC/Moore/M19A.lean`
#print axioms HPC.Moore.Gen.crossing
#print axioms HPC.Moore.m19_theoremA
-- `HPC/Moore/M19Bstep.lean`
#print axioms HPC.Moore.Gen.TArc.tail_in_open
#print axioms HPC.Moore.m19_B_step
-- `HPC/Moore/M19B.lean`
#print axioms HPC.Moore.Gen.PJ.symm
#print axioms HPC.Moore.Gen.PJ.trans
#print axioms HPC.Moore.loc_arc
#print axioms HPC.Moore.seg_nhds
#print axioms HPC.Moore.m19_theoremB
-- `HPC/Moore/M19D.lean`
#print axioms HPC.Moore.hair_isPreconnected
#print axioms HPC.Moore.m19_D_arc
-- `HPC/Moore/M41Replace.lean`
#print axioms HPC.Moore.Gen.continuous_unaffI
#print axioms HPC.Moore.Gen.unaffI_left
#print axioms HPC.Moore.Gen.unaffI_right
#print axioms HPC.Moore.Gen.unaffI_val
#print axioms HPC.Moore.Gen.unaffI_injOn
#print axioms HPC.Moore.Gen.unaffI_mem_Ioo
#print axioms HPC.Moore.Gen.unaffI_affI
#print axioms HPC.Moore.Gen.affI_mem_Ioo
#print axioms HPC.Moore.Gen.finite_long_intervals
#print axioms HPC.Moore.Gen.arc_replace
-- `HPC/Moore/M41Geom.lean`
#print axioms HPC.Moore.Gen.mem_connectedComponentIn_of_mem_closure
#print axioms HPC.Moore.Gen.frontier_connectedComponentIn_subset
#print axioms HPC.Moore.Gen.exists_unbounded_component
#print axioms HPC.Moore.Gen.disjoint_of_unbounded
#print axioms HPC.Moore.exists_other_arc
#print axioms HPC.Moore.chord_through
#print axioms HPC.Moore.chord_subset
#print axioms HPC.Moore.chords_null
-- `HPC/Moore/M41Side.lean`
#print axioms HPC.Moore.chord_side
#print axioms HPC.Moore.pocket
-- `HPC/Moore/M41Half.lean`
#print axioms HPC.Moore.Gen.image_Icc_diff_ends
#print axioms HPC.Moore.Gen.Ioo_eq_of_not_disjoint
#print axioms HPC.Moore.half_replace_gen
#print axioms HPC.Moore.half_replace
-- `HPC/Moore/M41.lean`
#print axioms HPC.Moore.exists_compact_superset_moore
#print axioms HPC.Moore.curve_of_frontier_subset
#print axioms HPC.Moore.fa_theorem41_caseII
#print axioms HPC.Moore.fa_theorem41
#print axioms HPC.Moore.fa_theorem42
-- `HPC/Moore/M43Pocket.lean`
#print axioms HPC.Moore.chord_pockets
#print axioms HPC.Moore.pocket_int
#print axioms HPC.Moore.pocket_ext
-- `HPC/Moore/M43Dual.lean`
#print axioms HPC.Moore.adjacent_piece
-- `HPC/Moore/M43Comp.lean`
#print axioms HPC.Moore.dual_component
-- `HPC/Moore/M43.lean`
#print axioms HPC.Moore.isPreconnected_scc_diff
#print axioms HPC.Moore.dual_step
#print axioms HPC.Moore.iterate_inner
#print axioms HPC.Moore.fa_theorem43
