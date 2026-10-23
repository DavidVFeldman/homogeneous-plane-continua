import HPC

-- batch 130 audit: every theorem of HPC/Plane/Enc1Cyc.lean, HPC/Plane/Enc1Grid.lean and
-- HPC/Plane/Enc1.lean, and `fugate_cor1` (still open)

-- Enc1Cyc.lean
#print axioms HPC.Plane.polyInterior_eq_oddSet
#print axioms HPC.Plane.cycParity_polyEdges
#print axioms HPC.Plane.graphSet_polyEdges
#print axioms HPC.Plane.fnxt_val
#print axioms HPC.Plane.fnxt_injective
#print axioms HPC.Plane.fnxt_ne
#print axioms HPC.Plane.fnxt_fnxt_ne
#print axioms HPC.Plane.SAdj.symm
#print axioms HPC.Plane.SAdj.ne
#print axioms HPC.Plane.SAdj.mem_vertices
#print axioms HPC.Plane.exists_other_nbr
#print axioms HPC.Plane.cycle_or_extend
#print axioms HPC.Plane.exists_cycle_vertices
#print axioms HPC.Plane.simpleCycle_of_vertices
#print axioms HPC.Plane.exists_simpleCycle_decomposition
#print axioms HPC.Plane.mem_foldr_union
#print axioms HPC.Plane.cycParity_foldr

-- Enc1Grid.lean
#print axioms HPC.Plane.mem_gsq
#print axioms HPC.Plane.isCompact_gsq
#print axioms HPC.Plane.int_le_of_mul_le
#print axioms HPC.Plane.int_lt_of_mul_lt
#print axioms HPC.Plane.idx_close
#print axioms HPC.Plane.idx_eq_of_strict
#print axioms HPC.Plane.mem_sqUnion
#print axioms HPC.Plane.isCompact_sqUnion
#print axioms HPC.Plane.exists_nbhd_cover_1d
#print axioms HPC.Plane.exists_nbhd_cover
#print axioms HPC.Plane.mem_interior_sqUnion
#print axioms HPC.Plane.exists_near_not_mem
#print axioms HPC.Plane.mem_frontier_sqUnion_iff
#print axioms HPC.Plane.mem_segSet_hseg
#print axioms HPC.Plane.mem_segSet_vseg
#print axioms HPC.Plane.IsGridSeg.lex_lt
#print axioms HPC.Plane.gridSeg_inter
#print axioms HPC.Plane.isProper_of_gridSeg
#print axioms HPC.Plane.mem_bdryOf
#print axioms HPC.Plane.isProper_bdryOf
#print axioms HPC.Plane.mem_graphSet_bdryOf_col
#print axioms HPC.Plane.mem_graphSet_bdryOf_row
#print axioms HPC.Plane.mem_graphSet_bdryOf_iff
#print axioms HPC.Plane.frontier_sqUnion

-- Enc1.lean
#print axioms HPC.Plane.gridUnion_eq
#print axioms HPC.Plane.finite_sqIdx_set
#print axioms HPC.Plane.mem_sqIdx_iff
#print axioms HPC.Plane.gridUnion_subset_cthickening
#print axioms HPC.Plane.isCompact_gridUnion
#print axioms HPC.Plane.disjoint_frontier_gridUnion
#print axioms HPC.Plane.subset_interior_gridUnion
#print axioms HPC.Plane.isProper_bdryGraph
#print axioms HPC.Plane.frontier_gridUnion
#print axioms HPC.Plane.graphSet_bdryGraph_subset
#print axioms HPC.Plane.mem_sqEdges
#print axioms HPC.Plane.hseg_inj
#print axioms HPC.Plane.vseg_inj
#print axioms HPC.Plane.hseg_ne_vseg
#print axioms HPC.Plane.card_filter_eq_one_iff_xor
#print axioms HPC.Plane.mem_bdryGraph_iff_card
#print axioms HPC.Plane.fst_le_gridR
#print axioms HPC.Plane.farPt_not_mem
#print axioms HPC.Plane.halfPlane_subset_component
#print axioms HPC.Plane.farPt_not_mem_graphSet
#print axioms HPC.Plane.not_isBounded_component
#print axioms HPC.Plane.interior_gridUnion_disjoint_component
#print axioms HPC.Plane.cycParity_oddSet_eq_one_on
#print axioms HPC.Plane.exists_enclosing_polygon

-- open target (unchanged)
#print axioms HPC.Plane.fugate_cor1
