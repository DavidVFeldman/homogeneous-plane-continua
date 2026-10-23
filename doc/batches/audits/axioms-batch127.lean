import HPC

-- batch 127 audit: every theorem of HPC/Plane/Cyc1.lean, and `fugate_cor1` (still open)

-- Cyc1.lean
#print axioms HPC.Plane.lex_le_of_mem_segment
#print axioms HPC.Plane.eq_of_segment_eq_lex
#print axioms HPC.Plane.exists_lineMap_of_mem_segment
#print axioms HPC.Plane.real_pair_eq_aux
#print axioms HPC.Plane.real_pair_eq
#print axioms HPC.Plane.mem_vertices
#print axioms HPC.Plane.IsProper.subset
#print axioms HPC.Plane.isClosed_graphSet
#print axioms HPC.Plane.mem_graphSet
#print axioms HPC.Plane.graphSet_mono
#print axioms HPC.Plane.end_mem_graphSet
#print axioms HPC.Plane.sum_symmDiff_zmod2
#print axioms HPC.Plane.symmDiff_subset_of
#print axioms HPC.Plane.deg_cast
#print axioms HPC.Plane.deg_symmDiff
#print axioms HPC.Plane.deg_singleton
#print axioms HPC.Plane.deg_empty
#print axioms HPC.Plane.exists_of_deg_ne_zero
#print axioms HPC.Plane.even_iff_deg_cast
#print axioms HPC.Plane.sum_deg_vertices
#print axioms HPC.Plane.zmod2_eq_zero_or_one
#print axioms HPC.Plane.card_odd_vertices
#print axioms HPC.Plane.cutSet_finite
#print axioms HPC.Plane.mem_cutSet_of_end
#print axioms HPC.Plane.mem_subdiv
#print axioms HPC.Plane.subdiv_inter
#print axioms HPC.Plane.exists_gap
#print axioms HPC.Plane.exists_piece
#print axioms HPC.Plane.exists_proper_subdivision
#print axioms HPC.Plane.cycParity_symmDiff
#print axioms HPC.Plane.not_sum_vJump_even_skeleton
#print axioms HPC.Plane.sum_vJump_even
#print axioms HPC.Plane.not_mem_segSet_of_not_mem_graphSet
#print axioms HPC.Plane.cycParity_eventually_eq
#print axioms HPC.Plane.cycParity_locallyConstant
#print axioms HPC.Plane.cycParity_eq_of_isPreconnected
#print axioms HPC.Plane.cycParity_far
#print axioms HPC.Plane.separatesPts_of_cycParity_ne
#print axioms HPC.Plane.cycParity_flip_horizontal_shift
#print axioms HPC.Plane.cycParity_flip_vertical_shift
#print axioms HPC.Plane.cycParity_flip
#print axioms HPC.Plane.exists_path_zmod
#print axioms HPC.Plane.graph_connected_of_isConnected
#print axioms HPC.Plane.exists_join_all
#print axioms HPC.Plane.inter_subset_graphSet_inter
#print axioms HPC.Plane.exists_cycle_decomposition
#print axioms HPC.Plane.separatesPts_mono
#print axioms HPC.Plane.graphSet_filter_subdivision
#print axioms HPC.Plane.janiszewskiPoly_of_oddCycle

-- open target
#print axioms HPC.Plane.fugate_cor1
