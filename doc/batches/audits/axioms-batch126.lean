import HPC

-- batch 126 audit: every theorem of HPC/Plane/Jct2.lean, and `fugate_cor1` (still open)

-- Jct2.lean
#print axioms HPC.Plane.zmod2_cases
#print axioms HPC.Plane.zmod2_ne_add_one
#print axioms HPC.Plane.zmod2_eq_of_ne'
#print axioms HPC.Plane.zmod2_eq_of_ne
#print axioms HPC.Plane.next_ne_self
#print axioms HPC.Plane.edge_ends_ne
#print axioms HPC.Plane.dist_shift_snd
#print axioms HPC.Plane.dist_shift_snd_sub
#print axioms HPC.Plane.dist_shift_fst
#print axioms HPC.Plane.dist_shift_fst_sub
#print axioms HPC.Plane.exists_param_avoid
#print axioms HPC.Plane.exists_near_on_segment
#print axioms HPC.Plane.exists_param_near_end
#print axioms HPC.Plane.polygonOf_nonempty
#print axioms HPC.Plane.isPreconnected_polygonOf
#print axioms HPC.Plane.parity_flip_at
#print axioms HPC.Plane.parity_flip_vertical
#print axioms HPC.Plane.mem_closure_parity_set
#print axioms HPC.Plane.cross_zero_of_mem_segment
#print axioms HPC.Plane.eq_add_smul_of_cross_zero
#print axioms HPC.Plane.polygon_local_chord
#print axioms HPC.Plane.mem_halfDisk_true
#print axioms HPC.Plane.mem_halfDisk_false
#print axioms HPC.Plane.halfDisk_convex
#print axioms HPC.Plane.halfDisk_nonempty
#print axioms HPC.Plane.ball_diff_chord
#print axioms HPC.Plane.parity_flip_edge
#print axioms HPC.Plane.compl_eq_union_parity_sets
#print axioms HPC.Plane.disjoint_parity_sets
#print axioms HPC.Plane.local_piece
#print axioms HPC.Plane.vertex_two_pieces
#print axioms HPC.Plane.exists_first_hit
#print axioms HPC.Plane.segment_subset_of_first_hit
#print axioms HPC.Plane.exists_segment_to_boundary
#print axioms HPC.Plane.sideNbhd_subset
#print axioms HPC.Plane.sideNbhd_isConnected
#print axioms HPC.Plane.sideNbhd_near
#print axioms HPC.Plane.exists_segment_to_sideNbhd
#print axioms HPC.Plane.isConnected_parity_set
#print axioms HPC.Plane.frontier_parity_set
#print axioms HPC.Plane.jct_polygon
#print axioms HPC.Plane.planeFacts_of_enclose_janiszewski

-- open
#print axioms HPC.Plane.fugate_cor1
