import HPC

-- batch 128 audit: every theorem of HPC/Plane/Cyc2Circle.lean and HPC/Plane/Cyc2.lean, and
-- `fugate_cor1` (still open)

-- Cyc2Circle.lean
#print axioms HPC.Plane.zmod2_const_of_loc
#print axioms HPC.Plane.zmod2_jump_sum
#print axioms HPC.Plane.eNorm_sq
#print axioms HPC.Plane.eNorm_pos
#print axioms HPC.Plane.continuous_circPt
#print axioms HPC.Plane.circPt_add_two_pi
#print axioms HPC.Plane.circPt_add_int_mul_two_pi
#print axioms HPC.Plane.dist_circPt_le
#print axioms HPC.Plane.circPt_mem_segment_iff
#print axioms HPC.Plane.dirAngle_mem_Ioc
#print axioms HPC.Plane.exists_angle
#print axioms HPC.Plane.angle_unique
#print axioms HPC.Plane.eq_of_two_pi_mul
-- Cyc2.lean
#print axioms HPC.Plane.segDir_ne_zero
#print axioms HPC.Plane.not_mem_other_seg
#print axioms HPC.Plane.not_mem_vertices_of_ne_ends
#print axioms HPC.Plane.vertices_mono
#print axioms HPC.Plane.vertices_subset_graphSet
#print axioms HPC.Plane.midpoint_mem_segSet
#print axioms HPC.Plane.midpoint_ne_ends
#print axioms HPC.Plane.midpoint_not_mem_vertices
#print axioms HPC.Plane.isClosed_otherSegs
#print axioms HPC.Plane.otherSegs_nonempty
#print axioms HPC.Plane.not_mem_otherSegs
#print axioms HPC.Plane.sideRadius_pos
#print axioms HPC.Plane.sideRadius_lipschitz
#print axioms HPC.Plane.mem_segSet_of_mem_ball_sideRadius
#print axioms HPC.Plane.edge_local
#print axioms HPC.Plane.halfDisk_subset_sideStrip
#print axioms HPC.Plane.halfDisk_subset_compl
#print axioms HPC.Plane.sideStrip_subset_compl
#print axioms HPC.Plane.sideStrip_nonempty
#print axioms HPC.Plane.nonvertex_eq_openSegment
#print axioms HPC.Plane.mem_halfDisk_of_shift
#print axioms HPC.Plane.sideStrip_isPreconnected
#print axioms HPC.Plane.subset_or_disjoint_component
#print axioms HPC.Plane.memC_eventually
#print axioms HPC.Plane.mem_C_iff_of_mem_sideStrip
#print axioms HPC.Plane.oddSet_subset
#print axioms HPC.Plane.mem_oddSet
#print axioms HPC.Plane.side_jump
#print axioms HPC.Plane.segSet_eq_othEnd
#print axioms HPC.Plane.ne_othEnd
#print axioms HPC.Plane.segDir_eq_of_eq
#print axioms HPC.Plane.segDir_eq_of_ne
#print axioms HPC.Plane.exists_pos_lt_finset
#print axioms HPC.Plane.int_eq_zero_of_two_pi_mul
#print axioms HPC.Plane.eNorm_circPt_sub
#print axioms HPC.Plane.circ_cross_formula
#print axioms HPC.Plane.exists_vertex_radius
#print axioms HPC.Plane.vertex_arcs
#print axioms HPC.Plane.even_deg_oddSet
#print axioms HPC.Plane.isCycle_oddSet
#print axioms HPC.Plane.cycParity_eq_on_sideStrip
#print axioms HPC.Plane.cycParity_sideStrip_ne_iff
#print axioms HPC.Plane.zmod2_add_eq_add_of_iff
#print axioms HPC.Plane.gFun_eq_of_mem_sideStrip
#print axioms HPC.Plane.gFun_eq_across_edge
#print axioms HPC.Plane.gFun_locallyConstant
#print axioms HPC.Plane.gFun_const
#print axioms HPC.Plane.cycParity_oddSet_ne
#print axioms HPC.Plane.separatingGraphHasOddCycle
#print axioms HPC.Plane.janiszewskiPoly_holds

-- still open
#print axioms HPC.Plane.fugate_cor1
