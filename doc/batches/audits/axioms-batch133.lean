import HPC

-- batch 133 audit: every theorem of HPC/Plane/TreeLikeNSGraph.lean, TreeLikeNSLog.lean and
-- TreeLikeNS.lean, with the re-proved `theorem6_1951_rel` and `theorem6_1951`

-- `HPC/Plane/TreeLikeNSGraph.lean`
#print axioms HPC.Plane.exists_seq_of_reflTransGen
#print axioms HPC.Plane.isCoherent_of_chainConn
#print axioms HPC.Plane.exists_chainConn_card
#print axioms HPC.Plane.circularChain_of_minimal
#print axioms HPC.Plane.no_two_nbrs

-- `HPC/Plane/TreeLikeNSLog.lean`
#print axioms HPC.Plane.continuous_toCpx
#print axioms HPC.Plane.toCpx_injective
#print axioms HPC.Plane.toCpx_lineMap
#print axioms HPC.Plane.sub_const_of_exp_eq
#print axioms HPC.Plane.slit_of_segment_ne_zero
#print axioms HPC.Plane.segment_ne_zero
#print axioms HPC.Plane.toCpx_sub_ne_zero
#print axioms HPC.Plane.div_mem_slitPlane
#print axioms HPC.Plane.log_diff_edge
#print axioms HPC.Plane.arg_div_jump
#print axioms HPC.Plane.crossesEast_iff_cross
#print axioms HPC.Plane.edge_jump

-- `HPC/Plane/TreeLikeNS.lean`
#print axioms HPC.Plane.isTreeChain_univ
#print axioms HPC.Plane.isTreeLikeOld_of_isContinuum
#print axioms HPC.Plane.norm_toCpx_sub_le
#print axioms HPC.Plane.dist_le_norm_toCpx_sub
#print axioms HPC.Plane.exists_log_on_ball
#print axioms HPC.Plane.exists_leaf
#print axioms HPC.Plane.exists_ball_branch
#print axioms HPC.Plane.exists_log_inv
#print axioms HPC.Plane.exists_log_on_treeChain
#print axioms HPC.Plane.no_log_on_polygon
#print axioms HPC.Plane.exists_enclosing_polygon_pt
#print axioms HPC.Plane.exists_polygon_around
#print axioms HPC.Plane.isPreconnected_compl_closedBall
#print axioms HPC.Plane.exists_bounded_component_of_separates
#print axioms HPC.Plane.isTreeChain_filter_meet
#print axioms HPC.Plane.treeLike_nonseparating
#print axioms HPC.Plane.theorem7_1951_treeLike
#print axioms HPC.Plane.isTreeLike_iff_nonseparating

-- `IsTreeLike` repaired: Theorem 6 re-checked
#print axioms HPC.Plane.theorem6_1951_rel
#print axioms HPC.Plane.theorem6_1951
