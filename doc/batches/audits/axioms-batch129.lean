import HPC

-- batch 129 audit: every theorem of HPC/Plane/Polygonal.lean, HPC/Plane/PolygonalPoly.lean and
-- HPC/Plane/JanPoly.lean, the edited theorems (the field, the two uses, Theorems 6 and 7, the
-- interface), and `fugate_cor1` (still open)

-- Polygonal.lean
#print axioms HPC.Plane.isCompact_segment_pt
#print axioms HPC.Plane.IsPolygonal.isCompact
#print axioms HPC.Plane.IsPolygonal.isClosed
#print axioms HPC.Plane.IsPolygonal.union
#print axioms HPC.Plane.isPolygonal_empty
#print axioms HPC.Plane.isPolygonal_segment
#print axioms HPC.Plane.isPolygonal_singleton
#print axioms HPC.Plane.isPolygonal_biUnion
#print axioms HPC.Plane.isPolygonal_iUnion_finset_of_pairs
#print axioms HPC.Plane.continuous_crossG
#print axioms HPC.Plane.continuous_linePt
#print axioms HPC.Plane.crossG_linePt
#print axioms HPC.Plane.dist_linePt
#print axioms HPC.Plane.linePt_injective
#print axioms HPC.Plane.exists_linePt_of_crossG
#print axioms HPC.Plane.crossG_eq_zero_of_two
#print axioms HPC.Plane.linePt_image_Icc
#print axioms HPC.Plane.zero_mem_specialParams
#print axioms HPC.Plane.one_mem_specialParams
#print axioms HPC.Plane.crossG_of_not_special
#print axioms HPC.Plane.mem_segment_iff_linePt
#print axioms HPC.Plane.mem_closure_halfDisks
#print axioms HPC.Plane.convex_crossG_pos
#print axioms HPC.Plane.convex_crossG_neg
#print axioms HPC.Plane.eventually_mem_closure_of_not_special
#print axioms HPC.Plane.isPolygonal_segment_inter_closure
#print axioms HPC.Plane.isPolygonal_inter_closure_inter
#print axioms HPC.Plane.linePt_affine
#print axioms HPC.Plane.convex_segParams
#print axioms HPC.Plane.isClosed_segParams
#print axioms HPC.Plane.isPolygonal_segment_inter_segment
#print axioms HPC.Plane.IsPolygonal.inter
#print axioms HPC.Plane.isPolygonal_segment_inter
#print axioms HPC.Plane.specialParams_subset
#print axioms HPC.Plane.mem_segment_of_gap
#print axioms HPC.Plane.linePt_image_Ioo
#print axioms HPC.Plane.exists_special_gap
#print axioms HPC.Plane.exists_open_pieces_of_saturated

-- PolygonalPoly.lean
#print axioms HPC.Plane.isPolygonal_polygonOf
#print axioms HPC.Plane.IsSimpleClosedPolygon.isPolygonal
#print axioms HPC.Plane.isSaturated_polyInterior
#print axioms HPC.Plane.isPolygonal_inter_closure_polyInterior
#print axioms HPC.Plane.IsSaturated.inter
#print axioms HPC.Plane.isPolygonal_inter_closure_polyInterior₃
#print axioms HPC.Plane.isPolygonal_frontier_inter_closure

-- JanPoly.lean
#print axioms HPC.Plane.isPreconnected_ball_diff_singleton
#print axioms HPC.Plane.isConnected_diff_singleton_of_isOpen
#print axioms HPC.Plane.separatesPts_insert_iff
#print axioms HPC.Plane.separatesPts_union_finite_iff
#print axioms HPC.Plane.isPolygonal_iff_graphSet
#print axioms HPC.Plane.IsPolygonal.exists_split
#print axioms HPC.Plane.subset_singleton_of_isolated
#print axioms HPC.Plane.exists_isolating_nbhd
#print axioms HPC.Plane.inter_split_connected
#print axioms HPC.Plane.janiszewski_polygonal
#print axioms HPC.Plane.polyInterior_local_halfDisk
#print axioms HPC.Plane.isPolygonal_segment_inter_polygon
#print axioms HPC.Plane.exists_open_pieces
#print axioms HPC.Plane.planeFacts_of_enclose

-- edited in batch 129
#print axioms HPC.Plane.PlaneFacts.crosscut'
#print axioms HPC.Plane.PlaneFacts.exists_theta_point
#print axioms HPC.Plane.compFamily_no_circular
#print axioms HPC.Plane.treeChain_of_cover
#print axioms HPC.Plane.theorem7_1951
#print axioms HPC.Plane.theorem6_1951
#print axioms HPC.Plane.theorem7_weak
#print axioms HPC.Plane.planeFacts_of_enclose_janiszewski

-- still open
#print axioms HPC.Plane.fugate_cor1
