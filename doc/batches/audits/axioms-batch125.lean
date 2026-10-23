import HPC

-- batch 125 audit: every theorem of HPC/Plane/Jct1.lean and HPC/Fold/Theorem4Ge4.lean, and
-- `fugate_cor1` (still open)

-- Jct1.lean
#print axioms HPC.Plane.straddle_iff_xor
#print axioms HPC.Plane.crossesEast_iff_xor
#print axioms HPC.Plane.crossFun_continuous
#print axioms HPC.Plane.crossesEast_comm
#print axioms HPC.Plane.mem_segment_of_straddle
#print axioms HPC.Plane.fst_eq_of_mem_segment
#print axioms HPC.Plane.mem_segment_of_horizontal
#print axioms HPC.Plane.not_crossesEast_of_mem
#print axioms HPC.Plane.ceInd_congr
#print axioms HPC.Plane.ceInd_comm
#print axioms HPC.Plane.zmod2_add_self
#print axioms HPC.Plane.zmod2_eq_of_add_eq_zero
#print axioms HPC.Plane.eventually_height
#print axioms HPC.Plane.eventually_sign
#print axioms HPC.Plane.iff_of_height
#print axioms HPC.Plane.sign_iff
#print axioms HPC.Plane.crossesEast_jump_end
#print axioms HPC.Plane.crossesEast_jump
#print axioms HPC.Plane.ceInd_eventually_eq
#print axioms HPC.Plane.crossesEast_locallyConstant_of_ne
#print axioms HPC.Plane.parity_eq_sum
#print axioms HPC.Plane.next_eq_finRotate
#print axioms HPC.Plane.sum_vJump_telescope
#print axioms HPC.Plane.not_mem_edge_of_not_mem
#print axioms HPC.Plane.parity_eventually_eq
#print axioms HPC.Plane.parity_locallyConstant
#print axioms HPC.Plane.parity_eq_of_isPreconnected
#print axioms HPC.Plane.fst_le_max_of_mem_segment
#print axioms HPC.Plane.parity_far
#print axioms HPC.Plane.polygonOf_subset_closedBall
#print axioms HPC.Plane.isClosed_polygonOf
#print axioms HPC.Plane.parity_eq_zero_of_far'
#print axioms HPC.Plane.parity_eq_zero_of_far
#print axioms HPC.Plane.not_mem_polyEdge_of_ne
#print axioms HPC.Plane.exists_parity_flip
#print axioms HPC.Plane.prev_val_eq
#print axioms HPC.Plane.next_val_eq
#print axioms HPC.Plane.exists_nonhorizontal_edge
#print axioms HPC.Plane.isOpen_parity_set
#print axioms HPC.Plane.polygon_separates
#print axioms HPC.Fold.theorem4_literal_ge4
#print axioms HPC.Fold.theorem4LiteralGe4_holds
-- Theorem4Ge4.lean
#print axioms HPC.Fold.Recon123.seg3Z
#print axioms HPC.Fold.Recon123.genG_lip4
#print axioms HPC.Fold.Recon123.genWin_spec4
#print axioms HPC.Fold.Recon123.two_coreZ
#print axioms HPC.Fold.Recon123.two_modelZ_lt
#print axioms HPC.Fold.Recon123.OnlyM.of_flip
#print axioms HPC.Fold.Recon123.two_modelZ
#print axioms HPC.Fold.onlyIn_of_meet
#print axioms HPC.Fold.onlyIn_of_onlyM
#print axioms HPC.Fold.theorem4_literal_ge4_model
-- open target
#print axioms HPC.Plane.fugate_cor1
