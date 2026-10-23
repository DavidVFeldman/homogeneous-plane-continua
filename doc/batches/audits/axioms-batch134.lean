import HPC

-- batch 134 audit: every theorem and instance of HPC/Effros/Fat.lean, OpenMapping.lean,
-- HomeoGroup.lean and Effros.lean

-- `HPC/Effros/Fat.lean`
#print axioms HPC.Effros.IsFat.mono
#print axioms HPC.Effros.NowhereMeagre.diff_meagre
#print axioms HPC.Effros.NowhereMeagre.inter_diff_nonempty
#print axioms HPC.Effros.IsFat.diff_meagre
#print axioms HPC.Effros.nonempty_interior_closure_of_not_meagre
#print axioms HPC.Effros.diam_closure_tendsto
#print axioms HPC.Effros.exists_mem_closure_nested
#print axioms HPC.Effros.coreGood_step
#print axioms HPC.Effros.exists_seq_of_step
#print axioms HPC.Effros.exists_eq_of_core
#print axioms HPC.Effros.exists_reduced_param
#print axioms HPC.Effros.NowhereMeagre.closure_subset_closure_diff
#print axioms HPC.Effros.inter_nonempty_of_nowhereMeagre
#print axioms HPC.Effros.inter_nonempty_of_isFat
#print axioms HPC.Effros.isFat_empty_of_isEmpty

-- `HPC/Effros/OpenMapping.lean`
#print axioms HPC.Effros.exists_vanMill_basis
#print axioms HPC.Effros.mem_orbitPart
#print axioms HPC.Effros.vanMill_3_1
#print axioms HPC.Effros.isMeagre_smul_image
#print axioms HPC.Effros.vanMill_3_2
#print axioms HPC.Effros.vanMill_3_3
#print axioms HPC.Effros.vanMill_3_4
#print axioms HPC.Effros.vanMill_3_4_dense
#print axioms HPC.Effros.vanMill_3_5
#print axioms HPC.Effros.effros_open_mapping
#print axioms HPC.Effros.isOpenMap_smul_left
#print axioms HPC.Effros.isOpen_orbitPart

-- `HPC/Effros/HomeoGroup.lean`
#print axioms HPC.Effros.homeoGroup
#print axioms HPC.Effros.homeoMulAction
#print axioms HPC.Effros.homeo_inv_def
#print axioms HPC.Effros.isInducing_homeoEmb
#print axioms HPC.Effros.homeoEmb_injective
#print axioms HPC.Effros.continuous_homeoEmb
#print axioms HPC.Effros.homeo_isTopologicalGroup
#print axioms HPC.Effros.homeo_continuousSMul
#print axioms HPC.Effros.range_homeoEmb
#print axioms HPC.Effros.isClosed_range_homeoEmb
#print axioms HPC.Effros.isClosedEmbedding_homeoEmb
#print axioms HPC.Effros.homeo_polishSpace
#print axioms HPC.Effros.bddAbove_move
#print axioms HPC.Effros.dist_le_supMove
#print axioms HPC.Effros.supMove_nonneg
#print axioms HPC.Effros.supMove_le
#print axioms HPC.Effros.supMove_eq_dist
#print axioms HPC.Effros.supMove_symm
#print axioms HPC.Effros.supMove_inv
#print axioms HPC.Effros.supMove_symm_trans_le
#print axioms HPC.Effros.supMove_mul_le
#print axioms HPC.Effros.hasBasis_supMove
#print axioms HPC.Effros.supMove_ball_mem_nhds

-- `HPC/Effros/Effros.lean`
#print axioms HPC.Effros.effros_homogeneous
#print axioms HPC.Effros.effros_homogeneous_set
