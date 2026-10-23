import HPC.Moore.M19CD

-- Batch 141: `#print axioms` for every new theorem (`HPC/Moore/M19CD*.lean`, `M19CRefute.lean`). Output: `axioms-batch141.txt`.
-- `HPC/Moore/M19CDDefs.lean`
-- `HPC/Moore/M19CDTile.lean`
#print axioms HPC.Moore.split_interior
#print axioms HPC.Moore.Space.Tiling.add_arc
#print axioms HPC.Moore.Space.Tiling.add_arc_finite
#print axioms HPC.Moore.Space.Tiling.components
-- `HPC/Moore/M19CDCells.lean`
#print axioms HPC.Moore.Space.InOrder.nodup_subset
#print axioms HPC.Moore.Space.InOrder.mid
#print axioms HPC.Moore.Space.Quad.sAB_sub
#print axioms HPC.Moore.Space.Quad.sBC_sub
#print axioms HPC.Moore.Space.Quad.sCD_sub
#print axioms HPC.Moore.Space.Quad.sDA_sub
#print axioms HPC.Moore.Space.DoubleRuling.X_inj
#print axioms HPC.Moore.Space.DoubleRuling.X_mem
#print axioms HPC.Moore.Space.DoubleRuling.X'_mem
#print axioms HPC.Moore.Space.DoubleRuling.Y_mem
#print axioms HPC.Moore.Space.DoubleRuling.Y'_mem
#print axioms HPC.Moore.Space.DoubleRuling.arcX_inter
#print axioms HPC.Moore.Space.DoubleRuling.arcY_inter
#print axioms HPC.Moore.Space.DoubleRuling.cross_mem
#print axioms HPC.Moore.Space.DoubleRuling.cross_unique
#print axioms HPC.Moore.Space.DoubleRuling.cross_ne
#print axioms HPC.Moore.Space.DoubleRuling.GX_succ
#print axioms HPC.Moore.Space.DoubleRuling.GY_succ
#print axioms HPC.Moore.Space.DoubleRuling.GY_m
#print axioms HPC.Moore.Space.DoubleRuling.tiling
#print axioms HPC.Moore.Space.DoubleRuling.cells_eq
#print axioms HPC.Moore.doubleRuling_cell
#print axioms HPC.Moore.doubleRuling_cells_ncard
-- `HPC/Moore/M19CRefute.lean`
#print axioms HPC.Moore.no_ruling_of_two_branches
#print axioms HPC.Moore.quad_of_params
#print axioms HPC.Moore.tangent_configuration
#print axioms HPC.Moore.not_m19_theoremC_printed
-- `HPC/Moore/M19CDSplit.lean`
#print axioms HPC.Moore.inter_eq_singleton_of_sub
#print axioms HPC.Moore.inter_eq_empty_of_sub
#print axioms HPC.Moore.union_shuffle_A
#print axioms HPC.Moore.union_shuffle_B
#print axioms HPC.Moore.union_shuffle_J
#print axioms HPC.Moore.union_rot4
#print axioms HPC.Moore.mem_image_Icc_iff
#print axioms HPC.Moore.split_interior_of
#print axioms HPC.Moore.Space.Quad.rot
#print axioms HPC.Moore.Space.Quad.disjoint_I_J
#print axioms HPC.Moore.Space.Quad.splitX
-- `HPC/Moore/M19CDRuling.lean`
#print axioms HPC.Moore.Space.XArc.symm
#print axioms HPC.Moore.Space.XArc.mono
#print axioms HPC.Moore.Space.ArcRuling.rot
#print axioms HPC.Moore.Space.cellsOf_mono
#print axioms HPC.Moore.connectedComponentIn_union_left
#print axioms HPC.Moore.Space.cellsOf_union
#print axioms HPC.Moore.Space.Quad.exists_cut
#print axioms HPC.Moore.Space.Quad.refl
#print axioms HPC.Moore.Space.Quad.notMem_of_ab
#print axioms HPC.Moore.Space.Quad.notMem_of_bc
#print axioms HPC.Moore.Space.Quad.notMem_of_cd
#print axioms HPC.Moore.Space.Quad.notMem_of_da
#print axioms HPC.Moore.Space.XArc.inter_J
#print axioms HPC.Moore.Space.ArcRuling.rule_refl
#print axioms HPC.Moore.Space.ArcRuling.side_of_cut
#print axioms HPC.Moore.Space.ArcRuling.restrict_half
-- `HPC/Moore/M19CDCut.lean`
#print axioms HPC.Moore.Space.Quad.Cut.s₁_sub
#print axioms HPC.Moore.Space.Quad.Cut.s₂_sub
#print axioms HPC.Moore.Space.Quad.Cut.t₁_sub
#print axioms HPC.Moore.Space.Quad.Cut.t₂_sub
#print axioms HPC.Moore.Space.Quad.Cut.single
#print axioms HPC.Moore.Space.Quad.Cut.B_notMem_s₁
#print axioms HPC.Moore.Space.Quad.Cut.A_notMem_s₂
#print axioms HPC.Moore.Space.Quad.Cut.C_notMem_t₁
#print axioms HPC.Moore.Space.Quad.Cut.D_notMem_t₂
#print axioms HPC.Moore.Space.Quad.Cut.IA_sub
#print axioms HPC.Moore.Space.Quad.Cut.IB_sub
#print axioms HPC.Moore.Space.Quad.Cut.IA_open
#print axioms HPC.Moore.Space.Quad.Cut.IB_open
#print axioms HPC.Moore.Space.Quad.Cut.closure_IA
#print axioms HPC.Moore.Space.Quad.Cut.closure_IB
#print axioms HPC.Moore.Space.Quad.Cut.inter_cl
#print axioms HPC.Moore.Space.Quad.Cut.closure_IB_disjoint_DA
#print axioms HPC.Moore.Space.Quad.Cut.closure_IA_disjoint_BC
#print axioms HPC.Moore.Space.Quad.Cut.restrictA
#print axioms HPC.Moore.Space.Quad.Cut.restrictB
#print axioms HPC.Moore.Space.Quad.Cut.sideA
#print axioms HPC.Moore.Space.Quad.Cut.sideB
#print axioms HPC.Moore.Space.Quad.Cut.X_eq
#print axioms HPC.Moore.Space.Quad.Cut.carrier_iffA
#print axioms HPC.Moore.Space.Quad.Cut.carrier_iffB
#print axioms HPC.Moore.Space.Quad.Cut.diff_eq
-- `HPC/Moore/M19CDGlue.lean`
#print axioms HPC.Moore.Space.XArc.sub_cl
#print axioms HPC.Moore.Space.Quad.Cut.yA_cl
#print axioms HPC.Moore.Space.Quad.Cut.yB_cl
#print axioms HPC.Moore.Space.Quad.Cut.yA_spec
#print axioms HPC.Moore.Space.Quad.Cut.yB_spec
#print axioms HPC.Moore.Space.Quad.Cut.wA_spec
#print axioms HPC.Moore.Space.Quad.Cut.wB_spec
#print axioms HPC.Moore.Space.Quad.Cut.x_inter_J
#print axioms HPC.Moore.Space.Quad.Cut.x_mid_I
#print axioms HPC.Moore.Space.Quad.Cut.pair_spec
#print axioms HPC.Moore.Space.Quad.Cut.glue
#print axioms HPC.Moore.Space.Quad.Cut.glue_carrier_iffA
#print axioms HPC.Moore.Space.Quad.Cut.glue_carrier_iffB
-- `HPC/Moore/M19CDExt.lean`
#print axioms HPC.Moore.Space.ArcRuling.mono
#print axioms HPC.Moore.Space.ArcRuling.empty
#print axioms HPC.Moore.Space.ArcRuling.insert_of_disj
#print axioms HPC.Moore.Space.Quad.Cut.x_sub_clA
#print axioms HPC.Moore.Space.Quad.Cut.x_sub_clB
#print axioms HPC.Moore.Space.Quad.Cut.sub_cl_union
#print axioms HPC.Moore.Space.Quad.Cut.y_eq
#print axioms HPC.Moore.extend_base
#print axioms HPC.Moore.extend_stepX
#print axioms HPC.Moore.extend_stepY
#print axioms HPC.Moore.extendsBelow
#print axioms HPC.Moore.Space.ArcRuling.extendY
#print axioms HPC.Moore.Space.ArcRuling.extendY_finite
-- `HPC/Moore/M19CDRefine.lean`
#print axioms HPC.Moore.Space.ArcRuling.isClosed_carrier
#print axioms HPC.Moore.Space.cellsOf_forall_mono
#print axioms HPC.Moore.Space.Quad.Cut.cells_split
#print axioms HPC.Moore.refine_stepX
#print axioms HPC.Moore.refinesBelow
#print axioms HPC.Moore.Space.ArcRuling.refine
-- `HPC/Moore/M19CDOrder.lean`
#print axioms HPC.Moore.Space.XArc.param
#print axioms HPC.Moore.Space.Quad.exists_cut_param
#print axioms HPC.Moore.Space.ArcRuling.param_mono
#print axioms HPC.Moore.pairwise_ends
#print axioms HPC.Moore.Space.ArcRuling.sortX
#print axioms HPC.Moore.Space.DoubleRuling.toArcRuling
#print axioms HPC.Moore.Space.DoubleRuling.carrier_eq
#print axioms HPC.Moore.Space.DoubleRuling.cells_eq_cellsOf
#print axioms HPC.Moore.Space.ArcRuling.toDoubleRuling
-- `HPC/Moore/M19CDMain.lean`
#print axioms HPC.Moore.exists_mem_openArc_notMem
#print axioms HPC.Moore.Space.ArcRuling.finite_inter_J
#print axioms HPC.Moore.Space.ArcRuling.padY
#print axioms HPC.Moore.Space.ArcRuling.padX
#print axioms HPC.Moore.Space.ArcRuling.toDoubleRuling'
#print axioms HPC.Moore.Space.DoubleRuling.arcX_injective
#print axioms HPC.Moore.Space.DoubleRuling.arcY_injective
#print axioms HPC.Moore.doubleRuling_pad
#print axioms HPC.Moore.doubleRuling_refine
-- `HPC/Moore/M19CDRegion.lean`
#print axioms HPC.Moore.m19_theoremD_regions_of_curves
