import HPC
import HPCExtra

/-!
# Axiom audit

`#print axioms` for the main list of the repository, grouped by source (one `-- ##` heading per
paper or batch, from Bing 1948 to Bing–Jones 1959 and the direct proof of Bing 1951 Theorem 6).
The file imports the libraries `HPC` (the classification and its import closure) and `HPCExtra`
(the modules outside that closure), since some listed declarations, among them counterexamples
cited by the ledgers, live in `HPCExtra`. The output is `axioms.txt`; regenerate it with
`lake env lean Axioms.lean > axioms.txt` after `lake build HPC HPCExtra`. Every listed
declaration must show `[propext, Classical.choice, Quot.sound]` or a subset of it. The two last
groups, `Open targets (class C)` and `Consequences of open targets`, are empty and are kept as
headings only.
-/

-- ## Bing 1948
-- Theorem 1
#print axioms HPC.Chain.isCrookedIn'_of_isConsolidationOf
-- Theorem 2
#print axioms HPC.Chain.isCrookedIn'_of_refines
-- Theorem 3
#print axioms HPC.Fold.theorem3
-- Theorem 3 in Bing's two-link form with his end clause, without the only-clause (batch 123)
#print axioms HPC.Fold.theorem3_bing
-- Theorem 3 with the end-link clause, three-link form (proved in batch 123)
#print axioms HPC.Fold.theorem3_end
#print axioms HPC.Fold.theorem3_end_of_bing
-- Theorem 4
#print axioms HPC.Fold.theorem4
#print axioms HPC.Fold.theorem4_pair
-- Theorem 4 in Bing's two-link form, without the only-clauses (batch 123)
#print axioms HPC.Fold.theorem4_two
#print axioms HPC.Fold.theorem4_of_two
-- Theorem 4 as printed: refuted in the degenerate case m = 3, r = s (batch 123)
#print axioms HPC.Fold.not_theorem4Literal
-- Theorem 4 as printed with at least four coarse links: proved (batch 125)
#print axioms HPC.Fold.Recon123.two_modelZ
#print axioms HPC.Fold.onlyIn_of_onlyM
#print axioms HPC.Fold.theorem4_literal_ge4
#print axioms HPC.Fold.theorem4LiteralGe4_holds
-- Theorem 5
#print axioms HPC.Description.theorem5
-- Theorem 6
#print axioms HPC.Description.theorem6
-- Theorem 7
#print axioms HPC.Fold.theorem7
#print axioms HPC.Fold.theorem7_minimal
-- Theorem 8 (corrected)
#print axioms HPC.Fold.theorem8
-- Theorem 8 as printed: refuted
#print axioms HPC.Fold.not_theorem8_literal
-- Theorem 9
#print axioms HPC.Fold.theorem9
-- Theorem 10
#print axioms HPC.Description.theorem10
-- Theorem 11
#print axioms HPC.MatchingCovers.exists_homeomorph
-- Theorem 12
#print axioms HPC.theorem12
-- Theorem 12 (description form)
#print axioms HPC.Description.exists_homeomorph
-- Theorem 13
#print axioms HPC.Description.theorem13
#print axioms HPC.Description.exists_description_from
-- Theorem 15 from Theorem 14
#print axioms HPC.Description.theorem15_of_theorem14
-- Theorem 14: the covering step, by Lehner's Lemma 3 (n = 2) (batch 114)
#print axioms HPC.Description.covering_step
#print axioms HPC.Description.exists_description_covering
-- Lehner's Lemma 3 (n = 2) and its ingredients (batch 114; listed in batch 116)
#print axioms HPC.lehner_lemma3_two
#print axioms HPC.isPseudoArc_of_subcontinuum
#print axioms HPC.not_mem_composant_of_irreducible
#print axioms HPC.exists_epsChain_of_irreducible
#print axioms HPC.Chain.IsConsolidationOf.trans
#print axioms HPC.exists_description_consolidating
#print axioms HPC.Lehner.exists_eq_of_lip
#print axioms HPC.Lehner.dist_le_of_near
#print axioms HPC.Lehner.blocks
#print axioms HPC.Lehner.indices
#print axioms HPC.Lehner.core
-- Theorem 14 (batch 115): the A-covering step and description, tracked patterns, the three-piece
-- follower, the tracked alternating construction
#print axioms HPC.Description.covering_stepA
#print axioms HPC.Description.exists_description_coveringA
#print axioms HPC.Description.theorem5_gen
#print axioms HPC.Chain.threePiece
#print axioms HPC.exists_trackedPattern_of_refines
#print axioms HPC.exists_tracked_follower
#print axioms HPC.exists_homeomorph_tracked
-- further batch-115 results named in its report (listed in batch 116)
#print axioms HPC.lehner_lemma3_twoA
#print axioms HPC.Description.exists_description_of_steps'
#print axioms HPC.Chain.exists_link_le_of_subset_span
#print axioms HPC.Carries.pos_of_lt
#print axioms HPC.exists_tracked_refinement
#print axioms HPC.TRung.exists_base
#print axioms HPC.TRung.exists_next
-- Theorem 14
#print axioms HPC.Description.theorem14
-- Theorem 15
#print axioms HPC.Description.theorem15
-- existence of a pseudo-arc in the plane
#print axioms HPC.Plane.pseudoArc_exists

-- ## Bing 1951 (Duke)
-- Theorem 1
#print axioms HPC.Plane.theorem1_snake
-- Theorem 2, in the plane (batch 110)
#print axioms HPC.Plane.isGδ_snakeLike
#print axioms HPC.Plane.dense_snakeLike_plane
#print axioms HPC.Plane.theorem2_1951_plane
-- Theorem 2 (batch 113)
#print axioms HPC.Plane.theorem2_1951
-- Theorem 4
#print axioms HPC.Plane.theorem4
-- Theorem 5 (batch 107)
#print axioms HPC.Plane.theorem5_1951
#print axioms HPC.Plane.theorem5_1951_uncountable
-- Theorem 8 (form proved)
#print axioms HPC.Plane.theorem8_1951'
-- Theorem 9
#print axioms HPC.Plane.theorem9_1951
-- Theorem 10
#print axioms HPC.Plane.theorem10_1951
#print axioms HPC.Plane.isSnakeLike_of_subcontinuum
-- Theorem 11, necessity
#print axioms HPC.Plane.isAtriodic_of_isSnakeLike
-- Theorem 11, necessity
#print axioms HPC.Plane.isHereditarilyUnicoherent_of_isSnakeLike
-- Theorem 11 under two hypotheses (kept, see report)
#print axioms HPC.Plane.theorem11_1951_of_T10
#print axioms HPC.Plane.theorem11_1951_iff_of_T10
-- Theorem 11 (Fugate 1969, Theorem 2 Case II)
#print axioms HPC.Plane.theorem11_1951
#print axioms HPC.Plane.theorem11_1951_iff
-- Fugate 1969, Lemma 4 (hereditarily decomposable case)
#print axioms HPC.Plane.exists_terminal_point_of_isTerminalSub
-- Fugate 1969, Lemma 3
#print axioms HPC.Plane.isTerminalSub_of_union_terminal
-- Fugate 1969, Claim 1
#print axioms HPC.Plane.claim1_contains_inter
-- Fugate 1969, amalgamated chain
#print axioms HPC.Plane.epsCoverable_of_halves
-- Theorem 12, A => B
#print axioms HPC.Plane.condB_of_condA
-- Theorem 13, necessity
#print axioms HPC.Plane.condB_of_endPoint
-- Theorem 13, sufficiency
#print axioms HPC.Plane.endPoint_of_condA
-- Theorem 14
#print axioms HPC.Plane.theorem14_1951
-- Theorem 12, B => A, and Theorem 12 (batch 106)
#print axioms HPC.Plane.condA_of_condB
#print axioms HPC.Plane.theorem12_1951
-- Theorem 12, B => A, and Theorem 12, for any M (Bing's proof via the arcs paper's Theorem 5; batch 108)
#print axioms HPC.Plane.condA_of_condB_general
#print axioms HPC.Plane.theorem12_1951_general
-- Theorem 13 in full (batch 106)
#print axioms HPC.Plane.theorem13_1951
#print axioms HPC.Plane.theorem13_1951'
-- Two end points of a hereditarily decomposable snake-like continuum (p. 661; batch 106)
#print axioms HPC.Plane.exists_two_endPoints_irreducible
#print axioms HPC.Plane.exists_oppositeEndPoints_of_hd
-- Theorem 15
#print axioms HPC.Plane.theorem15_1951
#print axioms HPC.Plane.isPseudoArc_iff_endPoints
#print axioms HPC.Plane.exists_two_endElts
#print axioms HPC.Plane.organ_isSnakeLike

-- ## Bing 1948, Amer. J. Math. (arcs paper; batch 108)
-- irreducible subcontinuum about a set (Zorn)
#print axioms HPC.Plane.exists_irreducibleAbout
-- Theorem 5
#print axioms HPC.Plane.arcs_theorem5
#print axioms HPC.Plane.arcs_theorem5_point
-- Corollary 2
#print axioms HPC.Plane.arcs_corollary2

-- ## Bing 1951 (Pacific)
#print axioms HPC.Plane.theorem1_HIC
#print axioms HPC.Plane.pseudoArc_unique
#print axioms HPC.Plane.homogeneous_of_isPseudoArc
#print axioms HPC.Plane.isGδ_pseudoArcs
#print axioms HPC.Plane.dense_pseudoArcs_of
#print axioms HPC.Plane.theorem2_HIC_of
#print axioms HPC.Plane.theorem3_HIC
#print axioms HPC.Plane.theorem3_HIC_bing
#print axioms HPC.Plane.theorem4_HIC
-- density lemma, batch 109
#print axioms HPC.Plane.stripSet_eq
#print axioms HPC.Plane.isThreadedChain_of_isTameChain
#print axioms HPC.Plane.exists_pseudoArc_in_threadedChain
#print axioms HPC.Plane.geomLemma'_of_geomLemma
#print axioms HPC.Plane.dense_pseudoArcs_of'
#print axioms HPC.Plane.theorem2_HIC_of'
#print axioms HPC.Plane.stretchTri_subset_ball
#print axioms HPC.Plane.stretchTri_subset_thickening
#print axioms HPC.Plane.stretchTri_separated
#print axioms HPC.Plane.roundedPath_continuousOn
#print axioms HPC.Plane.roundedNormal_continuousOn
#print axioms HPC.Plane.norm_roundedNormal
#print axioms HPC.Plane.roundedPath_mem_stretchTri
#print axioms HPC.Plane.band_injOn
#print axioms HPC.Plane.band_continuousOn
#print axioms HPC.Plane.latticeChain_link
#print axioms HPC.Plane.isThreadedChain_latticeChain
#print axioms HPC.Plane.exists_threadedChain_of_latticePath
-- density lemma, batch 110
#print axioms HPC.Plane.exists_connected_enumeration
#print axioms HPC.Plane.exists_latticeCycle
#print axioms HPC.Plane.exists_latticeCycle'
#print axioms HPC.Plane.exists_latticePath_of_polyomino
#print axioms HPC.Plane.exists_orthonormal_pair_span
#print axioms HPC.Plane.squaresMeeting_finite
#print axioms HPC.Plane.exists_sq_mem
#print axioms HPC.Plane.diam_sqSet_le
#print axioms HPC.Plane.latticePt_mem_sqSet
#print axioms HPC.Plane.squaresMeeting_connected
#print axioms HPC.Plane.geomLemma'_of_finrank_two
#print axioms HPC.Plane.dense_pseudoArcs_plane
#print axioms HPC.Plane.theorem2_HIC_plane
-- density lemma, batch 112
#print axioms HPC.Plane.stretchTriN_subset_ball
#print axioms HPC.Plane.stretchTriN_subset_thickening
#print axioms HPC.Plane.stretchTriN_separated
#print axioms HPC.Plane.continuous_plPathN
#print axioms HPC.Plane.plPathN_mem_stretchTriN
#print axioms HPC.Plane.plPathN_injOn
#print axioms HPC.Plane.norm_diagDir
#print axioms HPC.Plane.diagDir_not_mem_span
#print axioms HPC.Plane.continuous_bandN
#print axioms HPC.Plane.bandN_injOn
#print axioms HPC.Plane.exists_threadedChain_of_latticePathN
#print axioms HPC.Plane.exists_finiteDimensional_subspace_near
#print axioms HPC.Plane.exists_threadedChain_pullback
#print axioms HPC.Plane.geomLemma'_of_subspaces
-- density lemma, batch 113
#print axioms HPC.Plane.exists_cubeLoop_two
#print axioms HPC.Plane.exists_cubeLoop_succ
#print axioms HPC.Plane.exists_cubeLoop
#print axioms HPC.Plane.exists_latticeCycleN
#print axioms HPC.Plane.exists_latticePathN_of_cubes
#print axioms HPC.Plane.exists_orthonormal_basis_fin
#print axioms HPC.Plane.cubesMeeting_finite
#print axioms HPC.Plane.exists_cube_mem
#print axioms HPC.Plane.diam_cubeSet_le
#print axioms HPC.Plane.latticePtN_mem_cubeSet
#print axioms HPC.Plane.cubesMeeting_connected
#print axioms HPC.Plane.geomLemma'_of_finrank_ge_three
#print axioms HPC.Plane.geomLemma'_of_finrank
-- further batch-113 results named in its report (listed in batch 116)
#print axioms HPC.Plane.CubeLoopAux.fwd_edge
#print axioms HPC.Plane.CubeLoopAux.exists_isOpenedLoop
#print axioms HPC.Plane.CubeLoopAux.exists_two_free_edges
#print axioms HPC.Plane.exists_cubeLoop_ge
#print axioms HPC.Plane.CCyc.side_eq
#print axioms HPC.Plane.CCyc.pair_eq
#print axioms HPC.Plane.CCyc.A_tr_opp
#print axioms HPC.Plane.CCyc.B_tr_opp
#print axioms HPC.Plane.CCyc.inv_rot
#print axioms HPC.Plane.CCyc.inv_splice
#print axioms HPC.Plane.CCyc.inv_base
#print axioms HPC.Plane.CCyc.inv_grow
#print axioms HPC.Plane.CCyc.exists_inv_sub
#print axioms HPC.Plane.CCyc.exists_inv
#print axioms HPC.Plane.exists_latticeCycleN_of_loop
-- Theorem 2 (batch 113): the density lemma in dimension >= 2 and its consequences
#print axioms HPC.Plane.geomLemma'_of_two_le_rank
#print axioms HPC.Plane.dense_pseudoArcs
#print axioms HPC.Plane.theorem2_HIC

-- ## Fugate 1966
#print axioms HPC.Plane.fugate_lemma1
#print axioms HPC.Plane.fugate_lemma2'
#print axioms HPC.Plane.fugate_lemma4
-- class B rename
#print axioms HPC.Plane.fugate_theorem1_sufficiency
-- class B rename
#print axioms HPC.Plane.fugate_theorem1
#print axioms HPC.Plane.fugate_cor1_iff
-- class B rename
#print axioms HPC.Plane.fugate_cor2
-- class B rename
#print axioms HPC.Plane.isTerminalSub_iff_irreducible

-- ## Nadler
#print axioms HPC.Plane.exists_two_nonCutPoints
#print axioms HPC.Plane.not_subset_of_nonCutPoints
#print axioms HPC.Plane.sorgenfrey
#print axioms HPC.Plane.irreducible_iff_not_isTriod
-- class B rename
#print axioms HPC.Plane.exists_irreducibleBetween_of_atriodic
#print axioms HPC.Plane.isHereditarilyUnicoherent_union
#print axioms HPC.Plane.isUnicoherent_univ_of_contraction

-- ## Refutations (ledger certificates)
#print axioms HPC.Fold.theorem4_two_degenerate_false
#print axioms HPC.Fold.not_theorem4Literal
#print axioms HPC.Fold.not_theorem4LiteralND
#print axioms HPC.Fold.not_exitReach
#print axioms HPC.Fold.not_highExitValleyOpen
#print axioms HPC.Fold.not_lowExitPeak
#print axioms HPC.Fold.not_highExitValley
#print axioms HPC.Fold.not_f2Prime
#print axioms HPC.Fold.not_exitReachTight
#print axioms HPC.Fold.not_highExitValleyOpenTight
#print axioms HPC.Fold.not_lowExitPeakTight
#print axioms HPC.Fold.not_highExitValleyTight
#print axioms HPC.Fold.not_f2PrimeTight
#print axioms HPC.Fold.not_f2PrimeFree
#print axioms HPC.Fold.not_exitReachF
#print axioms HPC.Fold.not_f2PrimeF
#print axioms HPC.Fold.not_highExitValleyF
#print axioms HPC.Fold.not_lowExitPeakF
#print axioms HPC.Fold.not_cutData
#print axioms HPC.Fold.not_exists_cutData_cutSeq
#print axioms HPC.Fold.not_offDichotomy
#print axioms HPC.Fold.not_f2PrimeOff_of_faithful
#print axioms HPC.Fold.not_extendStepMin
#print axioms HPC.Fold.not_s3Zig
#print axioms HPC.Fold.not_armTimingClaim
#print axioms HPC.Fold.not_unservedHigh8
#print axioms HPC.Fold.not_unservedCeiling
#print axioms HPC.Fold.not_unservedValley
#print axioms HPC.Fold.not_crossCeilProfile
#print axioms HPC.Fold.not_unservedProfile
#print axioms HPC.Fold.not_unservedLeg3deep
#print axioms HPC.Description.not_theorem6Pos_shift_unconditional
#print axioms HPC.Description.not_patternFollowing_unconditional
-- T3: the 1951 notion does not imply the 1948 notion
#print axioms HPC.isCrookedIn_ne_isCrookedIn'
#print axioms HPC.Fold.model_covering_fold_refuted
#print axioms HPC.Fold.model_covering_fold₃_refuted
#print axioms HPC.Fold.model_end_time_refuted
#print axioms HPC.Fold.theorem8_skeleton_false
#print axioms HPC.Plane.Counter92.Crit.bar_mem
#print axioms HPC.Plane.Counter92.Crit.hgt_mem
#print axioms HPC.Plane.Counter92.Crit.inter
#print axioms HPC.Plane.Counter92.Crit.isPreconnected
#print axioms HPC.Plane.Counter92.Crit.neg_bar
#print axioms HPC.Plane.Counter92.Crit.pos_bar
#print axioms HPC.Plane.Counter92.Crit.zero_mem
#print axioms HPC.Plane.Counter92.S₀_cases
#print axioms HPC.Plane.Counter92.S₀_eq
#print axioms HPC.Plane.Counter92.barL_subset_of_interior
#print axioms HPC.Plane.Counter92.barLe_two
#print axioms HPC.Plane.Counter92.barR_subset_of_interior
#print axioms HPC.Plane.Counter92.bar_convex
#print axioms HPC.Plane.Counter92.bar_mem_closure_C₁
#print axioms HPC.Plane.Counter92.bar_mem_closure_C₁lo
#print axioms HPC.Plane.Counter92.bar_mem_interior_C₁lo
#print axioms HPC.Plane.Counter92.bar_mem_of_neg
#print axioms HPC.Plane.Counter92.bar_mem_of_pos
#print axioms HPC.Plane.Counter92.bar_piece
#print axioms HPC.Plane.Counter92.bingElt_bar
#print axioms HPC.Plane.Counter92.bingElt_curve
#print axioms HPC.Plane.Counter92.bingElt_subtype_reverse_false
#print axioms HPC.Plane.Counter92.bingS_S₀
#print axioms HPC.Plane.Counter92.cA_mem
#print axioms HPC.Plane.Counter92.closure_C₁_subset
#print axioms HPC.Plane.Counter92.closure_C₁lo_subset
#print axioms HPC.Plane.Counter92.conflict
#print axioms HPC.Plane.Counter92.connectedSpace_S₀
#print axioms HPC.Plane.Counter92.containsNested_window
#print axioms HPC.Plane.Counter92.continuousOn_arc1
#print axioms HPC.Plane.Counter92.continuousOn_arc2
#print axioms HPC.Plane.Counter92.continuousOn_cA
#print axioms HPC.Plane.Counter92.continuous_hgt
#print axioms HPC.Plane.Counter92.continuous_xc
#print axioms HPC.Plane.Counter92.crit_bar_le
#print axioms HPC.Plane.Counter92.crit_hgt_le
#print axioms HPC.Plane.Counter92.crit_le_bar
#print axioms HPC.Plane.Counter92.crit_le_hgt
#print axioms HPC.Plane.Counter92.crit_of
#print axioms HPC.Plane.Counter92.crit_univ
#print axioms HPC.Plane.Counter92.dist_S₀
#print axioms HPC.Plane.Counter92.eq_c₁
#print axioms HPC.Plane.Counter92.eq_c₂
#print axioms HPC.Plane.Counter92.eq_of_bar
#print axioms HPC.Plane.Counter92.eq_of_hgt
#print axioms HPC.Plane.Counter92.exists_cA_eq
#print axioms HPC.Plane.Counter92.exists_height
#print axioms HPC.Plane.Counter92.exists_hgt
#print axioms HPC.Plane.Counter92.exists_ne_zero_between
#print axioms HPC.Plane.Counter92.gElt_bar
#print axioms HPC.Plane.Counter92.gElt_not_partition_S₀
#print axioms HPC.Plane.Counter92.hd_S₀
#print axioms HPC.Plane.Counter92.hgt_ge
#print axioms HPC.Plane.Counter92.hgt_le
#print axioms HPC.Plane.Counter92.hu_S₀
#print axioms HPC.Plane.Counter92.isArc_of_separatesPairs_false
#print axioms HPC.Plane.Counter92.isClosed_S₀
#print axioms HPC.Plane.Counter92.isCompact_S₀
#print axioms HPC.Plane.Counter92.isConnected_C₁
#print axioms HPC.Plane.Counter92.isContinuum_barLe
#print axioms HPC.Plane.Counter92.isContinuum_barSet
#print axioms HPC.Plane.Counter92.isContinuum_closure_C₁
#print axioms HPC.Plane.Counter92.isContinuum_closure_C₁lo
#print axioms HPC.Plane.Counter92.isContinuum_window
#print axioms HPC.Plane.Counter92.isPreconnected_C₁lo
#print axioms HPC.Plane.Counter92.isPreconnected_tail1
#print axioms HPC.Plane.Counter92.isPreconnected_tail2
#print axioms HPC.Plane.Counter92.kind
#print axioms HPC.Plane.Counter92.mem_closure_of_forall
#print axioms HPC.Plane.Counter92.mem_of_hgt
#print axioms HPC.Plane.Counter92.no_down_down
#print axioms HPC.Plane.Counter92.no_down_right
#print axioms HPC.Plane.Counter92.no_left_left
#print axioms HPC.Plane.Counter92.no_pair
#print axioms HPC.Plane.Counter92.no_right_right
#print axioms HPC.Plane.Counter92.no_up_left
#print axioms HPC.Plane.Counter92.no_up_up
#print axioms HPC.Plane.Counter92.nontrivial_S₀
#print axioms HPC.Plane.Counter92.not_isTriod
#print axioms HPC.Plane.Counter92.not_partition_S₀
#print axioms HPC.Plane.Counter92.one_le_x_of_neg
#print axioms HPC.Plane.Counter92.open_window_subset_interior
#print axioms HPC.Plane.Counter92.pre_of_ambient
#print axioms HPC.Plane.Counter92.p₀_mem_interior
#print axioms HPC.Plane.Counter92.quotient_not_t2
#print axioms HPC.Plane.Counter92.q₀_mem_gElt_p₀
#print axioms HPC.Plane.Counter92.q₀_notMem_bingElt_bar
#print axioms HPC.Plane.Counter92.theorem8_1951_false
#print axioms HPC.Plane.Counter92.theorem8_1951_false_of_bingS
#print axioms HPC.Plane.Counter92.union_piece
#print axioms HPC.Plane.Counter92.x_le_one_of_pos
#print axioms HPC.Plane.Counter92.x_le_two
#print axioms HPC.Plane.Counter92.x_nonneg
#print axioms HPC.Plane.Counter92.x₀_mem_gElt_q₀
#print axioms HPC.Plane.Counter92.x₀_not_mem_gElt_p₀
#print axioms HPC.Plane.arcs_counterexample
#print axioms HPC.Plane.bingElt_degenerate_of_isContPt_refuted
#print axioms HPC.Plane.exists_degenerate_interior_elt_refuted
#print axioms HPC.Plane.isConnected_diff_of_superset_false
#print axioms HPC.Plane.isPseudoArc_of_description_false
#print axioms HPC.Plane.isSnakeLike_union_of_terminal_refuted
#print axioms HPC.Plane.lastLink_of_minimal_skeleton_false
#print axioms HPC.Plane.miller_1_5_false
#print axioms HPC.Plane.not_separation_of_accumulates_false
#print axioms HPC.Plane.rectStepSkeleton_false
#print axioms HPC.Plane.theorem11_hdeg_refuted
#print axioms HPC.Plane.theorem12_of_false
#print axioms HPC.Plane.two_organs_counterexample
-- skeleton refutations (commission slips, not the sources'): batch 107
#print axioms HPC.Plane.not_squeeze_stdRect_subset
-- skeleton refutations (commission slips, not the sources'): batch 109
#print axioms HPC.Plane.stripSet_zero_ne
#print axioms HPC.Plane.stretchTri_subset_ball_false
#print axioms HPC.Plane.stretchTri_subset_thickening_false

-- ## Bing 1951 (Duke) §3, Theorems 6–7 — relative forms (batch 117)
-- (`PlaneFacts` proved in batch 131 (`planeFacts_holds`); the relative forms below are
-- instantiated in `Enc2.lean`. Since batch 129 `theorem6_1951_rel` and `theorem7_weak_rel` are
-- corollaries of `theorem7_1951_rel`.)
#print axioms HPC.Plane.PlaneFacts.polyInterior_eq
#print axioms HPC.Plane.interior_eq_empty_of_noSeparating
#print axioms HPC.Plane.exists_grid_offset
#print axioms HPC.Plane.finite_gridSq_meeting
#print axioms HPC.Plane.isOpen_notched
#print axioms HPC.Plane.diam_notched_le
#print axioms HPC.Plane.inter_gridSq_subset_notched
#print axioms HPC.Plane.notched_no_triple
#print axioms HPC.Plane.exists_notched_cover
#print axioms HPC.Plane.isOpen_connectedComponentIn_of_isOpen
#print axioms HPC.Plane.isCoherent_of_minimal_cover
-- skeleton refutations (commission slips, not the sources'): batch 117
#print axioms HPC.Plane.janiszewski_closed_false
#print axioms HPC.Plane.inter_gridSq_subset_notched_false

-- ## Bing 1951 (Duke) §3, Theorem 6 — relative forms (batch 118)
#print axioms HPC.Plane.exists_polyPath_of_isConnected
#print axioms HPC.Plane.exists_simplePolyArc_of_polyPath
#print axioms HPC.Plane.IsSimplePolyArc.isContinuum
#print axioms HPC.Plane.IsSimplePolyArc.split
#print axioms HPC.Plane.IsSimplePolyArc.exists_first_mem
#print axioms HPC.Plane.IsThreaded.isSimpleClosedPolygon
#print axioms HPC.Plane.exists_threaded
#print axioms HPC.Plane.polyInterior_disjoint_of_unbounded
#print axioms HPC.Plane.PlaneFacts.local_side
#print axioms HPC.Plane.PlaneFacts.sides
#print axioms HPC.Plane.PlaneFacts.exists_theta_point
#print axioms HPC.Plane.compFamily_no_triple
#print axioms HPC.Plane.compFamily_no_circular
#print axioms HPC.Plane.theorem6_1951_rel

-- ## Bing 1951 (Duke) §3, Theorem 7 — relative forms (batch 119)
-- (the unconditional items 2, the geometric parts of 1 and 3, and the arc lemmas of 4 are listed
-- here too; they do not take `PlaneFacts`)
-- item 1: the links of Theorem 6, Theorem 7 in weak form
#print axioms HPC.Plane.exists_notched_cover_param
#print axioms HPC.Plane.isBounded_notched
#print axioms HPC.Plane.isConnected_notched
#print axioms HPC.Plane.isConnected_compl_notched
#print axioms HPC.Plane.regular_notched
#print axioms HPC.Plane.PlaneFacts.polyInterior_regular
#print axioms HPC.Plane.compFamily_isBounded
#print axioms HPC.Plane.compFamily_regular
#print axioms HPC.Plane.compFamily_compl_connected
#print axioms HPC.Plane.treeChain_of_cover
#print axioms HPC.Plane.theorem7_weak_rel
-- item 2: the 20-gon (unconditional)
#print axioms HPC.Plane.isSimpleClosedPolygon_notchedPoly
#print axioms HPC.Plane.frontier_notched
#print axioms HPC.Plane.notched_eq_polyInterior
-- item 3: general position by translation
#print axioms HPC.Plane.isSimpleClosedPolygon_iff
#print axioms HPC.Plane.finite_inter_of_gp
#print axioms HPC.Plane.notched_translate
#print axioms HPC.Plane.notchedVertices_translate
#print axioms HPC.Plane.subset_translate_of_compact
#print axioms HPC.Plane.exists_gp_translation
#print axioms HPC.Plane.PlaneFacts.exists_gp_cover
-- item 4: cross-cuts
#print axioms HPC.Plane.IsSimpleClosedPolygon.split_two
#print axioms HPC.Plane.isSimpleClosedPolygon_of_arcs
#print axioms HPC.Plane.IsSimplePolyArc.isConnected_diff_ends
#print axioms HPC.Plane.PlaneFacts.crosscut

-- ## Bing 1951 (Duke) §3, Theorem 7 — relative forms (batch 120)
-- (items 1, 3, 4 take `PlaneFacts`; the decompositions of item 2 and the 20-gon facts of item 5
-- are unconditional)
-- item 1: cross-cut families and the induction
#print axioms HPC.Plane.connectedComponentIn_union_of_disjoint_open
#print axioms HPC.Plane.IsCrosscut.of_side
#print axioms HPC.Plane.PlaneFacts.components_of_crosscuts
-- item 2: decompositions
#print axioms HPC.Plane.exists_arc_decomposition
#print axioms HPC.Plane.exists_polygon_decomposition
-- item 3: the cross-cut family of `P` in `J`
#print axioms HPC.Plane.PlaneFacts.exists_crosscutFamily
-- item 4: identification and the main theorem
#print axioms HPC.Plane.subset_of_isConnected_of_disjoint_frontier
#print axioms HPC.Plane.PlaneFacts.connectedComponentIn_inter_eq
#print axioms HPC.Plane.PlaneFacts.component_inter_eq_polyInterior
-- item 5: Theorem 7
#print axioms HPC.Plane.isSimpleVertices_notchedVertices
#print axioms HPC.Plane.finite_inter_notchedPoly_of_gp
#print axioms HPC.Plane.theorem7_1951_rel

-- ## Reconnaissance, batch 121 (Bing 1948, Theorem 3 as printed; `theorem3_end`)
-- Q1: the statements and their implications
#print axioms HPC.Fold.Recon121.theorem3EndTwo_of_literal
#print axioms HPC.Fold.Recon121.theorem3LiteralOr_of_literal
#print axioms HPC.Fold.Recon121.theorem3EndStmt_of_literalOr
#print axioms HPC.Fold.Recon121.theorem3EndStmt_of_endTwo
#print axioms HPC.Fold.Recon121.theorem3Stmt_of_endStmt
#print axioms HPC.Fold.Recon121.theorem3Stmt_holds
#print axioms HPC.Fold.Recon121.endClause_or_iff
-- Q1(a): the respective reading of the end clause fails for three coarse links; the only-clause
#print axioms HPC.Fold.Recon121.not_theorem3Literal
#print axioms HPC.Fold.Recon121.k3_unforced_meeting
#print axioms HPC.Fold.Recon121.only_clause_not_automatic
#print axioms HPC.Fold.Recon121.linkChain_only
-- Q2: general chains and the model
#print axioms HPC.Fold.Recon121.exists_chain_iff_isCrookedIvF
#print axioms HPC.Fold.Recon121.meets_of_forced
#print axioms HPC.Fold.Recon121.chain_of_modelEndP
#print axioms HPC.Fold.Recon121.theorem3_end_of_model
-- Q4: Bing's special case executed literally (defect in the proof)
#print axioms HPC.Fold.Recon121.seamD_special
#print axioms HPC.Fold.Recon121.seamD_hk
#print axioms HPC.Fold.Recon121.seamD_minIdx_maxIdx
#print axioms HPC.Fold.Recon121.seam_every_H_fails
#print axioms HPC.Fold.Recon121.seamC_crooked
#print axioms HPC.Fold.Recon121.seamIH_H0
#print axioms HPC.Fold.Recon121.seamIH_H1
#print axioms HPC.Fold.Recon121.seam_Cbot_fails

-- ## Reconnaissance, batch 122 (Bing's induction for Theorem 3, closed)
-- Q1: the batch-121 construction `Cbot` and the seam property
#print axioms HPC.Fold.Recon122.bingSpecialFCbot_eq_cutF
#print axioms HPC.Fold.Recon122.cbot_works_of_seamP
#print axioms HPC.Fold.Recon122.seamP_of_endClause
-- Q3: Bing's Theorem 3 in the model, by Bing's induction with the seams closed
#print axioms HPC.Fold.Recon122.special_five
#print axioms HPC.Fold.Recon122.special_case
#print axioms HPC.Fold.Recon122.general_case
#print axioms HPC.Fold.Recon122.bing_main
#print axioms HPC.Fold.Recon122.theorem3Strong_holds
-- Q3: transfer to chains and the statements
#print axioms HPC.Fold.Recon122.bHyp_of_crooked
#print axioms HPC.Fold.Recon122.chain_of_bconcl
#print axioms HPC.Fold.Recon122.theorem3Block_of_strong
#print axioms HPC.Fold.Recon122.theorem3Block_of_literalOr
#print axioms HPC.Fold.Recon122.theorem3EndStmt_of_block
#print axioms HPC.Fold.Recon122.theorem3Block_holds
#print axioms HPC.Fold.Recon122.theorem3EndStmt_holds
#print axioms HPC.Fold.Recon122.theorem3_end'

-- ## Batch 123 (Theorem 4 in Bing's two-link form; the only-clauses)
-- Theorem 4 in the model
#print axioms HPC.Fold.Recon123.seg3
#print axioms HPC.Fold.Recon123.two_small
#print axioms HPC.Fold.Recon123.two_core
#print axioms HPC.Fold.Recon123.two_model
#print axioms HPC.Fold.chain_of_twoConcl
-- the degenerate example
#print axioms HPC.Fold.degFine_crooked
#print axioms HPC.Fold.degFine_not_two
-- the only-clauses: reductions
#print axioms HPC.Fold.onlyIn_of_neighbour
#print axioms HPC.Fold.onlyIn_of_not_covered

-- ## Batch 124 (the pair form of Theorem 3; the only-clauses; Fugate's Corollary 1)
-- the pair form in the model
#print axioms HPC.Fold.Recon122.zbase
#print axioms HPC.Fold.Recon122.special_fiveZ
#print axioms HPC.Fold.Recon122.pair_main
-- the pair form for chains; Theorem 3 as printed
#print axioms HPC.Fold.Recon122.chain_of_bconclZ
#print axioms HPC.Fold.theorem3_pair
#print axioms HPC.Fold.theorem3Pair_holds
#print axioms HPC.Fold.onlyIn_of_no_common
#print axioms HPC.Fold.theorem3_literal
#print axioms HPC.Fold.Recon121.theorem3LiteralOr_holds
-- Theorem 4 as printed: refuted with three coarse links
#print axioms HPC.Fold.onlyFine_crooked
#print axioms HPC.Fold.not_theorem4LiteralND
-- Fugate's Corollary 1: (U) is exactly the missing step
#print axioms HPC.Plane.fugateU_iff_cor1Sufficiency
#print axioms HPC.Plane.fugate_cor1_of_fugateU

-- ## Jordan curve theorem for polygons (batch 125)
-- part I: the crossing parity
#print axioms HPC.Plane.crossesEast_comm
#print axioms HPC.Plane.not_crossesEast_of_mem
#print axioms HPC.Plane.crossesEast_locallyConstant_of_ne
#print axioms HPC.Plane.crossesEast_jump
#print axioms HPC.Plane.sum_vJump_telescope
#print axioms HPC.Plane.parity_locallyConstant
#print axioms HPC.Plane.parity_eq_of_isPreconnected
#print axioms HPC.Plane.parity_far
#print axioms HPC.Plane.parity_eq_zero_of_far
#print axioms HPC.Plane.exists_parity_flip
#print axioms HPC.Plane.exists_nonhorizontal_edge
#print axioms HPC.Plane.polygon_separates

-- ## Jordan curve theorem for polygons (batch 126)
-- part II: the two sides are connected; the field `jct` discharged
#print axioms HPC.Plane.polygon_local_chord
#print axioms HPC.Plane.halfDisk_convex
#print axioms HPC.Plane.halfDisk_nonempty
#print axioms HPC.Plane.ball_diff_chord
#print axioms HPC.Plane.parity_flip_at
#print axioms HPC.Plane.parity_flip_vertical
#print axioms HPC.Plane.parity_flip_edge
#print axioms HPC.Plane.mem_closure_parity_set
#print axioms HPC.Plane.vertex_two_pieces
#print axioms HPC.Plane.exists_first_hit
#print axioms HPC.Plane.exists_segment_to_boundary
#print axioms HPC.Plane.sideNbhd_subset
#print axioms HPC.Plane.sideNbhd_isConnected
#print axioms HPC.Plane.sideNbhd_near
#print axioms HPC.Plane.exists_segment_to_sideNbhd
#print axioms HPC.Plane.isConnected_parity_set
#print axioms HPC.Plane.frontier_parity_set
#print axioms HPC.Plane.jct_polygon
#print axioms HPC.Plane.planeFacts_of_enclose_janiszewski

-- ## Polygonal Janiszewski (batch 127)
-- part I: straight-line graphs, mod-2 cycles, parity, Mayer–Vietoris
#print axioms HPC.Plane.exists_proper_subdivision
#print axioms HPC.Plane.IsProper.subset
#print axioms HPC.Plane.isClosed_graphSet
#print axioms HPC.Plane.cycParity_symmDiff
#print axioms HPC.Plane.not_sum_vJump_even_skeleton
#print axioms HPC.Plane.sum_vJump_even
#print axioms HPC.Plane.cycParity_locallyConstant
#print axioms HPC.Plane.cycParity_eq_of_isPreconnected
#print axioms HPC.Plane.cycParity_far
#print axioms HPC.Plane.separatesPts_of_cycParity_ne
#print axioms HPC.Plane.cycParity_flip
#print axioms HPC.Plane.graph_connected_of_isConnected
#print axioms HPC.Plane.exists_cycle_decomposition
#print axioms HPC.Plane.janiszewskiPoly_of_oddCycle

-- ## Polygonal Janiszewski (batch 128)
-- part II: a separating graph contains an odd cycle; `JaniszewskiPoly` proved
#print axioms HPC.Plane.zmod2_jump_sum
#print axioms HPC.Plane.circPt_mem_segment_iff
#print axioms HPC.Plane.edge_local
#print axioms HPC.Plane.sideStrip_subset_compl
#print axioms HPC.Plane.sideStrip_nonempty
#print axioms HPC.Plane.sideStrip_isPreconnected
#print axioms HPC.Plane.subset_or_disjoint_component
#print axioms HPC.Plane.oddSet_subset
#print axioms HPC.Plane.vertex_arcs
#print axioms HPC.Plane.even_deg_oddSet
#print axioms HPC.Plane.isCycle_oddSet
#print axioms HPC.Plane.cycParity_sideStrip_ne_iff
#print axioms HPC.Plane.gFun_eq_across_edge
#print axioms HPC.Plane.gFun_locallyConstant
#print axioms HPC.Plane.gFun_const
#print axioms HPC.Plane.cycParity_oddSet_ne
#print axioms HPC.Plane.separatingGraphHasOddCycle
#print axioms HPC.Plane.janiszewskiPoly_holds

-- ## Polygonal Janiszewski (batch 129)
-- part III: polygonal sets, the field change (`janiszewski` for polygonal sets), the two uses;
-- `PlaneFacts` down to one undischarged field (`enclose`)
-- item 1: polygonal sets (`HPC/Plane/Polygonal.lean`, `HPC/Plane/PolygonalPoly.lean`)
#print axioms HPC.Plane.IsPolygonal.isCompact
#print axioms HPC.Plane.IsPolygonal.union
#print axioms HPC.Plane.IsPolygonal.inter
#print axioms HPC.Plane.isPolygonal_empty
#print axioms HPC.Plane.isPolygonal_segment
#print axioms HPC.Plane.isPolygonal_singleton
#print axioms HPC.Plane.isPolygonal_biUnion
#print axioms HPC.Plane.IsSimpleClosedPolygon.isPolygonal
#print axioms HPC.Plane.isPolygonal_iff_graphSet
-- item 2: isolated points; Janiszewski for polygonal sets
#print axioms HPC.Plane.isPreconnected_ball_diff_singleton
#print axioms HPC.Plane.isConnected_diff_singleton_of_isOpen
#print axioms HPC.Plane.separatesPts_insert_iff
#print axioms HPC.Plane.separatesPts_union_finite_iff
#print axioms HPC.Plane.IsPolygonal.exists_split
#print axioms HPC.Plane.inter_split_connected
#print axioms HPC.Plane.janiszewski_polygonal
-- item 3: the local half-disk of a polygon interior
#print axioms HPC.Plane.polyInterior_local_halfDisk
-- item 4: polygonality of `Γ₁ ∩ closure (h₁ ∩ h₂)`
#print axioms HPC.Plane.isPolygonal_segment_inter_segment
#print axioms HPC.Plane.isPolygonal_segment_inter_polygon
#print axioms HPC.Plane.exists_open_pieces_of_saturated
#print axioms HPC.Plane.exists_open_pieces
#print axioms HPC.Plane.eventually_mem_closure_of_not_special
#print axioms HPC.Plane.isPolygonal_segment_inter_closure
#print axioms HPC.Plane.isPolygonal_inter_closure_inter
#print axioms HPC.Plane.isSaturated_polyInterior
#print axioms HPC.Plane.isPolygonal_inter_closure_polyInterior₃
#print axioms HPC.Plane.isPolygonal_frontier_inter_closure
-- the edits: the two uses, Theorems 6 and 7, the interface
#print axioms HPC.Plane.PlaneFacts.crosscut'
#print axioms HPC.Plane.PlaneFacts.exists_theta_point
#print axioms HPC.Plane.compFamily_no_circular
#print axioms HPC.Plane.treeChain_of_cover
#print axioms HPC.Plane.theorem7_1951_rel
#print axioms HPC.Plane.theorem6_1951_rel
#print axioms HPC.Plane.theorem7_weak_rel
#print axioms HPC.Plane.planeFacts_of_enclose_janiszewski
#print axioms HPC.Plane.planeFacts_of_enclose

-- ## Enclosing polygon (batch 130)
-- `enclose`, part I: the grid union, its boundary graph, simple cycles, the enclosing polygon
-- item 1: the interior as the odd set (`HPC/Plane/Enc1Cyc.lean`)
#print axioms HPC.Plane.polyInterior_eq_oddSet
#print axioms HPC.Plane.cycParity_polyEdges
#print axioms HPC.Plane.graphSet_polyEdges
-- item 2: simple cycles
#print axioms HPC.Plane.exists_cycle_vertices
#print axioms HPC.Plane.simpleCycle_of_vertices
#print axioms HPC.Plane.exists_simpleCycle_decomposition
#print axioms HPC.Plane.cycParity_foldr
-- item 3: the grid union (`HPC/Plane/Enc1Grid.lean`, `HPC/Plane/Enc1.lean`)
#print axioms HPC.Plane.mem_frontier_sqUnion_iff
#print axioms HPC.Plane.mem_graphSet_bdryOf_iff
#print axioms HPC.Plane.isProper_bdryOf
#print axioms HPC.Plane.frontier_sqUnion
#print axioms HPC.Plane.mem_interior_sqUnion
#print axioms HPC.Plane.mem_sqIdx_iff
#print axioms HPC.Plane.gridUnion_subset_cthickening
#print axioms HPC.Plane.isCompact_gridUnion
#print axioms HPC.Plane.disjoint_frontier_gridUnion
#print axioms HPC.Plane.subset_interior_gridUnion
#print axioms HPC.Plane.mem_bdryGraph_iff_card
#print axioms HPC.Plane.isProper_bdryGraph
#print axioms HPC.Plane.frontier_gridUnion
#print axioms HPC.Plane.graphSet_bdryGraph_subset
-- item 4: the outer cycle
#print axioms HPC.Plane.farPt_not_mem
#print axioms HPC.Plane.not_isBounded_component
#print axioms HPC.Plane.interior_gridUnion_disjoint_component
#print axioms HPC.Plane.cycParity_oddSet_eq_one_on
#print axioms HPC.Plane.exists_enclosing_polygon

-- ## Enclosing polygon, part II; `PlaneFacts` discharged; Duke Theorems 6–7 unconditional (batch 131)
-- (`HPC/Plane/Enc2.lean`)
-- item 1: uniform membership in the outer component
#print axioms HPC.Plane.not_mem_graphSet_bdryGraph_of_far
#print axioms HPC.Plane.subset_component_of_far
#print axioms HPC.Plane.isPreconnected_eastRay
#print axioms HPC.Plane.one_le_infDist_of_far_coord
#print axioms HPC.Plane.pos_of_subset_ball
#print axioms HPC.Plane.one_le_infDist_eastRay
#print axioms HPC.Plane.eastRay_subset_component
#print axioms HPC.Plane.compl_closedBall_subset_component
-- item 2: paths in the complement and their distance from `M`
#print axioms HPC.Plane.joinedIn_compl_of_not_separates
#print axioms HPC.Plane.exists_pos_infDist_le_of_disjoint
#print axioms HPC.Plane.exists_far_piece
#print axioms HPC.Plane.exists_uniform_pieces
-- item 3: `enclose`, `PlaneFacts`, Theorems 6 and 7
#print axioms HPC.Plane.exists_mesh_compl_subset
#print axioms HPC.Plane.enclose_holds
#print axioms HPC.Plane.planeFacts_holds
#print axioms HPC.Plane.theorem7_1951
#print axioms HPC.Plane.theorem6_1951
#print axioms HPC.Plane.theorem7_weak

-- ## Fugate's Corollary 1: Part I (Corollary 1 under (∗)); Part II (Ingram 1968; (∗));
-- `fugate_cor1` proved (batch 132)
-- Part I: Corollary 1 under (∗) (`HPC/Plane/Fugate66Cor1Proof.lean`)
#print axioms HPC.Plane.ingramStarWeak_of_ingramStar
#print axioms HPC.Plane.exists_split_of_not_isConnected
#print axioms HPC.Plane.not_isPreconnected_of_split
#print axioms HPC.Plane.not_isUnicoherent_of_split
#print axioms HPC.Plane.subset_of_unicoherent_absorb'
#print axioms HPC.Plane.subset_of_unicoherent_absorb
#print axioms HPC.Plane.mem_chainUnion
#print axioms HPC.Plane.subset_chainUnion
#print axioms HPC.Plane.chainUnion_mono
#print axioms HPC.Plane.chainUnion_self
#print axioms HPC.Plane.chainUnion_split
#print axioms HPC.Plane.chainUnion_succ
#print axioms HPC.Plane.inter_chainUnion_nonempty
#print axioms HPC.Plane.isContinuum_chainUnion
#print axioms HPC.Plane.isSnakeLike_chainUnion_of_hu
#print axioms HPC.Plane.isHereditarilyUnicoherent_chainUnion
#print axioms HPC.Plane.isSnakeLike_chainUnion_of_ingramStarWeak
#print axioms HPC.Plane.finChainExt_snake
#print axioms HPC.Plane.finChainExt_meet
#print axioms HPC.Plane.finChainExt_partial
#print axioms HPC.Plane.finChainExt_union
#print axioms HPC.Plane.isHereditarilyUnicoherent_partial
#print axioms HPC.Plane.fugateCor1Sufficiency_of_ingramStarWeak
#print axioms HPC.Plane.fugateCor1Sufficiency_of_ingramStar
#print axioms HPC.Plane.fugate_cor1_of_ingramStar
#print axioms HPC.Plane.fugateU_of_ingramStar
-- Part II: Ingram 1968, Lemmas 1–2 and (∗∗) (`HPC/Plane/Ingram68Core.lean`)
#print axioms HPC.Plane.isTriod_of_core
#print axioms HPC.Plane.not_core_of_isAtriodic
#print axioms HPC.Plane.exists_open_closure_disjoint
#print axioms HPC.Plane.exists_arm
#print axioms HPC.Plane.not_isAtriodic_of_three
#print axioms HPC.Plane.ingram_lemma1
#print axioms HPC.Plane.eq_of_subset_of_split
#print axioms HPC.Plane.ingram_lemma2
#print axioms HPC.Plane.ingramStarWeak_holds
-- Part II: (∗) (`HPC/Plane/Ingram68Star.lean`)
#print axioms HPC.Plane.exists_split_of_no_continuum
#print axioms HPC.Plane.isUnicoherent_of_subsingleton
#print axioms HPC.Plane.isUnicoherent_of_subset_hu
#print axioms HPC.Plane.subset_satUnion
#print axioms HPC.Plane.satUnion_subset
#print axioms HPC.Plane.isContinuum_satUnion
#print axioms HPC.Plane.isUnicoherent_of_not_mem_diff
#print axioms HPC.Plane.isUnicoherent_of_not_mem_piece
#print axioms HPC.Plane.ingramStar_holds
-- Part II: Nadler 12.51; `fugate_cor1` proved (`HPC/Plane/Ingram68.lean`)
#print axioms HPC.Plane.isSnakeLike_of_subset_circleLike
#print axioms HPC.Plane.fugate_cor1
#print axioms HPC.Plane.fugateU_holds

-- ## Tree-like continua do not separate; Duke Theorem 7 as printed; `IsTreeLike` repaired (batch 133)
-- The old definition of `IsTreeLike` (links not required bounded) is trivial
#print axioms HPC.Plane.isTreeLikeOld_of_isContinuum
-- Theorem 6, re-checked under the repaired definition
#print axioms HPC.Plane.theorem6_1951_rel
#print axioms HPC.Plane.theorem6_1951
-- A logarithm on a fine tree cover (`HPC/Plane/TreeLikeNS.lean`, `TreeLikeNSGraph.lean`)
#print axioms HPC.Plane.no_two_nbrs
#print axioms HPC.Plane.exists_log_on_ball
#print axioms HPC.Plane.exists_leaf
#print axioms HPC.Plane.exists_log_on_treeChain
-- No logarithm on a polygon around `p` (`TreeLikeNSLog.lean`)
#print axioms HPC.Plane.log_diff_edge
#print axioms HPC.Plane.edge_jump
#print axioms HPC.Plane.no_log_on_polygon
-- A polygon in an open set around a point
#print axioms HPC.Plane.exists_enclosing_polygon_pt
#print axioms HPC.Plane.exists_polygon_around
-- Assembly
#print axioms HPC.Plane.exists_bounded_component_of_separates
#print axioms HPC.Plane.isTreeChain_filter_meet
#print axioms HPC.Plane.treeLike_nonseparating
#print axioms HPC.Plane.theorem7_1951_treeLike
#print axioms HPC.Plane.isTreeLike_iff_nonseparating

-- ## Effros theorem (batch 134)
-- van Mill 2004, Lemma 2.1 and Proposition 2.2 (`HPC/Effros/Fat.lean`)
#print axioms HPC.Effros.IsFat.mono
#print axioms HPC.Effros.IsFat.diff_meagre
#print axioms HPC.Effros.nonempty_interior_closure_of_not_meagre
#print axioms HPC.Effros.inter_nonempty_of_nowhereMeagre
#print axioms HPC.Effros.inter_nonempty_of_isFat
-- Proposition 2.2 needs a nonempty space (refutation candidate confirmed)
#print axioms HPC.Effros.isFat_empty_of_isEmpty
-- The open mapping principle, van Mill §3 (`HPC/Effros/OpenMapping.lean`)
#print axioms HPC.Effros.exists_vanMill_basis
#print axioms HPC.Effros.vanMill_3_1
#print axioms HPC.Effros.vanMill_3_2
#print axioms HPC.Effros.vanMill_3_3
#print axioms HPC.Effros.vanMill_3_4
#print axioms HPC.Effros.vanMill_3_4_dense
#print axioms HPC.Effros.vanMill_3_5
#print axioms HPC.Effros.effros_open_mapping
#print axioms HPC.Effros.isOpenMap_smul_left
#print axioms HPC.Effros.isOpen_orbitPart
-- The homeomorphism group of a compact metric space (`HPC/Effros/HomeoGroup.lean`)
#print axioms HPC.Effros.homeo_isTopologicalGroup
#print axioms HPC.Effros.homeo_polishSpace
#print axioms HPC.Effros.homeo_continuousSMul
#print axioms HPC.Effros.supMove_symm
#print axioms HPC.Effros.supMove_symm_trans_le
#print axioms HPC.Effros.hasBasis_supMove
#print axioms HPC.Effros.supMove_ball_mem_nhds
-- Ungar's corollary (`HPC/Effros/Effros.lean`)
#print axioms HPC.Effros.effros_homogeneous
#print axioms HPC.Effros.effros_homogeneous_set

-- ## Jones 1948, 1951 (batch 135)
-- Equivalences with the repository's definitions (`HPC/Jones/Basic.lean`)
#print axioms HPC.Jones.isDecomposableSpace_iff_not_isIndecomposable
#print axioms HPC.Jones.composant_eq_composant_univ
-- Jones 1948, §1 (`HPC/Jones/Basic.lean`, `HPC/Jones/Theorem6.lean`)
#print axioms HPC.Jones.theorem0
#print axioms HPC.Jones.theorem1
#print axioms HPC.Jones.theorem2
#print axioms HPC.Jones.theorem3
#print axioms HPC.Jones.theorem4
#print axioms HPC.Jones.theorem5
#print axioms HPC.Jones.theorem6
-- Theorem 6 as printed (`D` may be empty) is false
#print axioms HPC.Jones.not_theorem6_printed
#print axioms HPC.Jones.theorem7
#print axioms HPC.Jones.theorem8
#print axioms HPC.Jones.theorem9
-- Theorem 10, corrected (`D` nonempty)
#print axioms HPC.Jones.theorem10
-- Theorem 10 as printed is false: it says exactly that `X` is indecomposable; an arc refutes it
#print axioms HPC.Jones.theorem10_printed_iff
#print axioms HPC.Jones.isDecomposableSpace_unitInterval
#print axioms HPC.Jones.not_theorem10_printed_unitInterval
-- Jones 1948, §§3–5 (`HPC/Jones/Theorem13.lean`, `HPC/Jones/CutPoints.lean`)
#print axioms HPC.Jones.theorem11
#print axioms HPC.Jones.theorem12
#print axioms HPC.Jones.totallyNonApos_exists_weakCutPoint
#print axioms HPC.Jones.theorem13
#print axioms HPC.Jones.theorem14
#print axioms HPC.Jones.theorem15
#print axioms HPC.Jones.theorem15_cor
#print axioms HPC.Jones.theorem16
#print axioms HPC.Jones.theorem17
#print axioms HPC.Jones.theorem17_cor
#print axioms HPC.Jones.theorem18
#print axioms HPC.Jones.theorem19
-- Jones 1951 (`HPC/Jones/Jones51.lean`); Theorem 1 was open here, proved in batch 136 (listed below)
#print axioms HPC.Jones.isOpen_aposSet
#print axioms HPC.Jones.isHomogeneous_iff_isPretransitive
#print axioms HPC.Jones.exists_lsc_strictMono_aposSet
#print axioms HPC.Jones.jones51_lemma

-- ## Jones 1955, decompositions (batch 136)
-- Decomposition spaces (`HPC/Jones/Decomp.lean`)
#print axioms HPC.Jones.isClosedMap_mk
#print axioms HPC.Jones.t2Space_quotient
#print axioms HPC.Jones.secondCountable_quotient
#print axioms HPC.Jones.metrizableSpace_quotient
#print axioms HPC.Jones.isContinuum_preimage
#print axioms HPC.Jones.exists_homeomorph_quotient
#print axioms HPC.Jones.residual_lscAt
#print axioms HPC.Jones.exists_lscAt
#print axioms HPC.Jones.lscAt_homeomorph
-- Jones 1941 Theorem 4; Whyburn 1939 (6.1), (6.2), (6.21) (`HPC/Jones/Whyburn.lean`)
#print axioms HPC.Jones.semiLocConn_of_isAposyndetic
#print axioms HPC.Jones.isAposyndetic_of_semiLocConn
#print axioms HPC.Jones.whyburn_6_1
#print axioms HPC.Jones.whyburn_6_2
#print axioms HPC.Jones.whyburn_6_21
-- Jones 1955, claims (1)-(12), (a)-(f) (`HPC/Jones/Jones55Core.lean`)
#print axioms HPC.Jones.aposAt_of_isContinuum_interior
#print axioms HPC.Jones.isContinuum_Lset
#print axioms HPC.Jones.mem_Lset_iff_Lset_eq
#print axioms HPC.Jones.Lset_subset_of_meets
#print axioms HPC.Jones.jones55_claim1
#print axioms HPC.Jones.jones55_claim2
#print axioms HPC.Jones.jones55_claim3
#print axioms HPC.Jones.jones55_claim4
#print axioms HPC.Jones.jones55_claim5
#print axioms HPC.Jones.jones55_claim6
#print axioms HPC.Jones.jones55_claim7
#print axioms HPC.Jones.jones55_claim8
#print axioms HPC.Jones.jones55_claim9
#print axioms HPC.Jones.jones55_claim10
#print axioms HPC.Jones.jones55_claim11
#print axioms HPC.Jones.jones55_claim12
#print axioms HPC.Jones.Nset_eq_Lset
#print axioms HPC.Jones.Nset_characterization
#print axioms HPC.Jones.jones55_prop_a
#print axioms HPC.Jones.jones55_prop_b
#print axioms HPC.Jones.jones55_prop_c
#print axioms HPC.Jones.jones55_prop_d
#print axioms HPC.Jones.jones55_prop_e
#print axioms HPC.Jones.jones55_prop_f
-- Jones 1951 Theorem 1 (`HPC/Jones/Jones51Thm1.lean`)
#print axioms HPC.Jones.jones51_theorem1
-- Jones 1955 Theorem 1 (`HPC/Jones/Jones55.lean`)
#print axioms HPC.Jones.jones55_isContinuum
#print axioms HPC.Jones.jones55_b
#print axioms HPC.Jones.jones55_c
#print axioms HPC.Jones.jones55_usc
#print axioms HPC.Jones.jones55_continuous
#print axioms HPC.Jones.jones55_a
#print axioms HPC.Jones.jones55_elements

-- ## Moore F.A. §§2–5 (batch 137)
-- Theorems 1–9, `M'` closed (`HPC/Moore/Basic.lean`)
#print axioms HPC.Moore.fa_theorem1
#print axioms HPC.Moore.fa_theorem2
#print axioms HPC.Moore.fa_theorem3
#print axioms HPC.Moore.fa_theorem4
#print axioms HPC.Moore.fa_theorem5
#print axioms HPC.Moore.fa_theorem6
#print axioms HPC.Moore.fa_theorem7
#print axioms HPC.Moore.fa_theorem8
#print axioms HPC.Moore.fa_theorem9
#print axioms HPC.Moore.fa_cl_isClosed
-- Theorem 10 (`HPC/Moore/Chains.lean`)
#print axioms HPC.Moore.exists_simpleChain_sublist
#print axioms HPC.Moore.fa_theorem10
-- The bridge (`HPC/Moore/Bridge.lean`)
#print axioms HPC.Moore.heineBorel_iff
#print axioms HPC.Moore.isTopologicalBasis_region
#print axioms HPC.Moore.isLimitPt_iff
#print axioms HPC.Moore.cl_eq_closure
#print axioms HPC.Moore.isClosedM_iff
#print axioms HPC.Moore.isConn_iff
#print axioms HPC.Moore.isDomain_iff
#print axioms HPC.Moore.t1Space
#print axioms HPC.Moore.regularSpace
#print axioms HPC.Moore.t2Space
#print axioms HPC.Moore.secondCountable
#print axioms HPC.Moore.metrizable
#print axioms HPC.Moore.isCompact_closure_region
#print axioms HPC.Moore.isCompact_closure_of_isBoundedM
#print axioms HPC.Moore.isBoundedM_of_isCompact
-- Theorems 11–14, 17–19 (`HPC/Moore/Sec4.lean`); Theorem 14 as printed is false
#print axioms HPC.Moore.axiom5₁_of_axiom5
#print axioms HPC.Moore.fa_theorem11
#print axioms HPC.Moore.fa_theorem12
#print axioms HPC.Moore.fa_theorem13
#print axioms HPC.Moore.fa_theorem14
#print axioms HPC.Moore.not_fa_theorem14_printed
#print axioms HPC.Moore.fa_theorem17
#print axioms HPC.Moore.fa_theorem18
#print axioms HPC.Moore.fa_theorem19
-- Theorems 15, 16: Moore's nested simple chains (`HPC/Moore/Thm15.lean`)
#print axioms HPC.Moore.exists_irreducible
#print axioms HPC.Moore.isArc_iff_topological
#print axioms HPC.Moore.fa_theorem15
#print axioms HPC.Moore.fa_theorem16
-- The arc characterization (`HPC/Moore/ArcChar.lean`)
#print axioms HPC.Moore.ac_homeomorph
#print axioms HPC.Moore.isIrreducibleConnected_iff_arc
-- Arcs, pp. 139–140 (`HPC/Moore/Arcs.lean`); the printed limit-point statement fails
#print axioms HPC.Moore.isArc_iff
#print axioms HPC.Moore.Space.IsArc.union
#print axioms HPC.Moore.fa_sec5_arc_split
#print axioms HPC.Moore.fa_sec5_interval_unique
#print axioms HPC.Moore.fa_sec5_first_point
#print axioms HPC.Moore.fa_sec5_last_point
#print axioms HPC.Moore.fa_sec5_limitPt_iff
#print axioms HPC.Moore.not_fa_sec5_limitPt_printed
#print axioms HPC.Moore.fa_scc_two_arcs
-- `∅` as a region: printed Theorems 4 and 19 are not consequences of Axioms 1–8 (`HPC/Moore/Refute.lean`)
#print axioms HPC.Moore.isConn_univ
#print axioms HPC.Moore.not_fa_theorem4_printed
#print axioms HPC.Moore.not_fa_theorem19_printed

-- ## Moore F.A. §6 (batch 138)
-- The bridge for §6 (`HPC/Moore/Sec6A.lean`)
#print axioms HPC.Moore.bdry_eq_frontier
#print axioms HPC.Moore.ext_eq_compl_closure
#print axioms HPC.Moore.locallyConnectedSpace
#print axioms HPC.Moore.isArc_iff_tarc
#print axioms HPC.Moore.isSCC_iff_tscc
#print axioms HPC.Moore.isInteriorOf_iff
#print axioms HPC.Moore.arcConn
-- Theorems 20–23 and the interior of a closed curve (`HPC/Moore/Sec6A.lean`); Theorem 23 as printed is false
#print axioms HPC.Moore.fa_theorem20
#print axioms HPC.Moore.fa_theorem21
#print axioms HPC.Moore.fa_theorem22
#print axioms HPC.Moore.existsUnique_interior
#print axioms HPC.Moore.fa_theorem23
#print axioms HPC.Moore.not_fa_theorem23_printed
-- Theorems 24–27 (`HPC/Moore/Sec6B.lean`, topological forms in `Sec6Th24.lean` … `Sec6Th27.lean`)
#print axioms HPC.Moore.fa_theorem24
#print axioms HPC.Moore.fa_theorem25
#print axioms HPC.Moore.fa_theorem26
#print axioms HPC.Moore.fa_theorem27
#print axioms HPC.Moore.Gen.th25
#print axioms HPC.Moore.Gen.th26
#print axioms HPC.Moore.Gen.th27
-- Theorems 28–31 (`HPC/Moore/Sec6Th28.lean`, `Sec6Th29.lean`, `Sec6Th31.lean`)
#print axioms HPC.Moore.fa_theorem28
#print axioms HPC.Moore.fa_theorem29
#print axioms HPC.Moore.fa_theorem30
#print axioms HPC.Moore.th31_pocket
#print axioms HPC.Moore.fa_theorem31
-- Limit arcs and Theorem 32 (`HPC/Moore/Sec6Lim.lean`, `Sec6Th32.lean`); a hypothesis added to Theorem 32
#print axioms HPC.Moore.Gen.tarc_of_seq
#print axioms HPC.Moore.Gen.exists_tarc_of_seq
#print axioms HPC.Moore.accessible
#print axioms HPC.Moore.fa_theorem32
-- Theorems 33, 34 by Kline's proof (`HPC/Moore/Sec6Th33.lean`)
#print axioms HPC.Moore.fa_theorem33
#print axioms HPC.Moore.fa_theorem34_region
#print axioms HPC.Moore.fa_theorem34

-- ## Moore F.A. §7 (batch 139)
-- Jordan structure; Theorems 35, 39, 40; footnote p. 152 (`HPC/Moore/Sec7A.lean`); Theorem 35 as printed is false
#print axioms HPC.Moore.jordan
#print axioms HPC.Moore.access
#print axioms HPC.Moore.fa_theorem35
#print axioms HPC.Moore.not_fa_theorem35_printed
#print axioms HPC.Moore.fa_theorem39
#print axioms HPC.Moore.fa_theorem40
#print axioms HPC.Moore.fa_arcs_of_scc_meet
-- Theorem 36, and its interior inside `R` (`HPC/Moore/Sec7B.lean`)
#print axioms HPC.Moore.fa_theorem36
#print axioms HPC.Moore.fa_theorem36_interior_subset
-- Chords; Theorems 37, 38 (`HPC/Moore/Sec7Chord.lean`, `Sec7Th37.lean`, `Sec7Th38.lean`)
#print axioms HPC.Moore.param_chords_finite
#print axioms HPC.Moore.exists_maximal_chord
#print axioms HPC.Moore.fa_theorem37
#print axioms HPC.Moore.fa_theorem38
-- Theorem 41: Case I and the first sub-case of Case II (`HPC/Moore/Sec7Th41.lean`); Case II in batch 140 below
#print axioms HPC.Moore.fa_theorem41_caseI_nested
#print axioms HPC.Moore.fa_theorem41_caseI
#print axioms HPC.Moore.fa_theorem41_of_subset
-- Theorem 42 from Theorem 41; Theorem 43 as printed is false (`HPC/Moore/Sec7Th42.lean`)
#print axioms HPC.Moore.isSCC_eq_of_subset
#print axioms HPC.Moore.fa_theorem42_of_41
#print axioms HPC.Moore.not_fa_theorem43_printed

-- ## Moore F.A. 41–43, 1919 A–B (batch 140)
-- Moore 1919, Theorem A (`HPC/Moore/M19A.lean`)
#print axioms HPC.Moore.Gen.crossing
#print axioms HPC.Moore.m19_theoremA
-- Replacement of a null family of arcs; chords; pockets (`HPC/Moore/M41Replace.lean`, `M41Geom.lean`, `M41Side.lean`, `M41Half.lean`)
#print axioms HPC.Moore.Gen.finite_long_intervals
#print axioms HPC.Moore.Gen.arc_replace
#print axioms HPC.Moore.Gen.exists_unbounded_component
#print axioms HPC.Moore.Gen.disjoint_of_unbounded
#print axioms HPC.Moore.chords_null
#print axioms HPC.Moore.chord_side
#print axioms HPC.Moore.pocket
#print axioms HPC.Moore.half_replace
-- Theorems 41 (Case II and in full) and 42 (`HPC/Moore/M41.lean`)
#print axioms HPC.Moore.curve_of_frontier_subset
#print axioms HPC.Moore.fa_theorem41_caseII
#print axioms HPC.Moore.fa_theorem41
#print axioms HPC.Moore.fa_theorem42
-- Theorem 43, corrected (`HPC/Moore/M43Pocket.lean`, `M43Dual.lean`, `M43Comp.lean`, `M43.lean`)
#print axioms HPC.Moore.dual_component
#print axioms HPC.Moore.dual_step
#print axioms HPC.Moore.iterate_inner
#print axioms HPC.Moore.fa_theorem43
-- Moore 1919, Theorem B and its step; the arc of footnote * of p. 174 (`HPC/Moore/M19Bstep.lean`, `M19B.lean`, `M19D.lean`)
#print axioms HPC.Moore.m19_B_step
#print axioms HPC.Moore.m19_theoremB
#print axioms HPC.Moore.hair_isPreconnected
#print axioms HPC.Moore.m19_D_arc

-- ## Moore 1919 C–D (batch 141)
-- Double rulings: the subdivision lemma (`HPC/Moore/M19CDTile.lean`, `M19CDCells.lean`)
#print axioms HPC.Moore.Space.Tiling.add_arc
#print axioms HPC.Moore.Space.DoubleRuling.tiling
#print axioms HPC.Moore.doubleRuling_cell
#print axioms HPC.Moore.doubleRuling_cells_ncard
-- Theorem C as printed is false (`HPC/Moore/M19CRefute.lean`)
#print axioms HPC.Moore.no_ruling_of_two_branches
#print axioms HPC.Moore.tangent_configuration
#print axioms HPC.Moore.not_m19_theoremC_printed
-- Splitting a quadrilateral; rulings by sets of arcs; cuts (`HPC/Moore/M19CDSplit.lean`, `M19CDRuling.lean`, `M19CDCut.lean`, `M19CDGlue.lean`)
#print axioms HPC.Moore.Space.Quad.splitX
#print axioms HPC.Moore.Space.Quad.exists_cut
#print axioms HPC.Moore.Space.ArcRuling.restrict_half
#print axioms HPC.Moore.Space.Quad.Cut.glue
-- Extension and refinement of rulings (`HPC/Moore/M19CDExt.lean`, `M19CDRefine.lean`)
#print axioms HPC.Moore.Space.ArcRuling.extendY
#print axioms HPC.Moore.Space.ArcRuling.extendY_finite
#print axioms HPC.Moore.Space.ArcRuling.refine
-- Rulings by sets of arcs are double rulings; padding; refinement of double rulings (`HPC/Moore/M19CDOrder.lean`, `M19CDMain.lean`)
#print axioms HPC.Moore.Space.ArcRuling.sortX
#print axioms HPC.Moore.Space.DoubleRuling.toArcRuling
#print axioms HPC.Moore.Space.ArcRuling.toDoubleRuling
#print axioms HPC.Moore.doubleRuling_pad
#print axioms HPC.Moore.doubleRuling_refine
-- Theorem D: the curve form gives the region form (`HPC/Moore/M19CDRegion.lean`; Theorem D proved in batch 142, below)
#print axioms HPC.Moore.m19_theoremD_regions_of_curves

-- ## Moore 1919 C corrected, D (batch 142)
-- Theorem C corrected, three forms (`HPC/Moore/M19CD2.lean`)
#print axioms HPC.Moore.m19_theoremC_crosscuts
#print axioms HPC.Moore.m19_theoremC_within
#print axioms HPC.Moore.m19_theoremC_corrected
-- A ruling missing finitely many disjoint chords; a closed curve within; the chords of a curve (`M19DChords.lean`, `M19DInside.lean`, `M19DExtract.lean`)
#print axioms HPC.Moore.chords_rulable
#print axioms HPC.Moore.inside_rulable
#print axioms HPC.Moore.extract_chords
#print axioms HPC.Moore.curve_rulable
-- Lenses; a curve about a compact set crossing `J` at each common point (`M19DLens.lean`, `M19DNice.lean`)
#print axioms HPC.Moore.lens_data
#print axioms HPC.Moore.exists_nice_curve
-- Theorem D, curve form and region form (`M19DThm.lean`, `M19CD2.lean`)
#print axioms HPC.Moore.rulable_of_cover
#print axioms HPC.Moore.m19_theoremD
#print axioms HPC.Moore.m19_theoremD_regions

-- ## Moore 1919 E–F (batch 143)
-- The nested double rulings `β₁, β₂, …` ("This process may be continued") (`HPC/Moore/M19ESeq.lean`)
#print axioms HPC.Moore.nested_rulings
#print axioms HPC.Moore.nested_rulings_fund
-- A compact set with a grid of vanishing mesh is a square; boxes of a finite subgrid (`HPC/Moore/GridSquare.lean`, `HPC/Moore/GridMesh.lean`)
#print axioms HPC.Sq.Grid.exists_square
#print axioms HPC.Sq.PreGrid.box_sub_component
-- The grid of cross-cuts; its boxes are subdivisions (`M19ELines.lean`, `M19EFamily.lean`, `M19EGrid.lean`, `M19EMesh.lean`)
#print axioms HPC.Moore.exists_lineRec
#print axioms HPC.Moore.lfT_injective
#print axioms HPC.Moore.lfLine_cross
#print axioms HPC.Moore.preGrid_box_sub_cell
-- Schoenflies form; Theorem E from a square; Theorem E (`M19ESchoenflies.lean`, `M19EThm.lean`, `M19EF.lean`)
#print axioms HPC.Moore.m19_schoenflies_proof
#print axioms HPC.Moore.theoremE_of_square
#print axioms HPC.Moore.m19_theoremE_proof
#print axioms HPC.Moore.m19_schoenflies
#print axioms HPC.Moore.m19_theoremE
-- Theorem F (`M19F.lean`, `M19EF.lean`)
#print axioms HPC.Moore.exists_curve_about_compact
#print axioms HPC.Moore.m19_theoremF_proof
#print axioms HPC.Moore.m19_theoremF

-- ## Moore 1919, the plane (batch 144)
-- A compact grid is a square with prescribed lines; homeomorphisms of the square fixing two sides (`HPC/Moore/M19GSquare.lean`)
#print axioms HPC.Sq.Grid.exists_square_param
#print axioms HPC.Sq.exists_square_reparam
-- Pasting over an exhaustion; the radial step; a plane from collars (`HPC/Moore/M19GPaste.lean`)
#print axioms HPC.Sq.exhaust_homeomorph
#print axioms HPC.Sq.radial_step
#print axioms HPC.Sq.plane_of_collars
-- Schoenflies with prescribed boundary (`HPC/Moore/M19GBoundary.lean`)
#print axioms HPC.Moore.m19_schoenflies_param
#print axioms HPC.Moore.m19_schoenflies_boundary_proof
-- One interior; a closed curve is a square; two cuts of the annulus; the annulus as two quadrilaterals (`M19GCuts.lean`, `M19GSplit.lean`)
#print axioms HPC.Moore.interior_unique
#print axioms HPC.Moore.exists_square_of_interior
#print axioms HPC.Moore.exists_cuts
#print axioms HPC.Moore.annulus_decomp
-- The annulus is a collar; the plane (`M19GCollar.lean`, `M19GPlane.lean`)
#print axioms HPC.Moore.exists_collar
#print axioms HPC.Moore.annulus_square
#print axioms HPC.Moore.m19_plane_proof
-- Corollaries (`M19GCor.lean`)
#print axioms HPC.Moore.isOpenCurveFA_of_isClosedEmbedding
#print axioms HPC.Moore.isSeqLimit_iff_tendsto
#print axioms HPC.Moore.theoremG_of_homeomorph
#print axioms HPC.Moore.final_of_homeomorph
-- The skeleton (`HPC/Moore/M19G.lean`)
#print axioms HPC.Moore.m19_schoenflies_boundary
#print axioms HPC.Moore.m19_annulus
#print axioms HPC.Moore.m19_annulus_square
#print axioms HPC.Moore.m19_plane
#print axioms HPC.Moore.m19_theoremG
#print axioms HPC.Moore.m19_openCurve
#print axioms HPC.Moore.m19_final

-- ## Moore 1925 §I, Theorems 1–4 (batch 145)
-- Plane facts: Brouwer's boundary theorem, Janiszewski for compact sets (`HPC/Moore/M25Plane.lean`)
#print axioms HPC.Moore.plane_unicoherent
#print axioms HPC.Moore.frontier_connectedComponentIn_subset
#print axioms HPC.Moore.brouwer_boundary
#print axioms HPC.Moore.no_log_of_bounded_component
#print axioms HPC.Moore.janiszewski_compact
-- The quotient; Theorem 1 (`HPC/Moore/M25Quot.lean`)
#print axioms HPC.Moore.isClosedMap_mk_plane
#print axioms HPC.Moore.usc_of_isClosedMap
#print axioms HPC.Moore.quotient_metrizable_plane
#print axioms HPC.Moore.isProperMap_mk
#print axioms HPC.Moore.isLimitElt_iff
#print axioms HPC.Moore.m25_domain_iff
#print axioms HPC.Moore.ptsOf_connectedComponentIn
#print axioms HPC.Moore.locallyConnectedSpace_quot
#print axioms HPC.Moore.quot_brouwer
#print axioms HPC.Moore.m25_theorem1
-- Theorems 3 and 4; the region topology; the unbounded complementary domain (`HPC/Moore/M25Thm.lean`)
#print axioms HPC.Moore.exists_region_in_tube
#print axioms HPC.Moore.m25_theorem3
#print axioms HPC.Moore.isTopologicalBasis_mooreRegion
#print axioms HPC.Moore.spaceOfElts_topology
#print axioms HPC.Moore.m25_theorem4
#print axioms HPC.Moore.cl_eq_closure_quot
#print axioms HPC.Moore.m25_boundary_iff
#print axioms HPC.Moore.m25_unbounded_unique
-- Theorem 2 (`HPC/Moore/M25Thm2.lean`)
#print axioms HPC.Moore.m25_theorem2
-- The p. 420 claim: Axioms 1, 2, 4, 5 and F.A. Theorem 4 (`HPC/Moore/M25Ax.lean`)
#print axioms HPC.Moore.m25_axiom1
#print axioms HPC.Moore.m25_axiom2
#print axioms HPC.Moore.m25_axiom4
#print axioms HPC.Moore.m25_axiom5
#print axioms HPC.Moore.m25_region_infinite
#print axioms HPC.Moore.m25_axioms1245
-- F.A. Theorems for the space of elements (`HPC/Moore/M25FA.lean`)
#print axioms HPC.Moore.m25_fa_theorem15
#print axioms HPC.Moore.m25_FA_1_15

-- ## Moore 1925 §I, Theorems 5–12 (batch 146)
-- Cut-point arcs; the circle characterization, Moore 1920 Theorem 4 (`HPC/Moore/CutArc.lean`)
#print axioms HPC.Moore.IsCutArc.exists_embedding
#print axioms HPC.Moore.isCutArc_image_Icc
#print axioms HPC.Moore.IsCutArc.isConnected_diff_ends
#print axioms HPC.Moore.circle_char
-- Borsuk's theorem for the plane (`HPC/Moore/Borsuk.lean`)
#print axioms HPC.Moore.borsuk_exists_log
-- Mullikin 1922, Theorem 5, corrected (`HPC/Moore/Mullikin.lean`)
#print axioms HPC.Moore.no_log_pow_of_bounded_component
#print axioms HPC.Moore.not_isConnected_compl_union
#print axioms HPC.Moore.compl_union_two_components
#print axioms HPC.Moore.mullikin_theorem5
-- Mullikin 1922, Theorem 4 at `M₁ ∩ M₂ = ∅` (`HPC/Moore/Mullikin4.lean`)
#print axioms HPC.Moore.mullikin_theorem4_disjoint
#print axioms HPC.Moore.not_mullikin_theorem4_disjoint_mathlib
-- Theorems 5–8 (`HPC/Moore/M25B5.lean`)
#print axioms HPC.Moore.not_separatesPlane_ptsOf
#print axioms HPC.Moore.m25_theorem5
#print axioms HPC.Moore.m25_theorem6
#print axioms HPC.Moore.m25_theorem7
#print axioms HPC.Moore.m25_theorem8
-- Theorems 9, 10, 12 (`HPC/Moore/M25B9.lean`)
#print axioms HPC.Moore.m25_theorem9
#print axioms HPC.Moore.m25_theorem10
#print axioms HPC.Moore.m25_theorem12
-- Theorem 11 (`HPC/Moore/M25B11.lean`)
#print axioms HPC.Moore.frontier_eq_of_scc
#print axioms HPC.Moore.m25_theorem11
-- The decomposition into points; the printed statements refuted (`HPC/Moore/M25BPts.lean`,
-- `HPC/Moore/M25BRefute.lean`)
#print axioms HPC.Moore.mooreDecomp_ptSetoid
#print axioms HPC.Moore.not_m25_theorem2_printed
#print axioms HPC.Moore.not_m25_theorem7_printed
#print axioms HPC.Moore.not_m25_theorem10_printed
#print axioms HPC.Moore.not_m25_theorem11_printed
#print axioms HPC.Moore.not_m25_theorem11_singleton
#print axioms HPC.Moore.not_mullikin_theorem5_printed
#print axioms HPC.Moore.not_moore1920_theorem4_singleton

-- ## Moore 1925 §I, Theorems 13–22 (batch 147)
-- Two arcs with only their ends in common are cut by any two points (`HPC/Moore/TSCCCut.lean`)
#print axioms HPC.Moore.Gen.tscc_cut
-- Interiors; arcs and closed curves of elements (`HPC/Moore/M25CInt.lean`)
#print axioms HPC.Moore.sccInterior_spec
#print axioms HPC.Moore.isSCCElt_union
#print axioms HPC.Moore.mooreRegion_of_restricted
#print axioms HPC.Moore.isArcElt_iff_tarc
#print axioms HPC.Moore.isSCCElt_iff_tscc
#print axioms HPC.Moore.th21Prop_restricted
#print axioms HPC.Moore.ax8Prop_restricted
-- Theorems 13, 14 (`HPC/Moore/M25C13.lean`)
#print axioms HPC.Moore.exists_tscc_of_arcs
#print axioms HPC.Moore.quot_janiszewski
#print axioms HPC.Moore.m25_theorem13
#print axioms HPC.Moore.m25_theorem14
-- Theorems 15–18 (`HPC/Moore/M25C15.lean`)
#print axioms HPC.Moore.m25_theorem15
#print axioms HPC.Moore.m25_theorem16
#print axioms HPC.Moore.m25_theorem17
#print axioms HPC.Moore.m25_theorem18
-- Theorem 19 (`HPC/Moore/M25C19.lean`)
#print axioms HPC.Moore.m25_theorem19
-- Theorem 20; Axioms 1–5, 8, 6′, 7′ for the restricted regions (`HPC/Moore/M25C20.lean`)
#print axioms HPC.Moore.m25_theorem20
#print axioms HPC.Moore.spaceRestricted_topology
#print axioms HPC.Moore.m25r_axiom1
#print axioms HPC.Moore.m25r_axiom2
#print axioms HPC.Moore.m25r_axiom3
#print axioms HPC.Moore.m25r_axiom4
#print axioms HPC.Moore.m25r_axiom5
#print axioms HPC.Moore.isArc_restricted_iff
#print axioms HPC.Moore.isSCC_restricted_iff
#print axioms HPC.Moore.m25r_axiom8
#print axioms HPC.Moore.m25_axioms6'7'
-- Axioms 6, 7 for the restricted regions, proved directly (`HPC/Moore/M25C6.lean`)
#print axioms HPC.Moore.exists_crosscut
#print axioms HPC.Moore.m25r_axiom6
#print axioms HPC.Moore.m25r_axiom7
-- Theorems 21, 22: the space of elements is a plane (`HPC/Moore/M25C.lean`)
#print axioms HPC.Moore.m25_theorem21
#print axioms HPC.Moore.m25_theorem22
#print axioms HPC.Moore.m25_theorem22_moore

-- ## Jones 1955 Theorem 2 (batch 148)
-- Jones 1949 Theorem 1 as printed fails for a point; the Jordan curve theorem from Moore 1925
-- Theorem 11; Borsuk invariance; countability (`HPC/Jones/Jones55T2A.lean`)
#print axioms HPC.Jones.not_jones49_theorem1_point
#print axioms HPC.Jones.tscc_circle
#print axioms HPC.Jones.jordan_curve_theorem
#print axioms HPC.Jones.separatesPlane_of_homeomorph
#print axioms HPC.Jones.countable_of_pairwiseDisjoint_open
-- Part (2); the decomposition `G′` of the plane (`HPC/Jones/Jones55T2D.lean`)
#print axioms HPC.Jones.uncountable_quotient
#print axioms HPC.Jones.jones55_compl_connected
#print axioms HPC.Jones.jones55_compl_continuumwise
#print axioms HPC.Jones.jones55_elt_not_separates
#print axioms HPC.Jones.gPrimeRel_equivalence
#print axioms HPC.Jones.isClosedMap_mk_gPrime
#print axioms HPC.Jones.mooreDecomp_gPrime
#print axioms HPC.Jones.jones55_plane
#print axioms HPC.Jones.jones55_embedding_data
#print axioms HPC.Jones.jones55_embedding
#print axioms HPC.Jones.isAposyndetic_iff_T
-- Theorem 2 and the closing remarks, assuming Jones 1949 Theorem 1 (`HPC/Jones/Jones55T2.lean`)
#print axioms HPC.Jones.isHomogeneous_Lset
#print axioms HPC.Jones.jones55_circle
#print axioms HPC.Jones.jones55_theorem2
#print axioms HPC.Jones.jones55_two_domains
#print axioms HPC.Jones.jones55_elements_indecomposable
#print axioms HPC.Jones.jones55_three_domains

-- ## Jones 1949: order, Menger, Whyburn 9.2 (batch 149)
-- Order of a point; invariance; subspaces; triods; local connectedness (`HPC/Jones/Jones49Order.lean`)
#print axioms HPC.Jones.hasOrder_homeomorph
#print axioms HPC.Jones.orderLE_subtype
#print axioms HPC.Jones.not_orderLE_two_of_triod
#print axioms HPC.Jones.locallyConnectedSpace_of_orderLE
-- A topological simple closed curve is a circle (`HPC/Jones/Jones49Circle.lean`)
#print axioms HPC.Jones.glue_circle
#print axioms HPC.Jones.tscc_homeomorph_circle
-- Menger's theorem on curves of order 2 (`HPC/Jones/Jones49Menger.lean`)
#print axioms HPC.Jones.exists_continuum_of_isOpen
#print axioms HPC.Jones.exists_tarc_of_orderLE
#print axioms HPC.Jones.arc_eq_of_legs
#print axioms HPC.Jones.menger_order_two
#print axioms HPC.Jones.jones49_order_two
-- Whyburn (9.1); boundary bumping for a compact piece (`HPC/Jones/Jones49Why.lean`)
#print axioms HPC.Jones.exists_continuum_bump_compact
#print axioms HPC.Jones.whyburn_9_1
-- (9.2) and `jones49_some_order_two` (open in batch 149, proved in batch 150 below); the reduction
-- of the latter to the former (`HPC/Jones/Jones49A.lean`)
#print axioms HPC.Jones.IsLocalSepPoint.homeomorph
#print axioms HPC.Jones.jones49_some_order_two_of_whyburn_9_2

-- ## Whyburn Ch. III; Moore 1922 (batch 150)
-- Countable non-limit points of a relation; clopen separation of components; separation chains
-- (`HPC/Jones/Jones49Chain.lean`)
#print axioms HPC.Jones.countable_not_mem_closure_of_lt
#print axioms HPC.Jones.exists_clopen_of_connectedComponentIn_disjoint
#print axioms HPC.Jones.SepChain.countable_not_good
#print axioms HPC.Jones.SepChain.countable_res
#print axioms HPC.Jones.SepChain.exists_small_interval
#print axioms HPC.Jones.SepChain.exists_open_frontier_pair
#print axioms HPC.Jones.SepChain.orderLE_two
#print axioms HPC.Jones.SepChain.countable_of_not_orderLE_two
-- Separating points of an open set have order 2 except for countably many
-- (`HPC/Jones/Jones49Sep.lean`)
#print axioms HPC.Jones.OrderLE.mono
#print axioms HPC.Jones.sepT_mem_component
#print axioms HPC.Jones.countable_sepT
#print axioms HPC.Jones.countable_sepPoint_not_orderLE_two
#print axioms HPC.Jones.not_orderLE_one_of_isSepPointOf
#print axioms HPC.Jones.hasOrder_two_of_isSepPointOf
#print axioms HPC.Jones.countable_sepPoint_not_hasOrder_two
-- Whyburn (3.2), (8.4), (8.41), (9.2); `jones49_some_order_two` (`HPC/Jones/Jones49B.lean`)
#print axioms HPC.Jones.whyburn_3_2
#print axioms HPC.Jones.whyburn_8_4
#print axioms HPC.Jones.whyburn_8_41
#print axioms HPC.Jones.whyburn_9_2
#print axioms HPC.Jones.jones49_some_order_two
-- Moore 1922, Theorems 1–3 (`HPC/Jones/Moore22.lean`)
#print axioms HPC.Jones.moore22_theorem1
#print axioms HPC.Jones.moore22_theorem2
#print axioms HPC.Jones.moore22_theorem3
-- Moore 1922, Theorem 4: the parts proved in batch 150 (Theorem 4 itself: batch 151 below)
-- (`HPC/Jones/Moore22T4.lean`)
#print axioms HPC.Jones.isPreconnected_compl_of_mooreSimplyConnected
#print axioms HPC.Jones.isConnected_frontier_of_mooreSimplyConnected
#print axioms HPC.Jones.locallyConnectedSpace_of_cikAt
#print axioms HPC.Jones.exists_crossing_continua

-- ## Crossing continua; Moore 1922 Theorem 4; complementary domains (batch 151)
-- The sector theorem and the cyclic order (`HPC/Jones/Jones49C.lean`, from
-- `HPC/Jones/Jones49CStrip.lean`, `Jones49COrder.lean`, `Jones49CAnn.lean`)
#print axioms HPC.Jones.sector_theorem
#print axioms HPC.Jones.sector_cyclic_order
#print axioms HPC.Jones.Sector.sector_two
#print axioms HPC.Jones.Sector.sector_cyclic
#print axioms HPC.Jones.Sector.lc_disjoint_rc
#print axioms HPC.Jones.Sector.exists_lift
-- Moore's sufficiency in local form; Moore 1922 Theorem 4 (`HPC/Jones/Jones49C.lean`,
-- `HPC/Jones/Jones49CMoore.lean`)
#print axioms HPC.Jones.moore22_sufficiency_local
#print axioms HPC.Jones.moore22_theorem4
#print axioms HPC.Jones.Sector.sufficiency_local
#print axioms HPC.Jones.Sector.propertyS_of_locallyConnected
#print axioms HPC.Jones.Sector.hloc_of_propertyS
#print axioms HPC.Jones.Sector.exists_crossing_continua_closed
#print axioms HPC.Jones.Sector.exists_cross_sub
#print axioms HPC.Jones.Sector.cikAt_of_locallyConnectedSpace
#print axioms HPC.Jones.Sector.sphere_walk
-- Complementary domains of plane continua (`HPC/Jones/Jones49C.lean`)
#print axioms HPC.Jones.isConnected_frontier_complDomain
#print axioms HPC.Jones.mooreSimplyConnected_complDomain
#print axioms HPC.Jones.isPreconnected_compl_connectedComponentIn_compl
-- Whyburn 1939 (6.22), §14 form (`HPC/Jones/Jones49C.lean`)
#print axioms HPC.Jones.whyburn39_6_22_sec14

-- ## Whyburn 1939 Theorem 14 (batch 152)
-- Items A–D (`HPC/Jones/Jones49D.lean`)
#print axioms HPC.Jones.whyburn39_moore_curve
#print axioms HPC.Jones.whyburn39_curve_from_order_two
#print axioms HPC.Jones.whyburn39_local_noncut
#print axioms HPC.Jones.whyburn39_theorem14
-- Supporting results (`HPC/Jones/Jones49DSep.lean`, `HPC/Jones/Jones49DCross.lean`)
#print axioms HPC.Jones.Sec14.join_in_domain
#print axioms HPC.Jones.Sec14.local_join_of_noncut
#print axioms HPC.Jones.Sec14.not_orderLE_of_accumulating
#print axioms HPC.Jones.Sec14.exists_bad_point_of_crossing
#print axioms HPC.Jones.Sec14.IsPreconnected.inter_frontier_nonempty'

-- ## Whyburn 1939 Corollary 1 (batch 153)
-- Items A–F (`HPC/Jones/Jones49E.lean`)
#print axioms HPC.Jones.tarc_of_isSimplePolyArc
#print axioms HPC.Jones.exists_tarc_of_locallyConnected
#print axioms HPC.Jones.accessible_of_cyclic
#print axioms HPC.Jones.frontier_cyclic
#print axioms HPC.Jones.theta_of_cyclic_peano
#print axioms HPC.Jones.whyburn39_corollary1
-- Supporting results (`Jones49EArc.lean`, `Jones49ETheta.lean`, `Jones49EAcc.lean`,
-- `Jones49EPlane.lean`)
#print axioms HPC.Jones.exists_tarc_in_open
#print axioms HPC.Jones.exists_tarc_of_isOpen_plane
#print axioms HPC.Jones.tscc_split
#print axioms HPC.Jones.exists_scc_of_cyclic
#print axioms HPC.Jones.exists_theta_of_cyclic
#print axioms HPC.Jones.frontier_diff_nonempty
#print axioms HPC.Jones.theta_not_subset_closure

-- ## Jones 1949 Theorems 1–2; Jones 1955 Theorem 2 unconditional (batch 154)
-- Items A–F (`HPC/Jones/Jones49F.lean`)
#print axioms HPC.Jones.jones49_setting
#print axioms HPC.Jones.jones49_simple_domains
#print axioms HPC.Jones.jones49_case1
#print axioms HPC.Jones.jones49_case2
#print axioms HPC.Jones.jones49_theorem1
#print axioms HPC.Jones.jones49_theorem2
#print axioms HPC.Jones.not_jones49_theorem2_point
#print axioms HPC.Jones.jones55_theorem2'
#print axioms HPC.Jones.jones55_two_domains'
#print axioms HPC.Jones.jones55_elements_indecomposable'
#print axioms HPC.Jones.jones55_three_domains'
-- Supporting results (`Jones49FTheta.lean`, `Jones49FLocal.lean`, `Jones49FCase1.lean`,
-- `Jones49FCase2.lean`)
#print axioms HPC.Jones.mem_cc_of_not_mem_domain
#print axioms HPC.Jones.theta_no_common_side
#print axioms HPC.Jones.theta_separation_core
#print axioms HPC.Jones.theta_separation
#print axioms HPC.Jones.isLocalSepPoint_of_open_sub_tscc
#print axioms HPC.Jones.isLocalSepPoint_of_separation
#print axioms HPC.Jones.frontier_cc_of_jordan
#print axioms HPC.Jones.exists_frontier_through
#print axioms HPC.Jones.countable_complDomains
#print axioms HPC.Jones.jones49_case1_core
#print axioms HPC.Moore.Gen.TArc.first_point_split
#print axioms HPC.Jones.exists_domain_meeting
#print axioms HPC.Jones.exists_theta_arcs
#print axioms HPC.Jones.jones49_case2_core

-- ## Hagopian 1975 (batch 155)
-- Items A–K (`HPC/Hagopian/Hagopian75.lean`)
#print axioms HPC.Hagopian.admissible_quotient_homeomorph
#print axioms HPC.Hagopian.composant_dense
#print axioms HPC.Hagopian.composant_eq_or_disjoint
#print axioms HPC.Hagopian.composant_isMeagre
#print axioms HPC.Hagopian.uncountable_composants
#print axioms HPC.Hagopian.moore_triod_theorem
#print axioms HPC.Hagopian.hagopian75_lemma1
#print axioms HPC.Hagopian.hagopian75_lemma1_hu
#print axioms HPC.Hagopian.hagopian75_lemma2
#print axioms HPC.Hagopian.admissible_end_sets'
#print axioms HPC.Hagopian.layer_subset_of_meets
#print axioms HPC.Hagopian.hagopian75_lemma3
#print axioms HPC.Hagopian.hagopian75_lemma3_unique
#print axioms HPC.Hagopian.hagopian75_lemma4
#print axioms HPC.Hagopian.hagopian75_no_indecomposable_interior
#print axioms HPC.Hagopian.hagopian75_exists_typeA'
#print axioms HPC.Hagopian.hagopian75_layer_invariant
#print axioms HPC.Hagopian.hagopian75_layer_homogeneous
#print axioms HPC.Hagopian.indecomposable_of_unicoherent_homogeneous
#print axioms HPC.Hagopian.hagopian75_theorem1_of_layer
-- Refutations and corrected forms (`H75Counter.lean`)
#print axioms HPC.Hagopian.not_admissible_end_sets
#print axioms HPC.Hagopian.arc_of_degenerate_layers'
#print axioms HPC.Hagopian.exists_arc_of_degenerate_layers
-- The sin(1/x) curve refutes the arc skeleton statement (`H75Sine.lean`)
#print axioms HPC.Hagopian.not_arc_of_degenerate_layers
#print axioms HPC.Hagopian.isIrreducibleBetween_sinCurve
#print axioms HPC.Hagopian.isAdmissibleMap_sinProj
#print axioms HPC.Hagopian.interior_sinProj_fibre
#print axioms HPC.Hagopian.not_nonempty_homeomorph_sinCurve
-- Moore's triod theorem (`H75MooreA.lean`, `H75MooreB.lean`, `H75Triod.lean`)
#print axioms HPC.Hagopian.interlace
#print axioms HPC.Hagopian.exists_loop_param
#print axioms HPC.Hagopian.interlace_param
#print axioms HPC.Hagopian.interlace_three
#print axioms HPC.Hagopian.countable_of_separating
#print axioms HPC.Hagopian.exists_cross_continuum
#print axioms HPC.Hagopian.countable_of_nonseparating
#print axioms HPC.Hagopian.moore_triod_theorem'
#print axioms HPC.Hagopian.mooreTriodStatement
#print axioms HPC.Hagopian.isTriodSet_image
#print axioms HPC.Hagopian.not_isTriod_univ_of_indecomposable
-- Supporting results (composants, Lemma 1, Kuratowski §48, Theorem 1)
#print axioms HPC.Hagopian.composant_isMeagre'
#print axioms HPC.Hagopian.uncountable_composants'
#print axioms HPC.Hagopian.hereditarilyUnicoherent_of_homogeneous_indecomposable
#print axioms HPC.Hagopian.atriodic_of_homogeneous_indecomposable
#print axioms HPC.Hagopian.separatesPlane_of_not_isPreconnected_inter
#print axioms HPC.Hagopian.not_isIndecomposable_of_typeA'
#print axioms HPC.Hagopian.end_layers
#print axioms HPC.Hagopian.eq_of_meets_ends
#print axioms HPC.Hagopian.layer_subset_of_meets'
#print axioms HPC.Hagopian.fibre_subset_fibre
#print axioms HPC.Hagopian.fibre_eq_iff
#print axioms HPC.Hagopian.IsDElt.chain
#print axioms HPC.Hagopian.IsDElt.exists_between
#print axioms HPC.Hagopian.exists_countable_dense_D
#print axioms HPC.Hagopian.exists_scale
#print axioms HPC.Hagopian.scaleMap_spec
#print axioms HPC.Hagopian.exists_typeA'_map
#print axioms HPC.Hagopian.isTypeA'_of_decomposable
#print axioms HPC.Hagopian.indecomposable_of_unicoherent_homogeneous_aux
#print axioms HPC.Hagopian.no_indecomposable_interior_aux
#print axioms HPC.Hagopian.exists_typeA'_aux
#print axioms HPC.Hagopian.hagopian75_layer_invariant_aux
#print axioms HPC.Hagopian.layer_homogeneous_aux
#print axioms HPC.Hagopian.theorem1_of_layer_aux

-- ## Hagopian 1976 §2 (batch 156)
-- Items B–D, H, I (`HPC/Hagopian/Hagopian76A.lean`); items D (first paragraph as printed, no
-- maximal element, sequence), E, F, G are open and commented out (OPEN.md)
#print axioms HPC.Hagopian.hagopian76_lemma2
#print axioms HPC.Hagopian.hagopian76_end_sets
#print axioms HPC.Hagopian.hagopian76_lemma3
#print axioms HPC.Hagopian.hagopian76_lemma4_layers'
#print axioms HPC.Hagopian.hagopian76_lemma4_chain
#print axioms HPC.Hagopian.hagopian76_lemma4_seq_of_noMax
#print axioms HPC.Hagopian.hagopian76_lemma4_of_branch
#print axioms HPC.Hagopian.hagopian76_lemma4_seq_of_branch
#print axioms HPC.Hagopian.hagopian76_lemma4
#print axioms HPC.Hagopian.hagopian76_lemma4_seq
#print axioms HPC.Hagopian.hagopian76_lemma8
#print axioms HPC.Hagopian.hagopian76_theorem2
#print axioms HPC.Hagopian.hagopian75_corollary
#print axioms HPC.Hagopian.hagopian75_theorem1
#print axioms HPC.Hagopian.hagopian75_theorem2
#print axioms HPC.Hagopian.bing60_plane
-- Supporting results (`HPC/Hagopian/H76*.lean`)
#print axioms HPC.Hagopian.lemma2_aux
#print axioms HPC.Hagopian.end_sets_aux
#print axioms HPC.Hagopian.subset_of_meets_avoids
#print axioms HPC.Hagopian.lemma3_end_case
#print axioms HPC.Hagopian.lemma3_half
#print axioms HPC.Hagopian.lemma3_aux
#print axioms HPC.Hagopian.ext_chain
#print axioms HPC.Hagopian.exists_strictMono_seq_of_chain
#print axioms HPC.Hagopian.lemma4_layers_aux
#print axioms HPC.Hagopian.connected_meets_links
#print axioms HPC.Hagopian.component_of_caps
#print axioms HPC.Hagopian.lemma8_aux
#print axioms HPC.Hagopian.isIndecomposable_of_h1_sub
#print axioms HPC.Hagopian.hagopian76_theorem2_aux
#print axioms HPC.Hagopian.hagopian75_corollary_aux
#print axioms HPC.Hagopian.isDecomposableSpace_of_sub
#print axioms HPC.Hagopian.hagopian75_theorem2_aux
#print axioms HPC.Hagopian.isHereditarilyDecomposable_of_arc
#print axioms HPC.Hagopian.bing60_plane_aux
#print axioms HPC.Hagopian.isAdmissibleMap_symm
#print axioms HPC.Hagopian.interior_symm_fibre
#print axioms HPC.Hagopian.meets_inter_of_cover
#print axioms HPC.Hagopian.ext_of_branch
#print axioms HPC.Hagopian.lemma4_of_branch
#print axioms HPC.Hagopian.lemma4_seq_of_branch
#print axioms HPC.Hagopian.layer_one_subset_closure
#print axioms HPC.Hagopian.tail_subset
#print axioms HPC.Hagopian.false_of_layer_open
#print axioms HPC.Hagopian.three_continua
#print axioms HPC.Hagopian.exists_image_map
#print axioms HPC.Hagopian.ext_of_irreducible_union
#print axioms HPC.Hagopian.not_subset_layer_of_open
#print axioms HPC.Hagopian.ext_of_subset
#print axioms HPC.Hagopian.ext_of_side
#print axioms HPC.Hagopian.exists_proper_extension
#print axioms HPC.Hagopian.lemma4_aux
#print axioms HPC.Hagopian.lemma4_seq_aux

-- ## Hagopian 1976 §2 continued (batch 157)
-- Skeleton theorems (`HPC/Hagopian/Hagopian76B.lean`)
#print axioms HPC.Hagopian.hagopian76_lemma4_layers_of_no_swallowed
#print axioms HPC.Hagopian.hagopian76_no_swallowed_of_lemma4_layers
#print axioms HPC.Hagopian.hagopian76_lemma5_interior
#print axioms HPC.Hagopian.hagopian76_lemma5_usc
#print axioms HPC.Hagopian.hagopian76_lemma5_of_ends
#print axioms HPC.Hagopian.no_proper_subcontinuum_separates
#print axioms HPC.Hagopian.layerSetoid_mooreDecomp
#print axioms HPC.Hagopian.exists_quotient_plane
#print axioms HPC.Hagopian.exists_accessible_typeA'
-- Supporting theorems (`H76SepInv`, `H76NoSep`, `H76D1`, `H76Lemma5`, `H76Setup`)
#print axioms HPC.Hagopian.no_log_of_separates
#print axioms HPC.Hagopian.log_mul_near_one
#print axioms HPC.Hagopian.LogData.ne_zero
#print axioms HPC.Hagopian.LogData.ratio
#print axioms HPC.Hagopian.LogData.exp_branch
#print axioms HPC.Hagopian.LogData.continuousOn_branch
#print axioms HPC.Hagopian.LogData.branch_sub
#print axioms HPC.Hagopian.LogData.exp_const
#print axioms HPC.Hagopian.LogData.exists_glue
#print axioms HPC.Hagopian.exists_log_of_isTreeLike
#print axioms HPC.Hagopian.exists_separating_subcontinuum_of_homeomorph
#print axioms HPC.Hagopian.separating_in_copy
#print axioms HPC.Hagopian.no_proper_subcontinuum_separates_aux
#print axioms HPC.Hagopian.IsMinimalAdmissible.isCompact
#print axioms HPC.Hagopian.layer_param_eq
#print axioms HPC.Hagopian.layer_nonempty
#print axioms HPC.Hagopian.lemma4_layers_of_no_swallowed
#print axioms HPC.Hagopian.no_swallowed_of_lemma4_layers
#print axioms HPC.Hagopian.lemma5_interior_aux
#print axioms HPC.Hagopian.isUSCDecomp_ker
#print axioms HPC.Hagopian.lemma5_of_ends_aux
#print axioms HPC.Hagopian.layerKey_of_mem
#print axioms HPC.Hagopian.layerKey_of_notMem
#print axioms HPC.Hagopian.mem_toPt_iff
#print axioms HPC.Hagopian.toPt_layer_eq
#print axioms HPC.Hagopian.elt_layerSetoid_of_mem
#print axioms HPC.Hagopian.elt_layerSetoid_of_notMem
#print axioms HPC.Hagopian.layer_usc
#print axioms HPC.Hagopian.isCompact_toPt
#print axioms HPC.Hagopian.layer_ne_univ
#print axioms HPC.Hagopian.isContinuum_layer_min
#print axioms HPC.Hagopian.layerSetoid_mooreDecomp_aux
#print axioms HPC.Hagopian.exists_quotient_plane_aux
#print axioms HPC.Hagopian.exists_accessible_point
#print axioms HPC.Hagopian.exists_accessible_typeA'_aux

-- ## Hagopian 1976 III (batch 158)
#print axioms HPC.Hagopian.hagopian76_far_layer
#print axioms HPC.Hagopian.hagopian76_initial_segment
#print axioms HPC.Hagopian.hagopian76_lemma4_layers
#print axioms HPC.Hagopian.hagopian76_no_swallowed_layer
#print axioms HPC.Hagopian.hagopian76_lemma5
#print axioms HPC.Hagopian.moore62_theorem28
#print axioms HPC.Hagopian.exists_quotient_plane'
-- Supporting theorems (`H76Far`, `H76Lemma5End`, `H76Moore28`, `H76Quot`, `H76Sub`)
#print axioms HPC.Hagopian.lemma4_layers_far
#print axioms HPC.Hagopian.closure_inter_of_preconnected
#print axioms HPC.Hagopian.layer_subset_dom
#print axioms HPC.Hagopian.far_layer_aux
#print axioms HPC.Hagopian.IsMinimalAdmissible.symm_comp
#print axioms HPC.Hagopian.layer_symm_comp
#print axioms HPC.Hagopian.ext_layers
#print axioms HPC.Hagopian.initial_segment_aux
#print axioms HPC.Hagopian.lscAt_of_ext
#print axioms HPC.Hagopian.lscAt_end_aux
#print axioms HPC.Hagopian.lemma5_aux
#print axioms HPC.Hagopian.tscc_split_at
#print axioms HPC.Hagopian.TSCC.isCompact'
#print axioms HPC.Hagopian.TSCC.isConnected'
#print axioms HPC.Hagopian.tscc_aposyndetic
#print axioms HPC.Hagopian.tscc_cyclic
#print axioms HPC.Hagopian.exists_side_arc
#print axioms HPC.Hagopian.moore28_core
#print axioms HPC.Hagopian.moore62_theorem28_aux
#print axioms HPC.Hagopian.exists_quotient_plane'_aux
#print axioms HPC.Hagopian.layerSet_Ioo_subset
#print axioms HPC.Hagopian.layer_subset_closure_Ioo
#print axioms HPC.Hagopian.layer_subset_closure_Ioo'
#print axioms HPC.Hagopian.eq_layerSet_of_subcontinuum
#print axioms HPC.Hagopian.isTypeA'_of_subcontinuum

-- ## Hagopian 1976 IV (batch 159)
#print axioms HPC.Hagopian.plane_schoenflies
#print axioms HPC.Hagopian.exists_collar
#print axioms HPC.Hagopian.hagopian76_lemma8_caps
-- Supporting theorems (`H76Schoen`, `H76Invert`, `H76Collar`, `H76Lemma8Caps`)
#print axioms HPC.Hagopian.quad_split_pt
#print axioms HPC.Hagopian.eq_or_eq_of_frontier
#print axioms HPC.Hagopian.plane_schoenflies_aux
#print axioms HPC.Hagopian.image_eq_sccInterior
#print axioms HPC.Hagopian.region_restricted_pt
#print axioms HPC.Hagopian.plane_split
#print axioms HPC.Hagopian.isOpen_strip
#print axioms HPC.Hagopian.exists_open_inter_range
#print axioms HPC.Hagopian.isHalfCollar_bounded
#print axioms HPC.Hagopian.nsq_pos
#print axioms HPC.Hagopian.nsq_inv0
#print axioms HPC.Hagopian.inv0_ne_zero
#print axioms HPC.Hagopian.inv0_inv0
#print axioms HPC.Hagopian.continuousOn_inv0
#print axioms HPC.Hagopian.sq_le_nsq
#print axioms HPC.Hagopian.nsq_le_sq
#print axioms HPC.Hagopian.invcInv_invc
#print axioms HPC.Hagopian.invc_invcInv
#print axioms HPC.Hagopian.invc_ne_zero
#print axioms HPC.Hagopian.invcInv_ne
#print axioms HPC.Hagopian.continuousOn_invc
#print axioms HPC.Hagopian.continuousOn_invcInv
#print axioms HPC.Hagopian.invc_injOn
#print axioms HPC.Hagopian.tarc_image_of_injOn
#print axioms HPC.Hagopian.tscc_image_of_injOn
#print axioms HPC.Hagopian.invcInv_injOn
#print axioms HPC.Hagopian.isHalfCollar_unbounded
#print axioms HPC.Hagopian.accessible_of_noncut
#print axioms HPC.Hagopian.semiLocConnAt_of_locallyConnected
#print axioms HPC.Hagopian.locallyConnectedSpace_unitInterval
#print axioms HPC.Hagopian.TArc.semiLocConnAt
#print axioms HPC.Hagopian.TArc.isConnected_compl
#print axioms HPC.Hagopian.TArc.interior_eq_empty
#print axioms HPC.Hagopian.TArc.isConnected_compl_end
#print axioms HPC.Hagopian.TArc.exists_closing_arc
#print axioms HPC.Hagopian.exists_collar_aux
#print axioms HPC.Hagopian.lemma8_caps_aux

-- ## Hagopian 1976 V (batch 160)
-- skeleton theorems (`HPC/Hagopian/Hagopian76E.lean`)
#print axioms HPC.Hagopian.hagopian76_lemma6_X
#print axioms HPC.Hagopian.hagopian76_closure_extUnion
#print axioms HPC.Hagopian.hagopian76_lemma6
#print axioms HPC.Hagopian.hagopian76_Rset_composant
#print axioms HPC.Hagopian.hagopian76_essential_typeA'
#print axioms HPC.Hagopian.layer_nbhd_small
#print axioms HPC.Hagopian.plane_schoenflies₂
-- supporting (`H76USC`, `H76Schoen2`, `H76Absorb`, `H76Lemma6`, `H76Step8`, `H76Composant`, `H76Essential`)
#print axioms HPC.Hagopian.layer_nbhd_small_aux
#print axioms HPC.Hagopian.quad_split_two_pt
#print axioms HPC.Hagopian.plane_schoenflies₂_aux
#print axioms HPC.Hagopian.ext_of_irreducible_union_eq
#print axioms HPC.Hagopian.absorb_point
#print axioms HPC.Hagopian.subset_extUnion_of_meets
#print axioms HPC.Hagopian.exists_pos_le_dist
#print axioms HPC.Hagopian.layer_zero_subset_closure
#print axioms HPC.Hagopian.layer_zero_subset_of_meets
#print axioms HPC.Hagopian.subset_of_meets_ends
#print axioms HPC.Hagopian.IsExtensionAway.isContinuum
#print axioms HPC.Hagopian.IsExtensionAway.subset_extUnion
#print axioms HPC.Hagopian.IsExtensionAway.end_subset
#print axioms HPC.Hagopian.exists_mem_ext_not_mem
#print axioms HPC.Hagopian.isContinuum_closure_extUnion
#print axioms HPC.Hagopian.ext_upper
#print axioms HPC.Hagopian.lemma6_step1
#print axioms HPC.Hagopian.lemma6_step2
#print axioms HPC.Hagopian.lemma6_step3
#print axioms HPC.Hagopian.lemma6_main
#print axioms HPC.Hagopian.lemma6_X_aux
#print axioms HPC.Hagopian.mem_layerSet_val
#print axioms HPC.Hagopian.mem_layer_val
#print axioms HPC.Hagopian.false_of_indec_subset_layers
#print axioms HPC.Hagopian.extUnion_one_subset
#print axioms HPC.Hagopian.closure_extUnion_aux
#print axioms HPC.Hagopian.lemma6_aux
#print axioms HPC.Hagopian.not_indec_of_minimalAdmissible
#print axioms HPC.Hagopian.closure_extUnion_one
#print axioms HPC.Hagopian.not_isClosed_extUnion
#print axioms HPC.Hagopian.subset_union_of_escape
#print axioms HPC.Hagopian.exists_ext_of_subset
#print axioms HPC.Hagopian.ext_inter_subset
#print axioms HPC.Hagopian.Rset_composant_aux
#print axioms HPC.Hagopian.lsc_of_minimalAdmissible
#print axioms HPC.Hagopian.Rset_symm_comp
#print axioms HPC.Hagopian.IsEssential.symm_comp
#print axioms HPC.Hagopian.end_layer_param
#print axioms HPC.Hagopian.essential_typeA'_of_subset
#print axioms HPC.Hagopian.not_isClosed_Rset
#print axioms HPC.Hagopian.exists_ext_cover
#print axioms HPC.Hagopian.essential_typeA'_two_sided
#print axioms HPC.Hagopian.essential_typeA'_aux

-- ## Hagopian 1976 VI (batch 161)
-- skeleton theorems (`HPC/Hagopian/Hagopian76F.lean`)
#print axioms HPC.Hagopian.hagopian76_eps1
#print axioms HPC.Hagopian.hagopian76_eps1_chain
#print axioms HPC.Hagopian.exists_Gset
#print axioms HPC.Hagopian.hagopian76_chain11
#print axioms HPC.Hagopian.hagopian76_property1
#print axioms HPC.Hagopian.hagopian76_T9
#print axioms HPC.Hagopian.hagopian76_property3_shift
#print axioms HPC.Hagopian.hagopian76_lemma7_triod
#print axioms HPC.Hagopian.hagopian76_lemma7_of_F
-- supporting theorems (`H76Eps1`, `H76Lemma8Sep`, `H76Prop1`, `H76T9`, `H76Lemma7`, `H76Prop3`)
#print axioms HPC.Hagopian.isClosed_interval_set
#print axioms HPC.Hagopian.isCompact_layerSet_interval
#print axioms HPC.Hagopian.exists_pos_forall_finset
#print axioms HPC.Hagopian.piece_disjoint
#print axioms HPC.Hagopian.ends_middle_disjoint
#print axioms HPC.Hagopian.exists_isEps1
#print axioms HPC.Hagopian.isEps1_thickening_disjoint
#print axioms HPC.Hagopian.lemma8_caps_sep
#print axioms HPC.Hagopian.isOpen_Gset
#print axioms HPC.Hagopian.Gset_subset_ball
#print axioms HPC.Hagopian.inter_Gset_subset
#print axioms HPC.Hagopian.toPt_Wset_eq
#print axioms HPC.Hagopian.mem_Gset_of_homeo
#print axioms HPC.Hagopian.exists_Gset_aux
#print axioms HPC.Hagopian.piece_succ
#print axioms HPC.Hagopian.exists_elev
#print axioms HPC.Hagopian.exists_elev_between
#print axioms HPC.Hagopian.layer_subset_layerSet
#print axioms HPC.Hagopian.follows_of_elev
#print axioms HPC.Hagopian.isOpen_chainG
#print axioms HPC.Hagopian.chainG_subset_thickening
#print axioms HPC.Hagopian.image_piece_subset_chainG
#print axioms HPC.Hagopian.piece_subset_chainG
#print axioms HPC.Hagopian.elev_inter_nonempty
#print axioms HPC.Hagopian.isPlaneChain_of_pieces
#print axioms HPC.Hagopian.chainG_isPlaneChain
#print axioms HPC.Hagopian.toPt_layerSet_elev
#print axioms HPC.Hagopian.chainG_follows
#print axioms HPC.Hagopian.chainG_follows_self
#print axioms HPC.Hagopian.thickChain_follows
#print axioms HPC.Hagopian.piece_subset_middle
#print axioms HPC.Hagopian.middle_subset_pieces
#print axioms HPC.Hagopian.isPreconnected_middle
#print axioms HPC.Hagopian.property1_aux
#print axioms HPC.Hagopian.subset_Rset
#print axioms HPC.Hagopian.T9_aux
#print axioms HPC.Hagopian.lemma7_triod
#print axioms HPC.Hagopian.mem_closure_of_near
#print axioms HPC.Hagopian.lemma7_of_F
#print axioms HPC.Hagopian.exists_F_of_not_mem_composant
#print axioms HPC.Hagopian.lemma7_of_F_composant
#print axioms HPC.Hagopian.layer_shift


-- ## Hagopian 1976 VII (batch 162)
-- skeleton `HPC/Hagopian/Hagopian76G.lean`
#print axioms HPC.Hagopian.halfray_dense
#print axioms HPC.Hagopian.halfray_inter
#print axioms HPC.Hagopian.hagopian76_lemma7
#print axioms HPC.Hagopian.hagopian76_property2
-- supporting: `H76HalfRay.lean`, `H76Lemma7Ray.lean`
#print axioms HPC.Hagopian.piece_end_layers
#print axioms HPC.Hagopian.piece_map
#print axioms HPC.Hagopian.Rset_eq_of_maps
#print axioms HPC.Hagopian.extUnion_eq_of_subset
#print axioms HPC.Hagopian.closure_Rset_eq_of_subset
#print axioms HPC.Hagopian.closure_Rset_piece
#print axioms HPC.Hagopian.closure_Rset_of_common
#print axioms HPC.Hagopian.closure_Rset_essential
#print axioms HPC.Hagopian.halfray_inter_subset
#print axioms HPC.Hagopian.halfray_dense_aux
#print axioms HPC.Hagopian.exists_F_halfray
#print axioms HPC.Hagopian.lemma7_aux

-- ## Hagopian 1976 VIII (batch 163)
-- skeleton `HPC/Hagopian/Hagopian76H.lean`
#print axioms HPC.Hagopian.exists_collar_adapted
#print axioms HPC.Hagopian.no_M_below
#print axioms HPC.Hagopian.hagopian76_lemma9
#print axioms HPC.Hagopian.hagopian76_T6
#print axioms HPC.Hagopian.hagopian76_T3
-- supporting: `H76Adapt.lean`
#print axioms HPC.Hagopian.tarc_hseg
#print axioms HPC.Hagopian.tarc_vseg
#print axioms HPC.Hagopian.IsCollar.flip
#print axioms HPC.Hagopian.IsCollar.exists_continuous
#print axioms HPC.Hagopian.exists_drop_arc
-- supporting: `H76Rect.lean`
#print axioms HPC.Hagopian.rect_frontier
#print axioms HPC.Hagopian.rect_tarc₁
#print axioms HPC.Hagopian.rect_tarc₂
#print axioms HPC.Hagopian.rect_inter
#print axioms HPC.Hagopian.rectC₁_axis
#print axioms HPC.Hagopian.rectC₂_axis
-- supporting: `H76Glue.lean`
#print axioms HPC.Hagopian.clampI_val
#print axioms HPC.Hagopian.clampI_zero
#print axioms HPC.Hagopian.clampI_coe
#print axioms HPC.Hagopian.clampI_inj
#print axioms HPC.Hagopian.glue_memL
#print axioms HPC.Hagopian.glue_memR
#print axioms HPC.Hagopian.glueMap_L
#print axioms HPC.Hagopian.glueMap_R
#print axioms HPC.Hagopian.glueMap_vert
#print axioms HPC.Hagopian.glueMap_continuous
#print axioms HPC.Hagopian.glueMap_top
#print axioms HPC.Hagopian.glueMap_injOn
#print axioms HPC.Hagopian.glueMap_mapsTo
#print axioms HPC.Hagopian.glueMap_snd
#print axioms HPC.Hagopian.glueMap_image_sub
#print axioms HPC.Hagopian.glueMap_image_sup
-- supporting: `H76AdaptHalf.lean`
#print axioms HPC.Hagopian.halfcollar_side
#print axioms HPC.Hagopian.exists_lower_halfcollar
-- supporting: `H76AdaptMain.lean`
#print axioms HPC.Hagopian.collar_adapted_core
#print axioms HPC.Hagopian.exists_collar_adapted_aux
-- supporting: `H76NoBelow.lean`
#print axioms HPC.Hagopian.mem_layer_of_pi_eq
#print axioms HPC.Hagopian.disjoint_toPt_layerSet
#print axioms HPC.Hagopian.layer_close_of_pi_close
#print axioms HPC.Hagopian.IsCollar.isOpen_image
#print axioms HPC.Hagopian.IsCollar.uniform_height
#print axioms HPC.Hagopian.exists_closedBall_disjoint
#print axioms HPC.Hagopian.chain3_follows
-- supporting: `H76NoBelowCore.lean`
#print axioms HPC.Hagopian.no_M_below_core
-- supporting: `H76NoBelowMain.lean`
#print axioms HPC.Hagopian.no_M_below_left
#print axioms HPC.Hagopian.IsMinimalAdmissible.symm'
#print axioms HPC.Hagopian.layer_symm
#print axioms HPC.Hagopian.layerSetoid_symm
#print axioms HPC.Hagopian.IsCollar.reverse
#print axioms HPC.Hagopian.no_M_below_aux
#print axioms HPC.Hagopian.exists_collar_vertical

-- ## Names matching `*_false` that are helper lemmas, not refutations (listed for completeness)
#print axioms HPC.Plane.Org.frequently_false
#print axioms HPC.Plane.Org.isLeftEnd_of_last_false
#print axioms HPC.Plane.Org.lam_const_false
#print axioms HPC.Plane.Org.lam_flip1_false
#print axioms HPC.Plane.Org.lastF_succ_false
#print axioms HPC.Plane.Org.lastT_succ_false
#print axioms HPC.Plane.Org.zz_le_of_conf_false
#print axioms HPC.Plane.PA51.limit_false
#print axioms HPC.Plane.preconnected_closed_split_false


-- ## Hagopian 1976 IX (batch 164)
-- skeleton `HPC/Hagopian/Hagopian76I.lean`
#print axioms HPC.Hagopian.hagopian76_reparam
#print axioms HPC.Hagopian.hagopian76_T6_placed
#print axioms HPC.Hagopian.hagopian76_I1
#print axioms HPC.Hagopian.hagopian76_T7_accessible
#print axioms HPC.Hagopian.hagopian76_eps2_pos
-- supporting: `H76Reparam.lean`
#print axioms HPC.Hagopian.IsMinimalAdmissible.homeo
#print axioms HPC.Hagopian.layer_homeo
#print axioms HPC.Hagopian.layer_homeo_apply
#print axioms HPC.Hagopian.layerSetoid_homeo
#print axioms HPC.Hagopian.setup_homeo
#print axioms HPC.Hagopian.plr_of_le
#print axioms HPC.Hagopian.plr_of_lt
#print axioms HPC.Hagopian.plr_zero
#print axioms HPC.Hagopian.plr_one
#print axioms HPC.Hagopian.plr_self
#print axioms HPC.Hagopian.continuous_plr
#print axioms HPC.Hagopian.plr_le_iff
#print axioms HPC.Hagopian.plr_plr
#print axioms HPC.Hagopian.plr_strictMono
#print axioms HPC.Hagopian.plr_mem_Icc
#print axioms HPC.Hagopian.plr_mem_Ioo
#print axioms HPC.Hagopian.plrI_coe
#print axioms HPC.Hagopian.plrI_symm_coe
#print axioms HPC.Hagopian.image_plr_rect
#print axioms HPC.Hagopian.IsCollar.plrTransport
-- supporting: `H76Above.lean`
#print axioms HPC.Hagopian.eq_of_pi_eq_off
#print axioms HPC.Hagopian.pi_mem_range_of_mem
#print axioms HPC.Hagopian.pi_isOpen_image_off
#print axioms HPC.Hagopian.M_meets_above
#print axioms HPC.Hagopian.exists_notMem_piM
-- supporting: `H76AboveAcc.lean`
#print axioms HPC.Hagopian.IsCollar.disjoint_range_above
#print axioms HPC.Hagopian.exists_accessible_above
#print axioms HPC.Hagopian.exists_pos_dist_preimage

-- ## Hagopian 1976 X (batch 165)
-- skeleton `HPC/Hagopian/Hagopian76J.lean`
#print axioms HPC.Hagopian.rect_crossing
#print axioms HPC.Hagopian.hagopian76_no_hair
#print axioms HPC.Hagopian.preimage_pi_isContinuum
#print axioms HPC.Hagopian.hagopian76_T7
#print axioms HPC.Hagopian.exists_isEps1_endCtl
#print axioms HPC.Hagopian.hagopian76_link_control
#print axioms HPC.Hagopian.hagopian76_T8
#print axioms HPC.Hagopian.hagopian76_T9_full
#print axioms HPC.Hagopian.hagopian76_T11
-- supporting: `H76Crossing.lean`
#print axioms HPC.Hagopian.rect_split
#print axioms HPC.Hagopian.staple_isPreconnected
#print axioms HPC.Hagopian.frame_arc
#print axioms HPC.Hagopian.arc_cut
#print axioms HPC.Hagopian.rect_crossing_aux
-- supporting: `H76NoHair.lean`
#print axioms HPC.Hagopian.isPreconnected_preimage_of_fibres
#print axioms HPC.Hagopian.no_hair_aux
#print axioms HPC.Hagopian.isConnected_pi_fibre
#print axioms HPC.Hagopian.preimage_pi_isContinuum_aux
-- supporting: `H76T7.lean`
#print axioms HPC.Hagopian.isOpen_pi_image
#print axioms HPC.Hagopian.exists_height_below
#print axioms HPC.Hagopian.hagopian76_T7_aux
-- supporting: `H76Thin.lean`
#print axioms HPC.Hagopian.exists_pos_lt_on_compact
#print axioms HPC.Hagopian.mem_layer_of_pi_eq_gamma
#print axioms HPC.Hagopian.pi_thin_near_layer
#print axioms HPC.Hagopian.exists_isEps1_endCtl_aux
#print axioms HPC.Hagopian.mem_piece_ceil
#print axioms HPC.Hagopian.link_control_aux
-- supporting: `H76T9Full.lean`
#print axioms HPC.Hagopian.strip_in_links
#print axioms HPC.Hagopian.closure_disjoint_E_of_above
#print axioms HPC.Hagopian.T11_aux

-- ## Hagopian 1976 XI (batch 166)
-- skeleton `HPC/Hagopian/Hagopian76K.lean`
#print axioms HPC.Hagopian.rect_domain
#print axioms HPC.Hagopian.hagopian76_D
#print axioms HPC.Hagopian.hagopian76_K0
#print axioms HPC.Hagopian.hagopian76_K0_crosscut
-- supporting: `H76Domain.lean`
#print axioms HPC.Hagopian.isConnected_compl_rect
#print axioms HPC.Hagopian.tarc_frame
#print axioms HPC.Hagopian.rect_domain_aux
#print axioms HPC.Hagopian.rect_domain_low
#print axioms HPC.Hagopian.rect_domain_vert
-- supporting: `H76DCollar.lean`
#print axioms HPC.Hagopian.pi_isClosedMap
#print axioms HPC.Hagopian.pi_preimage_isPreconnected
#print axioms HPC.Hagopian.tarc_pullback
#print axioms HPC.Hagopian.hagopian76_D_aux
#print axioms HPC.Hagopian.mem_toPt_layer_of_pi_eq
#print axioms HPC.Hagopian.K0_aux
-- supporting: `H76Crosscut.lean`
#print axioms HPC.Hagopian.rect_domain_crosscut
#print axioms HPC.Hagopian.K0_crosscut_aux
-- supporting: `H76TwoComposants.lean`
#print axioms HPC.Hagopian.exists_two_composants_in_open

-- ## Hagopian 1976 XII (batch 167)
-- skeleton `HPC/Hagopian/Hagopian76L.lean`
#print axioms HPC.Hagopian.crossing_translate
#print axioms HPC.Hagopian.K0_dense_low
#print axioms HPC.Hagopian.crossing_essential
#print axioms HPC.Hagopian.hagopian76_T12_parts12
-- supporting: `H76Translate.lean`
#print axioms HPC.Hagopian.exists_mem_closure_component_notMem
#print axioms HPC.Hagopian.isPreconnected_interval_set
#print axioms HPC.Hagopian.collar_injOn
#print axioms HPC.Hagopian.openRect_subset_rect
#print axioms HPC.Hagopian.isOpen_collar_image
#print axioms HPC.Hagopian.collar_uniform
#print axioms HPC.Hagopian.pi_near_collar
-- supporting: `H76TranslateMain.lean`
#print axioms HPC.Hagopian.dist_prod_lt
#print axioms HPC.Hagopian.crossing_translate_aux
-- supporting: `H76K0Dense.lean`
#print axioms HPC.Hagopian.K0_low_point_aux
#print axioms HPC.Hagopian.K0_dense_low_aux
#print axioms HPC.Hagopian.T12_crossing_aux
-- supporting: `H76CrossEss.lean`
#print axioms HPC.Hagopian.crossing_essential_aux
#print axioms HPC.Hagopian.T12_parts12_aux

-- ## Hagopian 1976 XIII (batch 168)
-- skeleton `HPC/Hagopian/Hagopian76M.lean`
#print axioms HPC.Hagopian.crossing_piece_of_R
#print axioms HPC.Hagopian.crossing_separates
#print axioms HPC.Hagopian.crossing_pair_separates
#print axioms HPC.Hagopian.hagopian76_T12
-- supporting: `H76TranslateIn.lean`
#print axioms HPC.Hagopian.crossing_translate_in_aux
-- supporting: `H76RPiece.lean`
#print axioms HPC.Hagopian.mem_closure_extUnion_diff
#print axioms HPC.Hagopian.crossing_piece_of_R_aux
-- supporting: `H76PairSep.lean`
#print axioms HPC.Hagopian.rect_domain_crosscut_arc
#print axioms HPC.Hagopian.seg_subset_rect_domain
#print axioms HPC.Hagopian.mem_vsegment
#print axioms HPC.Hagopian.rect_domain_crossing_separates
-- supporting: `H76CrossSep.lean`
#print axioms HPC.Hagopian.injOn_pi_preimage
#print axioms HPC.Hagopian.crossing_separates_aux
-- supporting: `H76T12.lean`
#print axioms HPC.Hagopian.T12_part3_aux

-- ## Hagopian 1976 XIV (batch 169)
-- skeleton `HPC/Hagopian/Hagopian76N.lean`
#print axioms HPC.Hagopian.isMeagre_Rset
#print axioms HPC.Hagopian.crossing_sides
#print axioms HPC.Hagopian.exists_generic_pq
#print axioms HPC.Hagopian.hagopian76_T12_of_dichotomy
#print axioms HPC.Hagopian.Rset_homeo_dichotomy_of_closure
#print axioms HPC.Hagopian.iInter_chain_extension
#print axioms HPC.Hagopian.hagopian76_T13
-- supporting: `H76Meagre.lean`
#print axioms HPC.Hagopian.extension_proper
#print axioms HPC.Hagopian.Rset_subset_composant
#print axioms HPC.Hagopian.isMeagre_Rset_aux
#print axioms HPC.Hagopian.exists_notMem_Rset
-- supporting: `H76Sides.lean`
#print axioms HPC.Hagopian.isOpen_joined
#print axioms HPC.Hagopian.belowSet_isOpen
#print axioms HPC.Hagopian.aboveSet_isOpen
#print axioms HPC.Hagopian.mem_belowSet
#print axioms HPC.Hagopian.mem_aboveSet
#print axioms HPC.Hagopian.belowSet_of_preconnected
#print axioms HPC.Hagopian.aboveSet_of_preconnected
#print axioms HPC.Hagopian.crossing_sides_aux
-- supporting: `H76T12Sides.lean`
#print axioms HPC.Hagopian.T12_sides_aux
-- supporting: `H76Generic.lean`
#print axioms HPC.Hagopian.SepIn.mono
#print axioms HPC.Hagopian.subset_Rset_self
#print axioms HPC.Hagopian.val_mem_toPt_iff
#print axioms HPC.Hagopian.exists_generic_pq_aux
-- supporting: `H76Dichot.lean`
#print axioms HPC.Hagopian.image_composant
#print axioms HPC.Hagopian.disjoint_image_Rset
#print axioms HPC.Hagopian.Rset_dichotomy_of_closure_aux
-- supporting: `H76ChainSep.lean`
#print axioms HPC.Hagopian.sepIn_iInter_of_directed
#print axioms HPC.Hagopian.directed_supset_of_isChain
#print axioms HPC.Hagopian.toPt_sInter
#print axioms HPC.Hagopian.sepIn_sInter_chain
#print axioms HPC.Hagopian.iInter_chain_isContinuum
#print axioms HPC.Hagopian.T13_of_chainInter

-- ## Hagopian 1976 XV (batch 170)
-- skeleton `HPC/Hagopian/Hagopian76O.lean`
#print axioms HPC.Hagopian.extChainInter_in
#print axioms HPC.Hagopian.extChainInter
#print axioms HPC.Hagopian.hagopian76_T13_uncond
#print axioms HPC.Hagopian.crossing_sides_cover_frontier
#print axioms HPC.Hagopian.follows_crossing
#print axioms HPC.Hagopian.hagopian76_first_crossing_param
-- supporting: `H76ChainInter.lean`
#print axioms HPC.Hagopian.mem_layerSet_Icc_zero
#print axioms HPC.Hagopian.extChainInter_in_aux
#print axioms HPC.Hagopian.extChainInter_aux
-- supporting: `H76Follows.lean`
#print axioms HPC.Hagopian.T9_pieces_aux
#print axioms HPC.Hagopian.follows_crossing_aux
-- supporting: `H76Cover.lean`
#print axioms HPC.Hagopian.component_frontier_meets
#print axioms HPC.Hagopian.component_frontier_meets_of_subcontinuum
#print axioms HPC.Hagopian.component_reaches_frontier_D
-- supporting: `H76CrossClosed.lean`
#print axioms HPC.Hagopian.limsup_mem_of_tendsto
#print axioms HPC.Hagopian.limsup_subset_of_eventually
#print axioms HPC.Hagopian.limsup_isPreconnected
#print axioms HPC.Hagopian.isClosed_crossing_params
#print axioms HPC.Hagopian.crossing_set_closed

-- ## Hagopian 1976 XVI (batch 171)
-- skeleton `HPC/Hagopian/Hagopian76P.lean`
#print axioms HPC.Hagopian.layer_meets_translate_end
#print axioms HPC.Hagopian.hagopian76_property3_reduced
#print axioms HPC.Hagopian.crossing_bottom_below
#print axioms HPC.Hagopian.hagopian76_T12_uncond
-- supporting: `H76Prop3L3.lean`
#print axioms HPC.Hagopian.layer_meets_translate_end_aux
#print axioms HPC.Hagopian.translate_params_ordConnected
#print axioms HPC.Hagopian.layer_meets_translate_initial
-- supporting: `H76Bottom.lean`
#print axioms HPC.Hagopian.isPreconnected_preimage_off
#print axioms HPC.Hagopian.bottom_component_below_aux
-- supporting: `H76GenericComp.lean`
#print axioms HPC.Hagopian.translate_Rset_disjoint
#print axioms HPC.Hagopian.exists_generic_pq_comp_aux

-- ## Hagopian 1976 XVII (batch 172)
-- skeleton `HPC/Hagopian/Hagopian76Q.lean`
#print axioms HPC.Hagopian.hagopian76_property3_translate
#print axioms HPC.Hagopian.hagopian76_property3_of_end
#print axioms HPC.Hagopian.closure_Rset_subset_of_translate
#print axioms HPC.Hagopian.property3End_of_closure_Rset
#print axioms HPC.Hagopian.property3End_of_dichotomy
#print axioms HPC.Hagopian.hagopian76_property3_of_closure
#print axioms HPC.Hagopian.crossing_sides_cover_schoenflies
-- supporting: `H76Swallow.lean`
#print axioms HPC.Hagopian.layerSet_eq_inter_open
#print axioms HPC.Hagopian.mem_layer_self
#print axioms HPC.Hagopian.param_of_mem_layer
#print axioms HPC.Hagopian.swallow_core
#print axioms HPC.Hagopian.continuum_subset_layer_of_open
#print axioms HPC.Hagopian.translate_subset_layer
#print axioms HPC.Hagopian.translate_extension_subset_layer
#print axioms HPC.Hagopian.layer_disjoint_of_not_subset
-- supporting: `H76InnerCollar.lean`
#print axioms HPC.Hagopian.jordan_inner_collar
#print axioms HPC.Hagopian.rect_frontier_domain
#print axioms HPC.Hagopian.top_component_above_aux

-- ## Hagopian 1976 XVIII (batch 173)
-- skeleton `HPC/Hagopian/Hagopian76R.lean`
#print axioms HPC.Hagopian.crossing_from_layer_translate
#print axioms HPC.Hagopian.crossing_descends
#print axioms HPC.Hagopian.isCrossRegion_of_D
#print axioms HPC.Hagopian.hagopian76_property3_domain
#print axioms HPC.Hagopian.hagopian76_property3
#print axioms HPC.Hagopian.crossing_length_pos
-- supporting: `H76Descent.lean`
#print axioms HPC.Hagopian.exists_eleventh_le
#print axioms HPC.Hagopian.exists_eleventh_ge
#print axioms HPC.Hagopian.IsEps1.sep_of_gap
#print axioms HPC.Hagopian.isCompact_collar_image
#print axioms HPC.Hagopian.rect_sub
#print axioms HPC.Hagopian.layer_mem_E_same
#print axioms HPC.Hagopian.isClosed_layer
#print axioms HPC.Hagopian.isClosed_layerCrossing
#print axioms HPC.Hagopian.mem_E_of_axis
#print axioms HPC.Hagopian.pi_E_eq
#print axioms HPC.Hagopian.layerCrossing_disjoint
#print axioms HPC.Hagopian.crossing_from_layer_translate_aux
#print axioms HPC.Hagopian.crossing_descends_aux
#print axioms HPC.Hagopian.property3_layer_aux
#print axioms HPC.Hagopian.crossing_length_pos_aux

-- ## Hagopian 1976 XIX (batch 174)
-- skeleton `HPC/Hagopian/Hagopian76S.lean`
#print axioms HPC.Hagopian.hagopian76_property3_end_element
#print axioms HPC.Hagopian.hagopian76_property3_components
#print axioms HPC.Hagopian.hagopian76_I_finite
#print axioms HPC.Hagopian.hagopian76_J_xs
#print axioms HPC.Hagopian.hagopian76_property4_base
-- supporting: `H76EndElement.lean`
#print axioms HPC.Hagopian.layerCrossing_congr
#print axioms HPC.Hagopian.exists_end_extension
#print axioms HPC.Hagopian.property3_layer_all
#print axioms HPC.Hagopian.property3_end_element_aux
#print axioms HPC.Hagopian.crossing_length_pos_of_forall
#print axioms HPC.Hagopian.crossing_length_pos_all
-- supporting: `H76IFinite.lean`
#print axioms HPC.Hagopian.IsIrreducibleInterval.unique
#print axioms HPC.Hagopian.isClosed_layerSet_Icc
#print axioms HPC.Hagopian.exists_irreducibleInterval
#print axioms HPC.Hagopian.IsIrreducibleInterval.closure_meets
#print axioms HPC.Hagopian.IsIrreducibleInterval.layerSet_Ioo_subset_closure
#print axioms HPC.Hagopian.mem_component_of_mem_closure_in
#print axioms HPC.Hagopian.IsCrossingComponent.isConnected
#print axioms HPC.Hagopian.IsCrossingComponent.subset
#print axioms HPC.Hagopian.IsCrossingComponent.eq_of_mem_closure
#print axioms HPC.Hagopian.crossingIntervals_disjoint
#print axioms HPC.Hagopian.finite_of_disjoint_Ioo
#print axioms HPC.Hagopian.I_finite_aux
#print axioms HPC.Hagopian.property3_components_aux
-- supporting: `H76JXs.lean`
#print axioms HPC.Hagopian.crossSet_disjoint_E
#print axioms HPC.Hagopian.J_xs_aux
#print axioms HPC.Hagopian.property4_base_aux

-- ## Hagopian 1976 XX (batch 175)
-- skeleton `HPC/Hagopian/Hagopian76T.lean`
#print axioms HPC.Hagopian.translate_through_point_in_F
#print axioms HPC.Hagopian.component_over_middle_crossing
#print axioms HPC.Hagopian.component_over_middle_crossing_of_end
#print axioms HPC.Hagopian.cover_pocket_middle
#print axioms HPC.Hagopian.hagopian76_tail_middle
#print axioms HPC.Hagopian.hagopian76_x2n_eq_one_of_cut
-- supporting: `H76Pocket.lean`
#print axioms HPC.Hagopian.bump_in_extension
#print axioms HPC.Hagopian.component_over_middle_aux
#print axioms HPC.Hagopian.cover_pocket_middle_aux
#print axioms HPC.Hagopian.component_over_middle_crossing_aux
#print axioms HPC.Hagopian.tail_middle_reaches_end_aux
#print axioms HPC.Hagopian.translate_through_middle_aux
-- supporting: `H76X2n.lean`
#print axioms HPC.Hagopian.x2n_eq_one_of_cut

-- ## Hagopian 1976 XXI (batch 176)
-- skeleton `HPC/Hagopian/Hagopian76U.lean`
#print axioms HPC.Hagopian.eps3_positions_middle
#print axioms HPC.Hagopian.eps3_image_middle
#print axioms HPC.Hagopian.sep_by_crossing_cut
#print axioms HPC.Hagopian.hagopian76_x2n_eq_one
#print axioms HPC.Hagopian.hagopian76_property4_top
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond
-- supporting: `H76Eps3.lean`
#print axioms HPC.Hagopian.collar_abscissa_sep
#print axioms HPC.Hagopian.pi_abscissa_close
#print axioms HPC.Hagopian.Property2At.mono
-- supporting: `H76Cut.lean`
#print axioms HPC.Hagopian.sepIn_union_cases
#print axioms HPC.Hagopian.layerSet_subset
#print axioms HPC.Hagopian.layerSet_mono
#print axioms HPC.Hagopian.closure_crossing_subset_interval
#print axioms HPC.Hagopian.iUnion_crossing_subset
#print axioms HPC.Hagopian.tailCutKeepsSep_of_sepByCrossing
#print axioms HPC.Hagopian.isCompact_toPt_layerSet
#print axioms HPC.Hagopian.sepIn_above_gap
-- supporting: `H76Prop4.lean`
#print axioms HPC.Hagopian.T12Data.f_small
#print axioms HPC.Hagopian.not_property4_E
#print axioms HPC.Hagopian.false_of_property4_chain
#print axioms HPC.Hagopian.property4_top_of_sepByCrossing

-- ## Hagopian 1976 XXII (batch 177)
#print axioms HPC.Hagopian.exists_param_sep
#print axioms HPC.Hagopian.strand_fine_translate
#print axioms HPC.Hagopian.strand_lemma
#print axioms HPC.Hagopian.strand_fine_positions
#print axioms HPC.Hagopian.typeA'_inner_strands
#print axioms HPC.Hagopian.exists_T12Data
#print axioms HPC.Hagopian.pi_preimage_frontier_D
-- supporting: `H76Strand.lean`
#print axioms HPC.Hagopian.exists_param_sep_aux
#print axioms HPC.Hagopian.strand_fine_translate_aux
#print axioms HPC.Hagopian.strand_off_ends
#print axioms HPC.Hagopian.strand_closure_subset
#print axioms HPC.Hagopian.strand_crossing
-- supporting: `H76StrandUse.lean`
#print axioms HPC.Hagopian.crossSet_univ_eq
#print axioms HPC.Hagopian.val_preimage_connectedComponentIn
#print axioms HPC.Hagopian.val_preimage_closure_connectedComponentIn
#print axioms HPC.Hagopian.strand_inner_middle
#print axioms HPC.Hagopian.strand_fine_positions_aux
#print axioms HPC.Hagopian.typeA'_strand_aux
#print axioms HPC.Hagopian.typeA'_inner_crossing
#print axioms HPC.Hagopian.strand_essential
-- supporting: `H76T12Exists.lean`
#print axioms HPC.Hagopian.pi_fibre
#print axioms HPC.Hagopian.pi_preimage_continuum
#print axioms HPC.Hagopian.frontier_D_continuum
#print axioms HPC.Hagopian.pi_preimage_frontier_D_aux
#print axioms HPC.Hagopian.exists_T12Data_aux
#print axioms HPC.Hagopian.T15_T17_cond_hyps_inconsistent
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond_fix
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond2

-- ## Hagopian 1976 XXIII (batch 178)
#print axioms HPC.Hagopian.separatesPlane_union_of_inter_disconnected
#print axioms HPC.Hagopian.sepIn_iff_separatesPts_union
#print axioms HPC.Hagopian.crossing_piece_meets_sigma
#print axioms HPC.Hagopian.crossing_piece_sides
#print axioms HPC.Hagopian.crossing_piece_below_iff
#print axioms HPC.Hagopian.crossing_piece_below_trans
#print axioms HPC.Hagopian.crossing_piece_no_pocket
#print axioms HPC.Hagopian.strand_separation
#print axioms HPC.Hagopian.strand_separation_converse
#print axioms HPC.Hagopian.sepByCrossing_of_inner_crossing
#print axioms HPC.Hagopian.T12Data.end_layer_not_subset
#print axioms HPC.Hagopian.strand_misses_F_of_composant
#print axioms HPC.Hagopian.sep_by_crossing
#print axioms HPC.Hagopian.exists_blocks
-- supporting: `H76Unicoh.lean`
#print axioms HPC.Hagopian.separatesPlane_union_of_inter_disconnected_aux
#print axioms HPC.Hagopian.subset_of_preconnected_of_frontier
#print axioms HPC.Hagopian.sepIn_iff_separatesPts_union_aux
-- supporting: `H76Order.lean`
#print axioms HPC.Hagopian.VFrame.below_subset
#print axioms HPC.Hagopian.VFrame.above_subset
#print axioms HPC.Hagopian.VFrame.subset_below
#print axioms HPC.Hagopian.VFrame.subset_above
#print axioms HPC.Hagopian.VFrame.subset_below_of_lev
#print axioms HPC.Hagopian.VFrame.subset_above_of_lev
#print axioms HPC.Hagopian.VFrame.notMem_closure_of_lev
#print axioms HPC.Hagopian.VFrame.mem_below_of_lev
#print axioms HPC.Hagopian.VFrame.mem_above_of_lev
#print axioms HPC.Hagopian.VFrame.seg_subset_O
#print axioms HPC.Hagopian.VFrame.isOpen_below
#print axioms HPC.Hagopian.VFrame.isOpen_above
#print axioms HPC.Hagopian.VFrame.mem_below_of_mem_closure
#print axioms HPC.Hagopian.VFrame.mem_above_of_mem_closure
#print axioms HPC.Hagopian.VFrame.IsPiece.hts_pos
#print axioms HPC.Hagopian.VFrame.IsPiece.lo_mem
#print axioms HPC.Hagopian.VFrame.IsPiece.hi_mem
#print axioms HPC.Hagopian.VFrame.IsPiece.lo_le
#print axioms HPC.Hagopian.VFrame.IsPiece.le_hi
#print axioms HPC.Hagopian.VFrame.IsPiece.mem_of_lev
#print axioms HPC.Hagopian.VFrame.IsPiece.nonempty
#print axioms HPC.Hagopian.VFrame.IsPiece.disjoint_closure
#print axioms HPC.Hagopian.VFrame.IsPiece.subset_diff_closure
#print axioms HPC.Hagopian.VFrame.IsPiece.hts_disjoint
#print axioms HPC.Hagopian.VFrame.IsPiece.exists_lo
#print axioms HPC.Hagopian.VFrame.IsPiece.exists_hi
#print axioms HPC.Hagopian.VFrame.piece_sides
#print axioms HPC.Hagopian.VFrame.above_subset_above
#print axioms HPC.Hagopian.VFrame.below_subset_below
#print axioms HPC.Hagopian.VFrame.clopen_contra
#print axioms HPC.Hagopian.VFrame.not_below_below
#print axioms HPC.Hagopian.VFrame.not_above_above
#print axioms HPC.Hagopian.VFrame.below_iff_above
#print axioms HPC.Hagopian.VFrame.below_trans
#print axioms HPC.Hagopian.VFrame.no_pocket
#print axioms HPC.Hagopian.VFrame.sepIn_of_between
#print axioms HPC.Hagopian.VFrame.exists_sep_point
#print axioms HPC.Hagopian.VFrame.between_of_mem
#print axioms HPC.Hagopian.VFrame.strand_separation
#print axioms HPC.Hagopian.VFrame.sepByCrossing_of_inner_crossing
-- supporting: `H76OrderConcrete.lean`
#print axioms HPC.Hagopian.lowFrame_hyps
#print axioms HPC.Hagopian.isPiece_of_isCrossingPiece
-- supporting: `H76EndLayer.lean`
#print axioms HPC.Hagopian.separatesPlane_of_separatesPts
#print axioms HPC.Hagopian.T12Data.end_layer_not_subset_aux
-- supporting: `H76SepCross.lean`
#print axioms HPC.Hagopian.image_val_connectedComponentIn
#print axioms HPC.Hagopian.toPt_crossSet
#print axioms HPC.Hagopian.sepByCrossing_of_sigma_pieces
-- supporting: `H76Blocks.lean`
#print axioms HPC.Hagopian.blocks_of_finset
#print axioms HPC.Hagopian.blocks_of_finite
#print axioms HPC.Hagopian.exists_blocks_aux
-- supporting: `H76Comp.lean`
#print axioms HPC.Hagopian.strand_misses_of_composant
#print axioms HPC.Hagopian.hagopian76_T12_comp
#print axioms HPC.Hagopian.exists_T12Data_comp
#print axioms HPC.Hagopian.exists_T12Data_strands

-- ## Hagopian 1976 XXIV (batch 179)
#print axioms HPC.Hagopian.crossing_components_finite
#print axioms HPC.Hagopian.p_on_crossing_piece
#print axioms HPC.Hagopian.sep_by_crossing_uncond
#print axioms HPC.Hagopian.hagopian76_x2n_eq_one_final
#print axioms HPC.Hagopian.hagopian76_property4_top_final
#print axioms HPC.Hagopian.exists_blocks_uncond
#print axioms HPC.Hagopian.crossingIntervals_nondegenerate
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond3
#print axioms HPC.Hagopian.exists_thm1Setup
#print axioms HPC.Hagopian.hagopian76_theorem1_of_step
-- supporting: `H76Nondeg.lean`
#print axioms HPC.Hagopian.layerSet_Icc_self
#print axioms HPC.Hagopian.crossingIntervals_nondegenerate_of
#print axioms HPC.Hagopian.IsCrossingComponent.eq_of_irreducible
#print axioms HPC.Hagopian.crossingComponents_finite_of
-- supporting: `H76Uniform.lean`, `H76Uniform2.lean`, `H76Uniform3.lean` (§4, uniform heights)
#print axioms HPC.Hagopian.property3_reduced_unif
#print axioms HPC.Hagopian.property3_translate_unif
#print axioms HPC.Hagopian.crossing_from_layer_translate_unif
#print axioms HPC.Hagopian.crossing_descends_unif
#print axioms HPC.Hagopian.property3_layer_unif
#print axioms HPC.Hagopian.property3_layer_all_unif
#print axioms HPC.Hagopian.crossing_length_pos_all_unif
#print axioms HPC.Hagopian.hagopian76_I_finite_unif
#print axioms HPC.Hagopian.hagopian76_property3_components_unif
#print axioms HPC.Hagopian.hagopian76_x2n_eq_one_unif
#print axioms HPC.Hagopian.hagopian76_property3_unif
#print axioms HPC.Hagopian.component_over_middle_unif
#print axioms HPC.Hagopian.cover_pocket_middle_unif
-- supporting: `H76PieceB.lean`
#print axioms HPC.Hagopian.isClosed_M_of_compact
#print axioms HPC.Hagopian.closure_toPt
#print axioms HPC.Hagopian.side_point_open
#print axioms HPC.Hagopian.isCrossingPiece_of_crossingComponent
#print axioms HPC.Hagopian.closure_ne_univ_of_crossSet
-- ## Hagopian 1976 XXV (batch 180)
-- (`exists_thm1Setup` and `hagopian76_theorem1_of_step`, listed under batch 179, are restated in
-- place for the repaired set-up.)
#print axioms HPC.Hagopian.property4_lower_false_of_K_eq
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond4
#print axioms HPC.Hagopian.Thm1Setup.K_meets_crossing
#print axioms HPC.Hagopian.tip_meets_end_layer
#print axioms HPC.Hagopian.tip_meets_end_layer_mirror
#print axioms HPC.Hagopian.tip_end_layer_continuum
#print axioms HPC.Hagopian.tip_triod
#print axioms HPC.Hagopian.tip_triod_mirror
#print axioms HPC.Hagopian.tip_triod_on_tip_layer
#print axioms HPC.Hagopian.degenerate_chunk_iii
-- supporting: `H76Cond4.lean`
#print axioms HPC.Hagopian.p_on_crossing_piece_comp
#print axioms HPC.Hagopian.sep_by_crossing_uncond_comp
-- supporting: `H76Thm1Setup.lean`
#print axioms HPC.Hagopian.Thm1Setup.h_small_θ
#print axioms HPC.Hagopian.Thm1Setup.h₁_small_θ
#print axioms HPC.Hagopian.isCompact_I₂_aux
-- supporting: `H76Tip.lean`
#print axioms HPC.Hagopian.tip_param_low
#print axioms HPC.Hagopian.tip_param_high
#print axioms HPC.Hagopian.isContinuum_of_minimalAdmissible
#print axioms HPC.Hagopian.tip_Z_continuum
-- ## Hagopian 1976 XXVI (batch 181)
-- (`exists_thm1Setup`, listed under batch 179, is restated in place with the fields `hε₃O`, `hε₃S`.)
#print axioms HPC.Hagopian.two_div_le_of_forty
#print axioms HPC.Hagopian.closure_midSet_sub
#print axioms HPC.Hagopian.isCompact_closure_midSet
#print axioms HPC.Hagopian.mid_not_side
#print axioms HPC.Hagopian.exists_eps_mid_sides
#print axioms HPC.Hagopian.exists_eps_mid_O
#print axioms HPC.Hagopian.Thm1Setup.r₂_le
#print axioms HPC.Hagopian.Thm1Setup.s₂_le
#print axioms HPC.Hagopian.Thm1Setup.isCrossingComponent_of_piece
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.block_eq
#print axioms HPC.Hagopian.Thm1Setup.inner_component_in_block
#print axioms HPC.Hagopian.Thm1Setup.inner_point_in_block
#print axioms HPC.Hagopian.block_components_cross
#print axioms HPC.Hagopian.VFrame.notMem_closure_above_of_below
#print axioms HPC.Hagopian.VFrame.exists_mem_closure_of_preconnected
#print axioms HPC.Hagopian.VFrame.exists_mem_closure_of_segment
#print axioms HPC.Hagopian.VFrame.dist_le_of_mem_segment
#print axioms HPC.Hagopian.VFrame.infDist_le_of_segment
#print axioms HPC.Hagopian.VFrame.notMem_closure_below_of_above
#print axioms HPC.Hagopian.VFrame.exists_mem_closure_of_preconnected_mirror
#print axioms HPC.Hagopian.VFrame.infDist_le_of_segment_mirror
#print axioms HPC.Hagopian.VFrame.sepIn_of_below_below
#print axioms HPC.Hagopian.VFrame.property4_step_unless
#print axioms HPC.Hagopian.VFrame.joined_of_below
#print axioms HPC.Hagopian.VFrame.joined_of_above
#print axioms HPC.Hagopian.VFrame.opposite_of_sepIn
#print axioms HPC.Hagopian.above_closure_misses_bottom
#print axioms HPC.Hagopian.Thm1Setup.c₁_le_one
#print axioms HPC.Hagopian.Thm1Setup.c₁_pos
#print axioms HPC.Hagopian.Thm1Setup.disjoint_O_E
#print axioms HPC.Hagopian.Thm1Setup.D'_sub_rect
#print axioms HPC.Hagopian.Thm1Setup.lowFrame_hyps
#print axioms HPC.Hagopian.Thm1Setup.injOn_O
#print axioms HPC.Hagopian.Thm1Setup.V_O
#print axioms HPC.Hagopian.Thm1Setup.exists_low
#print axioms HPC.Hagopian.Thm1Setup.K_subset_mid
#print axioms HPC.Hagopian.Thm1Setup.h₁_Rset_notMem_G
#print axioms HPC.Hagopian.f_mem_O_of_mem_K
#print axioms HPC.Hagopian.f_notMem_G_of_Rset
#print axioms HPC.Hagopian.cross_strand_near
#print axioms HPC.Hagopian.cross_strand_near_mirror
#print axioms HPC.Hagopian.tip_meets_end_layer_mirror_rel
#print axioms HPC.Hagopian.tip_triod_mirror_rel
#print axioms HPC.Hagopian.chunk_edge_case_mirror
#print axioms HPC.Hagopian.SepIn.symm
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.mem_O
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.mem_comp
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.rset
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.notMem_G
#print axioms HPC.Hagopian.Thm1Setup.isClosed_toPt_layerSet
#print axioms HPC.Hagopian.property4_of_strand_sep
#print axioms HPC.Hagopian.Thm1Setup.isPiece_of_crossing
#print axioms HPC.Hagopian.Thm1Setup.comp_eq_or_disjoint
#print axioms HPC.Hagopian.property4_strand
#print axioms HPC.Hagopian.property4_step_unless_setup
#print axioms HPC.Hagopian.case1_ending
#print axioms HPC.Hagopian.case1_or_case2
#print axioms HPC.Hagopian.case1
#print axioms HPC.Hagopian.case2_ending
#print axioms HPC.Hagopian.case2
#print axioms HPC.Hagopian.hagopian76_property4_step_cond
#print axioms HPC.Hagopian.hagopian76_theorem1_of_cases

-- ## Hagopian 1976 XXVII (batch 182)
#print axioms HPC.Hagopian.layerSet_Icc_zero_inj
#print axioms HPC.Hagopian.Thm1Setup.d_surjective
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.x2_lt_one
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.G_ne_E
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.layer_x2_eq
#print axioms HPC.Hagopian.Thm1Setup.not_layerMeetsSide_of_layer_eq_one
#print axioms HPC.Hagopian.blockLayersMeetSides_false
#print axioms HPC.Hagopian.Thm1Setup.segment_misses_closure_above
#print axioms HPC.Hagopian.cross_strand_near_above
#print axioms HPC.Hagopian.closure_G_diff_E
#print axioms HPC.Hagopian.Thm1Setup.dn_up_disjoint
#print axioms HPC.Hagopian.cross_strand_near_o
#print axioms HPC.Hagopian.property4_of_strand_sep_o
#print axioms HPC.Hagopian.Thm1Setup.up_subset_up
#print axioms HPC.Hagopian.Thm1Setup.piece_sides_o
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.disjoint_strand
#print axioms HPC.Hagopian.Thm1Setup.GoodPoint.mem_mid
#print axioms HPC.Hagopian.Thm1Setup.dist_f_lt
#print axioms HPC.Hagopian.property4_step_unless_o
#print axioms HPC.Hagopian.case1_ending_oriented
#print axioms HPC.Hagopian.Case1WitnessO.property4
#print axioms HPC.Hagopian.case2_ending_oriented
#print axioms HPC.Hagopian.last_step_ending
#print axioms HPC.Hagopian.not_property4_x3x4
#print axioms HPC.Hagopian.hagopian76_property4_step_cond2
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.layer_x2_meets_right
#print axioms HPC.Hagopian.Thm1Setup.kminus_isContinuum
#print axioms HPC.Hagopian.Thm1Setup.kplus_isContinuum
#print axioms HPC.Hagopian.Thm1Setup.half_bump
#print axioms HPC.Hagopian.Thm1Setup.mem_toPt_E_of_pi_eq
#print axioms HPC.Hagopian.Thm1Setup.half_bump_side
#print axioms HPC.Hagopian.Thm1Setup.continuum_misses_G_of_h_Rset
#print axioms HPC.Hagopian.Thm1Setup.closure_comp_continuum
#print axioms HPC.Hagopian.Thm1Setup.comp_disjoint_G
#print axioms HPC.Hagopian.Thm1Setup.comp_disjoint_G_of_ess
#print axioms HPC.Hagopian.Thm1Setup.comp_f_disjoint_G
#print axioms HPC.Hagopian.minimalAdmissible_ne_univ
#print axioms HPC.Hagopian.Thm1Setup.admissible_misses_G_of_h_Rset
#print axioms HPC.Hagopian.Thm1Setup.extension_misses_G
#print axioms HPC.Hagopian.hagopian76_T15_T17_cond5
#print axioms HPC.Hagopian.exists_thm1Setup_tight
#print axioms HPC.Hagopian.hagopian76_theorem1_of_step_tight
#print axioms HPC.Hagopian.Thm1Setup.half_mem_sat
#print axioms HPC.Hagopian.stepStrands_of_frame
#print axioms HPC.Hagopian.hagopian76_theorem1_of_cases2

-- ## Hagopian 1976 XXVIII (batch 183)
#print axioms HPC.Hagopian.restrictParam_mem
#print axioms HPC.Hagopian.restrictParam_zero
#print axioms HPC.Hagopian.restrictParam_one
#print axioms HPC.Hagopian.minimalAdmissible_restrict_of_lsc
#print axioms HPC.Hagopian.minimalAdmissible_restrict
#print axioms HPC.Hagopian.Thm1Setup.cap_point_o
#print axioms HPC.Hagopian.Thm1Setup.near_strand_cross_o
#print axioms HPC.Hagopian.Thm1Setup.piece_nonempty
#print axioms HPC.Hagopian.e24_pair_between
#print axioms HPC.Hagopian.e24_pair_below
#print axioms HPC.Hagopian.Thm1Setup.exists_Rset_over
#print axioms HPC.Hagopian.exists_restrictParam_eq
#print axioms HPC.Hagopian.property2_violation
#print axioms HPC.Hagopian.E24Claims.false
#print axioms HPC.Hagopian.e24_between_false
#print axioms HPC.Hagopian.e24_below_far
#print axioms HPC.Hagopian.E24Data.far
#print axioms HPC.Hagopian.Case1ClaimsE24.claims'
#print axioms HPC.Hagopian.Case2ClaimsE24.claims'
#print axioms HPC.Hagopian.hagopian76_theorem1_of_cases3

-- ## Hagopian 1984 I (batch 184)
#print axioms HPC.Hagopian.exists_plane_quotient_of_monotone
#print axioms HPC.Hagopian.indecomposable_of_monotone_image
#print axioms HPC.Hagopian.hagopian76_theorem1_of_jones
#print axioms HPC.Hagopian.hagopian75_theorem1_of_noArc
#print axioms HPC.Hagopian.hagopian84_lemma1
#print axioms HPC.Hagopian.hagopian84_lemma6
#print axioms HPC.Hagopian.hagopian84_lemma11
#print axioms HPC.Hagopian.isPreconnected_preimage_of_monotone
#print axioms HPC.Hagopian.isContinuum_preimage_of_monotone
#print axioms HPC.Hagopian.isDecomposableSpace_of_monotone_image
#print axioms HPC.Hagopian.fibreKey_of_mem
#print axioms HPC.Hagopian.fibreKey_of_notMem
#print axioms HPC.Hagopian.elt_fibreSetoid_of_mem
#print axioms HPC.Hagopian.elt_fibreSetoid_of_notMem
#print axioms HPC.Hagopian.fibre_usc
#print axioms HPC.Hagopian.fibreSetoid_mooreDecomp
#print axioms HPC.Hagopian.exists_plane_quotient_of_monotone_aux

-- ## Hagopian 1976 XXX (batch 185)
#print axioms HPC.Hagopian.mem_layerSet_iff'
#print axioms HPC.Hagopian.mem_layer_iff'
#print axioms HPC.Hagopian.layer_subset'
#print axioms HPC.Hagopian.layerSet_subset'
#print axioms HPC.Hagopian.layerSet_Icc_inter_subset
#print axioms HPC.Hagopian.layerSet_Icc_zero_one
#print axioms HPC.Hagopian.eq_of_meets_end_layers
#print axioms HPC.Hagopian.layerGlueFun_mem
#print axioms HPC.Hagopian.layerGlueFun_of_memA
#print axioms HPC.Hagopian.layerGlueFun_of_memB
#print axioms HPC.Hagopian.layerGlueA_injective
#print axioms HPC.Hagopian.layerGlueB_injective
#print axioms HPC.Hagopian.layer_glue_A
#print axioms HPC.Hagopian.layer_glue_B
#print axioms HPC.Hagopian.layerGlue_cases
#print axioms HPC.Hagopian.layerGlueA_one
#print axioms HPC.Hagopian.layerGlueB_one
#print axioms HPC.Hagopian.interior_layer_of_subset_empty
#print axioms HPC.Hagopian.glue_minimalAdmissible
#print axioms HPC.Hagopian.ext_inter_ext_subset
#print axioms HPC.Hagopian.disjoint_layerSet_layer
#print axioms HPC.Hagopian.hagopian84_two_sided_aux
#print axioms HPC.Hagopian.no_arm_at_interior_layer
#print axioms HPC.Hagopian.two_layers_or_subset
#print axioms HPC.Hagopian.layer_common_of_essential
#print axioms HPC.Hagopian.hagopian84_lemma7_aux
#print axioms HPC.Hagopian.layers_agree_aux
#print axioms HPC.Hagopian.translate_run_left_aux
#print axioms HPC.Hagopian.translate_run_right_aux
#print axioms HPC.Hagopian.Thm1Setup.fine_over_D
#print axioms HPC.Hagopian.Thm1Setup.two_div_n_le
#print axioms HPC.Hagopian.Thm1Setup.kminus_not_subset_O
#print axioms HPC.Hagopian.Thm1Setup.kplus_not_subset_O
#print axioms HPC.Hagopian.Thm1Setup.closure_crossSet_mem_E
#print axioms HPC.Hagopian.Thm1Setup.F_ne_F10
#print axioms HPC.Hagopian.Thm1Setup.isCrossingPiece_of_crossingComponent_G
#print axioms HPC.Hagopian.Thm1Setup.crossing_of_halves
#print axioms HPC.Hagopian.Thm1Setup.innerComponentsCross_aux
#print axioms HPC.Hagopian.layer_nhds_subset_open
#print axioms HPC.Hagopian.left_layer_not_subset
#print axioms HPC.Hagopian.right_layer_not_subset
#print axioms HPC.Hagopian.Thm1Setup.isOpen_O
#print axioms HPC.Hagopian.Thm1Setup.layerMeetsSide_of_end
#print axioms HPC.Hagopian.Thm1Setup.IsBlocks.layer_disjoint_E
#print axioms HPC.Hagopian.Thm1Setup.IsTightBlocks.left_end_crossing
#print axioms HPC.Hagopian.Thm1Setup.IsTightBlocks.right_end_crossing
#print axioms HPC.Hagopian.Thm1Setup.leftEndLayerMeetsSide
#print axioms HPC.Hagopian.Thm1Setup.layer_x3_meets_side
#print axioms HPC.Hagopian.Thm1Setup.blockLayersMeetSides3_aux
#print axioms HPC.Hagopian.wset84_eq_wset
#print axioms HPC.Hagopian.hagopian84_two_sided
#print axioms HPC.Hagopian.hagopian84_lemma7
#print axioms HPC.Hagopian.hagopian84Lemma7_holds
#print axioms HPC.Hagopian.layers_agree
#print axioms HPC.Hagopian.translate_run
#print axioms HPC.Hagopian.translate_run_right
#print axioms HPC.Hagopian.noncrossing_half_in_O_steps45
#print axioms HPC.Hagopian.half_in_O_false
#print axioms HPC.Hagopian.innerComponentsCross_hagopian
#print axioms HPC.Hagopian.blockLayersMeetSides3
#print axioms HPC.Hagopian.layer_x3_meets_side
#print axioms HPC.Hagopian.hagopian76_theorem1_of_cases4

-- ## Hagopian 1984 III (batch 186)
#print axioms HPC.Hagopian.FoldAux.left_end
#print axioms HPC.Hagopian.FoldAux.right_end
#print axioms HPC.Hagopian.FoldAux.sweep_step
#print axioms HPC.Hagopian.FoldAux.exists_fold_nat
#print axioms HPC.Hagopian.exists_fold_aux
#print axioms HPC.Hagopian.layer_isPreconnected'
#print axioms HPC.Hagopian.layer_nonempty'
#print axioms HPC.Hagopian.layer_subset_set
#print axioms HPC.Hagopian.mem_layer_self84
#print axioms HPC.Hagopian.exists_layer_eq_of_minimal
#print axioms HPC.Hagopian.layer_eq_of_common_point
#print axioms HPC.Hagopian.subset_of_preconnected_meets_open
#print axioms HPC.Hagopian.layer_subset_link
#print axioms HPC.Hagopian.layer_disjoint_closure_of_mem
#print axioms HPC.Hagopian.chain5_disjoint
#print axioms HPC.Hagopian.delta_subset_component
#print axioms HPC.Hagopian.delta_subset_diff
#print axioms HPC.Hagopian.delta5_partition_aux
#print axioms HPC.Hagopian.closure_delta_subset_mid
#print axioms HPC.Hagopian.delta5_dist_pos_aux
#print axioms HPC.Hagopian.exists_interval_in_P2
#print axioms HPC.Hagopian.exists_interval_in_delta_aux
#print axioms HPC.Hagopian.endlayers_not_mid
#print axioms HPC.Hagopian.delta_regular_rep
#print axioms HPC.Hagopian.delta_translate_eq
#print axioms HPC.Hagopian.hagopian84_lemma14_aux
#print axioms HPC.Hagopian.exists_far_links
#print axioms HPC.Hagopian.hagopian84_lemma15_aux
#print axioms HPC.Hagopian.chain_consecutive_meet
#print axioms HPC.Hagopian.mem_frontier_diff_iff
#print axioms HPC.Hagopian.refineChain_subset
#print axioms HPC.Hagopian.refineChain_mid
#print axioms HPC.Hagopian.mem_refineChain_of
#print axioms HPC.Hagopian.runsStraight_refine
#print axioms HPC.Hagopian.hagopian84_lemma12_aux
#print axioms HPC.Hagopian.dist_symm_lt_of_small
#print axioms HPC.Hagopian.exists_comp_small_homeo
#print axioms HPC.Hagopian.hagopian84Decomp_of_package
#print axioms HPC.Hagopian.exists_fold
#print axioms HPC.Hagopian.hagopian84_lemma12
#print axioms HPC.Hagopian.delta5_partition
#print axioms HPC.Hagopian.delta5_dist_pos
#print axioms HPC.Hagopian.hagopian84_lemma14
#print axioms HPC.Hagopian.hagopian84_lemma15
#print axioms HPC.Hagopian.exists_interval_in_delta

-- ## Hagopian 1984 IV (batch 187)
#print axioms HPC.Hagopian.isOpen_params_meeting
#print axioms HPC.Hagopian.isOpen_params_disjoint
#print axioms HPC.Hagopian.isClosed_params_meeting
#print axioms HPC.Hagopian.strand_meets_P2_P0
#print axioms HPC.Hagopian.strand_layer_subset_mid
#print axioms HPC.Hagopian.strand_dichotomy
#print axioms HPC.Hagopian.strand_layer_mem_delta_aux
#print axioms HPC.Hagopian.closure_P2_subset
#print axioms HPC.Hagopian.not_strand_subset_extension_layer_aux
#print axioms HPC.Hagopian.strand_layer_of_extension_aux
#print axioms HPC.Hagopian.strand_end_layer_not_mid
#print axioms HPC.Hagopian.hagopian84_lemma16_aux
#print axioms HPC.Hagopian.layer_subset_closure_link
#print axioms HPC.Hagopian.omega_not_delta_side_aux
#print axioms HPC.Hagopian.meets_P2_of_connects
#print axioms HPC.Hagopian.bridge_setup
#print axioms HPC.Hagopian.exists_ext_meeting_P2
#print axioms HPC.Hagopian.exists_bridge84_aux
#print axioms HPC.Hagopian.mem_delta_of_bridge_chain_aux
#print axioms HPC.Hagopian.wsetOf_subset_thickening
#print axioms HPC.Hagopian.subset_wsetOf
#print axioms HPC.Hagopian.image_subset_wsetOf
#print axioms HPC.Hagopian.isOpen_wsetOf
#print axioms HPC.Hagopian.closure_wsetOf_subset
#print axioms HPC.Hagopian.image_subset_thickening
#print axioms HPC.Hagopian.chainLinks84_eq
#print axioms HPC.Hagopian.isCompact_seg84
#print axioms HPC.Hagopian.seg84_disjoint
#print axioms HPC.Hagopian.seg84_meet
#print axioms HPC.Hagopian.seg84_nonempty
#print axioms HPC.Hagopian.layer_zero_subset_seg84
#print axioms HPC.Hagopian.layer_one_subset_seg84
#print axioms HPC.Hagopian.mem_some_seg84
#print axioms HPC.Hagopian.xf84_strictMono
#print axioms HPC.Hagopian.xf84_mem
#print axioms HPC.Hagopian.xf84_zero
#print axioms HPC.Hagopian.xf84_fifteen
#print axioms HPC.Hagopian.xf84_three
#print axioms HPC.Hagopian.xf84_twelve
#print axioms HPC.Hagopian.exists_sep_radius
#print axioms HPC.Hagopian.exists_x84
#print axioms HPC.Hagopian.chainLinks84_chain_aux
#print axioms HPC.Hagopian.isOpen_sUnion_delta5
#print axioms HPC.Hagopian.closure_sUnion_delta5_subset
#print axioms HPC.Hagopian.exists_finite_cover84_aux
#print axioms HPC.Hagopian.xle84
#print axioms HPC.Hagopian.xlt84
#print axioms HPC.Hagopian.exists_gap84
#print axioms HPC.Hagopian.close84
#print axioms HPC.Hagopian.params_inner84
#print axioms HPC.Hagopian.gapBound84_near
#print axioms HPC.Hagopian.image_layer_subset_link84
#print axioms HPC.Hagopian.link_dichotomy84
#print axioms HPC.Hagopian.layer_frontier84
#print axioms HPC.Hagopian.mem_seg84_iff
#print axioms HPC.Hagopian.mem_link_le84
#print axioms HPC.Hagopian.mem_link_ge84
#print axioms HPC.Hagopian.no_fold84
#print axioms HPC.Hagopian.layer_convex84
#print axioms HPC.Hagopian.translate_runsStraight84
#print axioms HPC.Hagopian.mem_layerSet_iff84
#print axioms HPC.Hagopian.restrictParam_le84
#print axioms HPC.Hagopian.restrictParam_lt84
#print axioms HPC.Hagopian.params_adjacent_meet84
#print axioms HPC.Hagopian.exists_right_Icc84
#print axioms HPC.Hagopian.exists_left_Icc84
#print axioms HPC.Hagopian.layer_subset_layerSet84
#print axioms HPC.Hagopian.strand_of_runsStraight84
#print axioms HPC.Hagopian.exists_chain84_core
#print axioms HPC.Hagopian.chainLinks84_runsStraight_aux
#print axioms HPC.Hagopian.chainLinks84_regular_aux
#print axioms HPC.Hagopian.hagopian84_lemma13_aux
#print axioms HPC.Hagopian.chainLinks84_chain
#print axioms HPC.Hagopian.chainLinks84_runsStraight
#print axioms HPC.Hagopian.chainLinks84_regular
#print axioms HPC.Hagopian.hagopian84_lemma13
#print axioms HPC.Hagopian.strand_layer_mem_delta
#print axioms HPC.Hagopian.not_strand_subset_extension_layer
#print axioms HPC.Hagopian.strand_layer_of_extension
#print axioms HPC.Hagopian.hagopian84_lemma16
#print axioms HPC.Hagopian.omega_not_delta_side
#print axioms HPC.Hagopian.exists_bridge84
#print axioms HPC.Hagopian.mem_delta_of_bridge_chain
#print axioms HPC.Hagopian.exists_finite_cover84
#print axioms HPC.Hagopian.exists_chainZ84
#print axioms HPC.Hagopian.hagopian84_cover

-- ## Hagopian 1984 V (batch 188)
#print axioms HPC.Hagopian.midUnion_subset_iUnion84
#print axioms HPC.Hagopian.mem_midUnion_of_diff84
#print axioms HPC.Hagopian.endlayers_subset_closure84
#print axioms HPC.Hagopian.exists_piece_between84
#print axioms HPC.Hagopian.omega_layer_of_mem_mid
#print axioms HPC.Hagopian.omega_mem_delta_of_mem_mid
#print axioms HPC.Hagopian.exists_coverData84
#print axioms HPC.Hagopian.CoverData84.exists_mem
#print axioms HPC.Hagopian.CoverData84.exists_chain_of_mem
#print axioms HPC.Hagopian.CoverData84.eq_of_meet_delta
#print axioms HPC.Hagopian.CoverData84.members_disjoint
#print axioms HPC.Hagopian.CoverData84.setoid_iff
#print axioms HPC.Hagopian.CoverData84.cls_eq
#print axioms HPC.Hagopian.CoverData84.omega_subset_members
#print axioms HPC.Hagopian.CoverData84.omega_mem_members
#print axioms HPC.Hagopian.delta_translate_small84
#print axioms HPC.Hagopian.exists_pos_forall_finset84
#print axioms HPC.Hagopian.CoverData84.invariant
#print axioms HPC.Hagopian.CoverData84.isJonesDecomp
#print axioms HPC.Hagopian.sUnion_cover84_eq_univ
#print axioms HPC.Hagopian.hagopian84_decomp
#print axioms HPC.Hagopian.hagopian76_theorem1_jones

-- ## Jones 1975 I (batch 189)
#print axioms HPC.Hagopian.jonesSetting_of_plane
#print axioms HPC.Hagopian.Icc_zero_one_I
#print axioms HPC.Hagopian.image_Icc_zero_one
#print axioms HPC.Hagopian.unitInterval_eq_Icc_of_closed
#print axioms HPC.Hagopian.image_Icc_inter_image_Icc
#print axioms HPC.Hagopian.tarc_range
#print axioms HPC.Moore.Gen.TArc.image_homeomorph
#print axioms HPC.Hagopian.endpoint_of_preconnected
#print axioms HPC.Hagopian.sub_arc_param
#print axioms HPC.Hagopian.symm_image_Icc
#print axioms HPC.Hagopian.range_comp_symm
#print axioms HPC.Hagopian.tarc_isContinuum
#print axioms HPC.Hagopian.JonesSetting.inter_isPreconnected
#print axioms HPC.Hagopian.JonesSetting.no_three_arms
#print axioms HPC.Hagopian.inter_param
#print axioms HPC.Hagopian.JonesSetting.nested
#print axioms HPC.Hagopian.glue_case
#print axioms HPC.Hagopian.JonesSetting.union_arc_aux
#print axioms HPC.Hagopian.JonesSetting.union_arc
#print axioms HPC.Hagopian.JonesSetting.exists_arc_through
#print axioms HPC.Hagopian.mem_arcComp_self
#print axioms HPC.Hagopian.subset_arcComp
#print axioms HPC.Hagopian.mem_arcComp_comm
#print axioms HPC.Hagopian.mem_arcComp_trans
#print axioms HPC.Hagopian.arcComp_eq_of_mem
#print axioms HPC.Hagopian.image_arcComp_subset
#print axioms HPC.Hagopian.image_arcComp
#print axioms HPC.Hagopian.JonesSetting.rayArcs_total
#print axioms HPC.Hagopian.JonesSetting.extend
#print axioms HPC.Hagopian.JonesSetting.exists_ray_seq
#print axioms HPC.Hagopian.piece_of_sub
#print axioms HPC.Hagopian.RayChain.eq_zero_of_mem
#print axioms HPC.Hagopian.RayChain.param_eq_one
#print axioms HPC.Hagopian.JonesSetting.exists_rayChain
#print axioms HPC.Hagopian.JonesSetting.ray_inter
#print axioms HPC.Hagopian.JonesSetting.arcComp_eq_rays
#print axioms HPC.Hagopian.rayGlue_eqOn
#print axioms HPC.Hagopian.continuous_rayGlue
#print axioms HPC.Hagopian.rayGlue_injective
#print axioms HPC.Hagopian.range_rayGlue
#print axioms HPC.Hagopian.rayGlue_zero
#print axioms HPC.Hagopian.JonesSetting.exists_line
#print axioms HPC.Hagopian.JonesSetting.line_arc
#print axioms HPC.Hagopian.JonesSetting.line_arc_uIcc
#print axioms HPC.Hagopian.JonesSetting.arc_unique
#print axioms HPC.Hagopian.JonesSetting.arc_in_line
#print axioms HPC.Hagopian.IsLine.range_eq
#print axioms HPC.Hagopian.IsLine.comp_homeo
#print axioms HPC.Hagopian.IsLine.shift
#print axioms HPC.Hagopian.IsLine.neg
#print axioms HPC.Hagopian.JonesSetting.homeo_on_line_gen
#print axioms HPC.Hagopian.JonesSetting.homeo_on_line
#print axioms HPC.Hagopian.JonesSetting.no_reversal_arc
#print axioms HPC.Hagopian.JonesSetting.local_no_reversal
#print axioms HPC.Hagopian.JonesSetting.exists_no_reversal
#print axioms HPC.Hagopian.JonesSetting.orientation
#print axioms HPC.Hagopian.uniform_near_compact
#print axioms HPC.Hagopian.JonesSetting.no_backtrack
#print axioms HPC.Hagopian.no_backtrack_in_collar
#print axioms HPC.Hagopian.mem_omegaLim_iff
#print axioms HPC.Hagopian.JonesSetting.omegaLim_saturated
#print axioms HPC.Hagopian.JonesSetting.zero_mem_omegaLim
#print axioms HPC.Hagopian.omegaLim_shift
#print axioms HPC.Hagopian.JonesSetting.line_recurrent
#print axioms HPC.Hagopian.JonesSetting.jones75_d

-- ## Jones 1975 II (batch 190)
#print axioms HPC.Hagopian.IsCollar.injOn
#print axioms HPC.Hagopian.IsCollar.contOn
#print axioms HPC.Hagopian.collarCoord_mem
#print axioms HPC.Hagopian.collarCoord_apply
#print axioms HPC.Hagopian.collarCoord_eq
#print axioms HPC.Hagopian.continuousOn_collarCoord
#print axioms HPC.Hagopian.IsCollar.ne_of_fst_ne
#print axioms HPC.Hagopian.IsCollar.base
#print axioms HPC.Hagopian.tarc_of_injOn
#print axioms HPC.Hagopian.box_sub_cRect
#print axioms HPC.Hagopian.IsPass.mem_box
#print axioms HPC.Hagopian.IsPass.mem_rect
#print axioms HPC.Hagopian.lc_eq
#print axioms HPC.Hagopian.continuousOn_lc
#print axioms HPC.Hagopian.IsPass.lc_box
#print axioms HPC.Hagopian.IsPass.lc_left
#print axioms HPC.Hagopian.IsPass.lc_right
#print axioms HPC.Hagopian.IsPass.lc_int
#print axioms HPC.Hagopian.IsPass.continuousOn_lc
#print axioms HPC.Hagopian.IsPass.eq_of_le
#print axioms HPC.Hagopian.IsPass.disjoint
#print axioms HPC.Hagopian.IsPass.eq_of_mem
#print axioms HPC.Hagopian.IsPass.lt_of_mem
#print axioms HPC.Hagopian.isPass_base
#print axioms HPC.Hagopian.IsPass.eq_base_of
#print axioms HPC.Hagopian.IsPass.above_or_below
#print axioms HPC.Hagopian.PassAbove.not_below
#print axioms HPC.Hagopian.IsPass.exists_length
#print axioms HPC.Hagopian.IsPass.finite
#print axioms HPC.Hagopian.exists_first_pass
#print axioms HPC.Hagopian.flipC_flipC
#print axioms HPC.Hagopian.flipC_image
#print axioms HPC.Hagopian.symm_prod
#print axioms HPC.Hagopian.IsPass.flip
#print axioms HPC.Hagopian.PassThin.flip
#print axioms HPC.Hagopian.PassMon.flip
#print axioms HPC.Hagopian.PassBelow.flip
#print axioms HPC.Hagopian.PassAbove.flip
#print axioms HPC.Hagopian.PassAbove.of_flip
#print axioms HPC.Hagopian.FBProp.flip
#print axioms HPC.Hagopian.shadow_pass
#print axioms HPC.Hagopian.IsPass.mono
#print axioms HPC.Hagopian.IsPass.thin
#print axioms HPC.Hagopian.PassThin.mono
#print axioms HPC.Hagopian.flow_box
#print axioms HPC.Hagopian.FBProp.passMon
#print axioms HPC.Hagopian.scale_two
#print axioms HPC.Hagopian.exists_late_thin_pass
#print axioms HPC.Hagopian.tarc_lowest
#print axioms HPC.Hagopian.IsPass.lc_left_mem_closure
#print axioms HPC.Hagopian.IsPass.lc_injOn
#print axioms HPC.Hagopian.thinPass_arc
#print axioms HPC.Hagopian.region_pass
#print axioms HPC.Hagopian.region_thin_above
#print axioms HPC.Hagopian.region_cross
#print axioms HPC.Hagopian.region_lemmaA
#print axioms HPC.Hagopian.two_sides
#print axioms HPC.Hagopian.trap_jordan
#print axioms HPC.Hagopian.trap_pass
#print axioms HPC.Hagopian.IsPass.of_flip
#print axioms HPC.Hagopian.PassThin.of_flip
#print axioms HPC.Hagopian.exists_ball_box
#print axioms HPC.Hagopian.jones75_final_aux
#print axioms HPC.Hagopian.jones75_contra
#print axioms HPC.Hagopian.jones75_noArc
#print axioms HPC.Hagopian.hagopian76_theorem1
#print axioms HPC.Hagopian.bing60_plane_uncond
#print axioms HPC.Hagopian.hagopian76_theorem2_uncond
#print axioms HPC.Hagopian.hagopian75_corollary_uncond
#print axioms HPC.Hagopian.hagopian75_theorem2_uncond
#print axioms HPC.Hagopian.hagopian75_theorem1_of_noArc_uncond

-- ## Theorem C I (batch 191)
-- §2 span (HPC/Span/Defs.lean)
#print axioms HPC.Span.exists_pos_le_dist
#print axioms HPC.Span.otSemiSpanPos_iff
#print axioms HPC.Span.otSpanPos_iff
#print axioms HPC.Span.SurjSpanPos.surjSemiSpanPos
#print axioms HPC.Span.SurjSpanPos.image
#print axioms HPC.Span.SurjSemiSpanPos.image
#print axioms HPC.Span.isContinuum_swap
#print axioms HPC.Span.offDiag_swap
#print axioms HPC.Span.fst_image_swap
#print axioms HPC.Span.snd_image_swap
#print axioms HPC.Span.semiSpanZero_iff_hoSpanZero
#print axioms HPC.Span.hoSpanZero_iff_maps
-- §3 Cook 1967 Theorem 4, §4 Brouwer reduction and Davis 1.1 (HPC/Span/Cook.lean)
#print axioms HPC.Span.nested_of_hi
#print axioms HPC.Span.hi_mono
#print axioms HPC.Span.cook67_theorem4
#print axioms HPC.Span.directed_of_isChain_supset
#print axioms HPC.Span.isPreconnected_iInter_directed_compact
#print axioms HPC.Span.sInter_chain_inter_nonempty
#print axioms HPC.Span.isContinuum_sInter_chain
#print axioms HPC.Span.brouwer_reduction
#print axioms HPC.Span.isClosed_connectedComponentIn_of_isClosed'
#print axioms HPC.Span.exists_surjSpanPos_of_surjSemiSpanPos
#print axioms HPC.Span.semiSpanZero_of_spanZero
-- §5 Theorem 3.6 from Corollary 3.5 (HPC/Span/Thm36.lean)
#print axioms HPC.Span.union_proper_of_indec
#print axioms HPC.Span.exists_dense_proper_subcontinuum
#print axioms HPC.Span.exists_reduced_witness
#print axioms HPC.Span.not_surjSemiSpanPos_univ
#print axioms HPC.Span.ot82_theorem36_of_cor35
#print axioms HPC.Span.theoremC_of_cor35
-- §6.1 re-embedding (HPC/Span/Reembed.lean)
#print axioms HPC.Span.exists_homeomorph_unique_leftmost
#print axioms HPC.Span.exists_homeomorph_ball_step
#print axioms HPC.Span.exists_homeomorph_push
#print axioms HPC.Span.not_separatesPts_of_isConnected_compl
#print axioms HPC.Span.isConnected_rightHalf_diff
-- §6.2 crossing continua (HPC/Span/Crossing.lean)
#print axioms HPC.Span.exists_crossing_subcontinuum
#print axioms HPC.Span.composant_eq_of_mem
#print axioms HPC.Span.exists_uncountable_crossing
-- §6.4 Corollary 3.5 from Theorem 3.2; Theorem C from Theorem 3.2 (HPC/Span/OT82A.lean)
#print axioms HPC.Span.isContinuum_preimage_val_iff
#print axioms HPC.Span.SurjSpanPos.of_image
#print axioms HPC.Span.isHomogeneous_of_homeomorph
#print axioms HPC.Span.not_isDecomposableSpace_of_homeomorph
#print axioms HPC.Span.fst_lt_of_dist_lt
#print axioms HPC.Span.cor35_core
#print axioms HPC.Span.ot82_cor35_of_thm32
#print axioms HPC.Span.theoremC_of_thm32

-- ## Theorem C II (batch 192)
-- §3 parity tools (HPC/Span/OT82Parity.lean)
#print axioms HPC.Span.mem_segment_coords
#print axioms HPC.Span.polygonOf_subset_of_convex
#print axioms HPC.Span.parity_eq_zero_of_not_mem_convex
#print axioms HPC.Span.parity_four
#print axioms HPC.Span.parity_eq_of_perturb
#print axioms HPC.Span.parity_flip_vertical_edge
-- §4 a common zero on a rectangle (HPC/Span/OT82Zero.lean)
#print axioms HPC.Span.mem_Ioo_of_avoid
#print axioms HPC.Span.common_zero_rect
-- §5 strips, the strip lemma (HPC/Span/OT82Strip.lean)
#print axioms HPC.Span.finExt_of_le
#print axioms HPC.Span.continuous_plPath
#print axioms HPC.Span.plPath_eq_range
#print axioms HPC.Span.plPath_piece
#print axioms HPC.Span.piece_mem_Icc
#print axioms HPC.Span.plPath_eq_piece
#print axioms HPC.Span.plPath_zero
#print axioms HPC.Span.plPath_one
#print axioms HPC.Span.plPath_at
#print axioms HPC.Span.plPath_mem_segment
#print axioms HPC.Span.plPath_fst_nonneg
#print axioms HPC.Span.dist_combo_le'
#print axioms HPC.Span.dist_combo_le
#print axioms HPC.Span.dist_plPath_le
#print axioms HPC.Span.segment_plPath_subset
#print axioms HPC.Span.stripPoly_continuous
#print axioms HPC.Span.segment_min_subset
#print axioms HPC.Span.stripPoly_edge_cases
#print axioms HPC.Span.polygonOf_stripPoly_subset
#print axioms HPC.Span.stripPoly_fst_nonneg
#print axioms HPC.Span.parity_stripPoly_left
#print axioms HPC.Span.parity_stripPoly_zero_of_fst_ne
#print axioms HPC.Span.infDist_polygonOf_le
#print axioms HPC.Span.polygonOf_nonempty
#print axioms HPC.Span.parity_strip_eventually
#print axioms HPC.Span.infDist_segment_le
#print axioms HPC.Span.continuous_infDist_segment
#print axioms HPC.Span.mem_openSegment_vertical
#print axioms HPC.Span.height_of_mem_openSegment_vertical
#print axioms HPC.Span.stripInner_eventually
#print axioms HPC.Span.stripSign_continuousOn
#print axioms HPC.Span.stripSign_zero_nonneg
#print axioms HPC.Span.stripSign_nonpos_of_inner
#print axioms HPC.Span.stripSign_eq_zero
#print axioms HPC.Span.stripInner_one_of_isPreconnected
#print axioms HPC.Span.exists_eps_chain
#print axioms HPC.Span.dist_le_of_mem_segment_left
#print axioms HPC.Span.dist_le_of_mem_segment
#print axioms HPC.Span.strip_lemma
-- §6 disjoint crossing continua are ordered (HPC/Span/OT82Order.lean)
#print axioms HPC.Span.ceInd_eq_zero_of_horizontal
#print axioms HPC.Span.ceInd_eq_of_right
#print axioms HPC.Span.crossing_ge_of_subset
#print axioms HPC.Span.crossesEast_vertical
#print axioms HPC.Span.PolyReach.refl
#print axioms HPC.Span.PolyReach.snoc
#print axioms HPC.Span.polyReach_of_isPreconnected
#print axioms HPC.Span.segment_local_of_convex_diff
#print axioms HPC.Span.detour_edge_cases
#print axioms HPC.Span.crossing_core
#print axioms HPC.Span.crossing_traces_separated
-- §7 Theorem 3.2 (strip form) and Theorem C (HPC/Span/OT82B.lean)
#print axioms HPC.Span.exists_not_countable_of_cover
#print axioms HPC.Span.exists_pos_sep
#print axioms HPC.Span.exists_between_three
#print axioms HPC.Span.ot82_theorem32
#print axioms HPC.Span.theoremC

-- ## H–O Theorem 1, I (batch 193)
-- §2 definitions and lemmas (HPC/HO16/Defs.lean)
#print axioms HPC.HO16.IsPLGraph.isCompact
#print axioms HPC.HO16.mem_segment_iff_param
#print axioms HPC.HO16.segment_subset_union_of_mem
#print axioms HPC.HO16.eq_of_mem_segment_halves
#print axioms HPC.HO16.IsPLGraph.exists_fan
#print axioms HPC.HO16.separatesIn_of_closed
-- §3 Krasinkiewicz–Minc Lemma 2 (HPC/HO16/KM77.lean)
#print axioms HPC.HO16.IsPreconnected.subset_of_relClopen
#print axioms HPC.HO16.IsPreconnected.subset_connectedComponentIn_of_meet
#print axioms HPC.HO16.isClosed_biUnion_connectedComponentIn
#print axioms HPC.HO16.km77_lemma2
-- §4 H–O Theorem 8, (1) ⇒ (2), the core (HPC/HO16/Thm8.lean)
#print axioms HPC.HO16.IsFanAt.props
#print axioms HPC.HO16.exists_center_fun
#print axioms HPC.HO16.continuousOn_center_comp
#print axioms HPC.HO16.continuous_correction
#print axioms HPC.HO16.exists_open_nbhd_side
#print axioms HPC.HO16.ho16_theorem8_core
-- §5 H–O Theorem 4, path form (HPC/HO16/Thm4.lean)
#print axioms HPC.HO16.thm4_continuum_of_not_separates
#print axioms HPC.HO16.subset_of_tendsto_of_eventually
#print axioms HPC.HO16.thm4_limit_contra
#print axioms HPC.HO16.ho16_theorem4
-- §6.1, §6.3 plane approximations (HPC/HO16/Plane.lean)
#print axioms HPC.HO16.isContinuum_preimage_val_of
#print axioms HPC.HO16.interior_eq_empty_of_hi
#print axioms HPC.HO16.exists_chain_through
#print axioms HPC.HO16.dist_le_of_mem_segment'
#print axioms HPC.HO16.exists_path_approx
-- §6.2 grid graphs (HPC/HO16/Grid.lean)
#print axioms HPC.HO16.rectGauge_pos
#print axioms HPC.HO16.rectGauge_smul
#print axioms HPC.HO16.continuous_rectGauge
#print axioms HPC.HO16.rectGauge_le_one_iff
#print axioms HPC.HO16.rectGauge_eq_one_iff
#print axioms HPC.HO16.radProj_of_onBdry
#print axioms HPC.HO16.radProj_mem
#print axioms HPC.HO16.continuousOn_radProj
#print axioms HPC.HO16.dist_le_of_mem_rect
#print axioms HPC.HO16.mem_segment_gridH
#print axioms HPC.HO16.mem_segment_gridV
#print axioms HPC.HO16.int_eq_of_mul_eq
#print axioms HPC.HO16.int_le_of_mul_le
#print axioms HPC.HO16.int_le_succ_of_mul_le
#print axioms HPC.HO16.gridP_mem_edge
#print axioms HPC.HO16.exists_gridP_of_mem_two_edges
#print axioms HPC.HO16.gridEdge_inter_subset
#print axioms HPC.HO16.gridEdge_ne
#print axioms HPC.HO16.isInner_gridSq_iff
#print axioms HPC.HO16.mem_gridSq_iff
#print axioms HPC.HO16.onBdry_gridSq
#print axioms HPC.HO16.edges_subset_gridSq
#print axioms HPC.HO16.onBdry_of_mem_two_gridSq
#print axioms HPC.HO16.mem_gridSq_floor
#print axioms HPC.HO16.continuousOn_biUnion_finset
#print axioms HPC.HO16.exists_plGraph_approx
-- §7 the assembly (HPC/HO16/HO16A.lean; `HOThm20` is a hypothesis, not an axiom)
#print axioms HPC.HO16.ho16_theorem1_plane
#print axioms HPC.HO16.isPseudoArc_of_indec_homogeneous
#print axioms HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous

-- ## H–O Theorem 1, II (batch 194)
-- §2 definitions (HPC/HO16/FoldDefs.lean): no theorems
-- §3.1 common subdivision (HPC/HO16/Subdiv.lean)
#print axioms HPC.HO16.Subdiv.real_cross
#print axioms HPC.HO16.Subdiv.real_same
#print axioms HPC.HO16.Subdiv.mem_segment_iff_lineMap
#print axioms HPC.HO16.Subdiv.segment_lineMap
#print axioms HPC.HO16.Subdiv.openSegment_lineMap
#print axioms HPC.HO16.Subdiv.isClosed_segment'
#print axioms HPC.HO16.Subdiv.isCompact_segment'
#print axioms HPC.HO16.Subdiv.cutI_interval
#print axioms HPC.HO16.Subdiv.mem_cutV_fst
#print axioms HPC.HO16.Subdiv.mem_cutV_snd
#print axioms HPC.HO16.Subdiv.mem_cutV_of_mem
#print axioms HPC.HO16.Subdiv.mem_cutV_sInf
#print axioms HPC.HO16.Subdiv.mem_cutV_sSup
#print axioms HPC.HO16.Subdiv.IsPiece.swap
#print axioms HPC.HO16.Subdiv.piece_cross
#print axioms HPC.HO16.Subdiv.piece_same
#print axioms HPC.HO16.Subdiv.piece_inter_aux
#print axioms HPC.HO16.Subdiv.piece_inter
#print axioms HPC.HO16.Subdiv.exists_piece_cover
#print axioms HPC.HO16.Subdiv.exists_common_subdivision
-- §3 the PL-graph library (HPC/HO16/PLLib.lean)
#print axioms HPC.HO16.isPLGraph_biUnion_filter
#print axioms HPC.HO16.isClosed_biUnion_segment
#print axioms HPC.HO16.isPLGraph_biUnion
#print axioms HPC.HO16.IsPLGraph.exists_refinement
#print axioms HPC.HO16.IsPLGraph.exists_refinement_one
#print axioms HPC.HO16.segment_subset_closure_diff
#print axioms HPC.HO16.closure_diff_eq_of_refined
#print axioms HPC.HO16.IsPLGraph.union
#print axioms HPC.HO16.IsPLGraph.closure_diff
#print axioms HPC.HO16.relFrontier_subset_vertices
#print axioms HPC.HO16.finite_vertices
#print axioms HPC.HO16.IsPLGraph.relFrontier_finite
#print axioms HPC.HO16.connectedComponentIn_eq_biUnion
#print axioms HPC.HO16.IsPLGraph.connectedComponentIn
#print axioms HPC.HO16.IsPLGraph.finite_components
#print axioms HPC.HO16.IsPLGraph.inter_connectedComponentIn
#print axioms HPC.HO16.IsPLGraph.image_fst
#print axioms HPC.HO16.IsPLGraph.mem_closure_diff_finite
-- §5 Lemma 6 (HPC/HO16/Lemma6.lean)
#print axioms HPC.HO16.fold_diff_left
#print axioms HPC.HO16.fold_diff_right
#print axioms HPC.HO16.fold_diff_mid
#print axioms HPC.HO16.fold_diff_diff_left
#print axioms HPC.HO16.fold_diff_diff_right
#print axioms HPC.HO16.relFrontier_left_eq
#print axioms HPC.HO16.relFrontier_right_eq
#print axioms HPC.HO16.relFrontier_mid_eq
#print axioms HPC.HO16.relFrontier_disjoint
#print axioms HPC.HO16.relFrontier_diff_left
#print axioms HPC.HO16.relFrontier_diff_right
#print axioms HPC.HO16.mem_nhdsWithin_of_not_mem_closure_diff
#print axioms HPC.HO16.image_fst_mem_nhdsWithin
#print axioms HPC.HO16.continuousOn_invFunOn_fst
#print axioms HPC.HO16.IsFoldTriple.isPLGraph
#print axioms HPC.HO16.IsFoldTriple.relFrontier_left_finite
#print axioms HPC.HO16.IsFoldTriple.relFrontier_right_finite
#print axioms HPC.HO16.ho16_lemma6
-- §4 simple folds exist (HPC/HO16/FoldExists.lean)
#print axioms HPC.HO16.midpoint_eq_lineMap_half
#print axioms HPC.HO16.right_not_mem_segment_left_mid
#print axioms HPC.HO16.left_not_mem_segment_mid_right
#print axioms HPC.HO16.half_facts
#print axioms HPC.HO16.exists_midpoint_subdivision
#print axioms HPC.HO16.lineMap_real
#print axioms HPC.HO16.lineMap_prod
#print axioms HPC.HO16.mem_lift_segment
#print axioms HPC.HO16.fst_mem_of_mem_lift_segment
#print axioms HPC.HO16.lift_point_left
#print axioms HPC.HO16.lift_point_right
#print axioms HPC.HO16.image_fst_lift_segment
#print axioms HPC.HO16.lift_inter_cases
#print axioms HPC.HO16.liftG_props
#print axioms HPC.HO16.lineMap_lt_lineMap
#print axioms HPC.HO16.PairwiseEndpoints.mono
#print axioms HPC.HO16.exists_simpleFold
-- §6 Theorem 8, (1) ⇒ (2), for simple folds (HPC/HO16/Thm8Fold.lean)
#print axioms HPC.HO16.ho16_theorem8
-- §7 Proposition 7 (HPC/HO16/Prop7.lean)
#print axioms HPC.HO16.subset_of_relClopen
#print axioms HPC.HO16.exists_open_inter_eq
#print axioms HPC.HO16.IsPLGraph.comp_mem_nhdsWithin
#print axioms HPC.HO16.IsPLGraph.exists_open_comp
#print axioms HPC.HO16.isPreconnected_lift
#print axioms HPC.HO16.IsSimpleFoldOf.symm
#print axioms HPC.HO16.fold_union_symm
#print axioms HPC.HO16.IsSimpleFoldOf.exists_glue
#print axioms HPC.HO16.IsSimpleFoldOf.isPLGraph_union
#print axioms HPC.HO16.IsSimpleFoldOf.image_union
#print axioms HPC.HO16.disjoint_lift_of_disjoint_right
#print axioms HPC.HO16.comp_not_disjoint_both
#print axioms HPC.HO16.lift_subset_of_meets_both
#print axioms HPC.HO16.image_comp_mem_nhds_glue
#print axioms HPC.HO16.image_comp_eq
#print axioms HPC.HO16.isClosed_compsMiss
#print axioms HPC.HO16.mem_compsMiss
#print axioms HPC.HO16.of_mem_compsMiss
#print axioms HPC.HO16.Z_disjoint
#print axioms HPC.HO16.exists_comp_meets_both
#print axioms HPC.HO16.comp_meets_right
#print axioms HPC.HO16.comp_meets_left
#print axioms HPC.HO16.mem_comp_of_mid
#print axioms HPC.HO16.mem_comp_of_sides
#print axioms HPC.HO16.left_diff_subset_Z
#print axioms HPC.HO16.frontier_clause
#print axioms HPC.HO16.ho16_prop7
-- non-vacuity of `IsFoldTriple` / `IsSimpleFoldOf` (HPC/HO16/FoldExample.lean)
#print axioms HPC.HO16.isPLGraph_Icc
#print axioms HPC.HO16.isFoldTriple_example
#print axioms HPC.HO16.relFrontier_example_left
#print axioms HPC.HO16.relFrontier_example_right
#print axioms HPC.HO16.exists_simpleFold_example
-- §8 Theorem 1 (p. 211) and Theorem 1′ (p. 212) as printed (HPC/HO16/HO16B.lean)
#print axioms HPC.HO16.isHereditarilyIndecomposable_unit
#print axioms HPC.HO16.hoSpanZero_unit
#print axioms HPC.HO16.surjSemiSpanZero_unit
#print axioms HPC.HO16.not_homeomorph_pseudoArc_unit
#print axioms HPC.HO16.ho16_theorem1_printed_false
#print axioms HPC.HO16.ho16_theorem1prime_printed_false

-- ## H–O Theorem 1, III (batch 195)
-- §1 definitions (HPC/HO16/StairDefs.lean): no theorems
-- §2 library additions: components of complements, ordinary points, intersections (HPC/HO16/PLLib2.lean)
#print axioms HPC.HO16.mem_piece_of_mem_connectedComponentIn
#print axioms HPC.HO16.connectedComponentIn_eq_biUnion_pieces
#print axioms HPC.HO16.finite_components_of_pieces
#print axioms HPC.HO16.isPLGraph_empty
#print axioms HPC.HO16.IsPLGraph.biUnion_finite
#print axioms HPC.HO16.IsPLGraph.exists_pieces
#print axioms HPC.HO16.IsPLGraph.connectedComponentIn_inter_mem_nhdsWithin
#print axioms HPC.HO16.IsPLGraph.finite_components_diff
#print axioms HPC.HO16.IsPLGraph.comp_diff_mem_nhdsWithin
#print axioms HPC.HO16.IsPLGraph.closure_comp_diff
#print axioms HPC.HO16.IsPLGraph.relFrontier_comp_diff
#print axioms HPC.HO16.isOrdinaryPt_of_mem_openSegment
#print axioms HPC.HO16.posPar_of_mem_segment
#print axioms HPC.HO16.exists_common_of_posPar
#print axioms HPC.HO16.exists_small_step
#print axioms HPC.HO16.smul_rescale
#print axioms HPC.HO16.isOrdinaryPt_iff_order
#print axioms HPC.HO16.IsPLGraph.finite_not_ordinary
#print axioms HPC.HO16.IsPLGraph.inter_eq_union_finite
#print axioms HPC.HO16.isPLGraph_segment
#print axioms HPC.HO16.image_fst_segment
#print axioms HPC.HO16.injOn_fst_segment
#print axioms HPC.HO16.IsPLPlusFinite.union
#print axioms HPC.HO16.isPLPlusFinite_biUnion
#print axioms HPC.HO16.segment_inter_preimage_fst
#print axioms HPC.HO16.IsPLGraph.inter_preimage_fst
#print axioms HPC.HO16.isPLGraph_union_finite
-- §3 sides: workhorse lemmas (HPC/HO16/SidesLib.lean)
#print axioms HPC.HO16.exists_open_eq_inter
#print axioms HPC.HO16.IsPreconnected.subset_of_relClopenG
#print axioms HPC.HO16.inter_nonempty_of_mem_nhdsWithin
#print axioms HPC.HO16.comp_subset_G
#print axioms HPC.HO16.closure_subset_union_relFrontier
#print axioms HPC.HO16.IsPLGraph.compDiff_mem_nhdsWithin
#print axioms HPC.HO16.IsPLGraph.relFrontier_comp_subset
#print axioms HPC.HO16.IsPLGraph.relFrontier_comp_subset_relFrontier
#print axioms HPC.HO16.IsPLGraph.relFrontier_comp_nonempty
#print axioms HPC.HO16.IsPLGraph.closure_comp_inter_nonempty
#print axioms HPC.HO16.IsPLGraph.mem_closure_comp
#print axioms HPC.HO16.IsPLGraph.comp_eq_of_relFrontier_subset
#print axioms HPC.HO16.comp_subset_or_disjoint
#print axioms HPC.HO16.sideOf_subset
#print axioms HPC.HO16.isClosed_sideOf
#print axioms HPC.HO16.comp_subset_sideOf
#print axioms HPC.HO16.IsPLGraph.comp_meets_of_mem_sideOf
#print axioms HPC.HO16.IsPLGraph.disjoint_comp_sideOf
#print axioms HPC.HO16.subset_sideOf_diff
#print axioms HPC.HO16.IsPLGraph.subset_sideOf
#print axioms HPC.HO16.IsPLGraph.relFrontier_sideOf_subset
#print axioms HPC.HO16.IsPLGraph.disjoint_relFrontier_of_meets_sideOf
#print axioms HPC.HO16.IsPLGraph.mem_sideOf_of_relFrontier
#print axioms HPC.HO16.IsPLGraph.sideOf_char_aux
-- §3 Definition 9 observations, Propositions 10 and 11 (HPC/HO16/Sides.lean)
#print axioms HPC.HO16.ho16_obs9_emptyB
#print axioms HPC.HO16.ho16_obs9_emptyA
#print axioms HPC.HO16.ho16_obs9_nhds
#print axioms HPC.HO16.ho16_obs9_char
#print axioms HPC.HO16.ho16_obs9_unique
#print axioms HPC.HO16.sideOf_empty_of_connected
#print axioms HPC.HO16.ho16_prop10
#print axioms HPC.HO16.ho16_prop11
#print axioms HPC.HO16.ho16_prop11_frontier
#print axioms HPC.HO16.ho16_prop11_remark
-- §§4–6 tools for straight sets and stairwell structures (HPC/HO16/StairLib.lean)
#print axioms HPC.HO16.IsStraight.isCompact
#print axioms HPC.HO16.IsStraight.image_subset
#print axioms HPC.HO16.IsStraight.image_endSet
#print axioms HPC.HO16.endSet_subset
#print axioms HPC.HO16.disjoint_image_fst_of_injOn
#print axioms HPC.HO16.hasConsCompl_empty
#print axioms HPC.HO16.IsPLGraph.isClosed_comp
#print axioms HPC.HO16.IsPLGraph.comp_relOpen
#print axioms HPC.HO16.IsPLGraph.closure_inter_comp
#print axioms HPC.HO16.IsPLGraph.relFrontier_inter_comp
#print axioms HPC.HO16.image_fst_inter_star
#print axioms HPC.HO16.image_fst_inter_star_subset
#print axioms HPC.HO16.IsPLGraph.endSet_inter_comp
#print axioms HPC.HO16.IsStraight.inter_comp
#print axioms HPC.HO16.comp_diff_inter_comp
#print axioms HPC.HO16.HasConsCompl.inter_comp
#print axioms HPC.HO16.IsOrdinaryPt.comp
#print axioms HPC.HO16.forall₂_exists_of_mem
#print axioms HPC.HO16.IsGeneric.of_forall₂
#print axioms HPC.HO16.IsGeneric.perm
#print axioms HPC.HO16.IsGeneric.sublist
#print axioms HPC.HO16.parity_count
-- §§4–8 observation 12, observations 13/16 relative to a component, Claim 14.1, odd image, height one, Proposition 17, remarks after 17, the fold of Proposition 19 (HPC/HO16/Stairwell.lean)
#print axioms HPC.HO16.ho16_obs12
#print axioms HPC.HO16.ho16_obs13_comp
#print axioms HPC.HO16.ho16_claim14_1
#print axioms HPC.HO16.ho16_odd_image
#print axioms HPC.HO16.ho16_height_one
#print axioms HPC.HO16.ho16_obs16_comp
#print axioms HPC.HO16.ho16_prop17
#print axioms HPC.HO16.ho16_prop17_exists
#print axioms HPC.HO16.ho16_rem17_gamma
#print axioms HPC.HO16.ho16_rem17_P1
#print axioms HPC.HO16.ho16_prop19_fold
-- §7 Lemma 18 (HPC/HO16/Lemma18.lean)
#print axioms HPC.HO16.continuous_phiStar
#print axioms HPC.HO16.image_foldPre_inter
#print axioms HPC.HO16.image_foldPre
#print axioms HPC.HO16.injOn_foldPre
#print axioms HPC.HO16.lift_mem_closure
#print axioms HPC.HO16.lemma18_claim
#print axioms HPC.HO16.lemma18_claim'
#print axioms HPC.HO16.lemma18_points
#print axioms HPC.HO16.ho16_lemma18
-- §9 certificate (p. 193 remark without connectedness) and non-vacuity example (HPC/HO16/StairExample.lean)
#print axioms HPC.HO16.isStraight_segment
#print axioms HPC.HO16.isStraight_prod_singleton
#print axioms HPC.HO16.ho16_p193_remark_false
#print axioms HPC.HO16.relFrontier_Icc03_Icc02
#print axioms HPC.HO16.relFrontier_Icc03_Icc12
#print axioms HPC.HO16.relFrontier_Icc03_Icc13
#print axioms HPC.HO16.hasConsCompl_of_relFrontier_subset
#print axioms HPC.HO16.isOrdinaryPt_Icc03
#print axioms HPC.HO16.stairwell_example'
#print axioms HPC.HO16.stairwell_example
#print axioms HPC.HO16.broken_stairwell_example
#print axioms HPC.HO16.lemma18_example
#print axioms HPC.HO16.prop19_fold_example

-- ## H–O Theorem 1, IV (batch 196)
-- §2 ordinary points of a fold (HPC/HO16/OrdFold.lean)
#print axioms HPC.HO16.mem_segment_of_posPar_of_dist_le
#print axioms HPC.HO16.lineMap_mem_segment
#print axioms HPC.HO16.dist_lineMap_left'
#print axioms HPC.HO16.IsOrdinaryPt.of_local
#print axioms HPC.HO16.isOrdinaryPt_congr_local
#print axioms HPC.HO16.image_fst_openSegment
#print axioms HPC.HO16.isOrdinaryPt_image_fst_iff
#print axioms HPC.HO16.isOrdinaryPt_one_sheet
#print axioms HPC.HO16.exists_single_spoke
#print axioms HPC.HO16.posPar_of_mem_segment'
#print axioms HPC.HO16.segment_infinite_of_ne
#print axioms HPC.HO16.one_side_of_relFrontier
#print axioms HPC.HO16.IsSimpleFoldOf.isOrdinaryPt_of_mem_inter
#print axioms HPC.HO16.IsSimpleFoldOf.isOrdinaryPt_iff
-- §3 Proposition 19, library (HPC/HO16/P19Lib.lean)
#print axioms HPC.HO16.inter_preimage_image_of_injOn
#print axioms HPC.HO16.foldPre_mono
#print axioms HPC.HO16.foldPre_union
#print axioms HPC.HO16.foldPre_empty
#print axioms HPC.HO16.disjoint_foldPre
#print axioms HPC.HO16.isClosed_foldPre
#print axioms HPC.HO16.fst_mem_of_mem_foldPre
#print axioms HPC.HO16.phiStar_mem_of_injOn
#print axioms HPC.HO16.foldPre_finite
#print axioms HPC.HO16.hasConsCompl_pullback
-- §3 Proposition 19, hypotheses and basic facts (HPC/HO16/P19Ctx.lean)
#print axioms HPC.HO16.mem_gen_list
#print axioms HPC.HO16.P19.i₀_pos
#print axioms HPC.HO16.P19.i₀_le
#print axioms HPC.HO16.P19.T_straight
#print axioms HPC.HO16.P19.P₁_straight
#print axioms HPC.HO16.P19.P₂_straight
#print axioms HPC.HO16.P19.S_eq
#print axioms HPC.HO16.P19.endSet_T
#print axioms HPC.HO16.P19.endSet_Ti₀
#print axioms HPC.HO16.P19.disj_αα
#print axioms HPC.HO16.P19.disj_αγ
#print axioms HPC.HO16.P19.disj_α'γ
#print axioms HPC.HO16.P19.α_finite
#print axioms HPC.HO16.P19.γ_finite
#print axioms HPC.HO16.P19.α_one
#print axioms HPC.HO16.P19.α_last
#print axioms HPC.HO16.P19.endSet_P₂
#print axioms HPC.HO16.P19.disj_Eγ
#print axioms HPC.HO16.P19.S3
#print axioms HPC.HO16.P19.S3W
#print axioms HPC.HO16.P19.S4
#print axioms HPC.HO16.P19.S4γ
#print axioms HPC.HO16.P19.gen
#print axioms HPC.HO16.P19.S6
#print axioms HPC.HO16.P19.S3V
#print axioms HPC.HO16.P19.S4P₂E
#print axioms HPC.HO16.P19.S4P₂γ
#print axioms HPC.HO16.P19.fold
#print axioms HPC.HO16.P19.FPL
#print axioms HPC.HO16.P19.Fclosed
#print axioms HPC.HO16.P19.imgF
#print axioms HPC.HO16.P19.F₁PL
#print axioms HPC.HO16.P19.F₂PL
#print axioms HPC.HO16.P19.F₃PL
#print axioms HPC.HO16.P19.inj₁
#print axioms HPC.HO16.P19.img₁
#print axioms HPC.HO16.P19.inj₂
#print axioms HPC.HO16.P19.img₂
#print axioms HPC.HO16.P19.inj₃
#print axioms HPC.HO16.P19.img₃
#print axioms HPC.HO16.P19.disj₁₃
#print axioms HPC.HO16.P19.fr12
#print axioms HPC.HO16.P19.fr23
#print axioms HPC.HO16.P19.relFrontier_G₂
#print axioms HPC.HO16.P19.Ti₀_sub_img₃
#print axioms HPC.HO16.P19.γ_sub_Ti₀
#print axioms HPC.HO16.P19.γ_sub_P₂
#print axioms HPC.HO16.P19.E_sub_P₂
#print axioms HPC.HO16.P19.αi₀_sub_Ti₀
#print axioms HPC.HO16.P19.αi₀1_sub_Ti₀
#print axioms HPC.HO16.P19.gen_cross
#print axioms HPC.HO16.P19.disj_Eγ_img
#print axioms HPC.HO16.P19.disj_α_E
#print axioms HPC.HO16.P19.disj_α_γ
#print axioms HPC.HO16.P19.ordinary_E
#print axioms HPC.HO16.P19.ordinary_γ
#print axioms HPC.HO16.P19.ordinary_frontier
#print axioms HPC.HO16.P19.pre_E
#print axioms HPC.HO16.P19.pre_γ₃
#print axioms HPC.HO16.P19.pre_γ₂
#print axioms HPC.HO16.P19.pre_γ_sub
#print axioms HPC.HO16.P19.pre_γ_disj₁₂
#print axioms HPC.HO16.P19.pre_αi₀
#print axioms HPC.HO16.P19.pre_α_disj₁₂
#print axioms HPC.HO16.P19.pre_α_disj₂₃
#print axioms HPC.HO16.P19.exists_lift
-- §3 Proposition 19, (19.4), (19.8), (19.9) (HPC/HO16/Prop19A.lean)
#print axioms HPC.HO16.isPLGraph_sheet_inter_preimage
#print axioms HPC.HO16.P19.relFrontier_F₁
#print axioms HPC.HO16.P19.relFrontier_F₃
#print axioms HPC.HO16.P19.relFrontier_F₂
#print axioms HPC.HO16.P19.straight_T
#print axioms HPC.HO16.P19.straight_P'₁
#print axioms HPC.HO16.P19.frontier_inter_sub
#print axioms HPC.HO16.P19.straight_P'₂
-- §3 Proposition 19, level i₀, (19.5)-(19.7) (HPC/HO16/Prop19B.lean)
#print axioms HPC.HO16.p19T_self
#print axioms HPC.HO16.p19T_ne
#print axioms HPC.HO16.p19α_succ
#print axioms HPC.HO16.p19α_ne
#print axioms HPC.HO16.eq_of_phiStar_eq
#print axioms HPC.HO16.P19.Ti₀_straight
#print axioms HPC.HO16.P19.γ_img_sub
#print axioms HPC.HO16.P19.image_T'₀
#print axioms HPC.HO16.P19.isPLGraph_image_T'₀
#print axioms HPC.HO16.P19.compl_image_T'₀
#print axioms HPC.HO16.P19.relFrontier_T'₀
#print axioms HPC.HO16.P19.straight_T'₀
#print axioms HPC.HO16.P19.endSet_T'₀
-- §3 Proposition 19, images, (S3'), (S5'), (S6') (HPC/HO16/Prop19C.lean)
#print axioms HPC.HO16.p19α_sub
#print axioms HPC.HO16.preimage_fst_mem_nhdsSet
#print axioms HPC.HO16.inter_pullback_eq
#print axioms HPC.HO16.disjoint_of_over
#print axioms HPC.HO16.P19.α_sub_T
#print axioms HPC.HO16.P19.α_subG
#print axioms HPC.HO16.P19.γ_subG
#print axioms HPC.HO16.P19.i₀1_mem
#print axioms HPC.HO16.P19.i₀_mem
#print axioms HPC.HO16.P19.img_T'
#print axioms HPC.HO16.P19.img_α
#print axioms HPC.HO16.P19.img_γ
#print axioms HPC.HO16.P19.img_α₃
#print axioms HPC.HO16.P19.img_α₁₂
#print axioms HPC.HO16.P19.img_P'₁
#print axioms HPC.HO16.P19.img_P'₂
#print axioms HPC.HO16.P19.α₃_off
#print axioms HPC.HO16.P19.α₁₂_off
#print axioms HPC.HO16.P19.α₀_off
#print axioms HPC.HO16.P19.img_T'_off
#print axioms HPC.HO16.P19.α'_over
#print axioms HPC.HO16.P19.S3'T
#print axioms HPC.HO16.P19.S3'P
#print axioms HPC.HO16.P19.S3'γ
#print axioms HPC.HO16.P19.S6'
#print axioms HPC.HO16.P19.ordinary_lift
#print axioms HPC.HO16.P19.ordinary_α
#print axioms HPC.HO16.P19.generic_member
#print axioms HPC.HO16.P19.α'_finite
#print axioms HPC.HO16.P19.gen'_pairwise
#print axioms HPC.HO16.P19.gen'_members
#print axioms HPC.HO16.P19.gen'_stair
#print axioms HPC.HO16.P19.gen'_broken
-- §3 Proposition 19, (S4') (HPC/HO16/Prop19D.lean)
#print axioms HPC.HO16.relFrontier_over
#print axioms HPC.HO16.hasConsCompl_congr
#print axioms HPC.HO16.P19.F₁₂closed
#print axioms HPC.HO16.P19.F₃closed
#print axioms HPC.HO16.P19.imgF_sub
#print axioms HPC.HO16.P19.Gclosed
#print axioms HPC.HO16.P19.T_img_closed
#print axioms HPC.HO16.P19.comp_side
#print axioms HPC.HO16.P19.comp_over
#print axioms HPC.HO16.P19.S4'_reg
#print axioms HPC.HO16.P19.S4'_i₀
#print axioms HPC.HO16.P19.split_i₀1
#print axioms HPC.HO16.P19.S4'_i₀1_α
#print axioms HPC.HO16.P19.S4'_i₀1_γ
#print axioms HPC.HO16.P19.split_P'₂
#print axioms HPC.HO16.P19.S4'_P'₂_E
#print axioms HPC.HO16.P19.S4'_P'₂_γ
#print axioms HPC.HO16.P19.S4'T
-- §3 Proposition 19 in the full fold (HPC/HO16/Prop19.lean)
#print axioms HPC.HO16.foldPre_split
#print axioms HPC.HO16.lift_mem_foldPre
#print axioms HPC.HO16.P19.S1'T
#print axioms HPC.HO16.P19.P'₁_nonempty
#print axioms HPC.HO16.P19.P'₂_nonempty
#print axioms HPC.HO16.P19.S2'T
#print axioms HPC.HO16.P19.α'_finite'
#print axioms HPC.HO16.P19.α'_one
#print axioms HPC.HO16.P19.α'_last
#print axioms HPC.HO16.P19.sub_foldPre_S
#print axioms HPC.HO16.P19.broken
#print axioms HPC.HO16.P19.stair
#print axioms HPC.HO16.ho16_prop19_full
-- §3 Proposition 19, connected fold (HPC/HO16/Prop19Conn.lean)
#print axioms HPC.HO16.relFrontier_eq_empty_of_superset
#print axioms HPC.HO16.foldPre_inter_comp
#print axioms HPC.HO16.P19.relFrontier_G₁_ne
#print axioms HPC.HO16.P19.relFrontier_G₃_ne
#print axioms HPC.HO16.P19.comp_meets_F₂₃
#print axioms HPC.HO16.P19.T'_meets
#print axioms HPC.HO16.P19.γ_lift
#print axioms HPC.HO16.ho16_prop19
#print axioms HPC.HO16.hoProp19_holds
-- §4 certificate for p. 208 (HPC/HO16/P208.lean)
#print axioms HPC.HO16.fst_image_prod_single
#print axioms HPC.HO16.isStraight_prod_single
#print axioms HPC.HO16.endSet_prod_single
#print axioms HPC.HO16.isOrdinaryPt_Icc
#print axioms HPC.HO16.comp_subset_Ioo
#print axioms HPC.HO16.hasConsCompl_of_gaps
#print axioms HPC.HO16.relFrontier_eq_of
#print axioms HPC.HO16.p208_rf_A1
#print axioms HPC.HO16.p208_rf_A2
#print axioms HPC.HO16.p208_rf_G
#print axioms HPC.HO16.p208_rf_P1
#print axioms HPC.HO16.p208_rf_P2
#print axioms HPC.HO16.p208_half
#print axioms HPC.HO16.isPLGraph_p208G
#print axioms HPC.HO16.isPLGraph_p208A1
#print axioms HPC.HO16.isPLGraph_p208A2
#print axioms HPC.HO16.isPLGraph_p208P1
#print axioms HPC.HO16.isPLGraph_p208P2
#print axioms HPC.HO16.p208A1_sub
#print axioms HPC.HO16.p208A2_sub
#print axioms HPC.HO16.p208P1_sub
#print axioms HPC.HO16.p208P2_sub
#print axioms HPC.HO16.p208T1
#print axioms HPC.HO16.p208T2
#print axioms HPC.HO16.p208T3
#print axioms HPC.HO16.p208α2
#print axioms HPC.HO16.p208α_ne
#print axioms HPC.HO16.endSet_p208T1
#print axioms HPC.HO16.endSet_p208T2
#print axioms HPC.HO16.endSet_p208T3
#print axioms HPC.HO16.endSet_p208PP1
#print axioms HPC.HO16.endSet_p208PP2
#print axioms HPC.HO16.disj_single_prod
#print axioms HPC.HO16.gens_ordinary
#print axioms HPC.HO16.ho16_p208_false
-- §5 Theorem 20 with Proposition 19 as a hypothesis (HPC/HO16/Thm20.lean)
#print axioms HPC.HO16.isHereditarilyIndecomposable_univ_subtype
#print axioms HPC.HO16.ho16_lift_aux
#print axioms HPC.HO16.ho16_lift_stairwell_of_prop19
#print axioms HPC.HO16.ho16_theorem20_of_thm15_prop19
#print axioms HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19
-- §5 Theorem 20 from Theorem 15, skeleton form (HPC/HO16/HO16D.lean)
#print axioms HPC.HO16.ho16_lift_stairwell
#print axioms HPC.HO16.ho16_theorem20_of_thm15
#print axioms HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous_of_thm15
-- §6 non-vacuity (HPC/HO16/NonVac196.lean)
#print axioms HPC.HO16.prop19_example_stair
#print axioms HPC.HO16.prop19_example_broken
#print axioms HPC.HO16.isHereditarilyIndecomposable_univ_unit
#print axioms HPC.HO16.lift_stairwell_example
#print axioms HPC.HO16.hoThm15_segment_hyps

-- ## H–O Theorem 1, V (batch 197)
-- §2 ladder definitions, parameter calculus (HPC/HO16/LadderParam.lean)
#print axioms HPC.HO16.zU_pos
#print axioms HPC.HO16.zz_lr
#print axioms HPC.HO16.zzL_ge
#print axioms HPC.HO16.zz_step
#print axioms HPC.HO16.zz_lam
#print axioms HPC.HO16.zU_le
#print axioms HPC.HO16.zzR_grid
#print axioms HPC.HO16.zzL_grid
#print axioms HPC.HO16.lam_grid
#print axioms HPC.HO16.wδ_pos
#print axioms HPC.HO16.wδ_le
#print axioms HPC.HO16.wcases
#print axioms HPC.HO16.w_cover
#print axioms HPC.HO16.w_QA_P
#print axioms HPC.HO16.w_QB_P
#print axioms HPC.HO16.w_QA_QB
#print axioms HPC.HO16.w_A_sub
#print axioms HPC.HO16.w_ends
#print axioms HPC.HO16.w_gap
#print axioms HPC.HO16.w_S3
#print axioms HPC.HO16.w_I_disj
#print axioms HPC.HO16.w_A_grid
#print axioms HPC.HO16.w_A_idx
#print axioms HPC.HO16.int_of_real_eq
#print axioms HPC.HO16.w_A_disj
#print axioms HPC.HO16.eδ_pos
#print axioms HPC.HO16.e_cover
#print axioms HPC.HO16.e_QA_P
#print axioms HPC.HO16.e_QB_P
#print axioms HPC.HO16.e_QA_QB
#print axioms HPC.HO16.e_A_sub
#print axioms HPC.HO16.e_A_finite
#print axioms HPC.HO16.e_ends
#print axioms HPC.HO16.e_gap
#print axioms HPC.HO16.e_S3
#print axioms HPC.HO16.e_A_disj
#print axioms HPC.HO16.e_A_one
#print axioms HPC.HO16.e_A_top
#print axioms HPC.HO16.e_P_sub
-- §3 the pieces over one edge (HPC/HO16/LadderPiece.lean)
#print axioms HPC.HO16.zzLine_eq
#print axioms HPC.HO16.pieceLine_fst
#print axioms HPC.HO16.segment_lineMap_Icc
#print axioms HPC.HO16.eI_sub_eP
#print axioms HPC.HO16.eP_eq_iUnion
#print axioms HPC.HO16.ladderPiece_eq
#print axioms HPC.HO16.eI_sub_Icc
#print axioms HPC.HO16.eI_disj
#print axioms HPC.HO16.eI_zero
#print axioms HPC.HO16.eI_one
#print axioms HPC.HO16.mem_ladderPiece
#print axioms HPC.HO16.image_fst_ladderPiece
#print axioms HPC.HO16.lineMap_inj
#print axioms HPC.HO16.injOn_fst_ladderPiece
#print axioms HPC.HO16.pieceLine_zero
#print axioms HPC.HO16.pieceLine_one
#print axioms HPC.HO16.ladderPiece_snd_of_fst
#print axioms HPC.HO16.ladderPiece_snd_of_snd
#print axioms HPC.HO16.mem_ladderPiece_fst
#print axioms HPC.HO16.mem_ladderPiece_snd
#print axioms HPC.HO16.pieceLine_tip
#print axioms HPC.HO16.image_fst_ladderAlpha
#print axioms HPC.HO16.ladderAlpha_finite
#print axioms HPC.HO16.ladderAlpha_one
#print axioms HPC.HO16.ladderAlpha_top
#print axioms HPC.HO16.ladderAlpha_subset
#print axioms HPC.HO16.ladderY_mem
#print axioms HPC.HO16.ladderPiece_subset
#print axioms HPC.HO16.eI_shape
#print axioms HPC.HO16.isPLGraph_image_eP
#print axioms HPC.HO16.isCompact_ite_Icc
#print axioms HPC.HO16.isCompact_eQA
#print axioms HPC.HO16.isCompact_eQB
#print axioms HPC.HO16.isCompact_eP
#print axioms HPC.HO16.isCompact_ite_segment
#print axioms HPC.HO16.isCompact_ladderPiece
-- §3 the decomposition, (S1), gaps (HPC/HO16/LadderStair.lean)
#print axioms HPC.HO16.segment_subset_of_mem
#print axioms HPC.HO16.lineMap_mem_of_mem
#print axioms HPC.HO16.exists_param_of_mem
#print axioms HPC.HO16.lineMap_eq_left_iff
#print axioms HPC.HO16.lineMap_eq_right_iff
#print axioms HPC.HO16.eq_of_lineMap_mem_segment
#print axioms HPC.HO16.exists_ball_param
#print axioms HPC.HO16.IsLadder.ne
#print axioms HPC.HO16.IsLadder.G_eq
#print axioms HPC.HO16.IsLadder.dis
#print axioms HPC.HO16.IsLadder.evOK
#print axioms HPC.HO16.IsLadder.eJ2_eq
#print axioms HPC.HO16.IsLadder.piece_subset
#print axioms HPC.HO16.image_fst_ladderSheet
#print axioms HPC.HO16.image_fst_ladderAlphaSet
#print axioms HPC.HO16.mem_image_fst_ladderSheet
#print axioms HPC.HO16.ladderSheet_subset
#print axioms HPC.HO16.injOn_fst_ladderSheet
#print axioms HPC.HO16.IsLadder.isPLGraph
#print axioms HPC.HO16.isCompact_ladderSheet
#print axioms HPC.HO16.isCompact_image_fst_ladderSheet
#print axioms HPC.HO16.isPLGraph_image_fst_ladderSheet
#print axioms HPC.HO16.isStraight_ladderSheet
#print axioms HPC.HO16.length_le_ladderHeight
#print axioms HPC.HO16.exists_ladderHeight
#print axioms HPC.HO16.odd_ladderHeight
#print axioms HPC.HO16.ladderSheet_nonempty
#print axioms HPC.HO16.eQA_sub
#print axioms HPC.HO16.eQB_sub
#print axioms HPC.HO16.eA_sub_Ioo
#print axioms HPC.HO16.isClosed_gapA
#print axioms HPC.HO16.isClosed_gapB
#print axioms HPC.HO16.gapA_subset
#print axioms HPC.HO16.gapB_subset
#print axioms HPC.HO16.subset_sheet_union_gaps
#print axioms HPC.HO16.vertex_of_two
#print axioms HPC.HO16.vertex_label
#print axioms HPC.HO16.vertex_label_of_two
#print axioms HPC.HO16.gap_inter_sheet
#print axioms HPC.HO16.gapA_inter_sheet
#print axioms HPC.HO16.gapB_inter_sheet
#print axioms HPC.HO16.disjoint_gapA_gapB
-- §3 (S2)–(S5) and the stairwell structure (HPC/HO16/LadderStair2.lean)
#print axioms HPC.HO16.ladderAlphaSet_subset
#print axioms HPC.HO16.ladderAlphaSet_finite
#print axioms HPC.HO16.mem_image_fst_ladderAlphaSet
#print axioms HPC.HO16.lineMap_interior_eq
#print axioms HPC.HO16.disjoint_image_fst_ladderAlphaSet
#print axioms HPC.HO16.mem_closure_diff_sheet
#print axioms HPC.HO16.relFrontier_image_fst_ladderSheet
#print axioms HPC.HO16.endSet_ladderSheet
#print axioms HPC.HO16.ladder_S3
#print axioms HPC.HO16.relFrontier_gapA_subset
#print axioms HPC.HO16.relFrontier_comp_ladder
#print axioms HPC.HO16.ladder_S4
#print axioms HPC.HO16.ladder_S5
#print axioms HPC.HO16.ladder_isStairwellStr
-- §5 uniform subdivision (HPC/HO16/LadderSubdiv.lean)
#print axioms HPC.HO16.mem_subdiv
#print axioms HPC.HO16.subPt_zero
#print axioms HPC.HO16.subPt_n
#print axioms HPC.HO16.segment_subEdge
#print axioms HPC.HO16.Icc_sub_unit
#print axioms HPC.HO16.segment_subEdge_subset
#print axioms HPC.HO16.subdiv_ne
#print axioms HPC.HO16.biUnion_subdiv
#print axioms HPC.HO16.mem_ends_subEdge
#print axioms HPC.HO16.pairwiseEndpoints_subdiv
#print axioms HPC.HO16.dist_subEdge
-- §5 sign sequences, one flip (HPC/HO16/LadderSign.lean)
#print axioms HPC.HO16.mem_chg
#print axioms HPC.HO16.chg_congr
#print axioms HPC.HO16.sgnList_congr
#print axioms HPC.HO16.chg_succ
#print axioms HPC.HO16.length_chg_mod
#print axioms HPC.HO16.odd_length_chg
#print axioms HPC.HO16.midH_mem
#print axioms HPC.HO16.midH_inj
#print axioms HPC.HO16.abs_midH_pred
#print axioms HPC.HO16.abs_midH_self
#print axioms HPC.HO16.midH_mean
#print axioms HPC.HO16.range_split
#print axioms HPC.HO16.chg_split
#print axioms HPC.HO16.chg_flip
#print axioms HPC.HO16.chgPair_cases
#print axioms HPC.HO16.snd_mem_segment
#print axioms HPC.HO16.heightOK_of_segment
#print axioms HPC.HO16.getD_map_lt
#print axioms HPC.HO16.getD_mem_of_lt
#print axioms HPC.HO16.firstDiff_append_left
#print axioms HPC.HO16.firstDiff_le
#print axioms HPC.HO16.heightOK_of_mem_piece
-- §5 a sign function for a separator (HPC/HO16/LadderSep.lean)
#print axioms HPC.HO16.abs_infDist_sub_le
#print axioms HPC.HO16.exists_sign_fn
-- §5 the ladder inside U (HPC/HO16/LadderExists.lean)
#print axioms HPC.HO16.LData.fst_mem
#print axioms HPC.HO16.LData.snd_mem
#print axioms HPC.HO16.LData.σV_zero
#print axioms HPC.HO16.LData.σV_N
#print axioms HPC.HO16.LData.σE_zero
#print axioms HPC.HO16.LData.σE_N
#print axioms HPC.HO16.subPt_eq_fst_iff
#print axioms HPC.HO16.subPt_eq_snd_iff
#print axioms HPC.HO16.LData.sgnList_vertex
#print axioms HPC.HO16.LData.sgnList_wd
#print axioms HPC.HO16.LData.ly_eq
#print axioms HPC.HO16.lσE_flip
#print axioms HPC.HO16.length_chg_flip
#print axioms HPC.HO16.LData.piece_ends
#print axioms HPC.HO16.LData.mem_ly
#print axioms HPC.HO16.wedgeEv_eq_some
#print axioms HPC.HO16.wedgeEv_eq_none
#print axioms HPC.HO16.getD_mem_list
#print axioms HPC.HO16.LData.isLadder
#print axioms HPC.HO16.abs_midH_succ
#print axioms HPC.HO16.lσV_ne
#print axioms HPC.HO16.lσE_corner
#print axioms HPC.HO16.LData.sheet_corners
#print axioms HPC.HO16.dist_le_of_mem_segment_ends
#print axioms HPC.HO16.exists_ladder_aux
-- §3, §5 skeleton theorems (HPC/HO16/HO16E.lean)
#print axioms HPC.HO16.ho16_stairwell_of_ladder
#print axioms HPC.HO16.exists_ladder
#print axioms HPC.HO16.ho16_theorem15
#print axioms HPC.HO16.ho16_theorem20
#print axioms HPC.HO16.ho16_indec_homogeneous_pseudoArc
#print axioms HPC.HO16.isIndecomposable_univ_of_isIndecomposable
#print axioms HPC.HO16.not_isDecomposableSpace_of_isIndecomposable_univ
#print axioms HPC.HO16.ho16_pseudoArc_indec_homogeneous
#print axioms HPC.HO16.ho16_indec_homogeneous_iff
#print axioms HPC.HO16.exists_indec_homogeneous_plane
#print axioms HPC.HO16.ladder_example
#print axioms HPC.HO16.ladder_example_height
#print axioms HPC.HO16.ladder_example_stairwell
-- §6 non-vacuity (HPC/HO16/NonVac197.lean)
#print axioms HPC.HO16.exists_ladder_example
#print axioms HPC.HO16.isLadder_empty
#print axioms HPC.HO16.not_isLadder_even
#print axioms HPC.HO16.ladder_example_alpha2
#print axioms HPC.HO16.ladder_example_alpha3

-- ## Bing–Jones 1959, I (batch 198)
-- order of links along an arc of continua, Theorem 2 (HPC/BJ59/Order.lean)
#print axioms HPC.BJ59.exists_sep_of_disjoint
#print axioms HPC.BJ59.not_meets_both
#print axioms HPC.BJ59.not_meets_adjacent
#print axioms HPC.BJ59.order_core
-- chain operations (HPC/BJ59/ChainOps.lean)
#print axioms HPC.BJ59.chainMergeLast_link_last
#print axioms HPC.BJ59.chainMergeLast_link_of_ne
#print axioms HPC.BJ59.chainMergeLast_link_subset
#print axioms HPC.BJ59.subset_chainMergeLast_link
#print axioms HPC.BJ59.chainAppend_link_left
#print axioms HPC.BJ59.chainAppend_link_right
#print axioms HPC.BJ59.chainAppend_union
#print axioms HPC.BJ59.isEpsChain_chainAppend
-- snake-like arcs of continua, Theorems 2 and 4 (HPC/BJ59/Arc.lean)
#print axioms HPC.BJ59.isPreconnected_preimage_of_monotone'
#print axioms HPC.BJ59.isPreconnected_preimage_Icc
#print axioms HPC.BJ59.isCompact_preimage_Icc
#print axioms HPC.BJ59.theorem2_arc
#print axioms HPC.BJ59.theorem4_explicit
#print axioms HPC.BJ59.theorem4_of_chain
-- gluing, commission §4 steps 2–3 (HPC/BJ59/Glue.lean)
#print axioms HPC.BJ59.exists_half_homeomorph
#print axioms HPC.BJ59.exists_homeomorph_glue
-- Theorem 3 construction (HPC/BJ59/Thm3.lean)
#print axioms HPC.BJ59.dist_lt_of_mem_links
#print axioms HPC.BJ59.union_sub_eq
#print axioms HPC.BJ59.union_reverse
#print axioms HPC.BJ59.theorem3_of_chains
#print axioms HPC.BJ59.theorem3_arc
-- Theorem 3 assembly (HPC/BJ59/Thm3Assembly.lean)
#print axioms HPC.BJ59.isOpen_lowUnion
#print axioms HPC.BJ59.isOpen_highUnion
#print axioms HPC.BJ59.link_subset_lowUnion
#print axioms HPC.BJ59.link_subset_highUnion
#print axioms HPC.BJ59.lowUnion_mono
#print axioms HPC.BJ59.highUnion_anti
#print axioms HPC.BJ59.disjoint_lowUnion_highUnion
#print axioms HPC.BJ59.link_inter_lowUnion_subset
#print axioms HPC.BJ59.link_inter_highUnion_subset
#print axioms HPC.BJ59.isEpsChain_mono
#print axioms HPC.BJ59.isEpsChain_reverse
#print axioms HPC.BJ59.isEpsChain_sub
#print axioms HPC.BJ59.isEpsChain_chainRestrict
#print axioms HPC.BJ59.isEpsChain_chainMergeLast
#print axioms HPC.BJ59.restrict_hne
#print axioms HPC.BJ59.restrict_hc
#print axioms HPC.BJ59.chain_assembly
-- the decomposable case, commission §5 (HPC/BJ59/Decomp.lean)
#print axioms HPC.BJ59.isOpenMap_quotient_mk_of_continuous
#print axioms HPC.BJ59.isPseudoArc_Lset'
#print axioms HPC.BJ59.circle_or_circPAMap_of_decomposable
-- snake-likeness and pseudo-arcs are topological (HPC/BJ59/Transfer.lean)
#print axioms HPC.BJ59.continuous_posFn
#print axioms HPC.BJ59.posFn_nonneg
#print axioms HPC.BJ59.posFn_pos
#print axioms HPC.BJ59.posFn_zero
#print axioms HPC.BJ59.exists_epsMap_of_chain
#print axioms HPC.BJ59.exists_epsMap_of_isSnakeLike
#print axioms HPC.BJ59.isContinuum_of_homeomorph
#print axioms HPC.BJ59.isSnakeLike_of_homeomorph
#print axioms HPC.BJ59.isHereditarilyIndecomposable_of_homeomorph
#print axioms HPC.BJ59.isPseudoArc_of_homeomorph
#print axioms HPC.BJ59.isPseudoArc_subtype_of_image
#print axioms HPC.BJ59.isPseudoArc_image_of_subtype
#print axioms HPC.BJ59.isSnakeLike_univ_of_isSnakeLike
-- homogeneity and uniqueness from BJThm10 (HPC/BJ59/Homog.lean)
#print axioms HPC.BJ59.isHomogeneous_circle'
#print axioms HPC.BJ59.IsCircPAMap.mul_left
#print axioms HPC.BJ59.homeomorph_of_isCircPAMap
#print axioms HPC.BJ59.isHomogeneous_of_isCircPAMap
-- circle, pseudo-arc, circle of pseudo-arcs are distinct (HPC/BJ59/CircleFacts.lean)
#print axioms HPC.BJ59.isContinuum_range_halfC
#print axioms HPC.BJ59.isDecomposableSpace_circle
#print axioms HPC.BJ59.isContinuum_halfSet
#print axioms HPC.BJ59.isDecomposableSpace_of_isCircPAMap
#print axioms HPC.BJ59.continuousAt_arg_circle
#print axioms HPC.BJ59.arg_injective_circle
#print axioms HPC.BJ59.not_isHereditarilyIndecomposable_of_nontrivial_real
#print axioms HPC.BJ59.not_isPseudoArc_of_ne_univ_circle
#print axioms HPC.BJ59.exists_plane_circle
-- halves of a circle of pseudo-arcs (HPC/BJ59/Halves.lean)
#print axioms HPC.BJ59.halfC_zero
#print axioms HPC.BJ59.halfC_one_eq
#print axioms HPC.BJ59.range_halfC_union
#print axioms HPC.BJ59.mem_range_halfC_inter
#print axioms HPC.BJ59.exists_not_mem_range_halfC
#print axioms HPC.BJ59.halfParam_apply
#print axioms HPC.BJ59.isCircleOfPA_iff
#print axioms HPC.BJ59.IsCircPAMap.compactSpace
#print axioms HPC.BJ59.halfMap_eq_iff
#print axioms HPC.BJ59.continuous_halfMap
#print axioms HPC.BJ59.isOpenMap_halfMap
#print axioms HPC.BJ59.surjective_halfMap
#print axioms HPC.BJ59.isClosed_halfSet
#print axioms HPC.BJ59.image_val_halfMap_fibre
#print axioms HPC.BJ59.isContArcPA_halfMap
#print axioms HPC.BJ59.isSnakeLike_halfSet
-- helpers for Theorems 5 and 6 (HPC/BJ59/Thm56.lean)
#print axioms HPC.BJ59.sign_persist
#print axioms HPC.BJ59.isIndecomposable_singleton
#print axioms HPC.BJ59.isArcOfContinua_id
#print axioms HPC.BJ59.isSnakeLike_univ_unitInterval
#print axioms HPC.BJ59.circle_exp_pi_ne_one
-- Theorem 5, repaired (HPC/BJ59/Thm5.lean)
#print axioms HPC.BJ59.chainedAt_union_point
#print axioms HPC.BJ59.limSup_subset_fibre
#print axioms HPC.BJ59.fibre_subset_limSup_union
#print axioms HPC.BJ59.exists_mem_of_mem_limSup
#print axioms HPC.BJ59.theorem5_repaired
-- skeleton §3–§6 statements (HPC/BJ59/BJ59A.lean)
#print axioms HPC.BJ59.isHomogeneous_of_isCircleOfPA
#print axioms HPC.BJ59.homeomorph_of_isCircleOfPA
#print axioms HPC.BJ59.isHomogeneous_circle
#print axioms HPC.BJ59.isPseudoArc_Lset
#print axioms HPC.BJ59.circle_or_circleOfPA_of_decomposable
#print axioms HPC.BJ59.ho16_classification
#print axioms HPC.BJ59.ho16_classification_plane
#print axioms HPC.BJ59.bj_theorem2
#print axioms HPC.BJ59.bj_theorem3
#print axioms HPC.BJ59.bj_theorem4
#print axioms HPC.BJ59.bj_theorem5
#print axioms HPC.BJ59.bj_theorem5_printed_false
#print axioms HPC.BJ59.bj_theorem6
-- §8 non-vacuity (HPC/BJ59/NonVac198.lean)
#print axioms HPC.BJ59.nonvac_arc_id
#print axioms HPC.BJ59.nonvac_bj_theorem2
#print axioms HPC.BJ59.nonvac_bj_theorem3
#print axioms HPC.BJ59.nonvac_bj_theorem4
#print axioms HPC.BJ59.nonvac_bj_theorem6
#print axioms HPC.BJ59.nonvac_plane_circle
#print axioms HPC.BJ59.nonvac_bjThm10_halves
#print axioms HPC.BJ59.nonvac_theorem5_repaired_degenerate
#print axioms HPC.BJ59.bj_theorem5_hyps_fail_id
-- reused shape-changed Theorem 1 (HPC/Plane/Theorem11.lean)
#print axioms HPC.Plane.isUnicoherent_of_isSnakeLike

-- ## Bing–Jones 1959, II (batch 199)
-- atomic maps; atomic arcs are snake-like, skeleton §§2–3 (HPC/BJ59/Atomic.lean)
#print axioms HPC.BJ59.subset_fibre_or_saturated
#print axioms HPC.BJ59.fibre_subset_of_saturated
#print axioms HPC.BJ59.isAtomicMap_id
#print axioms HPC.BJ59.not_isAtomicMap_snd
#print axioms HPC.BJ59.nested_of_common_bound
#print axioms HPC.BJ59.condB_preimage_Icc
#print axioms HPC.BJ59.isPreconnected_preimage_of_fibres
#print axioms HPC.BJ59.isHereditarilyUnicoherent_of_atomic
#print axioms HPC.BJ59.isContinuum_univ_of_fibres
#print axioms HPC.BJ59.isSnakeLike_of_atomic'
#print axioms HPC.BJ59.isSnakeLike_of_atomic
#print axioms HPC.BJ59.nonvac_isSnakeLike_of_atomic'
-- the circle is circle-like (HPC/BJ59/CircleLike.lean)
#print axioms HPC.BJ59.dist_circle_exp_le
#print axioms HPC.BJ59.circle_exp_surjective
#print axioms HPC.BJ59.isConnected_univ_circle
#print axioms HPC.BJ59.circP_eq_iff
#print axioms HPC.BJ59.isOpen_circArc
#print axioms HPC.BJ59.circArc_adjacent
#print axioms HPC.BJ59.circArc_cover
#print axioms HPC.BJ59.diam_circArc_le
#print axioms HPC.BJ59.isCircleLike_circle
#print axioms HPC.BJ59.isCircleLike_univ_of_homeomorph
-- atomic circle maps, Domokos–Prajs Theorem 6.1, skeleton §4 (HPC/BJ59/AtomicCircle.lean)
#print axioms HPC.BJ59.isAtomicMap_halfMap
#print axioms HPC.BJ59.isContArcPA_halfMap'
#print axioms HPC.BJ59.isContArcPA_halfMap_of_atomic
#print axioms HPC.BJ59.isSnakeLike_halfSet_of_atomic
#print axioms HPC.BJ59.IsCircPAMap.isSnakeHalvesMap
#print axioms HPC.BJ59.IsAtomicCircPAMap.isSnakeHalvesMap
#print axioms HPC.BJ59.IsAtomicCircPAMap.mul_left
#print axioms HPC.BJ59.exists_half_homeomorph'
#print axioms HPC.BJ59.exists_homeomorph_glue'
#print axioms HPC.BJ59.homeomorph_of_isSnakeHalvesMap
#print axioms HPC.BJ59.dp22_theorem61
#print axioms HPC.BJ59.homeomorph_of_atomic
#print axioms HPC.BJ59.isHomogeneous_of_atomic
#print axioms HPC.BJ59.isCircleOfPA_of_atomic
-- chains in Bing–Jones's sense (HPC/BJ59/BJChains.lean)
#print axioms HPC.BJ59.adjacent_meet_of_cover
#print axioms HPC.BJ59.exists_bjChain_shrink'
#print axioms HPC.BJ59.exists_bjChain_shrink
-- Theorem 7: folding chains along walks (HPC/BJ59/Thm7Fold.lean)
#print axioms HPC.BJ59.foldChain_link
#print axioms HPC.BJ59.link_subset_foldChain
#print axioms HPC.BJ59.unfoldIdx_lt
#print axioms HPC.BJ59.unfoldIdx_zero
#print axioms HPC.BJ59.unfoldIdx_last
#print axioms HPC.BJ59.unfoldIdx_main
#print axioms HPC.BJ59.unfoldIdx_step
#print axioms HPC.BJ59.unfoldFin_adj
#print axioms HPC.BJ59.unfoldFin_main
#print axioms HPC.BJ59.unfoldMain_adj
#print axioms HPC.BJ59.isPattern_unfold
-- Theorem 7 in a compact pseudo-arc (HPC/BJ59/Thm7Core.lean)
#print axioms HPC.BJ59.composant_univ_eq_jones
#print axioms HPC.BJ59.exists_ne_mem_of_isOpen
#print axioms HPC.BJ59.not_isDecomposableSpace_of_pa
#print axioms HPC.BJ59.mem_composant_univ_self
#print axioms HPC.BJ59.chain_not_mem_of_far
#print axioms HPC.BJ59.exists_closedBall_subset_not_mem
#print axioms HPC.BJ59.exists_not_mem_composant_of_isOpen
#print axioms HPC.BJ59.exists_chain_isFrom
#print axioms HPC.BJ59.exists_follow_pattern
#print axioms HPC.BJ59.bj7_compact_of_le
#print axioms HPC.BJ59.bj7_compact
-- Theorem 7, first sentence (HPC/BJ59/Thm7.lean)
#print axioms HPC.BJ59.bj_theorem7'
-- Theorem 7, second sentence: the collar chain (HPC/BJ59/Thm7Ends.lean)
#print axioms HPC.Chain.linkN_of_lt
#print axioms HPC.Chain.linkN_disj
#print axioms HPC.Chain.isOpen_linkN
#print axioms HPC.BJ59.collar_data
#print axioms HPC.Chain.linkN_reverse
#print axioms HPC.BJ59.exists_collar_chain
#print axioms HPC.BJ59.bufIdx_lt
#print axioms HPC.BJ59.bufIdx_step
-- Theorem 7, second sentence: buffered pattern and assembly (HPC/BJ59/Thm7Ends2.lean)
#print axioms HPC.BJ59.bufIdx_main
#print axioms HPC.BJ59.bufIdx_of_lt_two
#print axioms HPC.BJ59.bufIdx_of_ge
#print axioms HPC.BJ59.bufIdx_two
#print axioms HPC.BJ59.bufIdx_pen
#print axioms HPC.BJ59.bufPat_mid
#print axioms HPC.BJ59.bufPat_pen
#print axioms HPC.BJ59.bufPat_last
#print axioms HPC.BJ59.bufPat_zero
#print axioms HPC.BJ59.bufPat_one
#print axioms HPC.BJ59.bufPat_cases
#print axioms HPC.BJ59.bufPat_lt
#print axioms HPC.BJ59.collarψ_bufPat
#print axioms HPC.BJ59.bufPat_eq_zero
#print axioms HPC.BJ59.bufPat_eq_last
#print axioms HPC.BJ59.bufPat_step
#print axioms HPC.BJ59.bj7_ends_compact_of_le
#print axioms HPC.BJ59.bj7_ends_compact
#print axioms HPC.BJ59.bj_theorem7_ends'
-- skeleton §§5–6 statements (HPC/BJ59/BJ59B.lean)
#print axioms HPC.BJ59.circle_or_atomic_of_decomposable
#print axioms HPC.BJ59.hoCircleLike
#print axioms HPC.BJ59.ho16_classification_atomic
#print axioms HPC.BJ59.ho16_classification₂
#print axioms HPC.BJ59.ho16_classification_plane₂
#print axioms HPC.BJ59.nonvac_atomic
#print axioms HPC.BJ59.bj_theorem7
#print axioms HPC.BJ59.bj_theorem7_ends
#print axioms HPC.BJ59.bj_theorem7_ends_printed_false
#print axioms HPC.BJ59.exists_bjChain_three
#print axioms HPC.BJ59.nonvac_bj_chains
-- §9 non-vacuity (HPC/BJ59/NonVac199.lean)
#print axioms HPC.BJ59.isAtomicMap_const
#print axioms HPC.BJ59.isBJChain_of_le_two
#print axioms HPC.BJ59.not_isBJChain_real3
#print axioms HPC.BJ59.nonvac_bj_theorem7_ends
-- optional items of commission 199 §7: IsBJChain ↔ IsTaut (HPC/BJ59/Taut.lean)
#print axioms HPC.BJ59.infDist'_pos_iff
#print axioms HPC.BJ59.isBJChain_iff_isTaut
-- optional items of commission 199 §7: BJ.5, the general certificate (HPC/BJ59/Thm5Cert.lean)
#print axioms HPC.BJ59.chainMergePenult_link_of_ne
#print axioms HPC.BJ59.chainMergePenult_link_penult
#print axioms HPC.BJ59.subset_chainMergePenult_link
#print axioms HPC.BJ59.chainMergePenult_union
#print axioms HPC.BJ59.closure_last_subset
#print axioms HPC.BJ59.bj_theorem5_printed_false_general
#print axioms HPC.BJ59.mem_real3Chain_clamp
#print axioms HPC.BJ59.nonvac_bj_theorem5_printed_false_general
-- batch-198 @[simp] lemmas omitted from the batch-198 audit (commission 199 §0)
#print axioms HPC.BJ59.chainRestrict_link
#print axioms HPC.BJ59.halfFibreEquiv_apply
#print axioms HPC.BJ59.halfFibreEquiv_symm_apply

-- ## Bing–Jones 1959, III (batch 200)
-- the homeomorphism of pp. 188–189, skeleton §2 (HPC/BJ59/Zigzag.lean)
#print axioms HPC.BJ59.mem_starImage
#print axioms HPC.BJ59.mem_closure_starImage
#print axioms HPC.BJ59.dist_le_of_mem_closure_of_forall
#print axioms HPC.BJ59.le_dist_of_mem_closure_of_forall
#print axioms HPC.BJ59.IsBJChain.adjacent_of_closure
#print axioms HPC.BJ59.dist_lt_of_adjacent
#print axioms HPC.BJ59.starImage_dist_le
#print axioms HPC.BJ59.starImage_succ_subset
#print axioms HPC.BJ59.starImage_antitone
#print axioms HPC.BJ59.le_zero_of_le_mul_tendsto
#print axioms HPC.BJ59.zigzag_homeomorph
#print axioms HPC.BJ59.zigzag_fibre
-- §8 non-vacuity of §2 (HPC/BJ59/NonVac200.lean)
#print axioms HPC.BJ59.starImage_eq_empty_of_notMem
#print axioms HPC.BJ59.starImage_zero
#print axioms HPC.BJ59.starImage_self_id
#print axioms HPC.BJ59.nvN_pos
#print axioms HPC.BJ59.nvN_pos'
#print axioms HPC.BJ59.nvN_succ
#print axioms HPC.BJ59.nvLink_isOpen
#print axioms HPC.BJ59.nvLink_mem
#print axioms HPC.BJ59.nvLink_inter_iff
#print axioms HPC.BJ59.nvChain_cover
#print axioms HPC.BJ59.nvChain_nonempty
#print axioms HPC.BJ59.nvChain_bj
#print axioms HPC.BJ59.nvChain_eps
#print axioms HPC.BJ59.nvK_chainMap
#print axioms HPC.BJ59.nvK_refine
#print axioms HPC.BJ59.nonvac_zigzag
#print axioms HPC.BJ59.tendsto_one_div_two_pow
#print axioms HPC.BJ59.nonvac_zigzag_homeomorph
-- private points; the certificate for BJ.19 (e), skeleton §§3, 6 (HPC/BJ59/Private.lean)
#print axioms HPC.BJ59.exists_privatePoint_interior
#print axioms HPC.BJ59.exists_mem_inter_notMem_finite
#print axioms HPC.BJ59.exists_injective_choice
#print axioms HPC.BJ59.exists_pos_forall_le
#print axioms HPC.BJ59.exists_privatePoint_shrink
#print axioms HPC.BJ59.bj_theorem7_proof_n3
-- Step 1(b), skeleton §3 (HPC/BJ59/Step1b.lean)
#print axioms HPC.BJ59.meets_all_of_meets_ends
#print axioms HPC.BJ59.exists_nhd_step1b
#print axioms HPC.BJ59.bj_step1b
-- tools for Theorem 8 (HPC/BJ59/Thm8Lib.lean)
#print axioms HPC.BJ59.family_meets_all
#print axioms HPC.BJ59.isBJChain_foldChain
#print axioms HPC.BJ59.exists_deep_radius
#print axioms HPC.BJ59.bj_cut
#print axioms HPC.BJ59.exists_deep_sets
-- Theorem 8, skeleton §4 (HPC/BJ59/Thm8.lean)
#print axioms HPC.BJ59.bj_theorem8_ends
#print axioms HPC.BJ59.bj_theorem8_le
#print axioms HPC.BJ59.bj_theorem8
-- corollary to Theorem 8, skeleton §4 (HPC/BJ59/Thm8Cor.lean)
#print axioms HPC.BJ59.walk_core
#print axioms HPC.BJ59.walk_any
#print axioms HPC.BJ59.walk_any'
#print axioms HPC.BJ59.exists_fibre_spread
#print axioms HPC.BJ59.bj_theorem8_cor
-- tools for Theorem 9: classes and consolidation (HPC/BJ59/Thm9Class.lean)
#print axioms HPC.BJ59.mem_linkN_iff
#print axioms HPC.BJ59.mem_linkN_of_mem
#print axioms HPC.BJ59.lt_of_mem_linkN
#print axioms HPC.BJ59.linkN_adj
#print axioms HPC.BJ59.IsBJChain.exists_uniform
#print axioms HPC.BJ59.chain_of_classes
#print axioms HPC.BJ59.exists_consolidation
-- Theorem 9: the chain D′ (HPC/BJ59/Thm9D.lean)
#print axioms HPC.BJ59.exists_dist_ge_of_notMem_closure
#print axioms HPC.BJ59.exists_private_radius
#print axioms HPC.BJ59.exists_fine_bjChain
#print axioms HPC.BJ59.dist_lt_of_mem_link
#print axioms HPC.BJ59.bj9_Dside
-- Theorem 9: the chain E′ (HPC/BJ59/Thm9E.lean)
#print axioms HPC.BJ59.closure_biUnion_links
#print axioms HPC.BJ59.bj9_Eside
-- Theorem 9: the two simplifications, skeleton §5 (HPC/BJ59/Thm9Base.lean)
#print axioms HPC.BJ59.bj9_core
#print axioms HPC.BJ59.bj9_base
-- Theorem 9, skeleton §5 (HPC/BJ59/Thm9.lean)
#print axioms HPC.BJ59.isEpsChain_of_refine
#print axioms HPC.BJ59.IsChainMap.comp'
#print axioms HPC.BJ59.bj9_half
#print axioms HPC.BJ59.meets_of_private
#print axioms HPC.BJ59.bj9_step
#print axioms HPC.BJ59.bj_theorem9
-- Domokos–Prajs Theorem 6.1, skeleton §6 (HPC/BJ59/DP61.lean)
#print axioms HPC.BJ59.IsAtomicCircPAMap.comp_homeomorph
#print axioms HPC.BJ59.exists_atomic_of_plane_isCircleOfPA
#print axioms HPC.BJ59.dp22_theorem61_iff
-- §8 non-vacuity of §§3, 5, 6 (HPC/BJ59/NonVac200b.lean)
#print axioms HPC.BJ59.nonvac_privatePoint_shrink
#print axioms HPC.BJ59.nonvac_privatePoint_interior
#print axioms HPC.BJ59.nonvac_step1b
#print axioms HPC.BJ59.nonvac_bj9
#print axioms HPC.BJ59.nonvac_bj9_one
#print axioms HPC.BJ59.nonvac_bj_theorem7_proof_n3
#print axioms HPC.BJ59.nonvac_dp22_theorem61
#print axioms HPC.BJ59.allowed_small
#print axioms HPC.BJ59.nonvac_bj9Stage
-- ## Bing–Jones 1959, IV (batch 201)
-- §2 conditions and §3 tools (HPC/BJ59/Thm10Defs.lean)
#print axioms HPC.BJ59.exists_point_only_of_minimal
#print axioms HPC.BJ59.exists_abs_le_one_of_steps
#print axioms HPC.BJ59.adjacent_of_properCover
#print axioms HPC.BJ59.isFibreFine_of_isEpsChain
-- library lemmas (HPC/BJ59/Thm10Lib.lean)
#print axioms HPC.BJ59.dist_lt_of_mem_closure_link
#print axioms HPC.BJ59.dist_lt_of_mem_closure_link'
#print axioms HPC.BJ59.card_filter_lt_iff_of_downward
#print axioms HPC.BJ59.card_filter_le
#print axioms HPC.BJ59.exists_tube
#print axioms HPC.BJ59.exists_meets_near
#print axioms HPC.BJ59.IsEpsChain.of_subset
#print axioms HPC.BJ59.exists_fine_bjChain_private
-- runs (HPC/BJ59/Thm10Runs.lean)
#print axioms HPC.BJ59.exists_minimal_run
#print axioms HPC.BJ59.exists_run_meeting
#print axioms HPC.BJ59.exists_eq_of_steps
#print axioms HPC.BJ59.chainMap_ivt
-- Step 2(b), skeleton §3 (HPC/BJ59/Thm10Pattern.lean)
#print axioms HPC.BJ59.exists_pattern
#print axioms HPC.BJ59.exists_pattern_skeleton
-- windows, skeleton §3 (HPC/BJ59/Thm10Window.lean)
#print axioms HPC.BJ59.winInv_mem
#print axioms HPC.BJ59.continuous_winInv
#print axioms HPC.BJ59.continuous_winScale
#print axioms HPC.BJ59.winScale_eq_iff
#print axioms HPC.BJ59.winScale_winInv
#print axioms HPC.BJ59.window_transfer
#print axioms HPC.BJ59.bj_theorem5_window_aux
#print axioms HPC.BJ59.bj_theorem5_window
#print axioms HPC.BJ59.exists_two_points_of_open
#print axioms HPC.BJ59.exists_window_set
-- the corollary to Theorem 8 on a sub-arc, skeleton §3 (HPC/BJ59/Thm10Sub.lean)
#print axioms HPC.BJ59.exists_chain_subtype
#print axioms HPC.BJ59.isEpsChain_subtype
#print axioms HPC.BJ59.zigN_lt
#print axioms HPC.BJ59.mod_eq_of_decomp
#print axioms HPC.BJ59.zigN_step
#print axioms HPC.BJ59.zigN_hits
#print axioms HPC.BJ59.bj_theorem8_cor_sub_three
#print axioms HPC.BJ59.bj_theorem8_cor_sub_one
#print axioms HPC.BJ59.bj_theorem8_cor_sub
-- gluing, §4 (HPC/BJ59/Thm10Glue.lean)
#print axioms HPC.BJ59.unitInterval_mem_Icc_iff
#print axioms HPC.BJ59.unitInterval_mem_Ioo_iff
#print axioms HPC.BJ59.bj_glue
-- the pieces of the step, §4 (HPC/BJ59/Thm10Pieces.lean)
#print axioms HPC.BJ59.exists_tau_run
#print axioms HPC.BJ59.exists_tau_incl
#print axioms HPC.BJ59.exists_subarc_piece
#print axioms HPC.BJ59.exists_end_piece
-- the step, skeleton §4 (HPC/BJ59/Thm10Step.lean)
#print axioms HPC.BJ59.bj_step
-- the induction, skeleton §5 (HPC/BJ59/Thm10Induct.lean)
#print axioms HPC.BJ59.IsEpsChain.mono'
#print axioms HPC.BJ59.BJStage.exists_next
#print axioms HPC.BJ59.BJStage.exists_init
#print axioms HPC.BJ59.bjThm10_of_step
-- Theorem 10 and the classification, skeleton §5 (HPC/BJ59/BJ59D.lean)
#print axioms HPC.BJ59.bjThm10
#print axioms HPC.BJ59.ho16_classification_atomic'
#print axioms HPC.BJ59.isHomogeneous_of_isCircleOfPA'
#print axioms HPC.BJ59.homeomorph_of_isCircleOfPA'
#print axioms HPC.BJ59.ho16_classification₃
#print axioms HPC.BJ59.ho16_classification_plane₃
-- §7 non-vacuity (HPC/BJ59/NonVac201.lean)
#print axioms HPC.BJ59.closure_nvLink_subset
#print axioms HPC.BJ59.nvChain_private
#print axioms HPC.BJ59.nonvac_conditions
#print axioms HPC.BJ59.nonvac_conditions_one
#print axioms HPC.BJ59.nonvac_conditions_zero
-- §7 non-vacuity of the tools (HPC/BJ59/NonVac201b.lean)
#print axioms HPC.BJ59.zero_notMem_nvLink
#print axioms HPC.BJ59.one_notMem_nvLink
#print axioms HPC.BJ59.nonvac_point_only
#print axioms HPC.BJ59.nonvac_adjacent
#print axioms HPC.BJ59.nonvac_fibreFine
#print axioms HPC.BJ59.nonvac_pattern

-- ## Bing–Jones 1959, V (batch 202)
-- the sweep lemma, §4.1 (HPC/BJ59/Sweep.lean)
#print axioms HPC.BJ59.PatCrookedOnZ.toNat
#print axioms HPC.BJ59.PatCrookedOn.toZ
#print axioms HPC.BJ59.PatCrookedOnZ.extend
#print axioms HPC.BJ59.exists_eq_of_lipZ
#print axioms HPC.BJ59.exists_last_le
#print axioms HPC.BJ59.exists_first_ge
#print axioms HPC.BJ59.exists_first_growth
#print axioms HPC.BJ59.sweep_lemma
-- sweep patterns, skeleton §4 (HPC/BJ59/SweepPattern.lean)
#print axioms HPC.BJ59.sweepQ_eq
#print axioms HPC.BJ59.swT_even
#print axioms HPC.BJ59.swT_odd
#print axioms HPC.BJ59.swB_even
#print axioms HPC.BJ59.swB_odd
#print axioms HPC.BJ59.swD_even
#print axioms HPC.BJ59.swD_odd
#print axioms HPC.BJ59.swD_eq
#print axioms HPC.BJ59.swK_mul
#print axioms HPC.BJ59.swK_eq
#print axioms HPC.BJ59.swK_pos
#print axioms HPC.BJ59.S_dvd_swK
#print axioms HPC.BJ59.sweepL_ge
#print axioms HPC.BJ59.stut_zero'
#print axioms HPC.BJ59.stut_last
#print axioms HPC.BJ59.sweep_decomp
#print axioms HPC.BJ59.sweepX_block
#print axioms HPC.BJ59.swVal_zero
#print axioms HPC.BJ59.swVal_last
#print axioms HPC.BJ59.swVal_range
#print axioms HPC.BJ59.sw_win_up
#print axioms HPC.BJ59.sw_win_down
#print axioms HPC.BJ59.swVal_junction
#print axioms HPC.BJ59.swT_add2
#print axioms HPC.BJ59.swB_add2
#print axioms HPC.BJ59.swD_add2
#print axioms HPC.BJ59.swVal_add6
#print axioms HPC.BJ59.slow_of_factor
#print axioms HPC.BJ59.sweepL_pos
#print axioms HPC.BJ59.sweepX_period
#print axioms HPC.BJ59.sweepX_step
#print axioms HPC.BJ59.sweepX_factor
#print axioms HPC.BJ59.sweepX_slow
#print axioms HPC.BJ59.sweepX_range
#print axioms HPC.BJ59.sw_bounds
#print axioms HPC.BJ59.sweepX_nest
#print axioms HPC.BJ59.sweepX_surv
#print axioms HPC.BJ59.sweepX_junction
#print axioms HPC.BJ59.sweepX_block_crooked
#print axioms HPC.BJ59.sweepX_crook
#print axioms HPC.BJ59.exists_sweepPattern
-- circular descriptions, skeleton §§2–3: (3.1), (3.2), (3.5) (HPC/BJ59/CircDescr.lean)
#print axioms HPC.BJ59.CircDescr.N_pos
#print axioms HPC.BJ59.CircDescr.N_pos'
#print axioms HPC.BJ59.CircDescr.lam_pos
#print axioms HPC.BJ59.CircDescr.inv_N_le
#print axioms HPC.BJ59.CircDescr.L_add_mul
#print axioms HPC.BJ59.CircDescr.c_add_mul
#print axioms HPC.BJ59.CircDescr.c_succ
#print axioms HPC.BJ59.CircDescr.pat_add_mul
#print axioms HPC.BJ59.CircDescr.L_bdd
#print axioms HPC.BJ59.CircDescr.L_nonempty
#print axioms HPC.BJ59.CircDescr.meet_succ
#print axioms HPC.BJ59.CircDescr.mul_cases
#print axioms HPC.BJ59.CircDescr.meet_small
#print axioms HPC.BJ59.CircDescr.L_succ_subset
#print axioms HPC.BJ59.CircDescr.U_eq_fin
#print axioms HPC.BJ59.CircDescr.U_succ_subset
#print axioms HPC.BJ59.CircDescr.U_anti
#print axioms HPC.BJ59.CircDescr.closure_U_succ
#print axioms HPC.BJ59.CircDescr.U_subset_K
#print axioms HPC.BJ59.CircDescr.isCompact_closure_U
#print axioms HPC.BJ59.CircDescr.M_eq
#print axioms HPC.BJ59.CircDescr.M_subset_U
#print axioms HPC.BJ59.CircDescr.isCompact_M
#print axioms HPC.BJ59.CircDescr.isPreconnected_U
#print axioms HPC.BJ59.CircDescr.U_nonempty
#print axioms HPC.BJ59.CircDescr.M_nonempty
#print axioms HPC.BJ59.CircDescr.isConnected_M
#print axioms HPC.BJ59.CircDescr.exists_mem_nested
#print axioms HPC.BJ59.CircDescr.mem_M_of_nested
#print axioms HPC.BJ59.CircDescr.mem_M_of_forall_ge
#print axioms HPC.BJ59.CircDescr.exists_pat_pair
#print axioms HPC.BJ59.CircDescr.inter_M_nonempty
#print axioms HPC.BJ59.CircDescr.fib_eq
#print axioms HPC.BJ59.CircDescr.mem_fib_iff
#print axioms HPC.BJ59.CircDescr.down
#print axioms HPC.BJ59.CircDescr.down_iter
#print axioms HPC.BJ59.CircDescr.fib_subset_M
#print axioms HPC.BJ59.CircDescr.fib_meets
-- runs and fibres, §3 (3.8)–(3.10) (HPC/BJ59/CircFibre.lean)
#print axioms HPC.BJ59.CircDescr.run_iff
#print axioms HPC.BJ59.CircDescr.run_len
#print axioms HPC.BJ59.CircDescr.runN_eq
#print axioms HPC.BJ59.CircDescr.runChain_link
#print axioms HPC.BJ59.CircDescr.mem_runChain_union
#print axioms HPC.BJ59.CircDescr.fib_eq_iInter
#print axioms HPC.BJ59.CircDescr.fib_subset_union
#print axioms HPC.BJ59.CircDescr.pat_mem_run
#print axioms HPC.BJ59.CircDescr.tight_run
#print axioms HPC.BJ59.CircDescr.runChain_crooked
#print axioms HPC.BJ59.CircDescr.exists_two
#print axioms HPC.BJ59.CircDescr.fib_nonempty
#print axioms HPC.BJ59.CircDescr.fib_nontrivial
#print axioms HPC.BJ59.CircDescr.closure_run_succ
#print axioms HPC.BJ59.CircDescr.runChain_union_subset_K
#print axioms HPC.BJ59.CircDescr.isPreconnected_runChain_union
#print axioms HPC.BJ59.CircDescr.isContinuum_fib
#print axioms HPC.BJ59.CircDescr.ε_nonneg
#print axioms HPC.BJ59.CircDescr.isSnakeLike_fib
#print axioms HPC.BJ59.CircDescr.isHereditarilyIndecomposable_fib
#print axioms HPC.BJ59.CircDescr.isPseudoArc_fib
-- the base map and the recognition theorem, skeleton §3 (HPC/BJ59/CircMap.lean)
#print axioms HPC.BJ59.isOpenMap_circP_one
#print axioms HPC.BJ59.dist_circP_one_le
#print axioms HPC.BJ59.CircDescr.lam_lt_one
#print axioms HPC.BJ59.CircDescr.near_of_link
#print axioms HPC.BJ59.CircDescr.small_tendsto
#print axioms HPC.BJ59.CircDescr.int_eq_of_near
#print axioms HPC.BJ59.CircDescr.eq_add_int_of_mem
#print axioms HPC.BJ59.CircDescr.fib_add_int
#print axioms HPC.BJ59.CircDescr.isClosed_parSet
#print axioms HPC.BJ59.CircDescr.exists_fib
#print axioms HPC.BJ59.CircDescr.yOf_mem
#print axioms HPC.BJ59.CircDescr.fmap_eq_iff
#print axioms HPC.BJ59.CircDescr.continuous_fmap
#print axioms HPC.BJ59.CircDescr.surjective_fmap
#print axioms HPC.BJ59.CircDescr.isOpenMap_fmap
#print axioms HPC.BJ59.CircDescr.isCircleLike_M
#print axioms HPC.BJ59.CircDescr.isCircleOfPA
-- joint positions of lifted patterns, §5 (HPC/BJ59/CircJoints.lean)
#print axioms HPC.BJ59.CircJ.dv_shift
#print axioms HPC.BJ59.CircJ.P_shift
#print axioms HPC.BJ59.CircJ.abs_sub_le_of_step
#print axioms HPC.BJ59.CircJ.wval_bounds
#print axioms HPC.BJ59.CircJ.xw_val
#print axioms HPC.BJ59.CircJ.xe_xw
#print axioms HPC.BJ59.CircJ.xw_unitSteps
#print axioms HPC.BJ59.CircJ.xw_slow
#print axioms HPC.BJ59.CircJ.x_add_mul
#print axioms HPC.BJ59.CircJ.x_add_D
#print axioms HPC.BJ59.CircJ.jointZ_add
#print axioms HPC.BJ59.CircJ.jointZ_succ
#print axioms HPC.BJ59.CircJ.link_facts_Z
-- ramps and the shear on the universal cover, §5 (HPC/BJ59/CircCover.lean)
#print axioms HPC.BJ59.Ramp.continuous_θ0
#print axioms HPC.BJ59.Ramp.θ0_mem
#print axioms HPC.BJ59.Ramp.θ0_of_le
#print axioms HPC.BJ59.Ramp.θ0_of_ge
#print axioms HPC.BJ59.Ramp.piece_spec
#print axioms HPC.BJ59.Ramp.piece_eq
#print axioms HPC.BJ59.Ramp.F_succ
#print axioms HPC.BJ59.Ramp.phat_eq
#print axioms HPC.BJ59.Ramp.continuous_F
#print axioms HPC.BJ59.Ramp.continuous_phat
#print axioms HPC.BJ59.Ramp.F_mem
#print axioms HPC.BJ59.Ramp.phat_mem_link
#print axioms HPC.BJ59.Ramp.phat_zone
#print axioms HPC.BJ59.Ramp.phat_mem
#print axioms HPC.BJ59.Ramp.phat_add
#print axioms HPC.BJ59.cover_apply
#print axioms HPC.BJ59.cover_symm_apply
#print axioms HPC.BJ59.cover_add
#print axioms HPC.BJ59.cover_symm_add
-- descent to the plane, §5 (HPC/BJ59/CircDescent.lean)
#print axioms HPC.BJ59.Descent.continuous_E
#print axioms HPC.BJ59.Descent.E_ne_zero
#print axioms HPC.BJ59.Descent.norm_E
#print axioms HPC.BJ59.Descent.E_lift
#print axioms HPC.BJ59.Descent.E_lift'
#print axioms HPC.BJ59.Descent.E_add_int
#print axioms HPC.BJ59.Descent.E_eq_imp
#print axioms HPC.BJ59.Descent.continuousAt_lift
#print axioms HPC.BJ59.Descent.continuousAt_lift'
#print axioms HPC.BJ59.Descent.G_add_int
#print axioms HPC.BJ59.Descent.desc_E
#print axioms HPC.BJ59.Descent.desc_of_E
#print axioms HPC.BJ59.Descent.continuousAt_desc
#print axioms HPC.BJ59.Descent.desc_zero
#print axioms HPC.BJ59.Descent.continuousAt_desc_zero
#print axioms HPC.BJ59.Descent.continuous_desc
#print axioms HPC.BJ59.Descent.descHomeo_E
-- the standard circular chains, skeleton §5 (HPC/BJ59/CircStd.lean)
#print axioms HPC.BJ59.CircStd.cpx_apply
#print axioms HPC.BJ59.CircStd.circExp_eq
#print axioms HPC.BJ59.CircStd.continuous_circExp
#print axioms HPC.BJ59.CircStd.circExp_add_int
#print axioms HPC.BJ59.CircStd.circExp_eq_imp
#print axioms HPC.BJ59.CircStd.isOpenMap_circExp
#print axioms HPC.BJ59.CircStd.isOpen_stdRectZ
#print axioms HPC.BJ59.CircStd.closure_stdRectZ
#print axioms HPC.BJ59.CircStd.isPreconnected_stdRectZ
#print axioms HPC.BJ59.CircStd.isOpen_stdCircLink
#print axioms HPC.BJ59.CircStd.isPreconnected_stdCircLink
#print axioms HPC.BJ59.CircStd.stdCircLink_periodic
#print axioms HPC.BJ59.CircStd.stdCircLink_meet_iff'
#print axioms HPC.BJ59.stdCircLink_meet_iff
-- the circular planar step, skeleton §5 (HPC/BJ59/CircStep.lean)
#print axioms HPC.BJ59.CircStepAux.small_images
#print axioms HPC.BJ59.CircStepAux.phat_height
#print axioms HPC.BJ59.circ_step
-- the assembly, §6 (HPC/BJ59/CircPlane.lean)
#print axioms HPC.BJ59.CircPlane.eta_pos
#print axioms HPC.BJ59.CircPlane.stepS_ge
#print axioms HPC.BJ59.CircPlane.stepS_one
#print axioms HPC.BJ59.CircPlane.stepX_spec
#print axioms HPC.BJ59.CircPlane.stepQ_eq
#print axioms HPC.BJ59.CircPlane.stepQ_ge
#print axioms HPC.BJ59.CircPlane.stepQ_half
#print axioms HPC.BJ59.CircPlane.stepψ_spec
#print axioms HPC.BJ59.CircPlane.N_ne
#print axioms HPC.BJ59.CircPlane.N_pos
#print axioms HPC.BJ59.CircPlane.circExp_mem_ball
#print axioms HPC.BJ59.CircPlane.link_zero_sub
#print axioms HPC.BJ59.CircPlane.zone_zero_sub
#print axioms HPC.BJ59.CircPlane.link_sub_zero
#print axioms HPC.BJ59.CircPlane.isBounded_zone
#print axioms HPC.BJ59.CircPlane.two_exp_lt
#print axioms HPC.BJ59.CircPlane.zone_diam
#print axioms HPC.BJ59.CircPlane.link_diam
#print axioms HPC.BJ59.CircPlane.N_ge
#print axioms HPC.BJ59.CircPlane.lam_succ
#print axioms HPC.BJ59.CircPlane.lam_mul
#print axioms HPC.BJ59.CircPlane.lam_tendsto
#print axioms HPC.BJ59.CircPlane.Q_pos
#print axioms HPC.BJ59.CircPlane.N_succ_real
#print axioms HPC.BJ59.CircPlane.o_succ
#print axioms HPC.BJ59.CircPlane.pat_period
#print axioms HPC.BJ59.CircPlane.arcNest
#print axioms HPC.BJ59.CircPlane.surv
#print axioms HPC.BJ59.CircPlane.crook
-- the plane example and the classification, skeleton §6 (HPC/BJ59/BJ59E.lean)
#print axioms HPC.BJ59.exists_circDescr_plane
#print axioms HPC.BJ59.bjPlaneExample
#print axioms HPC.BJ59.ho16_classification₄
#print axioms HPC.BJ59.ho16_classification_plane₄
#print axioms HPC.BJ59.dp22_theorem61'
#print axioms HPC.BJ59.dp22_theorem61_iff'
#print axioms HPC.BJ59.hoCircleLike'
-- §8 non-vacuity (HPC/BJ59/NonVac202.lean)
#print axioms HPC.BJ59.CircDescr.N_tendsto
#print axioms HPC.BJ59.sweepX_crookedZ
#print axioms HPC.BJ59.sweep_event
#print axioms HPC.BJ59.nonvac_sweep_single
#print axioms HPC.BJ59.nonvac_sweep_two_events
#print axioms HPC.BJ59.circExp_zero
#print axioms HPC.BJ59.not_stdCircLink_meet_iff_zero
#print axioms HPC.BJ59.stdCircLink_meet_small
#print axioms HPC.BJ59.nonvac_circ_step_hyps
-- §8 non-degenerate inputs for the batch-201 statements (HPC/BJ59/NonVac202b.lean)
#print axioms HPC.BJ59.exists_snakeArcPA
#print axioms HPC.BJ59.nonvac_bjThm10
#print axioms HPC.BJ59.nonvac_bjStep
#print axioms HPC.BJ59.nonvac_bj_theorem8_cor_sub
#print axioms HPC.BJ59.nonvac_bj_theorem5_window
-- §4.1 the sweep lemma with at most three events (HPC/BJ59/Sweep3.lean)
#print axioms HPC.BJ59.sweep_window_case2b
#print axioms HPC.BJ59.sweep_lemma3
-- §8 the sweep lemma on exactly three events; a sweep walk with four events that is not crooked
-- (HPC/BJ59/NonVac202c.lean)
#print axioms HPC.BJ59.nonvac_sweep_three_events
#print axioms HPC.BJ59.Cert4.cert4_step
#print axioms HPC.BJ59.Cert4.cert4_range
#print axioms HPC.BJ59.Cert4.cert4_end
#print axioms HPC.BJ59.Cert4.cert4_crook
#print axioms HPC.BJ59.Cert4.cert4_alt
#print axioms HPC.BJ59.Cert4.cert4_win_up
#print axioms HPC.BJ59.Cert4.cert4_win_down
#print axioms HPC.BJ59.Cert4.cert4_events
#print axioms HPC.BJ59.Cert4.cert4_not_crooked
#print axioms HPC.BJ59.nonvac_sweep_four_events
-- ## Bing 1951 (Duke), Theorem 6 by the compact Janiszewski theorem
#print axioms HPC.Plane.janiszewski_polygonal_of_compact
#print axioms HPC.Plane.exists_theta_point_open
#print axioms HPC.Plane.compFamily_no_circular_open
#print axioms HPC.Plane.treeChain_of_cover_open
#print axioms HPC.Plane.theorem6_direct
-- ## Open targets (class C)
-- (none since batch 132: `fugate_cor1` proved, `HPC/Plane/Ingram68.lean`)

-- ## Consequences of open targets
-- (none since batch 115: `theorem15` depended on `theorem14`, now proved)
