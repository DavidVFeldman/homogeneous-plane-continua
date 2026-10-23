import HPC
import HPC.Fold.ExitReachFWitness

/-!
# Axiom audit

`#print axioms` for the main list of the repository, grouped by source. The output is
`axioms.txt`; regenerate it with `lake env lean Axioms.lean > axioms.txt` after `lake build HPC`.
Every declaration outside the two groups of open targets must show exactly
`[propext, Classical.choice, Quot.sound]` or a subset of it; `sorryAx` appears exactly in the
groups `Open targets` and `Consequences of open targets`.
-/

-- ## Bing 1948
-- Theorem 1
#print axioms HPC.Chain.isCrookedIn'_of_isConsolidationOf
-- Theorem 2
#print axioms HPC.Chain.isCrookedIn'_of_refines
-- Theorem 3
#print axioms HPC.Fold.theorem3
-- Theorem 4
#print axioms HPC.Fold.theorem4
#print axioms HPC.Fold.theorem4_pair
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
-- existence of a pseudo-arc in the plane
#print axioms HPC.Plane.pseudoArc_exists

-- ## Bing 1951 (Duke)
-- Theorem 1
#print axioms HPC.Plane.theorem1_snake
-- Theorem 4
#print axioms HPC.Plane.theorem4
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
-- Theorem 12, A => B
#print axioms HPC.Plane.condB_of_condA
-- Theorem 13, necessity
#print axioms HPC.Plane.condB_of_endPoint
-- Theorem 13, sufficiency
#print axioms HPC.Plane.endPoint_of_condA
-- Theorem 14
#print axioms HPC.Plane.theorem14_1951
-- Theorem 15
#print axioms HPC.Plane.theorem15_1951
#print axioms HPC.Plane.isPseudoArc_iff_endPoints
#print axioms HPC.Plane.exists_two_endElts
#print axioms HPC.Plane.organ_isSnakeLike

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

-- ## Fugate 1966
#print axioms HPC.Plane.fugate_lemma1
#print axioms HPC.Plane.fugate_lemma2'
#print axioms HPC.Plane.fugate_lemma4
-- class B rename
#print axioms HPC.Plane.fugate_theorem1_sufficiency'
-- class B rename
#print axioms HPC.Plane.fugate_theorem1'
#print axioms HPC.Plane.fugate_cor1_iff
-- class B rename
#print axioms HPC.Plane.fugate_cor2'
-- class B rename
#print axioms HPC.Plane.isTerminalSub_iff_irreducible'

-- ## Nadler
#print axioms HPC.Plane.exists_two_nonCutPoints
#print axioms HPC.Plane.not_subset_of_nonCutPoints
#print axioms HPC.Plane.sorgenfrey
#print axioms HPC.Plane.irreducible_iff_not_isTriod
-- class B rename
#print axioms HPC.Plane.sorgenfrey_irreducible_of_atriodic_hu
#print axioms HPC.Plane.isHereditarilyUnicoherent_union
#print axioms HPC.Plane.isUnicoherent_univ_of_contraction

-- ## Refutations (ledger certificates)
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

-- ## Open targets (class C)
#print axioms HPC.Fold.theorem3_end
#print axioms HPC.Description.covering_step
#print axioms HPC.Description.theorem14
#print axioms HPC.Plane.exists_tame_chain_near
#print axioms HPC.Plane.isContPt_congr
#print axioms HPC.Plane.subcontinuum_of_isContPt
#print axioms HPC.Plane.theorem11_1951_of_T10'
#print axioms HPC.Plane.fugate_cor1

-- ## Consequences of open targets
-- from theorem14
#print axioms HPC.Description.theorem15
-- from covering_step
#print axioms HPC.Description.exists_description_covering
-- from exists_tame_chain_near
#print axioms HPC.Plane.dense_pseudoArcs
-- from exists_tame_chain_near
#print axioms HPC.Plane.theorem2_HIC
