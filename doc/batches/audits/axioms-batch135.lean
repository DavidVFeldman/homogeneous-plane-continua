import HPC

-- batch 135 audit: every theorem of HPC/Jones/*.lean (Jones 1948, 1951)

-- `HPC/Jones/Defs.lean`
#print axioms HPC.Jones.not_aposAt_self
#print axioms HPC.Jones.AposAt.ne
#print axioms HPC.Jones.aposAt_of_mem
#print axioms HPC.Jones.isOpen_setOf_aposAt
#print axioms HPC.Jones.isClosed_setOf_not_aposAt
#print axioms HPC.Jones.isOpen_aposAt_left
#print axioms HPC.Jones.isOpen_aposAt_right
#print axioms HPC.Jones.isClosed_not_aposAt_left
#print axioms HPC.Jones.isClosed_not_aposAt_right
#print axioms HPC.Jones.isContinuum_image_homeomorph
#print axioms HPC.Jones.AposAt.image
#print axioms HPC.Jones.aposAt_homeomorph_iff
#print axioms HPC.Jones.subset_of_isPreconnected_of_closed_cover
#print axioms HPC.Jones.isClosed_connectedComponentIn'
#print axioms HPC.Jones.exists_open_subset_component
#print axioms HPC.Jones.isClosed_fst_image
#print axioms HPC.Jones.isClosed_snd_image
#print axioms HPC.Jones.isClosed_exists_not_aposAt_right
#print axioms HPC.Jones.isClosed_exists_not_aposAt_left
#print axioms HPC.Jones.exists_finite_apos_cover
#print axioms HPC.Jones.exists_nhd_uniform_apos
#print axioms HPC.Jones.exists_radius_uniform_apos
#print axioms HPC.Jones.aposAt_of_frontier
#print axioms HPC.Jones.exists_ball_subset_of_closed_cover
#print axioms HPC.Jones.exists_dist_eq_half
#print axioms HPC.Jones.exists_ne_ne

-- `HPC/Jones/Basic.lean`
#print axioms HPC.Jones.isContinuum_univ
#print axioms HPC.Jones.isDecomposableSpace_iff_not_isIndecomposable
#print axioms HPC.Jones.composant_eq_composant_univ
#print axioms HPC.Jones.theorem1
#print axioms HPC.Jones.setOf_theorem2_eq
#print axioms HPC.Jones.setOf_theorem3_eq
#print axioms HPC.Jones.theorem2
#print axioms HPC.Jones.theorem3
#print axioms HPC.Jones.theorem4
#print axioms HPC.Jones.theorem0
#print axioms HPC.Jones.theorem5
#print axioms HPC.Jones.isContinuum_prod_cross
#print axioms HPC.Jones.aposAt_prod_of_fst_ne
#print axioms HPC.Jones.aposAt_prod_of_snd_ne
#print axioms HPC.Jones.theorem7
#print axioms HPC.Jones.aposAt_of_decomposition
#print axioms HPC.Jones.theorem8
#print axioms HPC.Jones.theorem9
#print axioms HPC.Jones.theorem10
#print axioms HPC.Jones.theorem10_printed_iff
#print axioms HPC.Jones.isDecomposableSpace_unitInterval
#print axioms HPC.Jones.not_theorem10_printed_unitInterval

-- `HPC/Jones/Theorem6.lean`
#print axioms HPC.Jones.Thm6Inv.nonempty_right
#print axioms HPC.Jones.theorem6_step
#print axioms HPC.Jones.theorem6
#print axioms HPC.Jones.not_theorem6_printed

-- `HPC/Jones/Theorem13Aux.lean`
#print axioms HPC.Jones.exists_mem_dist_eq
#print axioms HPC.Jones.exists_split_of_not_aposAt
#print axioms HPC.Jones.separation_nested

-- `HPC/Jones/Theorem13.lean`
#print axioms HPC.Jones.T13J.rad_lt
#print axioms HPC.Jones.T13J.rad_mono
#print axioms HPC.Jones.T13J.rad_strictMono
#print axioms HPC.Jones.T13J.rad_pos
#print axioms HPC.Jones.T13J.rad_lt_eps
#print axioms HPC.Jones.T13J.lo_ge
#print axioms HPC.Jones.T13J.isOpen_ring
#print axioms HPC.Jones.T13J.isClosed_outer
#print axioms HPC.Jones.T13J.Good.W_inter_open
#print axioms HPC.Jones.T13J.build
#print axioms HPC.Jones.T13J.exists_apos_point
#print axioms HPC.Jones.T13J.outer_subset
#print axioms HPC.Jones.T13J.ring_subset
#print axioms HPC.Jones.T13J.disjoint_ring_outer
#print axioms HPC.Jones.T13J.init
#print axioms HPC.Jones.T13J.step
#print axioms HPC.Jones.T13J.core
#print axioms HPC.Jones.theorem13

-- `HPC/Jones/CutPoints.lean`
#print axioms HPC.Jones.theorem11
#print axioms HPC.Jones.exists_ne_of_not_aposyndeticAt
#print axioms HPC.Jones.theorem12
#print axioms HPC.Jones.totallyNonApos_exists_weakCutPoint
#print axioms HPC.Jones.theorem14
#print axioms HPC.Jones.theorem15
#print axioms HPC.Jones.theorem15_cor
#print axioms HPC.Jones.nontrivial_of_isWeakCutPoint
#print axioms HPC.Jones.theorem16
#print axioms HPC.Jones.theorem17
#print axioms HPC.Jones.theorem17_cor
#print axioms HPC.Jones.theorem18
#print axioms HPC.Jones.theorem19

-- `HPC/Jones/Jones51.lean`
#print axioms HPC.Jones.aposSet_eq
#print axioms HPC.Jones.isOpen_aposSet
#print axioms HPC.Jones.isHomogeneous_iff_isPretransitive
#print axioms HPC.Jones.aposSet_homeomorph
#print axioms HPC.Jones.isOpen_setOf_subset_aposSet
#print axioms HPC.Jones.exists_lsc_strictMono_aposSet
#print axioms HPC.Jones.jones51_lemma
