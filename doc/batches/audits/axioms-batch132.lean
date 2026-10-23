import HPC

-- batch 132 audit: every theorem of HPC/Plane/Fugate66Cor1Proof.lean, Ingram68Core.lean,
-- Ingram68Star.lean and Ingram68.lean, with `fugate_cor1` and `fugateU_holds`

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
