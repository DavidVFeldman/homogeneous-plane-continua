import HPC.PseudoArc.Lehner

-- Batch 114: `#print axioms` for every statement of the skeleton `Lehner.lean`
-- (saved as `HPC/PseudoArc/Lehner.lean`) and for the auxiliary results of
-- `HPC/PseudoArc/LehnerCore.lean`. Output: `axioms-batch114.txt`.
#print axioms HPC.isPseudoArc_of_subcontinuum
#print axioms HPC.not_mem_composant_of_irreducible
#print axioms HPC.exists_epsChain_of_irreducible
#print axioms HPC.Chain.IsConsolidationOf.trans
#print axioms HPC.exists_description_consolidating
#print axioms HPC.lehner_lemma3_two
#print axioms HPC.Description.covering_step
#print axioms HPC.Description.exists_description_covering
-- auxiliary (LehnerCore.lean)
#print axioms HPC.Lehner.exists_eq_of_lip
#print axioms HPC.Lehner.dist_le_of_near
#print axioms HPC.Lehner.blocks
#print axioms HPC.Lehner.indices
#print axioms HPC.Lehner.core
