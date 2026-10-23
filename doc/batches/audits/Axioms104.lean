import HPC

/-!
# Axiom audit, batch 104 (Bing's Theorem 11 by Fugate 1969, Case II)

Output: `axioms-batch104.txt`; regenerate with `lake env lean Axioms104.lean > axioms-batch104.txt`
after `lake build HPC`.
-/

-- Item 1: Lemma 3
#print axioms HPC.Plane.isTerminalSub_of_union_terminal
-- Item 2: inductiveness, Lemma 4 (HD case)
#print axioms HPC.Plane.isTerminalSub_iInter
#print axioms HPC.Plane.exists_terminal_point_of_isTerminalSub
-- Item 3: the halves
#print axioms HPC.Plane.halves_terminal
-- Item 4: Claim 1
#print axioms HPC.Plane.claim1_contains_inter
-- Item 5: the common terminal point
#print axioms HPC.Plane.exists_mu
-- Item 6: Claim 2 and the chain
#print axioms HPC.Plane.claim2
#print axioms HPC.Plane.epsCoverable_of_halves
-- Item 7: Theorem 11
#print axioms HPC.Plane.exists_not_endElt
#print axioms HPC.Plane.theorem11_1951
#print axioms HPC.Plane.theorem11_1951_iff
