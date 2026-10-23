# Commission: batch 12 — Agreement reduced to one configuration

**Go!** Runs on top of the batch-11 delivery. One new file, `HPC/Fold/Agree.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

`Agreement` (batch 11) is the last mathematical obstacle to `F2Prime`, hence to Bing 1948
Theorem 3. This batch proves the half of it that is elementary and names the half that is not.

## Protocol

As batches 1–11. Expected: `hStarArm`, `hStarArm_mem`, `lStarArm`, `armG`, `armT`,
`Agreement`, `IsLip`, `IsCrookedSeq`.

## 1. The single-arm lemma

Recall `hStarArm A p = sSup {v | ∃ j, A j = v ∧ ∀ j' ≤ j, p − 1 ≤ A j'}` and
`lStarArm A p = − hStarArm (−A) (−p)`, which unfolds to
`sInf {v | ∃ j, A j = v ∧ ∀ j' ≤ j, A j' ≤ p + 1}`.

**not_hStarArm_and_lStarArm.** Suppose `p + 2 ≤ hStarArm A p` and `lStarArm A p ≤ p − 2`. By
`hStarArm_mem` there is `j` with `A j = hStarArm A p ≥ p + 2` and `p − 1 ≤ A j'` for all
`j' ≤ j`. By the reflected `hStarArm_mem` there is `k` with `A k = lStarArm A p ≤ p − 2` and
`A k' ≤ p + 1` for all `k' ≤ k`.

`Fin m` is linearly ordered, so `k ≤ j` or `j ≤ k`. If `k ≤ j`, the first prefix condition at
`j' := k` gives `p − 1 ≤ A k ≤ p − 2`, false. If `j ≤ k`, the second at `k' := j` gives
`A j ≤ p + 1` while `A j ≥ p + 2`, false.

No crookedness, no Lipschitz property, no relation between `p` and the ambient bounds is used.

**le_lStarArm_of_hStarArm, hStarArm_le_of_lStarArm.** Contrapositives, by `not_lt` and
`omega` from the above.

## 2. The reduction

**agreement_of_mixedGap.** Let `ρ` be crooked and Lipschitz, `i` a basepoint, `p := ρ i`.
Write `hG, hT, lG, lT` for the four demands. Note `p ≤ hG`, `p ≤ hT`, `lG ≤ p`, `lT ≤ p`, each
witnessed by the index `0` of the respective arm (`le_hStarArm`, batch 9, and its reflection).

Suppose `Agreement` fails: `2 ≤ |hG − hT|` and `2 ≤ |lG − lT|`. By symmetry in the two arms
assume `hT + 2 ≤ hG` (otherwise swap `G` and `T` throughout; the statement is symmetric).
Then `hG ≥ hT + 2 ≥ p + 2`, so by `le_lStarArm_of_hStarArm` applied to `armG`,
`lG ≥ p − 1`.

The hypothesis `2 ≤ |lG − lT|` splits.

*If `lG + 2 ≤ lT`:* then `lG ≤ lT − 2 ≤ p − 2`, contradicting `lG ≥ p − 1`.

*If `lT + 2 ≤ lG`:* this is exactly the configuration `MixedGap` forbids.

So `MixedGap` gives `Agreement`. *(supply: the symmetry step — either state the swap as a
lemma about the two arms, or prove the four-way case split directly; `armG` and `armT` have
different index types, so a literal swap needs care. Whichever is cleaner, record it.)*

## 3. `MixedGap`

A definition; nothing to prove. It is the residual: one arm rises to `p + 2` before ever
dropping, the other drops to `p − 2` before ever rising, and the two gaps are both at least
two. This is the configuration the Synchronization Lemma (batch 7) describes — its hypotheses
are met here, with the first drop and first rise as the two witnesses and everything between
them inside `[p − 1, p + 1]` — but `sync`'s conclusion alone does not close it.

Verified empty on 2 604 840 crooked basepoints. If a counterexample falls out while
formalizing, report it in preference to anything else.

## 4. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: how the arm symmetry in §2 was handled; what was supplied; any statement that did
   not go through.

## 5. Not in this batch

`MixedGap`; `SmallDemandCase`; `HighExitValley`; the assembly into `F2Prime`; Bing 1948
Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
