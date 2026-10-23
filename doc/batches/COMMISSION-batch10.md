# Commission: batch 10 — what `SegLam` demands of a single arm

**Go!** Runs on top of the batch-9 delivery. One new file, `HPC/Fold/Exits.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

`F2Prime` (batch 9) is a statement about both arms at once. This batch reduces it, arm by arm,
to conditions on where the arm first leaves the window `[p−1, p+1]`, and records three
propositions that further work must supply.

**What is claimed.** The four per-arm lemmas of §3. Nothing else.

**What is not claimed.** That the three propositions of §4 imply `F2Prime`. The natural chain —
"the Λ family fails only if both arms drop, the V family only if both rise, and `Exclusion`
forbids both" — is **wrong as stated**: when the height `hStar` is set by an arm that never
drops, that arm's demand can exceed the other arm's maximum, and the other arm can then fail
`SegLam` while being the only arm that drops. The correct combination has not been worked out
and is not part of this batch. The three propositions are recorded with their evidence so that
the next attempt starts from named objects rather than prose.

## Protocol

As batches 1–9. Batch-8 results expected: `SegLam`, `phase`, `phase_zero_or_one`. Batch-9:
`hStarArm`, `hStarArm_mem`, `le_hStarArm`, `exists_peak_index`, `hStar`, `armG`, `armT`,
`IsCrookedSeq`, `IsLip`.

## 1. Reading of `SegLam`

`SegLam A p H L h` asks for `s ≤ t ≤ m` with: (1) every `j < s` has `p − 1 ≤ A j ≤ h + 1`;
(2) if `s < m`, `h ≤ A s + φ s`; (3) every `j < s` has `A j + φ j < h`; (4) every `j ∈ [s, t)`
has `L ≤ A j ≤ h + 1`; (5) `t = m`, or `s < t` and the level just before `t` is at most `L + 1`.

Two consequences used throughout. First, the upper half of clause (1) is free: if
`A j > h + 1` then `A j + φ j ≥ A j > h`, so clause (3) already fails at `j`, meaning
`j ≥ s`. So clause (1) can only fail through `A j < p − 1`, that is, through a **drop**.
Second, `t = m` discharges clauses (4) and (5) whenever the arm never exceeds `h + 1` after
`s`, since `L ≤ A j` holds by hypothesis everywhere.

## 2. Definitions

`ValleyBefore A L h s`: past `s`, the arm does not exceed `h + 1` without having visited
`L + 1` or below in between.

## 3. The per-arm lemmas — proofs

**segLam_of_bounded.** Take `s :=` the least index with `A j + φ j ≥ h`, or `m` if there is
none, and `t := m`. Clause (1): the hypothesis gives both halves directly. Clauses (2), (3):
by choice of `s`. Clause (4): `L ≤ A j` is hypothesis `hb` weakened (`L ≤ p − 1` is *not*
assumed — use instead that clause (4) needs `L ≤ A j`, which must come from the ambient bound;
**add the hypothesis `∀ j, L ≤ A j` to this lemma and record it**). Clause (5): `t = m`.

**le_hStarArm_of_no_drop.** With no drop, every `j` satisfies the side condition
`∀ j' ≤ j, p − 1 ≤ A j'` defining the set whose supremum is `hStarArm`, so every `A j` lies in
that set and is at most its supremum (`le_csSup`, with boundedness as in batch 9).

**segLam_of_no_drop.** By `le_hStarArm_of_no_drop` and `hStarArm A p ≤ h`, every `A j ≤ h`, so
`A` is confined to `[p − 1, h + 1]`; apply `segLam_of_bounded`.

**segLam_of_peak_before_drop.** Use the given `s`. Clauses (2), (3) are hypotheses; clause (1)
is `hnodrop` for the lower half and the first consequence of §1 for the upper. For clauses (4)
and (5): if no `u ≥ s` has `A u > h + 1`, take `t := m`. Otherwise let `u₀` be the least such
`u`; `hvalley` gives `j` with `s ≤ j < u₀` and `A j ≤ L + 1`; take `t := j + 1`. Then `t ≤ u₀`
so clause (4) holds on `[s, t)` by minimality of `u₀` and the ambient lower bound `L ≤ A`;
clause (5) holds with `s < t` because `s ≤ j`. *(supply: the `Fin`/`ℕ` bookkeeping, and the
ambient `∀ j, L ≤ A j` hypothesis, which must be added to this lemma as well.)*

## 4. The three propositions

`Exclusion`, `Balance`, `HighExitValley` are definitions; nothing to prove. Each docstring
carries the size of the corpus on which it was checked. If any of the three is **found to be
false** while formalizing — for instance by a counterexample falling out of an attempted
proof — report it; that is more valuable than the definitions.

State them as written. In particular do not strengthen `Exclusion` to "some arm drops and some
arm rises": that form is false, since a single arm may do both.

## 5. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: the two added `L ≤ A j` hypotheses; what was supplied; any statement that did not
   go through.

## 6. Not in this batch

`F2Prime`; the combination of §4 into `F2Prime`; Bing 1948 Theorems 4, 5, 6; the reduction in
Bing 1951; the D8/D9 gap.
