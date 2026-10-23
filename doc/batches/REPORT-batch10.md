# Report — batch 10: what `SegLam` demands of a single arm

Delivered complete. One new file, `HPC/Fold/Exits.lean`; the root `HPC.lean` supplied by the
batch now imports it; the commission text is kept as `COMMISSION-batch10.md`. Nothing else in
the project was touched.

`lake build` succeeds on the default targets (`RequestProject`, `HPC`). The new file contains
no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`, and elaborates with no
linter warnings.

## 1. Census

### Theorems (all proved)

| Name | Statement | Depends on |
|---|---|---|
| `HPC.Fold.segLam_of_bounded` | An arm confined to `[p−1, h+1]` (and bounded below by `L`) satisfies `SegLam A p H L h`. | project: `SegLam`, `phase`, `exists_least_index`; mathlib: `Fin.ext`, `lt_of_not_ge`, `omega`, `push_neg`, `Classical` (for the case split) |
| `HPC.Fold.le_hStarArm_of_no_drop` | If `p − 1 ≤ A j` for every `j`, then `A j ≤ hStarArm A p` for every `j`. | project: `hStarArm`; mathlib: `le_csSup`, `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove` |
| `HPC.Fold.segLam_of_no_drop` | An arm with no drop to `p − 2` satisfies `SegLam` at any height `h ≥ hStarArm A p`. | `segLam_of_bounded`, `le_hStarArm_of_no_drop`; mathlib: `omega` |
| `HPC.Fold.segLam_of_peak_before_drop` | The general per-arm criterion: with a peak index `s` (clauses 2 and 3), no drop before `s`, and the valley condition past `s`, `SegLam` holds. | project: `SegLam`, `phase`, `phase_zero_or_one`, `exists_least_index`; mathlib: `Fin.ext`, `omega`, `push_neg`, `Classical` |

### Definitions (nothing to prove; recorded as commissioned)

| Name | Content |
|---|---|
| `HPC.Fold.Exclusion` | Never do both arms drop to `p − 2` and both arms rise to `p + 2`. |
| `HPC.Fold.Balance` | If both arms drop to `p − 2`, their demands `hStarArm` differ by at most one. |
| `HPC.Fold.ValleyBefore` | The per-arm valley condition, named so it can be quantified over both arms. |
| `HPC.Fold.HighExitValley` | At the height `hStar`, both arms satisfy `ValleyBefore` at their own peak indices. |

The three conjectures are stated exactly as written in the commission; in particular
`Exclusion` was *not* strengthened to "some arm drops and some arm rises". None of them was
found to be false in the course of the work — no attempted proof of any of them was made, as
the commission asks only that they be recorded.

Their combination into `F2Prime` is not claimed, in line with §"What is not claimed" of the
commission.

## 2. Changes to the commissioned statements

* **The two (in fact three) added `L ≤ A j` hypotheses.** Clause (4) of `SegLam` asks for
  `L ≤ A j` on the middle segment, and this does not follow from the window bounds
  `[p − 1, h + 1]` (no relation between `L` and `p` is assumed). As directed, the hypothesis
  `hL : ∀ j, L ≤ A j` was added to `segLam_of_bounded` and to `segLam_of_peak_before_drop`.
  It had to be added to `segLam_of_no_drop` as well, since that lemma is proved by reduction
  to `segLam_of_bounded`; this is the only deviation beyond the two the commission foresaw.
* **Unused hypotheses, kept as commissioned** (convention of batches 1–9, marked with a
  leading underscore): `_h0` in `segLam_of_bounded`; `_h0` in `le_hStarArm_of_no_drop`;
  `_hA`, `_h0`, `_hph` in `segLam_of_peak_before_drop`. In the last two lemmas `hm : 0 < m`
  is kept without an underscore only because it occurs in the type of `h0`. All the remaining
  explicit hypotheses are load-bearing; in particular `hs : s < m`, `hL`, `hpeak`, `hmin`,
  `hnodrop` and `hvalley` are all used in `segLam_of_peak_before_drop`, and `hb`, `hL` in
  `segLam_of_bounded`.

No commissioned statement failed to go through, and none was weakened.

## 3. What was supplied

* **`segLam_of_bounded`.** The case split on whether any index is a peak index is made
  explicit: if one exists, `s` is the least such index (`exists_least_index`) and clauses (2)
  and (3) are immediate; if none exists, `s := m`, clause (2) is vacuous because there is no
  proof of `m < m`, and clause (3) is the negated existential. In both cases `t := m`, so
  clause (5) is the left disjunct and clause (4) is `hL` together with the upper window bound.
* **`le_hStarArm_of_no_drop`.** The defining set of `hStarArm` is bounded above because it is
  contained in the (finite) range of `A`, exactly as in `hStarArm_mem` of batch 9; with no
  drop, `A j` lies in that set for every `j`, and `le_csSup` finishes.
* **`segLam_of_no_drop`.** `A j ≤ hStarArm A p ≤ h ≤ h + 1`, and `p − 1 ≤ A j` is the
  hypothesis, so `segLam_of_bounded` applies.
* **`segLam_of_peak_before_drop`.** The upper half of clause (1) is the first consequence of
  §1 of the commission: for `j < s`, `A j ≤ A j + φ j < h ≤ h + 1`, using `phase_zero_or_one`.
  For clauses (4) and (5), the `Fin`/`ℕ` bookkeeping is the item the commission marks
  *(supply)*: if no `u ≥ s` exceeds `h + 1`, take `t := m`; otherwise `u₀` is the least index
  satisfying the conjunction `s ≤ u ∧ h + 1 < A u` (`exists_least_index` applied to that
  conjunction, so that minimality is available in the form needed), `hvalley` supplies
  `s ≤ j < u₀` with `A j ≤ L + 1`, and `t := j + 1`. Clause (4) on `[s, t)` follows by
  minimality of `u₀`, since any `j'` with `s ≤ j' < t ≤ u₀` and `h + 1 < A j'` would
  contradict it; clause (5) takes the right disjunct, with `s < t` from `s ≤ j`, and the index
  just before `t` is `j` itself (`Fin.ext`).

## 4. Axiom profiles

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for each of

* `HPC.Fold.segLam_of_bounded`
* `HPC.Fold.le_hStarArm_of_no_drop`
* `HPC.Fold.segLam_of_no_drop`
* `HPC.Fold.segLam_of_peak_before_drop`
