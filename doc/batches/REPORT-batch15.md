# Report — batch 15: `MixedGap`, `MixedGapUp` and `Agreement` are refuted

One new file, `HPC/Fold/Refutations.lean` (127 lines); root `HPC.lean` updated as supplied by
the batch; the commission text kept as `COMMISSION-batch15.md`. Nothing else was touched — in
particular `Agree.lean`, `Symmetry.lean` and `Phase.lean` keep their docstrings, as §5 asks,
and the module docstring of the new file records that their corpus evidence was gathered under
the wrong model.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings. Every theorem in it has axiom profile within `[propext, Classical.choice,
Quot.sound]` (`badSeq_badPt`, decided, uses only `[propext, Quot.sound]`).

**Headline, as §6 requests.** The commission's sequence works exactly as described. `badSeq`
satisfies both crookedness conditions, the four demands are `5, 3, 3, 1` as stated, and all
three propositions are refuted. Nothing in the commission had to be adjusted.

## 1. Census

Everything in `HPC/Fold/Refutations.lean`, in file order. "Project" dependencies are results
and definitions from earlier batches; "mathlib" lists library lemmas used beyond the `omega`,
`simp`, `norm_num`, `decide` and `rcases`/`obtain` tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `badSeq` | def | — | `Matrix.of`/`![...]` notation |
| `badPt` | def | — | — |
| `badSeq_badPt` | theorem | `badSeq`, `badPt` | — |
| `badSeq_isLip` | theorem | `IsLip` (b6), `badSeq` | `fin_cases` |
| `badSeq_isCrookedSeq` | theorem | `IsCrookedSeq` (b5), `badSeq` | — |
| `badSeq_isCrookedSeqUp` | theorem | `IsCrookedSeqUp` (b13), `badSeq` | — |
| `hStarArm_eq_of_attained` | theorem | `hStarArm` (b9) | `le_csSup`, `csSup_le`, `le_antisymm`, `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove` |
| `badSeq_hStarArm_G` | theorem | `hStarArm_eq_of_attained`, `armG` (b6), `badSeq_badPt` | — |
| `badSeq_hStarArm_T` | theorem | `hStarArm_eq_of_attained`, `armT` (b6), `badSeq_badPt` | — |
| `badSeq_lStarArm_G` | theorem | `hStarArm_eq_of_attained`, `lStarArm` (b9), `armG` (b6), `badSeq_badPt` | — |
| `badSeq_lStarArm_T` | theorem | `hStarArm_eq_of_attained`, `lStarArm` (b9), `armT` (b6), `badSeq_badPt` | — |
| `not_mixedGap` | theorem | `MixedGap` (b12), the four demand theorems, `badSeq_isLip`, `badSeq_isCrookedSeq` | — |
| `not_mixedGapUp` | theorem | `MixedGapUp` (b13), the four demand theorems, `badSeq_isLip`, `badSeq_isCrookedSeqUp` | — |
| `not_agreement` | theorem | `Agreement` (b11), the four demand theorems, `badSeq_isLip`, `badSeq_isCrookedSeq` | — |
| `agreement_route_is_dead` | theorem | `not_mixedGap`, `not_agreement` | — |

`hStarArm_eq_of_attained` is the one statement added beyond the commissioned list; see §3.

## 2. The crookedness enumeration: which route was taken

`decide`, after `unfold`. The commission allowed for the possibility that the 81-case
enumeration over `Fin 9 × Fin 9` with `ℤ`-valued comparisons would be intractable in the
kernel; it is not. Both

    theorem badSeq_isCrookedSeq   : IsCrookedSeq   badSeq := by unfold IsCrookedSeq;   decide
    theorem badSeq_isCrookedSeqUp : IsCrookedSeqUp badSeq := by unfold IsCrookedSeqUp; decide

go through in a few seconds each with `maxRecDepth` raised to 100000. The `unfold` is needed:
`IsCrookedSeq` and `IsCrookedSeqUp` are plain `def ... : Prop`, so instance search does not see
through them to synthesize `Decidable`; once unfolded, the decidability of bounded `Fin`
quantification and of `ℤ` order does the rest. No witness had to be supplied by hand, so the
two witness tables of the commission (§2) were not needed in the proof, though they are exactly
what the decision procedure finds.

`badSeq_isLip` is the 81-case `fin_cases j <;> fin_cases j' <;> simp_all [badSeq]`: the
hypothesis `j'.val = j.val + 1` kills all but the eight consecutive pairs, and each of those is
a literal `|±1| ≤ 1`.

## 3. How `hStarArm` was computed

The delivered encoding is `hStarArm f p = sSup {v | ∃ j, f j = v ∧ ∀ j' ≤ j, p − 1 ≤ f j'}`,
an `sSup` over a set of integers, so the batch-9 lemmas `hStarArm_mem` and `le_hStarArm` give
only membership and the lower bound `p ≤ hStarArm`. What is needed here is an exact value, so
one small general lemma was added:

    hStarArm_eq_of_attained :
      f j = c → (∀ j' ≤ j, p − 1 ≤ f j') →
      (∀ k, (∀ k' ≤ k, p − 1 ≤ f k') → f k ≤ c) → hStarArm f p = c

— an attaining index and a uniform upper bound pin the supremum. Its proof is `le_antisymm` of
`csSup_le` (the set is nonempty, since `c` is in it) and `le_csSup` (the set is a subset of the
finite range of `f`, hence bounded above), three lines, the same shape as
`le_hStarArm_of_window` in batch 14.

With it, each of the four demands is one application with a witness index and three `decide`s
for the arithmetic side conditions, after `rw [badSeq_badPt]` replaces the basepoint level by
the literal `3`. The arms are concrete: `Fin (9 − badPt.val)` and `Fin (badPt.val + 1)` both
reduce to `Fin 5` definitionally, and `armG badSeq badPt j = badSeq ⟨4 + j, _⟩`,
`armT badSeq badPt j = badSeq ⟨4 − j, _⟩` are definitional too, so every side condition is a
closed statement about five integers.

* `hStarArm G = 5`: witness index `4`, value `5`; no index of `G = 3, 4, 3, 4, 5` goes below
  `p − 1 = 2`, so the side condition holds everywhere and `5` bounds all values.
* `hStarArm T = 3`: witness index `0`, value `3`; `T = 3, 2, 3, 2, 1` reaches `1 < 2` at index
  `4`, so index `4` is excluded and `3` bounds the values at `0..3`.
* `lStarArm G = 3` and `lStarArm T = 1`: by definition `lStarArm A p = − hStarArm (−A) (−p)`,
  so each is one application of the same lemma to the negated arm at `−3`, giving
  `hStarArm (−G) (−3) = −3` (witness index `0`; index `4` of `−G` is `−5 < −4`, excluded) and
  `hStarArm (−T) (−3) = −1` (witness index `4`; `−T = −3, −2, −3, −2, −1` never goes below
  `−4`), followed by `omega`.

## 4. The three refutations

Each is the commissioned two lines. `not_mixedGap` applies `MixedGap` at `9, badSeq, badPt`
with the Lipschitz and crookedness facts, and supplies the forbidden conjunction from the
demands: `3 + 2 ≤ 5` and `1 + 2 ≤ 3`. `not_mixedGapUp` is the same with the up-form
crookedness. `not_agreement` refutes both disjuncts: `|5 − 3| = 2` and `|3 − 1| = 2`, and the
orientation of the difference is immaterial under the absolute value.

`agreement_route_is_dead` is the recorded conjunction, unchanged from the skeleton.

## 5. Statements that did not go through

None. Every statement in the skeleton is proved as commissioned, with no weakening of any
conclusion and no added hypothesis.

## 6. On the arrangement of §5

The commission's arrangement was followed exactly: the three earlier files are untouched, and
the module docstring of `Refutations.lean` carries the correction. This is also what I would
recommend. The docstrings in question describe how the conjectures were arrived at, which is
still accurate history; editing them would lose the record of the modelling error, whereas the
new module docstring states plainly that the corpus was filtered with the exact-level model and
is therefore no evidence for either weak form. Readers of the three definitions reach the
refutations through the module: `HPC.lean` imports `Refutations.lean` last, and
`agreement_route_is_dead` is there so that a search for `MixedGap` turns up its negation.

## 7. What the refutation does and does not touch

`MixedGap`, `MixedGapUp` and `Agreement` are all `def ... : Prop` and none was ever discharged
as a hypothesis of a theorem, so no earlier result loses content. Concretely:

* `agreement_of_mixedGap` (batch 12) remains true, now with a false antecedent and a false
  consequent; it is no longer a route to anything.
* `mixedGap_swap` (batch 12) likewise: true, vacuous.
* `mixedGapUp_witnesses` (batch 14) remains true and is *not* vacuous — `badSeq` satisfies its
  antecedent, so the witnesses it produces exist for a real configuration. The refuted claim is
  only that the configuration is impossible.
* `sync`, `sync_up` and the itinerary/bump machinery are untouched: none of them mentions the
  three propositions.

The live consequence is that the residual configuration of the reduction really does occur, so
whatever replaces `Agreement` must accommodate `badSeq` rather than exclude it. That
replacement is explicitly not in this batch.
