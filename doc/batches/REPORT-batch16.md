# Report — batch 16: `ExitReach`, the corrected dichotomy

One new file, `HPC/Fold/ExitReach.lean` (296 lines); root `HPC.lean` updated as supplied by the
batch; the commission text kept as `COMMISSION-batch16.md`. Nothing else in the project was
touched. The re-run of the census (see §1) is the script `census-batch16.py`, added for
reproducibility.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings. Every theorem in it has axiom profile within `[propext, Classical.choice,
Quot.sound]` (`valleyBefore_neg_iff` uses only `[propext, Quot.sound]`).

**Headline, as §6.3 requests first.** `ExitReach` was **not** refuted. Nothing in it had to be
adjusted, and the two commissioned branches went through as described. One change to the
commission was forced, and it is in the assembly, not in the conjecture: `f2Prime_of_exitReach`
needs a *third* hypothesis, `LowExitPeak`, the reflection of `HighExitValley` through the
negation. See §4.

## 1. Census

The evidence was gathered afresh, as the commission directs, under the **down** form
`IsCrookedSeq` — the form `minIdx` satisfies and the one `F2Prime` is stated over. Exhaustive
enumeration of all 1-Lipschitz sequences, filtered for `IsCrookedSeq`, every basepoint of every
surviving sequence:

| levels | lengths | crooked sequences | basepoints |
|---|---|---|---|
| 6 | 4 – 12 | 429 496 | 4 890 680 |
| 7 | 4 – 11 | 207 038 | 2 152 074 |

(Basepoints in sequences of range at most two fall outside the hypothesis `L + 3 ≤ H` and were
skipped; `L` and `H` are taken as the actual minimum and maximum of the sequence, the tightest
admissible choice, which is also the choice `theorem3_of_F2Prime` makes.)

Three statements were tested at every one of those basepoints, with no failure of any of them:

* `ExitReach` — both arms `OkLam` at `hStar`, or both `OkVee` at `lStar`;
* `HighExitValley` — the Λ-side valley clause of batch 10, at every admissible peak index `s`;
* `LowExitPeak` — the reflected clause introduced here, at every admissible index `s`.

This is an exploratory computation in a separate script, not a Lean-checked claim; it is
recorded as evidence for the three conjectural propositions, exactly as the corpus figures in
earlier batches are. Everything asserted *in Lean* in this batch is proved outright.

### Declarations, in file order

"Project" dependencies are results and definitions from earlier batches (batch number in
parentheses); "mathlib" lists library lemmas used beyond the `omega`, `simp`, `rcases`/`obtain`
tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `DropsBelow` | def | — | — |
| `hReach` | def | `phase` (b8) | `sSup` |
| `lReach` | def | `hReach` | — |
| `OkLam` | def | `DropsBelow`, `hReach` | — |
| `OkVee` | def | `OkLam` | — |
| `reachSet` | private def | `phase` (b8) | — |
| `reachSet_bddAbove` | private thm | `reachSet` | `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove` |
| `reachSet_nonempty` | private thm | `reachSet` | `Fin.le_def`, `Fin.ext` |
| `hStarArm_le_hReach` | theorem | `hStarArm_mem` (b9), `phase_zero_or_one` (b8), `reachSet_bddAbove` | `le_csSup` |
| `hReach_mem` | theorem | `reachSet_nonempty`, `reachSet_bddAbove` | `Int.csSup_mem` |
| `le_succ_of_no_drop` | theorem | `le_hStarArm_of_no_drop` (b10), `DropsBelow` | — |
| `segLam_of_okLam_no_drop` | theorem | `segLam_of_bounded` (b10), `le_succ_of_no_drop` | — |
| `exists_peak_index_of_hReach` | theorem | `hReach_mem`, `exists_least_index` (b6) | `Fin.le_def`, `Fin.ext`, `lt_of_not_ge` |
| `segLam_of_okLam` | theorem | `segLam_of_okLam_no_drop`, `exists_peak_index_of_hReach`, `segLam_of_peak_before_drop` (b10) | — |
| `hStar_dem_armG`, `hStar_dem_armT` | theorems | `hStar` (b9), `hStarArm` (b9) | `le_min_iff`, `le_max_iff` |
| `lStar_dem_armG`, `lStar_dem_armT` | theorems | `lStar` (b9), `lStarArm` (b9) | `max_le_iff`, `min_le_iff` |
| `le_hStar`, `lStar_le` | theorems | `hStar`, `lStar` (b9) | `le_min_iff`, `le_max_iff`, `max_le_iff`, `min_le_iff` |
| `PeakBefore` | def | — | — |
| `valleyBefore_neg_iff` | theorem | `ValleyBefore` (b10), `PeakBefore` | — |
| `LowExitPeak` | def | `ValleyBefore` (b10), `phase` (b8), `lStar` (b9), `armG`, `armT` (b6) | — |
| `ExitReach` | def | `OkLam`, `OkVee`, `hStar`, `lStar` (b9), `IsLip` (b6), `IsCrookedSeq` (b5), `armG`, `armT` (b6) | — |
| `f2Prime_of_exitReach` | theorem | `ExitReach`, `HighExitValley` (b10), `LowExitPeak`, `F2Prime` (b9), `segLam_of_okLam`, the four `dem` lemmas, `le_hStar`, `lStar_le`, `armG_isLip`, `armT_isLip` (b6) | `abs_le` |

Beyond the commissioned list, five statements were added: `segLam_of_okLam` (the merge of the
two branches, so that the four applications in the assembly — two arms, two families — are one
lemma applied four times); the four `hStar`/`lStar` demand lemmas together with `le_hStar` and
`lStar_le` (§2); and `PeakBefore` with `valleyBefore_neg_iff` and `LowExitPeak` (§4). The
private `reachSet` triple is bookkeeping for the supremum.

## 2. `hdem`: taken as commissioned, discharged at the call site

The commission offered the choice of taking `hStar` itself as the hypothesis of
`le_succ_of_no_drop` and deriving the disjunction inside. The disjunction was kept, exactly as
written — it is the honest hypothesis of the lemma, and it keeps the lemma free of the
basepoint apparatus, which `hStar` would drag in. That `hStar` supplies it is recorded
separately:

    theorem hStar_dem_armG (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) :
        hStarArm (armG ρ i) (ρ i) ≤ hStar ρ i H L ∨ H - 1 ≤ hStar ρ i H L

and likewise for `armT`. Both are `simp only [hStar, le_min_iff, le_max_iff]` followed by
`omega`: once the `min` and the three `max`es are turned into conjunctions of inequalities the
case split the commission describes in prose — cap binding or not — is inside `omega`'s reach.
The valley-side pair `lStar_dem_armG`, `lStar_dem_armT` is the same computation for
`lStar ≤ lStarArm ∨ lStar ≤ L + 1`, converted at the call site by
`hStarArm (fun j => - A j) (-p) = - lStarArm A p`, which is the definition of `lStarArm`.

## 3. The two branches

Both went through as the commission describes, with no surprises.

*No drop.* `¬ DropsBelow A p` unfolds to `∀ j, p - 1 ≤ A j`, so batch 10's
`le_hStarArm_of_no_drop` bounds the arm by its own demand, and the two cases of `hdem` give
`A j ≤ h + 1` — via `hStarArm A p ≤ h` in the first, via `A j ≤ H ≤ h + 1` in the second.
`segLam_of_okLam_no_drop` is then one application of `segLam_of_bounded`, whose remaining
hypothesis `∀ j, L ≤ A j` is passed through.

*Drop.* `hReach_mem` is `Int.csSup_mem` on the same set pattern as `hStarArm_mem`: a subset of
the finite range of `fun j => A j + phase A j`, nonempty because index `0` qualifies
(`phase_zero` is not even needed — the membership proof keeps `A 0 + phase A 0` symbolic). The
least index `s` at which the phase-adjusted level reaches `h` then satisfies `s ≤ j₀`, so the
prefix condition at `j₀` covers everything below `s`, which is clause (4); clauses (2) and (3)
are the defining property of `s`. `hStarArm_le_hReach` is `le_csSup` on the same set plus
`phase_zero_or_one`; it is not used in the assembly, but it is what makes `OkLam` visibly
weaker than `h ≤ hStarArm A p`.

## 4. The reflection in §5, and the one statement that did not go through as commissioned

The Λ case of the assembly is exactly §5 of the commission. The V case is *not* available from
`HighExitValley` alone, and this is the single deviation from the commissioned statements.

`SegVee`, `OkVee` and `lStar` are indeed all defined by negation, and the lemmas of §3 and §4
carry no crookedness hypothesis, so applying `segLam_of_okLam` to `fun j => - armG ρ i j` at
`p' = -p`, `h' = - lStar`, upper bound `-L` and lower bound `-H` produces precisely
`SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L)`. That part of the reflection is sound and is what
the file does.

But `segLam_of_okLam` also consumes a valley hypothesis, and for the negated arm that
hypothesis reads: *past the valley index, the arm does not go below `lStar − 1` without having
visited `H − 1` or above in between*. That is a statement about the original sequence at
`lStar`, and `HighExitValley` is a statement about it at `hStar`; the only route from one to
the other is to instantiate `HighExitValley` at the negated sequence, which requires
`IsCrookedSeq (fun t => - ρ t)`. Batch 13 shows that this does not follow from
`IsCrookedSeq ρ` — `not_isCrookedSeq_neg` exhibits a sequence refuting it, and
`isCrookedSeqUp_neg_iff` identifies what negation *does* give as the strictly different
condition `IsCrookedSeqUp`. So the transport is unavailable, and the missing clause is a
genuine extra assumption, not a packaging matter.

It is recorded as

    def LowExitPeak : Prop := ...

stated in the negated shape in which `segLam_of_peak_before_drop` consumes it, so that the V
case of `f2Prime_of_exitReach` is literally the Λ case with negated data; `PeakBefore` and
`valleyBefore_neg_iff` give the same condition in unnegated form, for reading. `LowExitPeak` is
the exact mirror of `HighExitValley`, hypotheses included, and it was tested over the whole
corpus of §1 with no failure. The delivered theorem is therefore

    theorem f2Prime_of_exitReach (h1 : ExitReach) (h2 : HighExitValley) (h3 : LowExitPeak) :
        F2Prime

An alternative worth recording for a later batch: if `HighExitValley` were restated for the
symmetric crookedness notion `IsCrookedSeqSym` of batch 13 — which *is* negation-symmetric
(`IsCrookedSeqSym.neg`) and is implied by `IsCrookedSeq` — then its reflection would follow
from it, and the third hypothesis would disappear. That is a strengthening of
`HighExitValley`'s content, so it is not something this batch could do by rewriting the
assembly; it is a change to the conjecture, and the corpus for it would have to be gathered
again under the symmetric form.

## 5. What is now open

With this batch, Bing 1948 Theorem 3 in the block reading and three-link form
(`theorem3_of_F2Prime`, batch 9) rests on exactly three unproved propositions: `ExitReach`,
`HighExitValley` and `LowExitPeak`. All three are per-basepoint statements about crooked
1-Lipschitz integer sequences; none mentions chains, links or itineraries.
