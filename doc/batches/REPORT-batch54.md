# Report: batch 54 — inside the residues

**No counterexample.** Nothing in §1 of the commission is refuted, and no census or search of this
batch found a pair of the general model at which any of the targets fails. Nothing in §1 is proved
outright either. What the batch delivers is a *sharpening of both residues* — the valley one and
the ceiling one — with the first use in the crossing proofs of the clause that distinguishes the
faithful model from the two crookedness clauses of the sequence, and a census that measures the
sharpened residues and says which walks serve the pairs inside them.

`lake build HPC` is clean. The two new files, `HPC/Fold/CeilNarrow.lean` and
`HPC/Fold/ValleyNarrow.lean`, contain no `sorry`; every new theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`, no new `axiom`, no `@[implemented_by]`. The
`sorry`s of `HPC/Fold/CrossCeil.lean`, `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` are
unchanged in number and in statement.

---

## 1. The targets

### 1.1 `cross_ceil_sentence` inside the two residues

Not proved. It is, however, now known what the model says inside `CeilPeakResidual`, and the
residue is a strictly smaller configuration than it was.

`HPC/Fold/CeilNarrow.lean` re-proves the peak half of the crossing without appealing to
`ceil_cross_peak_fwd`, and follows the two times the crookedness clause returns all the way:

> **`ceil_cross_peak_fwd_narrow`.** In the configuration of `ceil_cross_peak_fwd` — a descent `s`
> to `L + 1` on the backward arm, an unprepared ascent `t` to `L + 8` on the forward arm — either
> the backward arm carries the peak `Valley5` asks for, or `CeilPeakResidual` holds **and** the
> forward arm carries a *flat narrow bottom* (`CeilFarFlatG`): a time `w` with `i + 2 ≤ w`,
> `ρ w = L + 2` exactly, `ρ ≥ L + 2` at both neighbours of `w`, and `ρ ≥ L + 2` at every time
> between `i + 2` and `w`.

Three observations carry it, and all three are about the arm that fails `Leg3Ceil`.

* *The low time the clause returns is on the far side.* In the residue the peak `u` sits two or
  three steps before the basepoint, so the low time `u'` that follows it cannot lie between them
  (`ρ u ≥ L + 6` and `ρ u' ≤ L + 2` are four levels apart, and there is no room), cannot be the
  basepoint, and cannot be one step past it. So `i + 2 ≤ u'`.
* *The failing arm keeps away from the floor* (`ceil_no_low_far_fwd`). From `i + 2` up to its
  unprepared ascent the arm never stands at `L + 1` or below: a time there at `L + 1` would let
  the clause return, between it and the ascent, exactly the pair of landmarks the failure of
  `Leg3Ceil` forbids. Hence `ρ u' = L + 2` exactly.
* *The bottom is narrow* (`ceil_flat_narrow_fwd`). This is where the faithful model says more than
  `CrookUp` and `CrookDown` do. `IsCrookedIvF.crooked` fires on any level **met within one step**
  of its anchor, and returns its two witnesses strictly *between the anchors*. Anchoring at `u'`
  and firing on a level at or below `L + 1` met at `u' − 1`, `u'` or `u' + 1` therefore returns a
  time at `L + 6` or above at an index `> u' ≥ i + 2` — that is, at `i + 3` or beyond, which is
  exactly the index the failure of `Leg3Ceil` needs — followed by a time at `L + 2` or below. So
  no such level is met. Anchoring one step earlier, which is all the two crookedness clauses of
  the sequence allow, loses that one index and proves nothing.

The assembled statement is `cross_ceil_sentence_of_not_narrow_residual`: the work item holds unless
`CeilHighResidual` holds, or `CeilPeakResidual` holds **together with** a flat narrow bottom on the
failing arm. It is `cross_ceil_sentence_of_not_residual` with the first exclusion weakened.

What the census says about the gain: **nothing, over this corpus.** Of 528 Λ-free ceiling
configurations, 34 are in `CeilPeakResidual`, and all 34 also carry a flat narrow bottom (on both
sides: `CeilFarFlatG` and `CeilFarFlatT` hold at all 528). So the sharpened theorem covers the same
494 configurations the old one did. The narrowing is a strictly stronger theorem and a strictly
smaller configuration; it is not a smaller *count* here.

### 1.2 `cross_valley_profile` inside `ValleyResidual`

Not proved, and sharpened in the same way — the ceiling argument transposes.

> **`cross_valley_dichotomy_narrow`** (`HPC/Fold/ValleyNarrow.lean`). Under the hypotheses of the
> work item, either both arms fold onto the V-walk, or `ValleyNarrowResidual` holds: the sequence
> stands at `L + 2` two or three steps to one side of the basepoint *and* at `L + 2` or above at
> both neighbours of that time.

Where the residual `L + 2` has a neighbour at `L + 1` or below, the interval clause anchored at the
residual time, fired between the ascent to `L + 7` and it, returns a time at `L + 2` or below
strictly between them — and "strictly between" is exactly the index bound (`4 ≤ j`) that the
V-criterion asks for and that the two-step-close residual time fails. `cross_valley_low_fwd_narrow`
and its mirror carry it; `cross_valley_profile_of_not_narrow_residual` is the work item outside the
narrow configuration.

Again the census gain is nil: over 1 152 344 branch basepoints, `ValleyResidual` and
`ValleyNarrowResidual` hold at exactly the same 285 274 of them (118 663 with a failing arm). Every
residual `L + 2` in this corpus is narrow. The sharpening is real as a theorem and empty as a
reduction of the corpus — which is itself the answer to "is the interval clause enough here?": at
the valley it is not, at the ceiling it is not, and both remaining residues are configurations the
faithful model genuinely permits.

### 1.3–1.5 `unserved_three_walks`, `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`

Untouched. They rest on 1.1 and 1.2 and inherit their state. The three `sorry`s of
`HPC/Fold/Mixed.lean` and the two of `HPC/Fold/General.lean` stand exactly as they did.

---

## 2. The questions

### 2.1 What happens inside the residues

Answered by census, per residue, with every predicate read as its definition reads it
(`census-batch54.c`, log `census-batch54.log`).

| residue | basepoints | Λ | V | w₃ | w₄ | w₅ | none of the five |
|---|---|---|---|---|---|---|---|
| `ValleyResidual` with a failing arm | 118 663 | 0 | **118 663** | 0 | 49 763 | 0 | 0 |
| `ValleyNarrowResidual` with a failing arm | 118 663 | 0 | **118 663** | 0 | 49 763 | 0 | 0 |
| `CeilPeakResidual`, Λ-free ceiling case | 34 | 0 | **34** | 0 | 0 | **34** | 0 |
| `CeilHighResidual`, Λ-free ceiling case | 0 | — | — | — | — | — | — |
| `CeilPeakResidual` and a flat narrow bottom | 34 | 0 | **34** | 0 | 0 | **34** | 0 |

So the answer to the question as asked is: **one walk serves each residue whole.** Every pair of
the valley residue with a failing arm folds onto the V-walk — the very conclusion the work item
asks for — and every pair of the ceiling peak residue folds onto the V-walk *and* onto `w₅`,
although by hypothesis it does not fold onto the Λ-walk. No pair of any residue is served by none
of the five. The residues are therefore not a new branch: they are configurations in which the
conclusion holds and the *proof* does not reach it, and the obstruction is the one level the
general clause loses, not a missing walk.

The ceiling high residue is unrealised over the whole corpus (0 of 528), as it was in batch 53.

### 2.2 Engines for four turns

**No new engine was built**, and the general sufficiency asked since batch 48 stands open. What
this batch can add is where exactly the existing four-leg engine stops, which is a concrete answer
to the concrete need.

`HPC/Fold/Leg4.lean` already carries a four-leg engine — `foldsOnto_leg4`, with the greedy time
assignment `gseq4` and the six progress clauses `E`, `R`, `E2`, `S`, `S2`, `T` on top of the window
condition `Val4`. Its walk is `leg4Walk L H K M P`: from `P − 1` up to `K`, down to `M`, up to
`H − 1`, down to `L + 1`. But its parameters are pinned to the branch `L + 4`:

```
L + 2 ≤ P ≤ L + 4,   P + 1 ≤ K ≤ H − 1,   L + 1 ≤ M,   M ≤ P − 2 ≤ M,   M + 3 ≤ K,   H ≤ K + 3
```

so `M = P − 2` exactly and the base is at most `L + 4`. The four-turn walks the branch `L + 5`
actually needs are outside that family on both counts. The shortest walk serving the hardest pairs
of `census-batch53.c` and of this batch's censuses is `5 → 7 → 3 → 8 → 1`, i.e. `P − 1 = L + 5`,
`K = L + 7`, `M = L + 3`, `H − 1 = L + 8`: it violates `P ≤ L + 4`, and its valley is `P − 3`, not
`P − 2`. Another of them, `4 → 3 → 7 → 1 → 8`, is the mirror shape — down, up, down, up — which
`leg4Walk` does not describe at all.

Relaxing the base alone would not be enough: the walk of the engine's own family with the base at
`L + 5` is `5 → 7 → 4 → 8 → 1`, seventeen links against the nineteen of `5 → 7 → 3 → 8 → 1`, and
the census — which searches four-turn walks based within one of `L + 5` in order of length — passes
over it and returns the longer one, so the seventeen-link walk does not serve those pairs. The
valley has to be three below the base.

So the answer to the question as asked is negative in the narrow sense: the engine that exists does
not reach the walks of the branch `L + 5`, and the obstruction is not the invariants but the
parameter window and the fixed valley `M = P − 2`. Whether the four invariants survive a base at
`L + 5`, a valley three below the base, and an arbitrary number of legs is still the open question,
now with the two walks above as the first test cases.

For the record, the covering list at the branch `L + 5` over this batch's corpus is unchanged in
shape from batch 53: the walks that serve the pairs the three reflected walks miss are
`5 → 7 → 1 → 8` (314 pairs), `4 → 7 → 1 → 8` (290), `5 → 6 → 8 → 1` (41), `5 → 3 → 8 → 1` (32),
`6 → 7 → 8 → 1` (12); 168 of the 857 missed basepoints are served by no walk of at most three
turns based within one of `L + 5` at all, and it is those that need the four-turn walks above.

### 2.3 The σ-route's lost link

Measured exactly, by `gap-batch54.c` (log `gap-batch54.log`), over 1 875 faithful pairs
(1 924 984 links, 0.194 % non-thin) from `bing 0 9`, `bing 9 0`, their shavings, fills and total
mixtures, and random concatenations of Bing blocks. At each of 432 069 basepoints of the branch
`L + 5` the program folds the arms of `τ = 9 − σ` and the arms of `9 − ρ` onto each of the five
walks of the branch `L + 4`, with window one, and compares:

* the τ-pair is served by one of the five at **333 463** basepoints;
* the pair of `9 − ρ` is served by one of the five at **333 463** basepoints — the same number, and
  there is **no basepoint at all** where the σ-route serves τ and nothing serves `9 − ρ`;
* but the *individual walk* is lost, and often: V serves τ and not `9 − ρ` at 591 basepoints, `w₃`
  at 390, `w₄` at 242, `w₅` at 18, Λ at none.

So the lost link is a loss of a particular fold, never of the basepoint: wherever the transported
walk fails on `9 − ρ`, another of the five picks the pair up. The census cannot decide the question
as put — whether the fold of τ can be *modified* into a fold of `9 − ρ` — but it says that the
modification, if it exists, must be allowed to change the walk, and that a modification which keeps
the walk provably does not exist: the 1 241 basepoints above are counterexamples to it, in the
general model, with `σ − ρ = 1` at the link that breaks the schedule.

### 2.4 Bing's seam

**Not attempted**, for the second batch running. No implementation of the dissolve-and-regroup
move at `bing 0 4` basepoint 6 was written, and nothing new is known about it. It is the one item
of the commission on which this batch has nothing to report. For the next one: nothing in the
repository currently carries the move — `census-batch24.py`, which is what batch 24 used at that
basepoint, implements the folds and the model, not the chain consolidation, and the consolidation
of `HPC/Chains/Consolidation.lean` is the inductive one, without the regroup-by-level step. The
move has to be written from the paper before it can be run.

---

## 3. The censuses

**`census-batch54.c`** (log `census-batch54.log`, sample `census-batch54-sample.txt`). Generators:
`bing 0 9`, `bing 9 0`, every single shaving and single fill of each, random mixtures at rate 1/3
and 1/2, the total mixture, random faithful perturbation walks, the two concatenated chains of
batch 53, and — new in this batch — **random concatenations of Bing blocks**: levels
`a₀, a₁, …, a_k` drawn uniformly from `0..9` and the blocks `bing aⱼ aⱼ₊₁` laid end to end. About
one draw in three or four is faithful (13 of 45 here), and the faithful ones are chains no census of
this repository has seen: they are `bing a b` for no `a`, `b`. Totals: **5 008 faithful pairs,
6 476 053 links, 48 618 of them non-thin (0.751 %)**, 1 152 344 basepoints of the branch `L + 4`
and 1 542 181 of the branch `L + 5`.

Over that corpus: no work item fails. 341 632 unserved pairs at the branch `L + 4`, every one
served by one of `w₃`, `w₄`, `w₅`; the landmark-sentence equivalence holds at all of them
(6 914 064 exactness checks, 0 failures); `cross_ceil_sentence` holds at all 528 Λ-free ceiling
configurations, always with the `w₅` disjunct; `cross_valley_profile` holds at all 221 655
basepoints with a failing arm. The new generator alone contributes 895 992 branch basepoints and
refutes nothing; at the branch `L + 5` its pairs are served by the three reflected walks without
exception.

**The definition audit, under the tightened protocol.** Every predicate that appears in the
statement of a Lean theorem this census is offered as evidence for is evaluated by the census as
the definition reads it, and is named here: `IsCrookedIvF` (`le`, `width`, `adj`, and `crooked`
with interval triggers read within one step of each anchor), `IsLip` (implied by `adj`),
`HighAt (L+1) (L+8)`, `LowAt (L+1) (L+8)`, `Leg3Valley`, `Leg3Ceil`, `Valley4`, `Valley5`, `TopW5`,
`MidW4`, `CeilW4`, `BottomW4`, `FoldsOnto` (the dynamic program of `HPC/Fold/Decide.lean`) for the
Λ-walk, the V-walk, `w₃`, `w₄`, `w₅` and their reflections, `ValleyResidual`,
`ValleyNarrowResidual`, `CeilPeakResidual`, `CeilHighResidual`, `CeilFarFlatG`, `CeilFarFlatT`. One
proxy is carried, and is reported as a proxy: `valleyResidualNarrow`, batch 53's interval-reading
version of the narrow valley residue, is kept beside the Lean predicate `ValleyNarrowResidual`,
which reads `ρ` alone. (They agree everywhere in this corpus.)

**`search-batch54.c`** (log `search-batch54.log`, hits file `search-batch54-hits.txt`) — the
counterexample hunt, over generators outside Bing's family. Three of them:

* **A**, random concatenations of Bing blocks, as above: 53 faithful of 159 drawn;
* **B**, random recursive chains whose consolidation levels are drawn per call rather than fixed at
  `b − 1` and `a + 1`: only **2 of 57** draws are faithful, which extends batch 53's finding for
  fixed parameters — the recursion is rigid, and a consolidation level one further in almost always
  breaks the model;
* **C**, a free depth-first random walk that extends `(ρ, σ)` one link at a time and rejects every
  extension violating the model, backtracking when a position runs out of candidates. The clause is
  checked incrementally and exactly — appending a link can only create violations of pairs `(s, t)`
  with `t` among the last two indices, and a violated pair is never repaired later. These walks do
  produce faithful pairs, but a myopic extension almost never finds the wiggle a three-level climb
  needs *before* the climb, so the individual walks stay within a narrow band of levels; the
  generator is reported for completeness (91 walks produced of 200 tried), and its pairs commonly
  fail the hypotheses `∃ t, ρ t = L` and `∃ t, ρ t = L + 9`: 5 913 of the pairs scanned were
  skipped on that ground.

Result: 8 287 faithful pairs, 4 041 230 links, 18 379 non-thin (0.455 %), 435 018 branch
basepoints — **no counterexample** to `cross_ceil_sentence`, to `cross_valley_profile`, to
`unserved_three_walks`, and no basepoint of the branch `L + 5` served by none of the three
reflected walks.

---

## 4. What is proved

All in `HPC/Fold/CeilNarrow.lean` and `HPC/Fold/ValleyNarrow.lean`, all `sorry`-free, each with
`#print axioms` giving `[propext, Classical.choice, Quot.sound]`.

* `CeilFarFlatG`, `CeilFarFlatT` — the flat narrow bottom on the far arm.
* `ceil_no_low_far_fwd`, `ceil_no_low_far_bwd` — the failing arm stands at `L + 2` or above from
  two steps past the basepoint until its unprepared ascent.
* `ceil_flat_narrow_fwd`, `ceil_flat_narrow_bwd` — and it meets no level at or below `L + 1` within
  one step of any such time, by the interval clause.
* `ceil_cross_peak_fwd_narrow`, `ceil_cross_peak_bwd_narrow` — the sharpened peak dichotomy.
* `ceil_gap_fwd_narrow`, `ceil_gap_bwd_narrow`, `ceilCrossGap_of_not_narrow_residual`,
  `cross_ceil_sentence_of_not_narrow_residual` — the work item outside the sharpened residues.
* `ValleyNarrowResidual`, `valleyResidual_of_narrow` — the narrow valley residue, and that it is a
  case of the old one.
* `cross_valley_low_fwd_narrow`, `cross_valley_low_bwd_narrow`,
  `critVee_armT_of_fail_armG_narrow`, `critVee_armG_of_fail_armT_narrow`,
  `cross_valley_dichotomy_narrow`, `cross_valley_profile_of_not_narrow_residual` — the sharpened
  valley crossing.

## 5. What this batch did not do

Question 2 (the four-turn engines) and question 4 (Bing's seam) were not attempted. Targets 1.3 to
1.5 are untouched. No statement of the repository was weakened, removed or commented out.
