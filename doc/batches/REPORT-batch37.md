# Report: batch 37 — span six, settled

One new file, `HPC/Fold/Span6.lean`; the commissioned `HPC/Fold/Open.lean` is installed
unchanged; root `HPC.lean` updated; `README.md` notes the batch. Nothing else is touched — the
forty-five earlier Lean files are byte-identical to the batch-36 delivery. The census program is
`census-batch37.py`, its output `census-batch37.log`.

## 0. No counterexample, and one new theorem

**No counterexample to `theorem3` was found**, and none is suggested by anything in this run:
every basepoint of every corpus examined is served, and the new theorem below explains why at
span six. `theorem3` itself is still open, with its single `sorry`.

**What is new: `S3` at span six.** Every faithful crooked sequence with `L + 3 ≤ H ≤ L + 6`
folds at every basepoint —

```
s3_span_six : IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) →
              L + 3 ≤ H → H ≤ L + 6 →
              ∃ len c, FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c
```

and, at the level of chains, `theorem3_span_six`: Bing's Theorem 3 in the block reading for a
crooked chain whose minimal-index range is at most six. The record before this run was span five
(`s3ZigFree_span_five`, `f2PrimeOff_span_five`), which is exactly the range in which
`s3_near_extreme` alone suffices and the crookedness is never used: at span five every level is
within two of an extreme. **Span six is the first span with any content** — `not_near_extreme_three`
shows the near-extreme range cannot be widened — and it is now closed. Everything is `sorry`-free
with axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

## 1. The shape of the proof, and why it is not a family argument

The two halves of the argument are separated, and the separation is the point.

**The folding half uses no crookedness.** `walk6 L` is the eight-time walk

```
L+2, L+3, L+4, L+5, L+4, L+3, L+2, L+1
```

— one bump, based *one level below* the basepoint, peaking at `H − 1`, ending at `L + 1` — and
`walk6' L` is its reflection. Define, for an arm `f` based at `L + 3`,

> **`LowLate f`**: before `f` ever reaches the bottom `L`, it has either reached `H − 1`, or
> reached `L + 1` and after that `H − 2`;

`HighLate` is the reflection. Then `foldsOnto_walk6_of_lowLate`: *every* 1-Lipschitz arm in
`[L, L+6]` based at `L + 3` that is `LowLate` folds onto `walk6 L`. No crookedness hypothesis
appears, so the reflected statement follows by reflecting the arm — which is legitimate here
precisely because `not_isCrookedSeq_neg` has nothing to bite on.

The fold is explicit, and it is the batch-24 phase device carried one step further. Let
`nascPhase f j` be the number of non-ascending steps up to `j`, **capped at two**. The ascending
assignment is

```
aVal = min 3 (max 0 (f j + nascPhase f j − (L + 3)))
```

— three lifts of the level, chosen by how much descent the arm has already done — and the
descending assignment is `bVal = 3 + max (L + 4 − f j) 0`, which is valid at every level of the
band. The whole fold is `aVal` up to one switch index and `bVal` after it. The switch is the
first index `s` with `L + 4 ≤ f s` and `2 ≤ aVal (s−1)`, and `LowLate` is exactly what makes such
an `s` exist before the arm's first visit to `L`: in the first clause the arm has been at `H − 1`,
so `aVal` has already reached `2`; in the second it has dropped two levels, so the phase is `2`
and `aVal` reaches `2` at level `L + 3`.

**The crooked half is one application of the crookedness clause.** `span6_dichotomy`: at any
basepoint of any faithful crooked sequence, either both arms are `LowLate` or both arms are
`HighLate`. Given an `H`-time `b` before the basepoint and an `L`-time `a` after it, the clause
supplies `b < r < r' < a` with `ρ r ≤ L + 1` and `ρ r' ≥ H − 2`; whichever side of the basepoint
`r` falls on, one of the two arms is handed the condition it was missing. Four such facts — two
of them pure logic, since one arm cannot fail both conditions — give the dichotomy. It is stated
and proved for **every** span, not only six; what is special about six is that the two walks then
serve.

This respects the record of what is refuted. The walk is not chosen from a family indexed by the
band (`notConstantOnBand`): it is chosen by a property of the *sequence*, and the census below
confirms that no single walk of length up to twelve serves every span-six basepoint. The arms are
not treated separately (`no_common_walk_pairA_pairB`): the dichotomy is the only place they meet,
and it uses a pair of times on opposite sides of the basepoint. Nothing is extended by two outer
legs (`not_extendStepMin`).

## 2. The census

`census-batch37.py`, output in `census-batch37.log`.

1. **The dichotomy, independently checked.** Every interior basepoint of every stretch of
   `bing 0 6`, `bing 0 7`, `bing 0 8` whose band is exactly six wide — **3 140 452 instances** —
   satisfies it; 2 479 908 are `LowLate` on both arms, the same number `HighLate` on both, and
   1 819 364 are both. Failures: **0**.
2. **The explicit assignment.** For every 1-Lipschitz `LowLate` arm of length at most fourteen —
   **1 271 062 arms** — the assignment the Lean proof constructs is a fold onto `walk6`.
   Failures: **0**.
3. **All lengths, exactly.** A reachability search over (level, fold-DP mask, predicate state)
   decides, for arms of *every* length at once, whether a walk serves every arm satisfying a
   condition. `walk6` serves every `LowLate` arm and `walk6'` every `HighLate` arm; of all walks
   of length at most eleven based within one of the basepoint, exactly twelve serve every
   `LowLate` arm, and all of them extend `walk6`.
4. **The route that is closed.** If one is content with the weaker witnesses the crookedness
   clause yields in one shot — "reaches `H − 2` before `L`" — then **no walk of length at most ten
   serves every arm satisfying it**, and this stays true after imposing local crookedness on every
   window of size up to six. So the two-clause form of `LowLate` is not a convenience: the
   one-clause form with the weaker threshold has no walk at all, and the dichotomy must deliver
   the `L + 1`-then-`H − 2` pattern, which is exactly what the crookedness clause gives.
5. **Two negative facts.** (a) No walk of length at most twelve serves every one of the 8 097
   distinct interior arm pairs of the corpus; `walk6` alone serves 6 615 of them, `walk6'` alone
   the same number, and the pair serves all 8 097. (b) **Neither arm folds onto the other arm's
   own trace** at 870 of those instances — so "fold one arm onto the other" is not a route, at any
   span; it already fails at span five (2 of 30 basepoints of `bing 0 5`) and at span eight at 116
   of 409.

## 3. What was attempted and abandoned

* **A universal walk for the interior level.** Abandoned within an hour: §5 of the census, and
  `notConstantOnBand`, agree that the walk must depend on the sequence.
* **"One arm folds onto the other."** The cheapest sequence-dependent rule there is, and false;
  §5(b). Recorded because it is the first thing one tries once the family approach is refuted.
* **The one-clause `LowLate`.** Abandoned on the evidence of §4, which is what pushed the
  argument to the two-clause form the crookedness clause actually supplies.
* **Span seven and beyond.** Not attempted in Lean. The obstruction is visible: at span seven the
  interior levels are `L+3` and `L+4`, and the reversal law says the least number of turning
  targets grows as `⌊span/2⌋ − 1`, so a two-walk dichotomy cannot survive indefinitely. What the
  span-six proof suggests for the induction is that the right inductive datum is not a *walk* but
  a *pair of conditions on the arms* that (i) some walk serves and (ii) the crookedness clause can
  always deliver on one side or the other. The second half is span-independent — `span6_dichotomy`
  is proved for every span — and it is the first half that needs a family of walks growing with
  the span.

## 4. Not in this batch

Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check.
