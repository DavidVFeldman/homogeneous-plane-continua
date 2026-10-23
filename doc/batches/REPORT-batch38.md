# Report: batch 38 — span seven, one case short

One new file, `HPC/Fold/Span7.lean`, containing the two commissioned statements unchanged (with
their `sorry`s) and everything the run proved; root `HPC.lean` updated; `README.md` notes the
batch. Nothing else is touched — the forty-six earlier Lean files are byte-identical to the
batch-37 delivery. The census program is `census-batch38.py`, its output `census-batch38.log`.

## 0. No counterexample, and what is new

**No counterexample to `theorem3` was found**, and nothing in this run suggests one. Both
commissioned targets, `s3_span_seven` and `theorem3_span_seven`, keep their `sorry`.

What the run does deliver is a generalisation of *both* halves of the batch-37 method, and a
theorem that is not about span seven at all:

> **`s3_span_seven_of_cases`.** At **every** span, a basepoint of a faithful crooked sequence is
> served unless both arms are simultaneously `HighAt (ρ i − 3) H` and `LowAt L (ρ i + 3)`.

At span seven that is the only case left. Everything is `sorry`-free with axiom profile inside
`propext`, `Classical.choice`, `Quot.sound`.

## 1. The crooked half, at arbitrary levels

`span6_dichotomy` was already span-independent, but its levels were pinned to the two extremes of
the band. Freeing them costs nothing in the proof and is what makes several applications of the
crookedness clause available at one basepoint:

```
LowAt  f tl th : for every d with f d ≤ tl, either f reaches th before d,
                 or f reaches tl+1 and afterwards th−2, both before d
HighAt f tl th : for every d with f d ≥ th, f reaches tl+1 before d

dichotomy_at : tl + 3 ≤ th →
  (LowAt (armG ρ i) tl th ∧ LowAt (armT ρ i) tl th) ∨
  (HighAt (armG ρ i) tl th ∧ HighAt (armT ρ i) tl th)
```

Two further economies fell out of the proof. `HighAt` is **one clause**: the second clause of
batch 37's `HighLate` is never used — not in the two crooked lemmas, not in the pure-logic one.
And `LowAt`'s first clause can ask for `th` rather than `th − 1`, because `not_lowAt_highAt` only
needs the `HighAt` trigger to be at least the `LowAt` witness level. Both make the conditions
*stronger*, which is what the folding half wants; `LowAt L H` implies batch 37's `LowLate`.

The triggers are inequalities (`f d ≤ tl`) rather than equalities. This costs nothing in the
dichotomy — the crookedness clause is applied at the actual level of the trigger index — and it
removes the need for a discrete intermediate-value step when the trigger is not an extreme of the
band, which is exactly what happens at the basepoint `L + 4` of a span-seven band.

## 2. The folding half: a greedy assignment, and one switch condition

Batch 37's ascending assignment lifted the level by the number of non-ascending steps, capped at
two. That cap is what fails at span seven: the walk's ascending leg is one longer, and the phase
device cannot reach its last two times except after two descents. The replacement is the **greedy**
assignment — the largest legal time — which has a closed form:

```
runMin f j = min over k ≤ j of (f k − k)
ascVal f p H j = min (H − p) (min j (runMin f j + j − p + 2))
descVal f p H j = (H − p) + max (H − 2 − f j) 0
```

`bumpWalk p H` is the one-bump walk `p−1, p, …, H−1, H−2, …, L+1` (peak index `A = H − p`), and

> **`foldsOnto_bumpWalk_of_switch`.** A 1-Lipschitz arm in `[L, H]` based at an interior level `p`
> folds onto `bumpWalk p H` as soon as: *before the arm ever falls to `p − 3` there is a time
> `s ≥ H − p` at which it stands at `H − 2` or above.*

Three things are worth recording about this statement.

* It mentions no crookedness, so its reflection `foldsOnto_bumpWalk'_of_switch` is free —
  legitimate exactly where `not_isCrookedSeq_neg` has nothing to bite on.
* It is **span-free and basepoint-free**: the same theorem covers span six, span seven and beyond.
  At span six the batch-37 condition `LowLate` implies the switch condition, so the greedy
  assignment subsumes the phase device.
* The switch condition is purely about *time*: `s ≥ H − p` is the statement that the arm has had
  room to climb. The two bridges `switch_of_lowAt` and `switch'_of_highAt` are then short: from
  `LowAt tl H` with `p − 3 ≤ tl ≤ p − 2`, the first clause gives a time at level `H` — necessarily
  at least `H − p` — and the second gives a time at `tl + 1 ≤ p − 1` followed by one at `H − 2`,
  which is at least `H − p − 1` steps later and at least one step after the start.

## 3. What is settled

```
s3_of_lowAt   : ρ i − 3 ≤ tl ≤ ρ i − 2 → both arms LowAt tl H       → served
s3_of_highAt  : ρ i + 2 ≤ th ≤ ρ i + 3 → both arms HighAt L th      → served
s3_of_not_highAt : ¬(both arms HighAt (ρ i − 3) H)                  → served
s3_of_not_lowAt  : ¬(both arms LowAt L (ρ i + 3))                   → served
s3_span_seven_of_cases : ¬(both HighAt (ρ i − 3) H ∧ both LowAt L (ρ i + 3)) → served
```

all at every span, with only `L + 3 ≤ H`; near-extreme basepoints are handed to
`s3_near_extreme`. The four dichotomy instances the method can use are `(p−3, H)` and `(p−2, H)`
on the `LowAt` side and `(L, p+2)`, `(L, p+3)` on the `HighAt` side; since `HighAt (p−3) H` implies
`HighAt (p−2) H` and `LowAt L (p+3)` implies `LowAt L (p+2)`, the residue of all four is the single
conjunction above. So `s3_span_seven_of_cases` is the strongest statement this method yields.

At span seven the interior levels are `L + 3` and `L + 4`, and the walks are

```
p = L+3 : L+2, L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1
p = L+4 : L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1
```

together with their reflections. Four walks at span seven against two at span six — the growth the
reversal law predicts.

## 4. The census

`census-batch38.py`, output in `census-batch38.log`.

1. **The dichotomy at arbitrary levels, independently checked.** Every interior basepoint of every
   stretch of `bing 0 7` and `bing 0 8` whose band is exactly seven wide, at every admissible level
   pair — **701 743 instances** — satisfies it. Failures: **0**.
2. **The bridge and the explicit fold.** For every 1-Lipschitz arm of length at most fourteen at
   `p = 3` satisfying `LowAt (p−3) H` or `LowAt (p−2) H` (**1 451 944** arms) the switch condition
   holds, and for every arm satisfying the switch condition (**1 463 371** arms) the greedy
   assignment the Lean proof constructs is a fold onto `bumpWalk`. The same at `p = 4`, with
   1 280 299 and 1 348 557 arms. Failures: **0** throughout.
3. **All lengths, exactly.** A reachability search over (level, fold-DP mask, predicate state)
   confirms that `bumpWalk` serves every arm satisfying the switch condition, at every length —
   and that it is the **only** walk of its length that does, at both interior basepoints.
4. **Which classes have a walk.** For each admissible level pair, whether one walk of length at
   most twelve serves every arm of the class. The servable ones are exactly the ones the Lean file
   uses (plus two with a lower `th` on the `HighAt` side, which are implied). In particular
   `LowAt (0,6)` and `HighAt (0,7)` are served by **no** walk of length at most twelve, which is
   the census form of the obstruction the theorem above leaves open.
5. **At span six the old condition implies the new one.** For all **1 271 062** `LowLate` arms of
   length at most fourteen in `[0, 6]` at the interior basepoint — batch 37's own corpus — the
   switch condition holds. Failures: **0**.
6. **The leaf, and why crookedness must enter.** Taking the unservable side of every dichotomy at
   `p = 3` leaves `HighAt(0,7) & LowAt(0,6) & …`. Two arms in it,
   `[3,2,3,2,1,2,3,4,5,6,7]` and `[3,2,3,2,1,2,3,4,3,2,1,0]`, fold onto no common walk of length at
   most thirteen — and **neither is internally crooked**. So the leaf cannot be closed by
   conditions the one-shot dichotomy delivers; the arms' own crookedness has to be used.

## 5. What was attempted and abandoned

* **A second walk family for the leaf.** The class that survives all eight dichotomies at `p = 3`
  is served by a two-bump walk of length twelve, `[3,4,5,4,3,2,1,2,3,4,5,6]`, on the branch where
  the `(1,6)` dichotomy lands `LowAt` — and by no walk of length at most thirteen on the branch
  where it lands `HighAt` (census §4b). A two-bump walk needs two switches and eight conditions in
  the folding lemma; with one branch not served at all, the route was dropped.
* **Shrinking the band.** If neither arm of the leaf ever reached an extreme, the band would shrink
  to `[L+1, H−1]`, where both interior levels are near-extreme and `s3_near_extreme` finishes — a
  clean way to close span seven. A depth-first search over *internally crooked* arms of the leaf
  classes (census §5) found none of length at most sixteen reaching an extreme on the two branches
  with `LowAt(1,6)`, but did find one on each branch with `HighAt(1,6)`:
  `[3,2,3,2,1,2,2,3,4,3,2,2,1,2,1,0]`. So the route closes two of the four branches at best, and
  even there only as unproved evidence; it is recorded, not used.
* **Imposing local crookedness by windows, as in batch 37 §4.** The obstructing arms of §5 violate
  crookedness only over windows of width eleven and twelve, so window constraints of the size that
  keeps the reachability automaton finite do not remove them.

## 6. The outlook

The remaining case is sharply delimited and is now a statement about a *single* conjunction of two
conditions, at every span:

> both arms `HighAt (ρ i − 3) H` and both arms `LowAt L (ρ i + 3)`.

Two things about it are known from this run. It is not reachable by one more application of the
crookedness clause at another level pair — every such pair has been enumerated, and the eight at
`p = 3` leave the leaf of §5. And it cannot be settled by any walk chosen without using the arms'
own crookedness, because the two arms of §5 satisfy every condition the dichotomies deliver and
have no common walk. The next step is therefore a folding lemma whose hypothesis is *crookedness
of the arm*, which is available (`isCrookedIvF_restrict`); the price is that the reflected case
can no longer be got by reflecting the arm, since the crookedness clause is not symmetric — its
witnesses are at `k + 1` and `h − 2`. The symmetric weakening (`k + 2`, `h − 2`) still kills both
arms of §5, so a reflection-invariant crookedness hypothesis is available if it is wanted.

## 7. Not in this batch

Spans eight and above; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time
far-index check.
