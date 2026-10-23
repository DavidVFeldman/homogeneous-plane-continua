# Report — batch 48: the two halves of the branch at `L + 4`

Runs on top of the batch-47 delivery, under `COMMISSION.md` (batch 48; the previous commission is
archived as `COMMISSION-batch47.md`). `lake build HPC` succeeds. Everything new that is proved is
`sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`.

**No counterexample to a target.** Nothing in this batch refutes any statement of the
development, and no statement is withdrawn. The first target is now a theorem; the second is cut
down to two statements across the basepoint, of which the unconditional part is also a theorem.

Files touched: `HPC/Fold/Leg3Profile.lean` (the first target and the new arm-only lemmas),
`HPC/Fold/Mixed.lean` (the re-split of the second), `HPC/Fold/General.lean` (state of play in the
docstring only). No new Lean file; `HPC.lean` unchanged. New censuses: `census-batch48.c`,
`census-batch48b.c`, with their logs.

## 1. The targets, in order

### 1.1 `foldsOnto_leg3deep_profile` — **proved**

A 1-Lipschitz arm in `[L, L + 9]` based at `L + 4` that satisfies `Leg3Valley` and `Leg3Ceil`
folds onto `leg3Walk L (L+9) (L+6) (L+4)`, the walk `L+3 → L+6 → L+1 → L+8`. Arms alone: no
crookedness, no pairs.

The engine of `HPC/Fold/Leg3Deep.lean` cannot prove it, and not for want of effort: its four
features `E`, `E2`, `R`, `S` are *history* predicates, and the closure rules
(`gseq3_inv_deep`) let a feature switch on only when the arm stands at the peak level `K` or at
`K - 1` after a visit to the valley. The profile clauses switch a feature on from `K - 1 = L + 5`
with no visit to the valley, at the price of an index. So the batch replaces the four features by
four **numerical invariants on the greedy time** `q t = gseq3 L (L+9) (L+6) (L+4) u t`, and it is
the clock — the walk advances at most one position per step, so its position at step `t` is at
most `t` — that pays for the missing level. Writing `a t = u t − L`:

* **the clock** `min (min t (a t − 2)) 3 ≤ q t`. Before the greedy time reaches the peak position
  `3` it is at least the arm's own first-leg position `a t − 2`, and at least the step count. At a
  step `t ≥ 3` where the arm stands at `L + 5` or above this gives `q t ≥ 3`, which is exactly the
  `R` bound there — and that is the whole of the clause `3 ≤ j`.
* **`R`**: `8 − a t ≤ q t`, once triggered, for ever. Propagation is the engine's clause `p6`.
* **the slack clock**: for every landmark `j` (`3 ≤ j`, `a j ≥ 5`) and every `t ≥ j`,
  `min (min (10 − a t) 8) (t − j + 3) ≤ q t`. Past the peak the greedy time gains one walk
  position per step until it reaches the far end `min (10 − a t) 8` of the descending leg; the
  advance is forced because the greedy time is then inside the second leg and one short of its
  window. Five steps carry it from the peak position `3` to the valley position `8`, and that is
  the whole of the clause `j + 5 ≤ k`.
* **`S`**: `a t + 6 ≤ q t`, once triggered, for ever (clause `p9`). It is triggered at a step `k`
  with `a k ≤ 2` reached by the slack clock, since `min (10 − a k) 8 ≥ a k + 6` there.

`prog3_profile` is the one-step lemma for the four — five implications proved from
`gstep3_facts` exactly as `prog3_deep` is — and `gseq3_inv_profile` the induction. The
announcements enter only as they do in the engine: a descent to `L + 1` at `t + 1` needs the `R`
bound at `t`, an ascent to `L + 8` needs the `S` bound at `t`.

**The criterion survives with room to spare.** The proof consumes two of the criterion's four
index bounds, and `foldsOnto_leg3deep_profile_min` states the fold from the two:

```
Leg3ValleyMin : ∀ d, f d ≤ L+1 → ∃ j, 3 ≤ j ∧ j < d ∧ L+5 ≤ f j
Leg3CeilMin   : ∀ d, L+8 ≤ f d → ∃ j k, 3 ≤ j ∧ j+5 ≤ k ∧ k < d ∧ L+5 ≤ f j ∧ f k ≤ L+2
```

The bounds `j + 5 ≤ d` and `k + 6 ≤ d` are never spent, because a landmark once reached is kept:
the `R` and `S` bounds propagate from the landmark to the event at no cost. The commissioned
statement is a one-line corollary. Over the census corpus the sharpened clauses fail on exactly
the same arms as the commissioned ones (26 819 of each), so the slack costs nothing and buys
nothing there — but it is the form a later batch should use.

### 1.2 `unserved_profile` — **cut down to two statements across the basepoint**

Two new arm-only theorems, in `HPC/Fold/Leg3Profile.lean`, say that a *failure* of a profile
clause is never the fault of the arm that exhibits it:

* `leg3Valley_or_vee` — an arm of the branch either satisfies `Leg3Valley` or folds onto the
  V-walk based at `L + 5`, by itself. The failing descent `d` is the witness the V-profile asks
  for (`crookDown_fall3` puts it at index four or later); an ascent to `L + 7` before `d` is
  impossible, because it would be six levels above `d` in fewer steps than 1-Lipschitz allows, and
  its own index would land inside the window where the failure forbids `L + 5`.
* `leg3Ceil_or_lam` — an arm either satisfies `Leg3Ceil` or folds onto the Λ-walk based at `L + 3`.
  The failing ascent `D` is the peak witness the Λ-profile asks for (`crookUp_climb4` puts it at
  index seven or later); a descent to `L + 1` before `D` is impossible, because one application of
  `CrookUp` between the two produces a time at `L + 6` or above followed by one at `L + 2` or
  below, and the three timing laws (`crookDown_fall3`, `crookDown_fall4`, `crookUp_climb5`) place
  them exactly where `Leg3Ceil` asks: index four or later, seven apart, twelve before `D`.

Two consequences, in `HPC/Fold/Mixed.lean`.

* **`unserved_profile_one`, proved**: an unserved pair of the branch has an arm satisfying
  `Leg3Valley` and an arm satisfying `Leg3Ceil` — possibly different arms. If both arms failed the
  same clause, both would fold onto the same canonical walk and the pair would be served by it.
  Neither `HighAt` hypothesis and neither end of the band is used.
* **What is left is exactly two statements across the basepoint**, and `unserved_profile` is now a
  derivation from them rather than a `sorry`:
  * `cross_valley_profile`: if either arm fails `Leg3Valley`, *both* arms fold onto the V-walk;
  * `cross_ceil_profile`: if either arm fails `Leg3Ceil`, *both* arms fold onto the Λ-walk.

  Neither says anything about the arm that fails — that half is now a theorem — so both are
  statements of the kind `crookUp_seq`, `cross_floor_excluded` and `mix_events_far` are there for.
  This is the sharpest split the branch has had: batch 44 left two announcements (both refuted in
  batch 46), batch 47 left one statement with an arm-only half and a pair half, and batch 48 leaves
  only the crossing.

The censuses exercise the two items hard and find no exception; `cross_valley_profile` is met at
50 296 branch basepoints, and `cross_ceil_profile` is never triggered at all, since no arm of the
corpus fails `Leg3Ceil` (see §3).

Where the difficulty now sits, precisely: an arm `X` failing `Leg3Valley` has a first descent `d`
to `L + 1` with `X ≤ L + 4` at every step from `3` to `d`, and the crookedness clause applied
across the basepoint between that descent and an ascent of the other arm `Y` to `L + 7` does
deliver a time of `Y` at `L + 2` or below before the ascent — the link the clause returns cannot
lie on `X`, because `X` is too low, nor at `X`'s first three steps, because those are too high.
What the clause does not deliver is the *index*: the V-criterion wants that low time at index four
or later, and the clause can place it at index two or three. That single index is what
`cross_valley_profile` is now worth.

### 1.3 `s3_span_nine_mid5` — not proved; see question 2 below.

### 1.4 `s3_span_nine`, `s3_general` — not proved

`s3_span_nine` is `s3_span_nine'` (`HPC/Fold/Mixed.lean`), which holds as soon as the two branch
statements do; it is left as a work item rather than a derivation, so that the `sorry` count keeps
saying what is open. `s3_general` waits on the spans ten and above, which this commission puts out
of scope, so `theorem3` is untouched.

## 2. The questions

### 2.1 Does the criterion survive the proof?

Yes, and it survives with slack: two of its four index bounds are never used
(`foldsOnto_leg3deep_profile_min`, §1.1). No clause needed adjusting, so no re-checking against
`census-batch47c.c` was required; the new census re-checks both forms anyway, and they fail on
exactly the same arms of the corpus.

### 2.2 Is `s3_span_nine_mid5` the reflection of `s3_span_nine_mid4`?

**No — not by `isCrookedIvF_reflect_general` alone, and the obstruction is twofold.** Reflection in
`a = 2L + 9` sends a faithful pair `(ρ, σ)` to `(a − σ, a − ρ)`.

1. *The basepoint moves off the branch.* The reflected point sequence is `a − σ`, and at the
   basepoint `i` of the branch `L + 5` it stands at `a − σ i`, which is `L + 4` exactly when
   `σ i = ρ i`, that is when the link at `i` is thin. At a non-thin basepoint — and filling a
   valley (`isCrookedIvF_fill`) makes non-thin links wherever one likes, moving no point of `ρ` —
   the reflected basepoint stands at `L + 3`, and `s3_span_nine_mid4` does not apply to it.
2. *The conclusion is about the wrong sequence.* Even at a thin basepoint, `s3_span_nine_mid4`
   applied to the reflected pair folds the arms of its point sequence `a − σ`, whereas the branch
   `L + 5` asks for folds of the arms of `a − ρ`. These differ pointwise by `σ − ρ ∈ {0, 1}`, and
   that difference is not free: `exists_blocks_first_of_folds_max` (`HPC/Fold/LinkFold.lean`,
   batch 47) is the exact statement of what a fold read on the upper ends costs, namely one link.
   A fold of `a − σ` with window one gives only a window-two statement about `a − ρ`.

   `isCrookedIvF_sig_isLip` does not close this: it says the reflected point sequence is again
   1-Lipschitz, so every *criterion* of the development can be read on it, but it says nothing
   about transporting a fold from one sequence to another one level away.

So the branch `L + 5` needs its own argument in the general model. For a **thin** sequence the
reflection does work, and that is exactly `s3_span_nine_mid5_thin` (`HPC/Fold/ThinSpan9.lean`),
which is the diagonal case `σ = ρ` of the general reflection. What the mirror argument would need
is the reflected copy of the whole batch-44 to batch-48 development — the reflected three-leg
engine (`leg3Walk'` of `HPC/Fold/Span8.lean` is the walk), the reflected profile criterion, and the
reflected cross items — and none of it follows formally from the `L + 4` case.

### 2.3 The general form of the criterion

The sentence, written out for an arbitrary zigzag walk `w` with landmarks (turning points) at
positions `p_1 < … < p_T` and levels `l_1, …, l_T`:

> for every step `d` of the arm let `u(d)` be the earliest position of the walk that serves the
> arm's level there, and let `r` be the number of landmarks strictly before `u(d)`; then there are
> steps `j_1 < … < j_r ≤ d` with the arm within one of `l_s` at `j_s` (one-sidedly: at or above
> `l_s − 1` at a peak, at or below `l_s + 1` at a valley), with
> `j_s ≥ j_{s−1} + (p_s − p_{s−1})` and `d ≥ j_r + (u(d) − p_r)`.

Both criteria of the development are instances: for `w = p → κ → L+1` it is the Λ-criterion
`CritLamProfile`, and for `w = L+3 → L+6 → L+1 → L+8` it is `Leg3Valley` together with `Leg3Ceil`
(at the valley the general sentence asks `d ≥ j + 4` where `Leg3Valley` asks `d ≥ j + 5`, because
the walk already serves `L + 1` from its position `7`).

`census-batch48b.c` tests the sentence over **54 zigzag walks** in `[0, 9]` with one, two and three
turns: exhaustively over every 1-Lipschitz arm of length at most thirteen starting within one of
the walk's first level, and over 50 000 random arms of length up to sixty per walk —
**113 019 462 arms in all**. The answer, as far as a census can give one:

* **no arm meets the sentence and fails to fold**, for any of the 54 walks; and
* **no arm folds without meeting the sentence** either. On this corpus the sentence is not merely
  sufficient: it *is* the fold.
* Every arm meeting `Leg3Valley ∧ Leg3Ceil` meets the sentence (0 exceptions), and 3 596 arms of
  length at most thirteen meet the sentence without meeting those two clauses — the sentence is
  strictly weaker than the criterion this batch proved sufficient, which is consistent with both.

So the answer to the question as asked is yes, on the evidence; and the stronger reading — that the
sentence characterises the fold for an arbitrary zigzag walk — is what the census actually shows.
A proof would be a general engine, and the proof of §1.1 is written so that it could become one:
the clock, the `R`/`S` bounds and the slack clock are the same four invariants for any walk, with
the landmark positions as their constants. Nothing in this batch proves the general statement.

## 3. The census

`census-batch48.c` (log: `census-batch48.log`). The **general** model. Two base chains, the Bing
chain of span nine `bing 0 9` (986 links) and the same chain run the other way, `bing 9 0`; time
reversal is not a symmetry of the crookedness clause, so this is a second corpus and not a
relabelling. Three generators:

| generator | pairs | non-thin links |
|---|---|---|
| the thin chains themselves | 2 | 0 / 1 972 |
| **shaving** a peak (`ρ` lowered by one at a strict local maximum) | 576 | 576 / 567 936 (0.10 %) |
| **filling** a valley (`σ` raised by one at a strict local minimum) | 576 | 576 / 567 936 (0.10 %) |
| random mixtures of the two | 800 | 154 087 / 788 800 (19.5 %) |

Filling is the generator `isCrookedIvF_fill` of batch 47, used here for the first time: it moves no
point of `ρ`, so it changes no walk criterion, and every one of the 576 fills is faithful. Every
pair is verified against the definition `IsCrookedIvF` before it is used, and every fold is decided
exactly by the dynamic program over `FoldsOnto`.

At each of the **180 609** branch basepoints (`ρ i = L + 4`, both arms `HighAt (L+1) (L+8)`):

* `leg3Valley_or_vee` confirmed 56 863 times, no exception; `leg3Ceil_or_lam` never triggered,
  because **no arm of the corpus fails `Leg3Ceil`** — its failure is a rarer event than the census
  reaches, which is also why `cross_ceil_profile` is untested there.
* **`cross_valley_profile`: 50 296 tests, no exception.** At every basepoint where an arm fails the
  valley clause, both arms fold onto the V-walk.
* `unserved_profile`: holds at all **44 450** unserved basepoints; `unserved_profile_one`, now a
  theorem, is confirmed at every one of them.
* The sharpened clauses `Leg3ValleyMin`, `Leg3CeilMin` fail on exactly the same arms as the
  commissioned ones (26 819 of each over the mixtures).

`census-batch48b.c` (log: `census-batch48b.log`) is the general-shape census of §2.3.

## 4. What is left

* The branch `L + 4`: `cross_valley_profile` and `cross_ceil_profile`, and nothing else. The first
  is about one index — see the end of §1.2 — and the second has no witness in any census.
* The branch `L + 5`: its own argument, the mirror of batches 44–48, since reflection does not
  reduce it (§2.2).
* With both branches, `s3_span_nine` follows from `s3_span_nine'`; `s3_general` waits on spans ten
  and above.
