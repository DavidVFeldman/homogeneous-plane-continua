# Report: batch 27 — the banding obstruction, and `Tracking`

One new file, `HPC/Fold/Cut.lean`; `HPC.lean` updated with its import. Nothing else in the
project was touched. The whole project builds. `HPC/Fold/Cut.lean` contains no `sorry`,
`admit`, `axiom`, `native_decide` or `@[implemented_by]`, and produces no linter warnings; every
theorem in it has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`. The census
script is `census-batch27.py`.

## 1. Counterexamples

**No counterexample to `LexCutExists` was found, and none is claimed. No counterexample to
`Tracking` was found, and none is claimed.**

`LexCutExists`, over contiguous subchains of `bing 0 8` (every pair of endpoints on a grid of
five) and 4 000 random subchains of `bing 0 10` of length at most 260 — 6 722 subchains of span
at least four in all:

* a `LexCut` exists in every case;
* still in every case when the cut points are additionally required to sit at crookedness
  witnesses, `ρ r ≥ H − 2` and `ρ r' ≤ L + 2`;
* raising the threshold to *three* levels per piece fails at 60 of the 6 722 subchains, 0.89%.
  (The commission reports 2.3% on its own corpus; the direction is the same — the threshold
  three is not available — and the exact rate is corpus-dependent.)

`Tracking` was censused in the instance the delivered proof actually uses (§4): at the
three-point window `[a, a+2]` of a chain, with the one-time walk whose value is the window's
centre `v`, is there an extension onto which the suffix from `a + 2` and the reversed prefix up
to `a` both fold from time `0`? Over all 8 107 windows of `bing 0 4 … bing 0 8`, of `cutSeq`,
and of 60 random subchains of `bing 0 10`, the answer was yes in every case, deciding folding
exactly by bitmask reachability and searching zigzag walks through `v` with up to four turning
targets: 1 201 windows needed one turning target, 5 887 two, 1 015 three, 4 four.

## 2. The obstruction — delivered in full

`cutSeq` is `bingPath 0 8` restricted to `[355, 391]`: thirty-seven links, span four on levels
`3 … 7`, attaining `3` at indices 0 and 24 and `7` at 12 and 36, visiting `L, H, L, H` in that
order. Proved:

* `cutSeq_isLip`, `cutSeq_bounds`, `cutSeq_attains` — kernel evaluation and index arithmetic.
* `cutSeq_faithful : IsCrookedIvF cutSeq cutSeq` — **the far-index method of batch 25 carried
  over directly**, as the commission expected: `cutLevHas` / `cutFirstLev` / `cutFirstVal` /
  `cutCheckOne` at thirty-seven links and levels `0 … 7`, with `cutCheckAll_true` by
  `decide +kernel` (a second or two, against minutes at 409 links). The one change is the
  numeral: at this length a `List` of the levels read by `List.getD` is cheaper than a
  base-sixteen numeral read by shift and mask, so `cutRho` is a list lookup.
* `cutSeq_no_three_cut` — **by `decide`**, not by certificate. `decide +kernel` over
  `r, r' < 36` evaluates all 595 pairs; the per-pair certificate was not needed. (The
  out-of-Lean census confirms the shape the commission predicted: every pair does have a piece
  carrying both `3` and `7`, the first piece for 276 pairs, the last for 187, the middle for
  132.)
* `no_three_banded_cut_in_general` — the existential, witnessed by `cutSeq` with `L = 3`,
  `H = 7`.

**`spanOn`: what was supplied.** The commission's `spanOn` was a `Finset.sup'` minus a
`Finset.inf'`, each with a nonemptiness side condition left as `sorry`. Rather than carry the
side conditions as hypotheses, `spanOn` here is total: it takes the largest minus the smallest
of `levelsOn ρ a b`, the list of levels of `ρ` at the indices of `[a, b]`, and is `0` on an
interval that meets no index. On a nonempty interval this is the commissioned value. It
evaluates in the kernel, which is what `cutSeq_no_three_cut` needs, and it carries the one
lemma the rest of the file uses, `sub_le_spanOn`: every difference of levels on the interval is
at most the span. `LexCut`, `LexCutExists` and the statements of §2 are otherwise verbatim.

## 3. The measure that survives

`LexCut`, `LexCutExists` and `Tracking` are recorded verbatim as definitions, with no theorems
beyond §2, as commissioned. One presentational change to `Tracking`: the three hypotheses on
the cut points are written as named binders, `(_hri : r < i.val) → …`, rather than bare arrows,
because Lean elaborates the right-hand side of a bare `→` without the antecedent in scope and
the index-bound obligations inside the statement (`ρ ⟨i.val + j.val, _⟩` and the rest) need
them. The proposition is unchanged.

## 4. `s3_of_tracking` — proved, at **all three** positions of the basepoint, by a route that
does not use the induction

`s3_of_tracking (_h1 : LexCutExists) (h2 : Tracking) : S3` is proved, `sorry`-free. It does not
go by induction on `(H − L, n)`, and it does not use `LexCutExists`, which is kept in the
statement only because the commission asked for it.

The reason is worth stating plainly, because it is a fact about the formulation of `Tracking`
rather than a trick:

> **`Tracking` may be instantiated at a three-point window, and then it already is `S3`.**

Take any three consecutive indices `[a, a+2]` with `a + 3 < n`, and apply `Tracking` with
`i = a+1`, `r = a`, `r' = a+2`. Three consecutive levels of a 1-Lipschitz sequence span at most
two, so a single level `v = min (H−1) (m+1)`, with `m` the least of the three, is within one of
all three and lies in `[L+1, H−1]` (`window_center`). So take `len = 1` and `c ≡ v`: both of
`Tracking`'s hypotheses on the middle piece's arms are satisfied by the constant time
assignment, with `uG = uT = 0`. Its conclusion is then exactly that the suffix from `a + 2` and
the reversed prefix up to `a` fold from time `0` of one common extension of that walk
(`tracking_window`).

From that, every basepoint of the window is immediate (`s3_at_window`): the basepoint's two
arms each consist of at most three links inside the window — all carried by the one time `0` —
followed by one of the two conclusions, and `foldsFrom_split` glues them. Every basepoint
`b ≤ n − 2` lies in such a window (`a = min b (n−4)`, and `n ≥ 4` follows from the span), so
the *left*, *middle* and *right* positions all go through. The last basepoint, `b = n − 1`, is
the one position not inside any window with `a + 3 < n`; it follows from the basepoint `n − 2`
by prefixing one fresh time to the walk, at the value the forward arm of `n − 2` reaches
`ρ (n−1)` on (`foldsOnto_cons`).

Two consequences for the programme:

* **`Tracking` is not a gluing step sitting on top of an induction.** Being able to extend an
  arbitrary given walk is strong enough that the induction, the cut and `LexCutExists` are all
  bypassed. In particular `Tracking` is at least as hard as `S3`; a proof of `Tracking` would
  be a proof of Bing's Theorem 3 in the block reading, and the commission's expectation that it
  will resist is, on this evidence, the right one.
* **The obstruction of §2 is unaffected.** It says what it says about banded cuts, and it is
  independent of how `S3` is eventually obtained.

The census of §1 is therefore also a census of the only instance of `Tracking` the delivered
proof consumes; it found no failure.

## 5. Not in this batch

`LexCutExists` as a theorem; `Tracking` as a theorem; `s3`; the linear-time far-index check
that would make `¬ F2PrimeOff` unconditional; Bing 1948 Theorems 4, 5, 6; the reduction in Bing
1951; the D8/D9 gap.
