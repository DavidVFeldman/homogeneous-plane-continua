# Report: batch 36 — shortest serving walks, gated

One new file, `HPC/Fold/Minimal2.lean`; root `HPC.lean` updated; `README.md` notes the batch.
Nothing else is touched — the forty-four earlier Lean files are byte-identical to the batch-35
delivery. The census program is `census-batch36.c`, its output `census-batch36.log`.

## 1. The gate, first: it fails, and it fails at span six

> **Census `ExtendStepMin` at spans 9, 10, 11 and 12 — every interior basepoint of `bing 0 n` —
> before any of §§2–3. If it fails, stop, report the failing basepoint with its trims and the
> shortest serving walk that does not extend.**

**It fails, at span six, before the spans the gate names.** The commission's premise — "at every
interior basepoint of `bing 0 6`, `bing 0 7` and `bing 0 8` there is a trim for which every
shortest serving walk extends — 25 of 25, 104 of 104, 319 of 319" — is **not reproduced**. Under
the conventions batches 33–35 fixed (an inner trim is a band `[L', H']` with `L + 1 ≤ L'`,
`H' ≤ H − 1`, `L' + 3 ≤ H'` together with a stretch attaining it; the extension is the oriented
one, the only order that can be a member of the free family of `[L, H]`), the counts are

| span | interior basepoints | MIN passes | SOME passes | EVERY passes | trims whose shortest serving members split |
|---|---|---|---|---|---|
| 6 | 25 | **19** | 25 | 15 | 32 |
| 7 | 104 | **90** | 104 | 70 | 150 |
| 8 | 319 | **281** | 319 | 221 | 458 |
| 9 | 868 | **794** | 868 | 624 | 976 |
| 10 | 2 229 | **2 109** | 2 229 | 1 663 | 1 774 |
| 11 | 5 556 | **5 378** | 5 554 | 4 370 | 3 116 |
| 12 | 13 635 | **13 373** | 13 627 | 11 229 | 5 568 |

* **MIN** is `ExtendStepMin`: at some inner trim, some member serves and *every serving member
  of least walk length* extends.
* **SOME** weakens it to: at some inner trim, *some* shortest serving member extends.
* **EVERY** is batch 34's form, recomputed for comparison.

The restriction to shortest walks is a real gain — the failures drop from 2 406 to 262 at span
twelve — but it does not close the gap, and the first failure is at span six.

**The failing basepoint, with its trims and the walk that does not extend.** Basepoint `5` of
`bing 0 6`, at level `3`. Only two bands carry a trim there:

* band `[1, 4]`, maximal stretch `[1, 28]`: the serving members are `[2, 3, 2]` and `[3, 2, 3]`,
  both of walk length three, which is the least length any member of a band four wide can have.
  `[3, 2, 3]` extends — `[3, 2, 3, 1, 5]` folds both whole arms — and **`[2, 3, 2]` does not**:
  its only extension that is a member of the free family of `[0, 6]` is `[2, 3, 2, 5, 1]`, whose
  walk `2 3 2 3 4 5 4 3 2 1` is at level `2` or above until time five, while the backward arm
  `3 2 1 2 1 0` is at level `0` at index five.
* band `[1, 5]`, maximal stretch `[1, 69]`: the least serving length is four, attained by
  `[3, 2, 4]`, and **it does not extend**: `[3, 2, 4, 1, 5]` has walk
  `3 2 3 4 3 2 1 2 3 4 5`, again at level `2` or above until time five.
* band `[2, 5]`: the maximal stretch containing the basepoint is `[4, 6]`, whose band is `[2, 3]`;
  it does not attain `5`, so it is not a trim.

**This is not an artefact of taking maximal stretches.** Section 1c of the census enumerates
*every* stretch an `IsInnerTrim` allows — every `[a, b]` inside a maximal run of the band,
containing the basepoint and attaining both its extremes — at spans six, seven and eight:
4 874, 65 991 and 919 400 trims. The verdict is unchanged, 19/25, 90/104, 281/319, with the same
first failure. Serving is monotone under shrinking a stretch, so the shortest members above serve
every stretch of their band, and the two bands' least possible lengths are three and four
whatever the stretch.

**The uniqueness question.** The commission asks whether "the *unique* shortest walk" is ever
needed, that is whether there are basepoints where some shortest serving walk extends and another
does not at every trim. **There are, at every span:** the basepoints passing SOME but not MIN
number 6, 14, 38, 74, 120, 176 and 254 at spans six to twelve. Basepoint `5` of `bing 0 6` is one
— the band `[1, 4]` splits exactly as described above. So "shortest" and "some shortest" are
genuinely different, and even "some shortest" fails: two basepoints at span eleven (891 and 4 850)
and eight at span twelve have no inner trim at which any shortest serving member extends.

## 2. The refutation in Lean

`not_extendStepMin` is a theorem, not a census finding. The chain is `hlSeq` of
`HPC/Fold/ValleyFWitness.lean` — seventy-one links, `bing 0 6` exactly, with
`IsCrookedIvF hlSeq hlSeq` already proved there — at basepoint `5`, `L = 0`, `H = 6`, so
`L + 6 ≤ H` and `L + 3 ≤ ρ i ≤ H − 3` both hold.

The proof is the argument above, uniform over the trims:

* `zigWalk_length_ge`: a member of the free family of `[L', H']` has walk length at least
  `H' − L'`. Its last leg crosses the band, `H' − L' − 2` steps, and at least one step precedes
  it (`ampSum_ge_first_add_last`). So the minimality clause of `ExtendStepMin` is satisfied by
  `[2, 3, 2]` in `[1, 4]` and by `[3, 2, 4]` in `[1, 5]` for free — they are as short as the band
  permits, and nothing shorter can be a serving member.
* `foldsOnto_232_of_band`: any sequence inside `[1, 4]` that starts at level `3` or below folds
  onto the walk of `[2, 3, 2]` — a level at `4` is served at time one, everything else at time
  zero. The band clause of `IsInnerTrim` supplies the hypothesis, so `[2, 3, 2]` serves *both*
  arms of *every* stretch of that band at the basepoint.
* `folds_324_armG`, `folds_324_armT` with `foldsOnto_restrict`: explicit time assignments fold
  the forward arm to index sixty-nine and the backward arm to index one onto the walk of
  `[3, 2, 4]`; a trim of the band `[1, 5]` cannot reach index `70` (level `6`) or index `0`
  (level `0`), so its arms are prefixes of those and fold too.
* `not_folds_232_51`, `not_folds_324_15`: batch 34's `no_fold_of_low_early`, at `v = 0` and index
  five.
* `not_isZigFree_232_15`, `not_isZigFree_324_51`: the other order of the outer legs fails the
  alternation at the join, so it is not a member of the free family of `[0, 6]` — which
  `ExtendStepMin` demands.
* The band `[2, 5]` is excluded by the chain: `ρ 3 = ρ 7 = 1` pin the stretch inside `[4, 6]`,
  where the maximum is `3`.

## 3. What is delivered besides the refutation

**`finite_isZigFree`** — by the bound on the number of targets, as the commission's first option:
`zigFree_amp_ge` shows the amplitudes grow by at least one from the second on, so
`zigFree_length_le` gives at most `H − L` targets, each in `[L+1, H−1]`, and
`finite_lists_of_bounded` (lists of bounded length over a finite set of levels) finishes.

**`exists_shortest_serving`** — by `Nat.find` on "some serving member has walk length `k`", as
the commission guessed would be shorter; the finiteness is not used.

**`s3ZigFreeInterior_of_extendStepMin`** — proved outright, not vacuously from the refutation.
It is batch 34's induction on the span with one change: the walk the induction hypothesis supplies
for the inner stretch is replaced by a shortest one before the step is invoked. So the route the
commission describes in §2 is sound; it is the step at its end that is false.

**A defect in the commissioned statement.** The commissioned `ExtendStepMin` does not elaborate:
its `Fin n` indices `⟨a + j.val, by omega⟩` need `a ≤ i.val`, `i.val ≤ b` and `b < n`, which batch
34's `ExtendStepZF` carries as explicit binders and which the commissioned text drops. The
statement in the file restores exactly those three binders and changes nothing else; the
commissioned text is kept, commented out, at the end of the file.

## 4. Hygiene

The project builds. `HPC/Fold/Minimal2.lean` has no `sorry`, `admit`, `axiom`, `native_decide` or
`@[implemented_by]` outside the commented block that keeps the commissioned statement, and adds
no linter warnings. Every theorem in it has axiom profile inside `propext`, `Classical.choice`,
`Quot.sound` — checked for `finite_isZigFree`, `exists_shortest_serving`,
`s3ZigFreeInterior_of_extendStepMin`, `not_extendStepMin`, `zigWalk_length_ge` and the explicit
folds. The file imports `HPC.Fold.ValleyFWitness` for the chain and its faithfulness; that file is
unchanged and is now reached from the root through `HPC.Fold.Minimal2`.

## 5. What the next formulation has to face

The mechanism is unchanged and is now measured three ways. An inner member's targets are at
`L + 2` or above, so the extension's walk is high for its whole first stretch, and an arm that
reaches `L` early cannot be folded. Restricting to shortest walks helps because a shorter inner
walk leaves the arm's low index within reach — the failures drop by an order of magnitude — but
the shortest serving member need not be the one that can be extended, and at 262 of 13 635
basepoints at span twelve none of them is. Two directions the census makes concrete:

* the length restriction the mechanism actually wants is an absolute bound — the inner walk must
  be no longer than the first index at which the arm reaches an extreme level — not "shortest";
  the census can be re-run against that form directly;
* the trim and the member must be chosen together, as batch 27 already concluded for the cut: the
  band `[1, 4]` at basepoint `5` of `bing 0 6` has a serving member of least length that extends,
  `[3, 2, 3]`, and one that does not, `[2, 3, 2]`, so a step that picks the member by the trim's
  geometry rather than by length alone is still open.
