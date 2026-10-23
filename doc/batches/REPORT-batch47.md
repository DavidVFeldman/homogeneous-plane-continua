# Report: batch 47 — the branch on one work item, and the two questions answered

Runs on top of the delivery carrying batches 45 and 46, under the batch-47 commission
(`COMMISSION.md`). Everything earlier is untouched except `HPC/Fold/Mixed.lean`, where the branch
`L + 4` is re-split, and root `HPC.lean`, which imports three new files:

* `HPC/Fold/Raise.lean` — the raise of a faithful pair need not be faithful;
* `HPC/Fold/LinkFold.lean` — a fold read on the upper ends gives four-link blocks, not three;
* `HPC/Fold/Reflect.lean` — the general model is reflection-symmetric, and valleys can be filled.

and one more, `HPC/Fold/Leg3Profile.lean`, which states the criterion the branch now needs.

`lake build HPC` succeeds. Everything proved is `sorry`-free and uses only
`[propext, Classical.choice, Quot.sound]`; no `native_decide`. The `sorry`s of the project are
`theorem3` (`HPC/Fold/Open.lean`), `s3_span_nine` and `s3_general` (`HPC/Fold/General.lean`), the
branch `s3_span_nine_mid5` (`HPC/Fold/Mixed.lean`), and the two halves of the branch `L + 4`:
`foldsOnto_leg3deep_profile` (`HPC/Fold/Leg3Profile.lean`) and `unserved_profile`
(`HPC/Fold/Mixed.lean`). `s3_span_nine_mid4` and `unserved_leg3deep` are no longer `sorry`s of
their own: each is a short derivation from those two.

## 0. Counterexamples, first

No counterexample to a **target**: `s3_span_nine_mid4`, `s3_span_nine_mid5`, `s3_span_nine`,
`s3_general` and `theorem3` are all still open, none refuted. Two of the commission's questions are
answered in the negative, and both negative answers are proved in Lean rather than checked:

* **Not every faithful pair is a shaving of a thin one** (§2.1). The six-term pair

  ```
  ρ = 0 1 1 1 2 2
  σ = 0 1 2 2 2 3
  ```

  is faithful (`raise_faithful`) and its raise `(σ, σ)` is not (`not_isCrookedIvF_raise`), so it is
  not a shaving of any thin sequence (`not_isShavingOfThin_example`,
  `exists_faithful_not_isShavingOfThin`). In the raise the clause fires between the index `0`, at
  level `0`, and the index `5`, at level `3`, and asks for a time at `2` followed by a later time
  at `1`; the raised sequence stands at `2` from its index `2` on and never returns to `1`. In the
  original pair the two middle links *meet* both `1` and `2`, which is what satisfies the clause.
  By the exhaustive census `census-batch47.c` this is a least counterexample: in the band `[0, 4]`
  there is none of length five or less, and 20 of length six.

* **A fold read on `σ` costs a link** (§2.2). `exists_blocks_first_of_folds_max`
  (`HPC/Fold/LinkFold.lean`) is Theorem 3's block conclusion from a fold of the upper ends, with
  **four** consecutive links of the coarse chain in place of three, and four is what the estimate
  gives: a walk within one of `σ t` is within two of `ρ t`, so two links of one block have minimal
  indices three apart. The same holds for a fold whose window condition reads the whole link.

## 1. The branch `L + 4`: one work item, and which walk

`s3_span_nine_mid4` now rests on the single statement `unserved_leg3deep`:

> a faithful pair of span nine with both ends attained, based at `L + 4` with both arms
> `HighAt (L + 1) (L + 8)`, that folds onto neither canonical walk has **both arms folding onto
> the third walk `L+3 → L+6 → L+1 → L+8`** — that is, onto `leg3Walk L (L+9) (L+6) (L+4)`.

This is the commission's question 2.3 — *which walk, as a function of which announcements?* — with
the answer **that walk, and no announcement**. The census `census-batch47b.c` (general pairs,
generator: shavings of `bing 0 9`, each verified against `IsCrookedIvF`, each fold decided by the
dynamic program over `FoldsOnto`) finds:

| | unserved branch basepoints | served by `L+3 → L+6 → L+1 → L+8` | by `L+3 → L+7 → L+1 → L+8` | by `L+3 → L+5 → L+1 → L+8` | by no three-leg walk |
|---|---|---|---|---|---|
| 288 single shavings | 6 340 | **6 340** | 6 326 | 0 | 0 |
| 20 random multiple shavings | 451 | 451 (with `a ∈ {5,6,7}`) | — | — | 0 |

So the batch-46 observation that *some* three-leg walk serves every unserved pair sharpens to: the
walk of the batch-44 engine serves every one of them, the two basepoints that refuted the batch-46
items included. What is missing is not a walk but a criterion for it.

**What the criterion has to be.** `census-batch47c.c` ranges over 1-Lipschitz arms in `[0, 9]`
starting at `L + 4`, exhaustively up to length sixteen, and compares the exact fold onto that walk
with the engine's criterion (`foldsOnto_leg3_deep`). Three facts:

* the engine's criterion is far from necessary — at length sixteen, 571 689 of the 7 183 837
  folding arms fail it;
* lowering every demand for a time at the peak level `L + 6` to `L + 5` — the level the *general*
  crookedness clause actually delivers, since it returns a link meeting `L + 6`, whose `ρ` may be
  `L + 5` — removes almost all of that: at length fourteen only 0 folding arms fail the lowered
  criterion, and at length sixteen only 878;
* but the lowered criterion is not sufficient: `4 5 4 3 2 1` satisfies it and does not fold. The
  walk's valley is its position 8, so an arm at `L + 1` at its step 5 cannot be tracked. What is
  missing is an **index clause**, exactly as in the Λ-criterion of `HPC/Fold/Profile.lean`, where
  the profile asks for the level `κ - 1` at an index at least `κ - p`. The crude index clause
  "`L + 1` only from step 8, `L + 8` only from step 14" is not yet enough (`4 4 5 4 3 2 2 2 1 …`
  fails at its step 3, where the walk must already stand at `L + 6`), so the clause has to relate
  the two times: the arm must stand at `L + 5` at a step `j ≥ 3`, and descend no faster than the
  walk from there.

**The criterion, exactly.** `census-batch47c.c` fixes it. Write it for an arm `f` based at
`L + 4`:

* `Leg3Valley` — every step `d` with `f d ≤ L + 1` has a step `j` with `3 ≤ j`, `j + 5 ≤ d` and
  `L + 5 ≤ f j`;
* `Leg3Ceil` — every step `d` with `L + 8 ≤ f d` has such a `j` and, after it, a step `k` with
  `j + 5 ≤ k`, `k + 6 ≤ d` and `f k ≤ L + 2`.

The three index bounds are the three landmarks of the walk, which stands at `L + 6` at its
position 3, at `L + 1` at its position 8 and at `L + 7` at its position 14 and advances at most one
position per step. Exhaustively over every 1-Lipschitz arm in `[0, 9]` of length at most sixteen
there is **no** arm meeting the criterion that fails to fold, and 59 982 of the 7 183 837 folding
arms of length sixteen fail it; over two million random arms of lengths 17 to 196 there is again
none meeting it that fails to fold. And over the general pairs of `census-batch47b.c`, **all
6 340** unserved branch basepoints have both arms meeting it.

So the branch splits in two, and the split is in the repository:

* `foldsOnto_leg3deep_profile` (`HPC/Fold/Leg3Profile.lean`) — the criterion suffices for the
  fold. A statement about 1-Lipschitz arms alone, with no crookedness, exactly like
  `foldsOnto_leg3_deep`. This is the next engine: the same shape of strengthening that batch 42
  made for the Λ-walk, where `CritLamProfile` asks for `κ - 1` at an index at least `κ - p`.
* `unserved_profile` (`HPC/Fold/Mixed.lean`) — an unserved pair of the branch meets the criterion
  on both arms. This is where crookedness enters, and it is the statement the general model can
  be expected to give, because the clause returns links meeting `L + 6`, that is times of `ρ` at
  `L + 5` or above, and the timing laws of `HPC/Fold/Timing.lean` are what the index clauses ask
  for.

`unserved_leg3deep` and with it `s3_span_nine_mid4` are proved from the two.

## 2. The answers to the commission's questions

**2.1 Is every faithful pair a shaving of a thin one?** **No**, on both halves of the question.

*The raise.* §0 above: `exists_faithful_not_isShavingOfThin`. The raise of a faithful pair need not
be faithful, so the pair is not a shaving of anything thin. This is not a rare accident: over the
exhaustive enumeration of the general model in the band `[0, 4]` (`census-batch47.c`), the raise
fails for 20 of the 7 356 faithful pairs of length six, 8 584 of 387 934 at length nine, and
910 420 of 20 552 008 at length twelve — about 4%, and rising with length. (About a third of all
links of a faithful pair of that band are non-thin, and the proportion is stable in the length.)

*The transfer of the fold.* Also no. `census-batch47b.c` compares, at each of the 22 280 branch
basepoints of the 288 single shavings, the walks serving the thin sequence with those serving the
shaved pair: the Λ-walk and the V-walk never lose a fold in that corpus, but the three-leg walk
`L+3 → L+6 → L+1 → L+8` loses 16 of 15 596 and `L+3 → L+7 → L+1 → L+8` loses 20 of 8 142 (and each
gains some: 60 and 10). So a fold of the thin sequence is not a fold of the general pair, and
`s3_span_nine_thin` does not carry across even where the raise is faithful.

*And the other direction is closed too.* One might hope to go down rather than up: if the point
sequence `ρ` of a pair were itself thin-faithful, `s3_span_nine_mid4_thin` would apply to it and
its conclusion — which mentions only `ρ` — would be the conclusion wanted. It is not:
`census-batch47d.c` finds that for **all 288** single shavings of `bing 0 9` the lowering
`(ρ, ρ)` fails the crookedness clause. The general model's point sequences are genuinely outside
the thin model.

*What the model does admit.* `HPC/Fold/Reflect.lean` proves that the general model is symmetric
under reflection of the levels — the reflection of `(ρ, σ)` is `(a - σ, a - ρ)`, so the reflected
*point* sequence is `a - σ` (`isCrookedIvF_reflect_general`) — and that the upper ends are
1-Lipschitz (`isCrookedIvF_sig_isLip`). Reflecting `isCrookedIvF_shave` through it gives a second
generator: **filling a valley** (`isCrookedIvF_fill`), which raises `σ` by one at a thin link whose
neighbours stand above it and leaves `ρ` where it is. All 288 strict local minima of `bing 0 9` can
be filled, singly or in random subsets, and fills and shavings can be combined
(`census-batch47d.c`). Filling changes no walk criterion, since every criterion reads `ρ`; what it
changes is which levels the clause may be applied at.

**2.2 Can the fold be of `σ`, or of the interval?** **Yes, at the cost of one link.**
`exists_blocks_first_of_folds_max` is the four-link form and is proved; the three-link conclusion
of Theorem 3 needs the fold of `ρ`. Where the pair is thin the two readings agree. So the first
candidate of REPORT-batch46.md §5 — announcements read on `σ` — cannot be carried all the way to
the block conclusion by simply folding `σ`: the announcements may be read on `σ`, but the fold they
feed must still be a fold of `ρ`.

**2.3 Which walk, as a function of which announcements, on general pairs?** The walk is
`L+3 → L+6 → L+1 → L+8`, always, on every unserved pair of every census in this repository (§1).
The announcements are the open question, and §1 says what they have to look like: the engine's two
announcements with every demand for the peak level `L + 6` lowered to `L + 5`, plus an index
clause. Stated on links rather than on levels of `ρ` — the form the commission asks about — the
lowered demand is exactly *"the clause returns a link meeting `L + 6`"*, which is what the general
model gives; so the two readings of the question meet at the same statement.

## 3. The censuses

All four range over the **general** model and verify every candidate against the definition
`IsCrookedIvF` of `HPC/Fold/Faithful.lean`; folding, where it is decided, is decided exactly by the
dynamic program over `FoldsOnto`.

* `census-batch47.c` (log `census-batch47.log`) — generator: **exhaustive enumeration** of all
  pairs of length at most twelve in the band `[0, 4]`. Reports the faithful pairs, the fraction of
  non-thin links (about 0.32 throughout), the pairs whose raise fails, and the pairs that are not
  shavings of a thin sequence.
* `census-batch47b.c` (log `census-batch47b.log`) — generator: **shavings of `bing 0 9`**, all 288
  single shavings (one non-thin link of 986) and 20 random multiple shavings (about 0.098 non-thin
  links). The unserved branch basepoints, the walks that serve them, and the transfer of folds
  between the thin sequence and the shaved pair.
* `census-batch47c.c` (log `census-batch47c.log`) — not pairs but **arms**: every 1-Lipschitz
  sequence in `[0, 9]` of length at most sixteen starting at `L + 4`, exhaustively. Compares the
  exact fold onto the third walk with the engine's criterion and with the lowered one. (The engine
  `foldsOnto_leg3_deep` uses no crookedness, so a sufficient criterion for the fold is a statement
  about arms alone; the general model enters only in `census-batch47b.c`.)
* `census-batch47d.c` (log `census-batch47d.log`) — generators: **fills** and **shavings** of
  `bing 0 9`, single and random-multiple, and the lowering `(ρ, ρ)` of each shaved pair.

## 4. Deliverables

1. Proved, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`:
   * `HPC/Fold/Raise.lean` entire — `raise_faithful`, `not_isCrookedIvF_raise`, `IsShavingOfThin`,
     `isShavingOfThin_shave`, `not_isShavingOfThin_example`,
     `exists_faithful_not_isShavingOfThin`;
   * `HPC/Fold/LinkFold.lean` entire — `foldsOnto_of_thin`, `exists_blocks_first_of_folds_max`;
   * `HPC/Fold/Reflect.lean` entire — `isCrookedIvF_sig_isLip`, `isCrookedIvF_reflect_general`,
     `isCrookedIvF_fill`.
2. Censuses `census-batch47.c`, `-47b`, `-47c`, `-47d` with their logs, as §3 states.
3. `HPC/Fold/Mixed.lean`: the branch `L + 4` re-split on `unserved_leg3deep`, itself proved from
   the two work items `foldsOnto_leg3deep_profile` and `unserved_profile`; the refuted statements
   of batches 44–46 are where batch 46 left them, commented out. `HPC/Fold/Leg3Profile.lean`:
   `Leg3Valley`, `Leg3Ceil` and the engine statement.
4. What is open: `foldsOnto_leg3deep_profile`, `unserved_profile`, `s3_span_nine_mid5`,
   `s3_span_nine`, `s3_general`, `theorem3`.

## 5. What the next batch might ask

The two halves, in either order. `foldsOnto_leg3deep_profile` is the self-contained one: no
crookedness, no pairs, and `HPC/Fold/Profile.lean` is the model of the proof, with
`census-batch47c.c` as the instrument for checking any variant of the clause before it is
attempted. `unserved_profile` is the one the thin material already rehearses:
`HPC/Fold/MixedThin.lean` does exactly this work one level higher, and every place where its proof
reads a level of `ρ` off the crookedness clause is a place where the general clause gives the same
level minus one — which is what the lowered criterion asks for.
