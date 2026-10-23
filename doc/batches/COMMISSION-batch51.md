# Commission: batch 51 — engines for `w₄` and `w₅`, and the level

**Go!** Runs on top of the batch-50 delivery in its continued form (the tarball that carries `HPC/Fold/CrossValley.lean`). No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they stand.

## 0. On batch 50

Audited: every earlier Lean file identical; five new files; standard axioms, no `native_decide`;
no target refuted. `foldsB_iff` (`Decide.lean`) makes `FoldsOnto` decidable in the kernel, so a
census verdict of *no fold* now has a Lean counterpart, and the definition audit (`Audit50.lean`:
12 arms, 13 predicates, 156 kernel checks, generated from the census's own sample) is in place
and caught the run's own wrong guess about `w₄` before it reached Lean. That is the protocol
working; it stays.

Facts fixed by the batch: the three walks announce different events, read off their positions
(`LandmarkW.lean`), so `unserved_three_walks` is three sentences and not one; its thin form is a
theorem, with the first disjunct always holding there; `three_walks_necessary` is the instrument
that would recognise a counterexample and never fires; the pair of batch 49 is served by `w₄` and
`w₅` both. `cross_valley_profile`: 127 525 tests over two batches; the steered search reaches `O = 1`, never
`O = 0`; and the continuation put the case analysis into Lean (`CrossValley.lean`):
`cross_valley_dichotomy` — either both arms fold onto the V-walk, or the sequence stands at exactly
`L + 2` at one of `i − 3, i − 2, i + 2, i + 3` (`ValleyResidual`); the item is a theorem off that
configuration (`cross_valley_profile_of_not_residual`); and with no exception at all the other arm
stands at `L + 3` or below at index ≥ 4 before each ascent (`cross_valley_armT_low3`,
`cross_valley_armG_low3`) — the V-criterion with `L + 3` for `L + 2`. Neither `HighAt` clause nor
either end of the band is used anywhere in that file.

## 1. Targets

1. `unserved_three_walks` (`Mixed.lean`). With it `s3_span_nine_mid4` is complete.
2. `cross_valley_profile`, if it is still on the route after 1.
3. `s3_span_nine_mid5`.
4. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first, after a definition audit of
the predicates that found it. A refuted statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The sufficiency halves for `w₄` and `w₅`.** `w₃` has an exact criterion; `w₅` has a
   sufficient one that asks a level more than the landmark sentence; `w₄` has none, its engine being
   stated for an arm based at the walk's own trough. Whether each gets an engine of the batch-48
   kind (numerical invariants on the greedy time, landmark positions as constants), and whether the
   three exact criteria then make `unserved_three_walks` a statement about crookedness and three
   sentences, is asked.
2. **The one level.** Every open item now stops at the same place: a clause application returns a
   link *meeting* a level, and the criterion wants the point `ρ` *at* it, one lower. `LinkFold.lean`
   says a fold of `σ` costs a link in the block conclusion. Whether a fold of `ρ` can be obtained
   from announcements read on `σ` by a route other than folding `σ` — or whether the three-link
   form is where the level is paid for and a proof of Theorem 3 in the three-link form must use
   the slack that `exists_blocks_first_of_folds` has and the criteria do not — is asked as a
   question about `Itinerary.lean`, not about span nine.
3. **`ValleyResidual` as a pair.** The residue is now a statement about the three steps either
   side of the basepoint. Whether a general pair realises `ValleyResidual` together with a failing
   arm and an other arm that misses the V-walk — a counterexample — or whether that configuration
   is excluded by the clause in its `σ`-reading or a second application, is the remaining half of
   `cross_valley_profile`. And whether the relaxed criterion that holds everywhere (`L + 3` at
   index ≥ 4) is itself enough for a fold onto *some* walk — not the V-walk based at `L + 5` — is
   asked alongside, since `unserved_three_walks` needs only some walk.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model, generators named, fraction of non-thin links stated, with the
   definition audit; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
