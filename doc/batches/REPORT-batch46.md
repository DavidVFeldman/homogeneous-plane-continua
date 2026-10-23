# Report: batch 46 — shaving a peak, and both work items refuted

Runs on top of the batch-45 delivery, under the same commission (`COMMISSION.md`, batch 45),
whose §1 names the two work items as targets and whose rule is that *a counterexample to any of
these is a success and is reported first*. Everything earlier is untouched except
`HPC/Fold/Mixed.lean`, where the two refuted statements are kept, commented out, exactly as they
stood. Three new files carry the new material — `HPC/Fold/Shave.lean`,
`HPC/Fold/Bing9Shave.lean`, `HPC/Fold/Bing9ShaveWitness.lean` — and root `HPC.lean` imports them.
`lake build HPC` succeeds. The only `sorry`s in the project are `theorem3` (`HPC/Fold/Open.lean`),
the two targets of `HPC/Fold/General.lean`, and the two branches `s3_span_nine_mid4`,
`s3_span_nine_mid5` of `HPC/Fold/Mixed.lean`. `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for everything proved; no `native_decide`.

## 0. The counterexamples, first

**Both work items of the branch `L + 4` are false in the general model.**

* `unserved_ceiling` — a pair of the branch folding onto neither canonical walk announces, on each
  arm, its ascents to `L + 8` — fails at the basepoint `336` of `bing9sB`
  (`not_unservedCeiling`).
* `unserved_valley` — the same pair announces, on each arm, its descents to `L + 1` — fails at the
  basepoint `138` of `bing9sA` (`not_unservedValley`).

Both witnesses are Bing's 986-link chain `bing 0 9` with **one peak shaved**, and both are proved
in Lean.

### Shaving

The general model records each link by the least and the greatest level it meets,
`ρ t ≤ σ t ≤ ρ t + 1`; the thin form, in which batch 45 proved the whole of span nine, is `σ = ρ`.
Let `j` be a strict local maximum of a faithful sequence: both neighbours stand at `ρ j - 1`.
Lower `ρ` at `j` by one and leave `σ` alone. The link at `j` now runs from `ρ j - 1` to `ρ j`: it
still *meets* the peak level, so every application of the crookedness clause that used it is
unaffected, but the point sequence no longer stands there.

`isCrookedIvF_shave` (`HPC/Fold/Shave.lean`) proves that the result is a faithful crooked pair,
for any faithful pair and any such `j`. The proof is four lines of bookkeeping and one
observation: a level met by the shaved link near an index `s` is met, in the original pair, by a
link near `s` too — the new level `ρ j - 1` is the level of the neighbours of `j` — while the
conclusion of the clause only gets easier, since the shaved link meets everything it met before.
Two hypotheses are needed and no more: the link being shaved must be thin (else the shaved link
would be two levels wide) and its neighbours must lie strictly below it (else adjacency fails).

**This answers the standing question of batches 44 and 45.** The thin form `σ = ρ` does lose
pairs, and it loses them at exactly the level at which the span-nine argument works: every walk
criterion of the development reads the *point* sequence `ρ`, every application of the crookedness
clause returns a *link meeting* a level, and shaving is the operation that separates the two.

### The two witnesses

`bing9sA` is `bing 0 9` with the peak at index `128` shaved from `6` to `5`; `bing9sB` is
`bing 0 9` with the peak at index `309` shaved from `7` to `6` (`HPC/Fold/Bing9Shave.lean`). Both
are faithful (`bing9sA_faithful`, `bing9sB_faithful`, by the shaving theorem from
`bing9_faithful`), both are non-thin (`bing9sA_not_thin`, `bing9sB_not_thin`), both lie in the
band `[0, 9]` with both ends attained, and both are Lipschitz.

| | valley witness | ceiling witness |
|---|---|---|
| chain | `bing9sA` (peak `128`: `6 → 5`) | `bing9sB` (peak `309`: `7 → 6`) |
| basepoint, at `L + 4` | `138` | `336` |
| arms | 848 forward, 139 backward | 650 forward, 337 backward |
| both arms `HighAt (L+1) (L+8)` | yes | yes |
| Λ-walk based at `L + 3` | fails on the backward arm | fails on the backward arm |
| V-walk based at `L + 5` | fails on the forward arm | fails on the forward arm |
| the unannounced event | backward arm at `L + 1`, step `39` | forward arm at `L + 8`, step `72` |
| the window before it | `[L + 2, L + 5]` | `[L + 2, L + 7]`, at `L + 3` or above after its first `L + 7` at step `31` |

For the valley witness the shaved link *is* the announcement that vanishes: unshaved, the backward
arm stands at `L + 6` at its step `10`, which announces the descent at step `39`; shaved, the link
still meets `L + 6` and the crookedness clause is satisfied exactly as before, but the point
sequence stays in `[L + 2, L + 5]`. For the ceiling witness the shaved link sits on the backward
arm and changes which canonical walks fold: the forward arm's unannounced ascent was always there,
but at the unshaved basepoint the pair was served.

The Lean proofs follow `HPC/Fold/Bing9Witness.lean` of batch 45 exactly: the arms are read off the
chain by kernel evaluation, the two fold failures are decided by the exact criteria of
`HPC/Fold/Profile.lean` with the index clauses of `HPC/Fold/Timing.lean`, and the announcement
failure is three windows.

## 1. What this does to the branch

`s3_span_nine_mid4` was, after batch 45, a case analysis over three walks resting on the two work
items. With both items refuted the reduction is gone and the branch is a `sorry` again; the
statement is unchanged, and so is everything it rests on (`foldsOnto_leg3deep_branch`,
`s3_span_nine_mid4_of_valley`, `ceiling_or_lam`, `valley_or_vee` are all still theorems — what
fails is only the claim that an unserved pair meets their hypotheses). The thin branch
`s3_span_nine_mid4_thin` and the whole of `s3_span_nine_thin` are untouched.

What the censuses say is that the branch itself is not in danger: over 15 798 branch pairs of
shaved chains that fold onto neither canonical walk — including every one of the 33 that refute a
work item — **every** pair is served by a walk of at most three legs. The third walk of batch 44
is the right kind of object; what was wrong was the criterion through which the branch reached it.

## 2. The answers to the commission's questions

**2.1 Is `s3_span_nine_mid5` the reflection of `s3_span_nine_mid4`?** Batch 45 answered this for
the thin model: not as the statements stand, but the *proof* of the thin branch `L + 4` uses
neither branch hypothesis and therefore reflects (`s3_span_nine_mid5_thin`). Nothing in this batch
changes that, and in the general model the question is now downstream of a branch that is open
again. Note that the general model is reflection-symmetric in its own way — reflecting `(ρ, σ)`
gives `(a - σ, a - ρ)` — but the reflected *point* sequence is `a - σ`, not `a - ρ`, so the
reflection does not carry a statement about the arms of `ρ` to a statement about the arms of `ρ`.
This is the same one-level gap as everywhere else in the general model, seen from the other side.

**2.2 What do the two work items say about the pair?** They say something false. The thin proofs
(REPORT-batch45.md §2.2) turn on one application of the crookedness clause across the basepoint,
which produces a link meeting `L + 7`; on a thin sequence that link stands at `L + 7` and
contradicts the other arm's window, and in the general model it may stand at `L + 6` and
contradict nothing. Batch 45 recorded that this was the whole of the gap. It is: shaving one peak
realises exactly that configuration on an actual pair, and both items fall.

**2.3 Does the thin form `σ = ρ` lose pairs?** **Yes** — `isCrookedIvF_shave`, and the two
witnesses. This settles the question that batches 44 and 45 left open, and it settles it against
the thin model: no census over thin sequences (which is every census in this repository before
this batch) is evidence about the general model, and the two censuses of batch 45 in particular
could not have found these counterexamples.

Two further facts about how wide the general model is, both from `census-batch46b.c` and
`census-batch46d.c`:

* **Contracting is not available.** Of the 985 ways to merge two consecutive links of `bing 0 9`
  into one, *none* gives a faithful pair: 816 fail adjacency and 169 fail crookedness. Random
  block contractions fail too (`census-batch46.c`: 0 of 200). Shortening the sequence destroys the
  clause; shaving, which keeps its length, does not.
* **Shaving is always available.** All 288 strict local maxima of `bing 0 9` can be shaved, one at
  a time, and all 288 results are faithful; so are all 40 random subsets of shavings tried.

## 3. The censuses

All four range over pairs of the **general** model and verify each candidate against the
definition `IsCrookedIvF` of `HPC/Fold/Faithful.lean` — `le`, `width`, `adj` and the crookedness
clause, read with "near" tolerance one and a link meeting every level between its `ρ` and its
`σ`. Generation is never trusted: the verifier decides. Folding is decided exactly, by the dynamic
program over the definition `FoldsOnto`. None ranges over a one-arm class.

* `census-batch46.c` (log `census-batch46.log`) — random block contractions of `bing 0 9`;
  0 of 200 faithful.
* `census-batch46b.c` (log `census-batch46b.log`) — every single merge of two consecutive links;
  0 of 985 faithful, with the failing clause recorded.
* `census-batch46d.c` (logs `census-batch46d.log`, `census-batch46d-all.log`,
  `census-batch46d-rand.log`) — peak shavings. Over the 36 peaks at level `7`: 6 552 branch basepoints, 1 928 folding onto neither
  canonical walk, 3 refuting the ceiling item, 0 refuting the valley item, 0 served by no walk of
  at most three legs. Over all 288 peaks: 52 502 branch basepoints, 15 798 unserved, 3 refuting
  the ceiling item, 30 refuting the valley item, again none unserved by a three-leg walk. Over 40
  random subsets of the shavable peaks (`census-batch46d-rand.log`): 40 of 40 faithful, 18 ceiling
  failures and 271 valley failures over 1 697 unserved pairs, and again none unserved by a
  three-leg walk.
* `census-batch46e.c` (log `census-batch46e.log`) — the two witnesses, printed with every fact the
  Lean proofs use: the shaved peak, the basepoint, the fold status of each arm with the index
  witnessing each failure, and the window that refutes the announcement.
* `census-batch46f.c` (log `census-batch46f.log`) — every walk of at most three legs serving each
  of the two witnesses. The valley witness is served by exactly four, among them
  `L+3 → L+6 → L+1 → L+8` — **the walk of the batch-44 engine itself**. The ceiling witness is
  served by ten, among them `L+3 → L+7 → L+1 → L+8`, the same shape with its middle peak one level
  higher, and `L+3 → L+2 → L+8 → L+1`.

## 4. Deliverables

1. Proved, `sorry`-free, standard axioms `[propext, Classical.choice, Quot.sound]`:
   * `HPC/Fold/Shave.lean` entire — `isCrookedIvF_shave`, `isLip_shave`;
   * `HPC/Fold/Bing9Shave.lean` entire — `bing9sA`, `bing9sB` with their faithfulness, band, ends
     and non-thinness;
   * `HPC/Fold/Bing9ShaveWitness.lean` entire — `not_unservedCeiling`, `not_unservedValley`.
2. Censuses `census-batch46.c`, `census-batch46b.c`, `census-batch46d.c`, `census-batch46e.c`,
   with logs; all over general pairs, as §3 states.
3. `HPC/Fold/Mixed.lean`: the two refuted statements kept, commented out, with the refutation
   named; `s3_span_nine_mid4` back to a `sorry`, with what is known recorded in its docstring.
4. What is open, all of it in the general model: `s3_span_nine_mid4`, `s3_span_nine_mid5`,
   `s3_span_nine`, `s3_general`, `theorem3`.

## 5. What the next batch might ask

The branch needs a criterion that survives shaving — and, by `census-batch46f.c`, not a new
engine: the valley witness is folded by the very walk `L+3 → L+6 → L+1 → L+8` that
`HPC/Fold/Leg3Deep.lean` drives, so what failed is only the announcement through which
`s3_span_nine_mid4_of_valley` reaches it. Two candidates, both suggested by the shape of the
counterexamples and neither attempted here:

* read the announcements on `σ` rather than on `ρ` — the clause returns links, so the announcements
  it can prove are announcements about links — and ask what the three-leg engine needs when its
  hypotheses are stated that way;
* or pay for the missing level with a fourth walk: the censuses say that every unserved pair,
  shaved or not, is served by a walk of at most three legs, so the question is which walk, as a
  function of which announcements hold.
