# Report: batch 34 — the gate passes, and the step it gates is still not an induction

One new file, `HPC/Fold/Step.lean`; the root `HPC.lean` updated with its import; `README.md`
notes the batch. Nothing else was touched. The whole project builds. The new file has no
`sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]` outside the commented block at
the end, adds no linter warnings (the four `unused variable` warnings in `HPC/Fold/Itinerary.lean`
and `HPC/Fold/Bump.lean` are the pre-existing ones of earlier batches), and every theorem in it
has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

The census program is `census-batch34.c`, its output `census-batch34.log`.

## 1. The gate (COMMISSION §1), run first

**Verdict: the gate as stated passes at spans 9, 10, 11 and 12 — 0 failures.** Folding is
decided exactly by bitmask reachability, one pair of sweeps per walk resolving every basepoint at
once; the whole free family of each inner band is enumerated; every interior basepoint of
`bing 0 n` (those with `L + 3 ≤ ρ i ≤ H − 3`) is tested.

| span | links | interior basepoints | G1 | G2 | G1 or G2 | failures |
|---:|---:|---:|---:|---:|---:|---:|
| 6 | 71 | 25 | 19 | 19 | 25 | **0** |
| 7 | 170 | 104 | 82 | 82 | 104 | **0** |
| 8 | 409 | 319 | 254 | 254 | 319 | **0** |
| 9 | 986 | 868 | 704 | 704 | 868 | **0** |
| 10 | 2 379 | 2 229 | 1 804 | 1 804 | 2 229 | **0** |
| 11 | 5 742 | 5 556 | 4 502 | 4 502 | 5 556 | **0** |
| 12 | 13 861 | 13 635 | 11 031 | 11 031 | 13 635 | **0** |

(G1 is the greedy left-first trim of span `H − L − 1`, G2 the greedy right-first one; the columns
count interior basepoints at which that trim admits an inner-serving member and **every**
inner-serving member extends. The weak "some" form holds at the same places and more.)

**The greedy-trim question is answered: the choice is genuinely needed.** Neither greedy order
suffices on its own — each passes at 11 031 of the 13 635 interior basepoints at span twelve —
and the two give different verdicts at 5 406 of them; together they cover all. So an induction
using this trim must choose, and neither fixed choice is right.

## 2. But the gate does not close the induction, and that is a theorem

`S3ZigFreeInterior` asks for a **member of the free family of `[L, H]`**. The walk the step
produces is `ts ++ [x, y]` with `ts` a member of the inner band's family. The batch proves

```
zigFree_append_forces_inner :
  IsZigFree L' H' ts → L' + 3 ≤ H' → (x,y) = (L+1,H-1) ∨ (x,y) = (H-1,L+1) →
  IsZigFree L H (ts ++ [x, y]) → L + 1 ≤ L' ∧ H' ≤ H - 1
```

so the trim must strip **both** extreme levels; the immediate corollary
`no_outer_member_of_span_one_trim` says that a trim whose span is only one less — exactly the
trim of §1 — can never be appended to. (Why: the inner member's last two targets are
`L'+1, H'−1` in one order or the other. If it ends high, the appended leg to `L+1` has amplitude
`H'−L−2`, which must exceed the inner member's last amplitude `H'−L'−2`, forcing `L < L'`, and
must be less than the final amplitude `H−L−2`, forcing `H' < H`. If it ends low, the first
appended leg reverses nothing and the alternation clause fails outright.) The census confirms it
numerically: of the members used at the G1 and G2 trims, **none** has an extension in the outer
family, at any span.

So §1's gate, though it passes, measures a property of walks that are not members of the family
the conclusion demands. The commissioned `ExtendStep` is kept in the file unchanged, and nothing
is derived from it.

The append lemma is therefore generalised to the trims that can work:
`isZigFree_append_outer'` — for any band `[L', H']` with `L + 1 ≤ L'`, `H' ≤ H − 1` and
`L' + 3 ≤ H'`, a member of its family becomes a member of `[L, H]`'s family when the two outer
legs are appended in the orientation its end dictates. Batch 33's `isZigFree_append_outer` is the
case `L' = L+1`, `H' = H−1`.

## 3. With the trim corrected, the strong form is false

Censused exactly (§1b of the log): for every interior basepoint, over **every** band inside
`[L+1, H−1]` and every maximal stretch of that band containing the basepoint, does some member
fold both inner arms and does every such member's oriented extension fold both whole arms?

| span | interior basepoints | EVERY form | SOME form | full inner band alone |
|---:|---:|---:|---:|---:|
| 6 | 25 | 15 (**10 fail**) | 25 | 13 |
| 7 | 104 | 70 (**34 fail**) | 104 | 64 |
| 8 | 319 | 221 (**98 fail**) | 319 | 199 |
| 9 | 868 | 624 (**244 fail**) | 868 | 586 |
| 10 | 2 229 | 1 663 (**566 fail**) | 2 229 | 1 531 |
| 11 | 5 556 | 4 370 (**1 186 fail**) | 5 556 | 3 904 |
| 12 | 13 635 | 11 229 (**2 406 fail**) | 13 635 | 9 691 |

Every oriented extension arising here *is* a member of the outer family — 0 exceptions — so what
fails is the fold, not the family.

**The witness, in full** (log §4). `bing 0 6` has 71 links; basepoint 5 is at level 3, and its
backward arm is `3, 2, 1, 2, 1, 0`. The bands inside `[1, 5]` that carry a trim containing 5 are
`[1, 4]`, whose maximal stretch is `[1, 28]`, and `[1, 5]`, whose maximal stretch is `[1, 69]`.

```
band [1,4], stretch [1,28]:
  [2, 3, 2]  folds both inner arms;  extension [2, 3, 2, 5, 1]  fails the backward arm
  [3, 2, 3]  folds both inner arms;  extension [3, 2, 3, 1, 5]  folds both whole arms
band [1,5], stretch [1,69]:
  [2, 4, 2]     folds both inner arms;  extension [2, 4, 2, 5, 1]     fails the backward arm
  [3, 2, 4]     folds both inner arms;  extension [3, 2, 4, 1, 5]     fails the backward arm
  [4, 2, 4]     folds both inner arms;  extension [4, 2, 4, 1, 5]     fails the backward arm
  [2, 3, 2, 4]  folds both inner arms;  extension [2, 3, 2, 4, 1, 5]  fails the backward arm
```

At the wider band not even the weak form survives; at the narrower one the weak form survives and
the strong one does not. Since an induction hypothesis returns *some* walk and gives no control
over which — the commission's own point — the step cannot be closed this way.

**Why, and it is a theorem.** The failing arm reaches the bottom level fast: five links. The
targets of an inner member all lie at `L + 2` or above, so the extension's centres stay at `L + 2`
or above throughout the inner walk (`zigWalk_prefix`, `zigLevels_append`, `zigTail_append`), and
a fold pins the token to time `0` and moves it by at most one time per link. Hence
`no_fold_of_early_low`: an arm at level `≤ L` at index `d` forces `d` to be at least the length
of the inner walk. Sharper in the witness, and proved as `bing6_arm_not_folded`: the extension
`[2, 4, 2, 5, 1]` runs `2 3 4 3 2 3 4 5 4 3 2 1`, so its centres up to time five are all at least
`2`, while the arm is at level `0` at index five; by `no_fold_of_low_early` there is no fold.
`isZigFree_2425_1` checks that the extension really is a member of the free family of `[0, 6]`.

The other half of the witness — that `[2, 4, 2]` does fold both arms of the 69-link stretch — is
decided by the census and is not formalised: any faithful crooked sequence of span six has at
least `z 6 = 71` links (batch 30's `minimality`), so no small instance of the failure exists, and
a Lean refutation of the corrected step would in addition have to quantify over all trims.

## 4. The ordinary item went through, with the case split costing one `by_cases`

`s3ZigFreeInterior_of_extendStepZF : ExtendStepZF → S3ZigFreeInterior` is proved, by strong
induction on `(H − L).toNat`, where `ExtendStepZF` is the commissioned step with three changes:

* the trim is an `IsInnerTrim` — band strictly inside `[L, H]` and at least three wide — as §2
  shows it must be;
* the existence clause is **dropped**, so the hypothesis is weaker and the induction real: it is
  the induction that must supply the inner walk;
* the conclusion asks for `IsZigFree L H (ts ++ [x, y])`, which is what the goal needs and what
  `isZigFree_append_outer'` supplies for an inner trim.

The base is free: `L + 3 ≤ ρ i ≤ H − 3` is empty unless `L + 6 ≤ H`, so every span up to five is
vacuous and no separate `H = L + 4` case is needed. The step supplies the inner stretch's
faithfulness by `isCrookedIvF_restrict` (batch 30), its band and attained extremes from
`IsInnerTrim`, and its basepoint `i − a`; the case split on whether that basepoint is still
interior costs one `by_cases`, the negative branch being `s3ZigFree_near_extreme` (batch 29)
applied to the stretch, whose `IsLip` comes from `IsCrookedIvF.isLip`. The supply the commission
anticipated — the arm-restriction bookkeeping and the `Fin` arithmetic of `⟨a + j, _⟩` — was
needed only in the small: the arms of the stretch at `i − a` are *literally* the terms appearing
in `ExtendStepZF`, so no transport was required, and the index work reduces to
`⟨a + (j − a), _⟩ = j` three times. One wrinkle: as commissioned the statement does not elaborate
— the `by omega` side conditions inside it have no access to `a ≤ i ≤ b < n` — so the three
bounds are carried as named components of the existential.

`ExtendStepSome`, the weak form the census does support at every basepoint at every span, is also
stated, and `s3ZigFreeInterior_of_extendStepSome` derives `S3ZigFreeInterior` from it in three
lines. It is recorded for what it is: a restatement of the goal with the shape of the witness
pinned down, not an induction.

`extendStep` itself is left unproved and commented out at the end of the file, with the verdict.

## 5. What is in the file

| name | statement |
|---|---|
| `IsTrim` | the commissioned trim: span at most one less |
| `IsInnerTrim` | the corrected trim: band strictly inside `[L, H]`, at least three wide |
| `isZigFree_append_two_inner`, `isZigFree_append_two_inner'` | the two orientations of the append at any width |
| `isZigFree_append_outer'` | the append lemma for every band strictly inside `[L, H]` |
| `zigFree_append_forces_inner` | only a trim stripping both extremes can be appended to |
| `no_outer_member_of_span_one_trim` | hence a span-`(H−L−1)` trim never yields a member |
| `ExtendStep` | the commissioned step, kept unchanged and unused |
| `ExtendStepZF` | the corrected step |
| `s3ZigFreeInterior_of_extendStepZF` | the induction it carries |
| `ExtendStepSome`, `s3ZigFreeInterior_of_extendStepSome` | the weak form, and its immediate implication |
| `no_fold_of_low_early` | no fold reaches a level the walk has not come near in time |
| `zigTail_append`, `zigLevels_append`, `zigWalk_prefix` | the walk through `ts ++ l` extends the walk through `ts` |
| `no_fold_of_early_low` | an arm that dives to `L` early is not folded by any extension |
| `arm5`, `bing6_arm_not_folded`, `isZigFree_2425_1` | the witness of §3 |
