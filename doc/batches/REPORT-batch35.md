# Report: batch 35 — the cut route

One new file, `HPC/Fold/CutRoute.lean` (424 lines); root `HPC.lean` updated with its import;
`README.md` notes the batch; the commission text is kept as `COMMISSION-batch35.md`. Nothing
else was touched: the forty-three earlier Lean files are byte-identical to the batch-34
delivery. The whole project builds. The new file has no `sorry`, `admit`, `axiom`,
`native_decide` or `@[implemented_by]` outside the three commented blocks that keep the
commissioned statements that are not proved, it adds no linter warnings, and every theorem in it
has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

The census is `census-batch35.c` with its output in `census-batch35.log`.

---

## 1. The counterexample, first: the commissioned `CutData` is empty

**`CutData` as commissioned is satisfied by nothing** — no sequence, no band, no choice of the
four indices. Two of its clauses contradict two others, locally:

* `atR` asks for `H − 1 ≤ ρ r`, and `bandA` asks for `ρ j ≤ H − 2` for every `a ≤ j ≤ r`, which
  includes `j = r` (`cutData_top_clash`);
* `atR'` asks for `ρ r' ≤ L + 1`, and `bandB` asks for `L + 2 ≤ ρ j` for every `r ≤ j ≤ r'`,
  which includes `j = r'` (`cutData_bot_clash`).

Hence `not_cutData : ¬ CutData ρ L H a r r' b`, with no hypotheses at all. The consequences run
through the whole of the commission's §2–§3:

* **`exists_cutData` is false.** Its hypotheses are satisfiable — `cutSeq` (batch 26) meets every
  one of them at `L = 3`, `H = 7`, `a = 0`, `b = 12`, and that is checked in Lean as
  `cutSeq_cutData_hypotheses` — while its conclusion is refuted
  (`not_exists_cutData_cutSeq`). The commissioned statement is kept, commented out, with this
  explanation.
* **`cutData_spans` is true but vacuous**; it is proved, from the emptiness of its hypothesis.
* **`cutWalk` is provable outright** (`cutWalk`), again by vacuity, so it is *not* the search
  item the commission took it for; it is proved in three lines.
* **`s3ZigFreeInterior_of_cutWalk` cannot be proved short of proving the goal**: since `CutWalk`
  holds, `(CutWalk → S3ZigFreeInterior)` is *equivalent* to `S3ZigFreeInterior`
  (`s3ZigFreeInterior_iff_cutWalk_imp`). The commissioned statement is kept, commented out.

The census confirms the emptiness numerically where it can be seen, which is everywhere: over
every contiguous subchain of `bing 0 n` taken as an ambient with its own band, 66 258 quadruples
at span six, 654 535 at span seven and 5 705 345 at span eight satisfy the two crossing clauses
`atR` and `atR'`, and **0 of them satisfy `bandA`, 0 satisfy `bandB`, and 0 satisfy `CutData`**
(`census-batch35.log` §1).

This is not a typo in one clause. `crookedIvF_cut_first` reaches `H − 2` at `r`, not `H − 1`,
and the whole point of `r'` is that the sequence *falls to* `L + 1` there — so the stretch
`[r, r']` cannot also be banded from below at its own right endpoint. The corrected form has to
change three clauses, not one.

## 2. Did the repackaging need hypotheses the commission omitted?

Yes, and it needed fewer of others.

* **`a` and `b` must be a bottom index and a *later* top index**, as the commission anticipated
  in its parenthesis. They are taken as elements of `Fin n` rather than as naturals with `∀ j`
  clauses, which is what `crookedIvF_cut_first` consumes.
* **The ambient bounds `hLb`, `hHb` are not needed** for the cut itself; they are needed only for
  the band statement `cutData'_spans`, where they supply the trivial sides.
* **Three clauses change.** `CutData'` has `ρ r = H − 2` (exactly, not `≥ H − 1`), `bandA` over
  the *half-open* stretch `(a, r]` (its value at `a` is `L`, which is pinned by `bot`), and
  `bandB` over the *open* stretch `(r, r')`. With those changes `exists_cutData'` is a
  repackaging of `crookedIvF_cut_first` and nothing more.
* **The reduction needs reversal symmetry**, as the commission said it might. It was not
  available and is proved here: `isCrookedIvF_revSeq` (faithful crookedness survives reversing
  the sequence — the crookedness clause maps to itself with the two witnesses and the two
  produced indices exchanged) and `s3ZigFreeInterior_arms_rev` (a walk serving both arms at the
  reversed basepoint serves both arms at the original). With them,
  `s3ZigFreeInterior_of_cutWalk'` splits on whether the attained bottom comes before the attained
  top and reverses in the second case.

## 3. How far `cutWalk` got

### 3.1 The premise of the route is false

The commission's reason for changing route was:

> Those bands are two narrower than the ambient, which is exactly what `isZigFree_append_outer'`
> requires and exactly what the trim route could not produce.

They are not. `isZigFree_append_outer'` requires `L + 1 ≤ L'` **and** `H' ≤ H − 1`: strictly
inside at *both* ends. Each stretch of the cut is narrower at one end only. The first stretch
`[a, r]` is banded above by `H − 2` — and contains `a`, whose level is `L` exactly. So batch 34's
obstruction applies to it verbatim:

* `no_outer_member_of_boundary_trim`: if the inner band reaches down to `L` or up to `H`, no
  member of its family becomes a member of the family of `[L, H]` when the outer legs are
  appended (immediate from `zigFree_append_forces_inner`);
* `cut_stretchA_no_extension`: the instance with `L' = L`, which is the cut's first stretch.

The census measures the same thing over 2 376 400 cuts at span ten: the first stretch `[a, r]`
has a level at `L` in **every** one of them (0 strictly above `L`), while the second stretch
`[r, r']` is strictly inside at both ends in 2 375 165 of them. Dropping the left endpoint fixes
the first stretch in 2 276 991 of 2 376 400 cuts (96 %) — the cut alone does not do it.

### 3.2 The gate: a walk built from the cut does not serve every interior basepoint

Taking the only repair available — the *core* of the cut's stretch, the maximal subinterval
containing the basepoint whose levels avoid `L` and `H`, so that the band is strictly inside and
the append lemma does apply — the census runs batch 34's gate over `bing 0 n`, `n = 6 … 12`,
at every interior basepoint, with the enclosing cut (`a` the last bottom index at or before the
basepoint, `b` the first top index at or after it):

| span | interior basepoints | existence | SOME extends | EVERY extends |
|---:|---:|---:|---:|---:|
| 6 | 25 | 25 | 24 | 13 |
| 7 | 104 | 104 | 98 | 64 |
| 8 | 319 | 319 | 296 | 204 |
| 9 | 868 | 868 | 797 | 584 |
| 10 | 2 229 | 2 229 | 2 026 | 1 523 |
| 11 | 5 556 | 5 556 | 5 011 | 3 887 |
| 12 | 13 635 | 13 635 | 12 239 | 9 657 |

*existence*: some member of the core's free family folds both core arms at the basepoint — this
holds everywhere. *SOME* / *EVERY*: some / every such member's extension by the two outer legs
folds both whole arms (and, for EVERY, is a member of the free family of `[L, H]`; the membership
never failed — 0 serving members at any span had an oriented extension outside the family, which
is `isZigFree_append_outer'` doing its work, the core's band being strictly inside).

So **the cut's own stretch is a worse trim than batch 34's**: batch 34's inner trims passed the
weak form at every interior basepoint at every span, and the cut's core fails it already at span
six — at basepoint 65 of `bing 0 6`, core `[17, 69]`, band `[1, 5]`, where no member of the
core's family extends to fold both whole arms. From span seven on the first failure is at
basepoint 5 with the core running from index 1 to the first crossing `r`.

The strong form fails much more widely, first at basepoint 5 of `bing 0 6`, core `[1, 12]`, band
`[1, 4]`, with the member `[2, 3, 2]` — the same shape of failure that batch 34 proved is forced
by timing (`no_fold_of_early_low`).

### 3.3 What the route is worth

`CutWalk'`, the corrected statement, is proved to imply the interior case
(`s3ZigFreeInterior_of_cutWalk'`). It is also implied by it, trivially, since the cut always
exists — so `cutWalk'_iff_s3ZigFreeInterior`: **the route adds data to work with, not strength to
the statement**. `cutWalk'` is left unproved and uncommented-out at the end of the file. No
construction suggested itself, so there is no span at which one was last checked; what the census
says is that the obvious construction — extend a member of the cut stretch's core — does not
serve every interior basepoint, at any span from six on.

## 4. Summary of the Lean content

Refutations and vacuities:
`cutData_top_clash`, `cutData_bot_clash`, `not_cutData`, `cutSeq_cutData_hypotheses`,
`not_exists_cutData_cutSeq`, `cutData_spans` (vacuous), `cutWalk` (vacuous),
`s3ZigFreeInterior_iff_cutWalk_imp`.

The corrected cut:
`CutData'`, `exists_cutData'`, `cutData'_spans`.

The obstruction the cut inherits:
`no_outer_member_of_boundary_trim`, `cut_stretchA_no_extension`.

Reversal symmetry:
`isCrookedIvF_revSeq`, `s3ZigFreeInterior_arms_rev`.

The route:
`CutWalk'`, `s3ZigFreeInterior_of_cutWalk'`, `cutWalk'_iff_s3ZigFreeInterior`.

## 5. Not in this batch

The linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4, 5, 6; the reduction in
Bing 1951; the D8/D9 gap.
