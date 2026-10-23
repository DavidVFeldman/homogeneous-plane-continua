# Report — batch 8: the one-bump itinerary (Lemma F1′)

Delivered: `HPC/Fold/Bump.lean`, with the root `HPC.lean` as supplied by the batch (it now
imports `HPC.Fold.Bump`). The batch-8 commission text is kept as `COMMISSION-batch8.md`.
Nothing else in the project was touched.

`lake build` succeeds on the whole project. `HPC/Fold/Bump.lean` contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`, and every theorem of the file has
axiom profile exactly `[propext, Classical.choice, Quot.sound]` (three of them use fewer:
`bumpCenter_eq` needs only `propext`, and `bumpCenter_zero`, `bumpCenter_eq_lamCenter` only
`propext, Quot.sound`).

Two commissioned statements do **not** go through as written, and in both cases the failure is
not a proof difficulty but a genuine falsehood, certified in the file by an explicit
counterexample. Both are described in §3; the delivered statements are the corrected ones, and
the commissioned segmented condition is kept verbatim under the name `SegLamC`.

## 1. Census

All names live in the namespace `HPC.Fold`.

| Name | Kind | Depends on |
| --- | --- | --- |
| `bumpA`, `bumpB`, `bumpLen`, `bumpCenter` | def | — (as commissioned) |
| `bumpCenter_eq` | thm | `bumpCenter` (added; the branch test on an arbitrary integer equal to the time) |
| `bumpCenter_zero` | thm | `bumpCenter_eq`; `omega` |
| `bumpCenter_lip` | thm | `bumpCenter_eq`; `abs_le`, `Int.natCast_nonneg`, `split_ifs`, `omega` |
| `bumpCenter_eq_lamCenter` | thm | batch-6 `lamCenter`, `κ`; `split_ifs`, `omega` |
| `phase` | def | `NonAscAt` (batch 6); classical, hence `noncomputable` |
| `phase_eq_one`, `phase_eq_zero`, `phase_zero_or_one` | thm | `phase`, `Fin.le_def` |
| `phase_zero` | thm | `phase_eq_zero`, `NonAscAt` |
| `phase_mono` | thm | `phase_eq_one`, `phase_eq_zero`, `phase_zero_or_one` |
| `phase_step_nonasc` | thm | `phase_eq_one`, `phase_eq_zero`, `Fin.ext` |
| `phase_add_isLip` | thm | `phase_mono`, `phase_step_nonasc`, `phase_zero_or_one`; `abs_le`, `omega` |
| `SegLamC` | def | `phase` — the commissioned condition, kept verbatim |
| `SegLam` | def | `phase` — the delivered condition (`SegLamC` plus one clause) |
| `SegLam_imp_SegLamC` | thm | the two definitions |
| `segLam_foldsOnto` | thm | `SegLam`, `phase_add_isLip`, `phase_zero`, `phase_zero_or_one`, `bumpCenter_eq`, `bumpLen`, `FoldsOnto`; `Int.toNat_of_nonneg`, `abs_le`, `Fin.ext`, `split_ifs`, `omega` |
| `segLam_ascending_example` | thm | `segLam_foldsOnto` (added; a nondegenerate instance) |
| `segLamC_not_foldsOnto` | thm | `SegLamC`, `FoldsOnto`, `bumpLen`, `bumpCenter`; `decide`, `abs_le`, `omega` |
| `bump_degenerate_not_foldsOnto` | thm | `SegLam`, `FoldsOnto`; `decide`, `abs_le`, `omega` |
| `veeBumpLen`, `veeBumpCenter`, `SegVee` | def | — (as commissioned) |
| `segVee_foldsOnto` | thm | `segLam_foldsOnto`, batch-6 `foldsOnto_neg`; `abs_le`, `le_max_iff`, `omega` |
| `exists_blocks_first_of_segLam` | thm | `segLam_foldsOnto`, batch-6 `armG`, `armT`, `exists_blocks_first_of_folds`; batch-4/5 `Chain.Refines.minIdx`, `Chain.ofBlocks`, `Chain.unionRange` |

Mathlib dependencies are confined to: `Fin` basics (`Fin.ext`, `Fin.le_def`, `Fin.isLt`),
integer absolute value (`abs_le`), `Int.toNat_of_nonneg`, `Int.natCast_nonneg`, `le_max_iff`,
and the `omega`, `split_ifs`, `decide`, `positivity`, `push_cast`, `norm_num` tactics. `omega`
is used throughout on goals containing `max`, `min` and `Int.toNat`, which it supports; this is
what keeps the leg arithmetic short. No new imports beyond the one the skeleton had.

## 2. What was supplied at each step

* **§2, `bumpCenter_zero`.** As in the commission: `0 ≤ a`, first branch.
* **§2, `bumpCenter_lip`, *(supply: the branch arithmetic, four cases)*.** Supplied by
  `bumpCenter_eq` plus `split_ifs <;> omega`: after the centers at `u` and `u + 1` are written
  as a three-way test on the integers `u` and `u + 1`, all nine branch combinations (four of
  them vacuous) are linear arithmetic over `ℤ` in `p, h, L, u`. Both commissioned hypotheses
  of this lemma turn out to be unnecessary — `p ≤ h` and `u + 1 < bumpLen p H L h` — while
  `L + 1 ≤ h` is load-bearing (it is what makes the descending leg nonempty; with `b < 0` the
  walk jumps by `b + 3 ≥ 2` at the first seam). Following the convention of batches 1–7 the two
  unnecessary hypotheses are kept in the statement with a leading underscore.
* **§2, `bumpCenter_eq_lamCenter`.** As in the commission: for `h = κ p H` the first two
  branches of `bumpCenter` are literally the two branches of `lamCenter`, and the hypothesis
  `u ≤ a + b` excludes the third.
* **§3, the phase auxiliaries.** They were **reproved**, not lifted. Batch 6 states them only
  as `have`s inside the proof of `foldsOnto_lam_of_crit`, over a locally `set` copy `φ` of the
  phase, so there was nothing importable; the arguments are, however, exactly batch 6's
  (`hφz`, `hstepNA`, `hglip`). They are now available in their own right as `phase_zero`,
  `phase_step_nonasc`, `phase_add_isLip`, together with `phase_eq_one`, `phase_eq_zero`,
  `phase_zero_or_one`, `phase_mono`. `phase` is `noncomputable`: `NonAscAt` carries no
  `Decidable` instance, so the `if` is classical.
* **§4, the windows and the seams.** As in the commission, with two simplifications. The
  clamp `min a (…)` of the leg-1 formula is not needed: clause (3) of the condition gives
  `g j < h`, i.e. `g j - p < a`, so `max 0 (g j - p) ≤ a` always and the leg-1 time never
  leaves the ascending leg. And the whole window analysis is done once, by rewriting the
  center with `bumpCenter_eq` at the integer value of the assignment and calling
  `split_ifs <;> omega` with the segment's level bounds in context — the three legs' case
  distinctions of §4 are then discharged as linear arithmetic rather than by hand.
* **§4, Start, *(supply: the `s = t = 0` sub-case)*.** Resolved by the change of §3(a): with
  the added clause, `t = 0` is impossible for a nonempty arm, so the sub-case does not arise.
  The remaining two cases are as in the commission (`s > 0`: `g 0 = p`; `s = 0 < t`: clause (2)
  forces `h ≤ p`, hence `a = 0` and the leg-2 formula gives `0`).
* **§5, the reflected family, *(supply: the unfolding)*.** `segLam_foldsOnto` applied to
  `g = −f`, then batch-6 `foldsOnto_neg`. The reflected hypotheses are exactly the
  commissioned `l ≤ p`, `min (L+1) p ≤ l`, `p ≤ H`, plus the reflection `l + 1 ≤ H` of the new
  hypothesis `L + 1 ≤ h` of §3(b).
* **§6, the consequence for chains.** As in the commission: `segLam_foldsOnto` on each arm
  (the base value of both arms is `minIdx i`, i.e. `p`), then batch-6
  `exists_blocks_first_of_folds` with `len := bumpLen p H L hb` and `c := bumpCenter p H L hb`.

## 3. The two changes, with their counterexamples

### (a) `SegLam` needs a nonempty middle segment (`segLamC_not_foldsOnto`)

The commissioned condition is insufficient. Its clauses (1), (3), (4) are conditions on
indices `< s` or in `[s, t)`, and clause (5) is vacuous when `t = 0`; so `s = t = 0` satisfies
the condition for **every** arm whose peak clause (2) holds at the first index, i.e. whenever
`h ≤ p`. Since the theorem also allows `p ≤ h`, this means every arm with `p = h` satisfies the
commissioned condition — including arms that cannot fold, because the walk `Λ(h)` descends to
`L + 1` before it climbs again and an arm that only ascends can never follow it.

The counterexample in the file is `p = h = 3`, `L = 0`, `H = 6`, arm `3, 4, 5, 6`. The walk is
`3, 2, 1, 2, 3, 4, 5` (seven times). The assignment starts at time `0` (center `3`), cannot be
at time `1` (center `2`) at index `1` where the level is `4`, hence is still `0` there, and at
index `2`, level `5`, neither time `0` nor time `1` has a center within one. So no fold exists,
while `SegLamC` holds with `s = t = 0`.

Diagnosis: with `s = t` the assignment jumps from the leg-1 formula straight to the leg-3
formula, and those differ by `b + 1` at the seam. The delivered `SegLam` therefore strengthens
clause (5) from

```
t = m ∨ ∀ j, j + 1 = t → f j ≤ L + 1
```
to
```
t = m ∨ (s < t ∧ ∀ j, j + 1 = t → f j ≤ L + 1),
```

i.e. leg 3 may only be used if leg 2 is nonempty. This is the option the commission itself
offers in §4 ("strengthen `SegLam` to require `0 < t` …"), in the slightly stronger form that
the whole middle segment, not just the prefix before it, is nonempty. The weaker form `0 < t`
alone would not repair the construction: the same seam jump of `b + 1` occurs at any
`s = t > 0` with `b ≥ 1`, where the assignment again passes from leg 1 directly to leg 3. The commissioned condition is kept verbatim as `SegLamC`, and `SegLam_imp_SegLamC`
records that the delivered condition is the stronger of the two, so no theorem of the file
applies to fewer arms than a corrected reading of the commission would allow.

With the new clause the seam analysis is exactly the commission's: at the first seam the
leg-1 value is `max 0 (a − 1)` and the leg-2 value is `a`; at the second seam the leg-2 value
is `a + b` or `a + b − 1` (because `L ≤ f (t−1) ≤ L + 1`) and the leg-3 value is `a + b`
(because `f t ≤ L + 2`).

### (b) `segLam_foldsOnto` needs `L + 1 ≤ h` (`bump_degenerate_not_foldsOnto`)

The commissioned hypotheses allow `h = L` (they only ask `L ≤ p ≤ h`), and then `b = −1`: the
itinerary is `p = L` at time `0` and `L + u + 2` afterwards, a walk whose first step is a jump
of three, which no 1-Lipschitz assignment with unit windows can follow when the levels in
between are attained. The counterexample in the file is `p = h = L = 0`, `H = 2`, arm
`0, 1, 2`: here `bumpLen = 1`, so the only time is `0` with center `0`, while the arm reaches
level `2`. The arm satisfies the delivered `SegLam` with `s = 0`, `t = 2`.

The hypothesis `L + 1 ≤ h` — which the commission already imposes on `bumpCenter_lip`, and
which is exactly the statement that the descending leg of `Λ(h)` is nonempty — is therefore
added to `segLam_foldsOnto`, and its reflection `l + 1 ≤ H` to `segVee_foldsOnto`, and
`L + 1 ≤ hb` to `exists_blocks_first_of_segLam`. Nothing else in any commissioned signature
changed.

## 4. Statements that failed, and load-bearing hypotheses

No commissioned statement failed for any reason other than the two falsehoods of §3, and each
of those is replaced by the nearest correct statement plus the counterexample that forces the
correction. No delivered statement is weakened in its conclusion.

Unused commissioned hypotheses (kept, with a leading underscore, as in batches 1–7):

* `bumpCenter_lip`: `p ≤ h` and `u + 1 < bumpLen p H L h`;
* `segLam_foldsOnto`: `h ≤ max (H − 1) p` and `L ≤ p`.

The other hypotheses of `segLam_foldsOnto` are all load-bearing: `p ≤ h` (nonnegativity of the
assignment), `f 0 = p` (the start), `L ≤ f` (leg 2's branch test and leg 3's window), `f ≤ H`
(the length bound), `L + 1 ≤ h` (§3(b)), and every clause of `SegLam` is used — (1) in the
leg-1 window, (2) at the first seam and at the start, (3) in the leg-1 window and length
bound, (4) in the leg-2 window and at the second seam, (5) at both seams and at the start.

`segLam_ascending_example` records a nondegenerate instance (`p = 0`, `h = 2`, `L = 0`,
`H = 3`, arm `0, 1, 2`, splitting at `s = 2`, `t = m`), so the hypothesis of F1′ is certified
satisfiable and the theorem is not vacuous.

## 5. Not in this batch

F2′ — that a common bump height exists for both arms — is untouched, as are Bing 1948
Theorems 3–6 in their unconditional form, the reduction, and the D8/D9 gap.
