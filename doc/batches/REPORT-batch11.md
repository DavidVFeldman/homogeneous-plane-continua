# Report — batch 11: the Phase Lemma

Delivered complete. The batch-11 archive was unpacked into the project: the new file
`HPC/Fold/Phase.lean`, with the root `HPC.lean` supplied by the batch, and the commission text
kept as `COMMISSION-batch11.md`. Nothing else was touched.

`lake build` succeeds on the whole project. `HPC/Fold/Phase.lean` contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`, and elaborates with no linter
warnings.

## 1. Census

All names live in namespace `HPC.Fold`, in `HPC/Fold/Phase.lean`.

| Name | Kind | Depends on |
| --- | --- | --- |
| `climb_of_no_nonAsc` | private theorem (step extraction) | `NonAscAt` (batch 6); `Fin.ext`, `omega`, `push_cast` |
| `exists_nonAsc_of_climb` | theorem (**the Phase Lemma**) | `IsCrookedSeq` (batch 7), `NonAscAt`, `climb_of_no_nonAsc`; `Fin.lt_def`, `Fin.le_def`, `Fin.ext`, `abs_of_nonneg`, `omega` |
| `phase_eq_one_of_climb` | theorem | `exists_nonAsc_of_climb`, `phase`, `phase_eq_one` (batch 8); `Fin.le_def` |
| `exists_peak_index_of_one_short` | theorem (**the one-short lemma**) | `hStarArm`, `hStarArm_mem` (batch 9), `phase`, `phase_eq_one_of_climb`; `omega` |
| `SmallDemandCase` | definition (recorded, not proved) | `IsLip`, `IsCrookedSeq`, `hStar`, `lStar`, `SegLam`, `SegVee`, `armG`, `armT` |
| `Agreement` | definition (recorded, not proved) | `IsLip`, `IsCrookedSeq`, `hStarArm`, `lStarArm`, `armG`, `armT` |

Mathlib use is confined to `Fin` index arithmetic (`Fin.ext`, `Fin.lt_def`, `Fin.le_def`,
`Fin.isLt`), `abs_of_nonneg`, and the tactics `omega`, `push_cast`, `simpa`.

## 2. Changes to the skeleton

None. Every commissioned statement is delivered verbatim, with the same hypotheses, and none
was weakened. The only addition is the private auxiliary `climb_of_no_nonAsc`, which is the
step-extraction the commission asks for in §1.

Hypothesis check: in all three theorems every explicit hypothesis is load-bearing (`hc`, `h0`,
`hj` in the Phase Lemma and its phase corollary; `hc`, `h0`, `hdem`, `hhigh` in the one-short
lemma). No commissioned hypothesis turned out to be unnecessary in this batch, so nothing is
marked unused.

## 3. How the step extraction was done

`climb_of_no_nonAsc` is stated with a natural-number offset rather than with two `Fin` indices:
for a base index `a` and an offset `k`, if no index of `(a, a + k]` carries a non-ascending
step then `A ⟨a⟩ + k ≤ A ⟨a + k⟩`. It is proved by induction on `k`. In the successor step, the
absence of a non-ascending step at `a + (k + 1)` is unfolded: `NonAscAt` at that index asks for
`0 < a + (k+1)`, which is immediate, and for `A ⟨a+(k+1)⟩ ≤ A ⟨t'⟩` at the unique predecessor
`t'`, which by `Fin.ext` is `⟨a + k⟩`; so its failure is exactly the strict ascent
`A ⟨a+k⟩ < A ⟨a+(k+1)⟩`, and the induction hypothesis then gives the claim.

The Phase Lemma applies this at `a = r`, `k = r' − r`. Crookedness at `(0, j)` — legitimate
because `A j ≥ p + 3 = A ⟨0⟩ + 3`, so the indices differ and the levels differ by at least
three — produces `0 < r < r' < j` with `A r ≥ A j − 2 ≥ p + 1` and `A r' ≤ p + 1`, hence
`A r' ≤ A r` with `r < r'`. If no index `≤ j` were a non-ascending step, then in particular
none of `(r, r']` would be, and the step extraction would give `A r + (r' − r) ≤ A r'` with
`r' − r ≥ 1`, contradicting `A r' ≤ A r`. The extracted index `t` satisfies `t ≤ r' < j`, so it
is at or before `j` as required.

`phase_eq_one_of_climb` is then `phase_eq_one` applied to that index, and
`exists_peak_index_of_one_short` is the composition: `hStarArm_mem` supplies an index `s` with
`A s = hStarArm A p` and the window condition for every earlier index; since
`A s = hStarArm A p ≥ p + 3`, the phase at `s` is `1`, so
`A s + phase A s = hStarArm A p + 1 ≥ h` by the one-short hypothesis.

## 4. Did the weakened `IsCrookedSeq` suffice?

Yes, throughout. Only the two inequalities of the ascending case are used — `A j − 2 ≤ A r` and
`A r' ≤ p + 1` — and not the exact values of the strong form `IsCrookedSeqStrong`. In fact the
lower bound on `A r` is used only through `A r ≥ p + 1`, so even the crookedness margin is not
tight: the argument needs a climb of three exactly because `3 ≤ |A j − A 0|` is what licenses
the appeal to crookedness.

## 5. The two recorded statements

`SmallDemandCase` and `Agreement` are recorded as Prop-valued definitions exactly as
commissioned. Neither is proved, neither is used by any theorem here, and neither was
strengthened or weakened. Nothing was found false while formalizing: no instance of either
statement was contradicted, and no commissioned statement failed to go through.

## 6. Axiom profiles

```
'HPC.Fold.exists_nonAsc_of_climb'          [propext, Classical.choice, Quot.sound]
'HPC.Fold.phase_eq_one_of_climb'           [propext, Classical.choice, Quot.sound]
'HPC.Fold.exists_peak_index_of_one_short'  [propext, Classical.choice, Quot.sound]
```

(`Classical.choice` enters through `phase`, which is defined by a classical `if`, and through
`hStarArm`, defined as a supremum.)
