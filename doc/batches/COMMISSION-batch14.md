# Commission: batch 14 — the witnesses in the residual configuration

**Go!** Runs on top of the batch-13 delivery. One new file, `HPC/Fold/Witnesses.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Batch 13 left two open definitions. One of them, `MixedGapUp_witnesses`, is discharged here:
in the configuration `MixedGapUp` forbids, the two exits from the window around the basepoint
exist and are of opposite kinds, with the window intact between them. The construction uses
the single-arm lemma of batch 12 and nothing about crookedness.

`sync_up` then applies, placing a link at exactly `p + 1` strictly between the two exits. The
case analysis on which arm carries that link is where the remaining work sits, and one branch
of it is proved here.

Note the configuration is empty in every instance examined (0 out of 2 890 280 crooked
basepoints), so nothing below can be checked numerically — it is all derived from the
hypotheses. That is the reason for proving it rather than testing it.

## Protocol

As batches 1–13. Expected: `hStarArm`, `hStarArm_mem`, `le_hStarArm`, `lStarArm`,
`lStarArm_mem`, `lStarArm_le` (batch 12), `not_hStarArm_and_lStarArm`,
`le_lStarArm_of_hStarArm`, `hStarArm_le_of_lStarArm` (batch 12), `armG`, `armT`, `IsLip`,
`IsCrookedSeqUp`, `sync_up`, `MixedGapUp_witnesses` (batch 13).

## 1. First exits

**exists_first_rise.** From `p + 2 ≤ hStarArm A p` and `hStarArm_mem` there is `j₀` with
`A j₀ = hStarArm A p ≥ p + 2` and `p − 1 ≤ A j'` for every `j' ≤ j₀`. The set of indices with
`A ≥ p + 2` is nonempty (it contains `j₀`); let `r` be its least element, so `r ≤ j₀`.

`A r = p + 2` exactly: `r ≥ 1` since `A 0 = p`; the predecessor has `A < p + 2`, i.e.
`≤ p + 1`, and `IsLip` gives `A r ≤ A (r−1) + 1 ≤ p + 2`, while `A r ≥ p + 2` by choice.

For `j < r`: `A j ≤ p + 1` by minimality of `r`, and `A j ≥ p − 1` because `j < r ≤ j₀`.

**exists_first_drop.** The same with `lStarArm_mem` and the least index with `A ≤ p − 2`.
*(supply: either mirror the argument directly, or apply `exists_first_rise` to `−A` at `−p`
and unfold `lStarArm`. The second is available here because no crookedness hypothesis is
involved — see batch 13 on why reflection is unsound when there is one.)*

## 2. The witnesses

**mixedGapUp_witnesses.** Fix `ρ`, `i`, and put `p := ρ i`. Assume
`hStarArm (armT) + 2 ≤ hStarArm (armG)` and `lStarArm (armT) + 2 ≤ lStarArm (armG)`.

`le_hStarArm` gives `p ≤ hStarArm (armT)`, so `hStarArm (armG) ≥ p + 2`. By
`le_lStarArm_of_hStarArm` applied to `armG`, `lStarArm (armG) ≥ p − 1`.

`lStarArm_le` gives `lStarArm (armG) ≤ p`, so `lStarArm (armT) ≤ p − 2`. By
`hStarArm_le_of_lStarArm` applied to `armT`, `hStarArm (armT) ≤ p + 1`. (This last is not
needed for the witnesses but is recorded in §4 below.)

Apply `exists_first_rise` to `armG` — its hypotheses hold, with base value `p` since
`armG ρ i 0 = ρ i` — to get `rG` with `armG rG = p + 2` and the window intact strictly before.
Apply `exists_first_drop` to `armT` similarly to get `dT`.

Set `u :=` the global index of `armT`'s index `dT`, namely `i − dT`, and `v :=` the global
index of `armG`'s index `rG`, namely `i + rG`. Then `u < v`, since `dT ≥ 1` and `rG ≥ 1` (both
arms take the value `p` at index `0`, which is neither `p + 2` nor `p − 2`).

`ρ u = p − 2` and `ρ v = p + 2` by the two exit lemmas. For the window: a global index `w`
strictly between `u` and `v` is either `i − b` for some `0 ≤ b < dT`, or `i`, or `i + a` for
some `0 < a < rG`; in the first case `armT b` is inside the window by `exists_first_drop`, in
the third `armG a` is by `exists_first_rise`, and in the second `ρ i = p`.

*(supply: the index translation between arms and the global sequence, which is the bulk of the
work. `armG ρ i j = ρ ⟨i + j, _⟩` and `armT ρ i j = ρ ⟨i − j, _⟩` hold definitionally; the
trichotomy on `w` is `omega` after unfolding `Fin.lt_def`.)*

## 3. What `sync_up` gives

**exists_peak_link_between.** Combine `mixedGapUp_witnesses` with `sync_up` at `u`, `v`,
whose hypotheses are exactly the conclusion of the former. The `sync_up` of batch 13 concludes
`ρ j ∈ [p − 1, p]` and `ρ k = p + 1` — note it pins the *second* witness, not the first; that
is what the upward form gives, and it is the reason this batch works with `IsCrookedSeqUp`
rather than `IsCrookedSeq`.

## 4. One branch of the case analysis

**hStarArm_eq_of_peak_on_T.** Suppose the `p + 1` link lies at a global index `k ≤ i`, that is,
on the backward arm, at `armT`'s index `b := i − k`. Since `k` is strictly between `u` and
`v`, `b < dT`, so every index `≤ b` on `armT` is inside the window, in particular `≥ p − 1`.
Hence `p + 1 = armT b` belongs to the set defining `hStarArm (armT)`, so
`hStarArm (armT) ≥ p + 1`. With `hStarArm (armT) ≤ p + 1` from §2, equality. The gap
hypothesis then gives `hStarArm (armG) ≥ p + 3`.

The complementary branch — the `p + 1` link on the forward arm, strictly before its first rise
— is **not** in this batch. It is the remaining content of `MixedGapUp`.

## 5. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: how the index translation of §2 was handled; whether `exists_first_drop` was
   mirrored or obtained by reflection; what was supplied; any statement that did not go
   through. If `mixedGapUp_witnesses` turns out **not** to follow — in particular if the
   single-arm lemma does not give `lStarArm (armG) ≥ p − 1` in the form needed — report that
   in preference to anything else.

## 6. Not in this batch

`MixedGapUp` itself and the forward-arm branch of §4; `SmallDemandCase`; `HighExitValley`; the
assembly into `F2Prime`; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
