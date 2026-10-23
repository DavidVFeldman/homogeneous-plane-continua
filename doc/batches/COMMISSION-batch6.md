# Commission: batch 6 — the Λ-itinerary and the peak-window criterion (Lemma F1)

**Go!** Runs on top of the batch-5 delivery. One new file, `HPC/Fold/Itinerary.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Bing 1948 Theorems 3 and 4 reduce (batch 5, `Schedule.lean`) to a statement about the
1-Lipschitz integer sequence of minimal indices: that it can be scheduled from any link with
fibers in three-level windows. The schedule is built by folding the two arms of the sequence,
read outward from the link, onto a common explicit walk — the Λ-itinerary or its reflection.
This batch proves the exact characterization of which arms fold onto the Λ-itinerary
(Lemma F1), derives the V case by reflection, proves that two folded arms assemble into a
schedule of the whole sequence, and connects that to block consolidations of chains. What it
does not prove is that crookedness forces both arms to accept a common itinerary (Lemma F2);
that is the remaining mathematics and is not commissioned.

Lemma F1 has been checked against a brute-force reachability computation on every arm of
every crooked sequence of length ≤ 12 on six levels and on ~500 000 random crooked sequences
up to length 60, with no exceptions.

## Protocol

As batches 1–5. Batch-5 results expected to be used in the last theorem:
`Chain.IsSchedule`, `Chain.exists_blocks_of_walk`, `Chain.Refines.minIdx`.

## 1. Definitions

- `IsLip f`: `|f (j+1) − f j| ≤ 1`.
- `κ p H = max (H−1) p`, the peak level.
- `lamLen`, `lamCenter`: the walk `p, p+1, …, κ` (times `0..κ−p`) followed by
  `κ−1, κ−2, …, L+1` (when `κ−1 ≥ L+1`; otherwise nothing). Write `a := κ − p` for the peak
  time. The window of time `u` is `[lamCenter u − 1, lamCenter u + 1]`.
- `FoldsOnto f len c`: a Lipschitz `β : Fin m → ℕ` with values `< len`, `β 0 = 0`, and
  `|f j − c (β j)| ≤ 1`.
- `NonAscAt f t`: `t ≥ 1` and `f t ≤ f (t−1)`.
- `CritLam f p H`: `p ≥ κ`, or for every index `d` with `f d ≤ p−2`, the prefix `[0, d)`
  contains a link `≥ κ`, or two links `≥ κ−1`, or a link `≥ κ−1` with a non-ascending step
  strictly before it. Quantifying over every drop index `d` is equivalent to requiring it for
  the first drop, and is vacuous when there is no drop.
- The V-itinerary and `CritVee` are the Λ-itinerary and `CritLam` of `−f` with `p, H, L`
  replaced by `−p, −L, −H`.

## 2. Proofs of the small lemmas

**lamCenter_zero.** `0 ≤ κ − p` since `κ ≥ p`; so the center is `p + 0`.

**lamCenter_lip.** On the ascending leg consecutive centers differ by `+1`; on the descending
leg by `−1`; at the seam `u = a`, `u + 1 = a + 1`: centers `κ` and `κ − 1`. The bound
`u + 1 < lamLen` keeps `u + 1` inside the walk.

**lamCenter_covers.** For `ℓ ∈ [p, κ]` take `u = ℓ − p` (center `ℓ`). For `ℓ ∈ {κ+1}` (only
possible if `H = κ + 1`) take `u = a` (center `κ`). For `ℓ ∈ [L+1, κ−1]` take
`u = a + (κ − ℓ)` (center `ℓ`), which is `< lamLen` since `κ − ℓ ≤ κ − L − 1`. For `ℓ = L`
take `u = a + (κ − L − 1)` (center `L+1`) if `κ − L − 1 ≥ 1`; otherwise `κ ≤ L + 1`, so
`p ≤ κ ≤ L+1` and `ℓ = L ≥ p − 1`, and `u = 0` (center `p`) serves. *(supply: the case split.)*

**armG_isLip, armT_isLip.** Reindex `hf`.

## 3. Lemma F1

Throughout, `f` is Lipschitz with `f 0 = p` and values in `[L, H]`; write `κ`, `a = κ − p`.

### (⇐) The criterion gives a fold

**Case `p ≥ κ`.** Then `κ = p` and `H ≤ p + 1`; the walk is `p` (time 0) then `p−1, …, L+1`
(time `u ≥ 1` has center `p − u`). Put `β j := max (0, p − 1 − f j)`. If `f j ≤ p − 1` the
center at time `p − 1 − f j` is `f j + 1`; if `f j ∈ {p, p+1}` the time is `0` with center
`p`. Lipschitz since `f` is. Bounded by `p − 1 − L = lamLen − 1`.

**Case `p < κ`.** Then `κ = H − 1`, `a ≥ 1`.

*Phase.* `φ j := 1` if some `t ≤ j` has `NonAscAt f t`, else `0`. `φ` is monotone and steps
from `0` to `1` exactly at the first non-ascending step.

*Phase-one assignment.* `β₁ j := max (0, f j − p + φ j)`. Window: if unclamped, the center at
time `f j − p + φ j` is `f j + φ j`, within one of `f j`; if clamped, `f j = p − 1`, `φ j = 0`,
center `p`. Lipschitz: at a step `t`, `(f t − f (t−1)) + (φ t − φ (t−1))`; if `φ` steps at
`t` then `f t ≤ f (t−1)` so the sum is in `{0, 1}`; otherwise it is `f t − f (t−1)`. Clamping
preserves Lipschitz.

*The switch index.* Let `m₀` be the first drop index (`f m₀ ≤ p − 2`), or `m` if none. Let
`j*` be the least `j < m₀` with `f j + φ j ≥ κ`, if any. The criterion supplies `j*` when
`m₀ < m`: a link `j` with `f j ≥ κ` has `f j + φ j ≥ κ`; two links `j₁ < j₂` with
`f ≥ κ − 1` — if some step in `(j₁, j₂]` is non-ascending then `φ j₂ = 1` and
`f j₂ + 1 ≥ κ`, and otherwise `f` strictly increases on `[j₁, j₂]` so `f j₂ ≥ κ`; a link
`j` with `f j ≥ κ − 1` and a non-ascending step before it has `φ j = 1`. Note that on the
prefix `[0, m₀)` all levels are `≥ p − 1`.

*Before the switch.* For `j < j*`, `f j + φ j ≤ κ − 1`, so `β₁ j ≤ a − 1`; use `β j := β₁ j`.

*At the switch.* `β j* := a`. Lipschitz from `j* − 1` (note `j* ≥ 1` since `f 0 + φ 0 = p <
κ`): if `φ j* = φ (j*−1)` then `f (j*−1) + φ (j*−1) ≥ κ − 1` so `β₁ (j*−1) ≥ a − 1`; if `φ`
steps at `j*` then `f (j*−1) ≥ f j* ≥ κ − 1`, again `β₁ (j*−1) ≥ a − 1`. Window at the
peak: `f j* ≥ κ − 1` (as `φ ≤ 1`) and `f j* ≤ H = κ + 1`.

*After the switch.* `β₂ j := a + max (0, κ − 1 − f j)` for `j > j*`. Center at time `a + d`
with `d ≥ 1` is `κ − d`; for `f j ≤ κ − 1`, `d = κ − 1 − f j` gives center `f j + 1`; for
`f j ≥ κ − 1`, `d = 0` gives center `κ`, within one since `f j ≤ κ + 1`. `β₂ j* = a`, so
the assignment is continuous at the switch. Lipschitz since `f` is. Bounded by
`a + (κ − 1 − L) = lamLen − 1`.

*No drop.* If `m₀ = m` and no `j*` exists, `β₁` alone is a fold, with `β₁ ≤ a − 1 < lamLen`.
If `m₀ = m` and `j*` exists, the switch construction applies unchanged.

### (⇒) A fold satisfies the criterion

If `p ≥ κ` there is nothing to prove; assume `a ≥ 1`. If `f` never drops to `≤ p − 2` the
criterion holds vacuously. Otherwise let `d` be any drop index and `β` a fold. The center at
time `β d` is within one of `f d ≤ p − 2`, hence `≤ p − 1`; ascending-leg centers are `≥ p`,
so `β d` is on the descending leg with center `≤ p − 1`, i.e. `β d ≥ a + (κ − (p − 1)) > a`.
Since `β 0 = 0 < a < β d` and `β` is Lipschitz, some `j < d` has `β j = a` (discrete IVT); let
`j₀` be the least such. Then `j₀ ≥ 1`, `β (j₀ − 1) = a − 1`, and by the windows
`f j₀ ≥ κ − 1` and `f (j₀ − 1) ∈ {κ − 2, κ − 1, κ}`.

- If `f j₀ ≥ κ`: first clause with `j = j₀ < d`.
- If `f j₀ = κ − 1` and `f (j₀ − 1) ≥ κ − 1`: second clause with `j = j₀ − 1`, `j' = j₀`.
- If `f j₀ = κ − 1` and `f (j₀ − 1) = κ − 2`: some step in `[1, j₀ − 1]` is non-ascending,
  giving the third clause. For if all steps `1..j₀` were strictly ascending then
  `f j₀ = p + j₀`, so `a = κ − p = f j₀ + 1 − p = j₀ + 1`; but `β` is Lipschitz from `β 0 = 0`,
  so `β j₀ ≤ j₀ < a`, contradicting `β j₀ = a`. (The step `j₀` itself is ascending in this
  subcase, so the non-ascending step is strictly before `j₀`.)

## 4. The V case

`foldsOnto_vee_iff`: negate. `g := −f` is Lipschitz with `g 0 = −p` and values in `[−H, −L]`;
`FoldsOnto f (veeLen …) (veeCenter …)` unfolds to `FoldsOnto g (lamLen (−p) (−L) (−H))
(lamCenter (−p) (−L) (−H))` because `|f j − (−c)| = |g j − c|`; apply `foldsOnto_lam_iff` to
`g`. *(supply: the unfolding.)*

## 5. Assembly

`exists_schedule_of_folds`: let `βG`, `βT` be the two folds. Define `β t := βG ⟨t − i, _⟩` for
`t ≥ i` and `β t := βT ⟨i − t, _⟩` for `t ≤ i`; at `t = i` both give `0`, so the definition is
consistent. Bounds and windows come from the folds. Lipschitz across `i`: the step `i → i+1`
is `βG 0 → βG 1`, the step `i−1 → i` is `βT 1 → βT 0`, both Lipschitz by the folds; away from
`i` the steps are steps of one fold.

## 6. Bridge

`exists_blocks_first_of_folds`: with `ρ t := (minIdx t : ℤ)`, `ρ` is Lipschitz (batch 4,
`minIdx_lip`), and `exists_schedule_of_folds` gives `β` with `β i = 0`, Lipschitz, and
`|minIdx t − c (β t)| ≤ 1`. Then `IsSchedule β` holds (Lipschitz; attains `0` at `i`), and
batch-5 `exists_blocks_of_walk` with `b := c` gives the block consolidation with blocks inside
three consecutive links; its `∀ t, (β' t).val = β t` clause gives `(β' i).val = 0`.

## 7. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step; any statement that did not go through.

## 8. Not in this batch

Lemma F2 (crookedness forces a common itinerary); Bing 1948 Theorems 3, 4, 5, 6; the
reduction; the D8/D9 gap.
