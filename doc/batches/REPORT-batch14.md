# Report — batch 14: the witnesses in the residual configuration

One new file, `HPC/Fold/Witnesses.lean` (258 lines); root `HPC.lean` updated as supplied by the
batch; the commission text kept as `COMMISSION-batch14.md`. Nothing else was touched.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings. Every theorem in it has axiom profile `[propext, Classical.choice, Quot.sound]`.

Everything commissioned is proved. `MixedGapUp_witnesses`, left open by batch 13, is
discharged: `mixedGapUp_witnesses` closes it. Two statements needed adjustment, both recorded
below and in the file; neither is a loss of content, and the commissioned form of the second is
kept verbatim, commented out, at the end of the file.

## 1. Census

Everything in `HPC/Fold/Witnesses.lean`, in file order. "Project" dependencies are results from
earlier batches; "mathlib" lists library lemmas used beyond the `omega`, `simp`, `norm_num`,
`ring` and `rcases`/`obtain` tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `exists_first_rise` | theorem | `IsLip` (b6), `hStarArm` (b9), `hStarArm_mem` (b9), `exists_least_index` (b6) | `Fin.ext`, `Fin.le_def`, `Fin.lt_def`, `abs_le` |
| `exists_first_drop` | theorem | `exists_first_rise`, `lStarArm` (b9), `IsLip` (b6) | `abs_neg` |
| `mixedGapUp_witnesses` | theorem | `MixedGapUp_witnesses` (b13), `exists_first_rise`, `exists_first_drop`, `armG`, `armT`, `armG_isLip`, `armT_isLip` (b6), `le_hStarArm` (b9), `lStarArm_le` (b12) | `Fin.ext`, `Fin.lt_def` |
| `exists_peak_link_between` | theorem | `mixedGapUp_witnesses`, `sync_up'` (b13), `IsCrookedSeqUp` (b13) | `norm_num` on a literal |
| `le_hStarArm_of_window` | theorem | `hStarArm` (b9) | `le_csSup`, `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove` |
| `hStarArm_eq_of_peak_on_T` | theorem | `le_hStarArm_of_window`, `lStarArm_le` (b12), `hStarArm_le_of_lStarArm` (b12), `armG`, `armT` (b6) | `Fin.ext`, `Fin.le_def` |

`le_hStarArm_of_window` is the one statement added beyond the commissioned list: the lower
bound for `hStarArm` that §4 needs, the mirror of `le_hStarArm_of_no_drop` (batch 10) with the
window hypothesis localized to the predecessors of a single index. Its proof is the same three
lines: the defining set is a subset of the (finite) range of the arm, hence bounded above, and
`le_csSup` applies.

## 2. The index translation of §2

Handled entirely by `show`, with no auxiliary transfer lemmas. `armG ρ i j = ρ ⟨i + j, _⟩` and
`armT ρ i j = ρ ⟨i − j, _⟩` are definitional, so each of the identities

* `armT ρ i ⟨0,_⟩ = ρ i`, `armG ρ i ⟨0,_⟩ = ρ i`,
* `armT ρ i dT = ρ ⟨i − dT, _⟩`, `armG ρ i rG = ρ ⟨i + rG, _⟩`,
* `armT ρ i ⟨i − w, _⟩ = ρ w` for `w ≤ i`, `armG ρ i ⟨w − i, _⟩ = ρ w` for `i ≤ w`,

is a `show` followed at worst by `congr 1` and `Fin.ext` with `omega` on the index arithmetic.
The truncated subtraction is harmless because `dT ≤ i` (it is an index of `Fin (i + 1)`) and
`i + rG < n` (`rG` is an index of `Fin (n − i)`), both recorded before use. The trichotomy on a
global index `w` strictly between the two exits is `lt_trichotomy w.val i.val`, the three cases
being the backward arm, the basepoint itself, and the forward arm, exactly as the commission
describes; `Fin.lt_def` turns the two ordering hypotheses into the `ℕ` inequalities that
`omega` needs.

No difficulty arose in the place the commission flagged: `le_lStarArm_of_hStarArm` is in fact
not needed at all. What the witnesses require is `lStarArm (armT) ≤ p − 2`, which comes from
`lStarArm_le` applied to `armG` (giving `lStarArm (armG) ≤ p`) together with the second gap
hypothesis; and `hStarArm (armG) ≥ p + 2`, which comes from `le_hStarArm` applied to `armT`
together with the first. Both are used in the direction the commission gives them, and the
single-arm lemma of batch 12 does supply what is needed.

## 3. `exists_first_drop`: obtained by reflection

By reflection, not mirrored. `lStarArm A p` is *by definition* `− hStarArm (−A) (−p)`, so the
hypothesis `lStarArm A p ≤ p − 2` is definitionally `−p + 2 ≤ hStarArm (−A) (−p)`, and
`exists_first_rise` applied to `−A` at `−p` returns the first index at which `−A` reaches
`−p + 2`, i.e. at which `A` reaches `p − 2`, with the window of `−A` about `−p` — which is the
window of `A` about `p`, reflected. Three `omega` calls convert. This is sound here precisely
because no crookedness hypothesis is involved, as the commission notes: only `IsLip`, which is
negation-symmetric, and the two demands, which are defined from one another by negation.

## 4. Correction 1: which form of the Synchronization Lemma applies (§3)

The two witnesses come out in the order *drop then rise*: `u = i − dT` carries `p − 2` and
`v = i + rG` carries `p + 2`, with `u < v`. So the interval is **ascending**, and `sync_up` —
whose hypotheses are `f u = p + 2`, `f v = p − 2` — does not apply to it; the ascending form
`sync_up'` does. The commission's §3 asks for `sync_up` and for its conclusion, `ρ j ∈ [p − 1,
p]` followed by `ρ k = p + 1`. What `sync_up'` gives is the same two values in the *opposite*
order: the first witness pinned at `p + 1`, the second only known to lie in `[p − 1, p]`. (This
is not an artefact of the formalization; it is the content of batch 13's correction, that the
upward form pins the witness at `p + 1` and that which of the two is pinned depends on the
direction of the interval.)

The commissioned conclusion is nonetheless obtained, and `exists_peak_link_between` is stated
and proved exactly as commissioned. One extra step does it: let `a` be the link at `p + 1`
produced by `sync_up'`, so `u < a < v` and `ρ a − ρ u = 3`. Crookedness applies again on
`[u, a]`, in its ascending case, and returns `r < r'` strictly inside with
`ρ r' ∈ [ρ u + 1, ρ u + 2] = [p − 1, p]`. Then `j := r'` and `k := a` satisfy the commissioned
conclusion, with `u < j < k < v`. The window clause is inherited unchanged from the witnesses.

## 5. Correction 2: the missing hypothesis in §4

`hStarArm_eq_of_peak_on_T`, as commissioned, assumes only that the `p + 1` link lies at a
global index `k ≤ i`. That is not enough, and the commission's own English proof says why: it
argues from "`k` is strictly between `u` and `v`" to "`b < dT`", i.e. to the link lying
**before the backward arm's first drop**. This is exactly the step the conclusion needs.
`hStarArm (armT) p` is a supremum over levels attained at indices *all of whose predecessors
stay at or above `p − 1`*; a link at `p + 1` sitting beyond the arm's first drop to `p − 2`
contributes nothing to that set, and from `k ≤ i` alone one cannot exclude it. Nothing else in
the hypotheses rules it out either: the residual configuration is empty in every instance
examined, so no argument from the two gap inequalities is available that does not amount to
proving `MixedGapUp` itself.

The hypothesis is therefore restored, in the form in which the caller actually has it:

    (hwin : ∀ w : Fin n, k ≤ w → w ≤ i → ρ i - 1 ≤ ρ w)

every global index between `k` and `i` stays at or above `p − 1`. This is an immediate
consequence of the window clause of `exists_peak_link_between`, since `[k, i] ⊆ (u, v)` when
`k` is the link that theorem produces, so the theorem is usable exactly where §4 intends it.
The commissioned statement is kept verbatim, commented out, at the end of the file, with a note
saying that it is not proved here; no claim is made about its truth.

With `hwin` in place the proof is the commissioned one: `lStarArm_le` on `armG` and the second
gap give `lStarArm (armT) ≤ p − 2`, hence `hStarArm (armT) ≤ p + 1` by
`hStarArm_le_of_lStarArm`; the index `b = i − k` of the backward arm has `armT b = p + 1` and
all its predecessors inside the window, so `le_hStarArm_of_window` gives
`hStarArm (armT) ≥ p + 1`; equality follows, and the first gap then forces
`hStarArm (armG) ≥ p + 3`.

## 6. Hypotheses that turned out unnecessary

Kept as commissioned, with a note in each docstring.

* `mixedGapUp_witnesses` uses no crookedness, as the commission predicted — `IsCrookedSeqUp` is
  part of the statement of `MixedGapUp_witnesses` and is simply not consumed.
* `hStarArm_eq_of_peak_on_T` uses neither `IsLip` nor `IsCrookedSeqUp`: only the two gap
  inequalities, the value at `k`, and the window.

`exists_peak_link_between` uses all of its hypotheses.

## 7. What is not here

As the commission directs: `MixedGapUp` itself, and the complementary branch of §4 — the
`p + 1` link on the forward arm, strictly before its first rise. `SmallDemandCase`,
`HighExitValley`, the assembly into `F2Prime`, Bing 1948 Theorems 4, 5, 6, the reduction in
Bing 1951, and the D8/D9 gap remain open as before.
