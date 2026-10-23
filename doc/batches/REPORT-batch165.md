Commission read: `doc/batches/COMMISSION-batch165.md` (batch 165 — Part E, Hagopian 1976 X: Theorem 1 — T7's arc `I₂` by a crossing argument; T8, T9, T11, Property 3; then T12–T17).

# Report, batch 165

**Status.**
* **A. T7 by the crossing route: proved.**
  * A.1 `hagopian76_no_hair`: proved (statement unchanged).
  * A.2 `preimage_pi_isContinuum`: proved (statement unchanged).
  * A.3 `rect_crossing`: proved (statement unchanged), by the first route of §1 step 3.
  * A.4 `hagopian76_T7`: proved; the unused hypothesis `hγ : IsEmbedding γ` is dropped.
* **B. Link control: proved.** `exists_isEps1_endCtl` (statement unchanged; `EndCtl` moved unchanged
  to `H76Thin.lean`), `hagopian76_link_control` (shape chosen, §1.B).
* **C. T8, T9 in full: proved in the shapes of §1.C**, with two parts open: `D` as a Jordan
  domain, and the sentence "the chain `L − {L₁, L₁₁}` follows `Cl B`".
* **D. T11: proved with one change** (`K` replaced by the whole of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`); for the
  single component `K`: open, obstruction stated (§1.D).
* **E. Property 3: open**, obstruction stated (§1.E).
* **F. T12–T17 and `hagopian76_theorem1`: open** (not reached; skeleton proposal in §5).
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76J` at the end of `HPC.lean`.
* No declaration uses `sorry`. The open statements are kept only inside the comment block at the end
  of `Hagopian76J.lean`.
* All 30 new theorems use only `propext`, `Classical.choice` and `Quot.sound` (§3). The regenerated
  `axioms.txt` has 1686 lines (1656 + 30), with `sorryAx` in none; every line shows the standard
  three axioms or a subset of them.

**Progress lines** (as written during the run):
* `STATUS: A.1 hagopian76_no_hair proved.`
* `STATUS: A.2 preimage_pi_isContinuum proved.`
* `STATUS: A.3 rect_crossing proved.`
* `STATUS: A.4 hagopian76_T7 proved.`
* `STATUS: B exists_isEps1_endCtl, hagopian76_link_control proved.`
* `STATUS: C hagopian76_T8 (property (D)), hagopian76_T9_full proved; D as a Jordan domain left open.`
* `STATUS: D hagopian76_T11 proved with K replaced by π⁻¹[D ∩ ⟨p₃, q₃⟩]; single K left open.`
* `STATUS: E Property 3 left open.`
* `STATUS: F T12–T17, theorem 1 left open.`

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76J.lean` | the skeleton: `rect_crossing`, `hagopian76_no_hair`, `preimage_pi_isContinuum`, `hagopian76_T7`, `exists_isEps1_endCtl`, `hagopian76_link_control`, `hagopian76_T8`, `hagopian76_T9_full`, `hagopian76_T11`; the open items as a comment block |
| `H76Crossing.lean` | `rect_split` (clopen split), `staple_isPreconnected`, `frame_arc` (Janiszewski), `arc_cut`, `rect_crossing_aux` |
| `H76NoHair.lean` | `isPreconnected_preimage_of_fibres` (closed maps with connected fibres), `no_hair_aux`, `isConnected_pi_fibre`, `preimage_pi_isContinuum_aux` |
| `H76T7.lean` | `isOpen_pi_image` (`π[U]` open for open `U ⊇ E`), `exists_height_below`, `hagopian76_T7_aux` |
| `H76Thin.lean` | `exists_pos_lt_on_compact`, `mem_layer_of_pi_eq_gamma`, `pi_thin_near_layer` (upper semicontinuity of the layers in collar coordinates), `EndCtl` (moved from the skeleton), `exists_isEps1_endCtl_aux`, `mem_piece_ceil`, `link_control_aux` |
| `H76T9Full.lean` | `strip_in_links` (link control + `π[St L]`), `closure_disjoint_E_of_above` (`Cl B ∩ E = ∅`), `T11_aux` |

**Edits to existing files.** All are allowed by the commission:
* `HPC.lean`: one import.
* `Axioms.lean` and `axioms.txt`: the new group "Hagopian 1976 X (batch 165)".
* `README.md`, `LEDGER.md` §6 and `OPEN.md`.
* Pointers replacing commented-out copies of statements proved here: `Hagopian76F.lean` (T11),
  `Hagopian76G.lean` (T7, T8, T9 in full, T11), `Hagopian76I.lean` (T7, T8, T9 in full, T11).
  The Property 3 comments are kept.
* `doc/notes/`: the ten stale copies `theorems-3-4-scheduling(1).md` … `(36).md` are deleted;
  `fugate-cor1-proof.md` is kept. Nothing referred to them (the references in the repository are to
  `doc/theorems-3-4-scheduling.md`, a different file).

**Housekeeping.** The commission is `doc/batches/COMMISSION-batch165.md`; the skeleton is kept
unchanged in `doc/batches/skeletons/Hagopian76J.lean`. Nothing is left at the root.

## 1. The items

### 1.A T7 — proved

**Step 1 (`hagopian76_no_hair`).** As in the commission. `E` is an extension of itself away from
`k⁻¹(0)` (map `k`) and away from `k⁻¹(1)` (map `σ ∘ k`, `layer (σ ∘ k) 0 = layer k 1`). Absorption
(`subset_extUnion_of_meets`) puts `Q` in `R(k⁻¹(0), E)` and in `R(k⁻¹(1), E)`; a point of `Q` lies in an
extension of each kind, and `ext_inter_subset` puts it in `E`. Checked: correct as stated.

**Step 2 (`preimage_pi_isContinuum`).** Mathlib's `IsPreconnected.preimage_of_isClosedMap` needs
an *injective* closed map, so it does not apply. Proved instead
`isPreconnected_preimage_of_fibres`: for continuous `f` from a compact space to a Hausdorff space,
a closed preconnected `C ⊆ range f` whose fibres are preconnected has preconnected preimage (split
the preimage by two closed sets; their images are closed, cover `C`, and are disjoint on `C` since
the fibres are connected). The fibres of `π` on `M` are layers (`isContinuum_layer_min`) or single
points (`elt_layerSetoid_of_notMem`). Checked: correct.

**Step 3 (`rect_crossing`).** First route of the commission, with this frame:
* `K = K_b ⊔ K_t` by `exists_clopen_split` (the component of the bottom edge misses the top edge,
  since a connected set meeting both, together with the bottom edge, would contradict `hno`).
* `A = K_b ∪ [a − 2, b + 2] × [−2, 0] ∪ [b + 1, b + 2] × [0, c]`, `B = K_t ∪ [a − 2, b + 2] × [c, c + 2]`.
  The frame is a `U` open to the left. `A ∩ B = [b + 1, b + 2] × {c}` (connected).
* `x = (a − 1/2, c/2)`, `y = (b + 1/2, c/2)`. `A` does not separate them (a staple over the top),
  `B` does not (a staple below). By `janiszewski_compact`, `A ∪ B` does not separate them; an arc
  joins them in the complement (`exists_tarc_of_isOpen_plane`).
* `arc_cut`: let `t₁` be the last time with abscissa `≤ a`, `t₂` the first later time with abscissa
  `≥ b`. After `t₁` the arc stays in `(a − 1, b + 1) × (0, c)` (it cannot get out of the `U` without
  passing abscissa `a` again). The piece `[t₁, t₂]` is the required arc.

Checked: no step fails. The route does not prove too much: `M_meets_above` (every window above
`π[E]` meets `π[M]`) is consistent; the arc passes between those points.

**Step 4 (`hagopian76_T7`).** `π[U]` is open for open `U ⊇ E`: `U` is saturated, since the class of a
point off `E` is a point and the class of a point of `E` is a layer `⊆ E` (`isOpen_pi_image`). The
compact set of points of `[a, b] × [0, 1]` with `F`-image outside `π[U]` misses the axis, so it lies
above some height `c` (`exists_height_below`). For `c' ≤ c`, `K = {z ∈ [a, b] × [0, c'] : F(z) ∈ π[M]}`
is closed and contains the bottom edge. If a connected `C ⊆ K` joined top and bottom, the preimage
of `F[Cl C]` would be a continuum of `M` (step 2) meeting `E` and missing the end sets (`0 < a`,
`b < 1`, `F` injective), hence inside `E` (step 1); but a point over the top edge would then be on
the axis. Step 3 gives the arc; `I₂ = F[I]`.

*Shape:* the statement of the skeleton, without `hγ` (unused).

### 1.B Link control — proved

* `pi_thin_near_layer`: for `[a, b] ⊆ [0, 1]` and `η > 0` there is `c > 0` such that a point `x` of `M`
  with `π(x) = F(z)`, `z ∈ [a, b] × [−c, c]`, is within `η` of a point `y ∈ E` with `k(y) ∈ [a, b]` and
  `|k(y) − z₁| < η`. (Compactness of `M × rectangle`: on the compact set of pairs `(x, z)` with
  `π(x) = F(z)` and no such `y`, the height `|z₂|` is positive.)
* `exists_isEps1_endCtl`: `ε₁ = min(ε₁', δ₁/4, δ₂/4)`.
* `hagopian76_link_control` (shape chosen): for an ordered refinement `L` of `chainG k ε₁` covering
  `E` and `0 < η ≤ ε₁`, a thin closed strip over `[3/22, 19/22]` lies in `π[St L]`, and every point of
  `M` over it lies in some link, never in `L₁`, `L₁₁`, and if it is in `Lⱼ` (Lean index `j`), its
  abscissa is in `((j − 1)/11 − η, (j + 2)/11 + η)`. `L₁`: a point of `G₁` is within `ε₁` of
  `k⁻¹[[0, 2/22]]`, and within `η ≤ ε₁` of `k⁻¹[[3/22, 1]]`, contradicting `EndCtl`. Abscissae:
  `IsEps1.sep` applied to the piece `⌈11 k(y)⌉` of `y`.

### 1.C T8, T9 in full — proved in the shapes chosen

* `hagopian76_T8`: property (D) — every point of `M ∩ Cl O` lies in one of `L₂, …, L₁₀` — for every
  `O ⊆ π⁻¹[R]`, `R` the thin closed strip of link control. Hagopian's `D` is the bounded domain of a
  Jordan curve inside `R`; that inclusion and the domain itself are **not** formalized (not needed
  for T9 and T11 in these shapes; Property 3 needs `D`'s side edges).
* `hagopian76_T9_full`: for every connected `B ⊆ M` over the open strip through a point of
  `L₂ ∪ … ∪ L₁₀`: `Cl B ∩ E = ∅` (`closure_disjoint_E_of_above`: `Cl B` lies over the closed strip,
  so misses the end sets; if it met `E` it would lie in `E` by no hair, whereas `B` is off the axis),
  and the conclusions of `hagopian76_T9` (batch 161) hold. A component of `M ∩ π⁻¹[D]` with `D` in
  the open strip is such a `B`.
* `ε₂`: `I₂` is a compact arc missing `π[M]`, so `hagopian76_eps2_pos` applies to `I₁ ∪ I₂`.
* **Open:** "the chain `L − {L₁, L₁₁}` follows `Cl B`" (needs `Cl B` to reach both verticals).

### 1.D T11 — proved with `K` replaced by `π⁻¹[D ∩ ⟨p₃, q₃⟩]`

`hagopian76_T11`: for every `D` in a thin open strip over `[3/22, 19/22]`, no connected
`S ⊆ π⁻¹[D] − π⁻¹[⟨p₃, q₃⟩]` contains a point of `M ∩ L₂` and one of `M ∩ L₁₀`. By link control
(with `η ≤ 1/22`) the first has abscissa `< 7/22 < 11/22`, the second `> 15/22`; the two open
half-strips `π⁻¹F[(3/22, 11/22) × (0, c)]`, `π⁻¹F[(11/22, 19/22) × (0, c)]` are disjoint and cover `S`.

**Open, the single component `K`.** If `I₂` crosses the vertical over `p₃` several times (it can: it
only has to miss `π[M]`), `D ∩ ⟨p₃, q₃⟩` has several components, and a channel of `D` above the lowest
crossing can run around `K` from one side to the other. Hagopian gives no argument; we have no
refutation (points of `M` in the channel need not lie in `L₂` or `L₁₀`). Whether T12–T13 need `K`
itself (connected, closure meeting `π⁻¹(p₃)` and `π⁻¹[I₂]`) or only a separating set is left to the
next batch: T12 picks `p ∈ K`, which any separating closed set provides.

### 1.E Property 3 — open

As in report 164 §1.6. New: the limit continuum of the hyperspace argument misses `E` by
`hagopian76_no_hair` (it lies over the closed strip, off the end sets, and is not inside `E` because
it reaches `I₂`'s side edges away from the axis). Still missing: that the limit is a crossing
continuum inside one layer of `F`, and the crossing property under the shift `g`. Both need `D` as a
domain (its side edges `⟨p₁, r⟩`, `⟨p₅, s⟩`).

### 1.F T12–T17, Theorem 1 — not reached

## 2. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 X (batch 165)":
1. T7 (p. 346): the printed route leaves the side of `h[E]` unargued; the crossing route replaces it
   (proved).
2. T8 (p. 346): true in substance; property (D) proved, the Jordan domain not built.
3. T9 (p. 346): the first sentence proved, with `Cl B ∩ E = ∅`; "follows `Cl B`" unargued, open.
4. `ε₁` (pp. 345–346): the printed families do not give property (D) by the argument printed;
   `EndCtl` added (harmless) and property (D) proved. Whether (D) fails for the printed `ε₁`: not
   decided.
5. T11 (p. 347): true for the whole of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` (proved); for the single component `K`
   unargued, open.
6. Property 3 (p. 347): not reached.
7. T12–T17: not reached.

Nothing is refuted; the count of defective proofs stays at fourteen.

## 3. Axioms

Every one of the 30 new theorems: `[propext, Classical.choice, Quot.sound]`. Per theorem:
`doc/batches/audits/axioms-batch165.txt`.

| file | theorems |
|---|---|
| `Hagopian76J.lean` | `rect_crossing`, `hagopian76_no_hair`, `preimage_pi_isContinuum`, `hagopian76_T7`, `exists_isEps1_endCtl`, `hagopian76_link_control`, `hagopian76_T8`, `hagopian76_T9_full`, `hagopian76_T11` |
| `H76Crossing.lean` | `rect_split`, `staple_isPreconnected`, `frame_arc`, `arc_cut`, `rect_crossing_aux` |
| `H76NoHair.lean` | `isPreconnected_preimage_of_fibres`, `no_hair_aux`, `isConnected_pi_fibre`, `preimage_pi_isContinuum_aux` |
| `H76T7.lean` | `isOpen_pi_image`, `exists_height_below`, `hagopian76_T7_aux` |
| `H76Thin.lean` | `exists_pos_lt_on_compact`, `mem_layer_of_pi_eq_gamma`, `pi_thin_near_layer`, `exists_isEps1_endCtl_aux`, `mem_piece_ceil`, `link_control_aux` |
| `H76T9Full.lean` | `strip_in_links`, `closure_disjoint_E_of_above`, `T11_aux` |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 165 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved |
| — (345) | the reparametrization | proved |
| T3 (345) | arc segments below `π[E]` | proved at interior points |
| T4, T5 (345–346) | `ε₁` (now with `EndCtl`); `L`; Property 1 | proved |
| T6 (346) | `I₁` below `⟨p₁, p₅⟩` | proved |
| T7 (346) | `I₂` above; the region between in `π[St L]` | **proved** (`hagopian76_T7`) |
| T8 (346) | `D` | **property (D) proved** (`hagopian76_T8`); the Jordan domain open |
| T9 (346) | components of `M ∩ π⁻¹[D]`; `ε₂` | **proved** (`hagopian76_T9_full`), except "follows `Cl B`" |
| T10 (346) | Property 2 | proved |
| T11 (347) | `K` separates | **proved for `π⁻¹[D ∩ ⟨p₃, q₃⟩]`** (`hagopian76_T11`); single `K` open |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6, Lemma 2; needs T11 (either form) |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6, Lemma 4; needs T12 |
| T14 (347) | Property 3 | "By Lemmas 2 and 3" proved; the least `v` and the crossing property open; needs `D` as a domain |
| T15 (347–348) | `e`, `J`, `xᵢ` | Property 3 |
| T16 (348) | Property 4 | Property 2 |
| T17 (348–349) | the induction | Property 2, Property 3, Lemmas 4–6 |

**Gateway.** `D` as a Jordan domain inside the strip (from `I₂`, the axis segment and the two
vertical segments up to `r`, `s`), then Property 3.

## 5. Skeleton proposal for what remains

In the set-up of `hagopian76_T6_placed` (accessible layer over `1/22`), with `c` the minimum of the
heights of `hagopian76_link_control`, `hagopian76_T8`, `hagopian76_T11`, and `I₂`, `r`, `s` from
`hagopian76_T7` at height `c' ≤ c`. The hypotheses `hI₂`, `hDL`, `hL2`, `hL10` of report 164 §5 are
now theorems; `hD` remains:

```
theorem hagopian76_D … : ∃ D : Set Pt, IsOpen D ∧ IsConnected D ∧
    D ⊆ F '' (Ioo (3/22) (19/22) ×ˢ Ioo 0 c') ∧
    frontier D = I₂ ∪ F '' (Icc (3/22) (19/22) ×ˢ {0}) ∪ F '' ({3/22} ×ˢ Icc 0 r.2') ∪ F '' ({19/22} ×ˢ Icc 0 s.2')
theorem hagopian76_property3 … (hF : IsExtensionAway E (layer k 0) F) (hd : IsMinimalAdmissible F d)
    (hdX : layer d 0 = layer k 0) : ∀ v (Q : Set M), IsPreconnected Q → toPt Q ⊆ π ⁻¹' D →
      (toPt (closure Q) meets π⁻¹ (left side)) → (… right side) → ¬ Q ⊆ layer d v
theorem hagopian76_T12 … : ∃ p ∈ K ∩ M, ∃ h₁ : M ≃ₜ M, (∀ v, dist v (h₁ v) < ε₂) ∧ p ∈ h₁ '' E ∧ …
theorem hagopian76_T13 … : ∃ (F : Set M) (d : F → unitInterval), IsMinimalAdmissible F d ∧ …
theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

In T12, `K` may be any closed subset of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` that separates (§1.D); if the
argument of T12–T13 uses that `K` is connected, the single-component claim of T11 has to be proved
first.

## 6. Build provenance

* **Fresh checkout:** yes — the run started from the delivered repository as checked out (no local
  build outputs of `HPC` present).
* **Mathlib:** the compiled Mathlib files at the pinned commit were already present in the build
  environment; they were neither downloaded with `lake exe cache get` nor rebuilt from source.
* **First full build:** about 75 minutes wall-clock in two parts: `lake build HPC.Hagopian.Hagopian76I`
  (the import closure of the batch-164 skeleton) took about 47 minutes, and the first
  `lake build HPC` afterwards (the remaining modules of the main build, plus the new files) about
  28 minutes.
