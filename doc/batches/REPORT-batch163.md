Commission read: `doc/batches/COMMISSION-batch163.md` (batch 163 — Part E, Hagopian 1976 VIII: the collar geometry (Lemma 9's argument made general; Lemma 9; T3, T6)).

# Report, batch 163

**Status.**
* **Proved:** items A–D.
  * A. `exists_collar_adapted`, in the skeleton's shape, unchanged.
  * B. `no_M_below`, both sides in one statement. *Shape change:* the unused hypothesis
    `hab : a ≤ b` is dropped (for `a > b` the strip is empty).
  * C. **Lemma 9** (`hagopian76_lemma9`), in the skeleton's shape, unchanged.
  * D. **T6** (`hagopian76_T6`). *Shape change:* the unused premise `a ≤ b →` is dropped.
* **Also proved, added:** **T3** at the interior points (`hagopian76_T3`): one collar in which, for
  every `0 < t < 1`, the vertical below `γ t` misses `π[M]` near its foot.
* **Open** (`OPEN.md`, batch-163 section; nothing is commented out in `Hagopian76H.lean`): T7
  (optional, not attempted); the reparametrization of item D placing Hagopian's `⟨p₁, p₅⟩` away from
  the accessible layer; T3 at the two end points of `π[E]`.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76H` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76H.lean` | the skeleton: `exists_collar_adapted`, `no_M_below`, `hagopian76_lemma9`, `hagopian76_T6` proved; `hagopian76_T3` added |
| `H76Adapt.lean` | `tarc_hseg`, `tarc_vseg` (segments are arcs), `IsCollar.flip`, `IsCollar.exists_continuous` (a collar agreeing with a continuous map of the plane on the closed rectangle), `exists_drop_arc` (the drop arc `β₁`) |
| `H76Rect.lean` | the two boundary arcs `rectC₁`, `rectC₂` of `[0, 1] × [−1, 0]` between `(y, 0)` and `(x₀, −1)`: frontier, arcs, intersection, points on the top edge |
| `H76Glue.lean` | `glueMap`: two square maps glued along a vertical; continuity, injectivity, image |
| `H76AdaptHalf.lean` | `halfcollar_side`, `exists_lower_halfcollar` (the new lower half-collar) |
| `H76AdaptMain.lean` | `collar_adapted_core` (upper half of the old collar + new lower half), `exists_collar_adapted_aux` (item A, with the flip if `β` arrives from above) |
| `H76NoBelow.lean` | `mem_layer_of_pi_eq`, `disjoint_toPt_layerSet`, `layer_close_of_pi_close` (upper semicontinuity through `π`), `IsCollar.isOpen_image`, `IsCollar.uniform_height`, `exists_closedBall_disjoint`, `chain3_follows` (the three-link chain) |
| `H76NoBelowCore.lean` | `no_M_below_core` (the contradiction, §1.2) |
| `H76NoBelowMain.lean` | `no_M_below_left` (the sequence argument), `IsMinimalAdmissible.symm'`, `layer_symm`, `layerSetoid_symm`, `IsCollar.reverse`, `no_M_below_aux` (both sides), `exists_collar_vertical` (the set-up of Lemma 9 from `hacc`) |

`no_M_below_core` is one long proof and is elaborated with `set_option maxHeartbeats 1600000`.

**Edits to existing files** (all allowed by the commission):
* `HPC.lean`: one import added.
* `Axioms.lean`, `axioms.txt`: the new group "Hagopian 1976 VIII (batch 163)".
* `README.md`, `LEDGER.md` §6, `OPEN.md`.
* `Hagopian76C.lean`, `Hagopian76D.lean`, `Hagopian76E.lean`, `Hagopian76F.lean`,
  `Hagopian76G.lean`: the commented-out copies of `hagopian76_lemma9` (with their `OPEN` notes) are
  replaced by the one-line pointer
  ``-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.``
  (in `Hagopian76C.lean`, whose copy had the straightened conclusion `DecompAccessible`, the pointer
  says that the collar form `DecompAccessibleC` is proved). In `Hagopian76G.lean` the commented-out
  T3/T6 proposal is replaced by ``-- `hagopian76_T6` (T3, T6): proved in batch 163, `Hagopian76H.lean`.``

**Housekeeping.**
* The commission is `doc/batches/COMMISSION-batch163.md`, and the uploaded skeleton is kept unchanged
  in `doc/batches/skeletons/Hagopian76H.lean`.
* The root copy of `REPORT-batch162.md` was removed; it is byte-identical to
  `doc/batches/REPORT-batch162.md`.
* The scheduling note `theorems-3-4-scheduling(10).md` was moved to `doc/notes/`.

Nothing is left at the root.

## 1. The items

### 1.1 Item A: `exists_collar_adapted` — proved

Route: commission §2.A, made concrete. The collar of `γ` is not rebuilt; its lower half is replaced.
1. Start from any collar (`exists_collar_aux`) and make it continuous on the plane by clamping
   (`IsCollar.exists_continuous`).
2. Near its end `γ y`, the arc `β` lies in the open collar rectangle `F((0, 1) × (−1, 1))`. Pulled
   back by `F⁻¹`, its end piece is a path `g` ending at `(y, 0)` that stays off the axis (since
   `β ∩ range γ = {γ y}`), so by connectedness it stays on one side. If it is above, flip the collar
   (`IsCollar.flip`).
3. In collar coordinates, cut the end piece at its last exit from a small box under `(y, 0)` and
   continue it by a vertical segment to the bottom side. This gives an arc `β₁` from `(y, 0)` to a point
   `(x₀, −1)`, crossing the open lower rectangle `Q = (0, 1) × (−1, 0)` (`exists_drop_arc`), whose
   part near `(y, 0)` lies in `g[[t₁, 1]]`.
4. `β₁` cuts `Q` into two Jordan domains `R₁`, `R₂` (`plane_split`, with the two boundary arcs of
   `H76Rect.lean`). Two-sided Schoenflies (`plane_schoenflies₂`) in each, with the bottom side on the
   top edge of `Q` and the left side on `β₁`, gives square maps `fL`, `fR`; glued along the vertical
   (`glueMap`), they form a new lower half-collar `H` of `[0, 1]²` onto `Cl Q`, the identity on the
   top edge, whose vertical over `y` runs along `β₁` (`exists_lower_halfcollar`).
5. The new collar is `F` on the upper half and `F ∘ H` (reflected) on the lower half
   (`collar_adapted_core`). Its vertical below `γ y` is, near the foot, in `F[g[[t₁, 1]]] ⊆ β`.

### 1.2 Item B: `no_M_below` — proved (both sides)

The route of commission §1 is followed, with three changes (recorded in `LEDGER.md`, checks 1–2).

**Set-up** (`no_M_below_core`, for a point `u` of an interior layer `U = k⁻¹(a′)`, `0 < a′ < y`).
Abscissae `α = a′/3`, `β₁ = 2a′/3`, `ζ₃ = y + (1 − y)/3`, `ζ₂ = y + 2(1 − y)/3`. `ε` is chosen so that
the `ε`-thickenings of the following pairs are disjoint: `k⁻¹[[a′, 1]]` and `k⁻¹[[0, β₁]]` (Hagopian's
`ρ(D, H₁)`); `k⁻¹[[ζ₃, 1]]` and `C = k⁻¹[[0, y]]` (`ρ(C, H₃)`); `k⁻¹[[a′, ζ₃]]` and
`k⁻¹(0) ∪ k⁻¹(1)` (`ρ(H₂, k⁻¹(0) ∪ k⁻¹(1))`); `k⁻¹(1)` and `C`. The chain is
`Gᵢ = π⁻¹[Rᵢ]`:
* `R₁ = F((0, β₁) × (−c₁, c₁)) ∪ B(γ 0, r₀)`;
* `R₂ = F((α, ζ₂) × (−c′, c′))`;
* `R₃ = F((ζ₃, 1) × (−c₁, c₁)) ∪ B(γ 1, r₂)`.

The discs about the ends make the end links open and contain the end layers; their radii are chosen
so that they miss the far parts of the collar. `chain3_follows` proves that `G` is a plane chain that
follows `E`. The heights are chosen so that, through `π`, every point of `Cl R₁` is near `k⁻¹[[0, β₁]]`
and every point of `Cl O` is near `C` (`layer_close_of_pi_close`, `IsCollar.uniform_height`).
`lemma8_caps_sep` gives the free refinement `L` with `L₂ = C′ ∩ G₂`.

**The contradiction.** Let `z ∈ M` be near `u`, with `π(z) = F(x, s)`, `x` near `a′`, `s < 0` small.
1. `z ∉ E`, since `π[E]` is the axis and `F` is injective. `z ∈ L₂`, since `z` is near `u ∈ E ⊆ C′`
   and `π(z) ∈ R₂`.
2. Lemma 2 at `u` (`hagopian76_lemma2`) gives an `ε`-homeomorphism `h` with `h(u) = z`.
3. `h[D] ∩ C = ∅` (in place of Hagopian's "`G₂ ∩ E` and `G₂ ∩ h[E]` are disjoint"; `LEDGER.md`,
   check 1): a point `h(e) ∈ C` would have `k(e) < ζ₃`, and the continuum
   `h[k⁻¹[[a′, k(e)]]]` meets `E`, misses both end sets, and contains `h(u) = z ∉ E`, against
   `subset_of_meets_avoids`.
4. `h[D]` misses the vertical over `y` (which misses `π[M]`) and `Cl G₁` (by `ρ(D, H₁)`).
5. Boundary bumping (`exists_continuum_bump_compact`) in `h[D]`, which leaves `π⁻¹[Cl O]` at
   `h[k⁻¹(1)]` (its points are near `k⁻¹(1)`, far from `C`, while points over `Cl O` are near `C`):
   the component `Q` of `h[D] ∩ π⁻¹[Cl O]` through `z` has a point `w` with `π(w) ∉ O`.
6. `π(w)` is on the bottom side of `O` at abscissa `≥ β₁`: the top side is `π[C]`, the right side is
   the vertical, the left side and the bottom side left of `β₁` are in `R₁`. So `w ∉ St L`.
7. `Q` is connected, contains `z ∈ St L` and `w ∉ St L`, so it meets `M ∩ Bd(St L)`
   (`meets_frontier_of_isPreconnected`). Freeness puts that point in `Cl G₁ ∪ Cl G₃`; `Q` misses
   `Cl G₁` (step 4), and `π⁻¹[Cl O]` misses `Cl G₃` (abscissae `≤ y` against `≥ ζ₃`).

**From the core to `no_M_below`.** If no strip below `γ([a, b])` works (`[a, b]` left of `y`), there
are `zₙ ∈ M` with `π(zₙ) = F(xₙ, sₙ)`, `xₙ ∈ [a, b]`, `sₙ ↑ 0`. A subsequence converges, `zₙ → u`,
`xₙ → a′`; `π(u) = F(a′, 0) = γ(a′)`, so `u ∈ k⁻¹(a′)` (`mem_layer_of_pi_eq`); the core at `u` is
contradicted for `n` large (`no_M_below_left`). This replaces "compactness over `a′`". The right side
is the left side for the reversed data `k ↦ 1 − k`, `γ ↦ γ ∘ (1 − ·)`, `F(x, s) ↦ F(1 − x, s)`
(`no_M_below_aux`). The skeleton's `F` is not assumed continuous off the closed rectangle; it is
replaced by a continuous collar agreeing with it there (`IsCollar.exists_continuous`).

**Check of the steps** (commission: "If one fails, say which and why").
* Set-up, step 1, step 2, steps 4–7: hold as stated.
* Step 3: the printed sentence is not proved; what the argument uses (`h[D] ∩ C = ∅`) is proved
  directly. One extra smallness condition on `ε` (the pair `k⁻¹[[a′, ζ₃]]`, end sets) is used.
* "Compactness over `a′`": replaced by the sequence argument above (same conclusion).
* The statement `no_M_below` is not stronger than the argument gives; it is proved as stated
  (without `a ≤ b`).

### 1.3 Item C: Lemma 9 — proved

`exists_collar_vertical`: from `hacc` take the arc `I` with `I ∩ M = {p}`, `p ∈ k⁻¹(y)`. `π` is
injective on `I` (points of `I − {p}` are off `M`, so their `S`-classes are singletons), so `π[I]` is
an arc ending at `γ y` (`tarc_image_of_injOn`), and `π[I] ∩ range γ = {γ y}`. Item A gives a collar
whose vertical below `γ y` lies in `π[I]`; it misses `π[M]` except at the foot, since a point of
`I` over `π[M]` is `p`. Then `no_M_below` on `[u − d, u + d]` (`d` small, `y` outside) gives the
vertical below `γ u`. Both sides `σ = −1`. The hypothesis "Assume `U` and `Y` are not decomposably
accessible" is not used (`LEDGER.md`, check 4).

### 1.4 Item D: T6 — proved; T3 (interior points) — proved, added

`hagopian76_T6`: one collar `F` (from `exists_collar_vertical`) and, for every `[a, b] ⊆ (0, 1)`
avoiding `y`, a strip `F([a, b] × [−c, 0))` disjoint from `π[M]` (`no_M_below`). Hagopian's `I₁` is
the bottom side `F([a, b] × {−c/2})`, its end points are on the verticals over `a` and `b`, and no
point of `π[M]` lies between `I₁` and `γ([a, b])`.

**Recorded change** (commission: "Choose the parametrization so that the accessible layer is outside
it … Record the change"). The statement is for every interval avoiding `y`, so no parametrization is
chosen inside T6. Applying it at Hagopian's `⟨p₁, p₅⟩` (abscissae `3/22 … 19/22`) needs
`y ∉ [3/22, 19/22]`. The reparametrization of `k` by a homeomorphism of `[0, 1]` (with the transport
of `IsMinimalAdmissible`, `γ` and the collar) is not formalized; it is listed in `OPEN.md`.

`hagopian76_T3`: for the same collar and every `0 < t < 1`, the vertical below `γ t` misses `π[M]`
near its foot (the vertical of item A at `t = y`; `no_M_below` on `[t, t]` otherwise). The two end
points `γ 0`, `γ 1` are not covered.

### 1.5 T7 — not attempted (optional)

Open as in batch 162 (`OPEN.md`). The core argument (`no_M_below_core`) is for the lower side of the
collar and for `E`; T7 needs it on the upper side, for `h[E]`, from an accessible point of `M ∩ L₆`
above `π[E]`.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 VIII … (batch 163)", checks 1–5 (the five places of commission §3):

| check | place | outcome |
|---|---|---|
| 1 | p. 344/345, "Since `M` is atriodic and `h(u)` is not in `E`, the sets `G₂ ∩ E` and `G₂ ∩ h[E]` are disjoint." | unargued; **not used**: its consequence `h[D] ∩ C = ∅` is proved by `subset_of_meets_avoids` (one extra smallness condition on `ε`); the sentence itself not decided |
| 2 | p. 345, "Since `L` is free relative to `M` and `π[C ∪ I] ∩ πh[Cl G₃] = ∅`, this is impossible [13, Theorem 28, p. 156]." | **replaced, proved**: collar rectangle `O`, boundary bumping, freeness; no Theorem 28. Printed route: the cited theorem is proved, its application (disc links with interlaced points) not supplied by the printed `L`; not decided |
| 3 | p. 344, the chain `G` with "`π[Gᵢ]` is an open disk" and "`π[Gᵢ] ∩ π[Gᵢ₊₁]` is an open disk" | **true** for collar rectangles; the disk property is not needed (end links: rectangle ∪ small disc) |
| 4 | p. 345, "Assume `U` and `Y` are not decomposably accessible from a side of `E`." | **not used**; Lemma 9 holds in the stronger form (direct, via `no_M_below`) |
| 5 | p. 345, T3, "… each point of `π[E]` is an end point of an arc segment in `R² − π[M]` below `π[E]` (Lemma 9)"; p. 346, T6, "It follows from the proof of Lemma 9 …" | **true; proved** from `no_M_below` (`hagopian76_T3` interior points, `hagopian76_T6`); reparametrization for `⟨p₁, p₅⟩` and the end points of T3 open |

No statement is refuted, and no defective proof is added. The count stays at fourteen.

## 3. Axioms

`doc/batches/audits/axioms-batch163.txt` lists `#print axioms` for the 51 new theorems: the 5
statements of `Hagopian76H.lean` and 46 supporting ones. Every line is
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` appears in none. `axioms.txt` is regenerated
with the group "Hagopian 1976 VIII (batch 163)" (1623 lines, 51 more than after batch 162), and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `exists_collar_adapted`, `no_M_below`, `hagopian76_lemma9`, `hagopian76_T6`, `hagopian76_T3` | standard three |
| `H76Adapt`: `tarc_hseg`, `tarc_vseg`, `IsCollar.flip`, `IsCollar.exists_continuous`, `exists_drop_arc` | standard three |
| `H76Rect`: `rect_frontier`, `rect_tarc₁`, `rect_tarc₂`, `rect_inter`, `rectC₁_axis`, `rectC₂_axis` | standard three |
| `H76Glue`: `clampI_val`, `clampI_zero`, `clampI_coe`, `clampI_inj`, `glue_memL`, `glue_memR`, `glueMap_L`, `glueMap_R`, `glueMap_vert`, `glueMap_continuous`, `glueMap_top`, `glueMap_injOn`, `glueMap_mapsTo`, `glueMap_snd`, `glueMap_image_sub`, `glueMap_image_sup` | standard three |
| `H76AdaptHalf`: `halfcollar_side`, `exists_lower_halfcollar` | standard three |
| `H76AdaptMain`: `collar_adapted_core`, `exists_collar_adapted_aux` | standard three |
| `H76NoBelow`: `mem_layer_of_pi_eq`, `disjoint_toPt_layerSet`, `layer_close_of_pi_close`, `IsCollar.isOpen_image`, `IsCollar.uniform_height`, `exists_closedBall_disjoint`, `chain3_follows` | standard three |
| `H76NoBelowCore`: `no_M_below_core` | standard three |
| `H76NoBelowMain`: `no_M_below_left`, `IsMinimalAdmissible.symm'`, `layer_symm`, `layerSetoid_symm`, `IsCollar.reverse`, `no_M_below_aux`, `exists_collar_vertical` | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 163 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157, 158) |
| T3 (345) | each point of `π[E]` is an end of an arc segment below `π[E]` | **proved at interior points** (`hagopian76_T3`, from Lemma 9's argument); end points not covered (not used) |
| T4 (345–346) | `ε₁` | proved (`hagopian76_eps1`) |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; `L`; Property 1 | proved |
| T6 (346) | `I₁` below `⟨p₁, p₅⟩` | **proved** (`hagopian76_T6`) for intervals avoiding the accessible layer; the reparametrization placing `⟨p₁, p₅⟩` there is open |
| T7 (346) | `I₂` above; the region between in `π[St L]` | open (unargued sentence; the core argument on the upper side, for `h[E]`) |
| T8 (346) | the bounded domain `D` | needs T7 (Jordan curve theorem available) |
| T9 (346) | components of `M ∩ π⁻¹[D]` | first sentence proved for `D` with (D); rest needs T8 |
| T10 (346) | `ε₂`, `ε₃`; Property 2 | proved (`hagopian76_property2`) |
| T11 (347) | `K` separates in `π⁻¹[D]` | open: needs T8 and the sides of `K` |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6 (proved), Lemma 2; needs T11 |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6 (proved), Lemma 4; needs T12 |
| T14 (347) | Property 3 | "By Lemmas 2 and 3" proved; the least `v` and the crossing property open |
| T15 (347–348) | `e`, `J`, `xᵢ` | `d⁻¹[[0, e]] = E` proved; Property 3 |
| T16 (348) | Property 4 | Property 2 |
| T17 (348–349) | the induction | Property 2 (twice), Property 3, Lemma 6 (proved), Lemma 4, Lemma 5 |

Lemmas 1–9 of §2 are now all proved (Lemma 9 in collar form, without its hypothesis "not decomposably
accessible").

**Gateways now.**
1. T7: the core argument on the upper side of the collar, for `h[E]` (the proof of
   `no_M_below_core` is the template), and the region between `I₂` and `⟨p₁, p₅⟩` in `π[St L]`.
   Then T8 (`D`), and from `D`: T9 (rest), T11, Property 3, T12–T17.
2. The reparametrization of `k` (with `γ` and the collar) so that the accessible layer lies outside
   `[3/22, 19/22]`; it is needed to place T6 at Hagopian's abscissae.
