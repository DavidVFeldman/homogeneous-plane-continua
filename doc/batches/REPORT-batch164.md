Commission read: `doc/batches/COMMISSION-batch164.md` (batch 164 — Part E, Hagopian 1976 IX: Theorem 1, from the reparametrization to Property 3 (T7, T8, T9, T11, T14)).

# Report, batch 164

**Status.**
* **A. The reparametrization: proved** (`hagopian76_reparam`). Corollaries `hagopian76_T6_placed`
  and `hagopian76_I1` give T6 at Hagopian's abscissae `[3/22, 19/22]`.
* **B. T7: partly proved.**
  * Proved: observation B.1, "`π[M]` approaches `γ([a, b])` from above" (`M_meets_above`).
  * Proved: T7's accessible point `y` of `M − E` above `π[E]` (`exists_accessible_above`;
    collected with T6 in `hagopian76_T7_accessible`).
  * **Open, obstruction stated (§1.2):** the arc `A` on one side of `h[E]`, and the arc `I₂` with
    the region between it and `⟨p₁, p₅⟩` inside `π[St L]`.
* **C. T8: open.** It needs `I₂`.
* **D. T9 in full, `ε₂`, Property 2 at `ε₂`: partly proved.**
  * Proved: the positivity in the definition of `ε₂` (`hagopian76_eps2_pos`, check 5). It applies to
    `I₁` now, and to `I₁ ∪ I₂` once `I₂` exists. Property 2 is already stated for every `ε₂ > 0`
    (`hagopian76_property2`, batch 162), so it holds at this `ε₂`.
  * Open: the rest of T9, which needs `D`.
* **E. T11: open.** It needs `D` and control of the links of `L` in collar coordinates.
* **F. Property 3 in full: open.** It needs `D`. The two unargued steps are recorded in §2, check 7.
* **Refuted:** nothing.

Following §2 of the commission ("If B takes the whole batch, stop there and leave a plan for the
rest"), work stopped inside B. The plan for B (rest) through F is in §1.2 and §5.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76I` at the end of `HPC.lean`.
* No new declaration uses `sorry`. The skeleton's five open `True := sorry` statements are kept only
  inside a comment block of `Hagopian76I.lean`, each with its obstruction.
* All 33 new theorems use only `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76I.lean` | the skeleton: `hagopian76_reparam`, `hagopian76_T6_placed`, `hagopian76_I1`, `hagopian76_T7_accessible`, `hagopian76_eps2_pos`; the open items as a comment block |
| `H76Reparam.lean` | relabelling by a homeomorphism `θ` of `[0, 1]`: `IsMinimalAdmissible.homeo`, `layer_homeo`, `layer_homeo_apply`, `layerSetoid_homeo`, `setup_homeo`; the piecewise linear map `plr y z` (`plr_*`, `plrHomeo`, `plrI`); collar transport `IsCollar.plrTransport`, `image_plr_rect` |
| `H76Above.lean` | `π` off `E` (`eq_of_pi_eq_off`, `pi_mem_range_of_mem`, `pi_isOpen_image_off`); `M_meets_above` (B.1); `exists_notMem_piM` (`π[M]` has no interior off `π[E]`) |
| `H76AboveAcc.lean` | `IsCollar.disjoint_range_above`, `exists_accessible_above` (T7's `y`), `exists_pos_dist_preimage` (positivity in `ε₂`) |

**Edits to existing files.** All are allowed by the commission:
* `HPC.lean`: one import.
* `Axioms.lean` and `axioms.txt`: the new group "Hagopian 1976 IX (batch 164)".
* `README.md`, `LEDGER.md` §6 and `OPEN.md`.
* No commented-out copy in the earlier `Hagopian76*.lean` files is superseded by this batch: T7, T8,
  T11 and Property 3 are still open. So no pointers were added there.

**Housekeeping.**
* The commission is `doc/batches/COMMISSION-batch164.md`.
* The skeleton is kept unchanged in `doc/batches/skeletons/Hagopian76I.lean`.
* The root copy of `REPORT-batch163.md` was removed; it was byte-identical to
  `doc/batches/REPORT-batch163.md`.
* Nothing is left at the root.

## 1. The items

### 1.1 Item A: the reparametrization — proved

`hagopian76_reparam` takes interior parameters `y` and `z`. It produces `θ = plrI` (piecewise
linear, increasing, `θ 0 = 0`, `θ 1 = 1`, `θ y = z`) such that:
* `θ ∘ k` is minimal admissible;
* `θ ∘ k` has the same relation `S`, hence the same `π`;
* `γ ∘ θ⁻¹` is an embedding with `π x = γ(θ⁻¹ t)` on the layer over `t`, and `range(γ ∘ θ⁻¹) = range γ`;
* the layer of `θ ∘ k` over `θ t` is the layer of `k` over `t`;
* accessibility of the layer over `y` moves to the layer over `z`;
* every collar `F` of `γ` gives the collar `F ∘ (θ⁻¹ × id)` of `γ ∘ θ⁻¹`, with the same open
  rectangle image.

Homogeneity is not needed. The general relabelling (`setup_homeo`) works for any homeomorphism `θ`;
monotonicity is used only for the collar.

`hagopian76_T6_placed` uses `z = 1/22`. It gives a set-up `k'`, `γ'` with:
* the same `E` and `π`;
* the same layers, and in particular the same end sets;
* the accessible layer over `1/22`;
* a collar such that every `[a, b]` with `1/22 < a`, `b < 1` has a strip below `γ'([a, b])` missing
  `π[M]`.

`hagopian76_I1` is the instance `[3/22, 19/22]`, which is Hagopian's `⟨p₁, p₅⟩` with
`pᵢ = γ'((2i + 1)/22)`.

### 1.2 Item B: T7 — first part proved; the arc `I₂` open

**B.1, proved (`M_meets_above`).** Hypothesis: some strip `F([a, b] × [−c′, 0))` misses `π[M]`,
with `0 < a < b < 1`. Then every window `F((a, b) × (0, c))` meets `π[M]`. The proof follows the
commission's argument:
* Otherwise `π⁻¹` of `F((a, b) × (−c″, c″))` is open in `R²`.
* Its trace on `M` is a nonempty open set of `M` inside the proper subcontinuum `k⁻¹[[a, b]]`.
* This contradicts `interior_eq_empty_of_proper` (indecomposability).

**The accessible point, proved (`exists_accessible_above`).** Same hypothesis. Every window
`F((a, b) × (0, c))` contains `π(x)` for some `x ∈ M − E` accessible from `R² − M`. Steps:
1. `π[M]` contains no open set off `π[E]` (`exists_notMem_piM`). Such a set would pull back to an
   open subset of the plane inside `M`, and a small closed disc there would be a proper subcontinuum
   of `M` with interior. This gives a point `w` of the window outside `π[M]`.
2. B.1 gives a point `q` of the window in `π[M]`.
3. Take the straight segment from `w` to `q` in collar coordinates. It stays in the window by
   convexity. Its first point in `π[M]` (an infimum over a closed parameter set) ends an arc that
   meets `π[M]` only there.
4. `π` restricted to `R² − E` is an open embedding (`pi_isOpen_image_off`, `eq_of_pi_eq_off`). So
   the arc lifts to an arc in `R² − E` that meets `M` only at its end `x`.

`hagopian76_T7_accessible` collects the T6 collar, B.1 and this point for every `[a, b]` avoiding
the accessible parameter. *Shape:* the window replaces "`M ∩ L₆`". Any link of a chain following
`E` contains such a window over a subinterval of its parameters, because the links are open and
contain layers.

**Open: the arc `A` and `I₂`.** Hagopian: "There exists an arc `A` in `(St L) − M` to one side of
`h[E]` that meets `L₁` and `L₁₁` (Lemma 9 (proof))". Following commission note B.2, this is
`hagopian76_T6` for the type A′ continuum `h[E]`. The missing pieces:
1. **`h[E]` as a type A′ continuum with `y` in an interior layer.**
   * `h` comes from Property 1 (`hagopian76_property1`, proved), with `y ∈ h[E]`.
   * `h[E]` with the map `k ∘ h⁻¹` is minimal admissible (transport along `h`).
   * `y` has to be off the end layers of `h[E]`. This follows if `y` is far from `k⁻¹(0) ∪ k⁻¹(1)`
     and `h` is `ε₁`-close, which holds for `y` in the window over `[a, b] ⊆ (0, 1)` with `c` small.
   * Not yet written.
2. **Its quotient `π′`, `γ′` and collar.**
   * `exists_quotient_plane'_aux` applies to `h[E]`.
   * `exists_collar_vertical` applies to the accessible layer through `y`.
   * Then `hagopian76_T6` gives strips on one side of `γ′`.
   * Available, not assembled.
3. **The side.** The strip of `h[E]` lies on the side from which `y` is accessible. The accessing
   arc built in `exists_accessible_above` comes from a point of the window above `π[E]`, but the
   strip of `h[E]` in `π′`-coordinates is not a priori between `E` and `h[E]`. Pulling back by `π′`
   and pushing forward by `π` (injective off `E`) gives an arc missing `M`. To show that it lies
   above `π[E]` and close to `π[E]`, one would need the collar of `h[E]` controlled in terms of the
   collar of `E`. Nothing in the printed proof does this.
4. **"By choosing `y` sufficiently close to `E` and `h` sufficiently close to the identity, every
   point between `⟨p₁, p₅⟩` and a subarc of `π[A]` … belongs to `π[St L]`."**
   * Unargued (check 2).
   * The likely route is to make `π[St L]` contain a collar strip `F([3/22, 19/22] × [0, c₀])`. That
     is plausible because `St L ⊇ E` is open, `π` is closed, and there is uniform height
     (`IsCollar.uniform_height`).
   * Then one would show that `π[A]` lies in that strip (from step 3, with `c` small).
   * The required subarc irreducible between the two verticals then comes from the arc `π[A]`
     crossing the strip from `π[L₁]` to `π[L₁₁]`.
   * Not attempted.

**A shorter construction, for comparison (not formalized).** Later steps use only these properties
of `I₂`:
* it is compact and misses `π[M]` (for `ε₂`);
* it joins the verticals over `3/22` and `19/22` above `π[E]`;
* the bounded domain `D` it cuts off has `M ∩ Cl π⁻¹[D] ⊆ L₂ ∪ … ∪ L₁₀` (property (D) of T9).

Any arc in the collar strip `F([3/22, 19/22] × (0, c₀])` that misses `π[M]` and joins the two
verticals would do. Its existence is exactly the upper-side analogue of `no_M_below` for some
continuum near `E`. By B.1 it cannot be the horizontal at a fixed height, so a construction through
`h[E]` (Hagopian's) or through the accessible arcs of `exists_accessible_above` is needed. We did
not find a construction avoiding `h[E]`.

### 1.3 Item C: T8 — open

It needs `I₂`. Given `I₂`, `D` is the bounded domain of the Jordan curve
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` (`jordan_curve_theorem`, `TSCC` from `TArc` unions). Property
(D) follows from `D ⊆` the collar strip `⊆ π[St L]` (item B, step 4), as proposed in report 162.

### 1.4 Item D: T9 in full, `ε₂`, Property 2 — positivity proved; the rest open

`hagopian76_eps2_pos`: for a closed `I ⊆ R²` missing `π[M]`, there is `δ > 0` with
`δ ≤ dist(m, z)` for every `m ∈ M` and every `z` with `π z ∈ I`. This is
`ρ(M, π⁻¹[I]) > 0`, proved from compactness of `M` and `Disjoint.exists_cthickenings`.
* `I₁` (the side of the strip of `hagopian76_I1` at height `−c/2`) is compact and misses `π[M]`.
* Once `I₂` is available, `ε₂ = min(ε₁, δ)` is positive.

Property 2 is stated for every `ε₂ > 0` (`hagopian76_property2`), so it holds at this `ε₂`. The
first sentence of T9 is `hagopian76_T9` (batch 161) for any open `O` with property (D); applying it
needs `D`.

### 1.5 Item E: T11 — open

The obstruction of batch 161 stands. Once `D` lies in the collar strip, the sides of `K` (the
vertical cross-cut of `D` over `p₃`, abscissa `7/22`) are decided by the abscissa:
* `π[L₂ ∩ π⁻¹[D]]` would have to project into abscissae `< 7/22`;
* `π[L₁₀ ∩ π⁻¹[D]]` would have to project into abscissae `> 7/22`.

This requires the links `L₂` and `L₁₀` to be controlled in collar coordinates, which the printed
`ε₁` does not give. Proposed shape: §5.

### 1.6 Item F: Property 3 — open

It needs `D`. The step "By Lemmas 2 and 3" is proved (`hagopian76_property3_shift`, batch 161). Two
steps are unargued (check 7):
* the least `v`, i.e. closedness of the set of crossing parameters;
* the crossing property under the shift `g`.

Plan for the least `v`: crossing components have closures that are continua meeting both vertical
preimages. A limit of such closures, in the hyperspace of a compact set, is a continuum meeting both
verticals, contained in `Cl π⁻¹[D]` and in the limit layer `d⁻¹(v)` (upper semicontinuity). It
contains a crossing component of `F ∩ π⁻¹[D]` provided it misses `π⁻¹[I₂]`, which holds because
`ε₂ ≤ ρ(M, π⁻¹[I₂])`.

## 2. Ledger entries

`LEDGER.md` §6 has the subsection "Hagopian 1976 IX … (batch 164)", with checks 1–7.

| check | place | outcome |
|---|---|---|
| 1 | p. 345, "Since `M` is homogeneous, we can assume … that `π[k⁻¹(i/22)] = (i, 0)`" | **true; proved** as a reparametrization by a homeomorphism of `[0, 1]` (`hagopian76_reparam`); homogeneity is not needed for it |
| 2 | p. 346, T7: the accessible `y` above; "(Lemma 9 (proof))"; "By choosing `y` sufficiently close …" | `y`: **true; proved** (`exists_accessible_above`, via B.1). "(Lemma 9 (proof))": the citation is right in substance (T6 for `h[E]`), but the side of `h[E]` is not argued; **open**. "By choosing …": **unargued; open** |
| 3 | p. 346, T8: the simple closed curve and `D` | not reached (needs `I₂`) |
| 4 | p. 346, T9: "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`" | not reached (needs `D`) |
| 5 | p. 346: "Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`" | **positive, proved** for any closed `I` missing `π[M]` (`hagopian76_eps2_pos`); `I₁` qualifies (`hagopian76_I1`), and `I₂` misses `π[M]` by its definition |
| 6 | p. 347, T11: "Note that `K` separates …" | not reached; obstruction of batch 161 stands |
| 7 | p. 347, Property 3: "Let `v` be the first point …"; "By Lemmas 2 and 3 …"; "This contradicts the definition of `v`" | "By Lemmas 2 and 3": proved (batch 161). The other two: unargued, not reached |

No statement is refuted, and no defective proof is added. The count stays at fourteen.

## 3. Axioms

`doc/batches/audits/axioms-batch164.txt` lists `#print axioms` for the 33 new theorems: 5 in
`Hagopian76I.lean` and 28 supporting ones.
* Every line is `[propext, Classical.choice, Quot.sound]`.
* `axioms.txt` is regenerated with the group "Hagopian 1976 IX (batch 164)". It has 1656 lines, 33
  more than after batch 163, and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `hagopian76_reparam`, `hagopian76_T6_placed`, `hagopian76_I1`, `hagopian76_T7_accessible`, `hagopian76_eps2_pos` | standard three |
| `H76Reparam`: `IsMinimalAdmissible.homeo`, `layer_homeo`, `layer_homeo_apply`, `layerSetoid_homeo`, `setup_homeo`, `plr_of_le`, `plr_of_lt`, `plr_zero`, `plr_one`, `plr_self`, `continuous_plr`, `plr_le_iff`, `plr_plr`, `plr_strictMono`, `plr_mem_Icc`, `plr_mem_Ioo`, `plrI_coe`, `plrI_symm_coe`, `image_plr_rect`, `IsCollar.plrTransport` | standard three |
| `H76Above`: `eq_of_pi_eq_off`, `pi_mem_range_of_mem`, `pi_isOpen_image_off`, `M_meets_above`, `exists_notMem_piM` | standard three |
| `H76AboveAcc`: `IsCollar.disjoint_range_above`, `exists_accessible_above`, `exists_pos_dist_preimage` | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 164 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved |
| — (345) | the reparametrization `π[k⁻¹(i/22)] = (i, 0)` | **proved** (`hagopian76_reparam`) |
| T3 (345) | arc segments below `π[E]` | proved at interior points |
| T4, T5 (345–346) | `ε₁`; `L`; Property 1 | proved |
| T6 (346) | `I₁` below `⟨p₁, p₅⟩` | **proved at Hagopian's abscissae** (`hagopian76_I1`) |
| T7 (346) | `I₂` above; the region between in `π[St L]` | **`y` above proved** (`hagopian76_T7_accessible`); the arc `A` / `I₂` open (§1.2) |
| T8 (346) | `D` | needs T7 |
| T9 (346) | components of `M ∩ π⁻¹[D]`; `ε₂` | first sentence proved for `D` with (D); `ε₂ > 0` proved; rest needs T8 |
| T10 (346) | Property 2 | proved, for every `ε₂ > 0` |
| T11 (347) | `K` separates | open: needs T8 and link control |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6, Lemma 2; needs T11 |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6, Lemma 4; needs T12 |
| T14 (347) | Property 3 | "By Lemmas 2 and 3" proved; the least `v` and the crossing property open |
| T15 (347–348) | `e`, `J`, `xᵢ` | Property 3 |
| T16 (348) | Property 4 | Property 2 |
| T17 (348–349) | the induction | Property 2, Property 3, Lemmas 4–6 |

**Gateway.** The one remaining plane construction is T7's arc: §1.2, steps 1–4. Everything from T8
on waits on it.

## 5. Skeleton proposal for T12, T13, T15–T17 and `hagopian76_theorem1`, revised

All of these are stated in the reparametrized set-up of `hagopian76_T6_placed`: `k'`, `γ'`, collar
`F`, accessible layer over `1/22`, `tᵢ = (2i + 1)/22`. They also take, as hypotheses, the outputs
of T7/T8 in the following form (so the skeleton can be checked before T7 is proved):

```
(hI₂ : IsCompact I₂ ∧ Disjoint I₂ (π '' M) ∧ I₂ ⊆ F '' (Icc t₁ t₅ ×ˢ Ioc 0 c₀))
(hD : D = bounded domain of I₂ ∪ F '' (Icc t₁ t₅ ×ˢ {0}) ∪ verticals over t₁, t₅)
(hDL : ∀ x : M, (x : Pt) ∈ closure (π ⁻¹' D) → ∃ j, 1 ≤ j ∧ j ≤ 9 ∧ (x : Pt) ∈ L j)
(hL2 : π '' (L 1 ∩ π ⁻¹' D) ⊆ F '' (Ioo t₁ t₃ ×ˢ Ioo 0 c₀))   -- link control for T11
(hL10 : π '' (L 9 ∩ π ⁻¹' D) ⊆ F '' (Ioo t₃ t₅ ×ˢ Ioo 0 c₀))
```

* **T11** (`hagopian76_T11`), under `hD`, `hL2`, `hL10`: the component `K` of `π⁻¹[D ∩ vertical(t₃)]`
  meeting `π⁻¹(p₃)` and `π⁻¹[I₂]` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
  `π⁻¹[D]`. With the hypotheses above, this is the cross-cut theorem (`plane_split`) pulled back by
  `π`, which is a homeomorphism off `E`.
* **T12** (`hagopian76_T12`): `∃ p ∈ K ∩ M, ∃ h₁ : M ≃ₜ M, ε₂-close ∧ p ∈ h₁[E] ∧ …` and
  `f = h₁ ∘ h⁻¹`, from Lemma 2 (`hagopian76_lemma2`) and Lemma 6 (`hagopian76_lemma6`).
* **T13** (`hagopian76_T13`): `∃ F ⊆ M, type A′ with map d, F irreducible with respect to (1), (2)`,
  from Lemma 4 (`hagopian76_lemma4`) and Lemma 6.
* **T14** (`hagopian76_property3`): for every extension `F` of `E` away from `k⁻¹(0)` (map `d`), no
  component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[vertical(t₁)]` and `π⁻¹[vertical(t₅)]` lies in
  a layer of `d`. Proof route: §1.6.
* **T15** (`hagopian76_T15`): `e`, `J`, `xᵢ` with `d⁻¹[[0, e]] = E` (proved), from Property 3.
* **T16** (`hagopian76_property4`): from Property 2 at `ε₂`.
* **T17** (`hagopian76_T17`): the induction producing infinitely many disjoint crossing continua in
  `π⁻¹[D]`, each `ε₂`-close to a subcontinuum of `E`, contradicting compactness of `M` with
  `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])`.
* **Assembly** (`hagopian76_theorem1 : Hagopian76Thm1`): T0–T2 give `E`, `π`, `γ` and an accessible
  interior layer (`exists_accessible_typeA'_aux`). Then `hagopian76_T6_placed`, T7 → `I₂`, T8 → `D`,
  and T11–T17 give the contradiction.
