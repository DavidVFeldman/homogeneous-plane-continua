Commission read: `doc/batches/COMMISSION-batch180.md` ("Commission: batch 180 — Part E, Hagopian 1976 XXV: Theorem 1 — the set-up repaired; saturation; 3c; the step").

# Report, batch 180

## 0. Summary

* **§1, the set-up: done.**
  * The certificate is **proved** (`property4_lower_false_of_K_eq`). The argument of §1.1 has no
    hole.
  * `Thm1Setup` is restated in place with the fields of §1.2 (table in §1.2 below), plus one field
    found by the audit (the low vertical over `15/22`).
  * `hagopian76_T15_T17_cond4` exposes the composant data (`H76Cond4.lean`).
  * `exists_thm1Setup` and `hagopian76_theorem1_of_step` are restated in place, with
    `InnerComponentsCross` on `(3/22 + 8/n, 19/22 − 8/n)`.
  * The positive check `Thm1Setup.K_meets_crossing` is **proved**.
* **§2, saturation: partly done.**
  * §2.1 is **proved**: `tip_meets_end_layer`, its mirror form, and the continuum `Z`
    (`tip_end_layer_continuum`).
  * 2a is **proved**, with its mirror form (`tip_triod`, `tip_triod_mirror`).
  * 2b is **proved** when the third arm is nonempty (`tip_triod_on_tip_layer`).
  * 2c is **proved** (`degenerate_chunk_iii`).
  * 2d and 2e are **open** (§2.5). `InnerComponentsCross` stays a named hypothesis.
* **§3: open.** 3c, E0 and E1 are not formalized, also with `InnerComponentsCross` as a hypothesis.
* **§4: open.** The set-up now carries what E2.1–E2.6 use. The steps themselves are not formalized.
  Case 2 is answered informally in §4.5: the listed facts do not give "`Cᵢ₋₁` is above `d⁻¹[I]`".
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

**Left out (with reasons).**
* 2d (`no_end_layer_chunk`), 2e (`innerComponentsCross_hagopian`): §2.5.
* 3c (`block_components_cross`), E0/E1 (`property4_step_unless`): §3.
* E2.1 (`first_strand`), E2.4 (`property2_far_from_I`), the cap (`case1_cap`), E2.5
  (`case1_local_to_global`), Case 2 (`case2`), and the step (`hagopian76_property4_step`): §4.
* `hagopian76_theorem1_final`: it needs 2e and the step. The strongest conditional form is
  `hagopian76_theorem1_of_step`.

The shapes left `True` in the skeleton for these items are replaced by commented-out statements, or
by prose where no shape was settled, at the end of `Hagopian76Y.lean`.

STATUS lines, in order:
* `STATUS: §1.1 certificate proved (property4_lower_false_of_K_eq)`
* `STATUS: §1.2 Thm1Setup repaired; hagopian76_T15_T17_cond4 proved`
* `STATUS: §1.3 exists_thm1Setup, hagopian76_theorem1_of_step restated and proved; Thm1Setup.K_meets_crossing proved`
* `STATUS: §2.1 tip_meets_end_layer proved (and mirror form)`
* `STATUS: §2 2a proved (tip_triod, tip_triod_mirror)`
* `STATUS: §2 2b proved when the third arm is nonempty (tip_triod_on_tip_layer); empty third arm open (hand-over to 2d)`
* `STATUS: §2 2c proved (degenerate_chunk_iii)`
* `STATUS: §2 2d open (step 2 of commission 178 §3b not formalized; the points zⱼ; the edge case)`
* `STATUS: §2 2e open (needs 2d)`
* `STATUS: §3 3c, E0, E1 open (lemma3_half both ways along a crossing component)`
* `STATUS: §4 open (E2.1–E2.6 not formalized)`

The build:
* `lake build HPC` succeeds, with `import HPC.Hagopian.Hagopian76Y` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 2051 lines (2032 + 19 added, none removed), with `sorryAx` in no
  line.
* All 19 new theorems use only `propext`, `Classical.choice` and `Quot.sound`
  (`doc/batches/audits/axioms-batch180.txt`). So do the restated `exists_thm1Setup` and
  `hagopian76_theorem1_of_step`, which keep their lines in the batch-179 group.
* No declaration uses `sorry`. The word occurs only in comment blocks: the open shapes at the end of
  `Hagopian76Y.lean`, and the existing ones in `Hagopian76W.lean` and `Hagopian76X.lean`.

New files (all under `HPC/Hagopian/`):
* `Hagopian76Y.lean`: the skeleton (§1.1, §1.3 positive check, a table locating each item, the open
  items commented out);
* `H76Cond4.lean`: §1.2.2 (`p_on_crossing_piece_comp`, `sep_by_crossing_uncond_comp`,
  `hagopian76_T15_T17_cond4`);
* `H76Tip.lean`: §2.1, 2a, 2b, 2c.

Changed files:
* `H76Thm1Setup.lean`: `Thm1Setup` repaired, `exists_thm1Setup` and `hagopian76_theorem1_of_step`
  restated;
* `Hagopian76X.lean`: a one-line pointer (2a, 2b, 2c proved in `H76Tip.lean`);
* `HPC.lean`, `Axioms.lean`, `axioms.txt`, `README.md`, `LEDGER.md` §6, `OPEN.md`.

`H76Final179.lean` is unchanged: the composant version is a new theorem, as §1.2.2 asked.

The uploads are moved to `doc/batches/COMMISSION-batch180.md` and
`doc/batches/skeletons/Hagopian76Y.lean`.

## 1. The set-up

### 1.1 The certificate

`property4_lower_false_of_K_eq` (`Hagopian76Y.lean`) is proved with the shape of the skeleton:
for a `T12Data` package with `D.K = {D.p}`, a strictly increasing `x` on `[1, 2m]` with
`d⁻¹[[0, x₂]] = E` and `x₂ₘ = 1`, and `2 ≤ i ≤ m`, Property 4 fails for `[x₂ᵢ₋₃, x₂ᵢ₋₂]`.

The proof follows steps 1–5 of §1.1. **No hole.**
* `yₙ = p`.
* `A := d⁻¹[[0, x₂ᵢ₋₂]]` contains `d⁻¹[J]` and lies in `D.G`, so it misses `p` and `f(p)`, and a
  connected subset of `O − A` is one of `O − d⁻¹[J]`.
* `A` is an extension of `E` away from `k⁻¹(0)`: `piece_map` with `lsc_of_minimalAdmissible`, and
  `x₂ᵢ₋₂ ≥ x₂ > x₁ ≥ 0`.
* `A ≠ D.G`, since a point of `d⁻¹(1)` would have parameter `≤ x₂ᵢ₋₂ < x₂ₘ = 1`.
* `D.irr` gives `A = D.G`, a contradiction.

The hypothesis `x₁ = 0` of the blocks is not needed; strict monotonicity gives `x₂ > 0`.

### 1.2 The repaired `Thm1Setup`

The new fields, each with the step that uses it:

| Field | Content | Used by |
| --- | --- | --- |
| `hn : 40 ≤ n` | `n = 40` | §2.1 step 2 (`3/22 > 4/n`; `tip_meets_end_layer`); §2.2 (`n ≥ 34`) |
| `cs`, `hcs`, `hcs1`, `hstrip` | the strip `F[[3/22, 19/22] × [−cs, 0)]` misses `π[M]` (`hagopian76_I1`) | the definition of `I₁` |
| `I₁`, `hI₁` | `I₁ = F[[3/22, 19/22] × {−cs/2}]` | `ε₂` (§1.2.3) |
| `hε₂`, `hε₂₁`, `hε₂I` | `0 < ε₂ ≤ ε₁`, `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` | E2.2, E2.4 (Property 2 at the printed `ε₂`), E2.5.2 |
| `hε₂V` | `5/n + ε₂ < 15/22 − 3/22` | E2.2 (`N` stays `ε₂` away from the vertical over `15/22`) |
| `hε₃θ : ε₃ ≤ θ/2` | `h`, `h₁` are `θ/4`-homeomorphisms (`Thm1Setup.h_small_θ`, `h₁_small_θ`) | S0 for the strands of `p`, `f(p)`; `strand_essential` in E2.1 |
| `hpos` | the position clause of `eps3_positions_middle` at `ε₃` | 3c, E2.5.2 (`f(yᵢ₋₁)` over `(3/8, 5/8)`) |
| `hK` | `D.K = {p} ∪ K₀`, `K₀ = {m ∈ M : π(m) ∈ F[{1/2} × (0, w₂)]}` | the base (`yₙ = p`); E2.1 (`yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`, `Thm1Setup.K_meets_crossing`) |
| `hcomp` | `x₀ ∈ E`, `k(x₀) = 1/2`, `p = h(x₀)`, `h(x₀)`, `h₁(x₀)` off the composant of `x₀` | E2.1 (`L ∩ F = ∅` by 4.A, `strand_misses_of_composant`) |
| `w₃`, `hw₃`, `hFw₃`, `hseg₃`, `hsub₃` | the low vertical `V` over `15/22`, up to its first point on `I₂` (`hagopian76_K0`) | E2.3 (`Q ⊆ V`), E2.5 (`A`, `B` contain `V`) |

The batch-179 fields stay. `hε₂₃ : ε₃ < ε₂` and `hP2 : Property2At k ε₂ ε₃` now refer to the printed
`ε₂`.

The construction in `exists_thm1Setup`:
* `n = 40` in `strand_fine_translate`;
* `cs = min c′ 1` from `hagopian76_I1`;
* `ε₂ = min (min ε₁ δ) (1/4)`, with `δ` from `hagopian76_eps2_pos` for the closed set `I₁ ∪ I₂`
  (`I₂` is compact, `isCompact_I₂_aux`). The `1/4` gives `hε₂V`; Property 2 holds at every
  `ε₂ > 0`, as the commission says;
* `ε₃ = min ε₃′ (θ/2)`, with `ε₃′` from `eps3_positions_middle` at this `ε₂`. Property 2 and the
  position clause pass to the smaller `ε₃` (`Property2At.mono`);
* the package from `hagopian76_T15_T17_cond4` with `K₀` as above.

**Field audit** (§1.2.6, `doc/notes/hagopian76-cases.md`, E2.1–E2.6):
* **E2.1** uses `hcomp`, `hε₃θ`, `hK` and the strand constants. Nothing is missing for the
  statement. The existence of the shortest extension `L` is a theorem still to prove.
* **E2.2** uses `hε₂V`, `hε₂I` and S6 (`hS`).
* **E2.3** uses the vertical over `15/22`, which was missing. It is added (`w₃`, …).
* **E2.4** uses `hP2` at the printed `ε₂`.
* **E2.5** uses `V`, `hpos`, `hε₂I` and `Y = π⁻¹[Fr D]` (`pi_preimage_frontier_D_aux`, a lemma rather
  than a field).
  * The bound of E2.5.2 is not added: "`[yᵢ₋₁, f(yᵢ₋₁)]` stays in `π⁻¹[D]` once `ε₃` is less than
    the distance from `π⁻¹[[3/8, 5/8] × [0, c₁/2]]` to `Y`".
  * Reason: that distance is `0`, because the region reaches the bottom edge, which lies over `E`
    and so in `Y`. Nothing in the choice of constants keeps `yᵢ₋₁ ∈ K` away from the bottom edge.
  * A correct form must bound `yᵢ₋₁` away from `π⁻¹[Fr D]`, or choose the segment differently.
    This is recorded as a point to check (§6, check 4).
* **E2.6** uses `hP2` and `hε₂₃`.

### 1.3 Restatements, positive check, non-vacuity

* `exists_thm1Setup`: the same statement, with the repaired `Thm1Setup` and `InnerComponentsCross`
  on `(3/22 + 8/n, 19/22 − 8/n)`. With `n = 40` this is `(3/22 + 1/5, 19/22 − 1/5)`, which
  contains `t₀ = 1/2` and `(3/8, 5/8)`.
* `hagopian76_theorem1_of_step`: the same statement, with `hICC` on `(3/22 + 8/n, 19/22 − 8/n)`.
* **`Thm1Setup.K_meets_crossing`** (proved), with the skeleton's shape.
  * Take a crossing piece `C ⊆ M` that misses `K`. Then `C` misses
    `π⁻¹F[{1/2} × (0, w₂)]`, because a point of `C` there is in `K₀`.
  * Its closure meets both open side segments.
  * The cross-cut lemma `hagopian76_K0_crosscut` then gives a contradiction.

**Non-vacuity notes.** These are informal. Theorem 1 says that no set-up exists at all, so no
hypothesis of `hagopian76_theorem1_of_step` can be shown consistent in Lean. What follows explains
why the set-up does not refute each hypothesis by a short argument of the kind in §1.1.
* **`hICC` (saturation).** It is a statement about the components of `F ∩ O` through points over
  the middle. The configurations that would contradict it are the ones that 2a–2c turn into triods
  or into violations of 3a. No field of `Thm1Setup` forces a non-crossing component. 3a uses only
  `D.irr` and `D.sep` for the pair `(p, f(p))`, and gives `d⁻¹(1) ⊄ O`, which is consistent with
  saturation.
* **`hstep` (the step).** The §1.1 refutation used `yₙ = p`: Property 4 for `J` made `d⁻¹[J]`
  separate `p` from `f(p)`, and so made the proper extension `d⁻¹[[0, x₂ᵢ₋₂]]` separate them,
  against `D.irr`.
  * With `K = {p} ∪ K₀`, the point `yᵢ₋₁` can be a point of `K₀` on a strand other than the strand
    of `p`.
  * Separating `yᵢ₋₁` from `f(yᵢ₋₁)` says nothing about `(p, f(p))`. `D.irr` constrains only
    separations of `p` from `f(p)`.
  * So the certificate argument does not apply. The batch-179 step hypothesis for `K = {p}` could
    only be met if Property 4 failed for the top block, which `hagopian76_property4_top_final`
    excludes once saturation holds. That obstruction is gone.

## 2. Saturation

### 2.1 `tip_meets_end_layer` (proved)

The shape is in `H76Tip.lean`.
* `G` (Hagopian's `F`) is type A′ with `d⁻¹(0) = k⁻¹(0)`, and `h` is a `θ/4`-homeomorphism.
* `b` is a parameter, and `K⁻ = G ∩ h[k⁻¹[[0, b]]]`.
* If `τ` is the least parameter of `K⁻`, attained at a point over `D`, then some `h(e′)` with
  `k(e′) = τ` lies in `d⁻¹(1)`.

Of "`K⁻ ⊆ O`", only the tip point over `D` is used, in step 1. The point `y = h(e)` need not be over
the inner middle. The proof is §2.1, steps 1–4, arranged as a contradiction:
* compactness of `E` gives `δ₁ > 0` with `h[k⁻¹[[τ − δ₁, τ + δ₁]]]` missing `d⁻¹(1)`;
* `δ = min(δ₁, 3/22 − 4/n)/2`;
* `Q_δ` misses `k⁻¹(0)` by S0: a point of `Q_δ` in `k⁻¹(0)` lies over `F(0, 0)`, so its parameter
  is `< 2/n`, while every parameter of `Q_δ` is `> 3/22 − 2/n − δ ≥ 2/n` (this uses `n ≥ 40`);
* no hair gives `Q_δ ⊆ G`;
* the point at parameter `τ − δ/2` contradicts the minimality of `τ`.

**Mirror form** (`tip_meets_end_layer_mirror`), for `K⁺ = G ∩ h[k⁻¹[[b, 1]]]` with greatest
parameter `σ`. It also uses `σ < 19/22 + 2/n` (S0, `tip_param_high`), so that `σ + δ/2 ≤ 1`.

**Consequences** (`tip_end_layer_continuum`, `tip_Z_continuum`): `Λ₁ = d⁻¹(1) ∩ h[E]` is a
continuum meeting the tip layer (by hereditary unicoherence), and `Z = Λ₁ ∪ h[k⁻¹(τ)]` is a
continuum.

### 2.2 2a (proved, with the mirror form)

`tip_triod`, in the set-up of §2.1, with:
* (i) `∃ e₁, k(e₁) ≤ b, h(e₁) ∈ G − d⁻¹(1), k(e₁) ≠ τ`;
* (iii) `d⁻¹(1) ⊄ h[E]`.

The conclusion is `False`.

The triod is `T = (d⁻¹(1) ∪ h[k⁻¹[[0, τ]]]) ∪ K⁻` over `Z`. The commission's `δ` is taken equal to
`τ` (`τ > 0` by S0); any `0 < δ ≤ τ` works the same way. The arms are:
* `K⁻ − Z`;
* `h[k⁻¹([0, τ))]`, which misses `G` by the minimality of `τ`;
* `d⁻¹(1) − h[E]`.

The six separations:
* `Cl(K⁻ − Z) ⊆ K⁻ ⊆ G ∩ h[E]`;
* `Cl(arm 2) ⊆ h[k⁻¹[[0, τ]]]`, and `K⁻ − Z` misses it: a point of `K⁻` with parameter `≤ τ` has
  parameter exactly `τ`, so it lies in `Z`;
* `Cl(arm 3) ⊆ d⁻¹(1) ⊆ G`;
* `(K⁻ − Z) ∩ d⁻¹(1) ⊆ Λ₁ ⊆ Z`.

`T` is a continuum: `d⁻¹(1)` meets `h[k⁻¹[[0, τ]]]` at the tip (§2.1), and `K⁻` meets it at the
tip point. Atriodicity is `hagopian75_lemma1`.

The **mirror form** `tip_triod_mirror` uses `T = d⁻¹(1) ∪ K⁺ ∪ h[k⁻¹[[σ, 1]]]`, with arms `K⁺ − Z`,
`h[k⁻¹((σ, 1])]` and `d⁻¹(1) − h[E]`.

As the commission says, the relation between `τ₁` and `k(e)` plays no role.

### 2.3 2b (proved when the third arm is nonempty)

In `tip_triod_on_tip_layer`, 2b is the case `b = τ + δ` of 2a:
* if `K⁻ = G ∩ h[k⁻¹[[0, τ]]]` lies in the tip layer, the least parameter of
  `G ∩ h[k⁻¹[[0, τ + δ]]]` is still `τ`;
* a point `h(e₁) ∈ G − d⁻¹(1)` with `τ < k(e₁) ≤ τ + δ` (the third arm) gives (i).

So 2b needs no new triod.

**Open:** the hand-over to 2d when the third arm is empty for every `δ`.

### 2.4 2c (proved)

`degenerate_chunk_iii` uses a `T12Data` package `D`, with `y = h(e)` over `D` and `k(e)` in the
core `[3/22 + 2/n, 19/22 − 2/n]`. If `Λ₁ ⊆ h[k⁻¹(t)]` for some `t` in the open core, then
`d⁻¹(1) ⊄ h[E]`.

Proof:
* Otherwise `d⁻¹(1) = Λ₁` lies in the closure of the strand of `y` (`strand_crossing`), hence over
  `Cl D`.
* A point of `d⁻¹(1)` over `Fr D` is excluded in each case:
  * over `I₂`: T7;
  * over the bottom edge: it would be in `E` (`mem_E_of_axis`), but `E = d⁻¹[[0, s]]` with `s < 1`
    (`ext_layers`; `F ≠ E` by `hagopian76_property4_base`);
  * over a side segment: by S0, since `t` is more than `2/n` from `3/22` and `19/22`.
* So `d⁻¹(1) ⊆ O`, against 3a (`T12Data.end_layer_not_subset`).

**Point to note.** The commission's "`Λ₁ ⊆ O`" is not automatic for a translated layer near the
bottom edge. It holds here because `d⁻¹(1)` misses `E`.

### 2.5 2d and 2e (open)

What is missing, in order:
1. **Step 2 of commission 178 §3b**: "`W` is non-crossing, so one half `K⁻` or `K⁺` lies in `O`".
   Report 178 found it sound, but it was never formalized, and 2e starts from it.
2. **The points `zⱼ`** (2d.3–2d.4):
   * `zⱼ → c` in `F ∩ U` with `d(zⱼ) < 1`, by the void interior of `d⁻¹(1)` in `F`;
   * for large `j`, the component `Wⱼ` of `zⱼ` is non-crossing (`crossing_components_finite`, and
     the closedness of crossing components in `O`).
3. **(iii) at `zⱼ`** (2d.5, with the margin of §2.2):
   * choose `c` near `y` as in §2.2;
   * `c ∈ hⱼ[E]` gives `c ∈ Sⱼ`, by the strand lemma at `zⱼ`;
   * so `c ∉ hⱼ[E]`.

   `tip_meets_end_layer` applies verbatim at `zⱼ`, as the commission says.
4. **The edge case**: `zⱼ` on its own tip layer with 2b's third arm empty. The commission suggests
   choosing `zⱼ` off the tip layers. That needs: a nonempty relatively open subset of `F` is not
   covered by the single translated layer that is the tip layer of each of its points. This is
   plausible from the void interior of the layers of `hⱼ[E]`, but the tip layer depends on `j`.

With 1–4, the proved lemmas `tip_triod`, `tip_triod_on_tip_layer` and `degenerate_chunk_iii` close
the cases. `InnerComponentsCross` stays a named hypothesis of `hagopian76_theorem1_of_step`, stated
for 2e on `(3/22 + 8/n, 19/22 − 8/n)` in the open block of `Hagopian76Y.lean`.

## 3. 3c, E0, E1 (open)

These are not formalized, even with `InnerComponentsCross` as a hypothesis.

**3c.** The component in `F ∩ O` of a point of `d⁻¹[B] ∩ O` over the middle must stay in
`d⁻¹[B]`. That needs `lemma3_half` in both directions along a crossing component. It also needs the
fact that gap layers and block end layers miss the points over the middle; this uses the irreducible
intervals and the clause "every member of `I` inside a block".

**E0, E1.** Their shapes are commission 179 §6.1 in `lowFrame`, and they need 3c.

The proposed shape of 3c, with `InnerComponentsCross` as a hypothesis, is commented out in
`Hagopian76Y.lean`.

## 4. The induction step (open)

1. **E2.1.**
   * The choice of `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁` is now available: `Thm1Setup.K_meets_crossing`, once `Cᵢ₋₁`
     is known to be a crossing piece in `M` (4.B-type argument, as in `p_on_crossing_piece`).
   * `L ∩ F = ∅` is available from `hcomp` and `strand_misses_of_composant`.
   * The existence of the shortest extension `L` is open.
2. **E2.4.** Open: `H ⊆ L` must be identified as an extension of a piece of `h[E]`, so that
   `Property2At` applies.
3. **The cap.** Open. It needs:
   * the two-point intersection `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∩ Q`;
   * the reading of "between" in (β).
4. **E2.5.** Open. It needs:
   * a second frame in `O_L`;
   * the bound of E2.5.2 (§1.2, field audit).
5. **Case 2.**
   * **The question.** Do the minimality of `L`, `L ∩ F = ∅`, Property 2 and the order give
     "`Cᵢ₋₁` is above `d⁻¹[I]`"?
   * **Answer (informal): not from these alone.** `L ∩ F = ∅` makes `Cᵢ₋₁` disjoint from every
     `I`-strand, so it is comparable with each of them, but the order says nothing about which side.
   * **The blocking configuration.**
     * `L` leaves `O` through the left side segment, above the left end of an `I`-strand `W` that
       lies below `Cᵢ`.
     * Outside `Cl D`, `L` goes around and re-enters through the left side segment below the left
       end of `W`. Its first strand `Cᵢ₋₁` is then below `W`.
     * `L` cannot leave through `I₂` (T7: `I₂ ∩ π[M] = ∅`), nor through the bottom edge (that is
       over `E ⊆ F`).
     * The minimality of `L` (it contains no strand other than `Cᵢ` before `Cᵢ₋₁`) is not violated.
   * Excluding this needs a bound on `L` outside `Cl D`, presumably Property 2 applied to the part
     of `L` outside `D` together with the `ε₂`-distance to `π⁻¹[I₁]`. The text does not argue this.

The step is the named `Prop` `Property4Step` (unchanged). Its statement for the repaired set-up
(`hagopian76_property4_step`) is commented out in `Hagopian76Y.lean`.

## 5. Named `Prop`s and structures

* `Thm1Setup` (structure, repaired in place).
* `InnerComponentsCross` (named `Prop`, batch 179; the open input 2e).
* `Property4Step` (named `Prop`, batch 176; the open input §4).
* No new named `Prop` was needed. The open shapes are the commented-out statements at the end of
  `Hagopian76Y.lean`.

## 6. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXV (batch 180)":
1. **p. 347, `K`** ("Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` …"): correct. The batch-179
   `K = {p}` was a **project error**; the certificate is `property4_lower_false_of_K_eq`. The
   induction uses two properties of `K`:
   * `p ∈ K` (the base);
   * `K` meets every strand (E2.1; `Thm1Setup.K_meets_crossing`).
2. **p. 346, `ε₂`** ("Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`"): correct as
   printed, and recorded in the set-up.
   * `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` keeps the continua of E2.2 and E2.4 away from `I₂` and from below the
     axis.
   * `ε₂ ≤ ε₁` enters through Property 2.
   * Neither use is formalized yet.
3. **The end layer of `F`** (not in the text): the gap is partly closed.
   * `tip_meets_end_layer` answers point (ii) of report 179 §1.2: `Z` is a continuum.
   * The margin of point (i) is handled by `n = 40` and the interval `(3/22 + 8/n, 19/22 − 8/n)`.
4. **pp. 348–349, Cases 1–2**: open. Two points to check:
   * the bound of E2.5.2;
   * "`Cᵢ₋₁` is above `d⁻¹[I]`" in Case 2 (§4.5).

## 7. Axioms

Every theorem below depends on `[propext, Classical.choice, Quot.sound]` exactly. The audit is
`doc/batches/audits/axioms-batch180.txt`.

| Theorem | File |
| --- | --- |
| `property4_lower_false_of_K_eq` | `Hagopian76Y.lean` |
| `Thm1Setup.K_meets_crossing` | `Hagopian76Y.lean` |
| `hagopian76_T15_T17_cond4` | `H76Cond4.lean` |
| `p_on_crossing_piece_comp` | `H76Cond4.lean` |
| `sep_by_crossing_uncond_comp` | `H76Cond4.lean` |
| `Thm1Setup.h_small_θ`, `Thm1Setup.h₁_small_θ` | `H76Thm1Setup.lean` |
| `isCompact_I₂_aux` | `H76Thm1Setup.lean` |
| `tip_meets_end_layer`, `tip_meets_end_layer_mirror` | `H76Tip.lean` |
| `tip_end_layer_continuum`, `tip_Z_continuum` | `H76Tip.lean` |
| `tip_param_low`, `tip_param_high`, `isContinuum_of_minimalAdmissible` | `H76Tip.lean` |
| `tip_triod`, `tip_triod_mirror`, `tip_triod_on_tip_layer` | `H76Tip.lean` |
| `degenerate_chunk_iii` | `H76Tip.lean` |
| `exists_thm1Setup`, `hagopian76_theorem1_of_step` (restated; batch-179 lines) | `H76Thm1Setup.lean` |

## 8. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_step                      [proved]
   ├─ exists_thm1Setup                              [proved]
   │  └─ hagopian76_T15_T17_cond4                   [proved]
   │     ├─ sep_by_crossing_uncond_comp             [proved]
   │     │  └─ p_on_crossing_piece_comp (4.B)       [proved]
   │     ├─ hagopian76_x2n_eq_one_unif, exists_blocks_uncond   [proved]
   │     └─ hagopian76_T15_T17_cond_fix             [proved]
   ├─ hICC: InnerComponentsCross on (3/22+8/n, 19/22−8/n)      [OPEN, 2e]
   │  ├─ step 2 of commission 178 §3b               [open]
   │  ├─ 2a  tip_triod, tip_triod_mirror            [proved]
   │  │  └─ tip_meets_end_layer (§2.1), mirror      [proved]
   │  ├─ 2b  tip_triod_on_tip_layer                 [proved, third arm nonempty]
   │  ├─ 2c  degenerate_chunk_iii                   [proved]
   │  └─ 2d  no_end_layer_chunk                     [open]
   └─ hstep: Property4Step for every block sequence            [OPEN, §4]
      ├─ 3c block_components_cross                  [open; needs 2e or hICC]
      ├─ E0, E1 property4_step_unless               [open; needs 3c]
      ├─ E2.1 first_strand                          [open; K_meets_crossing, hcomp available]
      ├─ E2.4 property2_far_from_I                  [open]
      ├─ cap, E2.5                                  [open; V over 15/22 in the set-up]
      └─ Case 2                                     [open; §4.5]
```

## 9. Skeleton proposal for what remains

```lean
/-- Step 2 of commission 178 §3b: a non-crossing component through a point over the inner middle
has one half inside `O`. -/
theorem noncrossing_half_in_O (S : Thm1Setup M) (y : M) (hy : …over (3/22 + 8/n, 19/22 − 8/n)…)
    (hW : ¬ IsCrossingPiece … (connectedComponentIn (toPt S.D.G ∩ O) y)) :
    ∃ (h : M ≃ₜ M) (e : E), (∀ v, dist (h v) v < S.θ / 4) ∧ h e = y ∧
      ((∀ e', k e' ≤ k e → h e' ∈ S.D.G → π (h e') ∈ S.F '' S.D') ∨
       (∀ e', k e ≤ k e' → h e' ∈ S.D.G → π (h e') ∈ S.F '' S.D')) := by sorry

/-- 2d.3–2d.5: the points `zⱼ` near `c`, with non-crossing components and (iii). -/
theorem chunk_points (S : Thm1Setup M) … : ∃ z : M, d z < 1 ∧ ¬ crossing (W z) ∧
    ¬ layer S.D.d 1 ⊆ hz '' E ∧ … := by sorry

/-- 2d, the edge case: points of `F ∩ U − d⁻¹(1)` off their own tip layer. -/
theorem chunk_points_off_tip (S : Thm1Setup M) … := by sorry

/-- 3c with saturation as a hypothesis. -/
theorem block_components_cross (S : Thm1Setup M) (hICC : InnerComponentsCross …) … := by sorry

/-- E2.1: the shortest extension `L` (chain intersection). -/
theorem exists_shortest_extension (S : Thm1Setup M) … := by sorry

/-- Case 2: a bound on `L` outside `Cl D` (the configuration of report 180 §4.5 excluded). -/
theorem case2_above (S : Thm1Setup M) … := by sorry
```

## 10. Delivery

* `doc/batches/batch180-MANIFEST.txt`: `git diff --name-status` against the run's initial commit
  (`68d1386`), plus the files the report names that this run did not change.
* `doc/batches/batch180-files.tar.gz`: every file of the manifest, at its final content.
