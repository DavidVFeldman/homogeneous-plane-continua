Commission read: `doc/batches/COMMISSION-batch179.md` ("Commission: batch 179 — Part E, Hagopian 1976 XXIV: Theorem 1 — the end layer of `F`; `SepByCrossing` without conditions; uniform heights; the assembly; the step").

# Report, batch 179

## 0. Summary

* **§1, the interval: done.** `InnerComponentsCross` is used on the inner middle
  `(3/22 + 3/n, 19/22 − 3/n)`, with `t₀ = 1/2` (`Thm1Setup`, `hagopian76_theorem1_of_step`).
* **§2, saturation: open.** `InnerComponentsCross` stays a named hypothesis. The finiteness tool of
  2d.4 is **proved** (`crossing_components_finite`). The route was checked informally; two points need
  care (§1.2).
* **§3: proved, with 2e as the only remaining hypothesis.**
  * 4.B is proved (`p_on_crossing_piece`), with `Disjoint I₂ (π '' M)` from T7 as the commission said.
  * `SepByCrossing`, `x₂ₙ = 1` and Property 4 for the top block are proved from
    `InnerComponentsCross` alone (`sep_by_crossing_uncond`, `hagopian76_x2n_eq_one_final`,
    `hagopian76_property4_top_final`).
  * The blocks are proved with only `x₂ₙ = 1` as a hypothesis (`exists_blocks_uncond`). `e`,
    finiteness and nondegeneracy are discharged.
  * 3c is open.
* **§4, uniform heights: proved.** Every height listed in §4 comes from `follows_crossing`,
  `pi_thin_near_layer` or `hagopian76_link_control`, and none of these mentions `G`. So each height
  can be chosen before `G` (the `…_unif` theorems). No gap in the order of the constants.
* **§5, the assembly: proved, with `InnerComponentsCross` as a second hypothesis.**
  * `Thm1Setup` is written.
  * `exists_thm1Setup` assembles T1–T13 from scratch: a homogeneous indecomposable plane continuum
    with a decomposable subcontinuum gives a set-up in which `InnerComponentsCross` and the step give
    `False`.
  * `hagopian76_theorem1_of_step`: `(∀ S, InnerComponentsCross …) → (∀ S x m, blocks → Property4Step
    S.D x m) → Hagopian76Thm1`.
* **§6, the step: open.** E0 and E1 need 3c. The rest has not been started.
* **§0.1 is confirmed.** Property 3 as printed gives nondegeneracy
  (`crossingIntervals_nondegenerate`).
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

STATUS lines, in order:
* `STATUS: §1 done (inner middle (3/22 + 3/n, 19/22 − 3/n), t₀ = 1/2)`
* `STATUS: §2d.4 proved (crossing_components_finite)`
* `STATUS: §2a, 2b, 2d, 2e open (not formalized; two points in report §1.2)`
* `STATUS: §3.2 4.B proved (p_on_crossing_piece)`
* `STATUS: §3.3 proved from InnerComponentsCross (sep_by_crossing_uncond, hagopian76_x2n_eq_one_final, hagopian76_property4_top_final)`
* `STATUS: §3.4 proved (exists_blocks_uncond)`
* `STATUS: §3.5 proved (hagopian76_T15_T17_cond3)`
* `STATUS: §3.1 3c open (needs 2e)`
* `STATUS: §4 proved (the …_unif theorems)`
* `STATUS: §5 proved with InnerComponentsCross as a hypothesis (Thm1Setup, exists_thm1Setup, hagopian76_theorem1_of_step)`
* `STATUS: §6 open (E0, E1 need 3c; E2.x not started)`

The build:
* `lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76X` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 2032 lines (2000 + 32 added, none removed), with `sorryAx` in no line.
* All 32 new theorems use only `propext`, `Classical.choice` and `Quot.sound`
  (`doc/batches/audits/axioms-batch179.txt`).
* No declaration uses `sorry`. The word occurs only in comment blocks: the open shapes at the end of
  `Hagopian76X.lean`, and the existing ones in `Hagopian76W.lean`.

New files (all under `HPC/Hagopian/`):
* `Hagopian76X.lean`: the skeleton, with a table locating each item, and the open items commented
  out;
* `H76Nondeg.lean`: §0.1 and §2d.4, abstract forms;
* `H76Uniform.lean`, `H76Uniform2.lean`, `H76Uniform3.lean`: §4;
* `H76PieceB.lean`: 4.B;
* `H76Final179.lean`: §3.3–3.5;
* `H76Thm1Setup.lean`: §5.

Earlier files edited, as allowed:
* `Hagopian76W.lean` (batch 178): three commented-out open shapes are replaced by one-line pointers.
  They are 4.B `p_on_crossing_piece`, nondegeneracy `crossingIntervals_nondegenerate`, and §7
  `hagopian76_theorem1_of_step`.
* No other earlier file changed. The old statements of §4 are kept. The uniform versions imply them:
  specialize at `G`.

The uploads are in `doc/batches/COMMISSION-batch179.md` and
`doc/batches/skeletons/Hagopian76X.lean`. Nothing is left at the root.

## 1. The items in order

### 1.1 §1: the interval

The narrow interval `(3/22 + 3/n, 19/22 − 3/n)` is used, as the commission asks. With `n = 15`
(the value fixed in `exists_thm1Setup`) it is `(0.336…, 0.663…)`, which contains `t₀ = 1/2`.
`Thm1Setup` fixes the low vertical over `1/2` (fields `hFw`, `hseg`, `hsub`).

`sep_by_crossing_uncond` and `hagopian76_T15_T17_cond3` accept any interval `(lo, hi) ∋ t₀`. The
narrowing is applied only in `exists_thm1Setup` and `hagopian76_theorem1_of_step`.

### 1.2 §2: saturation

**2d.4 (finitely many crossing components): proved.**
* `crossingComponents_finite_of` is the abstract form: if `I` is finite and nondegenerate, the
  crossing components form a finite set. Each component has an irreducible interval in `I`
  (`exists_irreducibleInterval`). Two components with the same nondegenerate interval coincide
  (`IsCrossingComponent.eq_of_irreducible`, the argument of `crossingIntervals_disjoint`).
* `crossing_components_finite` is the form for Hagopian's set-up, with a uniform height. Note that
  nondegeneracy (§0.1) is needed: two components with the same degenerate interval `[u, u]` would not
  be separated by the argument.

**2a, 2b, 2d (other steps), 2e: open, not formalized.** I checked the route informally. Two points
need care:
1. **2d.5, "`hⱼ[E]` meets `O` over the inner middle only inside `Sⱼ`".**
   * A point `hⱼ(e′)` over abscissa `s` has `|k(e′) − s| < 2/n` (S0).
   * The strand `Sⱼ` contains the translated layers `hⱼ[k⁻¹(t)]` only for
     `t ∈ (3/22 + 2/n, 19/22 − 2/n)` (`strand_lemma`).
   * So for the conclusion `c ∈ Sⱼ` from `c ∈ hⱼ[E]`, the point `c` should lie over
     `(3/22 + 4/n, 19/22 − 4/n)`, not only over the inner middle. This holds if the chunk of 2d
     meets `W` over that narrower interval. Otherwise 2d needs `n` larger in the margin argument.
     Margins are harmless (`n` is free), but the statement of 2d should carry them.
   * The rest of 2d.5 is sound:
     * `zⱼ ∉ h[E] ⊇ S` gives `Sⱼ ≠ S`;
     * `c ∈ Sⱼ` would give `Sⱼ = S` and `zⱼ ∈ S ⊆ h[E]`;
     * the eventual non-crossing of `Wⱼ` uses 2d.4 together with the relative closedness of crossing
       components.
2. **The triods of 2a, 2b.** The definition of a triod needs `Z = Λ₁ ∪ h[k⁻¹(τ)]` to be a continuum:
   * `Λ₁ = d⁻¹(1) ∩ h[E]` is a continuum (hereditary unicoherence) or empty;
   * the tip layer is a continuum;
   * their union is connected only if `Λ₁` is empty or meets the tip layer.

   The commission does not address this. It should be checked before 2a is formalized. A possible
   repair is to use the triod over `Z = h[k⁻¹(τ)]` alone and put `Λ₁` into an arm.

`InnerComponentsCross` remains a named hypothesis of `sep_by_crossing_uncond`,
`hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`, `hagopian76_T15_T17_cond3` and
`hagopian76_theorem1_of_step`.

### 1.3 §3: without conditions

**3c (`block_components_cross`): open.** It needs 2e.

**4.B: proved.**
* `isCrossingPiece_of_crossingComponent` is the general step: a crossing component of
  `M ∩ π⁻¹[D]` whose closure misses `E`, with `I₂ ∩ π[M] = ∅`, is a crossing piece. Its proof:
  * a component is closed in `M ∩ π⁻¹[D]` (`mem_component_of_mem_closure_in`), and `M` is closed in
    the plane (`closure_toPt`);
  * the closure misses `π⁻¹[I₂]` (it lies in `M`) and `π⁻¹` of the bottom edge (`mem_E_of_axis`);
  * **the side segments** (`side_point_open`): a point of the closure over the closed left side
    segment is a frontier point of `D`, so it lies over `F({3/22} × [0, r₂])`. Its height is not `0`
    (it is not in `E`) and not `r₂` (`F(3/22, r₂) ∈ I₂`, from `hIs`). The right side is the same.
* `p_on_crossing_piece` is the T12 form. It takes the package of `exists_T12Data_strands` for the
  constant `min ε₃ (θ/2)`, so that `h` and `h₁` are `θ/4`-small, and converts it back with
  `T12Data.mono`. Then:
  * the strands of `p = h x₀` and `f(p) = h₁ x₀` are crossing components (`strand_crossing`);
  * they are proper subcontinua (`closure_ne_univ_of_crossSet`) through points of `h[R(E)]` and
    `h₁[R(E)]`, hence miss `F` (4.A);
  * two components are equal or disjoint.

  The added hypothesis is `hI2M : Disjoint I₂ (π '' M)` (T7), as §0.2 asks.

**3.3 `sep_by_crossing_uncond`: proved, from `InnerComponentsCross` alone.**
* It combines 4.B with `sep_by_crossing` (batch 178).
* The frame hypotheses come from `lowFrame_hyps`, `injOn_pi_preimage` and `hπ.surjective`.
* **Added hypotheses:** `D′` connected and `{t₀} × (0, w₂) ⊆ D′`. Both are outputs of `hagopian76_D`
  and `hagopian76_K0`, and `exists_thm1Setup` discharges them.
* **Shape:** `∃ D : T12Data …, D.K = insert D.p K₀ ∧ ∀ lo hi, lo < t₀ → t₀ < hi →
  InnerComponentsCross D.G … lo hi → SepByCrossing D.G … D.p (D.f D.p)`. The package is chosen
  inside, because 4.B needs the particular package with small `h`, `h₁`.

**`hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`: proved, from
`InnerComponentsCross` alone.**
* **Shape:** `∃ cU > 0, cU ≤ 1 ∧ ∀ domain of height c₁ ≤ min c cU …, ∃ D, … InnerComponentsCross … →`
  `LastIntervalReachesOne`, respectively `→` blocks and `Property4 D (x (2m − 1)) (x (2m))`.
* `F ≠ E` (needed by `x2n_eq_one_of_cut`) comes from `hagopian76_property4_base`: `E` separates
  nothing.

**3.4 `exists_blocks_uncond`: proved.** Shape: `∃ c > 0, c ≤ 1 ∧ ∀ G d, … → ∀ c₁ D', c₁ ≤ c →
IsCrossRegion → LastIntervalReachesOne → ∃ e, … ∃ x n, …`, with the clauses of `exists_blocks`.
`e` comes from `hagopian76_J_xs`, finiteness from `hagopian76_I_finite_unif`, and nondegeneracy from
`crossingIntervals_nondegenerate`.

**3.5 `hagopian76_T15_T17_cond3`: proved.**
* **Shape:** the set-up of Property 3 and of the strand constants; a height `cU` chosen before
  `D`; for every domain with Hagopian's hypotheses, a package `D` such that
  `InnerComponentsCross` and `Property4Step D x m` (for every block sequence `x`) give `False`.
* Built inside: `SepByCrossing`, `F ≠ E`, `x₂ₙ = 1`, the blocks, `Y = π⁻¹[Fr D]`, and
  `hagopian76_T15_T17_cond_fix`.
* **Shape change:** the step hypothesis is restricted to block sequences, so the statement is
  stronger than with `∀ x m`.

### 1.4 §4: uniform heights

Checked: no height depends on `G` in substance. The sources are:

| theorem | height from |
|---|---|
| `hagopian76_property3_reduced` | `follows_crossing` |
| `hagopian76_property3_translate` | `hagopian76_property3_reduced` |
| `crossing_from_layer_translate_aux` (D1) | `pi_thin_near_layer` |
| `crossing_descends_aux` (D2) | the three above, `pi_thin_near_layer` |
| `property3_layer_aux` | D2 |
| `property3_layer_all` | `property3_layer_aux` for `G` and for the proper extension `G′` |
| `hagopian76_property3` | `property3_layer_aux`, `hagopian76_T7` |
| `crossing_length_pos_all`, `hagopian76_I_finite`, `hagopian76_property3_components`, `hagopian76_x2n_eq_one` | `property3_layer_all` |
| `component_over_middle_aux`, `cover_pocket_middle_aux` | `pi_thin_near_layer`, `hagopian76_link_control` |

The uniform statements have the shape
`∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
layer d 0 = layer k 0 → ∀ c₁ D', c₁ ≤ c → …`. They are `property3_reduced_unif`,
`property3_translate_unif`, `crossing_from_layer_translate_unif`, `crossing_descends_unif`,
`property3_layer_unif`, `property3_layer_all_unif`, `crossing_length_pos_all_unif`,
`hagopian76_I_finite_unif`, `hagopian76_property3_components_unif`, `hagopian76_property3_unif`,
`hagopian76_x2n_eq_one_unif`, `component_over_middle_unif` and `cover_pocket_middle_unif`.
As in the originals, `property3_reduced_unif` needs neither `E ⊆ G` nor `d⁻¹(0) = k⁻¹(0)`, and
`component_over_middle_unif` and `cover_pocket_middle_unif` do not need `E ⊆ G`.

The proofs are the original ones, with the inner heights taken from the uniform versions. One change
simplifies a proof: in `property3_layer_all_unif` the end layer `d⁻¹(1)` is handled through the
proper extension `G′` at the same height. The original took the minimum of the heights for `G` and
`G′`, and with a uniform height that minimum is not needed.

The old names are unchanged and remain valid, because each uniform statement implies the old one.
They are not re-proved as corollaries, so that the earlier files stay untouched.

### 1.5 §5: the assembly

**`Thm1Setup M`** (a structure; `M` with its instances is a parameter) carries:
* `hX`, `hi`;
* `E`, `k`, `hE`;
* `π`, `γ`, `hπ`, `hπS`, `hγπ`;
* the collar `F`, `hF`;
* `ε₁` with `IsEps1` and `EndCtl`;
* `L` with the chain, cover, refinement and Property 1;
* the strand constants `n`, `θ`, `c` (`n ≥ 15`);
* the domain: `c₁ ≤ c`, `D′` with `IsCrossRegion`, connected, the strip below, `r₂`, `s₂`, `I₂`,
  `hI`, `hIs`, `hIR`, `hDo`, `hDf`, `hFDf`, and `Disjoint I₂ (π '' M)`;
* the low vertical over `1/2` (`w₂`, `hFw`, `hseg`, `hsub`);
* Property 2 at `(ε₂, ε₃)` with `ε₃ < ε₂`;
* the package `D : T12Data E k π F D′ ε₃`;
* Property 3 as printed for `D.G`, and `I` finite.

`Thm1Setup.IsBlocks S x m` collects the block hypotheses.

Compared with commission 179 §5:
* the strand constants and `Property2At` are fields;
* the composant data and the blocks are not. Each statement that needs them builds them inside:
  the package with small `h`, `h₁` in `p_on_crossing_piece`, and the blocks in
  `hagopian76_T15_T17_cond3`. The step hypothesis quantifies over all block sequences.
* `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` is not a field: no statement of the project uses it.

**`exists_thm1Setup`: proved.** If `M` has a decomposable subcontinuum `A`:

| step | theorem |
|---|---|
| T1 | `hagopian75_exists_typeA'` |
| an accessible interior layer | `exists_accessible_typeA'` |
| T2 | `exists_quotient_plane'` |
| T3–T6 | `hagopian76_I1` (reparametrization, collar, strip below) |
| T5 | `exists_isEps1_endCtl`, `hagopian76_property1` |
| T9 | `strand_fine_translate` with `n = 15` |
| Property 2 | `hagopian76_property2` with `ε₂ = 1` |
| heights (§4) | `hagopian76_property3_components_unif`, `hagopian76_I_finite_unif`, `hagopian76_T15_T17_cond3` |
| T7, T8 | `hagopian76_T7`, `hagopian76_D`, `isCrossRegion_of_D` |
| `K₀` | `hagopian76_K0` at `t₀ = 1/2` |
| T12, T13, T15–T17 | `hagopian76_T15_T17_cond3` |

The domain height is the minimum of the strand height, the uniform heights and the height of T7.

**`hagopian76_theorem1_of_step`: proved.**
```
theorem hagopian76_theorem1_of_step
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 3 / (S.n : ℝ)) (19 / 22 - 3 / (S.n : ℝ)))
    (hstep : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsBlocks x m → Property4Step S.D x m) :
    Hagopian76Thm1
```
**Shape change:** `InnerComponentsCross` is a second hypothesis, because §2 stays open. It is asked
for every set-up. The 2a–2d route does not use the irreducibility of `F` beyond minimal
admissibility, so this is the form the route would deliver.

### 1.6 §6: the induction step

**Open.**
* E0 and E1 (`property4_step_unless`) need 3c: the components of `d⁻¹[B] ∩ O` through the low
  vertical must be pieces of the frame before SSL applies to `d⁻¹[J]`. 3c needs 2e.
* E2.1 (the shortest extension `L`), E2.4 (`H ⊆ L`, `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`), the cap, E2.5 and
  Case 2 are not started.

The named `Prop` is `Property4Step` (batch 175), with the block hypotheses `Thm1Setup.IsBlocks`.

## 2. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXIV (batch 179)". Its checks:
1. **The end layer of `F` (§2):** not in the text. 3a is proved (batch 178). 3b (2e) is still open,
   and two points of the proposed route need care (§1.2).
2. **p. 348, "Note that `x₂ₙ = 1`":** gap in exposition. It now rests on 2e alone
   (`hagopian76_x2n_eq_one_final`).
3. **p. 347, Property 3, used for the nondegeneracy of `I`:** correct. Property 3 as printed gives
   nondegeneracy (`crossingIntervals_nondegenerate`), as commission 179 §0.1 said.
4. **The order of the constants:** correct. Every height can be fixed before `F` (§1.4).
5. **pp. 348–349, Cases 1–2:** open (§1.6).

## 3. Axioms

`doc/batches/audits/axioms-batch179.txt` holds `#print axioms` for each of the 32 new theorems
(group *Hagopian 1976 XXIV (batch 179)* of `Axioms.lean`). Every one depends on exactly
`[propext, Classical.choice, Quot.sound]`.

The delivered statements are:
* `crossing_components_finite`, `crossingIntervals_nondegenerate`;
* `p_on_crossing_piece`, `sep_by_crossing_uncond`;
* `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`, `exists_blocks_uncond`;
* `hagopian76_T15_T17_cond3`;
* `exists_thm1Setup`, `hagopian76_theorem1_of_step`.

The named structures and `Prop`s of this batch are `Thm1Setup` and `Thm1Setup.IsBlocks`. The batch
also uses the earlier `InnerComponentsCross` (batch 178) and `Property4Step` (batch 175).

## 4. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_step (proved)
   ├─ exists_thm1Setup (proved): T1–T13 assembled
   │   └─ hagopian76_T15_T17_cond3 (proved)
   │       ├─ sep_by_crossing_uncond (proved)
   │       │   ├─ p_on_crossing_piece, 4.B (proved)
   │       │   └─ sep_by_crossing, SSL (proved, batch 178)
   │       ├─ hagopian76_x2n_eq_one_unif (proved)
   │       ├─ exists_blocks_uncond (proved): e, I finite, nondegeneracy
   │       └─ hagopian76_T15_T17_cond_fix (proved, batch 177)
   ├─ InnerComponentsCross for every set-up (2e)    OPEN
   │   └─ 2a, 2b, 2d (finiteness 2d.4 proved)       OPEN (two points, §1.2)
   └─ Property4Step for every set-up (§6)          OPEN
       ├─ E0, E1                                     need 3c ← 2e
       ├─ E2.1, E2.4                                 not started
       ├─ the cap, E2.5                              not started (tools proved, batch 178)
       └─ Case 2                                     not started
```

## 5. Skeleton proposal for what remains

1. **2e.** First settle the triod definition in 2a. Then, in order:
   * a statement of step 2 ("one half lies in `O`") as a lemma about `K⁻`, `K⁺` and
     `connectedComponentIn`;
   * 2a with `Z` a continuum;
   * 2d with the margin `4/n` (`no_end_layer_chunk`);
   * 2b's edge case.

   Proposed signature:
   ```
   theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
     InnerComponentsCross S.D.G S.π S.F S.D' (3/22) (19/22) S.r₂ S.s₂ S.I₂
       (3/22 + 3/S.n) (19/22 − 3/S.n)
   ```
   `Thm1Setup` has everything the route uses: the strand constants, Property 3, finiteness, and
   `D.hG` for void interiors.
2. **3c**, then **E0/E1** in the frame `lowFrame`.
3. **E2.1–E2.6** as in `doc/notes/hagopian76-cases.md`, against
   `hagopian76_property4_step (S : Thm1Setup M) x m (hx : S.IsBlocks x m) : Property4Step S.D x m`.
