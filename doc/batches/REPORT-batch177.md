Commission read: `doc/batches/COMMISSION-batch177.md` ("Commission: batch 177 — Part E, Hagopian 1976 XXII: Theorem 1 — the strand lemma; the endgame rebuilt on it").

# Report, batch 177

## 0. Summary

* **The strand lemma, S0–S3: proved** (`strand_fine_translate`, `strand_closure_subset`,
  `strand_crossing`, `strand_lemma`). The constants are chosen in the commission's order
  `n → θ(n) → δ′ → η → c(n)`, and none depends on `D`. Every point of `M` over the inner middle of
  a domain of height `≤ c(n)` lies on a **strand**. A strand is a crossing component whose closure
  lies in a `θ/4`-translate `h[E]` and contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`.
* **S4 (the order of strands): open.**
* **S5: proved in its whole-strand part** (`typeA'_strand_aux`, `typeA'_inner_strands`). The
  description of end strands as hairs is open.
* **S6 (fine positions): proved** (`strand_fine_positions`).
* **A (`T12Data` exists): proved** (`exists_T12Data`). T12 (2) now holds for the same `h` as
  T12 (3) (`strand_essential`). This was the batch-176 obstruction.
* **B (`π⁻¹[Fr D]` is compact and connected): proved** (`pi_preimage_frontier_D`, with the general
  `pi_preimage_continuum`).
* **C (the blocks of `St J`): open.** Not formalized this batch. There is also a finding about the
  shape of the block hypothesis; see §1.C.
* **D (`SepByCrossing`), E (`Property4Step`): open.** Both rest on S4.
* **F: the strongest conditional form is proved** (`hagopian76_T15_T17_cond2`). The `T12Data`
  package and `Y` are no longer hypotheses.
* **A defect in the batch-176 delivery, corrected.** The hypotheses of `hagopian76_T15_T17_cond`
  are inconsistent (`T15_T17_cond_hyps_inconsistent`), so that theorem is vacuous. The corrected
  statement `hagopian76_T15_T17_cond_fix` is proved, with the batch-176 proof. See §1.F.
* **Nothing of Hagopian's is refuted.** The count of defective proofs in the paper stays at fourteen.

STATUS lines, in order:
* `STATUS: S0–S1 proved (exists_param_sep, strand_fine_translate; structure StrandConst)`
* `STATUS: S2–S3 proved (strand_closure_subset, strand_crossing, strand_lemma = strand_inner_middle)`
* `STATUS: S4 open (strand_order)`
* `STATUS: S5 partly proved (typeA'_strand_aux, typeA'_inner_strands; end strands as hairs open)`
* `STATUS: S6 proved (strand_fine_positions)`
* `STATUS: A proved (exists_T12Data; strand_essential)`
* `STATUS: B proved (pi_preimage_frontier_D; pi_preimage_continuum, frontier_D_continuum)`
* `STATUS: C open (exists_blocks)`
* `STATUS: D open (sep_by_crossing; rests on S4)`
* `STATUS: E open (hagopian76_property4_step; rests on S4 and the cap)`
* `STATUS: F conditional form proved (hagopian76_T15_T17_cond2); hagopian76_theorem1_final open`
* `STATUS: batch-176 hagopian76_T15_T17_cond vacuous; corrected as hagopian76_T15_T17_cond_fix (proved)`

The build:
* `lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76V` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 1929 lines (1901 + 28), with `sorryAx` in no line; see §3.
* All 28 new theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* No declaration uses `sorry`. The word occurs only in the comment block at the end of
  `Hagopian76V.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76V.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Strand.lean`: `θ(n)`, `StrandConst` (S0–S1), S2, S3;
* `H76StrandUse.lean`: the inner middle, S5, S6, components in `M` and in the plane, strands are
  essential;
* `H76T12Exists.lean`: `π` proper with connected fibres, `Fr D`, `T12Data`, the corrected and the
  new conditional assembly.

No earlier `Hagopian76*.lean` file was edited. The commented-out shapes there (`exists_T12Data … :
Nonempty (T12Data …)` in `Hagopian76U.lean`, and the older copies) are not proved as stated. The
proved form has the T12 set-up as hypotheses and fixes `D.K`.

## 1. The items

### 1.S0–S1 The constants (proved)

* **`exists_param_sep`** (statement unchanged). The pairs `(a, b) ∈ E × E` with
  `|k(a) − k(b)| ≥ 1/n` form a closed subset of the compact `E × E` that misses the diagonal.
  `dist` is positive there, hence bounded below (`exists_pos_lt_on_compact`).
* **`StrandConst E k π F n θ c`** (structure; the shape of S0–S1):
  * `θ > 0`, and `c ∈ (0, 1]` is the height of the thin strip `F[[0, 1] × [−c, c]]`;
  * `fine` (S0): if `h` is a `θ/4`-homeomorphism, `z ∈ E`, and `h(z)` lies over the strip at
    abscissa `s`, then `|k(z) − s| < 2/n`;
  * `translate` (S1): every `y ∈ M` over the strip at abscissa `s` is `h(e)` for a
    `θ/4`-homeomorphism `h` and some `e ∈ E` with `|k(e) − s| < 1/n`.
* **`strand_fine_translate`**: for every `n ≥ 1` the constants exist. The proof follows the
  commission. `δ′` comes from `effros_homogeneous_set` at `θ/4`. `η = min(δ′, θ/4, 1/n)`. `c` comes
  from `pi_thin_near_layer` on `[0, 1]` at `η`. S0 is the computation
  `dist(z, e′) < θ/4 + η ≤ θ/2 < θ`. S1 is Effros applied to `dist(e′, y) < η ≤ δ′`.

**The order of constants (§2, checked).** Nothing in S0–S1 refers to `D`, `ε₁`, `L`, `ε₂` or `ε₃`.
The strand results take `D` as an arbitrary `IsCrossRegion` of height `c₁ ≤ c(n)`.
* T7 (`hagopian76_T7`) gives `I₂` at every height `≤` a prescribed `c`, so `c(n)` can be fed to it.
* `ε₁` and `L` are not used by the strand results at all.
* `ε₂` and `ε₃` are not used either. In `exists_T12Data` the T12 homeomorphisms are taken at
  `min(ε₃/2, θ/4)`, so **no constraint `ε₃ ≤ θ/2` is needed**.
The order is compatible with T4–T13 as formalized.

### 1.S2 The closure of a strand lies in the translate (proved)

**`strand_closure_subset`.** Assume `n ≥ 15`, a domain of height `c₁ ≤ c`, a `θ/4`-homeomorphism `h`
and `e ∈ E`. Then the closure of the component of `M ∩ π⁻¹[D]` through `h(e)` lies in `h[E]`.
* By S0 (`strand_off_ends`), a translate `h(z)` over `Cl D` has `3/22 − 2/n < k(z) < 19/22 + 2/n`.
  Hence the closure misses `h[k⁻¹(0)]` and `h[k⁻¹(1)]` (since `2/n ≤ 2/15 < 3/22`).
* Then no hair applies to `h[E]`. The transport of `IsMinimalAdmissible` along a homeomorphism of
  `M` was already a lemma (`exists_image_map`).
* *Shape:* `n ≥ 15` instead of `n ≥ 100`; S0 needs only `2/n < 3/22`. The commission's inner middle
  needs `3/22 + 3/n < 19/22 − 3/n`, which holds for `n ≥ 9`.

### 1.S3 Strands cross (proved)

**`strand_crossing`.** Assume, in addition, that `h(e)` is over `D` and
`3/22 + 2/n ≤ k(e) ≤ 19/22 − 2/n`. Then the component `C` through `h(e)` is a crossing component.
Moreover `Cl C` contains:
* `h(y_L)` and `h(y_R)`, with `k(y_L) ≤ k(e) ≤ k(y_R)`, `|k(y_L) − 3/22| < 2/n` and
  `|k(y_R) − 19/22| < 2/n`;
* `h[k⁻¹((k(y_L), k(y_R)))]`, hence `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`.

The proof follows the batch-175 argument, with S0 in place of `IsEps1.sep_of_gap`.
* Boundary bumping (`exists_mem_closure_component_notMem`) is applied in the halves
  `h[k⁻¹[[0, k(e)]]]` and `h[k⁻¹[[k(e), 1]]]`. Both lie in `M`, so no bumping inside an extension is
  needed. Their ends are not over `Cl D` by S0.
* The frontier point that bumping produces is constrained as follows:
  * it is not over the axis, by no hair for `E` (this would put `h(e)`, which lies above the axis,
    in `E`);
  * it is not over the far side, by S0 and the margin `2/n`;
  * frontier points over `I₂` do not arise, because `IsCrossRegion.frontier_sub` already confines
    `Fr D ∩ π[M]` to the bottom edge and the two side segments.
* The middle is `layerSet_Ioo_subset` applied in `h⁻¹[Cl C] ⊆ E`, which is S2.

**`strand_inner_middle` / `strand_lemma`** (S1 + S3). Every `y ∈ M` over `z ∈ D′` with
`3/22 + 3/n ≤ z₁ ≤ 19/22 − 3/n` is `h(e)` with `|k(e) − z₁| < 1/n`. Hence the bounds of S3 hold,
and the component through `y` is a strand.

### 1.S4 The order of strands (open)

*Obstruction:* the cross-cut argument needs Schoenflies coordinates for `D` itself. The project has
`jordan_inner_collar` for the collar rectangle, but not a homeomorphism of `Cl D` onto a square
that carries the side segments to sides. It also needs the separation of `D` by a cross-cut from
side to side. Neither is formalized. Disjointness of distinct strands is immediate: they are
distinct components of the same set.

### 1.S5 Type A′ continua meet the inner middle in whole strands (proved, except the hairs)

* **`typeA'_strand_aux`** (general end sets). Let `G` be type A′, `y ∈ G`, and `S` the component of
  `M ∩ π⁻¹[D]` through `y`, with `Cl S` missing `d⁻¹(0)` and `d⁻¹(1)`. Then `Cl S ⊆ G` (no hair
  for `G`), and `S` is the component of `G ∩ π⁻¹[D]` through `y`.
* **`typeA'_inner_strands`** is the case `d⁻¹(0) = k⁻¹(0)`, i.e. Hagopian's `F`.
  * `d⁻¹(0)` is not over `Cl D`, so only `d⁻¹(1)` can produce an end strand, as the commission
    says.
  * If `y ∈ G` is over the inner middle and the closure of its strand misses `d⁻¹(1)`, then the
    component of `G ∩ π⁻¹[D]` through `y` is that strand, and it is a crossing component of `G`.
* *Open:* "the part of `F` in an end strand is a hair". This needs `lemma3_half` along a small
  translate and the pocket structure of S4.

### 1.S6 Fine positions (proved)

**`strand_fine_positions`.** Every point `q` of the closure of the component through `h(e)` that
lies over the thin strip at abscissa `s` is `h(t)` with `|k(t) − s| < 2/n`. This is S2 followed by
S0.

### 1.A `T12Data` exists (proved)

**`exists_T12Data`.**
* *Set-up:* that of `hagopian76_T12_uncond` for `[a, b] = [3/22, 19/22]`, with `D = F[D′]` an
  `IsCrossRegion` of height `c₁ ≤ c(n)`, the strand constants with `n ≥ 15`, and
  `3/22 + 2/n ≤ t₀ ≤ 19/22 − 2/n`.
* *Conclusion:* for every `ε₃ > 0` and `K₀ ⊆ M` there is `D : T12Data` with `D.p = D.h(x)`,
  `k(x) = t₀` and `D.K = K₀ ∪ {D.p}`.
* *Proof:*
  * `hagopian76_T12_uncond` at `ε = min(ε₃/2, θ/4)` gives `x`, `h`, `h₁` and a separating extension
    `H`.
  * `p = h(x)` lies over `D`, because its component has closure meeting the sides and so is
    nonempty.
  * `hagopian76_T13_uncond` gives `G ⊆ H`, irreducible.
  * **`ess`** is `strand_essential` with `e = x`. By S2 and S3, `h⁻¹[Cl C_p] ⊆ E ⊆ R(E)` is a
    continuum meeting the two distinct layers `k(y_L) < k(y_R)`. This is Hagopian's "by Lemma 5".
* Components of `M ∩ π⁻¹[D]` taken in the plane and taken in `M` agree
  (`val_preimage_connectedComponentIn`).
* *Shape:* `T12Data.K` is an arbitrary set containing `p`, and Hagopian's arc component over
  `⟨p₃, q₃⟩` is not constructed. The theorem accepts any `K₀`. The p. 347 reading "essential to
  `R(E)` onto `Cl C`" is the one formalized (commission §3.A note; no misprint).

### 1.B `π⁻¹[Fr D]` is compact and connected (proved)

* **`pi_fibre`**: each fibre of `π` is a layer of `E` or a point, so it is compact and connected.
* **`pi_preimage_continuum`**: for compact connected `V`, `π⁻¹[V]` is compact and connected.
  * `π` is closed (`pi_isClosedMap`) with compact fibres, hence proper
    (`isProperMap_iff_isClosedMap_and_compact_fibers`).
  * Connectedness follows from `isPreconnected_preimage_of_fibres`, applied on the compact space
    `π⁻¹[V]`.
* **`frontier_D_continuum`**: `Fr D = I₂ ∪` bottom `∪` the two side segments is a continuum. The
  four pieces are chained at `F(a, 0)`, `F(b, 0)` and `F(a, r₂)`.
* **`pi_preimage_frontier_D`**: `Y = π⁻¹[Fr D]` is compact and connected, misses `π⁻¹[D]`, and
  contains `Fr π⁻¹[D]`. These are exactly the hypotheses on `Y` in `hagopian76_property4_top`.
* *Shape:* `Fr D` is not shown to be a simple closed curve; connectedness is all that is needed.

### 1.C The blocks of `St J` (open)

Not formalized. The input is in place: `hagopian76_I_finite`, `hagopian76_J_xs` (`e < x` for every
`[x, y] ∈ I`), and `hagopian76_property3_components` (no crossing component lies in one layer, so
`x < y`). The merging is finite combinatorics on closed intervals.

**Finding (shape of the block hypothesis).** The conditional forms (`hagopian76_T15_T17_cond_fix`,
`hagopian76_T15_T17_cond2`) ask only that every member of `I` lie in some block. The coarse choice
of two blocks, `[0, e]` and `[min x, max y]` (or `[min x, 1]`), already satisfies this. With coarse
blocks, `Property4Step` is the step from the top block straight to `[0, e]`. Hagopian's Cases 1–2 do
not prove that step: they use the gap structure of `St J`. So a faithful item C should also require
each block to be covered by members of `I`, and `Property4Step` should be stated for such blocks.
The conditional theorems remain correct as stated, but they are weaker than intended.

### 1.D `SepByCrossing` by the ladder (open)

*Obstruction:* the ladder argument needs S4 (the linear order of strands, and "between") and the
hair description of end strands (S5, last bullet). Neither is formalized. What is in place:
* `F ∩ K₀` over the inner middle lies in whole `F`-strands, except for end strands
  (`typeA'_inner_strands`);
* `p` and `q` lie on strands (`strand_lemma`).
The converse, "a whole `F`-strand between them separates them", also needs S4's sides.

### 1.E `Property4Step` (open)

*Obstruction:* every sentence of Cases 1–2 uses S4. The cap `Λ` of §3.E.3 needs the unicoherence
of the plane in the form "two continua with disconnected intersection separate". The project has
Janiszewski's theorem (`janiszewski_compact`, `sepIn_union_cases`), not this converse. Sentence 4
(`N` against `π⁻¹(p₄)`) is no longer blocked by the range of control: `p₄ = 15/22` lies in the
inner middle for `n ≥ 15`, and S6 gives fine positions there.

### 1.F The assembly (conditional form proved)

* **`T15_T17_cond_hyps_inconsistent`**: a strictly increasing `x : ℕ → [0, 1]` with
  `x(2n) = 1` is impossible, because `x(2n) < x(2n + 1) ≤ 1`. The batch-176 theorem
  `hagopian76_T15_T17_cond` assumes both, so **it is vacuous**. This is a defect of the batch-176
  statement, not of Hagopian's text.
* **`hagopian76_T15_T17_cond_fix`**: the same statement with `StrictMonoOn x (Icc 1 (2 * n))`. The
  proof is the batch-176 proof, using monotonicity only on the indices `1, …, 2n`.
* **`hagopian76_T15_T17_cond2`** (item F). Assume the set-up of `exists_T12Data` and that `D′` is
  connected. Then for every `ε₃ > 0` and `K₀` there is a package `D` such that the following give
  `False`:
  * `SepByCrossing` for `D.p`, `f(D.p)`;
  * blocks `x₁ < ⋯ < x₂ₙ` (strictly increasing on `1, …, 2n`, with `x₁ = 0`,
    `d⁻¹[[0, x₂]] = E`, every member of `I` in a block, and `x₂ₙ = 1`);
  * `Property4Step D x n`.
* Remaining for `hagopian76_theorem1_final`:
  * `SepByCrossing` (D);
  * the blocks (C), with the sharpening of §1.C;
  * `Property4Step` (E);
  * the reduction of `Hagopian76Thm1` to the set-up (T1–T11, with the strand constants chosen
    before `D`).

## 2. Ledger entries (`LEDGER.md` §6, batch 177)

1. **p. 346, T9**, "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`": **superseded in the fine
   form.**
   * A crossing component through the inner middle has closure in a `θ/4`-translate `h[E]`
     containing `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]` (S2, S3).
   * Along it, positions are within `2/n` (S6).
   * The chain `L` is not needed for this.
2. **p. 348**, "Note that `x₂ₙ = 1`": **still reduced** to `SepByCrossing`. That statement is open
   (D), and it rests on S4.
3. **p. 348, Case 1**, "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` …": **gap in exposition,
   open.** The cap `Λ` needs the converse of Janiszewski's theorem, which is not formalized.
   Whether a bounded side matters is not checked formally.
4. **p. 348**, "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`": **the range obstruction
   is removed.** `15/22` lies in the inner middle, and S6 gives positions within `2/n`. The full
   sentence is open with E.
5. **p. 349**, "Hence `f(yᵢ₋₁)` is either above …"; Case 2: **open**, resting on S4.
6. **The order of constants**: **recorded.** The resolution `n → θ → δ′ → η → c(n)` must be fixed
   before `D`. Hagopian's text does not fix an order. With this order nothing downstream is
   constrained (§1.S0–S1).

## 3. Axioms

Group *Hagopian 1976 XXII (batch 177)* of `Axioms.lean` / `axioms.txt`, with 28 declarations. The
audit is `doc/batches/audits/axioms-batch177.txt`. Every declaration shows exactly
`[propext, Classical.choice, Quot.sound]`.

| Theorem | Axioms |
| --- | --- |
| `exists_param_sep`, `strand_fine_translate`, `strand_lemma`, `strand_fine_positions`, `typeA'_inner_strands`, `exists_T12Data`, `pi_preimage_frontier_D` | standard three |
| `exists_param_sep_aux`, `strand_fine_translate_aux`, `strand_off_ends`, `strand_closure_subset`, `strand_crossing` | standard three |
| `crossSet_univ_eq`, `val_preimage_connectedComponentIn`, `val_preimage_closure_connectedComponentIn`, `strand_inner_middle`, `strand_fine_positions_aux`, `typeA'_strand_aux`, `typeA'_inner_crossing`, `strand_essential` | standard three |
| `pi_fibre`, `pi_preimage_continuum`, `frontier_D_continuum`, `pi_preimage_frontier_D_aux`, `exists_T12Data_aux`, `T15_T17_cond_hyps_inconsistent`, `hagopian76_T15_T17_cond_fix`, `hagopian76_T15_T17_cond2` | standard three |

Named `Prop`s and structures introduced: the structure `StrandConst` (S0–S1). No new named `Prop`.

## 4. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1  (open)
└─ reduction to the set-up T1–T11 (proved piecewise, not assembled; strand constants before D)
   └─ hagopian76_T15_T17_cond2  (proved)
      ├─ exists_T12Data            (proved, batch 177: strand_essential ← S2, S3)
      ├─ pi_preimage_frontier_D    (proved, batch 177)
      ├─ hagopian76_T15_T17_cond_fix (proved; corrects batch-176 cond)
      │  ├─ hagopian76_property4_top  (proved, batch 176, from SepByCrossing)
      │  ├─ not_property4_E           (proved, batch 176)
      │  └─ false_of_property4_chain  (proved, batch 176)
      ├─ SepByCrossing             (OPEN: D; needs S4, hairs)
      ├─ blocks of St J            (OPEN: C; combinatorics, and the sharpening of §1.C)
      └─ Property4Step             (OPEN: E; needs S4, the cap Λ)
```

## 5. Skeleton proposal for what remains

1. **S4a, Schoenflies for `D`.** A homeomorphism of `Cl D` onto `[0, 1]²` that carries the bottom
   edge, `I₂` and the side segments to the four sides. The inputs are `hagopian76_D_aux`,
   `jordan_inner_collar` and `tarc_pullback`.
2. **S4b, the cross-cut lemma.** A connected subset of `D` meeting both side segments separates the
   bottom edge from `I₂` in `D`.
3. **S4, `strand_order`.** For strands `S ≠ S′`, `S′` lies below or above `S`. Pockets contain no
   point of `M` over the inner middle; for this use S3 together with S4b.
4. **C′, `exists_blocks`.** Blocks covered by members of `I`, with `Property4Step` restated for
   such blocks.
5. **D, `sep_by_crossing`.** By `sepIn_union_cases` in `O_inner`, with S4 and S5.
6. **E.** The converse of Janiszewski's theorem (unicoherence of the plane), then Cases 1–2 with S4
   and S6.
