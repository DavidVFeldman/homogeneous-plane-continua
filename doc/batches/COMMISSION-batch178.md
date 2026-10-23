# Commission: batch 178 — Part E, Hagopian 1976 XXIII: Theorem 1 — the order of strands without Schoenflies; separation along the vertical; the end layer of `F`; unicoherence; the assembly

**Go!** This batch runs on top of the batch-177 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch178.md`: this text, also pasted into the prompt.
* `Hagopian76W.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76W.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76W` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXIII (batch 178)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `HPC/Hagopian/H76Prop4.lean`, only to add fields to `T12Data` (§4.A), if you take that route.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 177

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1929 lines, with `sorryAx` in none. All 28 new theorems use only the
  standard three axioms.

**Accepted.**
* The strand lemma S0–S3, S5 (whole strands) and S6, with both shape changes: `n ≥ 15`, and an
  arbitrary `T12Data.K`.
* `exists_T12Data`, `pi_preimage_frontier_D` and `hagopian76_T15_T17_cond2`.
* `T15_T17_cond_hyps_inconsistent`. Thank you: the batch-176 statement was vacuous, and I accepted
  it in my audit. It is recorded in the ledger as a project error. `hagopian76_T15_T17_cond_fix` is
  accepted.
* The finding on blocks (report §1.C). The sharpened form is item §6 below.

## 1. S4 needs no Schoenflies coordinates

Report 177 §1.S4 asks for Schoenflies coordinates for `Cl D` with sides to sides, and for a
cross-cut lemma. Neither is needed. The order of strands follows formally from two facts that are
already proved:
* `crossing_sides` (`Hagopian76N.lean`): a crossing set has disjoint below and above sets, relative
  to the low vertical;
* `rect_domain_crosscut` (`H76Crosscut.lean`): the low vertical is a cross-cut.

**Notation.**
* `O := π⁻¹[D]`, with `D = F[D′]`.
* `Y := π⁻¹[Fr D]`, compact and connected (`pi_preimage_frontier_D`).
* `σ` is the **low vertical** over abscissa `1/2`: `π⁻¹ F[{1/2} × (0, w₂)]`, where `(1/2, w₂)` is
  the lowest point of `I` over `1/2`. Since `π` is injective over `D`, `σ` is an open arc and
  heights on it are well defined.
* A **crossing piece** is a connected `X ⊆ M ∩ O` with the following properties:
  * `X` is closed in `O`, that is, `Cl X ∩ O = X`;
  * `Cl X` misses `π⁻¹` of the bottom edge and of `I₂`;
  * `Cl X` meets both open side segments.

**Examples of crossing pieces.**
* Every strand.
* Every crossing component of `Z ∩ O` for compact `Z ⊆ M`, in particular for `Z = F` or a block
  `d⁻¹[B]`:
  * a component of a set closed in `O` is closed in `O`;
  * its closure misses `E` by `hagopian76_no_hair`;
  * its closure misses `π⁻¹[I₂]` because `I₂ ∩ π[M] = ∅`.

**The sides of a crossing piece.** For a crossing piece `X`:
* `X ∩ σ` is compact and nonempty. It is nonempty by S4a below. It is compact because the two ends
  of the closed segment are not in `Cl X`.
* Let `m(X)` and `M(X)` be its least and greatest heights.
* `A(X)` is the component of `O − Cl X` containing the part of `σ` below `m(X)`. `B(X)` is the
  component containing the part above `M(X)`. These are `belowSet` and `aboveSet` with
  `u₁ < m(X)` and `M(X) < u₂`.
* By `crossing_sides`, `A(X) ∩ B(X) = ∅`.
* Write `X′ ≺ X` (**`X′` below `X`**) for `X′ ⊆ A(X)`.

**S4a (every crossing piece meets `σ`).** Transport `rect_domain_crosscut` by `F` and `π`. Since
`Cl X` meets both open side segments, `X` cannot miss the low vertical.

**S4b (totality).** Let `X ∩ X′ = ∅`. Then `X′ ⊆ A(X)` or `X′ ⊆ B(X)`.
* `X′` is connected and misses `Cl X`, because `Cl X ∩ O = X`.
* Suppose `X′` lies in neither. A `σ`-point of `X′` below `m(X)` would lie in `A(X)`, joined to the
  low part by the segment of `σ` beneath it. Similarly above `M(X)`. So every `σ`-height of `X′`
  lies in `(m(X), M(X))`, and `m(X) < m(X′) ≤ M(X′) < M(X)`.
* Then the `σ`-points of `X` at heights `m(X)` and `M(X)` lie in `A(X′)` and in `B(X′)`.
* `X` is connected, misses `Cl X′`, and contains both. This contradicts `A(X′) ∩ B(X′) = ∅`.

**S4c (antisymmetry, symmetric form).** For disjoint crossing pieces, `X′ ⊆ A(X)` if and only if
`X ⊆ B(X′)`. Proof of "not both `X′ ⊆ A(X)` and `X ⊆ A(X′)`":
* `B(X)` misses `Cl X′`: `X′ ⊆ A(X)`, and `B(X)` is open and disjoint from `A(X)`.
* `B(X)` is connected and contains `σ`-points above both `M(X)` and `M(X′)`. So `B(X) ⊆ B(X′)`.
  Symmetrically `B(X′) ⊆ B(X)`.
* Call this set `B`. Its frontier in `O` lies in `Cl X ∩ Cl X′ ∩ O = X ∩ X′ = ∅`. So `B` is
  clopen in the connected `O`, nonempty, and not all of `O`.

"Not both `X′ ⊆ B(X)` and `X ⊆ B(X′)`" is the same argument with `A`. Then use S4b.

**S4d (transitivity).** `X″ ≺ X′ ≺ X` implies `X″ ≺ X`.
* By S4c, `X ⊆ B(X′)`.
* So `A(X′)` misses `Cl X`, is connected, and contains the low part of `σ`.
* Hence `A(X′) ⊆ A(X)`.

**S4e (no pocket over the inner middle).** If `X` is a crossing piece and `S` is a strand disjoint
from `X`, then `S ⊆ A(X) ∪ B(X)`. This is S4b. Pockets of `X` therefore contain no point of `M` over
the inner middle whose strand misses `X`.

Prove S4a–S4e as stated, for crossing pieces. If `crossing_sides` needs the vertical at a general
abscissa `t₀`, keep `t₀` general: everything below works for any `t₀` in the inner middle.

## 2. Separation along the vertical

**SSL (strand separation lemma).** Let `Z ⊆ M` be compact, and let `x, y ∈ (M ∩ O) − Z`. Let `X ∋ x`
and `Y ∋ y` be crossing pieces that miss `Z` and are either equal or disjoint (for example, the
strands of `x` and `y`, when these miss `Z`). Suppose `SepIn O (toPt Z) x y`. Then:
1. `X ≠ Y`, since otherwise `X` joins `x` to `y` off `Z`. Hence `X ∩ Y = ∅`, and by S4b and S4c,
   say `Y ≺ X`.
2. Choose `P ∈ Y ∩ σ` and `P′ ∈ X ∩ σ` at minimal distance. The open segment `(P, P′)` of `σ` misses
   `X ∪ Y`.
3. `(P, P′) ⊆ A(X) ∩ B(Y)`.
   * Points of `(P, P′)` near `P` lie in the open `A(X)`, which contains `P ∈ Y`.
   * `(P, P′)` is connected in `O − Cl X`.
   * Likewise for `B(Y)`, which contains `P′ ∈ X` by S4c.
4. If `(P, P′) ∩ Z = ∅`, then `X ∪ [P, P′] ∪ Y` is connected in `O − Z` and joins `x` to `y`. So
   there is a `z ∈ Z ∩ (P, P′)`.
5. Let `W_z` be the component of `Z ∩ O` through `z`. **If `W_z` is crossing:**
   * `W_z ⊆ A(X) ∩ B(Y)`, so `Y ≺ W_z ≺ X` (S4c);
   * `x ∈ B(W_z)` and `y ∈ A(W_z)`;
   * so `Cl W_z` alone separates `x` from `y` in `O`.

**Conversely**, a crossing component `W` of `Z ∩ O` with `Y ≺ W ≺ X` separates `x` from `y`.

**Corollary (`SepByCrossing`, general form).** Suppose:
* every component of `Z ∩ O` that meets `σ` is crossing;
* the strands of `x` and `y` miss `Z`.

Then `SepIn O Z x y` implies separation by the union of the closures of the crossing components of
`Z ∩ O`. In fact one closure suffices.

Prove SSL, its converse and the corollary.

## 3. The end layer of `F`, and saturation

The corollary needs: every point of `F` on `σ` lies on a crossing component of `F ∩ O`. Below, `F`
is `D.G` with decomposition `d = D.d`.

**3a. `d⁻¹(1) ⊄ O`.** This is a consequence of the irreducibility of `F` (`D.irr`).
1. Suppose `d⁻¹(1) ⊆ O`. The sets `d⁻¹[[1 − 1/m, 1]]` are compact, decreasing, and meet in
   `d⁻¹(1)`. So `T := d⁻¹[[1 − ε, 1]] ⊆ O` for some small `ε > 0` with `1 − ε ≥ e`. (If `F = E`,
   then `d⁻¹(1) = k⁻¹(1)` is not over `Cl D`, and there is nothing to prove.)
2. `F_ε := d⁻¹[[0, 1 − ε]]` is an extension of `E` away from `k⁻¹(0)`, and `F_ε ⊊ F`.
3. Separation in `O` by a compact set `X` is separation in the plane by `X ∪ Y`. State this as a
   helper lemma: `Y` is compact and connected, misses `O`, and contains `Fr O`.
4. Put `A := F_ε ∪ Y` and `B := T`.
   * `A ∩ B = d⁻¹(1 − ε)`, which is connected (`T ⊆ O` misses `Y`).
   * `B` is a proper subcontinuum of `M`, so it separates no two points of the plane
     (`no_proper_subcontinuum_separates`).
   * `A ∪ B = F ∪ Y` separates `p` from `f(p)`.
   * By `janiszewski_compact`, `A` separates them. So `F_ε` separates `p` from `f(p)` in `O`. This
     contradicts `D.irr`.

**3b. Saturation (Prop `InnerComponentsCross D`).** Every component `W` of `F ∩ O` through a point
`y` over the inner middle is crossing. Route:
1. **Set-up.**
   * By S1, `y = h(e)` with `h` a `θ/4`-homeomorphism and `|k(e) − abscissa(y)| < 1/n`.
   * Let `K⁻ := F ∩ h[k⁻¹[[0, k(e)]]]` and `K⁺ := F ∩ h[k⁻¹[[k(e), 1]]]`.
   * Both are continua containing `y`: `M` is hereditarily unicoherent
     (`hereditarilyUnicoherent_of_homogeneous_indecomposable`, `isContinuum_inter_of_HU`).
2. **If `K⁻ ⊄ O`.**
   * Boundary bumping in `K⁻` (`exists_mem_closure_component_notMem`) gives a component of
     `K⁻ ∩ O` through `y`. It lies in `W`, and its closure meets `Fr O`.
   * That frontier point is not over the bottom edge (no hair: `y ∉ E`) and not over `I₂`.
   * It is not over the right side, by S0: points of `h[k⁻¹[[0, k(e)]]]` over the strip have
     abscissa `< k(e) + 2/n < 19/22`.
   * So `Cl W` meets the left side.
   * If also `K⁺ ⊄ O`, the same argument gives the right side, and `W` is crossing.
3. **If `K⁻ ⊆ O` (an inner tip on the left).**
   1. **The tip.**
      * Let `τ` be the least parameter `k ∘ h⁻¹` on `K⁻`. Then `τ > 3/22 − 2/n`, by S0.
      * For small `δ`, `Q_δ := h[k⁻¹[[τ − δ, τ + δ]]]` is a continuum that meets `F` and misses
        `d⁻¹(0) = k⁻¹(0)` (by `θ`).
      * If `Q_δ` missed `d⁻¹(1)`, it would lie in `F` (no hair for `F`), and `K⁻` would have
        parameters `< τ`.
      * So `d⁻¹(1)` meets `h[k⁻¹(τ)]`.
   2. **The triod.**
      * Let `Λ₁ := d⁻¹(1) ∩ h[E]`, a continuum with parameter interval `[τ, τ₁]`.
      * If `τ₁ < k(e)`, then `Λ₁ ⊆ K⁻ ⊆ O`, so by 3a `d⁻¹(1) − h[E] ≠ ∅`.
      * Put `T := d⁻¹(1) ∪ K⁻ ∪ h[k⁻¹[[τ − δ, τ]]]` and `Z := Λ₁ ∪ h[k⁻¹(τ)]`.
      * Then `T − Z` is the union of three mutually separated nonempty sets:
        * `K⁻ − Z`, which contains `y` and lies in `F − d⁻¹(1)`;
        * `h[k⁻¹([τ − δ, τ))]`, which misses `F`;
        * `d⁻¹(1) − h[E]`.
      * `T` is a triod. This contradicts atriodicity
        (`atriodic_of_homogeneous_indecomposable mooreTriodStatement`).
   3. **The remaining configuration, `τ₁ ≥ k(e)`.** `d⁻¹(1)` swallows a chunk
      `h[k⁻¹((τ, τ₁))]` through `y`. Settle it with the same three tools: the triod (arms beyond
      either end of the chunk, and `F`'s layers below `1`), 3a, and the void interior of `d⁻¹(1)`
      in `F`. `hagopian76_I_finite` excludes crossing strands accumulating at level `1`.
4. **The right half.** `K⁺ ⊆ O` is symmetric.

If a configuration survives, describe it exactly in the report. It would be a gap in the text: "Note
that `x₂ₙ = 1`" and Property 4 for the top block both depend on it. Then state
`InnerComponentsCross D` and continue with it as a hypothesis.

**3c. Blocks inherit saturation.** For each block `B` (a component of `St J`, §6), every component
of `d⁻¹[B] ∩ O` meeting the inner middle is a crossing component of `F ∩ O`.
* A crossing `F`-component's interval lies in one block.
* Gap layers miss the inner middle of `O` altogether.
* So do the end layers `d⁻¹(xⱼ)` of the blocks. Along a crossing `F`-component `W ⊆ h[E]`, the layer
  of `F` through a point over the inner middle is the translated layer through it: `lemma3_half`
  both ways, with `h` and with `h⁻¹`, all far from the end sets. So its parameter lies strictly
  inside `W`'s interval, and is not the end of a block.

## 4. `SepByCrossing`, `x₂ₙ = 1`, and the top block

**4.A. The strands that matter miss `F`: by composants.** `exists_T12Data` builds `h` and `h₁`
through `hagopian76_T12_uncond`, which uses `translate_Rset_disjoint`, that is,
`h x₀ ∉ composant x₀` for the base point `x₀ ∈ E` (`p = h x₀`). Check that the same holds for `h₁`.
Record the following in `T12Data` (new fields), or in a companion structure produced by a new
`exists_T12Data'`:
* `x₀`;
* `D.h x₀ = D.p`;
* both composant conditions.

Then:
* `F ⊆ composant x₀`, since `F` is a proper subcontinuum through `x₀`.
* `h[R(E)] ⊆ composant p` and `h₁[R(E)] ⊆ composant (f p)` (`Rset_subset_composant`). Both are
  disjoint from `composant x₀` (`composant_eq_or_disjoint'`).
* The closure of the strand through a point `z` is a proper subcontinuum through `z`
  (`strand_lemma`), so it lies in `composant z`.
* **Hence the strand of every point of `h[R(E)] ∪ h₁[R(E)]` misses `F`.** In particular this holds
  for `p`, for `f(p)`, for every `yᵢ` with `Cl Cᵢ` essential to `h[R(E)]`, and for every `f(yᵢ)`.

**4.B. `p` and `f(p)` lie on crossing pieces.** Use `strand_crossing` with `e = x₀`, for `h` and for
`h₁` (both are `θ/4`-homeomorphisms by construction).

**4.C. `SepByCrossing` for `(F, p, f(p))`.** It follows from §2, 3b and 4.A–B. Then:
* `x₂ₙ = 1`, from `tailCutKeepsSep_of_sepByCrossing` and `x2n_eq_one_of_cut`;
* Property 4 for the top block, from `hagopian76_property4_top`, now with no hypothesis beyond 3b.

## 5. Unicoherence of the plane

`separatesPlane_union_of_inter_disconnected` (statement in the skeleton): if `A`, `B` are compact
and connected and `A ∩ B = K₁ ⊔ K₂` with `K₁`, `K₂` closed, disjoint and nonempty, then `A ∪ B`
separates the plane. The repository has unicoherence only in its closed-cover form
(`HPC.Moore.plane_unicoherent`, `M25Plane.lean`: `A ∪ B = Pt` gives `A ∩ B` connected). Report 177
§1.E asked for the separation form. A direct proof uses `borsuk_exists_log` (`Moore/Borsuk.lean`);
derive it from the closed-cover form instead if that is shorter.
1. Put `φ(z) := infDist z K₁ / (infDist z K₁ + infDist z K₂)`. It is continuous on the plane, with
   `φ = 0` on `K₁` and `φ = 1` on `K₂`.
2. Put `f := exp(πiφ)` on `A` and `f := exp(−πiφ)` on `B`. The two agree on `A ∩ B`, where
   `φ ∈ {0, 1}`. `f` is continuous on `A ∪ B` (closed pieces) and never zero.
3. Suppose `(A ∪ B)ᶜ` is connected. Then `borsuk_exists_log` gives a continuous `g` on `A ∪ B` with
   `exp g = f`.
4. `(g − πiφ)/(2πi)` is integer-valued and continuous on the connected `A`, hence a constant `n_A`.
   Likewise `(g + πiφ)/(2πi)` is a constant `n_B` on `B`.
5. At a point of `K₁`, `n_A = n_B`. At a point of `K₂`, `πi + 2πi n_A = −πi + 2πi n_B`, so
   `n_B = n_A + 1`. Contradiction.

Also state the domain form used in §8: separation in `O` by `X` equals separation in the plane by
`X ∪ Y`. This is the helper of 3a.

## 6. The blocks (C′)

Take the blocks to be the components of `St J = ⋃ J`, a finite union of closed intervals
(`hagopian76_I_finite`). Produce `x : ℕ → [0, 1]` and `n ≥ 2` with:
* `StrictMonoOn x (Icc 1 (2n))`;
* `x₁ = 0`, `x₂ = e` (`hagopian76_J_xs`), `x₂ₙ = 1` (§4);
* every member of `I` inside a block;
* **each block `[x₂ᵢ₋₁, x₂ᵢ]` a union of members of `J`**, the sharpening of report 177 §1.C;
* gaps `(x₂ᵢ, x₂ᵢ₊₁)` free of members of `J`.

Then feed `hagopian76_T15_T17_cond2`.

## 7. The assembly: Theorem 1 from the step alone

Isolate the induction step as the only open input.
1. Bundle the set-up of T1–T13 as a structure `Thm1Setup`, with the constants in the order of
   commission 177 §2: `ε₁`, `L` (Property 1) → `n`, `θ`, `δ′`, `η`, `c(n)` → `D` (T7, height
   `≤ c(n)`) → `ε₂` → `ε₃` (Property 2, `Property2At`) → `D : T12Data` → the blocks of §6.
2. Prove `hagopian76_theorem1_of_step`:
   `(∀ S : Thm1Setup, Property4Step S.D S.x S.n) → Hagopian76Thm1`.
3. The pieces are proved:
   * the minimal admissible `E` (Lemmas 1–5);
   * the plane quotient (`exists_quotient_plane`);
   * the reparametrization (`hagopian76_reparam`);
   * the collar (`exists_collar`);
   * `ε₁`, `L`, Property 1;
   * T6–T8 (`hagopian76_I1`, `hagopian76_T7`, `hagopian76_D`);
   * the strand constants;
   * Property 2 (`hagopian76_property2`);
   * `exists_T12Data` and §6.
4. Put into `Thm1Setup` whatever the step will need, in particular Property 2 at `(ε₂, ε₃)`, the
   strand constants, and the composant fields of 4.A.
5. If 3b stays open, the theorem takes `InnerComponentsCross` as a second hypothesis.

## 8. The induction step (E): what to prove, and where the text is thin

Pages 348–349, Cases 1–2. Hagopian's notation: `I = [x₂ᵢ₋₁, x₂ᵢ]` has Property 4 with `yᵢ ∈ K`,
`Cᵢ` the `yᵢ`-component, and `J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`. The gap continuum is
`Γ := d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]`.

**E0. Property 4 (2) in strand terms.** Let `y` be a point over the inner middle such that the
strands of `y` and `f(y)` miss `F` (§4.A). Then `d⁻¹[B]` separates `y` from `f(y)` in `O` if and
only if some `B`-strand lies between the two strands. This is SSL with 3c.

**E1. The case printed as "unless".** "Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)` and `J` has
Property 4 unless `yᵢ` is above `d⁻¹[J]`." If some `J`-strand lies between `Cᵢ` and the strand of
`f(yᵢ)`, then `J` has Property 4 with `yᵢ₋₁ := yᵢ`. Prove it.

**E2. The remaining case.** No `J`-strand lies between `Cᵢ` and the strand of `f(yᵢ)`; some
`I`-strand `W` does. Hagopian's argument, rewritten, consists of the following claims. Prove what
you can and name the rest.
1. **The first strand.**
   * `L` is the shortest extension of `Cl Cᵢ` away from `X` in `h[R(E)]` that contains a strand
     other than `Cᵢ`, and `Cᵢ₋₁` is that strand ("the first component … met by extending `Cl Cᵢ`
     away from `X`").
   * Apply 3b's argument to `L`, whose end sets are `X` and its far end. `L` meets the inner middle
     in whole strands except at its ends. `L` misses `F` (§4.A).
   * `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`, with `Cl Cᵢ₋₁` essential to `h[R(E)]`.
2. **`N`.**
   * `N` is the subcontinuum of `L` essential to `h[R(E)]` with `yᵢ` and `yᵢ₋₁` in its end sets.
   * In Case 1, `N ∩ O` lies in the left parts of `Cᵢ` and `Cᵢ₋₁` and in stubs within `3/n` of the
     sides. So `N` stays `ε₂`-away from the low vertical `V` over `15/22` (S6).
   * Which end of `Cᵢ₋₁` `L` enters by is part of the Case 1 claim (item 3).
3. **The cap (Case 1).** With `P := d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`, Hagopian's two sentences ("`yᵢ₋₁` is
   between `d⁻¹[I]` and `d⁻¹[J]`"; "`f[N]` does not intersect `P`. Hence `f(yᵢ₋₁)` is either above
   …") together amount to: **`P` separates `yᵢ` from `f(yᵢ)` in the plane.** Since `N` and `f[N]`
   miss `P`, `P` then separates `yᵢ₋₁` from `f(yᵢ₋₁)`.

   Use §5 (`d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` meets `Q` in exactly two points), and check three things:
   * **(α)** `Q` is one segment of the vertical over `15/22` between consecutive points of `F`. If
     the band between the `J`- and `I`-strands crosses that vertical several times, one `Q` may not
     close it. Decide whether `Q` should be the segment met first by `Cᵢ` coming from the left, or
     whether the whole low vertical `V` should replace `Q`.
   * **(β)** `I`-strands and `J`-strands may interleave in the order of §1. Decide what "between
     `d⁻¹[I]` and `d⁻¹[J]`" must mean.
   * **(γ)** Which side of the cap is bounded.
4. **Property 2.** `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` ("for otherwise, a subcontinuum of `L` would violate
   Property 2"). Identify the subcontinuum `H ⊆ L` and its end sets, and use `Property2At`.
5. **Local to global.** From "`P` separates `yᵢ₋₁` from `f(yᵢ₋₁)`", item 4, and
   `|yᵢ₋₁ − f(yᵢ₋₁)| < ε₃`, conclude that a `J`-strand lies between `Cᵢ₋₁` and the strand of
   `f(yᵢ₋₁)`. This is not immediate. A route:
   1. Apply Janiszewski with `A := d⁻¹[J] ∪ V ∪ Y` and `B := d⁻¹[I] ∪ Γ ∪ V ∪ Y`.
      * `A ∪ B ⊇ P` when `Q ⊆ V`. A `Q` above the lowest point of `I` over `15/22` (in a bay of `D`)
        is not in `V`; this is part of (α).
      * Their intersection `V ∪ Y ∪ d⁻¹(x₂ᵢ₋₂)` is connected if `d⁻¹(x₂ᵢ₋₂)` meets `V ∪ Y`; check
        this.
   2. The short segment from `yᵢ₋₁` to `f(yᵢ₋₁)` misses `B`:
      * it misses `d⁻¹[I]` by item 4;
      * it misses `Γ` by 3c;
      * it misses `V`, by positions;
      * it misses `Y` if it stays in `O`.

      Check the last point. `M` stays `ε₂` away from `π⁻¹[I₁ ∪ I₂]`. `f(z) ∉ E` for
      `z ∈ h[R(E)]`. `eps3_positions_middle` (batch 176) gives positions. Hagopian asserts
      "`f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`" without argument; this is where it is used.

      So `A` separates `yᵢ₋₁` from `f(yᵢ₋₁)`.
   3. That is, `d⁻¹[J]` separates them in the left part `O_L` of `O − V`.
   4. Run SSL inside `O_L`, where `σ` is again a cross-cut and strands cut at `V` are crossing
      pieces from the left side to `V`.
   5. Then relate the order in `O_L` to the order in `O`.
6. **Case 2** (p. 349). The text uses only Property 2, and "`f(yᵢ₋₁)` is above `d⁻¹[I]`" is
   unargued there. Reconstruct it.

**Report for E.** Besides the Lean work, write `doc/notes/hagopian76-cases.md`: a reconstruction of
Cases 1–2 in strand language, with every configuration either handled or named as a `Prop`.

## 9. Order

1. §1, §2, §5. These are short and self-contained.
2. §3 and §4. If 3b resists, name `InnerComponentsCross` and go on.
3. §6, then §7.
4. §8: E0, E1 and the ingredients E2.1, E2.2, E2.4 first; then the cap.

If §7 is too large for this batch, stop after §6 and give a precise skeleton for §7 in the report.

## 10. Places to check (candidate ledger entries)

1. **p. 348**, "Note that `x₂ₙ = 1`": through §4. It depends on 3b, which the text never mentions.
2. **p. 348**, Property 4 for the top block: the same.
3. **p. 348**, "Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)` and `J` has Property 4 unless `yᵢ` is
   above `d⁻¹[J]`": E1.
4. **p. 348**, Case 1: the position sentence, `Q`, and "between" (α, β, γ).
5. **p. 349**, Case 2: "If `yᵢ₋₁` is above `d⁻¹[J]`, it is between … and `f(yᵢ₋₁)` is above
   `d⁻¹[I]`".
6. **The end layer of `F`** (3a, 3b). It is not in the text, and the text needs it.

## 11. Deliverables

1. The items of §1–§8.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch178.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. `doc/notes/hagopian76-cases.md` (§8).
5. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
