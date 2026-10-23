# Commission: batch 190 — Part E, Jones 1975 II: the planar core; `NoArcIndecHomPlane`

**Go!** This batch runs on top of the batch-189 work. Two files come with it, as separate uploads:

* `COMMISSION-batch190.md`: this text, also pasted into the prompt.
* `Jones75B.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones75B.lean`. You may split it under `HPC/Jones/`.
  * Add `import HPC.Jones.Jones75B` at the end of `HPC.lean`. It imports `HPC.Jones.Jones75A`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1975 II (batch 190)");
  * `README.md`;
  * `LEDGER.md`: the Jones 1975 section;
  * `OPEN.md`;
  * `doc/notes/jones75.md`;
  * comments only, in files that keep a commented-out copy of a statement proved here (for
    example `hagopian76_theorem1` in the `OPEN` block of `Hagopian76P.lean`): replace the copy by
    a one-line pointer.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 189

* **Delivery.** This time the project download was current: its `axioms.txt` equals the overlay of
  your tarball on my batch-188 tree (2479 lines). Keep publishing the tarball and manifest (§10.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2479 lines (2414 + 65 added, none removed), with `sorryAx` in none.
  The 65 new theorems use only the standard three axioms. The five `Jones75*.lean` files contain no
  `sorry`, `admit` or `axiom` outside comments.
* **Every formal item is proved**, including (L) in both forms. Your shape changes (`line_arc`
  without `S`, `no_reversal_arc` without `A ∩ C = {p}`) are improvements.
* **Your hand proof (report §6.3) has an error.** I read it and missed the error; an independent
  check (a separate agent) found it.
  * The shadow lemma and the flow box are stated for the whole box, but they hold only in the
    middle band `X ∈ [¼ + κ, ¾ − κ]`. Near an edge, backtracking up to `2κ` is allowed. So the
    sup/inf construction can produce a U-turn through one edge rather than a pass. For example,
    take `x = ¼ + κ/2`: then `X` may fall back to `¼` after `u`.
  * Hence "every point of `ℓ` in `R` lies on a pass" fails near the edges. "`R ∩ J = σ°`" is then
    unsupported, because edge U-turns of `ℓ((¾, a_m))` can enter `R`. The two-sides and
    frontier-point steps depend on it.
  * A minor slip as well: `N_o` must be chosen after `P_{m₂}`.
* **The repair.** The independent check rebuilt the trap in the column `3/8 ≤ X ≤ 5/8`, where the
  flow box holds, with a monotone-shadow property (Mon). It uses only lemmas the repository already
  has from the 1976 work, plus four small new ones. It does not need the cross-cut lemma, the
  decomposition `R ∖ σ = R_L ⊔ R_R`, or the claim `R ∩ J = σ°`. I checked it step by step.
  §2–§6 below are that repaired proof; your route and your two corrections to my sketch (U-turn
  pieces, the last time `s*`) are kept.
* Your ledger entries J75.1–J75.5 are adopted, with one change of wording (§9.1).

## 1. The plan

Formalize §2–§6 and close the arc step:
1. passes (§2);
2. the shadow lemma, the flow box and late thin passes (§3);
3. the region of a thin pass (§4);
4. the trapping lemma (§5);
5. the contradiction, `jones75_noArc : NoArcIndecHomPlane`, and with it
   `hagopian76_theorem1 : Hagopian76Thm1` and Bing 1960 for plane continua, unconditionally (§6).

If the whole does not fit, stop after §5 and report the obstruction.

## 2. Constants and passes

**Notation.**
* `κ = 1/32`. The *middle band* is `X ∈ [¼ + κ, ¾ − κ] = [9/32, 23/32]`. The column
  `[3/8, 5/8]` lies inside it.
* `η = ½`. Boxes `Q_η = F([¼, ¾] × [−η, η])`, open boxes `Q°_η`, left edges
  `L_η = F({¼} × [−η, η])` and right edges `Rt_η`.
* `F` is a collar of `γ = ℓ|[0,1]`, and `U = F((0, 1) × (−1, 1))` is open.
* `(X, Y)` are collar coordinates on `F([0, 1] × [−1, 1])`, and `o = ℓ(½) = F(½, 0)`.
* `F̄(x, y) = F(x, −y)` is again a collar (`IsCollar.flip`). It has the same passes, the same `X`
  and the same `|Y|`, so every constant below serves `F` and `F̄` alike.

**Passes** (skeleton `IsPass`).
* **(P1)** Distinct passes of `Q_η` have disjoint closed parameter intervals.
  * If `a < a′ < b`, then `ℓ(a′) ∈ L ∩ Q° = ∅`.
  * If `a′ = b`, then `ℓ(b) ∈ L ∩ Rt = ∅`.
  * If `a = a′` and `b < b′`, then `ℓ(b) ∈ Rt ∩ Q° = ∅`.
* **(P2)** Only finitely many passes meet `[−N, N]`. Those inside have length at least the
  uniform-continuity modulus for `d(L, Rt)`, and at most two straddle `±N`.
* **(P3)** `P₀ = ℓ[¼, ¾]` is a pass.
* **(P4)** Every other pass has its interior and both end points in `{Y > 0}`, or all of them in
  `{Y < 0}`. Each end point lies in the closure of the interior and has `Y ≠ 0`.
* **Nesting.** For `η′ ≤ η`, every pass of `Q_{η′}` is a pass of `Q_η`.

## 3. Shadow lemma and flow box

**(Mon)** (skeleton `PassMon`): for all `a ≤ v′ < v ≤ b`, `X(ℓ v) > X(ℓ v′) − 2κ`.
* *Order corollary.* On a pass with (Mon), if `X(ℓ v) = c`, `X(ℓ v′) = c′` and `c′ − c ≥ 2κ`, then
  `v < v′`.

**Shadow lemma** (`shadow_pass`).
* *Hypotheses.*
  * `0 < ε < ε₀`, where `ε₀` is the bound of (O).
  * Every point within `ε` of `γ(s)`, for `s ∈ [κ, 1 − κ]`, lies in `U` with `|X − s| < κ` and
    `|Y| < η′` (`uniform_near_compact`, once for `X`, once for `Y`).
  * `δ` is the Effros bound for `ε`.
* *Claim.* If `x ∈ [9/32, 23/32]` and `d(ℓ u, ℓ x) < δ`, then `u` lies in the open interval of a
  pass `[a, b]` of `Q_{η′}` with (Mon).

*Proof.*
1. Effros gives `h` with `h(ℓ x) = ℓ u` and displacement `< ε`. (O), applied to `ℓ(· + x)`, gives
   `h∘ℓ = ℓ∘ψ` with `ψ` strictly increasing, continuous and onto, and `ψ(x) = u`. Let `θ = ψ⁻¹`.
2. Put `s₁ = 3/16` and `s₂ = 13/16`. For `v ∈ [ψ s₁, ψ s₂]`, the point `ℓ(v) = h(γ(θ v))` lies in
   `U` with `|X(ℓ v) − θ v| < κ` and `|Y| < η′`. So `X < ¼` at `ψ s₁` and `X > ¾` at `ψ s₂`.
3. Put `a = max{v ∈ [ψ s₁, u] : X ≤ ¼}` and `b = min{v ∈ [u, ψ s₂] : X ≥ ¾}`.
4. *Interior.*
   * On `(a, u]`: `X > ¼`, and `X < θ v + κ ≤ x + κ ≤ ¾`.
   * On `[u, b)`: `X < ¾`, and `X > θ v − κ ≥ x − κ ≥ ¼`.
5. *End points.* `X(ℓ u) > ¼`, so `a < u` and `X(ℓ a) = ¼`; likewise `b > u` and `X(ℓ b) = ¾`.
   With `|Y| < η′`, `ℓ[a, b]` is a pass of `Q_{η′}`.
6. *(Mon).* For `v′ < v`: `X(ℓ v) > θ v − κ > θ v′ − κ > X(ℓ v′) − 2κ`.

**Two scales.**
* *Scale 1 (FB, `flow_box`).* Take `ε₁ < ε₀` with `η′ = η`, and its Effros `δ₁`. Take
  `η₂ ∈ (0, η)` with `d(F(x, y), F(x, 0)) < δ₁` for `x ∈ [¼, ¾]` and `|y| ≤ η₂`.
  * If `ℓ(u) ∈ F([9/32, 23/32] × [−η₂, η₂])`, then `u` lies in a pass of `Q_η` with (Mon): apply
    the shadow lemma at `x = X(ℓ u)`.
  * **(FB′)** By (P1), any pass of `Q_η` through such a point is that pass, and so has (Mon).
* *Thin passes.* A pass of `Q_η` is *thin* if it lies in `Q_{η₂}`. A thin pass meets `X = ½`, a
  middle-band point of `Q_{η₂}`, so every thin pass has (Mon).
* *Scale 2.* Take `ε₂ < ε₀` with `η′ = η₂/2`, and its Effros `δ₂`. If `d(ℓ u, o) < δ₂`, then `u`
  lies in a pass of `Q_{η₂/2}`. By nesting it is a pass of `Q_η`, it is thin, and by (P1) it is the
  pass of `Q_η` through `u`.

**Late thin passes** (`exists_late_thin_pass`). For every `T` there is a thin pass starting after
`T`.
* Let `T′` be the end of the pass containing `T`, if there is one, and `T′ = T` otherwise.
* Recurrence (`line_recurrent`, `mem_omegaLim_iff`) gives `u > T′` with `d(ℓ u, o) < δ₂`.
* If the thin pass `[a, b] ∋ u` had `a ≤ T`, it would contain `T`, so `b = T′ < u`, which is
  impossible.

**First thin pass.** By (P2), among the thin passes with `a > T` (optionally restricted to one side
of `P₀`) there is one with least `a`.

## 4. The region of a thin pass

Let `P_m = ℓ[a_m, b_m]` be a thin pass above `P₀` with `a_m > ¾`.
* `I_m = F⁻¹(P_m)` is an arc from `r = (¼, r₂)` to `s = (¾, s₂)` (N1). It satisfies
  `I_m ⊆ [¼, ¾] × (0, η₂]` and `I_m ∩ ({¼, ¾} × [0, η₂]) = {r, s}`.
* `rect_domain_aux` with `(a, b, c) = (¼, ¾, η₂)` gives an open, connected, bounded `D_m` with
  `D_m ⊆ (¼, ¾) × (0, η₂)` and
  `frontier D_m = I_m ∪ [¼, ¾] × {0} ∪ {¼} × [0, r₂] ∪ {¾} × [0, s₂]`.
  Put `R_m = F(D_m)`. This is the only use of `rect_domain_aux`, and its arc is the whole thin pass.
* *Low segments.* For `c ∈ (¼, ¾)`, let `w_m(c)` be the least height of a point of `I_m` over `c`
  (N2), and `τ_m(c) = {c} × (0, w_m(c))`.
* *Low strip.* Let `h_m > 0` be below every height of `I_m` (`exists_height_below`).

**(R1)** Let `P′ = ℓ[a′, b′]` be a pass other than `P₀` and `P_m` whose interior meets `R_m`. Then:
1. Its interior lies in `R_m`. By (P4) it lies in the upper rectangle. Its preimage is
   preconnected, meets `D_m`, and misses `I_m` (by (P1) and injectivity), the bottom and the sides;
   apply `conn_sub_of_frontier`.
2. `F⁻¹ℓ(a′) ∈ {¼} × (0, r₂)` (by N4 and the frontier formula; it is not a corner, since
   `a′ ∉ {¼, a_m}`). Likewise `F⁻¹ℓ(b′) ∈ {¾} × (0, s₂)`.
3. `P′ ⊆ F(cl D_m) ⊆ Q_{η₂}`, so `P′` is thin.

**(R2)** Under the conditions of (R1), the interior of `P′` meets `F(τ_m(c))` for every
`c ∈ (¼, ¾)`. This is `rect_domain_crosscut`, with the end points of (R1).2.

**(R3)** `τ_m(c) ⊆ D_m` (`seg_subset_rect_domain`), and `(¼, ¾) × (0, h_m) ⊆ D_m`
(`rect_domain_low`).

## 5. The trapping lemma

**Statement.**
* *Hypothesis (H):* no pass of `Q_η` with parameter interval inside `(¾, a_m)` has its interior in
  `R_m`.
* *Conclusion:* no pass with `a > b_m` has its interior in `R_m`.

**Lemma A.** No `v ∈ (¾, a_m)` has `ℓ(v) ∈ R_m` with `X(ℓ v) ∈ [9/32, 23/32]`.
* `R_m ⊆ Q_{η₂}`, so (FB) puts `v` in a pass `P′ ≠ P₀, P_m`.
* By (R1) its interior lies in `R_m`, and by (P1) its interval lies inside `(¾, a_m)`, which
  contradicts (H).

**Notation.**
* `w_L = w_m(3/8)`, `y_m = w_m(½)`, `w_R = w_m(5/8)`.
* `T_L = F(τ_m(3/8))`, `σ = F({½} × [0, y_m])`, `T_R = F(τ_m(5/8))`.
* `x_m = F(½, y_m) = ℓ(t_m)` and `z_R = F(5/8, w_R) = ℓ(t_R)`, with `t_m, t_R ∈ (a_m, b_m)`.

**Step 1: `t_m < t_R`.** `P_m` is thin, so it has (Mon). Since `5/8 − ½ ≥ 2κ`, the order
corollary gives `t_m < t_R`.

**Step 2: `J = σ ∪ ℓ[½, t_m]` is a Jordan curve.** We have `σ ∩ ℓ[½, t_m] = {o, x_m}`:
* `ℓ[½, ¾] = F([½, ¾] × {0})` meets `σ` only at `o`.
* `σ° ⊆ R_m` (R3), and Lemma A at `X = ½` excludes points of `ℓ((¾, a_m))` on `σ°`.
* Points of `P_m` on `X = ½` have height at least `y_m`, so `P_m ∩ σ = {x_m}`.

`jordan_curve_theorem` (through `tscc_homeomorph_circle`) gives `Jᶜ = W ⊔ W′`, open and connected,
with `frontier W = frontier W′ = J`.

**(J1)** For `v > t_m`: `ℓ(v) ∈ J` if and only if `ℓ(v) ∈ σ°` (injectivity).

**Step 3: four connected sets that miss `J`.** Put `h = h_m`,
* `B_L = F([3/8, ½) × (0, h))`,
* `B_R = F((½, 5/8] × (0, h))`,

together with `T_L` and `T_R`. All four lie in `R_m` by (R3). They miss `J`:
* they miss `σ`, because `X ≠ ½`;
* they miss `ℓ[½, ¾]`, because `Y > 0`;
* they miss `ℓ[a_m, t_m] ⊆ P_m`, because the boxes lie below `h` and the segments below the lowest
  points;
* they miss `ℓ((¾, a_m))` by Lemma A, since `X ∈ [3/8, 5/8]`.

`B_L` meets `T_L`, and `B_R` meets `T_R`. Let `W_L` be the component of `Jᶜ` containing `B_L ∪ T_L`,
and `W_R` the one containing `B_R ∪ T_R`. Edge U-turns may enter `R_m` near the edges and meet `J`;
the proof never uses `R_m ∩ J = σ°`.

**Step 4: `W_L ≠ W_R`** (N3).
1. Let `p = F(½, h/2) ∈ σ°`, and take a square `S` around `(½, h/2)` inside `[3/8, 5/8] × (0, h)`.
2. Then `F(S)` is open (`isOpen_collar_image`), and `F(S) ∖ J = F(S) ∖ σ ⊆ B_L ∪ B_R`.
3. `p` lies in the frontier of both components, so each meets `B_L ∪ B_R`. If `B_L` and `B_R` lay
   in the same component, the other would miss `B_L ∪ B_R`.

**Step 5: `z_R ∈ W_R`.** `t_R > t_m` and `X(z_R) ≠ ½`, so `z_R ∉ J` by (J1). Its component is open
and `z_R ∈ cl T_R`, so that component meets `T_R`.

**Step 6: the trap.** Suppose `P = ℓ[a, b]` has `a > b_m` and its interior in `R_m`.
1. By (R2) at `c = 3/8` there is `v_L ∈ (a, b)` with `ℓ(v_L) ∈ T_L ⊆ W_L`.
2. The path `ℓ[t_R, v_L]` joins `W_R` to `W_L`, so it meets `J`.
   * Let `s*` be the largest `v ∈ [t_R, v_L]` with `ℓ(v) ∈ J`. Then `s* ∈ (t_R, v_L)`.
   * By (J1), `ℓ(s*) ∈ σ°`.
   * `ℓ((s*, v_L])` is connected, misses `J` and meets `W_L`, so it lies in `W_L`.
3. `s* > b_m`, because `ℓ((t_m, b_m])` misses `σ`.
4. By (FB) at `X = ½`, `s*` lies in the open interval of a pass `P* = ℓ[a*, b*]` with (Mon). By
   (R1) its interior lies in `R_m`, and by (P1) `a* > b_m`.
5. `s* < a`. Otherwise `s* ∈ (a, v_L)`, so `P* = P`. Then (Mon) for `P` would put its point on
   `X = 3/8` after its point on `X = ½`, which the order corollary forbids. So `P* ≠ P` and
   `b* < a`.
6. By (R2) at `c = 5/8` there is `v_R ∈ (a*, b*)` with `ℓ(v_R) ∈ T_R ⊆ W_R`.
   * (Mon) for `P*` gives `v_R > s*`.
   * So `v_R ∈ (s*, v_L)` and `ℓ(v_R) ∈ W_L`, which contradicts Step 4. ∎

## 6. The contradiction, and the Theorem

**C1. The first thin pass.**
* Let `P_{m₁} = ℓ[a₁, b₁]` be the first thin pass with `a > ¾`.
* Without loss of generality it lies above `P₀`; otherwise use `F̄`.
* (H) holds for `R₁ = R_{m₁}`: a violating pass is thin (R1.3) and starts in `(¾, a₁)`. So the
  trap applies to `R₁`.

**C2. Choices from `P_{m₁}`.** Take `h₁ = h_{m₁}` and `ρ₁` with
`B(o, ρ₁) ⊆ F((3/8, 5/8) × (−h₁, h₁))`. Recurrence gives `u₁ > b₁` with
`d(ℓ u₁, o) < min(δ₂, ρ₁)`.

**C3. A thin pass below.** Write `ℓ(u₁) = F(x, y)`.
* `y = 0` would give `u₁ = x < b₁`, by injectivity.
* `y > 0` would put `ℓ(u₁) ∈ R₁` (`rect_domain_low`) on a thin pass whose interior lies in `R₁`
  (scale 2, (R1)) and which starts after `b₁` (P1). This contradicts C1.
* So `y < 0`, and some thin pass below `P₀` starts after `b₁`. Let `P_{m₂} = ℓ[a₂, b₂]` be the
  first.

**C4. The trap for `P_{m₂}`** (use `F̄`). A violating pass in `R₂` is thin and below `P₀`. By (P1)
its start avoids `[a₁, b₁]`. Before `a₁` contradicts the minimality of `m₁`, and in `(b₁, a₂)` the
minimality of `m₂`.

**C5. Choices after `P_{m₂}`.**
* Take `h = min(h₁, h₂)`, and `ρ` with `B(o, ρ) ⊆ F((3/8, 5/8) × (−h, h))`.
* Recurrence gives `u > b₂` with `d(ℓ u, o) < min(δ₂, ρ)`.
* `Y = 0` is excluded by injectivity. `Y > 0` puts `ℓ(u)` in `R₁` on a thin pass after `b₁`
  (C1). `Y < 0` puts it in `R₂` on a thin pass after `b₂` (C4).

This is a contradiction. ∎

**The Theorem.**
* `jones75_noArc : NoArcIndecHomPlane`. The bridge from `α ≃ₜ unitInterval` to a `TArc` in `M` is
  routine; then `jonesSetting_of_plane`, `exists_line`, `exists_collar`, and §2–§6.
* `hagopian76_theorem1 : Hagopian76Thm1 := hagopian76_theorem1_jones jones75_noArc`.
* `bing60_plane_uncond` and `hagopian76_theorem2_uncond`: the existing conditional theorems with
  `hagopian76_theorem1` supplied. List any other theorem whose only open hypothesis was
  `Hagopian76Thm1`, and add its unconditional form if it is short.

## 7. Lemmas used

**Planar lemmas in the repository:**
* `jordan_curve_theorem` (`Jones55T2A.lean`), via `tscc_homeomorph_circle`;
* `rect_domain_aux` and `rect_domain_low` (`H76Domain.lean`);
* `seg_subset_rect_domain` (`H76PairSep.lean`);
* `rect_domain_crosscut` (`H76Crosscut.lean`);
* `conn_sub_of_frontier` and `TArc.exists_sub` (`Sec6Arc.lean`);
* `exists_height_below` (`H76T7.lean`);
* `IsCollar.flip` and `tarc_vseg` (`H76Adapt.lean`);
* `isOpen_collar_image` and `collar_injOn` (`H76Translate.lean`);
* `isCompact_collar_image` (`H76Descent.lean`).

**Non-planar:**
* `uniform_near_compact` (`Jones75L.lean`);
* `effros_homogeneous`;
* `JonesSetting.orientation`;
* `line_recurrent` and `mem_omegaLim_iff`;
* `exists_line`, `jonesSetting_of_plane` and `exists_collar`.

**New, all small:**
* **N1 (collar preimage of an arc).** If `IsCollar γ F`, `TArc p q A` and `A ⊆ F '' K` (`K` the
  closed rectangle), then there is `I ⊆ K` with `TArc (F⁻¹p) (F⁻¹q) I` and `F '' I = A`.
* **N2 (lowest point on a vertical).** If `TArc r s I`, `I ⊆ [a, b] × (0, c]`, `r.1 = a`, `s.1 = b`
  and `x₀ ∈ (a, b)`, then there is `w₂ > 0` with `(x₀, w₂) ∈ I` and
  `Disjoint ({x₀} × (0, w₂)) I`. Use the intermediate value theorem and compactness. A version may
  exist inside `rect_domain_crossing_separates`.
* **N3 (two sides at a point of `J`).** If `frontier W = frontier W′ = J`, `p ∈ J`, `N` is open with
  `p ∈ N`, `N ∖ J ⊆ A ∪ B` and `A ∪ B ⊆ W`, then `False`.
* **N4 (end points).** If `S ⊆ K` and `z ∈ closure (F '' S)`, then `F⁻¹ z ∈ closure S`.

**No longer needed:** the general cross-cut lemma `crosscut_split`, the θ lemmas, Schoenflies, and
`rect_domain_crosscut_arc`.

## 8. Order

§2, §3, then N1–N4, §4, §5, §6. §2–§3 do not depend on the planar lemmas.

## 9. Places to check (ledger)

1. **J75.4, wording.** Your entry calls the step "This makes `h` take `[t₀, t_d]` onto
   (approximately) `[t_d, t₀]`" false. The hypotheses of the Theorem are never satisfied, so I would
   rather say: the step is unargued, and under the hypotheses of the setting it contradicts (O),
   so any argument for it would itself finish the proof. Adopt that wording, or argue for yours.
2. **Report 189 §6.3.** Record in `LEDGER.md` and `doc/notes/jones75.md` that its shadow lemma and
   flow box hold only in the middle band, and that the trap was rebuilt (§0 above).
3. **The route.** Record in `doc/notes/jones75.md` which steps of Jones's Theorem the route of
   §2–§6 replaces: accessibility, (e), the choice of `η`, `[t_a, t_b]`, `[t_c, t_d]`, the fixed
   point, the domains `Dᵢ`, and the final limit argument.

## 10. Deliverables

1. **The items of §2–§6.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch190.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** a subsection "Jones 1975 II (batch 190)", with the printed sentences quoted.
3. **Notes:** `doc/notes/jones75.md` (§9.2, §9.3).
4. **Publish the changes, as in batch 189.** At the end of the run:
   * create `doc/batches/batch190-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch190-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `Hagopian76Thm1`, with every open input marked (if §6 is proved, there
     should be none);
   * a short survey of what Part E now gives the classification: the verified statements about
     homogeneous plane continua, with their named hypotheses, if any.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
