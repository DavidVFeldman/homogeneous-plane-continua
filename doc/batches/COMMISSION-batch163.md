# Commission: batch 163 — Part E, Hagopian 1976 VIII: the collar geometry (Lemma 9's argument made general; Lemma 9; T3, T6)

**Go!** This batch runs on top of the batch-162 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch163.md`: this text, also pasted into the prompt.
* `Hagopian76H.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76H.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76H` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 VIII (batch 163)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

## 0. On batch 162

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1572 lines, with `sorryAx` in none, all on the standard three axioms.

**Accepted.**
* **Lemma 7**, by the route of commission 162 §1, and **`halfray_dense`**. Your argument for it
  through pieces and `extUnion_eq_of_subset` is accepted. My sentence ("both are composants … they
  share `E′`") was not an argument, as you say. The ledger records Hagopian's sentence as unargued
  and true, and `Lemma7F` as too strong and not needed.
* **`halfray_inter`.**
* **Property 2** (`hagopian76_property2`), unprompted.

**This batch is the collar geometry and nothing else.** It has been carried over twice. The
commission gives a complete route below, and the work is to formalize it.

## 1. The route: Lemma 9's argument, run for any point just below `π[E]`

Read Lemma 9's proof (pp. 344–345) once more. Its contradiction does not need the point `πh(u)` to lie
on the vertical segment `A`. It needs only that `h(u)` is a point of `M − E` lying in `L₂`, just
below `π[E]`, on the far side of `π[I]` from `G₃`. So the argument proves the stronger statement
`no_M_below`. That statement gives Lemma 9 (the vertical over `u` is then free), and it also gives
T3 and T6 ("no point of `π[M]` lies between `I₁` and `⟨p₁, p₅⟩`").

The argument also needs no Theorem 28. An open rectangle of the collar, with a Jordan-curve-free
boundary-bumping argument, does the job. Here it is for `[a, b]` to the left of `y`; the right side
is the mirror image, with the roles of `X` and `Z` exchanged.

**Set-up.**
* Take a collar `F` of `γ` in which the vertical `V_y = F({y} × [−c₀, 0))` misses `π[M]`
  (hypothesis `hvert`). Since layers are `π`-fibres, `π⁻¹[V_y] ∩ M = ∅`.
* Fix `a′ ∈ [a, b]` and write `U = k⁻¹(a′)`.
* Choose `0 < α < a′ < β < y < ζ < 1` (abscissae) and form three collar rectangles:
  * `R₁ = F([0, β₁) × (−c₁, c₁))` around the left part, with `α < β₁ < a′`;
  * `R₂ = F((α, ζ₂) × (−c, c))` around the middle, with `y < ζ₂ < ζ`;
  * `R₃ = F((ζ₃, 1] × (−c₃, c₃))` around the right part, with `y < ζ₃ < ζ₂`. Then `Cl R₃` lies at
    abscissae `> y`.
* Take `c < c₁` and `c ≤ c₀`. Put `Gᵢ = π⁻¹[Rᵢ]`. Use the half-open rectangles at the ends so that
  the end layers are covered.
* `G = {G₁, G₂, G₃}` is a plane chain that follows `E`. Everything is in the parameter: `π` sends
  the layer `k⁻¹(t)` to `γ(t) = F(t, 0)`.
* Its links are within any prescribed `ε` of `H₁ = k⁻¹[[0, β₁]]`, `H₂ = k⁻¹[[α, ζ₂]]` and
  `H₃ = k⁻¹[[ζ₃, 1]]` once the heights are small (`layer_nbhd_small`). Choose `ε` as Hagopian
  does: one third of the minimum of `ρ(C, H₃)`, `ρ(D, H₁)`, `ρ(H₂, k⁻¹(0) ∪ k⁻¹(1))`, and the
  distance from `H₁ ∪ H₃` to `π⁻¹[V_y]`. Here `C = k⁻¹[[0, y]]` and `D = k⁻¹[[a′, 1]]`.
* Lemma 8 with caps (`lemma8_caps_sep`) gives the free refinement `L` with `L₂ = C′ ∩ G₂`, where `C′`
  is Lemma 8's open set containing `E`.

**The region.** `O = F((0, y) × (−c, 0))`. It is open because the collar maps the open rectangle onto
an open set. Its boundary in the plane is the image of the boundary of the rectangle, and consists of:
* top: `γ([0, y]) = π[C]`;
* right: `V_y`, together with its foot `γ(y)`;
* left: `F({0} × [−c, 0])`, which lies in `R₁`;
* bottom: `F([0, y] × {−c})`. The part with abscissa `< β₁` lies in `R₁`. The part with abscissa in
  `[β₁, y]` lies outside `R₁ ∪ R₂ ∪ R₃`, so outside `St G ⊇ St L`.

**The contradiction.** Suppose a point `z ∈ M` has `π(z) ∈ F([a, b] × [−c, 0))`, with `c` small.
1. Then `z ∉ E`, since `π[E]` is the axis. Also `z ∈ L₂`: points near `U` lie in `C′ ∩ G₂`, by upper
   semicontinuity, because `C′` is an open set containing `E`.
2. By Lemma 2 (the union over `x ∈ U` of the open sets of `hagopian76_lemma2` is a neighbourhood of
   `U`), there are `u ∈ U` and an `ε`-homeomorphism `h` with `h(u) = z`.
3. **"Since `M` is atriodic and `h(u)` is not in `E`, the sets `G₂ ∩ E` and `G₂ ∩ h[E]` are
   disjoint."** This is unargued in Hagopian. Prove it by the 1975 ¶9 triod
   (`subset_of_meets_avoids`) or `three_continua`. Both `E` and `h[E]` follow `G`, and `h(u) ∈ G₂ − E`.
4. Hence the continuum `h[D]` contains `z`, meets `G₃` (it contains `h[k⁻¹(1)]`), and misses:
   * `C`, by step 3 and `ρ`;
   * `π⁻¹[V_y]`, since the latter misses `M`;
   * `Cl G₁`, by `ρ(D, H₁)`.

   Note that `π⁻¹π[C] = C`, because `C` is a union of layers.
5. Let `Q` be the component of `h[D] ∩ π⁻¹[Cl O]` containing `z`. Since `h[D]` meets `G₃`, which lies
   outside `π⁻¹[Cl O]`, boundary bumping gives a point `w ∈ Q` with `π(w)` on the boundary of `O`.
6. By step 4, `π(w)` is on the bottom side, at abscissa `≥ β₁`, so `w ∉ St L`.
7. `Q` is a connected subset of `M` from `z ∈ St L` to `w ∉ St L`, so it meets `M ∩ Bd(St L)`. By
   freeness that point lies in `Bd(L₁ ∪ L₃) ⊆ Cl G₁ ∪ Cl G₃`. But `Q` misses `Cl G₁` (step 4) and
   `Cl G₃` (`π⁻¹[Cl O]` and `Cl G₃` are disjoint, by abscissa). Contradiction.

Compactness over `a′ ∈ [a, b]`, with finitely many `a′` and the minimum of the `c`'s, gives
`no_M_below`.

**Check each step.** If one fails, say which and why. If the statement `no_M_below` is stronger than
the argument gives, weaken it and record the change.

## 2. Items

**A. `exists_collar_adapted`.** A collar of `γ` in which a given arc `β`, ending at the interior
point `γ y` and meeting `range γ` only there, contains the vertical below `γ y`. Use
`plane_schoenflies₂`, with one side on `γ` and the adjacent side on `β`, in the construction of
`exists_collar` (`exists_collar_aux`).

**B. `no_M_below`** (§1). Also state the mirror image for `[a, b]` to the right of `y`. Its statement
is the same; the hypothesis `hy : y ∉ [a, b]` covers both sides.

**C. `hagopian76_lemma9`.** Take the arc `I` from `hacc` (`IsAccessibleFrom`). Then:
* `π` is injective on `I`, since `I` meets `E` only at its end, so `π[I]` is an arc ending at `γ y`;
* `π[I] ∩ π[M] = {γ y}`;
* item A gives the collar, with `hvert`;
* item B, on a small interval about `u`, gives the vertical over `u`;
* the side is `σ = −1` for both.

**D. `hagopian76_T6`.** Hagopian's `⟨p₁, p₅⟩` is at abscissae `3/22 … 19/22`. Choose the
parametrization so that the accessible layer is outside it. `exists_accessible_typeA'` gives a point
in some interior layer, and a homeomorphism of `[0, 1]` moves it. Record the change.

If all of A–D are done, go on to T7 ("I₂ above"). It is the same core argument on the other side of
`π[E]`, for `h[E]`, using an accessible point of `M ∩ L₆` above `π[E]` (p. 346).

## 3. Places to check (candidate ledger entries)

1. **p. 344:** "Since `M` is atriodic and `h(u)` is not in `E`, the sets `G₂ ∩ E` and `G₂ ∩ h[E]` are
   disjoint." This is unargued.
2. **p. 345:** "Since `L` is free relative to `M` and `π[C ∪ I] ∩ π[Cl G₃] = ∅`, this is impossible
   [13, Theorem 28, p. 156]." Record the replacement: the collar rectangle with boundary bumping and
   freeness, without Theorem 28. Record whether Hagopian's Theorem 28 route is also valid as printed.
3. **p. 344:** the chain `G` with "`π[Gᵢ]` an open disk" and "`π[Gᵢ] ∩ π[Gᵢ₊₁]` an open disk". Collar
   rectangles satisfy both.
4. **p. 345, Lemma 9's hypothesis** "Assume `U` and `Y` are not decomposably accessible from a side of
   `E`". The general argument does not use it. Record that Lemma 9 holds in a stronger form.
5. **p. 345, T3 and p. 346, T6:** "each point of `π[E]` is an end point of an arc segment … below"
   and "It follows from the proof of Lemma 9 …". Both follow from `no_M_below`.

## 4. Deliverables

1. Items A–D, and T7 if reached.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch163.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
