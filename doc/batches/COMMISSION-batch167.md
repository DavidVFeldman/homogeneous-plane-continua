# Commission: batch 167 — Part E, Hagopian 1976 XII: Theorem 1 — crossing translates; the `p`-components; T12, Property 3, T13; then T15–T17

**Go!** This batch runs on top of the batch-166 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch167.md`: this text, also pasted into the prompt.
* `Hagopian76L.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76L.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76L` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XII (batch 167)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines.** As before: a `STATUS:` line in your trace when an item is proved, left open, or
stuck; `STATUS: need help` with the obstruction in one sentence when a hint would help.

**Build provenance.** No need to report it again unless it changes.

## 0. On batch 166

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1704 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `rect_domain`, `hagopian76_D`, `hagopian76_K0`, and `hagopian76_K0_crosscut` (unprompted).
* `exists_two_composants_in_open`.
* Your answer on "inaccessible": it is not used after `p` and `q` are chosen.

**On item C (your §1.C).** You are right that step 2 fails as I stated it.
* Your `sin(1/x)` example, however, cannot occur here. Its decomposition is not lower
  semicontinuous: the arc points converge only to `t₀`, not to all of `T`. In our setting every
  minimal admissible map has lower semicontinuous layers (`lsc_of_minimalAdmissible`, from Lemma 5).
  So `k⁻¹(u) ⊆ Cl k⁻¹[[0, u)]` for `u > 0`, and the same for the other side. This is your first
  repair.
* Lower semicontinuity still does not give a *connected* continuation inside `π⁻¹[D]`, so step 2
  remains open in general.
* **This batch does not need it.** Hagopian applies "follows `Cl B`" only to components through
  points `p = h(x)` with `h` small (T12), and through points `yᵢ ∈ K` (T17). For such components the
  crossing comes from the translate `h[E]`, below.

## 1. The route: crossing translates

Notation:
* `hagopian76_D` over `[3/22, 19/22]`, with `D = F[D′]` and the low strip
  `F[(3/22, 19/22) × (0, c₀)] ⊆ D` (`rect_domain_low`);
* `K₀` over `11/22`, from `hagopian76_K0`.
Fix `0 < a′ < 3/22` and `19/22 < b′ < 1`.

**Lemma T (`crossing_translate`).** For every `ζ > 0` there is `δ > 0` with the following property.
Let `x ∈ E` with `k(x) ∈ [3/22 + ζ, 19/22 − ζ]`, and let `h` be a `δ`-homeomorphism of `M` with
`h(x) ∉ E` and `π(h(x))` above the axis. Put `Q = h[k⁻¹[[a′, b′]]]`. Then:
1. **`Q ∩ E = ∅`.** `Q` is a continuum. For `δ` small it misses `k⁻¹(0)` and `k⁻¹(1)`. If it met
   `E`, it would lie in `E` by `hagopian76_no_hair`; but `h(x) ∈ Q − E`.
2. **`π[Q]` lies in the open collar band above the axis, below height `c₀`.**
   * For `δ` small, `Q` is near `k⁻¹[[a′, b′]]`. By `pi_thin_near_layer`, or by continuity of `π`
     and compactness, `π[Q]` is near `γ([a′, b′])`, inside `F[(0, 1) × (−c₀, c₀)]`.
   * `π[Q]` is connected and misses the axis, by step 1. So it lies on one side of the axis, the
     side containing `π(h(x))`: the upper side.
3. **Layer by layer.** For `t ∈ [a′, b′]`, `π[h[k⁻¹(t)]]` lies within any prescribed distance of
   `γ(t)`, for `δ` small (uniform in `t`).
   * Layers with `t ≤ 3/22 − ζ/2` lie left of the left edge.
   * Layers with `t ≥ 19/22 + ζ/2` lie right of the right edge.
   * Layers with `t ∈ [3/22 + ζ/2, 19/22 − ζ/2]` lie entirely in the low strip, hence in `D`.
4. **The `h(x)`-component crosses.** Let `C` be the component of `M ∩ π⁻¹[D]` containing `h(x)`.
   * `C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`, which is a connected subset of `π⁻¹[D]` containing
     `h(x)`.
   * `Z = h[k⁻¹[[a′, 3/22 + ζ/2]]]` is a continuum not contained in `π⁻¹[D]`. By boundary bumping
     (components of an open subset of a continuum), the component of `Z ∩ π⁻¹[D]` containing the
     layer `h[k⁻¹(3/22 + ζ/2)]` has closure meeting `π⁻¹[Fr D]`.
   * `Z` misses `E` and `π⁻¹[I₂]`. It lies at abscissae `< 19/22`, so it cannot reach the right
     edge. So that closure meets `π⁻¹` of the left edge. The same holds on the right.
   * Hence `Cl C` meets both side preimages: `C` is **crossing**.
   * `Cl C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`, so `L − {L₁, L₁₁}` follows it, in the sense
     T12 and T17 use (Property 1's `h[piece (j + 1)] ⊆ L j`, for `h` small).

**Lemma T′ (`K0_dense_low`).** Points of `M ∩ K₀` occur at every small height.
* Take `x₀ ∈ k⁻¹(11/22)` and points `y ∈ M − E` above, near `x₀` (`M_meets_above`).
* Lemma 2 gives a small `h` with `h(x₀) = y`.
* `π[h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]]` is a connected subset of the low strip, spanning
  abscissae across `11/22`. So it meets the vertical over `11/22` below `w`, at height
  `→ 0` as `h → id`.
* So there are points `zₙ ∈ M ∩ K₀` with `π(zₙ) → p₃`. By upper semicontinuity, a subsequence
  converges to a point `x ∈ k⁻¹(11/22)`.
* **Take Hagopian's `x` to be such a limit.** Then `x ∈ Cl(M ∩ K₀) ∩ k⁻¹(p₃) ⊆ Cl K ∩ π⁻¹(p₃)`, as
  T12 requires, and every neighbourhood `W` of `x` meets `M ∩ K₀`. This is your repair (report 166
  §1.E), done.

## 2. Items

**A.** `crossing_translate` (Lemma T) and `K0_dense_low` (Lemma T′). Check every step; if one fails,
say which and why.

**B. T12.** With `x` from Lemma T′ and `W` the Lemma 2 neighbourhood of `x` for `ε₃/2`:
* By Lemma T, every `p ∈ M ∩ K₀ ∩ W` with `p = h(x)` has a crossing `p`-component `C`. Hagopian's
  (2), "the closure of the `p`-component `C` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`", follows
  from `Cl C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]` and T9.
* **`p`, `q` off `R(E)`, in distinct composants of `Cl R(E)`.** First settle whether
  `Cl R(E) = M`.
  * If it is, `exists_two_composants_in_open` applied to `W` is not enough, because the points must
    lie on `K₀`.
  * Lemma T′ gives many points of `M ∩ K₀ ∩ W`, one for each small `h`. Show that they are not
    covered by two composants. I have no argument for this. A composant is a countable union of
    proper subcontinua, each nowhere dense in `M`, but its trace on the arc `K₀` need not be small
    in `K₀`. One approach: the crossing components through these points are pairwise disjoint or
    equal, and a single composant contains only countably many of them that are disjoint and
    crossing. Check this before using it.
  * If `Cl R(E) ≠ M`, say what changes. `p` and `q` must then lie in `Cl R(E)`; use pieces of the
    line `R(E)` near `x`. (`R(E)` is dense in `Cl R(E)`, and `E` is nowhere dense in it.)
* **"By Property 1, `R(E)` intersects an arc in `K` that is irreducible between `C` and the
  `q`-component of `M ∩ π⁻¹[D]`, and `R(E)` separates these components in `π⁻¹[D]`."**
  * Apply Lemma T to extensions inside `R(E)` (translates `h[E] ⊆ R(E)` are not available, but
    crossing pieces of `R(E)` near `E` are: a sub-arc of the line `R(E)` close to `E` and
    disjoint from `E`).
  * Order crossing continua along `K₀` by height. Two disjoint crossing continua cut `D` into an
    upper, a middle and a lower part (`hagopian76_K0_crosscut`, applied twice, or the Jordan curve
    theorem on the strip between them).
  * If this needs choosing `q` on the correct side of `C`, choose it so, and record it.

**C. Property 3.** Take the shape of report 166 §5, "crossing" with your margin (§1.D there),
accepted. Two pieces:
* `crossing_set_closed`, the hyperspace limit (attainment of the least `v`). The limit continuum
  `Z ⊆ d⁻¹(v)` misses `E` and `π⁻¹[I₂]` and meets both side preimages. To get a component reaching
  **both** sides, apply `hagopian76_K0_crosscut` to `Z`, or bypass the component: Property 3 can
  be stated for crossing *continua* `Z ⊆ M ∩ π⁻¹[Cl D] − E` instead of components. Say which
  form T15–T17 need.
* The shift under `g`, with the margin.

**D. T13**, with "The existence of such a continuum `F` follows from Property 1 and the fact that
`Cl R(E) = Cl R(k⁻¹(0), E)` (Lemma 6 (proof))".

**E. T15–T17 and `hagopian76_theorem1`**, if reached. For T17's "`L − {L₁, L₁₁}` follows
`Cl Cᵢ₋₁`", use Lemma T in the same way as for `C` in T12. Say whether `yᵢ₋₁` is of the form
`h(x)` with `h` small; if it is not, state what is missing.

**F. Item C of batch 166 in general** ("follows `Cl B`" for every component through `K₀`): optional,
and only if A–E leave time. Use the lower semicontinuity of the layers.

## 3. Order

A, B, C, D, E, F.

## 4. Places to check (candidate ledger entries)

1. **p. 346, T9:** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`". Record its status for the
   components T12 and T17 use, and in general.
2. **p. 347, T12:** "To see this let `x` be a point of `k⁻¹(p₃) ∩ Cl K`"; the choice of `p`, `q`;
   "By Property 1, `R(E)` intersects an arc in `K` …".
3. **p. 347, Property 3:** the three sentences of batch 166.
4. **p. 347, T13:** the existence sentence.
5. **pp. 347–349, T15–T17**, if reached: "It follows from Property 3 that `I` is finite"; Property 4;
   "Following Bing [2, p. 225]".
6. **Whether `Cl R(E) = M`.** Hagopian treats `Cl R(E)` as a possibly proper subcontinuum
   ("composants of the indecomposable continuum `Cl R(E)`").

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch167.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if E is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
