# Commission: batch 174 — Part E, Hagopian 1976 XIX: Theorem 1 — "`I` is finite"; the end element; pockets; T15–T17

**Go!** This batch runs on top of the batch-173 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch174.md`: this text, also pasted into the prompt.
* `Hagopian76S.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76S.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76S` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XIX (batch 174)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 173

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1838 lines, with `sorryAx` in none, all on standard axioms.

**Property 3 is verified.** Your three changes to the route are improvements:
* the closed condition `LayerCrossing`, with the axis allowed and excluded afterwards;
* one middle point;
* a ball in place of `ρ₀`.

The margin problem of batches 170–172 is gone. `crossing_length_pos` is also accepted.

## 1. "`I` is finite": a route

Let `C` be a crossing component of `F ∩ π⁻¹[D]` with irreducible interval `[x, y] ∈ I`.

1. **`d[Cl C] = [x, y]`.** `d[Cl C]` is a closed interval, since `Cl C` is a continuum and `d` is
   continuous. It contains `d[C]`. Minimality of `[x, y]` forces it to equal `[x, y]`.
2. **`Cl C ⊇ d⁻¹((x, y))`**, whole layers. `Cl C` is a subcontinuum of `F` meeting `d⁻¹(x)` and
   `d⁻¹(y)`, so `layerSet_Ioo_subset` applies.
3. **`C` meets every nonempty open set `d⁻¹(J)` with `J ⊆ (x, y)` open.** `d[C]` is dense in
   `d[Cl C] = [x, y]`, and `d⁻¹(J)` is open in `F`. Check that `d[C]` is dense: `C` is dense in
   `Cl C`, and `d` is continuous.
4. **Distinct intervals of `I` have disjoint interiors.** Let `[x₁, y₁]` and `[x₂, y₂]` come from
   `C₁ ≠ C₂`, with `J = (x₁, y₁) ∩ (x₂, y₂) ≠ ∅`.
   * By 3, `C₁` has a point `z ∈ d⁻¹(J)`.
   * By 2, `z ∈ Cl C₂`.
   * `z ∈ π⁻¹[D]`, which is open, and a component of the relatively open set `F ∩ π⁻¹[D]` is closed
     in it. So `z ∈ C₂`, and `C₁ = C₂`.
   * So the map from crossing components to intervals is injective, and the interiors are disjoint.
5. **Below any `v₀ < 1`,** each interval has length `≥ λ` (`crossing_length_pos`). Disjoint
   interiors then give at most `1/λ + 1` intervals with `y ≤ v₀`.
6. **The end element.** It remains to exclude infinitely many intervals accumulating at `1`. By
   Lemma 4, `F` has a proper extension `F′` away from `k⁻¹(0)`. By the strong form, the layers of `F`
   are layers of `F′`, and `F = d′⁻¹[[0, s′]]` with `s′ < 1`.
   * Crossing components of `F ∩ π⁻¹[D]` are connected subsets of `F′ ∩ π⁻¹[D]`, each in a
     crossing component of `F′`. Check whether they can merge in `F′`: if so, count components of
     `F′` instead, or argue directly.
   * Alternatively: if intervals of `I` accumulate at `1`, a hyperspace limit of their closures gives
     a layer crossing in `d⁻¹(1) = d′⁻¹(s′)`, an interior layer of `F′`. This contradicts
     `hagopian76_property3` for `F′`.
   * **This also covers the end element that report 173 §1.A left out:** Property 3 for `d⁻¹(1)`
     follows from Property 3 for `F′`.

So "It follows from Property 3 that `I` is finite" is true. The argument uses Property 3 (through
the length bound and the end element), together with steps 1–4, which the paper does not state.

## 2. Items

**A. `hagopian76_property3_end_element`** (§1.6): Property 3 for `d⁻¹(1)`, via a proper extension.

**B. `hagopian76_I_finite`** (§1). Define Hagopian's `I` (the shape proposed in report 173 §5).
Prove that distinct members have disjoint interiors, then finiteness.

**C. `J` and the `xᵢ`** (p. 347–348): "Let `e` be the point of `[0, 1]` such that
`d⁻¹[[0, e]] = E`. Let `J = I ∪ {[0, e]}`. Define `{xᵢ : 1 ≤ i ≤ 2n}` to be the finite increasing
sequence in `[0, 1]` such that `St J = ⋃{[x₂ᵢ₋₁, x₂ᵢ] : i ≤ n}`. Note that `x₁ = 0`, `x₂ = e`, and
`x₂ₙ = 1`." Check each "Note that":
* `x₂ = e` needs `[0, e]` disjoint from the intervals of `I`. Crossing components miss `E`, so each
  `x ≥ e`. Is `x > e` needed, and true?
* `x₂ₙ = 1` needs the last interval of `I` to end at `1`. Why is that? It should follow from the
  irreducibility of `F` with respect to separating `p` from `f(p)` (T13): the last part of `F` must
  cross `D`. Check it.

**D. Property 4 and its base case** (p. 348): "There exists a point `yₙ` of `K` such that (1) the
closure of the `yₙ`-component `Cₙ` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (2)
`d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates `yₙ` from `f(yₙ)` in `π⁻¹[D]`." Also "Note that `[x₁, x₂]` does not
have Property 4." Report 170 §1.E reduced the base case to the connectedness of `π⁻¹[D]`, which
`hagopian76_D` gives (`D` connected, `π` injective over `D`). The step from T13 to Property 4 for
`[x₂ₙ₋₁, x₂ₙ]` ("only the last block separates", unargued) uses the irreducibility of `F`: drop
blocks one at a time.

**E. The induction** (pp. 348–349, Cases 1 and 2), "Following Bing [2, p. 225]". Formalize as far as
it goes. Two points are still open:
* the pockets in "either above or below";
* "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`".

For both, first state precisely what the induction uses, then try:
* **Pockets.** The layer structure from §1.2 may help. A crossing closure `Cl Cᵢ₋₁` contains whole
  layers `d⁻¹((x, y))`, and the swallowing lemma relates those layers to translates. A pocket
  bounded by `Cl Cᵢ₋₁` and a side segment has a boundary strand in `Cl Cᵢ₋₁`. Is that strand a union
  of layers of `F` with parameters that leave and re-enter the side? Coarse monotonicity
  (`IsEps1.sep_of_gap`) bounds how far such a strand reaches from the side, if the strand is a
  translate of a short piece. State what you find.
* **`N`.** `N` lies in an extension of `Cl Cᵢ` from `yᵢ` to `yᵢ₋₁`. If `N` were within `ε₂` of
  `π⁻¹(p₄)`, then by Property 2 `N` would be "long". Read Hagopian's sentence and the role of `ε₂`
  in it; the definition of `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` suggests the point is that `N` cannot pass
  `I₁` or `I₂`.

**F. The assembly**, `hagopian76_theorem1`, unconditionally if A–E close; otherwise with named
`Prop`s for exactly the steps left open.

## 3. Order

A, B, C, D, E, F.

## 4. Places to check (candidate ledger entries)

1. **p. 347:** "It follows from Property 3 that `I` is finite."
2. **p. 347–348:** "Note that `x₁ = 0`, `x₂ = e`, and `x₂ₙ = 1`."
3. **p. 348:** Property 4; "Note that `[x₁, x₂]` does not have Property 4"; "we now show that if `I`
   has Property 4, then so does `J`".
4. **pp. 348–349:** Cases 1 and 2, each "Hence" and "Note that".
5. **Property 3 at the end element** (§1.6).

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch174.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s are `def … : Prop`, listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
