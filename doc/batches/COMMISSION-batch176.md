# Commission: batch 176 — Part E, Hagopian 1976 XXI: Theorem 1 — the cutting step; positions by `ε₃`; Property 4; the induction

**Go!** This batch runs on top of the batch-175 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch176.md`: this text, also pasted into the prompt.
* `Hagopian76U.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76U.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76U` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXI (batch 176)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 175

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1880 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `component_over_middle_crossing`, by the bumping shortcut, with both shape changes: the exception
  for `d⁻¹(1)`, and the middle `[3/8, 5/8]`.
* `cover_pocket_middle` and `hagopian76_tail_middle`.
* `hagopian76_x2n_eq_one_of_cut`, with `TailCutKeepsSep` as the named hypothesis.

## 1. Notes

**A. The positions the induction needs are near abscissa `1/2`, not anywhere in `L₆`.** Hagopian
writes "`f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`", but more is true:
* `yᵢ₋₁ ∈ K`, over abscissa `11/22 = 1/2`;
* `f` is an `ε₃`-homeomorphism;
* `π` is uniformly continuous on `M`, and the inverse of the collar is uniformly continuous on the
  closed rectangle.

So for `ε₃` small enough, `f(yᵢ₋₁)` lies over abscissae in `[3/8, 5/8]`. Shrinking `ε₃` is
harmless:
* Property 2 holds for every smaller `ε₃`: both its hypothesis on `h` and its condition
  `ρ(T, V) < ε₃` become stronger;
* T12's `ε₃/2`-homeomorphisms are chosen after `ε₃`.

The same applies to `f(yᵢ)`, `yᵢ`, `p` and `q`. Check this, and then use `[3/8, 5/8]` (P3)
throughout in place of `L₆`.

**B. The cutting step (`TailCutKeepsSep`), and Property 4 (2).** Separation of two middle points
should be witnessed by crossing components alone. Proposed lemma (`sep_by_crossing`):

> Let `X ⊆ F` be compact, and let `p, q ∈ π⁻¹[D] − X` lie over the middle. Suppose `X` separates `p`
> from `q` in `π⁻¹[D]`. Then the union of those crossing components of `F ∩ π⁻¹[D]` whose closures
> lie in `X` already separates `p` from `q`.

Routes:
1. **Through the middle strip.** Let `S = π⁻¹[D ∩ F[(3/8, 5/8) × (0, c₁)]]`. By P3, the points of
   `F ∩ S` lie in crossing components or in components meeting `d⁻¹(1)`.
   * If no crossing component in `X` separates `p` from `q`, look for a path from `p` to `q` in
     `π⁻¹[D] − X`. Build it inside `S` where possible, and around the crossing components of `X`
     otherwise. Their positions are ordered (`crossing_pair_separates`, `crossing_sides`).
   * The obstruction is a component of `X` meeting `d⁻¹(1)` that reaches into `S`. For `X = d⁻¹[[0, t]]`
     with `t < 1` there is none, since `X` misses `d⁻¹(1)`. **So for the cutting step, P3 already
     says: `X ∩ S` lies in crossing components of `F`.** These are components of `F ∩ π⁻¹[D]`, not of
     `X ∩ π⁻¹[D]`. Check whether a crossing component of `F` that meets `X` lies in `X`: it lies in
     one block, and the blocks are intervals of `d`.
2. **Through Schoenflies square coordinates** (`jordan_inner_collar`). For a compact proper
   subcontinuum `Z ⊆ M`, the components of `D′ − Z′` are of three kinds: one touching the bottom arc,
   one touching the top arc, and pockets touching only the side segments. There are no bubbles,
   since `Z` does not separate the plane. Use this to show that the only components of
   `π⁻¹[D] − X` containing middle points are bands between consecutive crossing components.
3. **Kuratowski's theorem**, if needed: a compact set separating two points of the plane has a
   component that separates them. The repository has the two-set form (`janiszewski_compact`).
   Apply it to `∂D ∪ X` and its components; each component of `X` meets `∂D` (boundary bumping), so
   the components of `∂D ∪ X` are easy to list. State what is needed.

With `sep_by_crossing`, `TailCutKeepsSep` follows: the tail beyond the last block holds no crossing
component. The same goes for Property 4 (2): only the top block separates, if `p` and `f(p)` are
separated by crossing components that all lie in the top block.

**C. Property 4 (1) and the set-up of T12.** "There exists a point `yₙ` of `K` such that (1) the
closure of the `yₙ`-component `Cₙ` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`". The base of the
induction takes `yₙ = p`. Use `hagopian76_T12_parts12` and `hagopian76_T12_uncond`, and package
`(K, h, h₁, f, p, F, d, xᵢ)` into one structure (`T12Data`) so that Property 4 can be stated as a
`Prop` on it.

**D. The induction** (Cases 1–2), with A–C. Two sentences remain:
* **"Let `Cᵢ₋₁` be the first component of `M ∩ π⁻¹[D]` … met by extending `Cl Cᵢ` away from `X`."**
  Extensions of `Cl Cᵢ`, a translate of a subcontinuum of `E`, are translates of extensions of `E`,
  or lie in `h[R(E)]`. Check whether Property 3 and `hagopian76_I_finite`, transported by `h`,
  supply "first".
* **"The continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`."** `N` lies in `L`, the extension of
  `Cl Cᵢ` up to `Cᵢ₋₁`, which is again a translate. P3 transported by `h` controls `L` over the
  middle. Check what is needed beyond that.

**E. The assembly**, `hagopian76_theorem1`, or a conditional form with named `Prop`s for exactly what
remains.

## 2. Items

A (positions by `ε₃`), B (`sep_by_crossing`, `TailCutKeepsSep`, `x₂ₙ = 1`), C (`T12Data`,
Property 4 for the top block), D (the induction), E (the assembly).

## 3. Places to check (candidate ledger entries)

1. **p. 348:** "`f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`": record that a stronger position is available.
2. **p. 348:** "Note that `x₂ₙ = 1`".
3. **p. 348:** Property 4 for the top block.
4. **pp. 348–349:** Cases 1–2; "first component"; `N`; "either above or below".

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch176.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
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
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
