# Commission: batch 164 — Part E, Hagopian 1976 IX: Theorem 1, from the reparametrization to Property 3 (T7, T8, T9, T11, T14)

**Go!** This batch runs on top of the batch-163 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch164.md`: this text, also pasted into the prompt.
* `Hagopian76I.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76I.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76I` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 IX (batch 164)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

## 0. On batch 163

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1623 lines, with `sorryAx` in none, all on the standard three axioms.
* **Shape changes accepted:** the unused `a ≤ b` dropped in two places.

**Lemmas 1–9 of Hagopian 1976 are now verified.** Lemma 9 is verified in a stronger form: its
hypothesis "not decomposably accessible" is unused.

Also accepted:
* **The adapted collar.** The new lower half-collar is built from two Schoenflies squares glued along
  the drop arc.
* **`no_M_below`.** You replaced Hagopian's step "`G₂ ∩ E` and `G₂ ∩ h[E]` disjoint" by
  `h[D] ∩ C = ∅`, proved directly. The end links are rectangles with small discs attached. "Compactness
  over `a′`" became a sequence argument. The ledger records the printed sentence as not used and not
  decided.
* **T3 at interior points, and T6.**

## 1. Notes on the items

**A. The reparametrization** (`OPEN.md`, batch 163). A homeomorphism `θ` of `[0, 1]` fixing `0` and
`1` turns `k` into `θ ∘ k`, which is still minimal admissible with the same layers. `γ` becomes
`γ ∘ θ⁻¹`, and the collar becomes `F ∘ (θ⁻¹ × id)` on the rectangle. Choose `θ` to send the
accessible parameter `y` into `(0, 3/22)`. This is bookkeeping, but T6 needs it to sit at Hagopian's
abscissae.

**B. T7.** Two observations may shorten it.
1. **Points of `π[M]` above.** `no_M_below` gives a strip below `γ([a, b])` missing `π[M]`. If a
   strip *above* also missed `π[M]`, then `π⁻¹` of the two strips together with `γ((a, b))` would be
   a neighbourhood of an open piece of `E` that meets `M` only in `E`. So `E` would have interior in
   `M`, against the indecomposability of `M`: a proper subcontinuum of an indecomposable continuum is
   nowhere dense. So `π[M]` approaches `γ([a, b])` from above. This is where Hagopian's "a point `y`
   of `M ∩ L₆` … such that `π(y)` is above `π[E]`" comes from. Its accessibility from `R² − M` still
   has to be shown: for example, take the first point of `π[M]` met by a vertical segment coming down
   from a point of the complement, or use the accessible points' density.
2. **Hagopian's arc `A`** "to one side of `h[E]` that meets `L₁` and `L₁₁` (Lemma 9 (proof))" is
   `hagopian76_T6` (or `no_M_below`) applied to the type A′ continuum `h[E]`, with its own quotient
   `π′`, its own collar, and the accessible point `y` of `h[E]`. Pull the strip back to `R²` by `π′`.
   It misses `M`, so it misses `h[E]`, where `π′` is not a homeomorphism. Then push it forward by
   `π`, which is injective off `E`.
   * The sentence "By choosing `y` sufficiently close to `E` and `h` sufficiently close to the
     identity, we get that every point of `R²` between `⟨p₁, p₅⟩` and a subarc of `π[A]` irreducible
     between `⟨p₁, q₁⟩` and `⟨p₅, q₅⟩` belongs to `π[St L]`" is unargued. Supply it, or replace it
     with whatever the later steps need of `D`. Property (D) of `hagopian76_T9` is the main use.
   * If a shorter construction of `I₂` and `D` gives the same properties, use it and record the
     comparison.

**C. T8.** `D` is the bounded domain of a simple closed curve made of four arcs (`jordan_curve_theorem`,
`TArc` unions). In collar coordinates it should be a region between the axis and `I₂`, over
`[p₁, p₅]`. State property (D), and whatever T11 and Property 3 use.

**D. T9 in full, the definition of `ε₂`, and Property 2 at `ε₂`.**

**E. T11.** Batch 161 recorded that the printed `ε₁` does not decide which sides of `K` contain
`L₂ ∩ π⁻¹[D]` and `L₁₀ ∩ π⁻¹[D]`. In collar coordinates the sides are decided by abscissae, once the
links of `L` are controlled. Prove it with whatever control is needed, and record it.

**F. Property 3**, in full.
* "Let `v` be the first point of `[0, 1]` such that `d⁻¹(v)` contains a component of `F ∩ π⁻¹[D]`
  whose closure meets `π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]`." Closedness of the set of such `v` is
  unargued. It is a limit argument for crossing components.
* The crossing property under the shift `g` ("`d⁻¹(u)` contains a component of `F ∩ π⁻¹[D]` whose
  closure meets …") is the other gap.

## 2. Order

A, B, C, D, E, F. If B takes the whole batch, stop there and leave a plan for the rest.

## 3. Places to check (candidate ledger entries)

1. **p. 345:** "Since `M` is homogeneous, we can assume … that `π[k⁻¹(i/22)] = (i, 0)` for each
   integer `i`". This is the reparametrization.
2. **p. 346, T7:** the sentences quoted in the skeleton. In particular:
   * the existence of an accessible `y` above;
   * "(Lemma 9 (proof))";
   * "By choosing `y` sufficiently close …".
3. **p. 346, T8:** the simple closed curve and `D`.
4. **p. 346, T9:** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`".
5. **p. 346:** "Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`". Check that this is
   positive: `I₁ ∪ I₂` misses `π[M]`.
6. **p. 347, T11:** "Note that `K` separates …".
7. **p. 347, Property 3:** "Let `v` be the first point …"; "By Lemmas 2 and 3 …"; "This contradicts
   the definition of `v`".

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch164.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map, updated;
   * a skeleton proposal for T12, T13, T15–T17 and the assembly `hagopian76_theorem1`, revised in the
     light of this batch.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
