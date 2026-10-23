# Commission: batch 165 — Part E, Hagopian 1976 X: Theorem 1 — T7's arc `I₂` by a crossing argument; T8, T9, T11, Property 3; then T12–T17

**Go!** This batch runs on top of the batch-164 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch165.md`: this text, also pasted into the prompt.
* `Hagopian76J.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76J.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76J` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 X (batch 165)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `doc/notes/`: see §5.

**Progress lines.** While you work, write a one-line message beginning `STATUS:` in your trace
whenever an item is proved, left open, or stuck. Example: `STATUS: A.1 hagopian76_no_hair proved.`
If you are stuck and a hint would help, write `STATUS: need help` followed by the obstruction in one
sentence.

## 0. On batch 164

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1656 lines, with `sorryAx` in none, all on the standard three axioms.

**Accepted.**
* The reparametrization (`hagopian76_reparam`), with `hagopian76_T6_placed` and `hagopian76_I1`.
* `M_meets_above` and `exists_accessible_above` (T7's `y`), collected in `hagopian76_T7_accessible`.
* `hagopian76_eps2_pos`.
* Your analysis of Hagopian's arc `A` through `h[E]`, and its four open steps. Step 3 (the side) is
  the real gap. This batch avoids it.

**One correction.** Report 164 §1.1 puts `pᵢ` at `(2i + 1)/22`. Hagopian (p. 345) has
`pᵢ = (4i − 1, 0)`, `oᵢ = (4i − 1, −1)`, `qᵢ = (4i − 1, 1)` for `1 ≤ i ≤ 5`. So `p₁, …, p₅` are at
abscissae `3, 7, 11, 15, 19` (out of 22). Your interval `⟨p₁, p₅⟩ = [3/22, 19/22]` is right. But
`p₃`, through which T11's `K` passes, is at `11/22`, not `7/22` (report 164 §1.5).

## 1. The route for T7: no hair on `E`, and a crossing arc

We do not need `h[E]`. Two facts give `I₂` at once.

**Step 1. No continuum leaves `E` through its middle** (`hagopian76_no_hair`). Let `Q` be a
continuum of `M` that meets `E` and misses both end sets `k⁻¹(0)` and `k⁻¹(1)`. Then `Q ⊆ E`.
* `E` is an extension of itself away from `k⁻¹(0)` (map `k`) and away from `k⁻¹(1)` (map `σ ∘ k`).
* Absorption (`subset_extUnion_of_meets`, batch 160) gives `Q ⊆ R(k⁻¹(0), E)` and
  `Q ⊆ R(k⁻¹(1), E)`.
* So each point of `Q` lies in an extension away from `k⁻¹(0)` and in an extension away from
  `k⁻¹(1)`. By `ext_inter_subset` (batch 160) it lies in `E`.

**Step 2. Pull continua back by `π`** (`preimage_pi_isContinuum`). For a continuum `C ⊆ π[M]`, the
set `{x ∈ M : π(x) ∈ C}` is a continuum. `π` restricted to `M` is a closed map, by compactness. Its
fibres are layers or points, so they are connected (`IsPreconnected.preimage_of_isClosedMap`).

**Step 3. The crossing lemma** (`rect_crossing`). Work in collar coordinates. Let
`K = {z ∈ [a, b] × [0, c] : F(z) ∈ π[M]}`. It is compact, and it contains the bottom edge, since
`F(t, 0) = γ(t) ∈ π[E]`.
* **No connected part of `K` joins the bottom edge to the top edge.** Suppose `C` did. Replace it by
  its closure. Then `F[C]` is a continuum in `π[M]`. By step 2, its preimage `Q` is a continuum of
  `M`. It meets `E`, and it misses `k⁻¹(0)` and `k⁻¹(1)`, because `0 < a` and `b < 1` and `F` is
  injective. By step 1, `Q ⊆ E`, so `F[C] ⊆ range γ`. But `C` meets the top edge, and
  `F(t, c) ∉ range γ` for `c > 0`.
* **Hence an arc in the rectangle, missing `K`, joins the left edge to the right edge.** This is
  the dual form of the statement above. Two routes:
  * **Clopen split, then Janiszewski.** Components of the compact set `K` are quasi-components
    (Mathlib, compact Hausdorff). So `K = K_b ⊔ K_t` with both closed, the bottom edge in `K_b`, and
    `K ∩ top` in `K_t`. Then apply `janiszewski_compact` (`HPC/Moore/M25Plane.lean`) to
    `A = K_b ∪ (lower frame)` and `B = K_t ∪ (upper frame)`, with `x` and `y` just outside the left
    and right edges. The frame is a polygon around the rectangle, attached at its four corners and
    split into a lower and an upper part. Arrange it so that:
    * `A ∩ B` is a single point;
    * neither `A` nor `B` separates `x` from `y`;
    * every path from `x` to `y` that misses the frame passes through the rectangle.

    For example, let the two parts meet at one point to the right, and leave a gap at the left.
    Then a path from `x` to `y` in the complement of `A ∪ B` crosses the rectangle. Take its part
    between the last visit to the left edge and the first visit to the right edge.
  * **A grid argument**, through the polygonal Janiszewski already in the repository
    (`janiszewski_polygonal`).

  Then extract an arc from the path (path-connected open sets of the plane) and cut it to meet the
  side edges only at its ends.

**Step 4. Assemble T7** (`hagopian76_T7`).
* Take `U = St L`. A thin closed collar rectangle over `[3/22, 19/22]` lies in `π[St L]`. `St L` is
  open and contains `E`, and `π⁻¹π[E] = E`. Then use compactness and the closedness of `π` on `M`,
  or upper semicontinuity of the layers (`layer_nbhd_small`).
* `I₂ = F[I]`, with `I` from step 3. It misses `π[M]`, so `π⁻¹[I₂] ⊆ (St L) − M`.
* Every point between `I₂` and `⟨p₁, p₅⟩` lies in the rectangle, hence in `π[St L]`.

**Check each step.** If one fails, say which and why. If you find a reason this route proves too
much, say so first. It proves more than Hagopian's sentence: the crossing arc exists in every thin
enough rectangle, with no accessible point and no `h[E]`.

**Consistency with B.1.** `M_meets_above` says every window above `π[E]` meets `π[M]`. The arc
`I₂` passes between those points; nothing conflicts. `M_meets_above` is what makes `D` contain
points of `M`.

## 2. The other items

**B. Link control.** Property (D) of `hagopian76_T9` needs every point of `M` over the thin
rectangle to lie in one of `L₂, …, L₁₀`.
* `L₁ ⊆ G₁` lies within `ε₁` of `k⁻¹[[0, 2/22]]`. But `IsEps1.sep` does not keep it away from
  parameters in `[3/22, 4/22]`.
* So add the term `EndCtl` to the minimum defining `ε₁`. It is positive, since the compact sets
  `k⁻¹[[0, 2/22]]` and `k⁻¹[[3/22, 1]]` are disjoint, and likewise at the other end. Shrinking `ε₁`
  is harmless: everything proved about `ε₁` holds for every `ε₁` with `IsEps1`.
* With `δ < ε₁` from upper semicontinuity, a point of `L₁` over the rectangle is within `2ε₁` of
  both sets, which is impossible. The same argument works for `L₁₁`.
* For T11, `IsEps1.sep` already suffices:
  * a point of `L₂` over the rectangle has abscissa at most `6/22 < 11/22`;
  * a point of `L₁₀` has abscissa at least `16/22 > 11/22`.

**C. T8 and T9 in full.**
* `D` is the bounded domain of the Jordan curve `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩`. In collar
  coordinates it is the bounded domain cut off in the rectangle. State it in whichever form T11 and
  Property 3 use best, and record that it is Hagopian's `D`.
* Property (D) follows from B.
* For T9, `hagopian76_no_hair` gives `Cl B ∩ E = ∅` for every component `B` of `M ∩ π⁻¹[D]`.
  `Cl B` lies over the closed rectangle, so it misses both end sets. If it met `E`, it would lie in
  `E` by `hagopian76_no_hair`, whereas `B` lies off the axis.
* So `Cl B` meets the boundary of `π⁻¹[D]` only over the open side edges `⟨p₁, r⟩` and `⟨p₅, s⟩`.
  It misses `π⁻¹[I₂]`, which misses `M`. Use this for "the chain `L − {L₁, L₁₁}` follows `Cl B`".
* `ε₂ = min(ε₁, ρ(M, π⁻¹[I₁ ∪ I₂]))` is positive by `hagopian76_eps2_pos`.

**D. T11.** The vertical over `p₃ = 11/22` cuts `D` into a left and a right part (`plane_split`, or
in collar coordinates). Link control (B) puts `L₂ ∩ M ∩ π⁻¹[D]` on the left and
`L₁₀ ∩ M ∩ π⁻¹[D]` on the right. Pull back by `π`, which is a homeomorphism off `E`.

**E. Property 3**, in full.
* The least `v`: use the plan of report 164 §1.6, a hyperspace limit of crossing continua. The limit
  continuum misses `π⁻¹[I₂]` by `ε₂`. By `hagopian76_no_hair`, it also misses `E`.
* The crossing property under the shift `g`.

**F. T12–T17 and the assembly `hagopian76_theorem1 : Hagopian76Thm1`**, if reached. Use the shapes
of report 164 §5. The hypotheses `hI₂`, `hD`, `hDL`, `hL2`, `hL10` should now be theorems.

## 3. Order

A (steps 1–4), B, C, D, E, F. Step 1 is short and should come first. If the crossing lemma (step 3)
takes long, state it, prove the rest from it, and leave it open with the obstruction stated.

## 4. Places to check (candidate ledger entries)

1. **p. 346, T7:** "There exists an arc `A` in `(St L) − M` to one side of `h[E]` that meets `L₁`
   and `L₁₁` (Lemma 9 (proof)). By choosing `y` sufficiently close to `E` and `h` sufficiently close
   to the identity …". Record:
   * that the printed route leaves the side unargued (report 164);
   * whether the crossing route replaces it.
2. **p. 346, T8:** the simple closed curve and `D`.
3. **p. 346, T9:** "Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is the
   image of a subcontinuum of `E` …" and "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`".
4. **pp. 345–346, `ε₁`:** whether the printed families give property (D), or `EndCtl` is needed.
   The printed `ρ(Aᵢ, Bᵢ)` keeps `G₁` off the vertical `⟨o₁, q₁⟩`, but not off the region to its
   right.
5. **p. 347, T11:** "Note that `K` separates …".
6. **p. 347, Property 3:** "Let `v` be the first point …"; "This contradicts the definition of `v`".
7. **pp. 347–349, T12–T17**, if reached.

## 5. Housekeeping

* Uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
* **Delete the stale copies of my scheduling notes in `doc/notes/`:** the ten files
  `theorems-3-4-scheduling(1).md`, `(2)`, `(3)`, `(4)`, `(5)`, `(6)`, `(8)`, `(9)`, `(10)` and
  `(36).md`. They are about 4.9 MB of duplicates, and nothing refers to them. Keep
  `doc/notes/fugate-cor1-proof.md`.

## 6. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch165.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if F is not finished, a skeleton proposal for what remains.
4. **Build provenance**, in a short section of the report:
   * whether this run started from a fresh checkout of the delivered repository;
   * whether Mathlib's compiled files were downloaded (cache) or built from source;
   * roughly how long the first full build took.
