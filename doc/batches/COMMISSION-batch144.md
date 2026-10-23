# Commission: batch 144 — Part D, Moore VIII: the end of Moore 1919. A Σ-space is a number plane.

**Go!** This batch runs on top of the batch-143 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch144.md`: this text, also pasted into the prompt.
* `Moore1919G.lean`: the skeleton.
  * Save it as `HPC/Moore/M19G.lean`. You may split it.
  * Add `import HPC.Moore.M19G` at the end of `HPC.lean`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1919, the plane (batch 144)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 143

Audited and accepted. The skeleton copy is byte-identical and the three statements are verbatim.
`axioms.txt` has 971 lines, and `sorryAx` appears in none of them.

What batch 143 delivered:

* **Theorem F.** It needed Theorem 42's connectedness, which Moore does not supply. The proof
  provides it with arcs.
* **The nested rulings.** These give Moore's "This process may be continued".
* **Schoenflies for Moore's space,** in three parts:
  * the grid of all ruling arcs;
  * mesh tending to 0, by the counting argument;
  * `Grid.exists_square`.
* **Theorem E**, derived from the square. This replaces Moore's unargued limit arcs.

Your recommendation for the end of the paper is accepted: the Schoenflies route, with Theorem G and
Moore's final paragraph as corollaries. The ledger will record the departure from Moore's open-curve
route.

## 1. Where this sits

| batch | content |
|---|---|
| 143 | 1919 E, F, Schoenflies (done) |
| **144 (this one)** | prescribed-boundary Schoenflies; annuli; **`m19_plane`**; Theorem G and the final paragraph as corollaries |
| 145 | Moore 1925 §I and Theorem 22: the decomposition space of `G′` satisfies F.A.'s axioms, so it is a plane |
| 146 | Jones 1955 Theorem 2, with Jones 1949 |

With `m19_plane`, Moore's characterization of the plane is complete. Batch 145 then needs only to
verify the axioms for the decomposition space.

## 2. Items

Follow your reading plan from REPORT-batch143.

**A. `m19_schoenflies_boundary`.**
* Two sides come from the grid construction itself; start from `Sq.Grid.mem_L_of_pos_eq`.
* The other two come from homeomorphisms of the square that fix two opposite sides.

**B. `m19_annulus`** (the shape is up to you). A closed annulus between nested closed curves is a
square annulus, compatible with a given boundary map on the inner curve.
* Use four quadrilaterals filling the annulus, made with the cutting lemmas of batches 141–142.
* Glue prescribed-boundary square maps along their common arcs.
* Record whether you prove Moore's nine-cell ruling of Fig. 3 as stated. Either way, record what the
  proof uses in its place.

**C. `m19_plane`.** Paste the annulus maps over Theorem F's exhaustion `Jₙ ∪ Iₙ ⊆ Iₙ₊₁`, `⋃ Iₙ = S`,
to get `S ≃ₜ ℝ²`.

**D. Corollaries.**
* `m19_theoremG`: images of the horizontal and vertical lines. Also prove that these are open curves
  in F.A.'s sense (p. 159).
* `m19_final`: Moore's sequential form. The space is metrizable (batch 137), so sequential and
  topological continuity agree.

## 3. Places to check (candidate ledger entries)

1. **Fig. 3:** "there exist on `Jₙ₊₁` four distinct points `Aₙ₊₁`, `Bₙ₊₁`, `Cₙ₊₁`, and `Dₙ₊₁` such
   that `Jₙ₊₁` can be divided by a double ruling … into nine subdivisions of which the central one is
   `AₙBₙCₙDₙAₙ (Jₙ)`". This is unargued. Record its status.
2. **The open curves `kₘ`, `tₙ`:** "It follows that there exists a set of open curves `[kₘ]` … and
   another set `[tₙ]` such that (1) … (2) … (3) …". This is unargued. Moore's route needs it; ours
   does not. Record that.
3. **"This process may be continued. It follows that there exist two sequences of arcs `gₘ₀, gₘ₁,
   …`"** and **"The sum of all the arcs … is clearly a continuous open curve"** (p. 178). Both are
   unargued. Record them.
4. **"It is clear that through every point there is just one curve of the set `α` and just one curve
   of the set `β` and furthermore each curve of the set `α` has just one point in common with each
   curve of the set `β`"** (p. 178). This is unargued; `m19_theoremG` supplies it.
5. **The final paragraph:**
   * "Between the points of `t₀` and the set of all real numbers there is a one-to-one continuous
     correspondence", which uses F.A. p. 159 and the 1915 characterization of the line;
   * "It is clear that the correspondence thus established … is continuous".

   Both are unargued. `m19_final` supplies them.
6. **"Σ₁ or Σ₂" (p. 169).** Moore's theorem is stated for the systems Σ₁ and Σ₂. F.A.'s Axioms 1–8
   are Σ₁. Σ₂ replaces Axioms 6 and 7 by 6′ and 7′ (F.A. p. 163). Moore 1925 Theorem 21 verifies the
   axioms of Σ₂ first, then Axioms 6 and 7.
   * Record whether `m19_plane` is stated for Σ₁ (as in the skeleton).
   * Record whether batch 145 will need it for Σ₂, or whether Moore 1925's verification of Axioms 6
     and 7 suffices.

   Read F.A. pp. 162–163 for Axioms 6′ and 7′.

## 4. Deliverables

1. Items A–D.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch144.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 145: Moore 1925 §I (`doc/sources/` will receive `moore1925.pdf`).

   For the reading plan, start from my transcription notes of 1925 §I: Theorems 1–22. Theorems 4–7,
   9, 10 and 15–19 are proved only by analogy with F.A. or other papers. Say what of batches 137–144
   transfers directly.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
