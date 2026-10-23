# Commission: batch 159 — Part E, Hagopian 1976 IV: Lemma 6, Lemma 7; plane Schoenflies and collars; Lemma 9

**Go!** This batch runs on top of the batch-158 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch159.md`: this text, also pasted into the prompt.
* `Hagopian76D.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76D.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76D` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 IV (batch 159)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76C.lean`: delete the commented-out copies of statements proved here,
    leaving one-line pointers. In the docstring of `AbutSameSide`, add one line saying it is
    superseded by `DecompAccessibleC`.

## 0. On batch 158

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** No statement changed.
* **Audit.** `axioms.txt` has 1415 lines, with `sorryAx` in none, all on the standard three axioms.

**Accepted.**
* **D1 is proved, in the strong form.** Your step-by-step check of my argument is recorded. In
  step 5 you used neighbourhoods and the continuity of `k` in place of sequences and upper
  semicontinuity; that is fine. The ledger records the third sentence of Lemma 4's first paragraph
  as unargued and true, supplied by an argument Hagopian does not give.
* **Lemma 5**, by one extension on each side. Hagopian's two-sided `F` is recorded as not needed.
* **Moore 1962 Theorem 28**, by your route through a side arc, `P ∪ L`, and Janiszewski.
* **`exists_quotient_plane'`.**

**My error, recorded in ledger C.4.** The Moore excerpt I sent stops at p. 156. Moore's proof of
Theorem 28 continues on p. 157, so you could not follow it. Your own proof makes the missing page
unnecessary.

## 1. Where this sits

The batch-158 dependency map shows three remaining gateways:
* Lemma 6, for T12, T13, T17, and through Lemma 7 for T10 and T16;
* Lemma 9 and the collar, for T3, T6 and T7;
* Property 1, for T5, T7, T11 and T14.

This batch takes the first two. Property 1 and T4–T9 come in batch 160, and the remaining
Properties and the induction in batches 161 and following.

## 2. Items

**A. Lemma 6 and the unnumbered claims.** Do this first; it is the gateway.
* Formalize steps 1–8 (report 157 §1.C), step 5 first. Step 5 is: the limit point `c` of the far
  ends `zᵢ`, the `δ`-homeomorphism `f` with `f(c) = zᵢ`, `L ∩ f[L] = ∅`, and `f[L] ⊆ R(X, E)`.
* Step 6 now has its "subcollection" from `hagopian76_initial_segment`.
* `hagopian76_essential_typeA'`. Formalize the containment argument of report 158 §1.C: an essential
  continuum lies in one extension, because otherwise it would contain the limit `c ∉ R(X, E)`. Then
  apply `isTypeA'_of_subcontinuum` with Lemma 5.

**B. Lemma 7.**

**C. Plane topology.**
* `plane_schoenflies`: transport `m19_schoenflies_boundary_proof` (or `m19_schoenflies_param`)
  through the plane model of Moore's axioms already used for `jordan_curve_theorem`
  (`mooreDecomp_ptSetoid` in `HPC/Jones/Jones55T2A.lean`). Choose the shape that transports most
  easily, as long as one side of the square goes to a prescribed arc of `J`.
* `exists_collar`, by the route in its docstring. If gluing two Schoenflies embeddings along `γ` is
  awkward, a one-sided collar on each side, with a statement that the two sides are the two
  complementary pieces near `γ` (the θ-curve), may serve instead. Record the shape.

**D. Lemma 8 with prescribed caps.** Choose its shape for Lemma 9 and for Property 1 (p. 346: "Here
the open sets `A` and `B` in the proof of Lemma 8 are in `G₁ − G₂` and `G₁₁ − G₁₀`
respectively").

**E. `DecompAccessibleC`, `hagopian76_lemma9`.**
* The collar form replaces `AbutSameSide`/`DecompAccessible`, which ask for a homeomorphism of the
  whole plane. Bing's definition (p. 215) straightens the arc and the two abutting arcs together. The
  collar form makes the two arc segments vertical in collar coordinates. Write the comparison in the
  report.
* Lemma 9's proof on p. 345 runs in coordinates where `π[E]` is horizontal and `π[I − {y}]` lies
  below it on a vertical line. Those coordinates are the collar's.
  * The chain `G = {G₁, G₂, G₃}` is to have `π[Gᵢ]` open disks. In collar coordinates, take
    rectangles about the three thirds of `π[E]`, pulled back by `π`.
  * Then use Lemma 8 with caps, Lemma 2, and Theorem 28.
* If the vertical arc `π[I − {y}]` cannot be made vertical in the same collar as the one used for
  `U`, record what is needed. A second application of Schoenflies, to the simple closed curve formed
  by `π[E]`, `π[I]` and a closing arc, should give it.

## 3. Places to check (candidate ledger entries)

1. **pp. 342–343, Lemma 6:** steps 1–8, each with the printed sentence quoted, formalized this time.
2. **p. 343:** the two unnumbered claims, with the containment of an essential continuum in one
   extension, which is unargued.
3. **pp. 343–344, Lemma 7:** the two sentences from commission 157 §3.6.
4. **p. 344:** "decomposably accessible from a side … abut on the same side of the arc `π[E]` in
   `R²` [2, p. 215]". Record the collar form and the comparison.
5. **pp. 344–345, Lemma 9:**
   * "We assume without loss of generality that `π[E]` is lying on a horizontal line `B` in `R²` and
     `π[I − {y}]` is below `B` on a vertical line": the Schoenflies theorem, unstated;
   * "Let `G = {G₁, G₂, G₃}` be a chain in `R²` that follows `E` such that (1) …, and (2) …";
   * "Note that `I` intersects `Bd G₂` and misses `Cl (G₁ ∪ G₃)`";
   * "this is impossible [13, Theorem 28, p. 156]". Record the configuration to which Theorem 28 is
     applied.

## 4. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch159.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for batch 160: Property 1 and T4–T9, T11, T14. Give Lean shapes for `ε₁`,
     `Wₓ`, `Gₓ`, the chain `{Gᵢ}`, `L`, Property 1, `I₁`, `I₂`, `D`, and Property 3, in collar
     coordinates.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
