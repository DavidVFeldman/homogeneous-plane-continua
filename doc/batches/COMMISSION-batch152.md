# Commission: batch 152 — Part F, Jones 1949 IV: Whyburn 1939, Theorem 14

**Go!** This batch runs on top of the batch-151 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch152.md`: this text, also pasted into the prompt.
* `Jones49D.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49D.lean`. You may split it.
  * Add `import HPC.Jones.Jones49D` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Whyburn 1939 Theorem 14 (batch 152)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 151

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** Every statement is verbatim except `sector_theorem`, whose shape you chose. It is
  accepted: the closed annulus is stronger than what was asked.
* **Audit.** `axioms.txt` has 1174 lines, with `sorryAx` in none. Nothing is open.

Points accepted:
* **The sector theorem by lifting to a strip** is accepted. It is an elementary route, without
  Janiszewski, unicoherence or the Jordan curve theorem, which suits the exposition.
* **Moore 1922 is complete.** The ledger now counts Theorem 4's necessity as a defective proof
  (the thirteenth).
* **Your plan to build the F.A. curve directly in `ℝ²`** is adopted.

## 1. Items

The steps follow the outline in the skeleton header.

**A. `whyburn39_moore_curve`** (choose its shape). It is the curve `C ⊂ J + C_ε` bounding a region
`E ∋ 0` inside `I·V_ε(p)`. Note that p. 748 prints `C_ε` here, not `C_δ`.
* Build it as the component of `I·V_ε(p)` containing `0`.
* Whyburn needs only two things from `C`: the arc `x₁xuyy₁` of `J` lies on `C`, and the other arc
  `x₁wy₁` of `C` lies in `C_ε + xy·V_ε(p)`.
* Prove the weakest form that carries the argument. Say whether the boundary of the component is
  in fact a simple closed curve.

**B. `whyburn39_curve_from_order_two`** (choose its shape). Your batch 151 sketch of `K`, which
picks frontier points of `V_δ(p)` of order 2, is not Whyburn's step. His step is a plane curve `K`
around the single point `p′`, which has order 2 in `M`, with `K·M = c + d`. Decide one of two
things:
* whether this holds in that form, given that `c`, `d` must be accessible from `Mᶜ`; or
* whether a weaker statement suffices. One candidate: an open `D ∋ p′` inside `V_ε(p)` whose
  frontier meets `M` in finitely many points, and whose frontier minus `M` has finitely many
  components. Whyburn's pigeonhole then goes through.

Record which form you prove.

**C. `whyburn39_local_noncut`.** This is step 3, with (6.22) (`whyburn39_6_22_sec14`) and item A.

**D. `whyburn39_theorem14`.**
* Step 4: the limit continuum `H`, `whyburn_3_2`, item B, and the pigeonhole.
* Then `moore22_sufficiency_local` and `isConnected_frontier_complDomain`.

No inversion is used.

## 2. Places to check (candidate ledger entries)

All are from page images.

1. **p. 747:** "Since almost all the points `pᵢ` lie in `V_δ(p)`, we may suppose that all of them do.
   Let `p₁p₂` be an arc in `R` from `p₁` to `p₂`." Arcs in an open connected plane set: record the
   repository lemma used.
2. **p. 747:** "There must exist a subarc `xy` of `p₁p₂` such that `x + y ⊂ C_δ`, `xy − (x + y)`
   lies without `C_δ` and `x` and `y` cannot be joined by a continuum of `R` lying in `V_{2ε}(p)`".
   The finite-cover argument that follows (p. 748) is short; check it.
3. **p. 748:** "Now the continuum `N` can intersect only one of the arcs `xuy`, `xvy` of `C_δ`, since
   neither `N` nor `xy` contains a point of `V_δ(p)` and `N·xy = 0`." This is a plane separation step
   (θ-curve), and it is unargued.
4. **p. 748:** "Let `0` be a point of `I·V_ε(p)` which can be joined to `u` by an arc `ou` such that
   `ou − o` lies in `I·V_ε(p)`." Record why such `0` exists. Note that `ou − o` contains `u ∈ J`,
   which is not in `I`.
5. **p. 748:** "it follows that since `ou − o ⊂ E`, the arc `x₁xuyy₁` of `J` is contained in `C`".
   This is unargued.
6. **p. 748:** "The sequence of arcs `pᵢqᵢ` contains a subsequence … converging to a non-degenerate
   continuum `H ⊂ M`". Why is the limit in `M`, and why is it nondegenerate? Also: "every point of
   `H` within `V_ε(p)` is, like `p`, the limit of a sequence of points of `R` no pair of which can be
   joined in `R` by a connected set of diameter `< 3ε`". This is unargued, and it uses `3ε` after
   `4ε`.
7. **p. 748:** "But there exists points `p′ᵢ, p′ⱼ, p′ₖ` from distinct arcs … which lie in `D`".
   Record it, together with the misprint "there exists" for "there exist".
8. **The inversion** (p. 747), already in the ledger as a candidate. Count it as a defective proof
   once Theorem 14 is verified.

## 3. Deliverables

1. Items A–D.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch152.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 153: Corollary 1 (p. 749), following your batch 150 §5 (d) route.
     Two of its ingredients are not in the repository: the accessibility of boundary points from `R`
     by arcs, and a θ-curve in a cyclic Peano continuum that is not a circle. For each, say whether
     it needs more than batches 146–152 provide.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
