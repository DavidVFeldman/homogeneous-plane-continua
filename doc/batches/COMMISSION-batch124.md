# Commission: batch 124 — the only-clauses (pair form of Theorem 3); Fugate's Corollary 1 as stated; survey for discharging `PlaneFacts`

**Go!** Runs on top of the batch-123 delivery. No skeleton; one file, `COMMISSION-batch124.md` (also
pasted into the prompt). Lean work in new files `HPC/Fold/Theorem3Pair.lean` (item 1) and
`HPC/Plane/Fugate66Cor1.lean` (item 2), imported at the end of `HPC.lean`; open statements as
`def … : Prop`; no new `sorry`. Existing files to be edited, and only these: `HPC.lean`,
`Axioms.lean`/`axioms.txt`, `LEDGER.md`, `OPEN.md`, `README.md`, `doc/census/README.md`, and
`HPC/Plane/Fugate66.lean` only if item 2 closes `fugate_cor1` (then its `sorry` goes, as
`theorem3_end`'s did in batch 123).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 123

Audited and accepted: `theorem3_end` closed (one `sorry` left in the build), `theorem3_bing`,
`theorem4_two` with the necessary `hdeg` and the refuted degenerate case, the only-clauses open with
`onlyIn_of_neighbour` and the pair form as the obstruction, ledger/OPEN/README as asked. 468
declarations. Two slips of mine recorded: `Theorem4Literal` without `hdeg`; the census README
was left out of the editable files.

## 1. The only-clauses: the pair form of Theorem 3 (`Theorem3Pair`)

REPORT-batch123 §3: the only-clause at a covered interior basepoint `i` holds iff some
consolidation as in `theorem3_bing` has `i` and one neighbour in its first block
(`onlyIn_of_neighbour`); `Theorem3Pair` (two adjacent links in a common coarse link, both in the
first block) would settle the case where the covered link shares a coarse link with a neighbour,
and the remaining case (levels `a, a+1, a+2` in a row with the middle link covered) needs its own
argument. The model census found no failure of either (≈ 3–4 M instances).

**Q1.** Prove `Theorem3Pair` in the model of batch 122, or refute it, or state the obstruction. The
natural attempt is Bing's induction (`bing_main`) with the basepoint replaced by the pair; say
exactly which step resists if one does (the special case at `r = 5`, where the explicit grouping
`special_five` puts the links up to `d_k` lying in `e₁ + e₂` in one block, is the place I would
look first: if the pair straddles `d_k`'s block boundary there, the pair form may need a second
explicit grouping).

**Q2.** The remaining case: a covered interior link `i` with `ρ(i−1) = a`, `ρ(i) = a+1`,
`ρ(i+1) = a+2` (so no coarse link contains `i` with a neighbour). In a chain, `E.link i ⊆
E.link (i−1) ∪ E.link (i+1)` with `E.link i ⊆ D_{a+1}` and `E.link (i−1) ⊆ D_a`, `E.link (i+1) ⊆
D_{a+2}` forces `E.link i ⊆ (D_a ∩ D_{a+1}) ∪ (D_{a+1} ∩ D_{a+2})`. Is this case possible at all for a
1948-crooked chain (crookedness is a hypothesis on *meetings*, and a link in `D_a ∩ D_{a+1}` meets
both)? If it is impossible, prove it and the only-clause for Theorem 3 follows from Q1; if it is
possible, settle the only-clause there or state the obstruction.

**Q3.** From Q1–Q2: `Theorem3LiteralOr` (Theorem 3 as printed, every clause) — proved / refuted /
open; and the only-clauses of `Theorem4LiteralND` likewise (the pair form at `r` and at `s`, the
two ends of the consolidation; `theorem4_two`'s construction may need the pair form at both ends
at once). If proved, `fugate`-style closure: `theorem3_literal` and `theorem4_literal` as chain
theorems, README/OPEN/LEDGER updated (the only-clause rows), OPEN item 2 closed.

## 2. Fugate's Corollary 1 as stated (`fugate_cor1`)

Fugate (p. 467) states Corollary 1 immediately after the proof of Theorem 1, **without proof**:

> Corollary 1. Suppose (X, d) is a metric space and for each positive integer i, 1 ≤ i ≤ n, A_i is
> a chainable compact continuum in X such that A_i ∩ A_{i+1} ≠ ∅. Then ⋃ A_i is chainable if and
> only if ⋃ A_i is a-triodic and unicoherent.

The intended proof is the induction on `n` through Theorem 1, which needs each partial union
`A₁ ∪ ⋯ ∪ A_p` to be unicoherent; unicoherence is not hereditary in general, and the repository
proves the corollary only under hereditary unicoherence of the union (`fugate_cor1'`,
`fugate_cor1_iff`, batch 101). What is needed is exactly:

**(U)** if `A₀, …, A_k` are snake-like continua, consecutive ones meeting, and `⋃ Aᵢ` is atriodic
and unicoherent, then every partial union `A₀ ∪ ⋯ ∪ A_p` is unicoherent (equivalently, by
`isHereditarilyUnicoherent_union` and induction, `⋃ Aᵢ` is hereditarily unicoherent).

My analysis so far (informal): if some partial union is not unicoherent, let `p` be least with
`U_p := A₀ ∪ ⋯ ∪ A_p` not unicoherent; then `U_{p−1}` is hereditarily unicoherent (induction with
`isHereditarilyUnicoherent_union`), so `U_{p−1} ∩ A_p` is disconnected; unicoherence of the whole
union applied to `U_{p−1} ∪ (A_p ∪ ⋯ ∪ A_k)` and to `(U_{p−1} ∪ A_{p+1} ∪ ⋯) ∪ A_p` (when those are
continua) forces the later pieces to bridge the components of `U_{p−1} ∩ A_p` inside `U_{p−1}` and
inside `A_p`; with arcs this always creates a circle in a Peano continuum (not unicoherent) or a
triod; with non-locally-connected pieces I could not decide. Miller's Theorem 1.5 (as Fugate uses
it: a non-unicoherent subcontinuum of a unicoherent `A ∪ B` lies in `A` or in `B`) places a
non-unicoherent subcontinuum inside `U_{k−1}` or `A_k`, which does not close the induction.

**Q4.** Decide (U): proved (then `fugate_cor1` closes from `fugate_cor1'`: replace its `sorry`;
`sorryAx` disappears from the build), refuted (a continuum built from snake-like pieces; an
informal counterexample with a convincing argument is acceptable if a Lean certificate is out of
reach — say so plainly; the ledger would then record "Corollary 1 as stated is false; true under
hereditary unicoherence"), or open with the obstruction. Note for the ledger in every case: Fugate
gives no proof, and the one-line induction he presumably intends needs (U).

## 3. Survey for discharging `PlaneFacts` (no proofs; the report only)

The interface `HPC.Plane.PlaneFacts` (jct for simple closed polygons; enclosing polygon around a
non-separating continuum inside an open set; Janiszewski for compacta) is the last hypothesis in
the repository. Before commissioning its discharge I need a survey, half a page each:

**Q5 — `jct`.** Does the project's Mathlib (`lake-manifest.json`) contain any form of the Jordan
curve theorem, or of the polygonal case, or of the ray-crossing parity argument for polygons?
(Search the Mathlib sources in `.lake/packages/mathlib` for `Jordan`, `windingNumber`,
`IsPathConnected` results about complements of curves, and anything about polygons.) If not,
estimate the polygonal JCT by the parity argument in the repository's conventions (`Pt = ℝ × ℝ`,
`IsSimpleClosedPolygon`, the local structure lemmas `polygon_local_rays`, `ball_diff_rays` of
batch 118, the cross-cut machinery of batches 119–120): which lemmas exist, which are missing,
and roughly how large the missing part is (in the units of the batches you have done).

**Q6 — `enclose`.** Same for the enclosing polygon: a non-separating compact continuum `M` inside an
open `G` has a simple closed polygon `J` with `M ⊆ polyInterior J ⊆ G`, `J ∩ M = ∅`. The
construction I know: a fine grid, the union of closed squares meeting `M` thickened slightly (so
no two meet in a point), its complement's unbounded component `V`, and the frontier of `V` as the
polygon — the frontier is a disjoint union of simple closed polygons (1-manifold classification
of a rectilinear boundary, the thing the general-position route of batch 119 avoided), exactly one
since `M` does not separate. Say what the repository has towards it and what is missing.

**Q7 — `janiszewski` (compacta).** This is the hard one: the proofs I know go through Alexander
duality, through Borsuk's separation criterion, or through the unicoherence of the plane/sphere.
Is there any elementary route for the special case the repository actually uses? List the uses:
`exists_theta_point` (batch 118, `A ∪ Γ`, `B ∪ Γ` with `A, B` compact subsets of the closure of a
component of `U ∩ h₁ ∩ h₂`, `Γ` a simple closed polygon) and `crosscut'` (batch 119, `Γ₁`, `Γ₂`
simple closed polygons with `Γ₁ ∩ Γ₂` a polygonal arc). If every use has both sets *polygonal* (or
polygonal plus a compact subset of a polygon's closure), is a polygonal Janiszewski within reach
from polygonal jct? Assess; do not prove.

**Q8 — `treeLike_nonseparating`.** With Q5–Q7 in view: is there a route to "tree-like ⇒ no
subcontinuum separates the plane" that uses only what a discharged `PlaneFacts` would provide,
or does it need a new field (Borsuk's criterion)? One paragraph.

## 4. Housekeeping

`doc/census/README.md`: list the batch-123 files (`recon-batch123-only.py`,
`recon-batch123-{only,pair,nocontain}.log`). `README.md`: batch count 124; if item 1 or 2 closes
something, the corresponding lines. Notes file to `doc/` as usual; no stray copies.

## 5. Deliverables

1. Items 1–2 in Lean (Props, proofs, any certificates); `axioms-batch124.txt`; `axioms.txt`
   regenerated (`sorryAx` in one line, or none if item 2 closes `fugate_cor1` — say which).
2. Report: first line names the commission read; Q1–Q8 in order; the ledger texts for the
   only-clauses and for Corollary 1; the survey of item 3 with the estimates.
3. Not attempted: `PlaneFacts` itself, `treeLike_nonseparating` (survey only).
