# Commission: batch 137 — Part D, Moore I: F.A. §§2–5 (Theorems 1–19), the bridge to topology, arcs

**Go!** This batch builds on the batch-136 delivery. Three files come with this commission, as
separate uploads (no archive):

* `COMMISSION-batch137.md`: this text, also pasted into the prompt.
* `MooreFA.lean`: the skeleton; each `sorry` is a work item.
  * Save it as `HPC/Moore/FA.lean` (a new directory).
  * Add `import HPC.Moore.FA` at the end of `HPC.lean`.
  * You are expected to split it into several files under `HPC/Moore/`.
* `moore1916.pdf`: R. L. Moore, *On the foundations of plane analysis situs*, Trans. AMS 17
  (1916), 131–164 ("F.A."). Save it as `doc/sources/moore1916.pdf`.

**Rules.**
* You may adjust shapes. Record each change at the statement and in the report.
* The report's first line names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore F.A. §§2–5 (batch 137)");
  * `README.md` (a Part D line and the batch count);
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 136

Audited and accepted:
* every definition is verbatim from the skeleton;
* every statement is the skeleton's, or the skeleton's with hypotheses dropped as recorded;
* `axioms.txt` has 796 lines, with `sorryAx` in none.

The following results go into the exposition:
* the spreading lemma from Effros;
* your proof of Jones 1951 Theorem 1 by an irreducible continuum;
* the location of the `M₀ ⊆ M₁` gap: only when `o(q) ∈ V₂`;
* the second gap on p. 738, where "`q` does not cut `o` from `U_q`" presupposes (b).

I checked p. 859 of Jones 1951 myself. It uses "`M′` is hereditarily unicoherent",
"homogeneous and aposyndetic" and "contains a nonseparating point" without argument.

**Two stale texts to fix in this batch** (I authorize the edits):
* the docstrings of `HPC/Jones/Jones51.lean` and `HPC/Jones/Jones48.lean` that still call Jones
  1951 Theorem 1 open;
* the README's `HPC/Jones` and `doc/sources/` rows.

## 1. Where this sits: the route to Jones 1955 Theorem 2

Jones 1955 Theorem 2 needs Moore's theorem: an u.s.c. decomposition of the plane into nonseparating
continua has the plane as decomposition space. The cited source is Moore 1925 (Trans. AMS 27),
Theorem 22. Moore proves it in three steps:

1. The space of elements, with suitably defined "regions", satisfies the axioms of F.A. (Moore
   1925 §I, Theorems 1–21).
2. A space satisfying those axioms is a number plane (Moore, *Concerning a set of postulates for
   plane analysis situs*, Trans. AMS 20 (1919)).
3. Step 2 uses F.A. throughout.

We follow this route but only as far as the goal requires, in four batches:

| batch | content |
|---|---|
| **137 (this one)** | F.A. §§2–5 (Theorems 1–19); the bridge to topology; arcs |
| 138 | F.A. §6 (Theorems 20–35) |
| 139 | F.A. §7, only what 1919 and 1925 use |
| later | 1919; then 1925 §I and Theorem 22; then Jones 1955 Theorem 2 with Jones 1949 |

**The arc substitution.** Moore's arc theory rests on N. J. Lennes (Amer. J. Math. 33, 1911).
F.A. §5 (p. 139) says only that "it is possible to prove Theorems 2–9 of §4 of Lennes' paper"
and supplies no proofs. We replace Lennes by the classical arc characterization in a metrizable
space: a nondegenerate metric continuum with exactly two non-cut points is an arc (Nadler,
*Continuum Theory*, Ch. 6). Section 4 of the skeleton makes Moore's space metrizable, so this
applies. The ledger records the substitution as "Lennes's theorems, not supplied in F.A., proved
via the arc characterization".

## 2. Items

**A. Definitions** (skeleton §1, pp. 132–139).
* Transcribed from the page images. Moore's primitives are kept: points, and a class of subsets
  called regions. Limit point, boundary, `M′`, exterior, connected, Heine–Borel, closed, bounded,
  domain, arc, simple closed curve, sequential limit, simple chain, and Axioms 1–8 and 5₁ are all
  defined from regions.
* **The overbars in Axioms 1, 6 and 7 denote second objects (`P̄`, `R̄`, `K̄`, `L̄`), not
  closures.** pdftotext drops them; the skeleton follows the page image. Check against p. 132.

**B. F.A. §3, Theorems 1–10, and "M′ is closed"** (skeleton §2). The hypotheses are those of the
section heading: Axioms 1–3 and 5₁. For each theorem, record which axioms the proof uses.

**C. F.A. §4, Theorems 11–16** (skeleton §3). Hypotheses: Axioms 1–4, 5. Theorem 15 is Moore's own
construction of an arc by nested simple chains (pp. 136–139). Formalize that proof.

**D. The bridge** (skeleton §4). Under Axioms 1–4 and 5₁, show that:
* the regions form a basis;
* Moore's limit point, closed, connected and Heine–Borel are the topological notions for the
  generated topology, and `M′` is the closure;
* the space is metrizable (T2, regular, second countable, then Urysohn).

If some identification needs more axioms, say which.

**E. Arcs** (skeleton §5).
* `isIrreducibleConnected_iff_arc`, in a metrizable space. Prove it from the standard argument
  (non-cut points; the order on an irreducible continuum; the separable dense order gives
  `[0, 1]`). Any correct route is fine.
* `isArc_iff`: Moore arcs are embedded `[0, 1]`'s.
* The unnumbered facts of pp. 139–140, each as its own lemma, via `isArc_iff`:
  * splitting an arc at a point;
  * the unique interval `XY`;
  * first and last points on a closed set;
  * limit points along an arc;
  * the two arcs between two points of a simple closed curve.
* Theorems 17–19.

## 3. Places to check (candidate ledger entries)

1. **Connected (p. 132).** "However it be divided into two mutually exclusive subsets": the parts
   must be nonempty, or every set is disconnected. The skeleton includes this. Confirm it is
   needed.
2. **Theorem 1** has no proof. It needs no axiom: `R` itself is a region containing `P` with
   `R − R = ∅`. Check.
3. **No proof printed:**
   * Theorems 1, 3, 7, 11, 16 and 18;
   * Theorem 13 ("see Hausdorff, *Grundzüge*, p. 231");
   * Theorem 17 ("a consequence of Axiom 5 and Theorem 13");
   * "It is clear that … `M′` is closed" (p. 135).

   Record what each proof needs.
4. **Theorem 14.** The proof opens with "For each `n`, `Mₙ` contains at least one point", but this
   is not a hypothesis. If every `Mₙ` is empty, the printed statement fails. Refute the printed
   form, or show why it is not needed. The skeleton carries `hne`.
5. **Theorem 5:** "It is clear that the sequence … satisfies conditions (1), (2), and (3)". Check
   (1): the intersection is exactly `{P}`.
6. **Theorem 9** invokes "Zermelo's postulate". It is fine in Lean; noted for the exposition.
7. **Theorem 15, part III:** the ordering of the points of `C`. The steps "Furthermore it is clear
   that …" and "It is clear that `S_A` contains `A`" (p. 138) need arguments. Supply them.
8. **Theorem 16, second half:** two points *without* `R` are joined by an arc without `R`. This
   needs the exterior to be a domain: open by Theorem 1 and Axiom 1, connected by Axiom 3. Check
   that this is what is meant.
9. **Section 6's first sentence (p. 140):** "It is clear that Theorems 1–19 are consequences of
   Axioms 2–5 and Theorems 5 and 15". Not to be formalized. Record whether your proofs bear it out.

## 4. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch137.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction recorded in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for F.A. §§2–5 with the outcome of each check in §3. Quote the
   printed sentence each time.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * for each theorem, the axioms actually used;
   * what batch 138 (F.A. §6, Theorems 20–35) needs from this one.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   Nothing goes at the root.
