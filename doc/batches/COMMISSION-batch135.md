# Commission: batch 135 — Part D, foundations: Jones 1948 complete; Jones 1951, the Lemma (and Theorem 1)

**Go!** Runs on top of the batch-134 delivery. Five files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch135.md` — this text (also pasted into the prompt);
* `Jones48.lean` — a skeleton, `sorry`s as work items. Save it as `HPC/Jones/Jones48.lean` (a new
  directory) and add `import HPC.Jones.Jones48` at the end of the root `HPC.lean`. Splitting into
  several files under `HPC/Jones/` is expected.
* `jones1948.pdf` — F. B. Jones, *Concerning non-aposyndetic continua*, Amer. J. Math. 70 (1948),
  403–413. Save it as `doc/sources/jones1948.pdf`.
* `jones1951.pdf` — F. B. Jones, *Certain homogeneous unicoherent indecomposable continua*, Proc.
  AMS 2 (1951), 855–859. Save it as `doc/sources/jones1951.pdf`.
* `jones1955.pdf` — F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6
  (1955), 735–740. Save it as `doc/sources/jones1955.pdf`. It is for reference only; it is the
  target of the next batches.

Shapes may be adjusted, with each change recorded. The report names the commission read in its
first line. Each item is reported as *proved*, *refuted*, or *open with the obstruction stated*.
No existing file is edited except `HPC.lean`, `Axioms.lean` and `axioms.txt` (new group "Jones
1948, 1951 (batch 135)"), `README.md` (a Part D line and the batch count), `LEDGER.md` (§6), and
`OPEN.md` only if something is left open.

## 0. On batch 134

Audited and accepted: the Effros theorem, Ungar's corollary and the Polish homeomorphism group.
Part C is done: 717 lines, `sorryAx` in none.

Your reading of the scan was right. The Lemma 3.4 "gap" was mine: I transcribed from extracted
text, which drops overlines. The ledger records it, and I have adopted a rule: transcriptions
from now on are made from page images rendered at 200 dpi or more. The statements in this
commission and skeleton were transcribed that way.

## 1. Where this sits

Part D is Jones's decomposition theorem (Jones 1955). A decomposable homogeneous plane continuum
is a circle of mutually homeomorphic indecomposable homogeneous continua, unless it is a simple
closed curve. The plan:

* **This batch.** Jones 1948, in full. Jones 1955 cites its Theorems 1, 3, 6, 9 and the corollary
  on p. 409; the 1949 note cites Theorem 18; the rest is cheap once these are done. Also Jones
  1951's Lemma, which Jones 1955 cites twice as "the lemma of [5]".
* **Next.** Jones 1955, Theorem 1. Any decomposable homogeneous compact metric continuum: the sets
  `L_x` form a continuous decomposition, homogeneous and aposyndetic as a space. This needs
  decomposition spaces (item C below starts them).
* **Then.** Jones 1955, Theorem 2 (the plane). It needs Moore's decomposition theorem, from
  Moore's *Foundations*, which I have asked David for, and Jones 1949 (homogeneous + aposyndetic
  plane continuum ⇒ simple closed curve).

**Convention.** Jones's `M` is the whole space `X`, a compact connected metric space, as in
`HPC.Effros`. Subcontinua are subtypes.

## 2. Items

**A. Jones 1948** (skeleton §§1–5). Definitions: `AposAt`, `AposyndeticAt`, `IsAposyndetic`,
`TotallyNonAposyndetic`, `SemiLocConnAt`, `CutsPts`, `IsWeakCutPoint`, `IsStrongCutPoint`,
`composant`, `IsDecomposableSpace`. Theorems 0–19 and the three Corollaries. Examples 0–3 are not
required.

* Use what the repository has: `Fold.Q78.IsContinuum`, boundary bumping, irreducibility,
  composants (Bing 1948 Thms 10–11, Pacific), `Fold.Q78.IsIndecomposable`, Bing's arcs paper
  (`HPC/Plane/Arcs48.lean`: `Cuts`, `arcs_corollary2`), and Sorgenfrey.
* Where the repository has an equivalent definition (decomposable/indecomposable, composant),
  prove the equivalence rather than duplicating it.
* Order of priority: Theorems 1, 2, 3, 6, 8, 9, the p. 409 Corollary (via 10, 11, 12), then 13–19,
  then 0, 4, 5, 7.

**B. Jones 1951** (skeleton, last section).
* `aposSet`, `isOpen_aposSet` ("It is evident").
* `IsHomogeneous`. If `HPC.Effros` or Mathlib already has an equivalent, use it.
* **`jones51_lemma`** — the item that matters for Jones 1955.
* `jones51_theorem1` is a stretch item; see C.

**C. Decomposition spaces (stretch, only for `jones51_theorem1`).** Jones forms `G` "with respect
to its elements as points" as a continuum `M′`. What is needed: an upper semicontinuous
decomposition of a compact metric space into closed sets has a compact metrizable quotient, and
the quotient map is closed. Mathlib's quotient by a setoid, plus `T2` and second countability,
then metrization. If it fits, state it in the general form, since Jones 1955 needs it next batch.
If not, leave `jones51_theorem1` open with the obstruction stated.

## 3. Places to check (candidate ledger entries)

* **Theorems 2, 3, 5 and 0: no proof printed.**
  * Theorem 2 has no proof at all.
  * Theorem 3 has no proof either, and Jones 1955 relies on it.
  * Theorem 5 is "similar to Theorem 4"; Theorem 0 is "with the help of the Heine–Borel theorem".

  Record what the proofs need.
* **Theorems 15, 18 and 19: proof sketches only.**
  * 15 is "with the help of Theorems 0 and 13";
  * 18 is "with the help of Theorems 4, 5, 12, and 15";
  * 19 "follows from Theorem 15".
* **Theorem 10: as printed it is false.** `D` may be empty, and then the condition holds in every
  continuum. Prove the corrected form with `D` nonempty, and refute the printed form for a
  decomposable continuum (an arc, say).
  * Theorems 11, 12, 13 and 19 also need `D` (resp. `U`) nonempty. Without that their conclusions
    are false; in the skeleton they carry `hDne`.
  * Check Theorem 6 too. As printed, its conclusion asks for `x₀ ∈ D`, so `D = ∅` falsifies it
    whenever `M₀ ≠ X`.
* **Theorem 14: "Follows immediately from Theorem 13."** Theorem 13 gives three points in a given
  open `D`. Density of weak cut points needs it for every nonempty open `D`; check that this is
  immediate.
* **Theorem 16: notation.** The text says "the composant of `M` containing `P`" while `p` is the
  weak cut point (`P` vs `p`).
* **Jones 1951, Lemma: two steps to check.**
  * "Evidently `x_ω ≠ xₙ`".
  * The transfinite continuation. At a limit stage, `x_λ` is a limit point of a countable
    subsequence, and `U_{x_λ} ⊆ U_{x_i}` for all earlier `i` (the argument given at `ω`).
  * The contradiction: no strictly monotone `ω₁`-sequence of open sets in a second countable
    space. Formalize it with `Ordinal`/`Cardinal`, or by a direct countability argument, whichever
    is cleaner. Alternatively, find a proof without transfinite recursion and report it.
* **Jones 1955 citations, for the record (not to be formalized here).**
  * Its last step of Theorem 2, "by [5]" (Jones 1951), appears to be a citation slip. The result
    used (homogeneous + aposyndetic plane continuum ⇒ simple closed curve) is Jones 1949, Theorem
    1, cited as [3] in the introduction.
  * Its continuity step ("`G` must be continuous at one of its elements") uses an unstated
    theorem: an upper semicontinuous decomposition is continuous at a residual set of elements.

  Note both in the report if you see the same thing.

## 4. Deliverables

1. Items A and B (C if reached).
   * Write `#print axioms` output to `doc/batches/audits/axioms-batch135.txt`, and regenerate
     `axioms.txt`. `sorryAx` should still appear in no line; anything left open is commented out,
     with its obstruction stated, as in batch 132.
   * `LEDGER.md` §6: a subsection for Jones 1948 / 1951. It records refutations (Theorem 10 as
     printed), missing proofs and implicit hypotheses.
2. The report. Its first line names the commission read. It covers:
   * items in order;
   * the ledger entries;
   * what Jones 1955 Theorem 1 will need from the decomposition-space side.
3. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   at the root.
