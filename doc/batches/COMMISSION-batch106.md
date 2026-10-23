# Commission: batch 106 — Duke 1951 Theorem 12 (B ⇒ A), Theorem 13 in full, and the "two end points" claim

**Go!** Runs on top of the batch-105 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch106.md` — this text (also pasted into the prompt);
* `Thm12B.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Thm12B.lean`
  and add `import HPC.Plane.Thm12B` at the end of the root `HPC.lean`. No existing file is to be
  edited, except: add the new theorems to `Axioms.lean` (Duke group) and regenerate `axioms.txt`;
  update `README.md`'s one-line summary of the Duke paper if it lists Theorem 12 as half done.
  Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 105

Audited: the housekeeping exactly as asked; 229 declarations, `sorryAx` in 9 lines, five `sorry`
warnings. The stale docstring line in `Theorem11B.lean` (line 8, naming the deleted
`theorem11_1951_of_T10'`) may be fixed in this batch since the file is touched by the import.

## 1. The text (p. 661)

**Theorem 12.** *Conditions A and B are equivalent.* Proof: "If `H` and `K` are two continua such
that neither of them contains the other and each of them contains `p`, `H + K` is not irreducible
from `p` to any point. Hence, condition A implies condition B. Suppose `M'` is a nondegenerate
subcontinuum of `M` containing `p`. By Theorem 5 of [4] there is a point `q` of `M' − p` such that
the sum of all continua in `M' − q` containing `p` is dense in `M'`. Condition B implies
condition A because if `p` satisfies condition B, `M'` is irreducible from `p` to `q`. If `H` were a
proper subcontinuum of `M'` containing `p + q`, there would be a continuum `K` in `M − q` such that
`K` contains `p` but is not a subset of `H`. But neither `H` nor `K` would contain the other."

[4] is Bing, *Some characterizations of arcs and simple closed curves*, Amer. J. Math. 70 (1948);
its Theorem 5 is not available here. **Replacement**, with what the repository has: let `M'` be a
nondegenerate subcontinuum of `M` through `p`. Condition B for `M` at `p` restricts to `M'` and
says `{p}` is a terminal subcontinuum of `M'` (`isTerminalSub_singleton_iff`). `M'` is snake-like
(`isSnakeLike_of_subcontinuum`), hence atriodic and hereditarily unicoherent
(`isAtriodic_of_isSnakeLike`, `isHereditarilyUnicoherent_of_isSnakeLike`). Fugate's Lemma 3 (⇒)
(`isTerminalSub_iff_irreducible`, batches 100/102) applied with `B := M'` gives points `p' ∈ {p}`,
`q` with `{p} ∪ M' = M'` irreducible between `p` and `q`; `q ≠ p` since `M'` is nondegenerate.
That is condition A. So the citation of [4] is replaced by Sorgenfrey's theorem through Fugate's
Lemma 3; record this in the ledger as the route taken, not as a defect of Bing's.

**Theorem 13.** *A necessary and sufficient condition that a point `p` be an end point of a
snake-like continuum `M` is that it satisfy either condition A or condition B.* Proof: "The
sufficiency follows from Theorems 10, 11, and 12. To see that the condition is necessary, …"
(necessity is batch 85's `condB_of_endPoint`). Note Bing's "Theorems 10, 11, and 12": Theorem 11
(atriodic + HU + HD ⇒ snake-like) plays no role here; "10 and 12" is what is used — record as a
slip in the text.

**The unnumbered claim.** "We find from Theorems 8, 9, and 13 that each hereditarily decomposable
snake-like continuum contains two end points between which it is irreducible." Route: `S`
snake-like and hereditarily decomposable gives `BingS` (necessity of Theorem 11 + `hd`);
`exists_two_endElts` gives end elements `g_a ≠ g_b`; `theorem9_1951` gives condition-A points
`p ∈ g_a`, `q ∈ g_b`; Theorem 13 makes them end points; `p ≠ q` since the elements are disjoint;
`bingElt_irreducible` (Theorem 8 (c)) gives irreducibility between them (a subcontinuum containing
`p` and `q` meets both end elements, so it is `S`). Then Theorem 14 (`theorem14_1951`) makes them
opposite end points — Bing's next sentence.

## 2. Items

1. `condA_of_condB`, `theorem12_1951`.
2. `theorem13_1951`, `theorem13_1951'`.
3. `exists_two_endPoints_irreducible`, `exists_oppositeEndPoints_of_hd`.
4. Audit and README as in the header. Report the ledger notes above and any further step the
   text leaves out.

## 3. Deliverables

1. Items 1–4; `#print axioms` in `axioms-batch106.txt`; `axioms.txt` regenerated (expected 235
   lines, `sorryAx` still in exactly 9).
2. Report: first line names the commission read; refutations first (none expected); items in
   order.
3. Not attempted: the five open targets.

## 4. Next

Duke Theorem 5 (uncountably many disjoint planar copies of a snake-like continuum), by a
branching construction inside the rectangle chains of Theorem 4's proof — no plane topology
beyond what the repository has.
