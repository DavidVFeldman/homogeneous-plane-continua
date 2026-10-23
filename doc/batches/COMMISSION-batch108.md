# Commission: batch 108 — the arcs paper's Theorem 5 and Corollary 2; Duke Theorem 12 in Bing's generality

**Go!** Runs on top of the batch-107 delivery. Three files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch108.md` — this text (also pasted into the prompt);
* `Arcs48.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Arcs48.lean`
  and add `import HPC.Plane.Arcs48` at the end of the root `HPC.lean`. No existing file is to be
  edited, except `Axioms.lean`/`axioms.txt` (add a group "Bing 1948, Amer. J. Math." and the
  general Theorem 12 to the Duke group). Shapes may be adjusted with the change recorded;
* `bing1948-arcs.pdf` — R. H. Bing, *Some characterizations of arcs and simple closed curves*,
  Amer. J. Math. 70 (1948) 497–506; read pp. 497 (definitions) and 500–501 (Theorem 5,
  Corollary 2) from the scan.

The report names the commission read in its first line.

## 0. On batch 107

(Audited separately when it arrives; this commission does not depend on it beyond the import.)

## 1. The text

[Quotation moved to doc/sources/transcriptions/bing48arcs.md, §doc/batches/COMMISSION-batch108.md, 1. The text; batch 204.]

**Corollary 2 (p. 501).** *Each nondegenerate compact continuum contains two points neither of
which cuts between two open subsets of the continuum.* (No proof given; from Theorem 5 with
`R = {r}`, applied twice? — determine the argument and record it.)

## 2. Items

1. `exists_irreducibleAbout` (Zorn; batch 93's Brouwer reduction or batch 83's
   `exists_irreducible` pattern).
2. **Theorem 5** (`arcs_theorem5`, `arcs_theorem5_point`). Points to settle, in order:
   * the first case (`M = N`) is a contradiction argument that produces, for the chosen `p`,
     density of the union: make explicit how "no such `E`" yields density (for every open `E` of
     `N` some subcontinuum meeting `Ē` and `R` avoids `p` — so the union meets `Ē`? it meets
     `Ē`, and density needs it to meet `E`; check);
   * "each component of `N − E` which contains a point of `R` also contains `p`" and "then there
     is a continuum in `N − E` containing `R`": the union of those components with `p` is
     connected; it must also be closed — components of the closed set `N − E` are closed, but
     their union over possibly infinitely many components need not be; state what is used
     (boundary bumping, or a finite subfamily by compactness of `R`?);
   * the second case: "`a point of M − ΣN_i`" needs `ΣN_i ≠ M`. An increasing union of proper
     subcontinua can be all of `M` (the cone over `{0} ∪ {1/n}`, with `N_k` the cone over the first
     `k` points and the segment to `0`). Decide whether Bing's choice of the `N_i` excludes this
     (each `N_{i+1}` has an *open subset containing* `N_i ∪ D_i`), and if not, how the case is
     handled (Baire: if `⋃ N_i = M`, some `N_k` has interior … then?). If the statement needs a
     different argument here, give it and record the gap;
   * "For convenience, suppose that `ΣN_i = N`" — justify the reduction, or restructure;
   * `E_i · F_i` contains no open subset of `M` (since `E_i` is a component of the open set
     `M − D_i`, `F_i = cl (M − E_i)`, and `E_i ∩ F_i ⊆ ∂E_i`): check `E_i` is open (components of
     open subsets of a compact metric continuum need not be open!) — this is a likely gap: if
     `E_i` is not open, `E_i ∩ F_i` can have interior. Record what is true and what the proof
     needs (perhaps `E_i` should be replaced by the quasi-component or the proof reorganized);
   * "`F_i + N` is a continuum": the argument via `X + E_i`; and `G_i` is a continuum missing `p`
     meeting `R`; "`ΣG_i` is dense": each `D_i`'s points are approached — check.
   Prove the theorem by whatever correct route is closest to Bing's; record every deviation. The
   point form `arcs_theorem5_point` is what batch 106's note needs.
3. **Corollary 2** (`arcs_corollary2`).
4. **Duke Theorem 12, general** (`condA_of_condB_general`, `theorem12_1951_general`), by Bing's
   proof as transcribed in COMMISSION-batch106.md §1, with `arcs_theorem5_point` in place of
   "Theorem 5 of [4]"; `M'` ranges over nondegenerate subcontinua through `p`; condition B makes
   the family nested, so the union is connected and its closure is a continuum, equal to `M'` by
   density.

Report each item *proved / refuted / open with the obstruction stated*; refutations first; the
ledger of the arcs paper's Theorem 5 (every gap above, settled one way or the other).

## 3. Deliverables

1. Items 1–4; `#print axioms` in `axioms-batch108.txt`; `axioms.txt` regenerated (`sorryAx`
   still in 9).
2. Report: first line names the commission read; items in order; the ledger.
3. Not attempted: the five open targets; the arcs paper's Theorems 1–4, 6–13 (its arc and
   simple-closed-curve characterizations may serve the parked `isArc_of_separatesPairs` later).

## 4. Next

The density lemma `exists_tame_chain_near` in the plane (polygonal arc tracing + tube).
