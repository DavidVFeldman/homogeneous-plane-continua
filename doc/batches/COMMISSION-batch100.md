# Commission: batch 100 — Fugate 1966: terminal subcontinua, Lemma 1 in general, Theorem 1 (gluing), corollaries; housekeeping

**Go!** Runs on top of the batch-99 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch100.md` — this text (also pasted into the prompt);
* `Fugate66.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Fugate66.lean` and add `import HPC.Plane.Fugate66` at the end of the root
  `HPC.lean`. Shapes may be adjusted with the change recorded.

Two edits to existing files are permitted and requested (item 0). The report names the
commission read in its first line.

## 0. Housekeeping: the stale duplicates

Batch 99 proved Theorem 10 as `theorem10_1951'` and Theorem 13's sufficiency as
`endPoint_of_condA'`; the originals in `HPC/Plane/EndPoints51.lean` keep a `sorry` only because
of import order, and nothing outside that file and `LastLink99.lean` refers to them except
docstrings (checked: `Recon91.lean`, `Theorem11.lean` mention them in comments only).

1. Delete `theorem10_1951` and `endPoint_of_condA` (the two `sorry` declarations) from
   `HPC/Plane/EndPoints51.lean`; adjust its module docstring in one sentence; nothing else there
   changes.
2. In `HPC/Plane/LastLink99.lean` rename `theorem10_1951'` → `theorem10_1951` and
   `endPoint_of_condA'` → `endPoint_of_condA`, keeping the primed names as `alias`es.
3. Report `#print axioms` for `theorem10_1951`, `endPoint_of_condA`, `theorem11_1951_of_T10` in
   `axioms-batch100.txt`.

If a build error shows a dependence I missed, stop the edit, restore, and report it instead.

## 1. The source

Fugate 1966, §2–4 (text in COMMISSION-batch99.md §1 for Lemma 1; the rest verbatim here).

[Quotation moved to doc/sources/transcriptions/fugate66.md, §doc/batches/COMMISSION-batch100.md, Fugate 1966, §2–4; batch 204.]

**Lemma 4 and Theorem 1**: as in Fugate's pp. 465–467 (text in `/tmp/claude-0/fugate.txt` is
garbled; the structure: taut `ε`-chain `G` of `A` with `A ∩ B` exactly in `G(j,m)` (Lemma 2);
`ε''`-chain `H` of `B` with `A ∩ B` exactly in `H(k,n)`, `ε''` small enough that closures of
`H(k,n)`-links lie in single links of `G(j,m)` and miss `Cl G*(1,j−1)`; separate `A − B` from
`B − A` by open `S`, `T`; `F_i = H_i ∩ T` for `i < k`, `F_i = H_i` for `i ≥ k`; `E_i = G_i ∩ S` for
`i < j`, `E_i = G_i − Cl F*(1,k−1)` for `i ≥ j`, `i ≠ t`, `E_t = G_t − Cl F*(1,k−2)` where `t` is the
least index with `Cl H_k ⊆ G_t`; properties (1)–(6). Theorem 1: Claim 1 (`A ∩ B` terminal in `A`
and `B`, by Sorgenfrey's lemma); Case i (`t = m`): the chain is `E ⊕ F(k−1, 1)`; Case ii: the
index `r`, the sets `D`, Claims 2–3, Moore Thm 44 again, open `S`, `T`, and the displayed chain
`E(1,j−1) ⊕ E(j,m−1) ∩ S ⊕ E_m ⊕ F(r−1,k) ∩ T ⊕ (F_{k−1} ∩ T) ∪ (F_{k−1} − Cl E*) ⊕ F(k−2,1)`.)
Read the scan pages 465–467 directly (the PDF is attached to the session as
`fugate1966.pdf`; the OCR of those pages is unreliable).

**Corollary 1** (finite unions along a chain of continua) and **Corollary 2** (decomposable,
unicoherent, all proper subcontinua chainable ⇒ chainable; proof: `M` is not a triod — a triod
`A ∪ B ∪ D` gives, via a subcontinuum `D''` of `D` irreducible from a point of `A ∩ B` and the
density of its composant, a triod `D'' ∪ (A ∩ B), A, B` of proper… — follow the text; then
Theorem 1).

## 2. Items

1. **Definitions and comparisons**: `IsTerminalSub`; `isTerminalSub_singleton_iff` (Definition 4
   at a point is condition B); `IsFugateTriod` vs batch 92's `IsTriod` (`isFugateTriod_iff_isTriod`:
   prove the equivalence or the direction(s) that hold, with the obstruction).
2. **Sorgenfrey's two facts.** `isTriod_union_of_three` (three pairwise-meeting continua, none in
   the union of the other two, form a triod — in Bing's sense; batch 92 proved it under `BingS`
   as property 3's contrapositive; here with no hypothesis) and
   `exists_irreducibleBetween_of_atriodic` (atriodic + HU ⇒ irreducible between two points;
   Sorgenfrey 1944; Nadler 11.35 is a related characterization). The second is the one place
   where a classical theorem outside the repository is needed; prove it or state the obstruction.
3. **Lemma 3** (`isTerminalSub_iff_irreducible`).
4. **Lemma 1 in general** (`fugate_lemma1`) and **Lemma 2** (`fugate_lemma2`). For the point case
   this is batch 99; the general case replaces condition A by terminality: irreducibility from
   `p ∈ A` to `q ∉ A` comes from Lemma 3, the composant density from batch 91
   (`exists_proper_subcontinuum_meeting`), the counting argument from batch 99's consolidation
   (does `exists_shorter_T10Chain` apply with `A` in the last link in place of `p` in the first?
   the "`p` stays in the first link" clause becomes "`A` meets the last link outside the closure
   of the previous one" — check), and the surgery from batch 91 (`theorem10_1951_of_lastLink`
   was stated for a point `p` with condition B; a set version is needed — state it).
5. **Theorem 1** (`fugate_theorem1`), **Corollaries 1–2**. Tautness: Fugate carries it through
   Lemma 4; decide whether it is needed (the disjointness of nonadjacent links' closures is what
   is used) and either prove `exists_taut_epsChain` (Barrett) or do without it, recording which.
6. Report each item *proved / refuted / open with the obstruction stated*; refutations first.

## 3. Deliverables

1. Item 0; items 1–5; `#print axioms` in `axioms-batch100.txt`.
2. Report: first line names the commission read; refutations first; item 0; items 1–5 with the
   gaps in Fugate's text named (as for Bing's).
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
   `isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.

## 4. Next

Fugate 1969 (Theorem 11 proper) when supplied; otherwise 1948 Theorem 14 (`covering_step`)
revisited with the chain tools of batches 96–99.
