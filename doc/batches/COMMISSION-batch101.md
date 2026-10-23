# Commission: batch 101 — Fugate 1966: Lemma 2 corrected, Miller's theorem, Lemma 4, Theorem 1 (sufficiency), Corollary 1

**Go!** Runs on top of the batch-100 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch101.md` — this text (also pasted into the prompt);
* `Fugate66B.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Fugate66B.lean` and add `import HPC.Plane.Fugate66B` at the end of the root
  `HPC.lean`. No existing file is to be edited. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line. The scan of Fugate's paper was not
available to the batch-100 run; this commission transcribes the pages needed, from the scan,
below. Everything in §1 is Fugate's text (1-indexed chains, his notation; `E*(a,b)` is the union
of the links `E_a, …, E_b`; `Cl` is closure; `⊕` concatenation; `E(1,m) ∩ S` the chain of links
`E_i ∩ S`).

## 0. On batch 100

Audited: housekeeping done; Lemma 1 proved in general and without Lemma 3, atriodicity or
hereditary unicoherence; Lemma 3 (⇐) unconditional, (⇒) conditional on Sorgenfrey's irreducibility
theorem (open); Claim 1 of Theorem 1 proved with the gap named (Sorgenfrey's lemma is applied
inside a merely unicoherent `A ∪ B`; the core lies in the hereditarily unicoherent `A`); Barrett's
taut chains; Corollary 2 from Theorem 1's sufficiency. Two refutations of my transcriptions
(Fugate's triod needs a connected core; Sorgenfrey's lemma needs a hereditarily unicoherent
ambient), both recorded as mine. Lemma 2 was proved in a form weaker than Fugate's Definition 5,
because my `ContainedExactly` omitted "`A` meets the last link"; corrected here.

## 1. Fugate's text (pp. 463–467)

[Quotation moved to doc/sources/transcriptions/fugate66.md, §doc/batches/COMMISSION-batch101.md, 1. Fugate's text (pp. 463–467); batch 204.]

## 2. Items

1. **Lemma 2 corrected** (`ContainedExactly'`, `fugate_lemma2'`): Definition 5 with full clause
   (2). From batch 100's `fugate_lemma1` and the paragraph above.
2. **Miller's theorem** (`miller_1_5`), as Fugate cites it, and the consequence actually used
   (`hu_union_of_snakeLike`: `A`, `B` snake-like, `A ∪ B` unicoherent ⇒ `A ∪ B` hereditarily
   unicoherent). Prove or refute each; the bare `miller_1_5` as transcribed may be false (two
   half-disks), in which case say which hypothesis of Miller's restores it — his paper
   (H. C. Miller, *On unicoherent continua*, Trans. AMS 69 (1950) 179–194) is not available
   here — and prove `hu_union_of_snakeLike` by whatever route works (Claim 1-style: a
   non-unicoherent subcontinuum `D` of `A ∪ B` meeting both `A − B` and `B − A` has `D ∩ A`,
   `D ∩ B`… — but `D` is not known to be hereditarily unicoherent, which is what Claim 3 of
   Theorem 1 uses; this is the circularity to resolve). Note that Theorem 1's proof uses
   hereditary unicoherence of `A ∪ B` only in Claim 3 (for `M ⊆ D`); if `hu_union_of_snakeLike`
   stays open, prove Theorem 1's sufficiency with `IsHereditarilyUnicoherent (A ∪ B)` as the
   hypothesis instead of `IsUnicoherent`, under a separate name, and record it.
3. **Lemma 4** (`fugate_lemma4`), 0-indexed as in the skeleton (clause (6) guarded by `1 ≤ k`;
   say how `k = 0`, i.e. `A ∩ B` reaching the first link of `F`, is handled — it may be excluded
   by Lemma 2's construction, or the clauses are vacuous). Tautness via batch 100's
   `exists_taut_epsChain` and its preservation under the cuts. Report where Fugate's text needs
   more than it says (candidates: that `E_i = G_i − Cl F*(1,k−1)` still meets `E_{i+1}`; that the
   cut links still cover `A`; the Lebesgue-number step for links *meeting* `A ∩ B` versus
   Lemma 2's exact containment).
4. **Theorem 1, sufficiency** (`fugate_theorem1_sufficiency'`): Cases i and ii; Claims 2–3; the
   separation (batch 94's `exists_clopen_split`/Moore Thm 44 as in the Surgery91 file); the
   displayed chain `𝒢` with its adjacency check. The "for notational convenience assume `E' = E`"
   step is a genuine re-run of Lemma 4's conclusion for `E'`; check that `E'` keeps (1)–(6).
5. **Corollary 1** (`fugate_cor1'`): with the hypothesis under which the induction through
   Theorem 1 runs (hereditarily unicoherent union), or Fugate's if item 2 provides hereditary
   unicoherence of partial unions. Record which.

Report each item *proved / refuted / open with the obstruction stated*; refutations first; name
the gaps in Fugate's text as they are met.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch101.txt`.
2. Report: first line names the commission read; items 1–5 in order.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
   `isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`,
   `exists_irreducibleBetween_of_atriodic` (Sorgenfrey).

## 4. Next

Fugate 1969 (Theorem 11 proper) when supplied; Sorgenfrey's irreducibility theorem; then
1948 Theorem 14.
