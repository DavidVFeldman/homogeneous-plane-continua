# Commission: batch 102 — Sorgenfrey's theorem (Nadler 11.22–11.35)

**Go!** Runs on top of the batch-101 delivery. Four files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch102.md` — this text (also pasted into the prompt);
* `Sorgenfrey.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Sorgenfrey.lean` and add `import HPC.Plane.Sorgenfrey` at the end of the root
  `HPC.lean`. No existing file is to be edited. Shapes may be adjusted with the change recorded;
* `nadler-11-22-to-11-35.pdf` — the source, pp. 208–222 of Nadler, *Continuum Theory* (1992), as
  page images (read these; the bars that mark closures do not survive OCR);
* `nadler-11-26-to-11-35.txt` — the OCR text of the same pages, for searching only.

The report names the commission read in its first line.

## 0. On batch 101

Audited: Fugate's Theorem 1 proved under his own hypotheses, with Lemma 2 corrected (Definition 5
now exact, with the witness points), Lemma 4 in weak-chain form, the gluing chain checked, and
the gaps in Fugate's text named; Miller 1.5 as cited refuted on the disk, and the consequence
Fugate needs proved directly (`isHereditarilyUnicoherent_union`), with unicoherence of
contractible spaces as a by-product; Corollary 1 under hereditary unicoherence; Corollary 2.
Standard axioms. The one `sorry` left in the Fugate files is Sorgenfrey's irreducibility theorem,
used only in Lemma 3 (⇒). This batch is that theorem, in Nadler's stronger form.

## 1. The source

Nadler's statement (11.34): *every nondegenerate unicoherent continuum which is not a triod is
irreducible.* Its proof runs through 11.23 (essential sums), 11.24 (weak triods), 11.25,
11.26 (for unicoherent continua, triod ⇔ weak triod), 11.27–11.28 (complements of summands are
connected), 11.29–11.30 (`irr(A, B)` and its existence), 11.31–11.33, and the three-page argument
of 11.34, which contradicts "not a weak triod" three times. Nadler's triod (11.22) is batch 92's
`IsTriod` (a subcontinuum whose complement is three mutually separated nonempty sets). The
notation: `X = Y ⊕ Z` means `X = Y ∪ Z` with `Y`, `Z` proper subcontinua; `U = X − Z` and
`V = X − Y` are open, and `Ū`, `V̄` their closures; `irr(A, B)` as in 11.29.

The skeleton transcribes 11.25–11.35 with the bars placed as on the page images (checked for
11.27, 11.28, 11.31, 11.32, 11.33: `p ∈ U − A` with `U` open; `A ⊇ Ū ∩ Z`; `A ∪ B ⊇ U`;
`W = U − A` and `W̄ = E ⊕ F`; `p ∈ U`, `q ∈ V` in 11.33). If a statement as transcribed is wrong,
say so against the page.

## 2. Items

1. **11.25–11.26** (`isWeakTriod_of_isTriod`, `isTriod_iff_isWeakTriod`), and the remark after
   11.24 (`not_irreducible_of_isWeakTriod`, via 11.5: an irreducible continuum is not the union
   of two proper subcontinua both containing a point of irreducibility — batch 83's
   `IsIrreducibleBetween` gives this directly).
2. **11.27–11.28.** 11.27 uses Nadler 6.3 (batch 94's `isConnected_union_of_separation`) and
   Moore's separation theorem 5.2 (batch 101's `exists_closed_split_of_no_connected`). Note the
   closures in (1)–(8) of the proof.
3. **11.29–11.30** (`IrrFromTo`, `exists_irrFromTo`): Brouwer reduction (batch 93's
   `exists_minimal_of_seq`) on subcontinua meeting both `A` and `B`.
4. **11.31–11.33.** Transcribe from the page images. 11.31's proof uses boundary bumping (Nadler
   5.7; batch 91's `exists_subcontinuum_meeting_closedBall` or the `Fold` boundary-bumping lemma).
5. **11.34** (`sorgenfrey`). Reduction to the decomposable case by 11.15.1 (indecomposable
   continua are irreducible: a point not in the composant of `p` — batch 83's
   `composant_ne_of_indecomposable` or the repository's composant facts). Then (a) and (b) by
   contradiction: the induction defining `p_{n(i)}`, `K_i`, `U_i` from a countable dense subset
   of `U` (second countability), the facts (7)–(9), the decomposability of each `U_i` (12),
   the claim (*) with the triod `A = Z ∪ J`, `B = E ∪ J`, `C = F ∪ J`, and the final triod
   `Z ⊕ K_n ⊕ (Q ∪ U_n)`. Name every place where the text needs more than it says, as for Bing
   and Fugate. If the whole does not close, prove 11.34 conditionally on the least lemma that
   remains and say which.
6. **11.35** and the two Fugate consequences (`sorgenfrey_irreducible_of_atriodic_hu`,
   `isTerminalSub_iff_irreducible'`).

Report each item *proved / refuted / open with the obstruction stated*; refutations first.

## 3. Deliverables

1. Items 1–6; `#print axioms` in `axioms-batch102.txt`.
2. Report: first line names the commission read; items in order; the ledger of Nadler's text.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
   `isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.

## 4. Next

Fugate 1969 (Theorem 11 of Bing's Duke paper) when supplied; then the pruning pass.
