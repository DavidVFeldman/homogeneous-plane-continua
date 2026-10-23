# Commission: batch 97 — Q-deg: a degenerate interior element of Bing's decomposition

**Go!** Runs on top of the batch-96 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch97.md` — this text (also pasted into the prompt);
* `Layers51.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Layers51.lean` and add `import HPC.Plane.Layers51` at the end of the root
  `HPC.lean`. If `exists_degenerate_interior_elt'` is proved, the `sorry` of
  `exists_degenerate_interior_elt` in `HPC/Plane/Theorem11.lean` may be replaced by a reference
  to it, or the statement moved here with the old name — that is the only permitted edit to an
  existing file; record it. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 96

Audited: Theorem 9 record closed; necessity of Theorem 11 proved; sides, condition A on a side,
degenerate separation, minimal counterexample, amalgamation (with the observation that Bing's
middle link can have diameter near `2ε`, repaired by a separate small link), Theorem 11 from
Theorem 10 and Q-deg. My `not_separation_of_accumulates` was refuted — `¬ g ⊆ N` was too weak —
and corrected with `¬ g ⊆ closure N`; the observation about Bing's nondegenerate branch stands in
that form. Standard axioms, one `sorry` (Q-deg). This batch is that one `sorry`.

## 1. The question

Bing (p. 660): "there is an uncountable collection `G'` of `G` such that if `g₁` and `g₂` are the
end elements of `G` and `g'` is an element of `G'`, there is a sequence of elements of `G`
converging to `g'` such that infinitely many elements of this sequence separate `g'` from `g₁` and
infinitely many separate `g'` from `g₂`." Then: "If `g'` is nondegenerate, let `p'` be a point
satisfying condition A for `M` equal to `g'`; otherwise, let `p'` be the only point in `g'`."

Batch 96 showed the nondegenerate branch cannot be completed as Bing writes it, and that the
degenerate branch completes (modulo Theorem 10). So Theorem 11 rests on: **some interior element
is a point.** The literature on layers ("tranches") of irreducible continua (Kuratowski,
*Topology* II, §48; E. S. Thomas, *Monotone decompositions of irreducible continua*, Rozprawy
Mat. 50, 1966) is the place where this is settled, but I have no text of it at hand and nothing in
Nadler covers it (his Chapter XI is composants and irreducibility only). So the question is put as
a reconnaissance with three parts, each answered *proved / refuted / open with the obstruction
stated*.

## 2. Items

**Q1 (`isContPt_congr`, `isMeagre_not_isContPt`).** Fort's theorem for the map `x ↦ bingElt x`:
the non-continuity points form a meagre set. The map is upper semicontinuous (`bingElt_usc`) with
compact nonempty values, and constant on elements. Fort's argument: for each `n`, the set
`A_n = {x : ∀ W ∋ x open, ∃ y ∈ W, bingElt x ⊄ thickening (1/n) (bingElt y)}` of points where
lower semicontinuity fails by `1/n` is closed and nowhere dense (closed: u.s.c. and a limit
argument; nowhere dense: if `A_n` contained an open set, pick inside it a point whose element is
"maximal" in a suitable sense… — follow Fort; the precise argument is the report's). Then
`{x : ¬ IsContPt x} ⊆ ⋃ A_n`, and `S` is a complete metric space, so Baire applies. Report the
lemma proved; if Mathlib has a form of Fort's theorem, say which.

**Q2 (`exists_contPt_not_endElt`).** The two end elements (`exists_two_endElts`,
`at_most_two_endElts`) are closed with empty interior (Theorem 8 (b)), so their union is meagre;
the complement of a meagre set in a Baire space is nonempty; take a continuity point outside both.
`IsEndElt` is a property of the element, so `¬ IsEndElt x` for the point `x` found.

**Q3 (`bingElt_degenerate_of_isContPt`) — the open core.** At a continuity point `x` that is not
an end element, `bingElt x = {x}`. Batch 96 derived (`subcontinuum_of_isContPt` here, to be
recorded as a theorem): every subcontinuum meeting `T = bingElt x` lies in `T` or contains `T`.
Questions, in order:

* (a) Is Q3 true? If a `BingS` space can have a nondegenerate element that is a two-sided
  Hausdorff limit of elements, construct one in Lean (the candidate shape: a continuous family
  of nondegenerate layers over an interval; the obstruction to such a family is likely hereditary
  unicoherence or atriodicity — a continuous family of nondegenerate continua tends to contain a
  "rectangle"), and then Theorem 11 needs a different route to its degenerate element (for
  instance only *one-sided* continuity, or Kuratowski's first-category theorem for the union of
  the nondegenerate layers, which is a different statement from Q3). If no such space exists,
  prove Q3.
* (b) What exactly is needed from hereditary decomposability? The batch-96 fact uses only (a)–(c)
  and u.s.c.; a nondegenerate `T` with "every subcontinuum meeting `T` is in `T` or contains `T`"
  is consistent with those (it holds for the bar of `S₀`, which is a one-sided limit from each
  side separately — or is it? check: `cl C₁` meets the bar and neither contains nor is contained
  in it; so the fact already fails for the bar of `S₀`, which is not a continuity point).
  Record what the fact plus HD plus two-sided continuity give.
* (c) Does one-sided continuity suffice for degeneracy? (Not needed for Theorem 11; answer only if
  it falls out.)

**Q4 (`exists_degenerate_interior_elt'`, `theorem11_1951_of_T10'`).** Assembly: Q2 gives
`x`; Q3 makes `bingElt x = {x}`; then `theorem11_1951_of_T10` with `hdeg` discharged. If Q3 is
open, prove the assembly from Q3 as a hypothesis and say so.

## 3. Deliverables

1. Q1–Q4; `#print axioms` in `axioms-batch97.txt`; the status of `exists_degenerate_interior_elt`
   and of `theorem11_1951_of_T10` after this batch.
2. Report: first line names the commission read; refutations first; Q1–Q4 in order.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## 4. Next

Whatever Q3 leaves: if proved, Theorem 11 depends on Theorem 10 alone, and the last-link claim of
Theorem 10 becomes the single open sentence gating Theorems 10, 11 and 13 (sufficiency) of the
Duke paper; if refuted, Kuratowski's route.
