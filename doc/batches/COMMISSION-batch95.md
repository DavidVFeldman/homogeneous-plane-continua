# Commission: batch 95 — Theorem 9 (Duke 1951), the two open steps

**Go!** Runs on top of the batch-94 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch95.md` — this text (also pasted into the prompt);
* `Theorem9B.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Theorem9B.lean` and add `import HPC.Plane.Theorem9B` at the end of the root
  `HPC.lean`. The `sorry`s of batch 93's `endElt_mem_bingH` and `bingH_irreducible_singleton`
  (`HPC/Plane/Atriodic51B.lean`) may be replaced by references to the results here if they close;
  that is the only permitted edit to an existing file, and the report records it. Shapes may be
  adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 94

Audited: Nadler 6.3–6.7 for arbitrary spaces with the implicit steps named; end elements ⇔ non-cut
elements; the decomposition space; two end elements; `not_subset_of_endElts` directly from (c)
(the obstruction I anticipated does not arise); `BingS` hereditary with no missing Mathlib lemma;
elements of a subcontinuum inside the elements of `S`, with the reverse inclusion refuted on the
bar of `S₀`. Standard axioms, no `sorry`. The refutation is recorded: elements of `S'` refine the
traces and can be strictly smaller.

## 1. Q1 by route 1 (`elt_between_subset`, `endElt_contains_endElt_sub`, `endElt_mem_bingH'`)

Setting: `g = bingElt r` an end element of `S` (`IsEndElt r`), `S' ⊋ g` a subcontinuum, which
satisfies `BingS` (batch 94) and so has its own decomposition `G'` with two end elements, and
whose elements through points of `g` lie in `g` (batch 94, `bingElt_subtype_subset`). Hence `g` is
a union of elements of `S'`.

**QA (`elt_between_subset`).** The elements of `S'` inside `g` form an interval of the separation
order of `G'`: if `e, e' ⊆ g` are elements of `S'` and `e''` separates them in `S'`, then
`g ∖ e''` meets both sides of the separation; `g` is connected, so `g ∩ e'' ≠ ∅`; an element of
`S'` through a point of `g` lies in `g`. Three lines; prove it.

**QB (`endElt_contains_endElt_sub`).** `g` contains an end element of `S'`. The question is open
and is the heart of the batch. What is known: `S ∖ g` is connected (`isEndElt_iff_not_isCutElt`).
Suppose neither end element `e₁', e₂'` of `S'` lies in `g`. Then (by QA and Theorem 8 (a) for
`S'`) the elements of `S'` inside `g` form an interval of `G'` containing neither end, and
`S' ∖ g = A ∪ B` is a separation of `S'` with `e₁' ⊆ A`, `e₂' ⊆ B` — justify this from (a) for
`S'` (every element of `S'` outside `g` is separated from one of the ends by some element inside
`g`, or is separated from the other; the two classes are the sides). Then `S ∖ g` connected gives
a continuum `K ⊆ S ∖ g`… — no: connectedness of `S ∖ g` does not directly give a continuum
through `A` and `B` avoiding `g`, since `S ∖ g` is open and need not be arcwise anything. Use
instead: `cl A ∪ g` and `cl B ∪ g` are continua (Nadler 6.3 relative to `S'`, batch 94's
`isConnected_union_of_separation`); `S` is irreducible between the end elements of `S`, and `g`
is one of them; so… — find the argument, or the obstruction, or a counterexample. Candidate
counterexample shape: `S` with end element `g` nondegenerate, `S'` running "through" `g` so that
`g` is a middle element of `S'`. Atriodicity of `S` should forbid it: `S'` would leave `g` on two
sides and `S ∖ g` connected gives a third direction. Make that a triod or a violation of property
3 if it can be done. Answer *proved / refuted / open with the obstruction stated*.

**QC (`endElt_mem_bingH'`).** From QB: `e ⊆ g` an end element of `S'`, `e'` the other
(`exists_two_endElts` for `S'`, and `e' ≠ e` as elements); for `p ∈ e'`, a subcontinuum of `S'`
containing `g ∪ {p}` contains a point of `e` and a point of `e'`, hence is `S'` (Theorem 8 (c) for
`S'`, `bingElt_irreducible`). So `S'` is irreducible from `g` to `p`, and `g ∈ H` (`g ≠ S` from
Theorem 8 (b)). If QB is open, prove QC from QB as a hypothesis and say so.

## 2. Q3 by descent (`endElt_of_bingH_mem_bingH`, `bingH_irreducible_singleton'`)

Batch 93 showed Q3 ⇔ every member of `H` contains a condition-A point. A descent would settle it:

**Q3′ (`endElt_of_bingH_mem_bingH`).** For a nondegenerate `h ∈ H`, some end element `e` of `h`
(as a space, `BingS h` by batch 94) is in `H`. Then a minimal member of `H` is degenerate
(`bingH_irreducible_singleton'`: a nondegenerate minimal `h` would contain the proper member `e`,
proper by Theorem 8 (b) for `h`).

What `e ∈ H` needs: `e ≠ S` (clear) and for every subcontinuum `S'' ⊋ e` a point `p` with `S''`
irreducible from `e` to `p`. Two cases: `S'' ⊇ h` — then `h ∈ H` gives `p` with `S''` irreducible
from `h` to `p`, and QB-type reasoning inside `S''` should pass from `h` to `e` (this is the
"far point transfers to a smaller member" fact batch 93 checked informally); `S'' ⊉ h` — then
`S'' ∩ h` is a subcontinuum of `h` containing `e` (property 1), and `S'' ∪ h ⊋ h` gives a far
point `p` for `h`; is `p` a far point for `e` in `S''`? That is the open question. Answer
*proved / refuted / open*; if open, state precisely which inclusion fails and whether `S₀` or the
`sin(1/x)` continuum gives a counterexample to the *descent* (not to Q3 itself).

## 3. Assembly (`theorem9_1951'`)

From batch 93's `theorem9_1951_of_steps` with whatever closes. If both close, Theorem 9 is
unconditional; discharge the two batch-93 `sorry`s and record it. If not, `theorem9_1951'` is
proved from the open items as hypotheses, under a name saying so.

## 4. Deliverables

1. QA, QB, QC, Q3′, Q3, assembly; `#print axioms` in `axioms-batch95.txt`; the status of
   `theorem9_1951` (batch 93) after this batch.
2. Report: first line names the commission read; refutations first; QA; QB with the argument or
   the obstruction; QC; Q3′/Q3; assembly.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## 5. Next

Theorem 11 (p. 660): its proof needs, beyond Theorems 8–10, the order on `G` ("a sequence of
elements of `G` converging to `g'` such that infinitely many … separate `g'` from `g₁` and
infinitely many separate `g'` from `g₂`"), Theorem 9 applied to a nondegenerate element `g'` as a
space, and the unargued "`p'` satisfies condition A for `M` equal to either `H` or `K`".
