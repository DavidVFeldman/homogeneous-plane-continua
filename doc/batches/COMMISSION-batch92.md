# Commission: batch 92 — Bing 1951 (*Snake-like continua*), §4, part one: the six properties and Theorem 8

**Go!** Runs on top of the batch-91 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch92.md` — this text (also pasted into the prompt);
* `Atriodic51.lean` — a skeleton of seven definitions (one a structure), one `def`, and nine statements, all `sorry`, all work
  items. Save it as `HPC/Plane/Atriodic51.lean` and add `import HPC.Plane.Atriodic51` at the end
  of the root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the change
  recorded; `theorem8_1951` keeps its conclusion.

The report names the commission read in its first line.

## 0. On batch 91

Audited: Bing's windows restored (`theorem3_HIC_bing`, with the one-link case and the last window
handled; Bing's rule for the last window, `j − 5 ≤ 3k + 1 < j − 3`, admits no `k` when
`j ≡ 1 (mod 3)` — recorded); the ledger note added; the step "`M` contains a proper subcontinuum
`M'' ∋ p` meeting every link" **proved** (the composant of `p` is dense: boundary bumping), so the
commission's `sin(1/x)` candidate was wrong — links are open in the ambient space and the limit
bar lies in the closure of the curve, so no link meets `M` only in the bar; Bing's surgery for
Theorem 10 proved under weaker hypotheses (`theorem10_1951_of_lastLink`); Theorem 10 proved for end
points; Theorem 10 itself now rests on one claim: *some subcontinuum `M'' ∋ p` has a Theorem-10
chain whose last link meets `M'' ∩ (d_1 ∪ d_m)` at a point other than `p`* — Bing's "or else a
chain with fewer links covers `M''`", which remains unestablished. Standard axioms throughout.

So the ledger entry for Duke Theorem 10 is: proof complete except for one sentence, now isolated;
and the entry for the commission's own candidate counterexample is: refuted.

## 1. What this batch is

Bing's §4 characterizes snake-like continua among hereditarily decomposable ones (Theorem 11:
compact, hereditarily decomposable, atriodic and hereditarily unicoherent ⇔ snake-like). The
proof builds, in any nondegenerate compact continuum `S` that is atriodic, hereditarily unicoherent
and hereditarily decomposable, an upper semicontinuous decomposition `G` into continua that is
"an arc with respect to its elements" (Theorem 8), locates in its end elements points satisfying
condition A (Theorem 9), and then uses Theorem 10 twice (Theorem 11). This batch is the six
preparatory properties and Theorem 8. Theorems 9 and 11 are the next batch; Theorem 11 will be
conditional on Theorem 10, which is open at the one sentence above.

Decompositions are handled as in batch 89: a decomposition of `S` into continua is a set of
subsets; "upper semicontinuous" is stated directly (for each element `g` and open `U ⊇ g`, the
union of the elements inside `U` is open). The decomposition *space* is not needed for Theorem 8
as stated here; it enters only through "arc with respect to its elements", which is the point
of §3.7 below.

## 2. Bing's text (pp. 657–658), transcribed

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch92.md, 2. Bing's text (pp. 657–658); batch 204.]

## 3. Facts about the text, and what the skeleton does with them

1. **Property 1.** For two subcontinua, hereditary unicoherence gives a connected intersection
   (apply unicoherence to `H ∪ K`), provided `H ∩ K ≠ ∅` — Bing's statement presupposes a
   nonempty intersection; the skeleton adds it. For an arbitrary collection: finite
   subintersections by induction, then a directed family of continua whose intersection is a
   continuum (batch 88's nested-intersection lemma, or Nadler 1.8).
2. **Property 2.** From atriodicity: if `S ∖ H` had three components `C_1, C_2, C_3`, then `H ∪ C̄_1 ∪
   C̄_2 ∪ C̄_3` … — Bing says only "follows from atriodicity". The argument: each `C̄_i` meets `H`
   (boundary bumping, `T13.clopen_meets_closure_diff`), `N := H ∪ (the closures of the other
   components)` is a continuum and `S ∖ N` would be the union of three mutually separated sets.
   The report writes it out. The second clause likewise with `H ∪ K` when `H ∩ K ≠ ∅`; **when
   `H ∩ K = ∅`** `H + K` is not a continuum and the clause as written needs `S ∖ (H ∪ K)` handled
   through the components of `S ∖ H` and `S ∖ K` separately — the report says what is true.
3. **Property 3.** As Bing, with: `H_1 ∪ H_2 ∪ H_3` is a continuum (pairwise intersecting);
   unicoherence of it applied to `H_1 ∪ H_2` and `H_3` gives `(H_1 ∪ H_2) ∩ H_3 = H_1 H_3 ∪ H_2 H_3`
   connected, and since both summands are nonempty and closed they meet, so the three have a
   common point; then `H_0` connected by property 1; then property 2 for `H_1 ∪ H_2 ∪ H_3 ∖ H_0`.
   The last step — "therefore one of the sets is a subset of `H_0`" — is the one to check: the
   three sets `H_i ∖ H_0` are pairwise disjoint and open in `H_1 ∪ H_2 ∪ H_3`, and if all three
   are nonempty they give three mutually separated pieces.
4. **Properties 4–6.** The skeleton states each with "`A` contains `B` interiorly" as
   `B ⊆ interior A` (interior in `S`, which is the whole space). Bing's proof of 4 defines `K_i`
   without saying how (a continuum containing `H_i`, meeting the other two, with no interior point
   of them) — the natural `K_i` is `H_i` together with the closure of the component of
   `S ∖ (H_1 ∪ H_2 ∪ H_3)`… the report supplies a construction or says the claim as stated needs
   one. Property 5's `C` "the component with limit points on both" — existence needs an argument
   (connectedness of `S` and property 2). Property 6's three cases are as stated.
5. **Theorem 8, the elements.** `g_p := ⋂ {H : H continuum, p ∈ interior H}`; the family is
   nonempty (`S` itself) and closed under finite intersections (property 1 and interiors), so
   `g_p` is a continuum by property 1. `g_p ∋ q ⇒ g_p = g_q` as Bing, with condition (6) used
   twice; the sentence "`K_2` contains `K_4` interiorly and `K_4` contains `p` interiorly" needs
   `p ∉ H_4` and the components defined; the report writes it out. Upper semicontinuity: the
   limit-superior clause is batch 81's `T13.limSup` machinery.
6. **(b) and (c).** (b) uses hereditary decomposability in the form "a continuum with interior
   contains three subcontinua each with an interior point in neither of the others" — this is
   where Bing's closing remark (indecomposable continua with interior suffice to exclude) comes
   from; the report proves the three-continua claim from decomposability of `g` (decompose `g`,
   then decompose a piece again). (c) is the triod argument; "three elements of `G` not in `M`"
   uses that `G` is uncountable and `M` meets only... — the report supplies: `M` proper and
   connected lies within an interval of the arc `G`, missing an end element and hence
   (property: `G` has no isolated elements) infinitely many elements near it.
7. **"Arc with respect to its elements."** Bing proves: of any three elements, one separates the
   other two in `S`. The skeleton states (a) in that form (`SeparatesPairs`). That the
   decomposition *space* is then an arc is the classical characterization (a continuum in which
   of any three points one separates the other two has exactly two non-cut points, and a continuum
   with exactly two non-cut points is an arc — Nadler, *Continuum Theory*, 6.6, 6.16, 6.17). The
   skeleton states that as a separate target `isArc_of_separatesPairs` on the decomposition space
   (the quotient by the equivalence `p ~ q ⇔ g_p = g_q`, with the quotient topology; compact
   Hausdorff metrizable because `G` is u.s.c.), **expected to need the non-cut-point
   characterization, which is not in Mathlib**; it may be left `sorry` with what was established
   (that the quotient is a continuum; that it has at most two non-cut points) recorded. "End
   elements" in (c) are then the two elements that separate no pair; the skeleton defines
   `IsEndElement` that way and (c) is stated for it.
8. **Implicit hypotheses.** `S` nondegenerate (stated); compactness (stated); `S` the whole
   space (Bing's convenience — the skeleton works in a compact metric space `S` with `univ`
   as the continuum, since every statement is internal to `S`). Nothing else found; the report
   confirms or corrects.

## 4. Deliverables

1. The definitions and statements of `Atriodic51.lean`, `sorry`-free where achieved, with `#print
   axioms` in `axioms-batch92.txt`; reshaped statements recorded; any counterexample in Lean;
   for `isArc_of_separatesPairs`, if open, the partial results.
2. Report: first line names the commission read; counterexamples first; then properties 1–6 and
   Theorem 8 (a)–(c) in order, each with what Bing's text left to the reader.
3. Not attempted: the parked items (`covering_step`, `theorem14` (1948), `theorem3_end`,
   `theorem10_1951`'s last-link claim, `exists_tame_chain_near`).

## 5. Next

Theorems 9 and 11 (§4, part two), the latter conditional on Theorem 10; then Bing's arcs paper if
supplied, which would also discharge `isArc_of_separatesPairs`.
