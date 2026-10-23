# Commission: batch 94 — Moore's non-cut-point theorem; the two end elements of Bing's decomposition

**Go!** Runs on top of the batch-93 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch94.md` — this text (also pasted into the prompt);
* `NonCut51.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/NonCut51.lean`
  and add `import HPC.Plane.NonCut51` at the end of the root `HPC.lean`. Nothing else is to be
  replaced. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 93

Audited: `theorem8_1951'` with all seven clauses, the two flags closed (the stronger
`cl C₄ ⊆ C₂`; the forced order of the two inclusions), the counterexample answered on `S₀`, Q2
proved, the Brouwer reduction, the conditional Theorem 9; standard axioms, `sorry` only in Q1 and
Q3. The relative-Theorem-9 obstruction in Q1 (`S' = cl C₁ ∪ [1, 3/2] × {0}`, far point `(3/2, 0)`
inside a partly contained element) is recorded; so is the reformulation `bingH_step3_iff`.

This batch takes the report's own suggestion: two end elements, by Moore's theorem. Theorem 11
(p. 660) needs them explicitly ("`g_1` and `g_2` are the end elements of `G`"), and route 1 for
Q1 needs them for `S'`. The theorem is general topology and is stated as such.

## 1. Item 1: Nadler Chapter VI (`IsSeparation`, `IsCutPoint`, 6.3, 6.4, 6.6, 6.7)

Nadler, *Continuum Theory*, 6.3–6.7, for a nondegenerate compact connected `T₁` space (he writes
"`T₁`-continuum"; the proof uses only compactness, connectedness, closed points and the maximal
principle — no metric). The proof of 6.6 is on his pp. 89–90; its steps:

1. Suppose every `x ∈ U` is a cut point, `S ∖ {x} = U_x | V_x` with `c ∈ V_x`.
2. By 6.4, `U_x ∪ {x} ⊆ U`; by 6.3, `U_x ∪ {x}` and `V_x ∪ {x}` are connected.
3. If `y ∈ U_x` then `U_y ∪ {y} ⊆ U_x` (one of the two connected sets `U_y ∪ {y}`, `V_y ∪ {y}`
   lies in `S ∖ {x}`, hence in `U_x` or `V_x`; three of the four cases are excluded by `y ∉ V_x`
   and `c ∈ V_x ∩ V_y`), so `x ∉ U_y ∪ {y}`.
4. A maximal nest in `{U_x ∪ {x} : x ∈ U}` (closed sets, finite intersection property) has
   nonempty intersection; a point `p` of it lies in `U`, and `U_p ∪ {p}` lies in every member of
   the nest; any `q ∈ U_p` gives a strictly smaller member `U_q ∪ {q}`, contradicting maximality.

In Lean the nest is a `zorn`-style chain of closed sets; the skeleton's `IsSeparation Y P Q` is
Nadler's `Y = P | Q` with openness relative to `Y`. Prove `exists_nonCutPoint_of_cut`, then
`exists_two_nonCutPoints` (if `S` has no cut point at all, any two distinct points serve; otherwise
6.6), then 6.7 (`not_subset_of_nonCutPoints`: a proper connected `Z` containing all non-cut points
misses some `c`, which is a cut point; `Z` lies on one side of its separation, contradicting 6.6).
Report which of 6.3/6.4 needed more than the text says.

## 2. Item 2: end elements (`isEndElt_iff_not_isCutElt`, `exists_two_endElts`, `not_subset_of_endElts`)

1. `isEndElt_iff_not_isCutElt`. Batch 93's `IsEndElt r` says `g_r` separates no two other elements
   (`Separates`, batch 92: disjoint open `U, V` covering `S ∖ g_r`, one element in each). ⇒: if
   `S ∖ g_r = U ∪ V` is a separation, take `q ∈ U`, `q' ∈ V`; `g_q`, `g_{q'}` are connected and
   disjoint from `g_r` (partition, Theorem 8), so `g_q ⊆ U`, `g_{q'} ⊆ V`, and they are distinct
   from each other and from `g_r`; `U`, `V` are open in `S` since `g_r` is closed. ⇐: a
   `Separates` witness is a separation of `S ∖ g_r`.
2. The decomposition space. Two routes; choose and record.
   * (a) `Quotient (Setoid.ker bingElt)` with the quotient topology
     (`instTopologicalSpaceQuotient`). Compact and connected as a continuous image; `T₁` because
     the preimage of a class is an element, closed; nontrivial because no element is `S`
     (Theorem 8 (b): `interior (bingElt p) = ∅`, and `S` is nonempty). Then
     `isCutElt_iff_isCutPoint_quot`: `(S/G) ∖ {[r]}` is disconnected iff `S ∖ g_r` is; ⇒ by
     continuity of the quotient map restricted to `S ∖ g_r`; ⇐: a separation of `S ∖ g_r` is
     saturated (each element is connected, so lies on one side), and saturated open sets are open
     in the quotient. Then Item 1 on the quotient gives two non-cut points, i.e. two non-cut
     elements, i.e. two end elements.
   * (b) Run Nadler's argument directly in `S` on saturated sets, without the quotient. Then
     `decompositionSpace_props` and `isCutElt_iff_isCutPoint_quot` are dropped (record it) and
     `exists_two_endElts` is proved from a saturated version of 6.6. Route (a) is preferred since
     it leaves the general theorem reusable (Theorem 11's proof speaks of the elements as points
     of an arc).
3. `not_subset_of_endElts`: 6.7 transported. A proper subcontinuum `Z` of `S` misses some end
   element. (Through the quotient: the image of `Z` is a proper connected subset of `S/G` —
   proper because `Z` is proper and the elements it meets are not all of `S`… careful: the image
   of `Z` is proper only if some element misses `Z`, which is what is to be proved. Use 6.7 in the
   form: if the image of `Z` contained all non-cut points, it would be all of `S/G`, so every
   element meets `Z`; then `Z ∪ (elements it meets)`… — the obstruction is real; state what is
   proved. The weaker statement actually needed later is: a proper subcontinuum meeting both end
   elements does not exist, which is Theorem 8 (c), already proved as `bingElt_irreducible`.)

## 3. Item 3: reconnaissance (`bingS_subcontinuum`, `bingElt_subtype_subset`)

Both Q1 route 1 and Theorem 11's step "`p'` satisfies condition A for `M` equal to either `H` or
`K`" (p. 660, unargued) need Bing's hypothesis and Bing's decomposition on a subcontinuum.

**Q1 (`bingS_subcontinuum`).** A nondegenerate subcontinuum `S'`, as a subtype with the induced
metric, satisfies `BingS`. The three hereditary properties are hereditary by definition; the work
is the transfer of `Fold.Q78.IsContinuum`, `IsTriod`, `IsUnicoherent` and the decomposition
`A ∪ B = K` between `Set S'` and `Set S` (`Subtype.val '' ·` and `Subtype.val ⁻¹' ·`; a subset of
`S'` is compact/connected iff its image is). The instance `CompactSpace S'` comes from
`isCompact_iff_compactSpace`. Prove it, or state exactly which transfer lemma is missing from
Mathlib.

**Q2 (`bingElt_subtype_subset`).** For `x ∈ S'`, the element of `x` in `S'` lies in the element
of `x` in `S`. The report's argument: if `H ⊇ int H' ∋ x` doubly interiorly in `S`, then `H ∩ S'`
contains interiorly (in `S'`) `H' ∩ S'`, which contains `x` interiorly (in `S'`), and both are
continua by unicoherence of `S` (property 1 applied to `H ∩ S'`, `H' ∩ S'`; both intersections
nonempty since they contain `x`). Prove or refute; if proved, say whether the reverse inclusion
`bingElt (x : S) ∩ S' ⊆ image of bingElt x` holds (expected false: on `S₀` with
`S' = cl C₁ ∪ [1, 3/2] × {0}` and `x = (1/2, 0)`, the element in `S'` should be
`[0, 3/2] × {0}`… or is it `[0,1] × {0}`? compute it) — this is exactly the data Q1 of Theorem 9
needs.

Report Q1, Q2 as *proved / refuted / open with the obstruction stated*.

## 4. Deliverables

1. §1 (6.3, 6.4, 6.6, 6.7), §2 (`isEndElt_iff_not_isCutElt`, `exists_two_endElts`, and
   `not_subset_of_endElts` or its proved form), §3 Q1–Q2; `#print axioms` in `axioms-batch94.txt`.
2. Report: first line names the commission read; refutations first; item 1 with the two
   lemmas' extra steps; item 2 with the route chosen; Q1–Q2.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`, Q1/Q3 of Theorem 9.

## 5. Next

Theorem 9 Q1 by route 1 (Theorem 8 on `S'`, two end elements of `S'`, an end element of `S`
meeting `S'` meets an end element of `S'`); then the arc structure of `G` (Nadler 6.16–6.17), which
Theorem 11's "sequence of elements converging to `g'` … separating `g'` from `g_1`/`g_2`" requires.
