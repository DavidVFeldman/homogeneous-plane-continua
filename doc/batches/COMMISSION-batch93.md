# Commission: batch 93 — Theorem 8 (Duke 1951) with Bing's own elements; Theorem 9

**Go!** Runs on top of the batch-92 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch93.md` — this text (also pasted into the prompt);
* `Atriodic51B.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Atriodic51B.lean` and add `import HPC.Plane.Atriodic51B` at the end of the root
  `HPC.lean`. Nothing else is to be replaced; the one permitted edit to an existing file is the
  ledger note of item 4. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 92: the refutation stands, but it refutes the commission, not Bing

Batch 92 audited: properties 1–6 proved; `theorem8_1951_of_partition` proved; the counterexample
`S₀` with `BingS S₀` proved; standard axioms throughout. Thank you for the care in §1.4 of the
report ("Theorem 8 itself is not refuted … what is refuted is Bing's choice `G = {g_p}`, which the
skeleton hard-codes"). The second half of that sentence is where the correction lies.

**Bing's definition is not the skeleton's.** Page 658, verbatim: "For each point `p` let `g_p`
denote the intersection of all continua which contain interiorly a continuum that contains `p`
interiorly." Two layers. The batch-92 commission (§5) and the skeleton docstring wrote "the
intersection of all continua containing `p` interiorly" — one layer. The error was ours.

With Bing's definition the counterexample dissolves, and it does so in exactly the way §1.4
anticipated: for a bar point `b = (s, 0)` of `S₀`, every continuum `H` that contains interiorly a
continuum `H'` containing `b` interiorly has `H' ⊇ [0,1] × {0} ∋ q`, hence `q ∈ int H`, hence
`H ⊇ [1,2] × {0}`; conversely `H_ε = S₀ ∩ {|y| ≤ ε}` is a continuum containing the bar interiorly
and containing `H_{ε/2}` interiorly. So `g_b = [0,2] × {0}` for every bar point, `g_c = {c}` for
every curve point, and `G` is the collection of §1.4: the curve points and the bar. The
decomposition space is an arc.

Two consequences for the report's §3.2:

* Bing's sentence "there is a continuum `H_1` in `S − p'` which contains interiorly a continuum
  `H_2` which contains `q` interiorly" is, under his definition, the *unpacking of
  `p' ∉ g_q`*, with the roles exactly as he wrote them. The remark that the roles must be swapped
  was an artefact of the one-layer definition and is withdrawn.
* The one-layer variant is false, and that is a true and worth-keeping fact about Bing's
  construction: the inner layer is what makes the elements saturate. The `Counter92` files stay in
  the repository, with the note of item 4.

## 1. Item 1: Theorem 8 with `bingElt` (`theorem8_1951'`)

`bingElt p := ⋂₀ {H : continuum ∧ ∃ H' continuum, H' ⊆ int H ∧ p ∈ int H'}`. Prove the seven
clauses, in the conclusion shape of batch 92's `theorem8_1951`.

1. **Continuum.** The family is nonempty (`H = H' = S`) and closed under finite intersections
   (`H'_1 ∩ H'_2` is a continuum by property 1, `p ∈ int H'_1 ∩ int H'_2 ⊆ int (H'_1 ∩ H'_2)`,
   `H'_1 ∩ H'_2 ⊆ int H_1 ∩ int H_2 = int (H_1 ∩ H_2)`); then property 1.
2. **Partition**, following Bing's paragraph, which is now to be read with his definition.
   Suppose `q ∈ g_p` and `p' ∈ g_p ∖ g_q`. Unpack `p' ∉ g_q`: `H_1 ∌ p'`, `H_2 ⊆ int H_1`,
   `q ∈ int H_2`. Property 6 twice: `H_1 ⊇ int H_3 ⊇ H_3 ⊇ int H_4 ⊇ H_4 ⊇ int H_2 ⊇ H_2`
   (Bing's "`H_1` contains `H_3` interiorly, `H_3` contains `H_4` interiorly, and `H_4` contains
   `H_2` interiorly"). `p ∉ H_4`: otherwise `p ∈ H_4 ⊆ int H_3`, so `H_1` contains interiorly a
   continuum (`H_3`) containing `p` interiorly, so `g_p ⊆ H_1 ∌ p'`, contradiction. Then
   `K_i` (`i = 2, 4`) the closure of the component of `S − H_i` containing `p` (`p ∉ H_2 ⊆ H_4`).
   Bing: "`K_2` contains `K_4` interiorly and `K_4` contains `p` interiorly", so `g_p ⊆ K_2`, but
   `K_2 ∌ q`. **Flag.** `K_4 ⊆ int K_2`: the component `C_4` of `S − H_4` through `p` is open
   (batch 92's `isOpen_component_compl`) and lies in `C_2`, the component of `S − H_2` through
   `p`; so `C_4 ⊆ int K_2`. The points of `cl C_4 ∖ C_4 ⊆ H_4` (boundary bumping) need an
   argument: such a point `y` lies in `H_4 ⊆ int H_3`, and one wants a neighbourhood of `y` inside
   `cl C_2`. State what is used (`H_3 ∖ H_2 ⊆ C_2`? that needs `H_3 ∖ H_2` connected, which is not
   given). If Bing's `K_i` do not work as stated, find the argument (possibly with a fifth
   continuum from property 6, or with `K_4` := the closure of the component of `S − H_3`) and
   record the change. `K_2 ∌ q`: `q ∈ int H_2`, and `cl C_2 ⊆ C_2 ∪ H_2`… — careful: `cl C_2` can
   meet `H_2`, so the claim is `q ∉ cl C_2`, i.e. `q ∈ int H_2` and `C_2 ∩ H_2 = ∅` give
   `q ∉ cl C_2` since `int H_2` is an open set disjoint from `C_2`. Then "each point in `g_q` is in
   `g_p`" by symmetry — **flag**: Bing's "similarly" is for the reverse inclusion
   `g_q ⊆ g_p`, which also uses `q ∈ g_p`; write out why the same argument applies (it uses
   `p ∈ g_q`, which is what was just proved).
3. **Upper semicontinuity, (a), (b), (c).** Batch 92's `theorem8_1951_of_partition` was proved for
   `gElt`; its arguments (neighbourhood form from compactness, `gElt_separates_of`,
   `two_disjoint_with_interior`, the triod argument for (c)) should transfer to `bingElt` with the
   neighbourhood form now reading: every open `U ⊇ bingElt p` contains a continuum `H` with
   `ContainsNested H p`. Transfer them; report which lemma needed more than a renaming.
4. `gElt_subset_bingElt` (one line) stays as a bridge, so the record shows the relation between the
   two definitions.
5. `Counter92.bingElt_bar` and `Counter92.bingElt_curve`: the corrected elements on `S₀`, as
   computed above (the `Crit`/tail machinery of batch 92 should give the bar case; the curve case
   uses that a curve point has a closed arc neighbourhood in `S₀` which contains interiorly a
   smaller arc). These two are the record that the counterexample is answered, not just overruled.

## 2. Item 2: Theorem 9 (`theorem9_1951`)

Bing, p. 659, verbatim: *If `G` is the upper semi-continuous collection mentioned in Theorem 8,
each end element of `G` contains a point `p` satisfying condition A for `M` equal to `S`.*

*Proof.* Let `H` be the collection of all proper subcontinua `h` of `S` such that if `h` is a
proper subcontinuum of a subcontinuum `S'` of `S`, there is a point `p` of `S'` such that `S'` is
irreducible from `h` to `p`. Then the end elements `g_1` and `g_2` of `G` are elements of `H`. The
property of being an element of `H` is inductive because for each monotone decreasing sequence
`h_1, h_2, ⋯` of elements of `H`, `Π h_i` is an element of `H`. Hence, in each of `g_1` and `g_2`
there is an element of `H` which is irreducible with respect to being an element of `H` and each
irreducible element of `H` is a point.

(Condition A, p. 659: each nondegenerate subcontinuum of `M` containing `p` is irreducible from
`p` to some other point. Bing adds that such a `p` is "a special kind of terminal point as defined
by Miller [6; 190]".)

Four sentences, four claims, none argued. The skeleton splits them. Answer each
*proved / refuted / open with the obstruction stated*; shapes may change with the change recorded.

**Q1 (`endElt_mem_bingH`).** Why is an end element `g_r` in `H`? Given `S' ⊋ g_r` a continuum,
produce `p ∈ S'` with `S'` irreducible from `g_r` to `p`. Bing gives nothing. Candidates: (c) of
Theorem 8 relativized (is `S'` a union of elements of `G`? the elements inside `S'` are
ordered — by (a) — and `S'` is irreducible between its "ends" in that order?); or the subcontinua
of `S'` containing `g_r` are nested (a condition-B-like statement for sets, from (a) and property
3). State what is proved. Note Bing's `H` requires `h ≠ S`; an end element is proper by (b).

**Q2 (`bingH_iInter`).** Inductiveness. The intersection of a decreasing sequence of continua is a
continuum (batch 92's property 1 or the general fact); it is proper; given `S' ⊋ ⋂ h_i`, one needs
`p` with `S'` irreducible from `⋂ h_i` to `p`. If `S' ⊉ h_n` for some `n`… the obvious attempts
produce irreducibility from `h_n` to `p` for the continuum `S' ∪ h_n`, not for `S'`. Find the
argument or state the obstruction. (Brouwer reduction: the inductiveness Bing needs is for the
Zorn/Brouwer step; the skeleton states it for sequences, as Bing does; if the proof of Q4 needs
the chain form, change the shape.)

**Q3 (`bingH_irreducible_singleton`).** A member of `H` with no proper sub-member is a point. Given
a nondegenerate `h ∈ H`, produce a proper subcontinuum of `h` in `H`. Hereditary decomposability
gives `h = A ∪ B` with `A, B` proper; is `A` (or `B`) in `H`? For `S' ⊋ A`, `S'` need not contain
`h`. State what is proved.

**Q4 (`theorem9_1951`).** Assemble: Brouwer reduction (a `sInf`/Zorn argument on the chains of
members of `H` inside `g_r`, using Q2 in whatever form it holds) gives a minimal member inside
`g_r`; Q3 makes it a point `{p}`; `condA_of_bingH_singleton` turns membership of `{p}` in `H` into
condition A (immediate from the definitions: a nondegenerate subcontinuum `S'` of `S` containing
`p` has `{p}` as a proper subcontinuum, so `S'` is irreducible from `{p}` to some `q`, and
`q ≠ p` since `S'` is nondegenerate). If Q1–Q3 are not all closed, prove Theorem 9 conditionally
on the open ones, as hypotheses, under a name `theorem9_1951_of_…`, and say so.

## 3. Item 3: the arc (parked)

`isArc_of_separatesPairs` for `bingElt` is not commissioned. If, while proving (a), the separation
order on `G` is set up in a reusable form (a linear order on the elements with the order topology),
record it; the non-cut-point characterization of the arc (Nadler 6.16–6.17) remains the missing
piece.

## 4. Item 4: the ledger

Prepend to the module docstring of `HPC/Plane/Atriodic51Counter.lean` a `-- Note (batch 93)`: the
one-layer definition `gElt` refuted there is the batch-92 commission's transcription, not Bing's
definition (p. 658: "all continua which contain interiorly a continuum that contains `p`
interiorly"); Bing's elements are `bingElt` in `Atriodic51B.lean`, and on `S₀` they are the curve
points and the bar (`Counter92.bingElt_bar`, `bingElt_curve`). No other existing file is to be
edited.

## 5. Deliverables

1. `theorem8_1951'` with its seven clauses; `gElt_subset_bingElt`; `Counter92.bingElt_bar`,
   `bingElt_curve`; Q1–Q4 of Theorem 9 with `theorem9_1951` or its conditional form;
   `#print axioms` for all of them in `axioms-batch93.txt`.
2. Report: first line names the commission read; refutations first; item 1 with the two flags of
   §1.2 answered; Q1–Q4 in order; item 4.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## 6. Next

Theorem 11 (snake-like ⇔ atriodic and hereditarily unicoherent, for compact hereditarily
decomposable continua), conditional on `theorem10_1951` or its proved forms, and its corollaries.
