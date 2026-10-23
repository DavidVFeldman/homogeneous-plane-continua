# Commission: batch 81 — Bing's Theorem 13: `M` is homogeneous

**Go!** Runs on top of the batch-80 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch81.md` — this text (also pasted into the prompt);
* `Theorem13.lean` — a skeleton: `theorem13` and three auxiliary statements, all `sorry`, all work
  items; two `sorry`s inside index bounds are placeholders for `0 < Δ.n j` (which follows from
  `Δ.isFrom j`) and are to be discharged. Save it as `HPC/PseudoArc/Theorem13.lean` and add
  `import HPC.PseudoArc.Theorem13` at the end of the root `HPC.lean`. Nothing else is to be
  replaced. The auxiliary statements may be reshaped, with each change recorded, provided
  `theorem13` is reached.

The report names the commission read in its first line.

## 0. On batch 80

Audited: `theorem5` proved as stated; `theorem6Pos_shift`, `patternFollowing`, `theorem6` proved
with `P ≠ Q`, which is necessary (kernel-checked counterexample on the one-point space, my
omission); **`theorem12` proved unconditionally, statement unchanged** — Bing's uniqueness theorem
for the pseudo-arc is machine-checked. Standard axioms throughout; `theorem3_end` the only live
`sorry`, parked. Recorded: the proof is a combinatorial lift (`PatCore.realize`) with anchors
carrying a radius budget, not Bing's geometric induction; the elided step of Bing's (P4) is that
budget; windows must be as long as the pattern.

## 1. Targets

1. `composant_ne_of_indecomposable`.
2. `exists_subchain_meets_ends`.
3. `exists_description_from`.
4. **`theorem13`**: for every description with `P ≠ Q` and every `P₁, P₂ ∈ M` there is a
   self-homeomorphism of `M` carrying `P₁` to `P₂`.

With 4 the classification's use of Bing 1948 is complete: `theorem12` (uniqueness) and
`theorem13` (homogeneity). A counterexample to any statement is a success and is reported first,
after a definition audit; the `P ≠ Q` lesson of batch 80 applies — if a statement needs a
hypothesis Bing leaves implicit, add it and record it.

## 2. Bing's proof of Theorem 13 (p. 740), transcribed

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch81.md, 2. Bing's proof of Theorem 13 (p. 740); batch 204.]

## 3. The claims of the proof, as facts about the text

Each is a statement Bing asserts without proof, and each is something the formalization must
supply. Where the repository already has the piece, it is named.

1. **(Q1) "The limiting set … is a continuum containing `R` and `S`."** The sets
   `D^*_k(R, S)` are unions of subchains; their closures are compact; the limiting set (Bing's
   usage: the set of points every neighbourhood of which meets `D^*_k(R, S)` for infinitely many
   `k` — the topological limit superior) contains `R` and `S` and is connected because each
   `D^*_k(R, S)` is connected (the union of a chain of connected… — **links need not be connected**;
   the union of a chain's links is connected only if each link is. `Description` does not assume
   links connected. Whether the argument needs connected links, or whether the limit of unions of
   chains from `R` to `S` is connected for another reason (each `D^*_k(R,S)` is a "chain of small
   sets" from `R` to `S`, and a limit of `ε_k`-chained sets with `ε_k → 0` is connected), is the
   first question. The second reason is the standard one and does not need connected links.
2. **(Q1) "Since `R` and `S` belong to different composants, this continuum is `M`."** A
   subcontinuum of `M` containing `R` and `S` that is not `M` is a proper subcontinuum containing
   `R`, so `S ∈ composant(R)`. Immediate from `composant`'s definition.
3. **(Q1) "Hence there is `k > j` such that `D_k(R, S)` intersects both end links of `D_j`."**
   The negation assumed at the start was: for every `k > j`, `D_k(R, S)` misses the first link of
   `D_j` or misses the last. Infinitely many `k` miss the same one, say the first. The limiting set
   of those `D^*_k(R, S)` is then disjoint from the *interior* of the first link in `M` — but
   `d(j)_1 ∩ d(j)_2 ≠ ∅`, so "misses `d(j)_1`" does not put the closure outside `d(j)_1`. What makes
   the limit proper: `P ∈ d(j)_1` and `P ∉ d(j)_2` (`D_j` is a chain from `P` to `Q`), and `P` lies
   in a link of `D_{j+1}` whose closure lies in a link of `D_j`, which must be `d(j)_1`; so a
   neighbourhood of `P` (that link of `D_{j+1}`, whose closure is inside `d(j)_1`) misses every link
   of `D_k` (`k > j+1`) that lies outside `d(j)_1` — since a link of `D_k` lies inside a link of
   `D_{j+1}`, and a link of `D_{j+1}` meeting the `P`-link… This chain of containments is the
   claim to check; the conclusion needed is that `P` (or `Q`) is not in the limiting set, so the
   limiting set is a proper subcontinuum containing `R` and `S`, contradicting 2.
4. **(Q1) `composant(R) ≠ M`**, needed to have `S` at all, and in (Q4) to have `Q_n`. This is
   `composant_ne_of_indecomposable`. Standard proof (Kuratowski; Nadler, *Continuum Theory*,
   Thm 11.13 and 11.15): (a) a proper subcontinuum `K` of an indecomposable continuum `M` has empty
   interior — else, with `U = int K ≠ ∅`, a component `C` of `M ∖ U` meeting `M ∖ K` is a proper
   subcontinuum meeting `∂U ⊆ K` (boundary bumping: every component of `M ∖ U` meets `∂U`), so
   `K ∪ C` is a subcontinuum; one shows `M` decomposes (the standard proof takes the closure of a
   component of `M ∖ K` and uses that `M ∖ K ⊆` finitely many… — the prover should take the
   textbook argument, not this sketch); (b) `composant(p) = ⋃_U C_U` over a countable base
   `{U}` of open sets with `p ∉ closure U`, `C_U` the component of `M ∖ U` containing `p`: every
   proper subcontinuum containing `p` misses some basic `U` and lies in `C_U`, and each `C_U` is a
   proper subcontinuum; (c) Baire: `M` is a compact metric space, a countable union of closed sets
   with empty interior is not `M`. Mathlib has Baire for complete metric spaces, second
   countability of compact metric spaces, and connected components; the boundary bumping theorem
   is to be checked for and proved if absent. `hnd : M.Nontrivial` is needed (a point is
   indecomposable with composant `= M`).
5. **(Q2) Theorem 4 gives a chain from `R` to `S`.** This is `theorem4_pair` with the pair of links
   of `D_k` containing `R` (one or two, adjacent) and the pair containing `S`, together with
   `Q78.isFrom_ofBlocks_iff`; the hypothesis "a link of `D_k(R, S)` meets the first link and one
   meets the last" is 3. "No element of diameter more than 1": each block lies in three
   consecutive links of `D_h`, so its diameter is at most `3 · ε_h`; choose `h` accordingly.
6. **(Q2) "By Theorem 1, `D_j` is crooked in `E_1`."** `isCrookedIn'_of_isConsolidationOf`, with
   `D_j` crooked in `D_h` by transitivity of crookedness down the description (Theorem 2's corollary,
   `isCrookedIn'_of_refines` / `isCrookedIn'_of_isConsolidationOf'` — the repository has these;
   the report says which composes to "`D_j` crooked in `D_h` for `j > h`").
7. **(Q2) "There is `k` such that the closure of the sum of each pair of intersecting links of
   `D_k` is a subset of a link of `D_j`."** A Lebesgue-number argument as in batch 80's
   `eventually_thick`: two intersecting links of `D_k` have union of diameter `≤ 2ε_k`, and the
   closure of a small set meeting `M`… — the precise statement: for `k` large every set of
   diameter `< δ` meeting `(D_{j+1})^*` lies in a link of `D_j`; `eventually_thick` may already
   give this with "two consecutive links" in place of "`W+1` consecutive links".
8. **(Q2) "`E_2` is contained in `D_j`"**: each block of `E_2` lies in three consecutive links of
   `D_k`; with 7 (applied twice, or with "three" in place of "two"), its closure lies in a link of
   `D_j`. This is condition (2) of (Q3) for the pair `E_1, E_2`; it is what `closure_subset` of
   `Description` needs. The report says what bound on `k` gives "closure of three consecutive
   links of `D_k` inside a link of `D_j`".
9. **(Q2) "By Theorem 2, `E_2` is crooked in `E_1`."** `E_2` is a consolidation of `D_k`, `D_k`
   crooked in `D_j` (transitivity), `D_j` refines… — Bing's Theorem 2: `E` contains `F` and `E`
   crooked in `D` ⇒ `F` crooked in `D`; here `F = E_2`?? No: `E_2` is coarser than `D_k`. The
   repository's `isCrookedIn'_of_isConsolidationOf` is Theorem 1 (coarsen the target). To get
   `E_2` crooked in `E_1`: `D_k` is crooked in `D_j` (transitivity), `D_j` is crooked in `E_1` (6),
   hence `D_k` crooked in `E_1` (transitivity again, Theorem 2's corollary: a chain crooked in a
   chain crooked in `D` is crooked in `D`? — that is *not* Theorem 2; Theorem 2 says a subchain of
   a crooked chain is crooked). **The step "`E_2` crooked in `E_1`" from "`D_k` crooked in `E_1`"
   coarsens the fine chain to its consolidation `E_2`, which is neither Theorem 1 nor Theorem 2 as
   stated.** Bing says "By Theorem 2". Whether it follows from `E_2 ⊆`-containment in `D_j`
   (each link of `E_2` inside a link of `D_j`, and `D_j` crooked in `E_1`, so `E_2` "refines" `D_j`
   and Theorem 2 = `isCrookedIn'_of_refines` applies with `E_2` in the role of the finer chain) —
   yes: Theorem 2 needs `E_2` to *refine* `D_j`, which is 8. So the order is: 8 first, then
   Theorem 2. The report confirms or corrects this reading.
10. **(Q3) The sequence is a `Description X R S`.** Fields: `isFrom` (5), `crooked` (9),
    `closure_subset` (8), `ε` with `ε_pos`, `ε_tendsto` (choose `ε_i = 1/i` or the diameters
    obtained), `bdd`, `diam_le`. Its `M'` equals `Δ.M`: `E_i` is a consolidation of `D_{k_i}`, so
    `E_i^* = D_{k_i}^*`, and `⋂_i D_{k_i}^* = ⋂_i D_i^*` because the unions are nested
    (`D_{i+1}^* ⊆ D_i^*`). This is `exists_description_from`.
11. **(Q4)** For `P₁, P₂ ∈ M`: by 4 pick `Q_n ∉ composant(P_n)`; by 10 get `Δ_n : Description X P_n Q_n`
    with `Δ_n.M = Δ.M`; `theorem12 Δ₁ Δ₂` (needs `P_n ≠ Q_n`: immediate from `Q_n ∉ composant(P_n)`
    since `P_n ∈ composant(P_n)` when `M` is nontrivial — a proper subcontinuum `{P_n}`) gives
    `T : Δ₁.M ≃ₜ Δ₂.M` with `T P₁ = P₂`; transport along `Δ₁.M = Δ.M = Δ₂.M` to `Δ.M ≃ₜ Δ.M`.
    `M` nontrivial from `P ≠ Q`.

## 4. Deliverables

1. `theorem13` and the three auxiliaries, `sorry`-free, with `#print axioms` in
   `axioms-batch81.txt`; any reshaped statement recorded with its reason.
2. Report: first line names the commission read; any counterexample first; then §1; then, for each
   of the eleven claims of §3, what was proved, what Bing's text lacked, and which existing
   theorems were used — in particular the reading of claim 9 ("By Theorem 2").

## 5. Not in this batch

`theorem3_end`; Theorems 8, 9, 14, 15; the 1951 reduction; anything about spans, walks or
censuses.
