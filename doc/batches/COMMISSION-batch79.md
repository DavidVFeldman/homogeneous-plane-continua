# Commission: batch 79 — Theorem 4 for a chain from `R` to `S`; Theorem 10; the statements of Theorems 5, 6 and 13

**Go!** Runs on top of the batch-78 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch79.md` — this text (also pasted into the prompt);
* `Theorem4Pair.lean` — a skeleton of one statement, `sorry`, a work item. Save it as
  `HPC/Fold/Theorem4Pair.lean` and add `import HPC.Fold.Theorem4Pair` at the end of the root
  `HPC.lean`. Also add `import HPC.Fold.Questions78` to `HPC.lean`, so that the definitions of
  batch 78 §4.4 (`IsContinuum`, `IsIndecomposable`, `Theorem10Statement`) and the `IsFrom` lemmas
  of §4.3 are part of the default build. Nothing else in the workspace is to be replaced.

The report names the commission read in its first line.

## 0. On batch 78

Audited: `theorem4` proved with its statement unchanged, `[propext, Classical.choice,
Quot.sound]`; `theorem3_end` open, unused, the only live `sorry`; build clean. Recorded facts:

* The splice is cut at the *time* `U` at which the fold reaches a fake level-`L` link appended
  after the link meeting `D.link 0` (`B78.fold_low_end`), not at that link's block; `c(U) ≤ L + 1`
  is then automatic and Bing's end-link clause is not needed for Theorem 4. `theorem3_end` stays as
  a statement of what Bing proves; it is not on the path to the classification and is not a
  target of this batch.
* `Q78.isFrom_ofBlocks_iff`: `E.ofBlocks β hβ` is a chain from `R` to `S` (Bing p. 729) iff every
  fine link containing `R` is in block `0` and every fine link containing `S` is in the last block.
  A point of a chain lies in at most two links, which are adjacent. So Theorem 13 needs Theorem 4
  with two-link basepoints, and `theorem4`'s `β'(r) = 0` alone does not give it when `R` lies in
  `d_r ∩ d_{r+1}`.

## 1. Targets

1. **`theorem4_pair`** (`Theorem4Pair.lean`): Theorem 4 with the first block containing both
   `E.link r`, `E.link (r+1)` and the last block containing both `E.link (s−1)`, `E.link s`.
2. **Theorem 10** (Bing pp. 737–738): `Theorem10Statement Δ` for every `Δ : Description X P Q` —
   every subcontinuum of `M` is indecomposable. Bing's proof is transcribed in §3.
3. **Statements only, no proof**: Theorems 5, 6 and 13 in Lean, in a new file
   `HPC/PseudoArc/Statements79.lean`, so that the next batch has its skeleton. §4 gives Bing's text.

A counterexample is a success and is reported first, after a definition audit.

## 2. `theorem4_pair`: two readings of the same idea, asked as questions

The level sequence of a two-link basepoint. `E.link r` and `E.link (r+1)` have level intervals
`[ρ(r), σ(r)]` and `[ρ(r+1), σ(r+1)]`; the faithful model's adjacency field
(`IsCrookedIvF.adj`) says the union of the two intervals has width at most one. So the merged link
`d_r ∪ d_{r+1}` has an interval of the faithful model's shape.

1. **Merge, then fold.** Replace the pair `(r, r+1)` (and `(s−1, s)`) by one index carrying the
   union interval; is the merged sequence `IsCrookedIvF`? The crookedness clause's witnesses "within
   one index of `s`" shift by one across the merge, and the merged index carries both intervals.
   If it is, `B78.theorem4_core` (or `Z77.greedy_fit` directly, through the batch-78 assembly)
   applies to the merged sequence, and the pulled-back schedule puts `r` and `r+1` in block `0`.
   What then needs checking is the three-link containment of block `0` and of the last block: the
   merged link's level is one number but its two constituents lie in links `ρ(r)` and `ρ(r+1)`,
   which may differ by one; whether the walk's start (`T0` within one of the basepoint level) can
   always be chosen so that both constituents fall in the block's three-link window, or whether the
   window at the two end blocks is four links wide, is the question. A four-link window at the two
   end blocks alone would still serve Theorem 13's mesh purpose, but the statement should then say
   so; the skeleton's statement asks for three throughout and may be weakened at the two ends if it
   must, with the change recorded.
2. **Start the zigzag from an edge.** `Z77.greedy_fit` starts both arms at index `0` with the
   common level `S 0`. With the forward arm `j ↦ ρ(r+1+j)` and the backward arm `j ↦ ρ(r−j)`, the
   two start levels differ by at most one and the crookedness clause across the basepoint reads
   between indices `≤ r` and `≥ r+1`. Whether `first_direction` and `main_up` go through with two
   start levels (the first up phase from `b = min − 1`, previous top `max + 1`), or whether a fake
   basepoint link at the shared level (as in `fold_low_end`) does it, is the alternative.

Either route is acceptable; both are questions.

## 3. Theorem 10, Bing's proof (pp. 737–738), transcribed

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch79.md, 3. Theorem 10, Bing's proof (pp. 737–738); batch 204.]

The bracketed remarks are glosses, not Bing's words; each is a claim to be checked, not assumed.
What the repository lacks and this proof needs: the subchain of a level's chain determined by two
points (Bing's `D_j(h, k)`), the fact that every link of such a subchain meets a continuum
containing the two points (a connectedness statement about chains), and the separation step. The
report says which of these were proved and which not; a partial result with the missing step named
is a good outcome.

## 4. Theorems 5, 6, 13: statements to be written in Lean (no proof)

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch79.md, 4. Theorem 5 (pp. 733–734); batch 204.]

"Follows the pattern" (p. 730): the chain `D` follows the pattern `(x_1, y_1), …, (x_n, y_n)` in
the chain `E` if the `x_i`-th link of `D` is a subset of the `y_i`-th link of `E`. Here the pattern
is `(i, x_i)`: the `i`-th link of `E` lies in `d(1)_{x_i}`.

**Theorem 6 (p. 736).** *Suppose `(1, x_1), …, (n, x_n)` as above with `1 = x_1 ≤ x_i ≤ x_n` and
`|x_i − x_{i+1}| ≤ 1`. Suppose `D_1, D_2, …` is a sequence of chains from `P` to `Q` such that `D_1`
has `x_n` links and for each `i`, `D_{i+1}` is crooked in `D_i`, the closure of each link of
`D_{i+1}` is a compact subset of a link of `D_i`, and no link of `D_i` has a diameter of more than
`1/i`. Then there is an integer `j` and a chain `E` from `P` to `Q` such that `E` is a
consolidation of `D_j` and `E` follows the pattern `(1, x_1), …, (n, x_n)` in `D_1`.*

Theorem 6 is the hypothesis `Description.PatternFollowing` under which `Description.exists_homeomorph`
(Theorem 12) is proved; check that the existing `PatternFollowing` is Theorem 6 and record any
difference (the existing definition is indexed from level `i` to a deeper level `j`; Bing's is from
`D_1`, which is the same up to re-indexing the description).

**Theorem 13 (p. 740).** *The continuum `M` is homogeneous.* Bing's proof: `M` is indecomposable
(Theorem 10); for `R`, `S` in different composants and each `j` there is `k > j` with `D_k(R, S)`
meeting both end links of `D_j` (else the limit of the `D_i(R, S)` is a proper subcontinuum
containing `R` and `S`); Theorem 4 gives a chain `E_1` from `R` to `S` consolidating `D_k` with mesh
`< 1`; Theorem 1 makes `D_i` crooked in `E_1` for large `i`; a `k` with the closure of each pair of
intersecting links of `D_k` inside a link of `D_j`, and Theorem 4 again, give `E_2` from `R` to `S`
consolidating `D_k` and contained in `D_j`; Theorem 2 makes `E_2` crooked in `E_1`; iterating
gives chains `E_1, E_2, …` from `R` to `S` with `E_{i+1}` crooked in `E_i`, closures of links inside
links, mesh `< 1/i`, each a consolidation of some `D_i`; then Theorem 12 gives a homeomorphism of
`M` carrying `P_1` to `P_2` for any two points (through a point in a third composant). The Lean
statement asked for is: for every `Δ : Description X P Q` and points `P₁ P₂ ∈ Δ.M`, there is
`T : Δ.M ≃ₜ Δ.M` with `T P₁ = P₂` — together with the two auxiliary notions the proof names and
the repository lacks: composant (the union of all proper subcontinua containing a point) and the
subchain `D_i(R, S)`.

No proof of Theorems 5, 6, 13 is asked for in this batch.

## 5. Deliverables

1. `theorem4_pair`, `sorry`-free, with `#print axioms` in `axioms-batch79.txt`; if the end blocks
   need a four-link window, the statement so amended and the change recorded.
2. Theorem 10 as `theorem theorem10 (Δ : Description X P Q) : Theorem10Statement Δ`, or the
   partial result with the missing step named.
3. `HPC/PseudoArc/Statements79.lean`: Theorems 5, 6, 13 as statements, elaborating, with the
   auxiliary definitions they need; a note on `PatternFollowing` versus Theorem 6.
4. Report: first line names the commission read; any counterexample first; then §1 1–3; then §2.

## 6. Not in this batch

Proofs of Theorems 5, 6, 13; `theorem3_end`; Theorems 8, 9, 14, 15; the 1951 reduction; anything
about spans, walks or censuses of the Theorem-3 campaign.
