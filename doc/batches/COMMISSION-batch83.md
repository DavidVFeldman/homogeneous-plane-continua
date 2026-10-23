# Commission: batch 83 — the rest of Bing 1948, part two: irreducible subcontinua; Theorems 14 and 15

**Go!** Runs on top of the batch-82 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch83.md` — this text (also pasted into the prompt);
* `Theorem14.lean` — a skeleton of one definition and six statements, all `sorry`, all work
  items. Save it as `HPC/PseudoArc/Theorem14.lean` and add `import HPC.PseudoArc.Theorem14` at the
  end of the root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the
  change recorded, except that `theorem14` and `theorem15` keep their conclusions.

The report names the commission read in its first line.

## 0. On batch 82

Audited: `theorem7`, `theorem7_minimal`, `theorem8` (corrected), `theorem9` proved; the two
Theorem 8 counterexamples (`theorem8_skeleton_false`, `not_theorem8_literal`) kernel-checked;
standard axioms throughout; `theorem3_end` the only live `sorry`, unchanged. Recorded facts:
Theorem 8's orientation clause needed "forwards or backwards" (`blockMap_self`); the union clause
holds for like-oriented chains through *tightness* (`tight_of_crooked`, `crooked_of_tight`); Bing's
literal Theorem 8 fails in a four-link `E` on a finite subset of `ℕ`, with the crosswise
intersection at the point `20`; Theorem 9 is trivial for `t ≤ r`; `H + D(s+1, n)` is a block
consolidation of `D` by `foldMap`, crooked by a direct four-case argument.

`theorem3_end` stays parked: it is worked on last again, only if everything else is done.

## 1. Targets, in order

1. **`IsIrreducibleBetween`** (definition, given) and **`exists_irreducible`**: a continuum
   containing two points contains a subcontinuum irreducible between them. Standard: Zorn on
   the subcontinua containing both points ordered by reverse inclusion; the intersection of a
   nested family of continua is a continuum (compactness for nonemptiness, and connectedness of
   a nested intersection of compact connected sets).
2. **`Description.irreducible_unique`**: in the described continuum `M` there is exactly one
   subcontinuum irreducible between two given distinct points `A`, `B`. This is Bing's last
   paragraph (p. 742), and its proof is in §3.1 below; the batch-81 tools (`T13.limSup`,
   `T13.isPreconnected_limSup`, `Chain.span`, `Chain.chainedAt_span`,
   `Description.exists_isSubchainFrom_of_lt`, `Chain.inter_link_nonempty_between`) are what it needs.
3. **`theorem15_of_theorem14`**: Theorem 15 from Theorem 14 (as a statement `Theorem14Statement Δ`)
   and item 2. Bing's proof (§2) with the gap in §3.2 closed.
4. **`Description.exists_description_covering`**: the sequence `X_{i,1}, X_{i,2}, …` of Bing's
   proof of Theorem 14 — a description of `M` from `P'` to `Q'` whose subchain from `P'` to `R`
   covers, at every level, the subcontinuum `W` irreducible between `P'` and `R`. Bing: "that there
   exist such sequences follows as a consequence of Theorem 9". How it follows is not said; §3.3
   records what has been worked out and what has not. This is the first place where the
   commission does not have a proof to transcribe.
5. **`theorem14`**: Bing's Theorem 14, proof in §2 and §3.4.
6. **`theorem15`**: items 3 and 5 combined.

Items 1–3 are expected to go through. Items 4 and 5 are where Bing's text is a sketch; if either
cannot be completed, the report states precisely which claim of §3.3 / §3.4 resisted and why, with
the partial results left as proved lemmas and the target as `sorry`. A kernel-checked
counterexample to any statement as skeletoned is a success and is reported first.

## 2. Bing's statements and proofs (pp. 740–742), transcribed

Bing's `D_i` is the repository's `Δ.D i`; his `d(j)_R` is a link of `D_j` containing `R`; his
`D_j(R, Q)` is the subchain of `D_j` from `R` to `Q` (`Chain.IsSubchainFrom`); `X*` is the union of
the links of `X`.

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch83.md, 2. Bing's statements and proofs (pp. 740–742); batch 204.]

## 3. Facts about the text, and what the skeleton adds

### 3.1 The unique irreducible subcontinuum (`irreducible_unique`)

Bing gives the statement and names the witness; the proof is this. Let `A ≠ B` in `M`. For
`ε_k < dist A B`, `D_k` has a subchain `D_k(A, B)` from `A` to `B` (`exists_isSubchainFrom_of_lt`;
either orientation). Let `S_k` be the union of its links (`Chain.span`) and `L` the limit superior
of the `S_k` over `k ≥ k_0` (`T13.limSup`). Then:

* `L` is closed, connected (`T13.isPreconnected_limSup`: each `S_k` is `ε_k`-chained,
  `Chain.chainedAt_span`, and contains `A`), and contains `A` and `B` (`T13.mem_limSup`); `L ⊆ M`
  as in `false_of_disjoint_limit` (`S_k ⊆ (D_k)^*` and levels refine earlier levels). So `L` is a
  subcontinuum of `M` containing `A` and `B`.
* Every subcontinuum `K` of `M` containing `A` and `B` contains `L`: `K ⊆ (D_k)^*` meets the link
  of `A` and the link of `B`, hence every link of `D_k(A, B)` (`Chain.inter_link_nonempty_between`),
  so every point of `S_k` is within `ε_k` of `K`; hence `⋃_{k ≥ N} S_k` lies in the closed
  `ε_N`-neighbourhood of `K` (`ε` decreasing may be arranged, or use `sup_{k ≥ N} ε_k → 0`), and `L`
  lies in every such neighbourhood, hence in the closed set `K`.
* Hence `L` is irreducible between `A` and `B` (a subcontinuum of `L` through `A, B` contains `L`),
  and any `W` irreducible between `A` and `B` satisfies `L ⊆ W` and so `W = L`.

The hypothesis `A ≠ B` is needed for the subchains; for `A = B` the unique irreducible
subcontinuum is `{A}` and the skeleton excludes the case.

### 3.2 Theorem 15's implicit hypotheses

* **`W_i ≠ M`.** "A composant not containing `W_i`" presupposes `W_i` lies in a composant, i.e. is a
  proper subcontinuum. The proof needs it: "`R_i` and `P_i` belong to the same composant of `M`"
  is because both lie in the proper subcontinuum `W_i`. Without it the statement is false
  (`W_1 = M`, `W_2` proper: no homeomorphism carries `M` onto `W_2`). The skeleton adds
  `W_i ≠ Δ.M`.
* **"A composant not containing `W_i`"** is stated in the skeleton as `Q_i ∉ composant Δ.M P_i`.
  Under the standard fact that composants of an indecomposable continuum are pairwise disjoint or
  equal (not in the repository, not needed), the two are equivalent: `W_i` lies in the composant of
  `P_i`.
* **"A different composant of `W_i` from `P_i`"** uses `composant W_i P_i ≠ W_i`
  (`composant_ne_of_indecomposable` applied to `W_i`, which is an indecomposable continuum by
  `theorem10`; nondegeneracy is where "nondegenerate" enters). Then `W_i` is irreducible between
  `P_i` and `R_i`: a proper subcontinuum of `W_i` containing both would put `R_i` in the composant
  of `P_i` in `W_i`. And `P_i ≠ R_i` (`P_i` lies in its own composant of `W_i`, as `{P_i}` is a
  proper subcontinuum of the nondegenerate `W_i`).
* **The last step.** `T` carries `W_1` onto a subcontinuum of `M` containing `P_2` and `R_2` and
  irreducible between them (irreducibility is preserved by homeomorphisms of `M`); by §3.1 it is
  `W_2`.

### 3.3 The covering description (`exists_description_covering`) — Bing's "consequence of Theorem 9"

What is wanted: a description `Δ'` of `M` from `P'` to `Q'` such that at every level `i` the
subchain of `Δ'.D i` from `P'` (its first link) to `R` covers `W`, where `W` is irreducible between
`P'` and `R`, `R` in the composant of `P'`, `Q'` not.

What is known:

* Theorem 13's construction (`exists_description_from`) gives a description from `P'` to `Q'`
  (`R := P'`, `S := Q'` there). Its levels are consolidations `F` of deep levels `D_k` produced by
  Theorem 4 on the subchain `D_k(P', Q')`.
* `W` is *not* in general covered by the subchain from `P'` to `R` of an arbitrary chain from
  `P'` to `Q'` that covers `M`: if the chain folds (visits a far link and returns) between `P'` and
  `R`, `W` follows the fold, and the fold's links lie beyond `R`'s link. So the block map must be
  chosen so that every fine link that `W` meets goes to a block at or before `R`'s block.
* Theorem 9 (`theorem9`) controls the opposite side: with `d_r ⊆ e_m`, `d_s ⊆ e_1`, `r < s` and
  `t < s`, the consolidation `F` has every `u ≥ r` in a block `≥ β t`. Read with `R ∈ d_t`, this
  says the subchain `F(R, Q')` contains `D(r, n)`, so `F(P', R)` consists of links of `D(0, r−1)`
  together with the block of `t`. For this to give "`F(P', R)` covers `W`" one needs `W`'s links
  among `D(0, r−1)`, *and* those links placed in blocks `≤ β t`. The second is not part of
  `theorem9`'s conclusion as stated; Bing's `F` has `G_1` (a Theorem 7 consolidation of `D(0, r)`)
  on `D(0, r)` cut at block `v = β t`, and the links of `D(0, r−1)` in `G_1`-blocks `> v` are
  moved to blocks `≥ v` — so whether they can be kept before `R`'s block depends on `G_1` and on
  where `W`'s links sit in it.
* By §3.1, `W = limsup_k S_k` where `S_k` is the span of `D_k(P', R)`; so for `k` large, `W` is
  close to `S_k` but the containment `W ⊆ S_k` is not given by that (and fails in the fold
  example above, when `D_k(P', R)` is read as the index interval from `P'`'s link to `R`'s link).

So the statement to prove is more than an application of `theorem9`. The commission asks for a
proof if one is found, with the route recorded; if not, for the precise obstruction, stated as a
proposition where possible (for instance: a description from `P'` to `Q'`, a level, and `W` not
covered by any block consolidation's `(P', R)`-subchain — or the opposite, a proof that some block
consolidation always works). No route is proposed here beyond Bing's sentence.

### 3.4 Theorem 14's alternating construction

Read against Part VI of the exposition (`Rung`, `exists_half_step`, `exists_next`):

1. **The invariant.** Bing's rungs carry, beyond `Rung`'s data: the same number of links in the
   two `(P, R)`-subchains, `R_1` and `R_2` at the *same position*, and `W_i` covered by
   `Y_{i,n}(P_i, R_i)`.
2. **The base rung** takes `Y_{1,1} = X_{1,1}` and needs a consolidation `Y_{2,1}` of some `X_{2,j}`
   with the same length and the same `R`-position, whose `(P_2, R_2)`-subchain covers `W_2`. The
   length matching is `exists_consolidation_isFrom` refined to prescribe the position of `R_2`
   (blocks singletons up to `R_2`'s block, then one tail block? — only if `W_2` lies before `R_2`'s
   link, which is §3.3 at level `j`).
3. **The point `A`.** In the level `X_{1,j}` (crooked in `Y_{1,1}`), `A` is a point of `M` beyond
   `R_1` whose link returns into the first coarse link `y(1,1)_{P_1}`, with `X_{1,j}(P_1, A)`
   inside `Y_{1,1}(P_1, R_1)`. Such an `A` exists by crookedness of `X_{1,j}` in `Y_{1,1}` read
   between `P_1`'s link and `Q_1`'s link (a link inside the first coarse link occurs after a link
   inside the last-but-one) — but "inside `Y_{1,1}(P_1, R_1)`" for the whole of `X_{1,j}(P_1, A)`
   is a further requirement, again of the §3.3 kind.
4. **Three applications of Theorem 5** (`theorem5`, `Theorem5Statement`), with `D_1 = Y_{1,1}`
   (which must be a level of the description `X_{1,·}` for `theorem5` as stated: `Y_{1,1} = X_{1,1}`
   is; at later rungs `Y_{1,n}` is a level by the alternation) and `D_2 = X_{1,j}`:
   * `E_1` on `u = x_{P_1}`, `v = x(1,j)_{R_1}`, pattern = that of `Y_{2,2}(P_2, R_2)` in `Y_{2,1}`,
     transported to `Y_{1,1}` by position; its values must lie in `[0, pos(y_{R_1})]`
     (`theorem5` needs `h ≤ x t ≤ k`), which is the requirement that `Y_{2,2}(P_2, R_2)` refine
     `Y_{2,1}(P_2, R_2)` — another invariant of the §3.3 kind, to be carried;
   * `E_2` on the links between `R_1` and `A`, "this same pattern" — necessarily read backwards
     (from `R_1`'s coarse link back to `P_1`'s, which contains `A`'s link);
   * `E_3` on the links from `A` to `Q_1`, pattern = that of `Y_{2,2}` in `Y_{2,1}` (values in
     `[0, last]`, from `A`'s link in `y_{P_1}` to `Q_1`'s).
   `theorem5`'s clause "interior links miss `D_1(u) ∪ D_1(v)`" is what keeps the three pieces
   from meeting except at the junctions.
5. **`Y_{1,2}` as a chain.** Its `n`-th link is `E_1(n) ∪ E_2(n) ∪ E_3(n)` (a piece shorter than `n`
   contributing nothing). It must be a chain from `P_1` to `Q_1` (links meet exactly when
   adjacent; `P_1` in the first link only, `Q_1` in the last only), a consolidation of `X_{1,k}`,
   covering `M`. The batch-82 lesson (`not_theorem8_literal`) applies: unions of pieces are not
   automatically a chain. Here the pieces are consolidations of three consecutive subchains of
   the one chain `X_{1,k}`, so cross-intersections can come only from fine links adjacent across
   the junctions at `R_1` (position `pos(y_{R_1})` in both `E_1` and `E_2`) and at `A` (position
   `0` in `E_2` and `E_3`); the report checks this. Whether `Y_{1,2}` is a *block* consolidation of
   `X_{1,k}` (it is not: `E_2`'s fine links are placed in reverse) matters for reuse of
   `Chain.ofBlocks`; `MatchingCovers` (Theorem 11) needs only open covers meeting `M`, so
   block structure is not needed for the final step, but `Rung`'s `IsConsolidationOf` is.
6. **Theorem 11 at the end** with the tracking clause (`MatchingCovers.exists_homeomorph`): the
   constant index sequences `0` and `last` track `P` and `Q` as in `theorem12`; the sequence of
   `R`-positions tracks `R_1` and `R_2` — this is why (2) of the invariant is needed and why the
   skeleton's `theorem14` follows from a `Rung`-like structure carrying `R`-positions.

Bing's alternation runs `Y_{1,3}, Y_{2,3}, Y_{2,4}, Y_{1,4}, Y_{1,5}, …`: two steps on one side,
then two on the other; the side that is a level is refined and the other side follows. The
exposition's `Rung.exists_next` is one half-step; four such half-steps with the extended invariant
are one cycle here.

### 3.5 Theorem 14's implicit hypotheses

* `P_i ≠ R_i` (both `i`): if `R_1 = P_1` and `R_2 ≠ P_2` no `T` exists. The skeleton adds
  `P_i ≠ R_i`; the case `R_i = P_i` for both `i` is `theorem12` on two descriptions from
  `exists_description_from` and is not part of `theorem14`.
* `Q_i ∈ M` is stated explicitly (`Q_i ∉ composant Δ.M P_i` alone allows `Q_i ∉ M`).
* `P ≠ Q` for the ambient description, as everywhere since batch 80.

## 4. Deliverables

1. `exists_irreducible`, `irreducible_unique`, `theorem15_of_theorem14`,
   `exists_description_covering`, `theorem14`, `theorem15`, `sorry`-free where achieved, with
   `#print axioms` in `axioms-batch83.txt`; every reshaped statement recorded with its reason;
   any counterexample in Lean.
2. Report: first line names the commission read; counterexamples first; then the targets in
   order; then, for §3.3 and §3.4, each numbered claim confirmed, corrected, or left open with the
   obstruction stated.
3. `theorem3_end` only after all of the above.

## 5. Not in this batch

The 1951 paper (*Snake-like continua*), which follows.
