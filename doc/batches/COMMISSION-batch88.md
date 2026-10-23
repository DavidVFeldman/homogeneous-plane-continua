# Commission: batch 88 — Bing, *Concerning hereditarily indecomposable continua* (Pacific J. Math. 1 (1951), 43–51), Theorem 1 and its consequences

**Go!** Runs on top of the latest delivery (batch 85, which was run after 86 and 87). Two files
accompany this commission as separate uploads, not an archive:

* `COMMISSION-batch88.md` — this text (also pasted into the prompt);
* `PseudoArc51.lean` — a skeleton of one definition and nine statements, all `sorry`, all work
  items. Save it as `HPC/Plane/PseudoArc51.lean` and add `import HPC.Plane.PseudoArc51` at the end
  of the root `HPC.lean`. Nothing else is to be replaced. Shapes of the auxiliary statements may
  be adjusted with the change recorded; `theorem1_HIC`, `theorem1_HIC'`, `isPseudoArc_iff_endPoints`
  keep their conclusions.

The report names the commission read in its first line.

## 0. On batch 85, and what this paper is for

Audited: six of seven statements proved, `theorem10_1951` open at one sentence of Bing's surgery;
standard axioms; the unused `IsContinuum M` hypotheses dropped. Recorded: condition C's "in no
other link" is not used by the necessity of Theorem 13.

The present paper is the source of the three results *Snake-like continua* quotes as its
Theorems 1–3. Its Theorem 1 — any two nondegenerate chainable hereditarily indecomposable continua
are homeomorphic, and any point pair from different composants can be carried to any other such
pair — is the theorem that makes "the pseudo-arc" a single topological object. Its proof is the
argument of Bing 1948 Theorem 13 run on an arbitrary chainable hereditarily indecomposable
continuum instead of a described one, and the repository has nearly every piece. This batch is
Theorem 1 and what follows from it; §3 (Theorem 2, Baire category in the hyperspace), §4
(Theorems 3–4, monotone decompositions) and §5 (Example 2, Theorem 5, plane topology) are for
later batches or not at all (§5 rests on Moore's decomposition theorem for the plane).

## 1. Targets, in order

1. **`exists_description_of_chainable_HI`**: a nondegenerate chainable hereditarily indecomposable
   continuum `M` (compact, in a metric space, no compactness of the ambient space) and points
   `p, q ∈ M` with `q ∉ composant M p` admit a description `Δ : Description X p q` with `Δ.M = M`.
   This is the body of Bing's proof (§2 below). Its steps, in the repository's terms, are in §3.
2. **`theorem1_HIC`** (the "in fact" clause): two such continua `M ⊆ X`, `M' ⊆ X'`, pairs `(p, q)`,
   `(p', q')` from different composants, a homeomorphism `M ≃ₜ M'` carrying `p ↦ p'`, `q ↦ q'`.
   From item 1 twice and `theorem12`; `theorem12` assumes compact ambient spaces, so restrict to
   `M`, `M'` as `Transfer.lean` does for `theorem13` (`theorem13_of`) — a `theorem12_of` is wanted.
3. **`theorem1_HIC'`**: the same without points: `Nonempty (M ≃ₜ M')`. Needs a pair from
   different composants in each: `composant_ne_of_indecomposable` (Bing 1948 batch 81) applied to
   `M` itself, which is indecomposable.
4. **`IsPseudoArc`** (definition: nondegenerate, chainable, hereditarily indecomposable) and the
   consequences Bing draws on p. 45: **`homogeneous_of_isPseudoArc`** (from item 1 and
   `theorem13_of`, or directly from item 2 with `M = M'`), and **`isPseudoArc_of_subcontinuum`**
   with **`homeomorphic_subcontinuum`**: a nondegenerate subcontinuum of a pseudo-arc is a
   pseudo-arc, hence homeomorphic to it. Needs: a subcontinuum of a chainable continuum is chainable
   (the links meeting it form an index interval, `Chain.meet_ordConnected` or `exists_chain_last_only`
   from batch 85/86; the trimmed chain covers it); hereditary indecomposability passes to
   subcontinua by definition.
5. **`isPseudoArc_of_description`**: the continuum of any description (Bing 1948) is a pseudo-arc
   in this sense — chainable (each level is an `ε_i`-chain covering `M`), hereditarily
   indecomposable (`theorem10`), nondegenerate when `P ≠ Q`. In particular `Plane.pseudoArc_exists`'s
   continuum is one, and by item 3 every pseudo-arc is homeomorphic to it.
6. **`isPseudoArc_iff_endPoints`** — Bing 1951 (*Snake-like continua*) Theorem 16, now complete: a
   nondegenerate snake-like continuum is a pseudo-arc iff every point is an end point
   (`IsEndPoint`, batch 85). Necessity: given `p`, take `q ∉ composant M p` (item 3's lemma) and the
   description from `p` to `q` (item 1); its levels are `ε_i`-chains from `p` to `q` covering `M`, so
   `p` lies in the first link only — condition C. Sufficiency: `exists_not_endPoint_of_not_HI`
   (batch 85) and the definition. Bing's own proof of necessity says "if `p` and `q` are points of
   different composants of a pseudo-arc, they are opposite ends of it", which is item 1 read at
   each level; state that too (**`oppositeEndPoints_of_composants`**, with `OppositeEndPoints` from
   batch 85).
7. **`theorem1_snake`**: *Snake-like continua* Theorem 1 as stated there (two nondegenerate
   snake-like hereditarily indecomposable continua are homeomorphic) — item 3 under the names of
   that paper (`IsSnakeLike`), so that the 1951 record is closed on this point.

## 2. Bing's text (pp. 43–45), transcribed

[Quotation moved to doc/sources/transcriptions/bing51pacific.md, §doc/batches/COMMISSION-batch88.md, 2. Bing's text (pp. 43–45); batch 204.]

## 3. Facts about the text, and the steps in the repository's terms

1. **The sequence `C_i`.** Refinement with each link meeting `M`: batch 84's `refine_step` /
   `MinCover` (minimal covering subchains have every link meeting `M`, and a chain of mesh below a
   Lebesgue number of the previous cover refines it). The repository's crookedness `IsCrookedIn'`
   is read on links that *meet* `D_h`, `D_k`; Bing's on links *in* them. `IsCrookedIn'.isCrookedIn`
   relates them; the report says which reading item 2 below produces, and converts if needed (a
   refinement crooked in the meet-sense is crooked in the containment sense trivially; the
   converse is where the two differ).
2. **Crookedness eventually** (the paragraph "First, we show …"): the new lemma of this batch.
   Read closely, the argument is: if no `C_m` is crooked in `C_1` then for a fixed pair `(h, k)`,
   `k − h > 2`, infinitely many `m` carry a failure witnessed by links `c_{m,i} ⊆ c_{1,h}`,
   `c_{m,j} ⊆ c_{1,k}`, a *first* link `c_{m,r} ⊆ c_{1,k−1}` between them, and no link in `c_{1,h+1}`
   between `c_{m,r}` and `c_{m,j}`. The spans `W_m` (from `i` to `r`) and `V_m` (from `r` to `j`) are
   `1/m`-chained (`Chain.chainedAt_span`), share the link `c_{m,r}`, and their limit superiors `W`,
   `V` (`T13.limSup` along a subsequence; connected by `T13.isPreconnected_limSup`, inside `M`,
   meeting each other) are continua whose union `W ∪ V` is a subcontinuum of `M`. The
   contradiction needs *neither contains the other*. Bing says `W` meets `c̄_{1,h}` and misses
   `c̄_{1,k}`, `V` the reverse. What is clean: the links of `W_m` lie in `c_{1,l}` for `l ≤ k − 2`
   (the refinement index moves by one per link and never takes the value `k − 1` before `r`), so
   `W` is disjoint from the *open* link `c_{1,k}`; likewise `V` is disjoint from the open links
   `c_{1,h}` and `c_{1,h+1}`. What needs care: that `V` has a point outside `W` and `W` a point
   outside `V`. A limit of points of `c_{m,j} ⊆ c_{1,k}` lies in `M ⊆ C_1^*`, hence in some open
   `c_{1,l}` that contains those points eventually, so `l ∈ {k−1, k, k+1}`; if `l ≠ k − 1` it is
   outside `W`, but `l = k − 1` is not excluded by the text. The report either closes this (for
   instance by choosing the failing pair with the largest possible `k − h`, or by using
   `c_{m,r} ⊆ c_{1,k−1}` and a point of `c_{m,j}`'s neighbours, or by a different pair of
   witnesses), or states the corrected argument. This is the one place where Bing's text may be
   short of a proof; the statement itself (some `C_m` is crooked in `C_1`) is what item 1 needs,
   and a proof by any route is acceptable.
3. **Subsequence.** Iterate item 2 with `C_{n_i}` in place of `C_1` (its tail is again a
   refining sequence of `1/m`-chains covering `M`).
4. **Subchain from `p` to `q` meets both end links.** This is `exists_subchain_meets_ends'`
   (batch 81) with a description replaced by the sequence `C_{n_i}`: the limit argument uses only
   that the spans are chained, lie in `M`'s covers, contain `p` and `q`, and miss an open set
   meeting `M` — `false_of_disjoint_limit` generalized from `Δ.D k` to any sequence of chains
   covering `M` with mesh `→ 0`. `p ≠ q` from `q ∉ composant M p` and nondegeneracy
   (`mem_composant_self` needs `M` nontrivial). Note that Bing's "each such limiting set is `M`"
   uses that `p`, `q` are in different composants exactly as batch 81 did.
5. **Theorem 4 on the subchain**, then closures: `Chain.exists_blockChain` (batch 81) gives, from
   `theorem4_pair`, a chain from `p` to `q` that is a block consolidation of `C_{n_k}` with each
   block in three consecutive links of `C_{n_j}` (Bing: two adjacent; three is what the repository
   has, and it only changes the mesh constant). Closures inside links of a shallower `C_{n_L}`:
   the Lebesgue-number step of `exists_step` (batch 81), with `closure (C_{n_{j+1}})^*` compact —
   here the covers are of `M` only, so use `M` itself as the compact set (all chains cover `M`, and
   the blocks are unions of links meeting `M`; their closures need not lie in `M`, so the Lebesgue
   number must be taken for the cover of a compact set containing the blocks: `closure` of the
   union of a deep level's links is compact only if the ambient space is proper — instead, shrink:
   the report says how the closure clause is obtained; one route is to intersect every link with
   a fixed open neighbourhood of `M` of compact closure when `X` is proper, another is to choose
   the deep level's mesh so small that each block lies within a Lebesgue ball about a point of `M`,
   which is what `exists_step` in fact does — the ball, not the level's closure, carries the
   closure). Assemble the description by `exists_description_of_steps` (batch 83), which takes
   exactly "for every `L` a step chain from `p` to `q`, consolidation of a deep level, closures in
   `C_L`'s links, mesh `≤ 1/(L+1)`" — with the levels now `C_{n_i}` rather than `Δ.D i`, so the
   assembly is to be restated for a general refining sequence (its proof does not use
   crookedness of the given levels except through Theorems 1–2 to make the new levels crooked,
   `isCrookedIn'_of_isConsolidationOf`, `isCrookedIn'_of_refines`).
6. **`Δ.M = M`.** `⋂ D_i^* ⊇ M` since every `D_i` covers `M`; `⊆` since a point of every `D_i^*`
   is within `3/i`-ish of `M` (each block meets `M`) and `M` is closed.
7. **Theorem 12 without a compact ambient space.** `theorem12` has `[CompactSpace X₁]
   [CompactSpace X₂]`. Restrict both descriptions to the compact subspaces `M`, `M'` themselves
   (links intersected with `M` are open in `M`; `IsFrom`, crookedness, closures, diameters
   restrict; the continuum is `M`), as `Transfer.lean` restricts to `closure (D 0)^*`. State
   `theorem12_of` in that generality.
8. **Implicit hypotheses.** Nondegeneracy of `M` is used (Bing states it); `p ≠ q` follows from
   the composant hypothesis. Compactness of `M` is in "compact continuum". No other hypothesis
   was found necessary; the report confirms or corrects.

## 4. Deliverables

1. The statements of `PseudoArc51.lean`, `sorry`-free where achieved, with `#print axioms` in
   `axioms-batch88.txt`; reshaped statements recorded; any counterexample in Lean.
2. Report: first line names the commission read; counterexamples first; then targets 1–7 in
   order; then §3 items 2, 5, 7 in detail (item 2: which argument closes "neither contains the
   other").
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `theorem10_1951`.

## 5. Not in this batch

§3 Theorem 2 (Baire category in the hyperspace of continua; needs a pseudo-arc inside any chain
of balls along a broken line in `ℝⁿ` or Hilbert space — a generalization of batch 84's planar
construction); §4 Theorems 3–4 (monotone decompositions; statable with a monotone continuous
surjection onto a compact metric space); §5 (plane topology, Moore's theorem). Candidates for
batches 89–90 in that order.
