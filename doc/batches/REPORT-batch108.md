Commission read: `COMMISSION-batch108.md` — batch 108, the arcs paper's (Bing 1948, Amer. J. Math.) Theorem 5 and Corollary 2; Duke Theorem 12 in Bing's generality.

# Report, batch 108

**Refutations: none.** No skeleton statement is false.

All four items are **proved**, with no `sorry`. `lake build HPC` succeeds and reports exactly the
five existing `declaration uses sorry` warnings (`theorem3_end`, `covering_step`, `theorem14`,
`exists_tame_chain_near`, `fugate_cor1`). None comes from the new file, and the new file contains
no `sorry` text. All six new main declarations depend only on `propext`, `Classical.choice`,
`Quot.sound` (`doc/batches/audits/axioms-batch108.txt`).

## 0. Files

* `HPC/Plane/Arcs48.lean`: the skeleton, saved as asked, with every proof filled in. Proof-internal
  lemmas are in the namespace `HPC.Plane.Arcs48`.
* `HPC.lean`: `import HPC.Plane.Arcs48` added as the last line.
* `Axioms.lean`: new group `## Bing 1948, Amer. J. Math. (arcs paper; batch 108)` (four lines:
  `exists_irreducibleAbout`, `arcs_theorem5`, `arcs_theorem5_point`, `arcs_corollary2`), placed
  after the Duke group; two lines (`condA_of_condB_general`, `theorem12_1951_general`) added to the
  Duke group after batch 106's Theorem 12. `axioms.txt` regenerated (243 lines, up from 237;
  `sorryAx` still in exactly 9 lines; the diff is only the six new lines).
* Audit: `doc/batches/audits/Axioms108.lean`, its output `axioms-batch108.txt`, and the pre-edit
  `axioms-before-batch108.txt`.
* Filing: commission → `doc/batches/COMMISSION-batch108.md`; skeleton →
  `doc/batches/skeletons/Arcs48.lean`; the scan → `doc/sources/bing1948-arcs.pdf` (PDFs are
  git-ignored in this repository, as for the other sources).
* No other existing file was edited.

## 1. Shape changes (all recorded in the file header)

1. **`arcs_theorem5` did not elaborate as uploaded**: `Dense[instTopologicalSpaceSubtype] …` is not
   valid syntax (it parses as `GetElem`). It is now `Dense ((↑) ⁻¹' (⋃ …) : Set M)`, which is the
   same statement with the subspace topology inferred.
2. **`Cuts`** now uses Bing's literal clause. Page 497 reads: "If `M` contains a continuum
   intersecting both `A` and `B` and `R` is a set containing neither `A` nor `B` but intersecting
   each continuum in `M` intersecting both `A` and `B`, we say that `R` cuts `A` from `B` in `M`."
   Bing uses "contains" for inclusion throughout ("`M` contains a continuum", "`N` contains an open
   subset `E`"), so the clause is `¬ A ⊆ R ∧ ¬ B ⊆ R`, which is weaker than disjointness. The two
   readings coincide when `A`, `B` are points (the paper's main use: "cuts two points"). The new
   `Cuts` is weaker, so `¬ Cuts` (Corollary 2) is stronger. The proof of Corollary 2 does not use the
   clause at all, so the corollary holds under either reading.
3. **`IsClosed R` removed** from `exists_irreducibleAbout` and `arcs_theorem5`: neither proof uses it,
   and Bing's Theorem 5 says "each proper subset `R`". `R.Nonempty` is kept: for `R = ∅` the union is
   empty and the statement is false, so Bing's "proper subset" must mean nonempty.
4. **`hM : IsContinuum M` removed** from `condA_of_condB_general` and `theorem12_1951_general`: it is
   not used (each `W` in condition A is a continuum by hypothesis, and Theorem 5 is applied to `W`).
   The ambient compact metric space `S` is still required.

## 2. Items

### Item 1. `exists_irreducibleAbout` — proved

Zorn on `{W ⊆ M | W continuum, R ⊆ W}` under reverse inclusion, as in batch 83's
`exists_irreducible`: a chain's intersection is compact, contains `R` (so is nonempty), and is
preconnected by `T14.isPreconnected_sInter_chain`.

### Item 2. Theorem 5 (`arcs_theorem5`, `arcs_theorem5_point`) — proved

The proof keeps Bing's two cases. The second case is isolated as `Arcs48.exists_point_dense`: *for a
nonempty proper subcontinuum `N` of `M` there is `p ∈ M ∖ N` such that the union of the
subcontinua of `M` containing `N` and missing `p` is dense in `M`.* For `N ⊋ R` irreducible about
`R`, such continua meet `R`, which gives Theorem 5. `arcs_theorem5_point` is the case
`N = R = {r}`: it is `exists_point_dense` applied to `{r}`, which is a proper subcontinuum because
`M` is nondegenerate.

The structure of the proof:

* `Arcs48.tight_or_point` covers Bing's sequence `N₁ ⊆ N₂ ⊆ …`. Either the point exists directly, or
  `N' = closure (⋃ Nᵢ)` is a proper subcontinuum containing `N` which is *tight*: it is not
  contained in the relative interior of any proper subcontinuum of `M` (`Arcs48.Tight`).
* `Arcs48.exists_point_of_tight` is the Baire argument for a tight `N`.
* `Arcs48.exists_nowhereDense_piece` handles one `Dᵢ`: the sets `Eᵢ`, `Fᵢ`, `Eᵢ ∩ Fᵢ` and the
  continuum `Gᵢ`.
* `Arcs48.isPreconnected_closure_diff_union` proves "`Fᵢ + N` is a continuum".

### Item 3. Corollary 2 (`arcs_corollary2`) — proved

**Argument (Bing gives none).** Theorem 5 with `R = {r}` is applied twice.

1. Take any `r ∈ M`. Theorem 5 gives `p ≠ r` such that the continua in `M ∖ {p}` through `r` have
   dense union.
2. Such a `p` cuts no two nonempty open subsets `D ∩ M`, `E ∩ M`. By density, some continuum
   `K₁ ∌ p` through `r` meets `D ∩ M`, and some continuum `K₂ ∌ p` through `r` meets `E ∩ M`. Then
   `K₁ ∪ K₂` is a continuum in `M` meeting both and missing `p`.
3. Apply Theorem 5 again with `r := p`. This gives `q ≠ p` with the same property.

Nothing beyond the point form of Theorem 5 is needed. In particular, the "contains neither" clause
of `Cuts` and the existence clause are never used.

### Item 4. Duke Theorem 12 in general (`condA_of_condB_general`, `theorem12_1951_general`) — proved

Let `W ∋ p` be a nondegenerate subcontinuum of `M`. `arcs_theorem5_point` (applied to `W`, `r = p`)
gives `q ∈ W`, `q ≠ p`, with `W ⊆ closure ⋃ {K ⊆ W continuum : q ∉ K, p ∈ K}`. Let `H ⊆ W` be a
subcontinuum containing `p` and `q`. For each `K` in the family, condition B gives `K ⊆ H` or
`H ⊆ K`, and `H ⊆ K` is impossible because `q ∈ H ∖ K`. So the union lies in `H`, hence so does its
closure (`H` is closed), so `W ⊆ H`. Therefore `W` is irreducible between `p` and `q`.

**Deviation from the commission's route:** it is simpler than "the family is nested, so the union
is connected and its closure is a continuum equal to `M'`". Nestedness and connectedness of the
union are not needed, only that every member lies in `H`.

`theorem12_1951_general` combines this with batch 85's `condB_of_condA`. Batch 106's
`condA_of_condB`/`theorem12_1951` (snake-like `M`, via Fugate's Lemma 3) are now special cases.
They were left unedited, as the commission requires.

## 3. Ledger: the arcs paper's Theorem 5

Each point raised in §2 of the commission, settled.

1. **First case (`M = N`): from "no such `E`" to density.**
   * Suppose the union `V` is not dense, and let `O = M ∖ closure V`. Then every continuum in `M`
     that meets `R` and `O` contains `p`, because otherwise it would lie in `V`.
   * Every point of `R` lies in `V`, since `{r}` is such a continuum. Hence `R ∩ O = ∅`.
   * To get Bing's `E` with closure inside `O` and `p ∉ Ē`, pick `x' ∈ O ∩ M` with `x' ≠ p` and set
     `E = ball(x', δ)` with `δ ≤ ε/2` and `δ ≤ dist(x', p)/2`. Then `Ē ⊆ closedBall ⊆ O`, and
     "meets `Ē`" is handled by this closed ball.
   * The step Bing leaves out is that such an `x'` exists even when the non-approached point is `p`
     itself. If `O ∩ M = {p}`, connectedness of `M` forces `M ⊆ O`, which contradicts
     `∅ ≠ R ⊆ M ∖ O` (`Arcs48.exists_other_point`).
   * The commission's worry ("density needs it to meet `E`, not `Ē`") disappears this way: one
     argues by contradiction from a point not in `closure V`, and density is exactly
     `M ⊆ closure V`.
2. **"Each component of `N − E` containing a point of `R` contains `p`"; "a continuum in `N − E`
   containing `R`".**
   * Boundary bumping (`exists_continuum_bump_closed`) gives, for each `r ∈ R`, a continuum
     `K_r ⊆ N ∖ E` through `r` that meets `Ē`. Hence `K_r` contains `p`.
   * All these continua share the point `p`, so they lie in one component, the component of `p` in
     `N ∖ E`. That component is closed. So there is no infinite-union issue: Bing's union of
     components is a *single* component.
   * Formally we take `C = closure (⋃_r K_r)`. It is connected (common point `p`), contained in the
     closed set `N ∖ E`, and contains `R`. It is proper because it misses `x'`. This contradicts
     irreducibility about `R`. Neither compactness of `R` nor closedness of `R` is used.
3. **Second case: "a point of `M − ΣNᵢ`" needs `ΣNᵢ ≠ M`.** Bing's choice does exclude the cone
   example.
   * Whenever `N_{i+1} ≠ Nᵢ`, the construction gives `Nᵢ ⊆ int_M N_{i+1}`.
   * If `⋃ Nᵢ = M`, there are two possibilities:
     - Only finitely many steps change the set. Then `⋃ Nᵢ` is one `N_k`, which is proper.
     - Infinitely many steps change it. Then the relative interiors cover `M`, compactness gives one
       of them, and `M = N_k`. This is a contradiction.
   * In the cone example, `N_{k-1}` is not in the interior of `N_k`, so that sequence is never
     produced.
   * Formalised in `Arcs48.tight_or_point` with the increasing open sets
     `Wₙ = ⋃ {O open : O ∩ M ⊆ Nₙ}` and `IsCompact.elim_directed_cover`.
4. **"For convenience, suppose that `ΣNᵢ = N`."** Justified by passing to `N' = closure (⋃ Nᵢ)`.
   * `N'` is a proper subcontinuum (closure of an increasing union of continua, not dense) and
     contains `N`.
   * `N'` lies in no relative interior of a proper subcontinuum `K` of `M`. Suppose it did. Since
     `M` is connected, the open set `O ⊇ N'` with `O ∩ M ⊆ K` contains a point `q ∈ M ∖ N'`. A basic
     set `Dⱼ ∋ q` inside `O ∖ N'` would then have been absorbed into `N_{j+1} ⊆ N'` at step `j`,
     which is a contradiction.
   * The point found for `N'` works for `N`: `p ∉ N' ⊇ N`, and continua containing `N'` contain `N`.
   * The property Bing uses, "`N` does not belong to any open subset of any proper subcontinuum of
     `M`", is proved for `N'`. It need not hold for the non-closed set `⋃ Nᵢ`.
   * The countable family `Dᵢ` is taken as a countable basis of `S` (traced on `M`) rather than of
     `M ∖ N`. This is harmless.
5. **"`Eᵢ · Fᵢ` contains no open subset of `M`": not a gap.**
   * `Eᵢ ∩ closure (M ∖ Eᵢ) = Eᵢ ∖ int_M Eᵢ` for any `Eᵢ ⊆ M`. If a relatively open `W` lay inside
     it, then `W ⊆ Eᵢ`, so `W ⊆ int Eᵢ`, so `W = ∅`. It is also closed.
   * So `Eᵢ` need not be open, and the commission's suspected gap does not arise.
   * Moreover, the *maximality* of `Eᵢ` (being a component) is never used. Any continuum `Eᵢ` with
     `N ⊆ Eᵢ ⊆ M ∖ Dᵢ` meeting `closure Dᵢ` works. The formal proof takes `Eᵢ = K ∪ N` with `K` from
     boundary bumping.
6. **Baire.** It is applied in the compact metric subspace `M` (a Baire space) to the countably many
   closed sets `Eᵢ ∩ Fᵢ`, which have empty relative interior, and to the nonempty relatively open
   set `M ∖ N`. This gives `p ∈ M ∖ N` outside every `Eᵢ ∩ Fᵢ`.
7. **"`Fᵢ + N` is a continuum."** Bing's argument is correct once two unstated facts are supplied.
   Let `Fᵢ ∪ N = X ⊔ Y`, closed and disjoint, with `N ⊆ X` and `Y ≠ ∅`.
   * `X ∪ Eᵢ` is connected. If `X ∪ Eᵢ = Q₁ ⊔ Q₂` with `Eᵢ ⊆ Q₁`, then `Q₂` is disjoint from the
     closed set `Q₁ ∪ Y`, and `M = Q₁ ∪ Q₂ ∪ Y`. So `Q₂` is clopen in `M`, hence empty.
   * `X ∪ Eᵢ ≠ M`. If `Y ⊆ Eᵢ`, then `M ∖ Eᵢ ⊆ X`, so `Fᵢ ⊆ X` and `Y = ∅`. So some point of `Y`
     lies outside `Eᵢ`, and that point is not in `X ∪ Eᵢ`.
   * The open set `M ∖ Y ⊇ N` lies in `X ∪ Eᵢ`, which contradicts tightness.

   (`Arcs48.isPreconnected_closure_diff_union`.)
8. **`Gᵢ`, and "`ΣGᵢ` is dense".**
   * `Gᵢ` is `Eᵢ` if `p ∉ Eᵢ`, and `Fᵢ ∪ N` otherwise (then `p ∉ Fᵢ`, since `p ∉ Eᵢ ∩ Fᵢ`). It
     contains `N`, misses `p`, and meets `closure Dᵢ`: `Eᵢ` by boundary bumping, and `Fᵢ ⊇ Dᵢ ∩ M`.
   * Density needs, for a point `x ∈ M ∖ N` and an open `O ∋ x`, a basic `Dᵢ ∋ x` with
     `closure Dᵢ ⊆ O ∖ N`. This uses regularity, through `IsTopologicalBasis.exists_closure_subset`.
     Then `Gᵢ` meets `closure Dᵢ ⊆ O`.
   * Points of `N` are in the union already.
   * Bing's "each `Dᵢ`'s points are approached" is correct with this choice of `Dᵢ`. Shrinking to
     the closure is the step he omits.
9. **Hypotheses.** `R` need not be closed (Bing: "proper subset"). `R` must be nonempty. `M` is a
   compact continuum in a compact metric space.

## 4. Not attempted

As instructed: the five open targets; the arcs paper's Theorems 1–4 and 6–13.
