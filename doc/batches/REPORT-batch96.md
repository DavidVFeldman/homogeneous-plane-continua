Commission read: `COMMISSION-batch96.md` (batch 96: closing Theorem 9's record; Theorem 11 (Duke 1951), necessity and reconnaissance on sufficiency), with its skeleton `Theorem11.lean`, saved as `HPC/Plane/Theorem11.lean`; `import HPC.Plane.Theorem11` is added at the end of `HPC.lean`.

# Report, batch 96

## Summary

* **Refutations first.** Item 1, `not_separation_of_accumulates`, is **false as stated**. The
  hypothesis `¬ g ⊆ N` allows the open set `N` to miss a point of `g` while containing every point
  of `K ∖ g` near it. The skeleton statement is commented out in the file, with the explanation.
  The refutation is `not_separation_of_accumulates_false`, on the unit interval:
  `g = H = {0}`, `K = [0, 1]`, `N = (0, 1/2)`, `H' = {0}`, `K' = [1/2, 1]`. The corrected statement,
  `not_separation_of_accumulates'`, replaces `¬ g ⊆ N` with `¬ g ⊆ closure N` and is proved; it does
  not need `N` open. This is the form the observation needs: in Bing's setting `diam N < ε < diam g'`,
  so `closure N` cannot contain `g'` either.
* **Item 0: done.** The three `sorry` declarations were removed from
  `HPC/Plane/Atriodic51B.lean`; `theorem9_1951` is now `sorry`-free (details below).
* **§1 (necessity): all four statements proved.** None of the four needed anything beyond chain
  combinatorics plus compactness. Details below.
* **Items 2, 4, 5, 7, 8: proved.**
* **Item 3 (`exists_degenerate_interior_elt`, Q-deg): open.** It is the only remaining `sorry` in
  the new files. The obstruction is stated below.
* **Item 6 / §3.** `theorem11_1951_of_T10` and `theorem11_1951_iff_of_T10` are proved. Their
  hypotheses are the statement of `theorem10_1951` (`hT10`, as in the skeleton) and, as the
  commission allows, the statement of `exists_degenerate_interior_elt` (`hdeg`, shape change).
  Neither proof contains a `sorry`.
* **Build and axioms.** `lake build HPC` passes. `Axioms96.lean` writes `axioms-batch96.txt`.
  Every batch-96 result, and `theorem9_1951`, uses only `propext`, `Classical.choice`,
  `Quot.sound`. The exception is `exists_degenerate_interior_elt` (`sorryAx`), listed there for the
  record.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/Theorem11.lean` | the skeleton, with every item proved except item 3; the refuted item 1 is commented out and replaced |
| `HPC/Plane/Theorem11Nec.lean` | chain combinatorics for §1 (`meets_between`, `chain_ivt`, `chain_two_sets`, `isPreconnected_union_of_separated`, `exists_pos_le_dist`) and the necessity proofs (`isUnicoherent_of_isSnakeLike_aux`, `not_isTriod_of_isSnakeLike`, `isSnakeLike_of_subcontinuum_aux`) |
| `HPC/Plane/Theorem11Gen.lean` | `EpsCoverable`; the chain constructions `chainSingle`, `chainRestrict`, `chainAppend`; `consec_meet`, `exists_trim`, `trim_first`; `epsCoverable_amalgam_gen` |
| `Axioms96.lean`, `axioms-batch96.txt` | `#print axioms` |

**Shape changes.**

* §1: `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsAtriodic` and `IsTriod` are defined only
  over a compact metric space (`Atriodic51Defs.lean`). The skeleton's last three §1 statements,
  written over `X`, therefore do not typecheck, so they are stated over `S` with `[CompactSpace S]`.
  `isSnakeLike_of_subcontinuum` stays over `X`.
* `EpsCoverable` moved to `Theorem11Gen.lean` (same definition).
* `exists_minimal_notCoverable` is stated over `S`, because the Brouwer reduction
  `exists_minimal_of_seq` needs second countability. Its `hε` turned out not to be needed; it is
  kept since it is in the commissioned statement.
* `sides_continua`: `hr` turned out not to be needed; kept.
* `theorem11_1951_of_T10`, `theorem11_1951_iff_of_T10`: extra hypothesis
  `hdeg : ∀ (T : Type u) [MetricSpace T] [CompactSpace T], BingS T → ∃ p : T, bingElt p = {p} ∧ ¬ IsEndElt p`.
  This is the statement of item 3, quantified over compact metric spaces in the universe of `S`. It is
  applied to Bing's minimal counterexample `S'` as a subtype.
* Item 1: the original statement is commented out; `not_separation_of_accumulates_false` refutes
  it and `not_separation_of_accumulates'` is the corrected version.

## Item 0: `theorem9_1951`

`endElt_mem_bingH`, `bingH_irreducible_singleton` and `theorem9_1951` (the three `sorry`
declarations) are deleted from `HPC/Plane/Atriodic51B.lean`; nothing else there is changed,
including its module docstring. In `HPC/Plane/Theorem9B.lean`:

* `endElt_mem_bingH'` is renamed to `endElt_mem_bingH`;
* `bingH_irreducible_singleton'` is renamed to `bingH_irreducible_singleton`;
* `theorem9_1951'` is renamed to `theorem9_1951`.

The primed names are kept as `alias`es, because `Axioms95.lean` (and `REPORT-batch95.md`) refer to
them. The "shape changes" note in that file's docstring is updated. No other existing file was
edited. `axioms-batch96.txt`:
`'HPC.Plane.theorem9_1951' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## §1. Necessity

All four are proved. None needs more than chain combinatorics and compactness. The one existing
chain lemma used is `Chain.inter_link_nonempty_between`; the new combinatorial lemmas
(`Theorem11Nec.lean`) are elementary.

* **12.5, `isSnakeLike_of_subcontinuum`: easy.** Lemma used: `meets_between`. The links meeting a
  preconnected set covered by a chain have consecutive indices; it follows from
  `Chain.inter_link_nonempty_between`. Take the least and greatest index of a link meeting `K`; the
  subchain `Chain.sub` between them covers `K`. Every link of `M`'s chain missing `K` lies outside
  this interval, so the commission's worry about a middle link missing `K` does not arise.
* **12.2, `isUnicoherent_of_isSnakeLike`.** The proof differs from Nadler's and uses only a
  *discrete intermediate value theorem* along a chain (`chain_ivt`). Let `f` be 1-Lipschitz on a
  chain of mesh `< ε`. If the link `i` has a point with `f ≤ c`, the link `j` has a point with
  `f ≥ c`, and `Y` meets every link between them, then some link between contains `y ∈ Y` with
  `|f y − c| < ε`.
  * Suppose `M = H ∪ K` with `H ∩ K = P ⊔ Q`, where `P` and `Q` are closed (from
    `isPreconnected_closed_iff`). Let `δ = dist(Q, P) > 0`, `f = dist(·, P)`, and take the band
    `δ/4 ≤ f ≤ 3δ/4`.
  * The parts of `H` and `K` in the band are disjoint compact sets, since the band misses `P ∪ Q`.
    Let `η > 0` be their distance.
  * Take a chain of mesh `ε = min η (δ/8)`, and links through `p ∈ P` and `q ∈ Q`. Both `H` and `K`
    meet every link between them, so `chain_two_sets` gives `y ∈ H` and `z ∈ K` in one link, both
    in the band. Then `η ≤ dist y z < ε`, a contradiction.
  * **Compactness of `M`** (from `Fold.Q78.IsContinuum`) is used three times: for `δ > 0`, for
    `η > 0` (`exists_pos_le_dist`: a compact set and a disjoint closed set are at positive
    distance), and for the closedness of `P` and `Q`.
* **12.4, `isAtriodic_of_isSnakeLike`.** The batch-92 triod definition is used unchanged. The
  statement proved is `not_isTriod_of_isSnakeLike`: a snake-like continuum is not a triod. The
  atriodic statement follows with 12.5.
  * First, Nadler 6.3 for a subset, `isPreconnected_union_of_separated`: if `T = N ∪ A ∪ R` is
    preconnected, `N` is preconnected and nonempty, and `A`, `R` are separated, then `N ∪ A` is
    preconnected. So the arms `N ∪ A`, `N ∪ B`, `N ∪ C` are connected.
  * Let `f = dist(·, N)`, with `ρ` the least of `f(a)`, `f(b)`, `f(c)` at chosen points. The parts
    of `A`, `B` and `C` in the band `ρ/4 ≤ f ≤ 3ρ/4` are closed, because `closure A ⊆ N ∪ A` and
    the band misses `N`. They are pairwise at distance `≥ η > 0`.
  * Take a chain of mesh `min η (ρ/8)`, with link `m` through a point of `N`. Two of the links
    through `a`, `b`, `c` lie on the same side of `m`; say the link of `a` lies between `m` and the
    link of `b`. Then both arms `N ∪ A` and `N ∪ B` cross every link between `m` and the link of
    `a`.
  * `chain_two_sets` (with `f`, level `ρ/2`) gives `y ∈ A` and `z ∈ B` in one link, both in the
    band. Then `η ≤ dist y z < ε`.
  * The commission's caveat, that points of two arms in a common link need not be close *in `T`*,
    is handled by the band: inside the band the arms are compact and disjoint, hence at positive
    distance, and the discrete intermediate value step puts the common link inside the band.

## §2–3, items 1–8

### Item 1 — `not_separation_of_accumulates`: **refuted** (see the summary)

What the observation needs is `not_separation_of_accumulates'` (proved):

* hypotheses: `H ∩ K = g`, `K ∖ g` accumulates at every point of `g`, and `¬ g ⊆ closure N`;
* conclusion: no pair `H'`, `K'` with `H' ∪ K' = Nᶜ`, `H'` and `K'` separated, `H ∖ N ⊆ H'` and
  `K ∖ (g ∪ N) ⊆ K'`.

Proof: take `x ∈ g ∖ closure N`. Then `x ∈ H ∖ N ⊆ H'`. Also
`x ∈ (closure N)ᶜ ∩ closure (K ∖ g) ⊆ closure ((closure N)ᶜ ∩ (K ∖ g)) ⊆ closure K'`, which
contradicts `H'` and `K'` being separated. So the nondegenerate branch of Bing's proof fails as
written, as the commission observed. The precise condition is "`N` small", meaning
`g' ⊄ closure N`, not merely `g' ⊄ N`.

For nondegenerate `g'`, condition A can hold on one side and fail on the other (the commission's
`S₀` example, bar and `C₁`). As the commission asked, this is recorded only as a remark, with no
Lean refutation.

### Item 2 — `separation_of_degenerate`: **proved**

`U ∪ {p} = Vᶜ` and `V ∪ {p} = Uᶜ`, so both pieces are closed after removing `N`. They intersect only
in `{p} ∖ N = ∅`.

### Item 3 — `exists_degenerate_interior_elt` (Q-deg): **open**

Obstruction:

1. **The suggested route needs two facts that are not in the repository.**
   * The structure of the decomposition space `S/G` as an arc, or at least a usable linear order on
     the elements together with the order topology. The repository has `decompositionSpace_props`
     (compact, connected, `T₁`, nondegenerate) and `exists_two_endElts`, but
     `isArc_of_separatesPairs` is listed as *not attempted*.
   * Kuratowski's statement that the union of the nondegenerate elements is of first category.
     The natural proof goes through the following steps:
     * the sets `F_n = {t : diam π⁻¹(t) ≥ 1/n}` are closed in `S/G` (upper semicontinuity);
     * the points where `t ↦ π⁻¹(t)` is Hausdorff-continuous form a residual set (Fort's theorem
       for upper semicontinuous set-valued maps; not in Mathlib);
     * the elements at such interior points are degenerate.

     I could not establish the last step from the facts available here (Theorem 8 (a)–(c),
     `bingElt_usc`, `bingElt_interior_eq_empty`, hereditary decomposability). What I could derive
     is: at a two-sided continuity point `t` with element `T`, every subcontinuum meeting `T` either
     lies in `T` or contains `T`. I did not find a way to turn this into a contradiction with
     hereditary decomposability when `T` is nondegenerate.
2. **Not refuted either.** I did not find, and did not construct, a `BingS` continuum all of whose
   interior elements are nondegenerate. So the statement is recorded as open, not as false.
3. **What Bing's argument needs.** As the commission notes, Bing's argument needs only *one*
   degenerate element that is not an end element. That is exactly the hypothesis `hdeg` of the
   conditional theorem. The uncountability of `G'` plays no role in the proof below.

### Item 4 — `exists_two_sides`, `sides_continua`: **proved**

* `exists_two_sides`.
  * Not an end element means a cut element (`isEndElt_iff_not_isCutElt`), so `(bingElt r)ᶜ`
    (nonempty, by `bingElt_ne_univ`) is not preconnected. This gives `U`, `V`.
  * Each side is preconnected by property 2: otherwise the complement of the element splits into
    three disjoint nonempty open sets, which contradicts `BingS.no_three_open`. The lemma is
    `side_isPreconnected`.
* `sides_continua`.
  * Nadler 6.3 in the closed form `isContinuum_side` (batch 95) shows that each side together with
    the element is a continuum.
  * Each is proper, because the other side is nonempty.
  * The hypothesis `hr` is not needed.

### Item 5 — `condA_side` (Q-A): **proved**, by the route in the commission

* `H = U ∪ {p}` is a continuum (item 4), nondegenerate, and `BingS` as a subtype
  (`bingS_subcontinuum`).
* `{p}` is an element of `H`. By `bingElt_subtype_subset`, the element of `p` computed in `H` lies
  in the element of `p` computed in `S`, which is `{p}`.
* Its complement in `H` is the preimage of `U`, which is connected. So `{p}` is not a cut element of
  `H`, hence it is an end element of `H` (`isEndElt_iff_not_isCutElt`).
* For a nondegenerate subcontinuum `L ∋ p` of `H`, apply `endElt_inter_contains_endElt` (batch 95)
  in the space `H` with `Y = L`. It gives an end element `e` of `L`, contained in `{p}`.
* Take a second end element `e'` of `L` whose element differs from that of `e`
  (`exists_two_endElts`). Theorem 8 (c) for `L` (`bingElt_irreducible`) makes `L` irreducible
  between `p` and `e'`; this is transported back through the two subtype layers.

### Item 6 — Theorem 10 for each side

Item 6 is used in the form "each": `hT10` is applied to `H` and to `K` separately, inside
`theorem11_1951_of_T10`. Condition A is transported from the subtype `S'` to `S` by
`condA_image_val`, and the chains given by `hT10` refine the chosen `ε`-chains, so they are again
`ε`-chains (`isEpsChain_of_refines`).

### Item 7 — `epsCoverable_amalgam`: **proved** (general form `epsCoverable_amalgam_gen`, for any `Z ⊆ H ∪ K`)

Bookkeeping, and the facts used:

* **Bing's middle link `(H'·h_m) ∪ N ∪ (K'·k₁)` can have diameter close to `2ε`.** Its two
  outer pieces have diameter `< ε` each and meet only near `p`. Theorem 10 refines a given chain,
  so it does not shrink the end links, and the minimal counterexample only provides `ε`-chains for
  `H` and `K`, not `ε/2`-chains. The chain built here therefore keeps `h_m` and `k₁` as separate
  links. The only new link is a small ball `N = B(p, ρ)`, with `2ρ ≤ ε/2`:
  `h₁ ∩ O_H, …, h_m ∩ O_H, N, k₁ ∩ O_K, …, k_n ∩ O_K`.
* **Trimming (`trim_first`).** Both chains are first cut down to the links meeting `H` (resp.
  `K`). This uses `exists_trim` (min/max index plus `meets_between`) and `Chain.sub`, and keeps
  "`p` in the end link only, and in no other link's closure".
* **Consecutive links meet inside the covered set (`consec_meet`).** This answers the commission's
  question: in a chain all of whose links meet a preconnected set `C` that it covers, consecutive
  links meet *inside* `C`. Otherwise the links up to `i` and the links from `i + 1` on would
  disconnect `C`. This is why trimming comes first.
* **The ball.** `ρ` is chosen so that:
  * `B(p, ρ)` lies in `h_m ∩ k₁` and misses the closures of all other links (finitely many);
  * `ρ ≤ ε/4`;
  * `H` and `K` both reach distance `ρ` from `p`, which is possible since both are
    nondegenerate. The degenerate cases `H = {p}` or `K = {p}` are trivial: one chain already
    covers `Z`.
* **Open separation.** `H ∖ B(p, ρ/2)` and `K ∖ B(p, ρ/2)` are disjoint closed sets, so they
  have disjoint open neighbourhoods `O_H`, `O_K` (`normal_separation`).
* **Adjacency.** Consecutive links on the `H` side meet at points of `H` in `h_i ∩ h_{i+1}`. Such a
  point lies in a non-end link, hence outside `B(p, ρ/2)`, hence in `O_H`. The links `h_m ∩ O_H`,
  `N`, `k₁ ∩ O_K` meet at points of `H` (resp. `K`) at distance exactly `3ρ/4` from `p`, which exist
  by the intermediate value theorem on the connected sets `H`, `K`. Links on opposite sides are
  disjoint, because `O_H ∩ O_K = ∅`. Non-end links miss `N`.
* **Chain constructions.** The general constructions are `chainRestrict`, `chainSingle` and
  `chainAppend` (concatenation of two chains that meet only at the junction).

### Item 8 — `exists_minimal_notCoverable`: **proved**

Brouwer reduction (`exists_minimal_of_seq`, batch 93) is applied to the property
"subcontinuum of `M`, not `ε`-coverable". It passes to decreasing intersections for two reasons:

* the intersection is a continuum (`isContinuum_iInter_antitone`);
* a chain covering the intersection covers some member (`exists_subset_of_iInter_subset`; the union
  of a chain is open, and the sets `K_n ∖ ⋃ links` are decreasing compact sets).

Batch 90's hyperspace lemma `isClosed_notCoverable` was not needed.

### §3 — `theorem11_1951_of_T10`, `theorem11_1951_iff_of_T10`: **proved, conditionally on `hT10` and `hdeg`**

Assembly:

1. If `S` is not snake-like, some `ε` has no covering `ε`-chain.
2. Take a minimal non-coverable `S'` (item 8). It is nondegenerate, since a point is covered by one
   ball, and `BingS` as a subtype (`bingS_subcontinuum`).
3. `hdeg` gives a degenerate element `{p}` of `S'` that is not an end element.
4. Its sides give continua `H`, `K` (item 4), proper in `S'`, hence `ε`-coverable.
5. Condition A holds for `p` on each side (item 5).
6. `hT10` gives `ε`-chains with `p` in the first link only; the chain for `H` is reversed.
7. `epsCoverable_amalgam_gen` covers `S'`, which is a contradiction.

The equivalence uses §1 for necessity. For sufficiency it assembles `BingS` from the instances and
hypotheses.

## Not attempted (as instructed)

`covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of `theorem10_1951`,
`exists_tame_chain_near`, `isArc_of_separatesPairs`.
