# Commission: batch 199 — Part G, II: Domokos–Prajs Theorem 6.1; Bing–Jones Theorems 7 and 9

**Go!** This batch runs on top of the batch-198 work. Three files come with it, as separate
uploads:

* `COMMISSION-batch199.md`: this text, also pasted into the prompt.
* `BJ59B.lean`: the skeleton.
  * Save it as `HPC/BJ59/BJ59B.lean`. You may split it under `HPC/BJ59/`.
  * Add `import HPC.BJ59.BJ59B` at the end of `HPC.lean`. Adjust the skeleton's imports as needed.
  * Save copies under `doc/batches/` (`COMMISSION-batch199.md`, `skeletons/BJ59B.lean`) and
    include them in the tarball, as in batch 198.
* `domokos-prajs2022.pdf`: **new source**, A. Domokos and J. R. Prajs, *The Planck boundary within
  the hyperspace of the circle of pseudo-arcs*, arXiv:2203.15906v1 (March 2022). Save it as
  `doc/sources/domokos-prajs2022.pdf`. Only §6 (pp. 13–14) is used.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before, including the test of every named `Prop` and every
  new definition on degenerate inputs.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more (400 dpi for subscripts, primes, tildes and bars), not
  against the text layer.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Bing–Jones 1959, II (batch 199)");
  * `README.md`;
  * `LEDGER.md`: a new section "Domokos–Prajs 2022 and Bing–Jones §§4–5 (batch 199)";
  * `OPEN.md`;
  * `doc/notes/bj59.md` (append).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 198

* **Delivery.** The download was current (`axioms.txt` 3507 lines, equal to the tarball's). The
  commission, skeleton and source copies are byte-identical to what I sent.
* **Audit.** The sixteen new files declare 122 theorems. The audit lists 119 of them and the
  reused `isUnicoherent_of_isSnakeLike`, all on exactly the three standard axioms; `sorryAx` in
  none. Three `@[simp]` lemmas are missing from the audit and from `Axioms.lean`:
  `chainRestrict_link`, `halfFibreEquiv_apply`, `halfFibreEquiv_symm_apply` (the report's "120 new
  theorems" counts the audit). Add them this time (§11). The new files contain no `sorry`, `admit`
  or `axiom` outside comments; all twenty skeleton declarations are textually the skeleton's.
* **Results.** Everything proved, the stretch included: the classification from the three named
  inputs, Bing–Jones Theorems 2–4 and 6, Theorem 5 repaired, and the certificate against Theorem 5
  as printed. Your route changes are improvements: rotating the map for homogeneity, the
  aposyndesis dichotomy in the decomposable case, and `not_isPseudoArc_of_ne_univ_circle` for
  `C₁ ≄ C₃`. Thank you.
* **Ledger.** BJ.1–BJ.16 adopted as written. **BJ.5 is counted**: Theorem 5 as printed is the
  twenty-third false printed statement. The verified certificate is the degenerate one, which is
  the ledger's practice for degenerate failures (Hoehn–Oversteegen Theorem 1′); the
  non-degenerate construction stays in prose until it is formalized (§7, optional). BJ.4 is not
  counted. The counts are now 23 false printed statements and 17 defective proofs.

## 1. The plan for Part G, and what this batch does

Batch 198 proved the classification from three named inputs: `BJThm10` (Bing–Jones Theorem 10),
`HOCircleLike` (a decomposable homogeneous plane continuum is circle-like) and `BJPlaneExample`
(Bing–Jones §7). This batch removes `HOCircleLike` (Part A, §§2–5) and starts on `BJThm10` from the
bottom (Part B, §6).

**Part A: Domokos–Prajs Theorem 6.1, with Bing's 1951 argument in place of shape theory.** The
first proof I have found of the step `HOCircleLike` stands for is Domokos–Prajs's (p. 14,
200 dpi):

> "The next theorem gives a characterization of the circles of pseudo-arcs. Compared to the
> characterization in [4], we do not use *circular chainability*. We include the proof because we
> did not find in the literature a proper reference to this theorem.
>
> **Theorem 6.1.** *A continuum X is a circle of pseudo-arcs if and only if X admits an open atomic
> map f : X → S onto a simple closed curve S such that all point-inverses, f⁻¹(y), are
> pseudo-arcs.*
>
> *In particular, the circle of pseudo-arcs is topologically unique.*"

Their [4] is Bing–Jones 1959. Their definitions (p. 13): "A subcontinuum K ⊂ X is terminal in X,
if for any continuum L ⊂ X with K ∩ L ≠ ∅ we have either K ⊂ L or L ⊂ K. A map f : X → Y between
continua X and Y is called atomic if all point-inverses f⁻¹(y) for y ∈ Y are terminal
subcontinua of X." Their proof of "if" (p. 14):

> "Let X be a continuum with an open atomic map f : X → S¹ onto the unit circle in the plane.
> Using the atriodicity of S¹ and of the pseudo-arc, and the atomicity of f one can easily show
> that X is atriodic.
>
> Define A = {(x, y) ∈ S¹ : y ≥ 0} and B = {(x, y) ∈ S¹ : y ≤ 0}. Then f⁻¹(A) and f⁻¹(B) are
> atriodic folders of chainable continua in the sense of [7]. Therefore, they are chainable by
> Proposition 6 of [7]. Using Theorem 10 of [4], X = f⁻¹(A) ∪ f⁻¹(B) can be mapped
> homeomorphically onto the circle of pseudo-arcs of [4]."

[7] is Hagopian–Marsh–Prajs, *Folders of continua*, Topology Proc. 55 (2020); its Proposition 6
(p. 16, checked on a 300-dpi rendering; the source is not sent, since the route does not use it:
"A folder of chainable continua is chainable if and only if it is atriodic.") reaches hereditary
unicoherence through Čech cohomology, dimension theory and shape theory and then applies Fugate
1969. **We do not need it.** For an atomic map onto an arc with snake-like hereditarily
indecomposable fibres, the chainability of the preimage follows from Bing's proof of 1951
Theorem 11 as the library already has it (§3). Domokos–Prajs's "Theorem 10 of [4]" is our
`BJThm10`, and the gluing is batch 198's (`exists_homeomorph_glue`).

The decomposable homogeneous plane continua of the classification that are not simple closed curves
have such a map: the quotient map of Jones's decomposition (batch 198,
`circle_or_circPAMap_of_decomposable` without its circle-likeness hypothesis), which is atomic by
`jones55_c`. Once this batch is done:
* the classification with Domokos–Prajs's third class (`ho16_classification_atomic`) depends on
  `BJThm10` alone;
* the classification with Bing–Jones's third class, and its plane form, depend on `BJThm10` and
  `BJPlaneExample` (`ho16_classification₂`, `ho16_classification_plane₂`), because an atomic map
  gives circle-likeness only through a homeomorphism with a circle of pseudo-arcs that is already
  known to be circle-like.

**Part B: Bing–Jones Theorems 7 and 9.** Theorem 10's proof (pp. 181–189) uses Theorems 5, 6, 8
(through its corollary) and 9; Theorem 8 uses Theorems 4 and 7. Theorems 2–6 are done. Theorems 7
and 9 are statements about single pseudo-arcs (two of them in Theorem 9), not about arcs of
pseudo-arcs, and rest on Bing 1948 Theorems 6, 11, 12 and 13, all in the library. Theorem 8 and
Theorem 10 come in later batches; I have a candidate repair of Theorem 8's last step (BJ.7) and will
commission it with the corollary.

## 2. Atomic maps (skeleton §2)

* `IsAtomicMap f`: Domokos–Prajs's terminality clause for every fibre. Their definition also
  makes the fibres continua (and so `f` surjective); here that is a separate hypothesis wherever it
  is used. With empty fibres allowed, the clause is vacuous at points outside the range.
* `IsAtomicCircPAMap f`: batch 198's `IsCircPAMap` with `atomic` in place of `circ`.
* `subset_fibre_or_saturated` (the saturation lemma). If `L` lies in no fibre, then for each
  `y ∈ f(L)` the continuum `L` meets `f⁻¹(y)` without lying in it, so `f⁻¹(y) ⊆ L`.
* Tests: `isAtomicMap_id`; `not_isAtomicMap_snd` (for `[0, 1]²` and the second coordinate,
  `L = {0} × [0, 1]` meets the fibre `[0, 1] × {t}`, is not in it and does not contain it). The
  product of a pseudo-arc and `[0, 1]` is the standard example of an open map with pseudo-arc
  fibres that is not atomic; the square has the same feature and is easier.

## 3. Atomic arcs are snake-like (skeleton §3)

`X` compact metric, `f : X → [0, 1]` continuous, every fibre snake-like and hereditarily
indecomposable, `f` atomic. Every subcontinuum of `X` lies in a fibre or is `f⁻¹(I)` for a closed
interval `I` (saturation lemma; `f(L)` is compact and connected).

* `condB_preimage_Icc`. Let `a ≤ b`, `μ ∈ f⁻¹(a)` (the case `f(μ) = b` is symmetric), and `H`, `K`
  subcontinua of `f⁻¹[a, b]` through `μ`. If both lie in `f⁻¹(a)`: `H ∪ K` is a subcontinuum of a
  hereditarily indecomposable continuum, so it equals `H` or `K`. If `H ⊆ f⁻¹(a)` and `K` does not:
  `f⁻¹(a) ⊆ K` by atomicity, so `H ⊆ K`. If neither: `H = f⁻¹[a, c]`, `K = f⁻¹[a, c′]`.
* `isHereditarilyUnicoherent_of_atomic`. Let `K = H ∪ L` be a non-degenerate subcontinuum, `H`, `L`
  subcontinua. Since `K` is connected, `H ∩ L ≠ ∅`.
  * If `K` lies in a fibre: the fibre is snake-like, so hereditarily unicoherent
    (`isHereditarilyUnicoherent_of_isSnakeLike`).
  * Otherwise, if `H` lies in a fibre `F` and `L` does not, `L` meets `F`, so `F ⊆ L` and
    `H ∩ L = H`.
  * If neither does, `H ∩ L = f⁻¹(I ∩ J)` with `I ∩ J` a non-empty closed interval, connected
    because `f` is closed with connected fibres (`isPreconnected_preimage_of_monotone'`).
  * `H` and `L` cannot both lie in fibres, since `K` does not.
* `isSnakeLike_of_atomic'` (**the main item of Part A**). Bing's proof of 1951 Theorem 11, as in
  `theorem11_1951` (`HPC/Plane/Theorem11B.lean`), with the fibres in place of Bing's layers.
  `univ` is a continuum: compact, and connected as the preimage of `[0, 1]` under a closed map
  with connected fibres (`isPreconnected_preimage_of_monotone'`). Suppose `X` is not
  `ε`-coverable.
  1. `exists_minimal_notCoverable` gives a subcontinuum `S′` that is not `ε`-coverable, all of
     whose proper subcontinua are.
  2. `S′` lies in no fibre: a fibre is snake-like, so it and its subsets are `ε`-coverable.
  3. So `S′ = f⁻¹[a, b]` with `a < b`. Put `c = (a + b)/2`, `A = f⁻¹[a, c]`, `C = f⁻¹[c, b]`,
     and pick `μ ∈ f⁻¹(c)`. Then `A`, `C` are proper subcontinua of `S′`, `A ∪ C = S′` and
     `A ∩ C = f⁻¹(c)`.
  4. `CondB A μ` and `CondB C μ` (`condB_preimage_Icc`). As in the `chain` step of
     `theorem11_1951`: minimality gives an `ε`-chain covering `A`; `fugate_lemma1` with
     `IsTerminalSub A {μ}` (`isTerminalSub_singleton_iff`) refines it to one whose last link
     contains `μ`; likewise for `C`.
  5. Claim 1 of `epsCoverable_of_halves`: a subcontinuum `Q ⊆ C` that meets `f⁻¹(c)` and is not
     inside it contains `f⁻¹(c)`, by atomicity.
  6. Hereditary unicoherence of `S′` from `isHereditarilyUnicoherent_of_atomic`.
  7. `epsCoverable_of_halves` makes `S′` `ε`-coverable: a contradiction.

  No subtype is needed: `A`, `C`, `S′` are sets in `X`. Openness of `f` is not used.
* `isSnakeLike_of_atomic`: pseudo-arcs are snake-like and hereditarily indecomposable.

This replaces Hagopian–Marsh–Prajs Proposition 6 and Fugate 1969 Theorem 2 in the case at hand.
In Fugate's terms the continuum `K` of his Case II is a point here, because every point of a middle
fibre satisfies condition B in each half.

## 4. Atomic circle maps (skeleton §4)

* `isAtomicMap_halfMap`: a continuum in `halfSet f s` is a continuum in `X` (`isContinuum_image_val`
  or the like); the fibres of `halfMap f hs` are the traces of fibres of `f` (`halfMap_eq_iff`).
* `isContArcPA_halfMap_of_atomic`: the proof of `isContArcPA_halfMap` uses only `cont`,
  `isOpenMap`, `surj` and `fib`.
* `isSnakeLike_halfSet_of_atomic`: §3 applied to `halfMap f hs` on the compact space
  `halfSet f s`.
* `dp22_theorem61`, `homeomorph_of_atomic`, `isHomogeneous_of_atomic`: batch 198's
  `exists_half_homeomorph`, `exists_homeomorph_glue` and `isHomogeneous_of_isCircPAMap` use
  `IsCircPAMap.circ` only through `isSnakeLike_halfSet` and for compactness
  (`IsCircPAMap.compactSpace`). Generalize them to maps whose halves are snake-like (for instance a
  structure with `cont`, `isOpenMap`, `surj`, `fib` and snake-like halves, on a compact space), and
  instantiate both ways: by `isSnakeLike_halfSet` for `IsCircPAMap`, by §3 for `IsAtomicCircPAMap`.
  Put the generalized versions in new files; do not edit `Halves.lean`, `Glue.lean` or `Homog.lean`.
  The end homeomorphisms exist because any two pseudo-arcs are homeomorphic (as used in
  `homeomorph_of_isCircleOfPA`). For homogeneity, rotating an atomic map keeps it atomic (its fibres
  are the same sets).
* `isCircleLike_circle`: for `n ≥ 4`, the open arcs `{exp(iθ) : θ ∈ (2πk/n − δ, 2π(k+1)/n + δ)}`
  with `δ < π/n` form an `ε`-circular chain when `2π/n + 2δ < ε` (cyclic distance `≥ 2` gives
  disjoint arcs).
* `isCircleLike_univ_of_homeomorph`: `Y` is compact (`IsCircleLike univ` contains
  `IsContinuum univ`), so `e.symm` is uniformly continuous; choose `δ` with
  `dist (e x) (e x′) < δ → dist x x′ < ε / 2`, take a `δ`-circular chain of `Y`, and pull its links
  back by `e`. (`CompactSpace X` may then be unused.)
* `isCircleOfPA_of_atomic`: `dp22_theorem61` and `isCircleLike_univ_of_homeomorph`; the map is the
  given one.
* `isAtriodic_of_atomic` (**optional**): Domokos–Prajs's "one can easily show". My reading of the
  argument, with Domokos–Prajs's triods (three continua whose pairwise intersections are one
  subcontinuum `K`, proper in each); a triod in the library's sense gives one of these (each
  `N ∪ Aᵢ` is a continuum):
  * if `K` lies in no fibre, all three are saturated, and their images are three arcs of `S¹`
    (or `S¹`), each properly containing the arc `f(K)`, pairwise meeting exactly in `f(K)`;
    impossible in `S¹`;
  * if `K` lies in a fibre `F`, the three cannot all lie in `F` (a pseudo-arc is hereditarily
    indecomposable, so meeting subcontinua are nested); if one of them, `T₁`, is saturated
    (`F ⊆ T₁`) and another, `T₂`, lies in `F`, then `T₁ ∩ T₂ = T₂ = K`, against properness; so all
    three are saturated, contain `F`, and `K = F`: three non-degenerate arcs of `S¹` pairwise
    meeting exactly in one point, impossible.

## 5. The decomposable case and the classification (skeleton §5)

* `circle_or_atomic_of_decomposable`: the proof of batch 198's `circle_or_circPAMap_of_decomposable`
  without `hCL`; atomicity from `jones55_c` (each fibre of `q` is an `Lset`, by `hfib` there).
* `hoCircleLike`: in the circle case, `isCircleLike_circle` and `isCircleLike_univ_of_homeomorph`;
  in the atomic case, `isCircleOfPA_of_atomic` with `Y = C₃` from `BJPlaneExample`.
* `ho16_classification_atomic`: forward as `ho16_classification` with
  `circle_or_atomic_of_decomposable`; backward by `isHomogeneous_of_atomic`.
* `ho16_classification₂`, `ho16_classification_plane₂`: batch 198's theorems with
  `hoCircleLike h10 hEx` for `hCL`.

Dependency map wanted in the report: which theorems of Parts F–G use which named inputs, after this
batch.

## 6. Bing–Jones Theorems 7 and 9 (skeleton §6)

**Chains.** Bing–Jones (pp. 172–173, 200 dpi): "A *chain* is a finite collection D of open sets d₁,
d₂, ⋯, d_n such that d_i intersects d_j if i, j are adjacent integers and otherwise ρ(d_i, d_j) is
positive." And: "We say that D *properly covers* X if each link of D contains a point of X. Also, D
*irreducibly covers* X of each link of D contains a point of X that is not covered by any other link
of D." ("of each link" is printed for "if each link"; record it.) `IsBJChain` is the
positive-distance condition; `Chain` + `IsBJChain` is Bing–Jones's chain. The library's `IsTaut`
(`Fugate66.lean`) is the same condition, but it carries `[CompactSpace S]`; prove
`IsBJChain D ↔ IsTaut D` in a compact space if you need the library's lemmas.

* `exists_bjChain_shrink`. My proof: compact `Kᵢ ⊆ dᵢ` with `⋃ Kᵢ ⊇ K`; enlarge each by `C i` and
  a point of `dᵢ ∩ K`; take `D′ᵢ` the `ρ`-neighbourhood of `Kᵢ`, with `ρ` less than each
  `infDist (Kᵢ) (dᵢ)ᶜ` and less than a third of each `dist(Kᵢ, Kⱼ)` for nonadjacent `i`, `j`
  (disjoint compact sets). Adjacent links still meet: otherwise the links up to `i` and those after
  `i` would split the connected `K`. No compactness of `X` is needed. (`infDist` to the empty set
  is `0`: treat `dᵢ = univ` separately, or use `posFn` from `Transfer.lean`.)

**Theorem 7** (pp. 176–177, 400 dpi):

> "THEOREM 7. *Suppose D = d₁, d₂, ⋯, d_n is a chain properly covering a pseudo-arc P and H is a
> chain map of a chain X = x₁, x₂, ⋯, x_m onto D. Then there is a chain E = e₁, e₂, ⋯, e_m properly
> covering P such that e_i ⊂ d_j if H(x_i) = d_j.*
>
> *In fact, if A, B are closed sets in P·d₁, P·d_n respectively and H(x_r) = d₁, H(x_s) = d_n, the
> chain E may be selected so that A ⊂ e_r, B ⊂ e_s.*"

**The second sentence is false as printed for `n ≤ 2`.** For `n = 1`: `D` one link, `m = 3`, `H`
constant, `A = B = {p}`, `r = 1`, `s = 3`; then `p ∈ e₁ ∩ e₃`, and `e₁`, `e₃` are not adjacent.
For `n = 2` the same with `p ∈ P ∩ d₁ ∩ d₂` and `H = (d₁, d₁, d₂)`. (With `n ≤ 2` it can fail
even when `A ∩ B = ∅`: `n = 1`, `A = P`, `B = ∅`, `m = 3`, `r = 1`; then `e₃` meets `P ⊆ e₁`.)
For `n ≥ 3`, `d₁ ∩ d_n = ∅`, so `A ∩ B = ∅`. Certificate wanted:
`bj_theorem7_ends_printed_false` (the `n = 1` case). This is a degenerate case of a printed
statement; I would count it, as the ledger counts degenerate failures (Hoehn–Oversteegen
Theorem 1′). Say whether you agree. Bing–Jones's own use (Theorem 8, p. 178) takes `A`, `B` inside
the closures of two open sets `U_A`, `U_B` chosen by the prover.

**Reading of "closed sets in P·d₁".** The skeleton reads it as `A ⊆ P·d₁` with `A` closed in the
space, as in Bing–Jones's use (`Ū_A·p_a`). Read as "closed in the subspace P·d₁", the sentence
fails for every `n ≥ 3` as well: `H = (d₁, d₂, d₁, d₂, d₃)`, `r = 1`, `A = P·d₁`, `B = ∅`; then
`e₃ ⊆ d₁` meets `P` only inside `P·d₁ ⊆ e₁`, while `e₁ ∩ e₃ = ∅`. Record both readings.

**Compactness.** The library's pseudo-arc lemmas need a compact ambient space: `theorem6Pos_of_ne`,
`consolidation_link_inter_M_nonempty`, `PA51.eventually_crookedIn`, `PA51.exists_crooked_next`,
`PA51.exists_preDesc`, `composant_ne_of_indecomposable`, `Description.exists_homeomorph`. §6 of the
skeleton has only `[MetricSpace X]` (the certificate lives in the plane). Work in the compact
subspace `P` (the traces of the links of a chain on `P` form a chain, `P` being connected) and lift
the chains back to open sets of `X`, as `PA51.lift_description` does.

`bj_theorem7_ends` (`n ≥ 3`) and `bj_theorem7`. Route (p. 177, 400 dpi):
1. Shrink `D` to a chain in Bing–Jones's sense keeping `A`, `B` inside the end links
   (`exists_bjChain_shrink` with `C 0 = A`, `C (n − 1) = B`; `A`, `B` are compact).
2. *The special case*: "The proof would be slightly easier if A ⊂ d₁ − d̄₂, B ⊂ d_n − d̄_{n−1},
   r = 1, s = m, x_r is the only element of X that H takes into d₁, and x_s is the only element of
   X that H takes into d_n." Bing–Jones: "Let p₁, p₂ be points of different components of P in
   d₁ − d₂, d_n − d_{n−1} respectively and D₁, D₂, ⋯ be a sequence of chains from p₁ to p₂ such that
   each D_i covers P, D_i is of mesh less than 1/i, D_{i+1} is crooked in D_i, and D = D₁. Then it
   follows from Theorem 6 of [3] that there is a chain E = e₁, e₂, ⋯, e_m from p₁ to p₂ such that E
   covers P, e_i ⊂ d_j if H(x_i) = d_j, and for some integer r, each link of E is the sum of links
   of D_r." ("components" for "composants": BJ.6.) [3] is Bing 1948.
   * The special case needs `P·(d₁ − d̄₂)` and `P·(d_n − d̄_{n−1})` non-empty (arrange it in the
     reduction). Each composant of `P` is dense in `P` (a proper subcontinuum of an indecomposable
     continuum has empty interior; Baire), so `p₁`, `p₂` can be chosen in these open sets and in
     different composants. The library proves density for `Jones.composant` (`composant_dense'`
     in `H75Composants.lean`, `composant_dense` in `Hagopian75.lean`), a different definition from
     the `composant` of `Statements79.lean` used by descriptions; prove it for the latter or
     bridge the two.
   * A description of `P` from `p₁` to `p₂` whose level 0 is `D` (links made bounded): take any
     description `Δ` of `P` from `p₁` to `p₂` (`exists_description_of_chainable_HI`, or
     `PA51.exists_description_univ` in the space `P` with `PA51.lift_description`); for large `k`
     the level `D_k` refines `D`, with closures of links inside links of `D`, and is crooked in
     `D` (`PA51.eventually_crookedIn`); put `D` in front of `D_k, D_{k+1}, ⋯`. Bing–Jones assume
     such a sequence starting at `D` without comment; record it.
   * Bing 1948 Theorem 6 (`theorem6Pos_of_ne`) for the pattern `H` gives `E`. Its links meet `P`
     (`consolidation_link_inter_M_nonempty`).
   * Unargued and immediate: `A ⊆ e₁`, since a point of `A` lies in no link of `D` but `d₁`, and
     only `e₁` lies in `d₁`.
3. *The reduction*: `D′ = U₀, U₁, U₂, d₃, ⋯, d_{n−2}, U_{n−1}, U_n, U_{n+1}`,
   `X′ = y′, y_r, y_{r−1}, ⋯, y₂, x₁, x₂, ⋯, x_m, z_{m−1}, ⋯, z_s, z′`, `H′`, `E′`, and
   `e_i = e′_i + f_i + g_i` (`f′` added to `e_r`, `g′` to `e_s`), as printed on p. 177. As printed
   `D′` needs `n ≥ 4`. For `n = 3` the printed conditions cannot all hold: a link `V` serving as
   both `U₂` and `U_{n−1}` must contain `P·(d₂ − d₁) ∪ P·(d₂ − d₃) = P·d₂`, and then it meets `U₄`,
   which is not adjacent to it (`U₄` is open and meets `P`; if `P·(d₃ − d₂) = ∅` then
   `U₄ ∩ P ⊆ P·d₂`, and otherwise `U₄ ⊇ P·(d₃ − d₂)`, a non-empty closed subset of the connected `P`
   other than `P`, which meets the closure of `P·d₂`). For `n = 3` build five links differently, for
   instance `U₀`, `U₄` thin neighbourhoods of `cl(P·(d₁ − d₂)) ∪ A` and `cl(P·(d₃ − d₂)) ∪ B`
   (compact subsets of `d₁ − d₂` and `d₃ − d₂` once `D` is in Bing–Jones's sense),
   `V = d₂ − (Ū₀ ∪ Ū₄)`, and `U₁ ⊆ d₁·d₂`, `U₃ ⊆ d₂·d₃` covering the rest of `P` with
   `A ∩ Ū₁ = ∅ = B ∩ Ū₃`. Check that `E` is a chain: `f_i` and `e′_j` are adjacent in `E′` only for
   `(i, j) = (2, 1)`, and `g_k`, `e′_j` only for `(k, j) = (m − 1, m)`, so the sums are a chain
   whether or not `r < s`. Record whatever else you need.
4. The chain `E` obtained is a library chain (a consolidation of a level of a description, then
   sums); make it a chain in Bing–Jones's sense with `exists_bjChain_shrink` (`C r = A`,
   `C s = B`).
5. The first sentence: for `n ≥ 3` it is `bj_theorem7_ends` with `A = B = ∅`. For `n = 1`,
   consolidate a fine chain of `P` into `m` consecutive blocks. For `n = 2`, run step 3 with a
   chain `D′` of four links: `P·(d₁ − d̄₂)` can be empty (for instance when `d₁ ⊆ d₂`), so first
   remove from `d₂` a small closed ball about a point `p ∈ P·d₁` inside `d₁`, and from `d₁` one
   about a point `q ≠ p` of `P·d₂` inside `d₂`; then `U₀ ⊆ d₁` about `p`, `U₃ ⊆ d₂` about `q`, and
   `U₁ ⊆ d₁`, `U₂ ⊆ d₂` covering the rest, `H′` sending `d₁`-elements to `U₁` and `d₂`-elements to
   `U₂`, `y′ ↦ U₀`, `z′ ↦ U₃`. Or any argument you prefer.

**Theorem 9** (p. 179, 400 dpi):

> "THEOREM 9. *Suppose D, E are chains properly covering pseudo-arcs P, Q and H is a chain map of D
> onto E such that each link of E is the image of a link of D which contains a point of P not on
> the closure of any other link of D. Then there is a homeomorphism h of P onto Q such that for
> each link d_i of D, h(P·d_i) ⊂ H(d_i).*"

The skeleton keeps Bing–Jones's chains (`IsBJChain` for `D` and `E`). I expect the statement to
fail without it, though I have not built an instance: if
`x ∈ P ∩ d_k ∩ cl(P·d_{k−1}) ∩ cl(P·d_{k+1})` (possible when nonadjacent links are only disjoint)
and `H` sends `d_{k±1}` to `e_{H(k)±1}` with `ē_{H(k)−1} ∩ ē_{H(k)+1} = ∅`, continuity puts `h(x)`
in both closures. Do not drop the hypothesis without checking this.

Route, pp. 179–181 (Bing–Jones: "We use two simplifications in this proof so as to make the
remaining part of the proof essentially like the proof of Theorem 12 of [3]"):
1. *First simplification*: `d″_i` is the sum of the links of `D` that `H` sends to `e_i`. `D″` is
   a chain: links of `D` sent to nonadjacent links of `E` are themselves nonadjacent, because `H`
   is a chain map. Each end link of `D″` has a point of `P` off the closures of the others (from
   the hypothesis), and `h(P·d″_i) ⊂ e_i` suffices. Choose `p₁ ∈ P·(d₁ − d̄₂)` and
   `p₂ ∈ P·(d_n − d̄_{n−1})` in different composants.
2. *Second simplification*: the chains `D′`, `E′` of `4n − 3` links (p. 180, Figure 1), with
   `ε`, `δ`, `F`, `G` as printed, and the reduction "if h is any homeomorphism of P onto Q such
   that h(P·d′_i) ⊂ ē′_{i−1} + ē′_i + ē′_{i+1}, then h is the required homeomorphism". Known
   slips (BJ.8): "links of G" for "links of F" (forming `e′_{4n−6}`, `e′_{4n−5}`, `e′_{4n−4}`); `e`
   for `d` in "d₂′ is the sum of the other links of G in e₁−e₂" and the next two clauses; the last
   display ends "⊂ē_i" where `h(P·d_i) ⊂ e_i` is claimed. The closures must be removed, for
   instance by choosing `F` with closures of links inside links of `E`. Repair as needed and record
   it.
3. *Completion* (pp. 180–181): Bing 1948 Theorem 13 gives crooked sequences `F_i` from `p₁` to
   `p₂` and `G_i` from `q₁` to `q₂`; alternate Bing 1948 Theorem 6 to build `D_i`, `E_i` with
   matching chain maps `H_i`; `h(p)` is the intersection of the closures of `e(p, i)`. Known slips
   (BJ.9): "refines E_i" for `E₁`, "H₂" for `H₁`, and "d¹_k" for `e¹_k`. "That h is a homeomorphism
   of P onto Q follows from an argument similar to that contained at the end of the proof of
   Theorem 10 of this paper or in Theorem 11 of [3]": unargued. The library's
   `Description.exists_homeomorph` (`HPC/PseudoArc/Uniqueness.lean`, the `Rung` construction) is
   Bing 1948 Theorem 12 with this argument; generalize its base step to start from `D′`, `E′` and
   the chain map, rather than redoing the limit argument.

Unnumbered claim (p. 179): "The rather awkward condition … is necessary because it may be that
D = d₁, d₂, ⋯, d_n and E = e₁, e₂, ⋯, e_n have the same number of links, H(d_i) = e_i,
P ⊂ d̄₂ + d̄₃ + ⋯ + d̄_{n−1}, and Q ⊄ ē₂ + ē₃ + ⋯ + ē_{n−1}." Read existentially, this is true;
the configuration as written does not by itself prevent `h`.
* *An `h` can exist in that configuration.* From a three-link chain `C` in Bing–Jones's sense
  properly covering a plane pseudo-arc `P` with `P ∩ (c₁ − c̄₂) ≠ ∅`, put `d₁ = c₁`,
  `d₂ = c₂ ∪ ((c₁ ∪ c₃) − P)`, `d₃ = c₃`, `E = C`, `Q = P`. Then `P ⊂ d̄₂` (`P` has empty interior
  in the plane), `Q ⊄ ē₂`, and `h = id` satisfies `h(P·d_i) ⊂ e_i`.
* *An instance where none exists.* Take `a ≠ b` in `P`, `n = 3`, `d₁ = B(a, ρ)`, `d₃ = B(b, ρ)`,
  `d₂ = U − {a, b}` for an open `U ⊇ P` and small `ρ`, and `E` with `Q ∩ (e₁ − ē₂) ≠ ∅`. A point
  of `Q ∩ (e₁ − ē₂)` lies in `e₁` only, so `h⁻¹` sends it into `d₁ − (d₂ ∪ d₃) = {a}`; the set
  `Q ∩ (e₁ − ē₂)` has more than one point, so `h` is not injective.
Record it; a certificate is not asked for.

## 7. Optional

* **BJ.5, the general certificate** (carried over from commission 198 §6): from any instance of
  Theorem 5's printed hypotheses with `n ≥ 3` links, produce one in which the printed conclusion
  fails with no fibre inside `U` (merge the last two links: `chainMergeLast` enlarges the last
  link by an open set, so apply it to the chain without its last link, with that link as the open
  set, and append the last link again).
* `isAtriodic_of_atomic` (§4).
* `IsBJChain D ↔ IsTaut D` in a compact space (§6).

## 8. Ledger

New section "Domokos–Prajs 2022 and Bing–Jones §§4–5 (batch 199)". Check each item on page images.

1. **Domokos–Prajs p. 14, "one can easily show that X is atriodic"**: unargued; supplied if you do
   `isAtriodic_of_atomic`, otherwise recorded with the reading of §4. Not used by our route.
2. **Domokos–Prajs p. 14, "It is known that the circle of pseudo-arcs from [4] admits an open,
   atomic map onto a circle with pseudo-arcs as fibers"**: the "only if" direction rests on this.
   The support offered is Example 6.1 (p. 13): Bing and Jones "constructed the *circle of
   pseudo-arcs*, denoted here by Ψ, which is a homogenous, decomposable and nowhere
   locally-connected continuum in the plane admitting a continuous decomposition into terminal
   pseudo-arcs". Bing–Jones do not prove that the elements are terminal. Not used by our route.
   Not counted.
3. **Domokos–Prajs p. 14, the halves "are chainable by Proposition 6 of [7]"**: true in our case;
   replaced by §3 (no shape theory). Not a defect.
4. **Domokos–Prajs p. 14**: their circle of pseudo-arcs is "homeomorphic to the original example
   Ψ of Bing and Jones"; Bing–Jones define it by circle-likeness and a continuous decomposition.
   Record the two definitions and which our theorems use.
5. **Bing–Jones p. 172 (400)**: "D *irreducibly covers* X of each link": `of` for `if`.
6. **Theorem 7, second sentence**: false as printed for `n ≤ 2` (§6; certificate), and for every
   `n` if "closed sets in P·d₁" means closed in the subspace. Proposed for the count (degenerate
   case, under the reading the skeleton adopts).
7. **Theorem 7, proof**: BJ.6 (components/composants); the special case's unargued `A ⊆ e₁`; the
   crooked sequence starting at `D`, assumed without comment; the non-emptiness of
   `P·(d₁ − d₂)`, `P·(d_n − d_{n−1})`, assumed; `D′` as printed works for `n ≥ 4` and its
   conditions cannot all hold for `n = 3` (§6); the case `n ≤ 2` not treated; the check that `E`
   is a chain; and whatever else you find.
8. **Theorem 9**: BJ.8 and BJ.9 revisited with the repairs you used; the "awkward condition"
   remark (§6: true read existentially).

Count nothing yourself; say which items, if any, you would count.

## 9. Non-vacuity

* `isSnakeLike_of_atomic'`, `isHereditarilyUnicoherent_of_atomic`, `condB_preimage_Icc`: `[0, 1]`
  with the identity (`nonvac_isSnakeLike_of_atomic'`).
* `isSnakeLike_of_atomic`, all of §4 and `circle_or_atomic_of_decomposable`'s second alternative:
  `nonvac_atomic` (under `BJThm10` and `BJPlaneExample`: `C₃` is homogeneous and decomposable and
  not a simple closed curve, so `circle_or_atomic_of_decomposable` gives an atomic map). No
  unconditional witness is known to me; say if you find one.
* `circle_or_atomic_of_decomposable`, `ho16_classification_atomic`: the plane circle
  (`nonvac_plane_circle`).
* `bj_theorem7`, `bj_theorem7_ends`: `nonvac_bj_chains` with `H = id`.
* `bj_theorem9`: `P = Q` a plane pseudo-arc, `D = E` one link (the plane), `H = id`; and, if you
  can, a chain of at least three links each containing a point of `P` outside the closures of the
  other links, with `H = id`.
* New definitions on degenerate inputs: `IsAtomicMap` (identity, constant maps, `Prod.snd`),
  `IsBJChain` (one link; three links of `ℝ`, `(0, 2)`, `(1, 3)`, `(2, 4)`, where the outer two are
  disjoint at distance `0`, so `IsBJChain` fails).

## 10. Order

Part A first: §2, §3 (`isSnakeLike_of_atomic'` is the main item), §4, §5. Then §6:
`exists_bjChain_shrink`, the certificate, `bj_theorem7_ends`, `bj_theorem7`, then `bj_theorem9`
(stretch). §8 alongside.

## 11. Deliverables

1. **The items of §§2–7.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch199.txt`,
     together with the three batch-198 `@[simp]` lemmas of §0 (add them to `Axioms.lean`).
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section of §8.
3. **Notes:** append to `doc/notes/bj59.md` what this batch proved and the state of the named
   inputs.
4. **Publish the changes, as in batch 198**: `doc/batches/batch199-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies and the new source) and
   `doc/batches/batch199-MANIFEST.txt`.
5. **The report.** Its first line names the commission it read. It covers the items in order, the
   non-vacuity notes, the ledger entries, the axioms used by each theorem, and the dependency map
   of §5.
