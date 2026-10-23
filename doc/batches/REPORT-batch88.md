Commission read: `COMMISSION-batch88.md` (batch 88 — Bing, *Concerning hereditarily indecomposable continua*, Pacific J. Math. 1 (1951), 43–51, Theorem 1 and its consequences).

# Report, batch 88

The skeleton is saved as `HPC/Plane/PseudoArc51.lean`, and `import HPC.Plane.PseudoArc51` is the
last line of `HPC.lean`. The proofs are in four new files:

| file | contents |
| --- | --- |
| `HPC/Plane/PA51Crook.lean` | crookedness eventually (§3 item 2) |
| `HPC/Plane/PA51Pre.lean` | Bing's sequence of mutually crooked chains; the description from `p` to `q`, in the compact space `M` |
| `HPC/Plane/PA51Lift.lean` | passing from `M ⊆ X` to the space `M` and back (restricting chains, lifting descriptions) |
| `HPC/Plane/PA51Counter.lean` | a description whose continuum is compact but not connected |

`lake build HPC` succeeds. None of the new files contains `sorry`. `Axioms88.lean` prints the
axioms of every statement (output in `axioms-batch88.txt`): all use only `propext`,
`Classical.choice`, `Quot.sound`. The only `sorry`s in the repository are the old ones
(`covering_step`, `theorem3_end`, `theorem10_1951`, …); nothing in this batch depends on them.

## 0. Counterexamples

Two of the skeleton's nine statements are **false as stated**. Both assume `IsCompact Δ.M` in
place of a compact ambient space.

* **`theorem12_of`** (Theorem 12 with `hc₁ : IsCompact Δ₁.M`, `hc₂ : IsCompact Δ₂.M`). Refuted
  by `theorem12_of_false`.
* **`isPseudoArc_of_description`** (with `hc : IsCompact Δ.M`). Refuted by
  `isPseudoArc_of_description_false`.

**The counterexample** (`PA51.exists_description_compact_disconnected`). Start from the plane
description `Δ₀` from `P` to `Q` (batch 84) and its continuum `M₀`. Let `Y` be the plane with
every point of `M₀` except `P` and `Q` removed.

1. `M₀` is hereditarily indecomposable (`theorem10`). So it contains no square, since a square
   is the union of two proper closed sub-rectangles. Hence `M₀` has empty interior
   (`PA51.interior_eq_empty_of_HI`).
2. So every nonempty open set of the plane meets `Y`. The links of `Δ₀` cut down to `Y` therefore
   keep the chain condition and all the other conditions of a description
   (`PA51.denseDescription`).
3. The continuum of the cut description is `M₀ ∩ Y = {P, Q}`. This set is compact, `P ≠ Q`, and
   it is not connected.

So it is neither a pseudo-arc nor homeomorphic to `M₀`. The point is that `Description` allows a
non-complete ambient space, and compactness of the described set does not make up for that.

Both statements are kept, commented out, in `PseudoArc51.lean`, each next to its refutation.
Their reshaped replacements are proved:

* `theorem12_of`: the links of each description lie in a compact set `K₁` or `K₂`, as
  `Transfer.lean` assumes for Theorem 13. Proof: restrict both descriptions to `K₁` and `K₂`,
  apply `theorem12`, and transport along the identity homeomorphisms (`restrictHomeo`).
* `isPseudoArc_of_description`: the links lie in a compact set `K`. Also
  `isPseudoArc_of_description'` for a compact ambient space.

Neither change affects Theorem 1. Its proof never uses `theorem12_of`: it applies `theorem12` in
the compact spaces `M` and `M'` themselves (§3 item 7).

No other statement was reshaped. `theorem1_HIC`, `theorem1_HIC'`, `isPseudoArc_iff_endPoints`,
`exists_description_of_chainable_HI`, `homogeneous_of_isPseudoArc`, `isPseudoArc_of_subcontinuum`
and `oppositeEndPoints_of_composants` are proved exactly as in the skeleton.

## 1. Targets

1. **`exists_description_of_chainable_HI`**: proved as stated, in an arbitrary metric space `X`.
   - `PA51.exists_description_sub` builds the description in the compact space `M`, with
     continuum all of `M`. This is Bing's proof (§3 items 2–5).
   - `PA51.lift_description` lifts it to `X`, with continuum `M` (§3 item 5, closures).
2. **`theorem1_HIC`**: proved as stated. Take the descriptions of the spaces `M` and `M'` from
   item 1, apply `theorem12` (both spaces are compact), and compose with `M ≃ₜ univ = Δ₁.M`. The
   commission asked for `theorem12_of`; it is not needed here, and as stated it is false (§0).
3. **`theorem1_HIC'`**: proved as stated. The pair from different composants comes from
   `exists_not_mem_composant`, which applies `composant_ne_of_indecomposable` in the compact space
   `M` (where `M` is `univ` and indecomposable) and carries the point back to `X`.
4. **`IsPseudoArc`**: kept verbatim. Its consequences:
   - **`homogeneous_of_isPseudoArc`**: from `theorem1_HIC` with `M = M'`, taking `r ∉ composant p`
     and `s ∉ composant q`.
   - **`isPseudoArc_of_subcontinuum`**: immediate. A chain covering `M` covers `K`, so no trimming
     is needed (the commission suggested trimming). Hereditary indecomposability passes to `K` by
     definition.
   - **`homeomorphic_subcontinuum`** (added): `Nonempty (K ≃ₜ M)`.
5. **`isPseudoArc_of_description`**: false as stated (§0). Reshaped and proved: links in a
   compact set, or a compact ambient space.
   - Chainable: level `i` is an `ε`-chain once `Δ.ε i < ε`.
   - Hereditarily indecomposable: `theorem10`.
   - A continuum: `isContinuum_M_of`.
   - Nondegenerate: `P ≠ Q`.

   Added: **`isPseudoArc_plane`** (the continuum of `exists_description_plane` is a pseudo-arc)
   and **`pseudoArc_unique`** (every pseudo-arc, in any metric space, is homeomorphic to it).
6. **`isPseudoArc_iff_endPoints`**: proved as stated.
   - Necessity: for `p`, take `q ∉ composant M p`. Then **`oppositeEndPoints_of_composants`**
     (also proved) gives `ε`-chains from `p` to `q` covering `M`: the levels of the description
     of item 1. The first link is then the only one containing `p` (condition C).
   - Sufficiency: batch 85's `exists_not_endPoint_of_not_HI`.
7. **`theorem1_snake`** (added): *Snake-like continua* Theorem 1, in terms of `IsSnakeLike` and
   `IsHereditarilyIndecomposable`. It is `theorem1_HIC'`.

## 2. §3 item 2 in detail: crookedness eventually, and "neither contains the other"

**Statement proved** (`PA51.eventually_crookedIn`). Let `X` be a compact metric space in which
every subcontinuum is indecomposable, and let `C` be a chain covering `X`. Let `E m` be chains
refining `C`, with links bounded of diameter `≤ ε m → 0`. Then eventually `E m` is crooked in `C`
**in the 1948 (meet) sense**, `IsCrookedIn'`. This is the reading the description needs, so no
conversion is required. It is stronger than the containment reading `IsCrookedIn`, since a link
contained in `C_h` meets `C_h`. Refinement and small mesh are the only hypotheses on the `E m`: they
need not cover `X`, and their links need not have closures in links of `C`.

**Choice of witnesses** (`PA51.failData_of_fail_lt`). Take a failure at `(h, k, i, j)` with
`k − h > 2` and `i < j`; the case `i > j` reduces to it by reversing the fine chain. Here `E_i`
meets `C_h`, `E_j` meets `C_k`, and no `r, s` strictly between with `r` nearer `i` have
`E_r ⊆ C_{k−1}` and `E_s ⊆ C_{h+1}`.

* Let `r` be the **first** index after `i` with `E_r ⊆ C_{k−1}`. It exists and is at most `j`, by
  the discrete intermediate value theorem on a refinement map.
* Let `W_m` be the span of `E_i, …, E_{r−1}`. **No link of `W_m` lies in `C_{k−1}`**: for `E_i`
  because `C_h ∩ C_{k−1} = ∅`, for the others because `r` is the first such index.
* Let `V_m` be the span of `E_{r+1}, …, E_j`, or `E_j` alone when `r = j`. **No link of `V_m` lies
  in `C_{h+1}`**: for `E_j` because `C_k ∩ C_{h+1} = ∅`, for the others by the failure (with the
  pair `r` and `s`).
* The link `E_r` itself belongs to neither span. Bing lets `W` and `V` share `c_{m,r}`. That link
  can lie in both `C_{k−1}` and `C_{h+1}` when `k = h + 3`, and that breaks the argument below.
  `W_m` and `V_m` are instead joined through points of `E_{r−1} ∩ E_r` and `E_r ∩ E_{r+1}`, which
  are at most `ε m` apart.

**Limits** (`PA51.limit_false`). By pigeonhole, one pair `(h, k)` fails infinitely often. Pass to
a subsequence along which the junction points converge to some `R`. Let `W` and `V` be the limit
superiors of `W_m ∪ {R}` and `V_m ∪ {R}`. These are still finely chained, so `W` and `V` are
continua (`T13.isPreconnected_limSup`) and they meet at `R`.

* **`W` misses the open link `C_{k−1}`.** At a point of `W` inside `C_{k−1}`, a ball about it lies
  in `C_{k−1}`, and small links of `W_m` near the point would then lie in `C_{k−1}`. Likewise
  **`V` misses `C_{h+1}`** (`PA51.limSup_miss`). This is the fact that repairs the text: it is a
  statement about open links. Bing's "`W` misses `c̄_{1,k}`" is about closures, and it fails at
  boundary points.
* A cluster point `Y` of points of `W_m ∩ C_h` lies in `W`, in a link `C_{l₁}` with
  `l₁ ≤ h + 1`. A cluster point `Z` of points of `V_m ∩ C_k` lies in `V`, in a link `C_{l₂}` with
  `l₂ ≥ k − 1`.
* **`W` meets `C_{h+1}`.** Otherwise `W`, being connected and covered by the links other than
  `h + 1`, lies in the links below `h + 1` (it contains `Y`). `V`, which misses `C_{h+1}` and
  contains `Z`, lies in the links above `h + 1`. Then `R ∈ W ∩ V` is impossible.
* **`V` meets `C_{k−1}`**, by the symmetric argument.

So `V ⊄ W`, because `V` meets `C_{k−1}` and `W` misses it, and `W ⊄ V` in the same way. Hence
`W ∪ V` is a decomposable subcontinuum, which is a contradiction. The contradiction is purely
about open links, so Bing's case `l = k − 1`, which the commission flagged, never comes up.

**The subsequence** (§3 item 3, `PA51.exists_preDesc`).
- Choose a Lebesgue number `λ` of the current chain.
- Take chains of mesh `< min(λ/2, 1/(m+1))` covering `M`; the closures of their links lie in links
  of the current chain.
- `eventually_crookedIn` gives one that is crooked in the current chain and has mesh `≤ 1/(i+2)`.

Iterating this gives `PA51.PreDesc`: chains covering `M`, each crooked in the previous one, with
closures nested and mesh `≤ 1/(i+1)`. Unlike a description, the levels are not chains from one
fixed point to another.

## 3. §3 item 5 in detail: the description from `p` to `q`, and closures

The body of the proof runs in the **compact space `M`** (`M = univ`).

**Reduction to the space `M`** (`PA51.exists_description_sub`). Four facts pass from `M ⊆ X` to
the space `M`:
- *chains*: `PA51.subChain`. A chain covering `M` with every link meeting `M`, as given by
  batch 85's `exists_cover_meeting`, restricts to a chain of the space `M`. Consecutive links
  still meet inside `M` because `M` is connected (`PA51.inter_inter_nonempty`).
- *hereditary indecomposability*: `PA51.hI_sub`.
- *chainability*: `PA51.snake_sub`.
- *composants*: `PA51.not_mem_composant_sub`.

**Steps** (`PA51.PreDesc.exists_step`): the argument of `Description.exists_step`, with the
pre-description in place of a description.
* **Reaching both ends** (`PreDesc.exists_subchain_meets_ends`) is batch 81's argument. The limit
  superior of the spans from `p` to `q` is a subcontinuum containing `p` and `q` and missing an
  end link, so it is proper. This contradicts `q ∉ composant p`. Nothing needs `M ⊆` anything,
  since `M` is the whole space.
* **Theorem 4**: `Chain.exists_blockChain` gives a block consolidation of a deeper level that is a
  chain from `p` to `q`. Each block lies in three consecutive links of level `m`, where Bing has
  two; only the mesh constant changes.
* **At least five links** at deep levels (`PreDesc.eventually_five_le`). This follows from
  `p ≠ q` and the mesh bound, through `Chain.diam_le_length_mul`.
* **Closures.** Take a Lebesgue number `δ` of level `L` as a cover of the compact space `M`.
  Each block lies in a closed ball of radius `3/(m+1) < δ` about one of its points, and hence in a
  Lebesgue ball contained in a link of level `L`. The ball carries the closure, as the commission
  suggested. The difficulty the commission raised, that the closure of a deep level's union need
  not be compact, disappears because the ambient space is now `M` itself.

**Assembly** (`PA51.PreDesc.exists_description`): as `exists_description_from'`. The new levels
are crooked by Theorems 1–2 applied to the pre-description's crookedness
(`isCrookedIn'_of_isConsolidationOf`, `isCrookedIn'_of_refines`). The described set is all of `M`,
because every consolidation has the same union as the level it consolidates.

**Lifting back to `X`** (`PA51.lift_description`). A relatively open `U ⊆ M` extends to the open
set `ext M r U` of points of the `r`-neighbourhood of `M` that are nearer to `U` than to `M \ U`
(extended distances).
* It meets `M` in `U`.
* It is monotone in `U` and `r`.
* It sends disjoint sets to disjoint sets, so the chain condition and the meet-sense crookedness
  hypotheses transfer both ways.
* It lies in the `r`-neighbourhood of `U`, which gives the mesh bound `diam U + 2r`.
* **Closures** (`PA51.exists_closure_ext_subset`): if `closure U ⊆ V`, then
  `closure (ext M r U) ⊆ ext M ρ V` whenever `r < min(δ, ρ)`, where `δ` separates the compact set
  `closure U` from the closed set `M \ V`.

The radii `r_i` are chosen decreasing to `0`, each small enough for all links of its level. The
lifted continuum is `⋂_i` of the lifted unions. It contains `M`, and it lies in every
`r_i`-neighbourhood of `M`, hence in `M`, since `M` is closed.

**`Δ.M = M`** (§3 item 6) is therefore exact, both in the space `M` and after lifting.

## 4. §3 item 7 in detail: Theorem 12 without a compact ambient space

As stated in the skeleton, with `IsCompact Δ.M`, this is **false** (§0). The idea of restricting to
`M` itself, links intersected with `M`, fails for an arbitrary description. A link need not meet
`M`, and two adjacent links need not meet inside `M`. In the counterexample `M = {P, Q}`, and the
chain condition fails completely inside `M`.

Two correct forms are in the repository:
* **Links inside a compact set** (the reshaped `theorem12_of`). The restriction is to `K`, as in
  `Transfer.lean`.
* **Theorem 1 itself**. The descriptions are *built* in the compact spaces `M` and `M'`, where
  `theorem12` applies directly. This is how `theorem1_HIC` is proved.

## 5. Implicit hypotheses (§3 item 8)

Confirmed, with one addition:
* nondegeneracy of `M` is used, to get `p ≠ q` from the composant hypothesis and to get at least
  five links at deep levels;
* compactness of `M` is used, via the subspace `M`;
* no other hypothesis is needed. In particular the ambient space `X` is arbitrary for Theorem 1.

The addition concerns descriptions rather than Theorem 1. For a *description*, compactness of
`Δ.M` does not replace a compact ambient space (§0).
