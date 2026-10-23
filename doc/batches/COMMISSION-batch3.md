# Commission: batch 3 — Bing's description of M, and Theorem 12 conditional on Theorem 6

**Go!** Runs on top of the batch-2 delivery (run 0d9c2796-c970-49e6-8ea3-3a30df3febea). Two
new files, `HPC/PseudoArc/Description.lean` and `HPC/PseudoArc/Uniqueness.lean`; root
`HPC.lean` updated. Nothing in `HPC/Chains/` or `HPC/Covers/` touched. Every `sorry` is a
work item; delivery contains none.

## Purpose

Bing 1948 Theorem 12: two continua described by nested crooked chains from `P₁` to `Q₁` and
from `P₂` to `Q₂` are homeomorphic by a map carrying `P₁ ↦ P₂`, `Q₁ ↦ Q₂`. Its proof is the
alternating construction (§3 below), which feeds Theorem 11 (batch 2). The one ingredient
not yet formalized is Theorem 6, pattern following. It is taken as a **named hypothesis**,
`Description.PatternFollowing`, in the main theorem. The result is therefore conditional, and
the project's status table will say so until Theorem 6 is discharged in a later batch. No
axiom is introduced; the hypothesis is an ordinary premise.

## Protocol

As batches 1 and 2: no `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`;
`#print axioms` on every theorem showing only `propext`, `Classical.choice`, `Quot.sound`;
census first; report rather than repair; first make the skeleton compile with proofs still
`sorry`, changing only syntax and mathlib names, recording every change. If a statement
cannot be made to compile without changing its meaning, stop on it and report.

Batch-1 results available and expected to be used: `Chain.link_nonempty`,
`Chain.IsCrookedIn'.isCrookedIn`, `Chain.isCrookedIn'_of_refines` (T5),
`Chain.isCrookedIn'_of_isConsolidationOf` (T4), `Chain.exists_consolidation_isFrom` (T6),
`Chain.diam_le_length_mul` (T7), `Chain.refineIdx`, `Chain.refineIdx_subset`,
`Chain.Refines.trans`, `Chain.pattern_lipschitz`, and the discrete intermediate-value lemmas in
`HPC/Chains/Aux.lean`. Batch-2 result: `MatchingCovers.exists_homeomorph`.

## 1. The description

`Description X P Q` packages Bing's "Description of M" (p. 730) as Theorem 12 uses it: a
sequence of chains `D i` from `P` to `Q`, each `D (i+1)` crooked in `D i` in the **1948 sense**
(`IsCrookedIn'`, since that is what Theorems 3–6 are proved for), with the closure of each
link of `D (i+1)` inside a link of `D i`, and a mesh bound `ε i → 0` with all links bounded.
`M := ⋂ i, (D i).union`. The ambient space is assumed compact (`CompactSpace X`) where
needed; Bing takes it so throughout.

## 2. Properties of a description — proofs

**P_mem_M, Q_mem_M.** `P ∈ (D i).link 0 ⊆ (D i).union` for every `i`, by `isFrom`. Likewise
`Q` in the last link.

**two_le_n_of_lt.** `isFrom` gives `0 < n i`. If `n i = 1`, the first and last links coincide,
so `P` and `Q` both lie in link `0`, whence `dist P Q ≤ diam (link 0) ≤ ε i < dist P Q`.
Contradiction. (Note: `IsFrom` alone does not exclude `n i = 1`; the mesh hypothesis is
what does. In Theorem 12 the levels used are chosen with mesh below `dist P Q`.)

**refines_of_le.** `closure_subset` gives `(D (i+1)).Refines (D i)`, since a set lies in its
closure. Induct on `j − i` using `Chain.Refines.trans`.

**closure_union_subset.** For `i < j`: each link of `D j` has closure inside a link of
`D (j−1)` by `closure_subset`, and that link lies inside a link of `D i` by `refines_of_le`.
The closure of a finite union is the union of the closures, so `closure (D j).union ⊆
(D i).union`.

**isClosed_M, isCompact_M.** `⋂ i, (D i).union = ⋂ i, closure (D (i+1)).union`: the left side
is contained in the right because each `(D (i+1)).union` lies in its closure and the
intersection over `i+1` is the intersection over `i ≥ 1`, which contains the intersection over
all `i`; the right side is contained in the left because `closure (D (i+1)).union ⊆ (D i).union`
by `closure_union_subset`. An intersection of closed sets is closed; closed in a compact space
is compact.

**crooked_of_lt.** For `j = i + 1` it is the field `crooked i`. For `j > i + 1`: `D j` refines
`D (i+1)` by `refines_of_le`, and `D (i+1)` is crooked in `D i`; batch-1 T5
(`Chain.isCrookedIn'_of_refines`) gives `D j` crooked in `D i`.

**exists_closure_link_subset.** For each `t : Fin (n (i+1))`, `closure_subset` gives an index
`χ t` with `closure ((D (i+1)).link t) ⊆ (D i).link (χ t)`; in particular
`(D (i+1)).link t ⊆ (D i).link (χ t)`, so `χ` is an assignment to which batch-1
`Chain.pattern_lipschitz` applies: `|χ (t+1) − χ t| ≤ 1`. `P ∈ (D (i+1)).link 0 ⊆
(D i).link (χ 0)`, and `P` lies in no link of `D i` other than link `0`, so `χ 0 = 0`. Likewise
`χ (last) = last`. By the discrete intermediate value theorem in `HPC/Chains/Aux.lean`,
`χ` attains every value between `0` and `n i − 1`; take `t` with `χ t = s`.

**link_inter_M_nonempty.** By `exists_closure_link_subset`, iterated, choose links
`ℓ_k` of `D (i+k)` for `k ≥ 0` with `ℓ_0 = (D i).link s` and `closure ℓ_{k+1} ⊆ ℓ_k`. The
sets `closure ℓ_k` are nonempty (links are nonempty), closed, hence compact in `X`, and
nested: `closure ℓ_{k+1} ⊆ ℓ_k ⊆ closure ℓ_k`. So they have a common point `z`. For every
`k`, `z ∈ closure ℓ_{k+1} ⊆ ℓ_k ⊆ (D (i+k)).union`; and for `j < i`, `(D i).union ⊆
(D j).union` by `closure_union_subset`. Hence `z ∈ M`, and `z ∈ ℓ_0`.

**M_subset_union.** Immediate from the definition of `M`.

**n_tendsto_atTop.** `P, Q ∈ M` give `diam M ≥ dist P Q > 0`. `M ⊆ (D i).union`, each link
of `D i` is bounded with diameter `≤ ε i < 2 ε i`; batch-1 T7 (`Chain.diam_le_length_mul`,
with `ε := 2 ε i`) gives `diam M ≤ n i · 2 ε i`, so `n i ≥ diam M / (2 ε i)`, which tends to
infinity as `ε i → 0`.

**exists_level_refining.** `Y` is a consolidation of `D j`, so `(D j).Refines Y`. For `k ≥ j`,
`(D k).Refines (D j)` by `refines_of_le`, hence `(D k).Refines Y` by `Chain.Refines.trans`.
Choose `k ≥ j` with `ε k ≤ δ` by `ε_tendsto`.

**IsPattern, PatternFollowing.** Definitions; nothing to prove.

## 3. Theorem 12 — proof

**Chain.pattern_matching.** Suppose the `j`-th link of `Y₁` meets the `k`-th link of `Z₁`. By
`h₁`, the `j`-th link of `Y₁` lies in the `x j`-th link of `Z₁`, so the `x j`-th and `k`-th
links of `Z₁` meet, hence `|x j − k| ≤ 1` by `adjacent`. On the other side, the `j`-th link of
`Y₂` lies in the `x j`-th link of `Z₂` (by `h₂`) and is nonempty (`link_nonempty`); pick `p` in
it. The `x j`-th and `k`-th links of `Z₂` meet (again `|x j − k| ≤ 1` and `adjacent`); pick `q`
in their intersection. Both `p` and `q` lie in the `x j`-th link of `Z₂`, so
`dist p q ≤ diam (Z₂.link (x j)) < ε`.

**Chain.diam_le_of_followsPattern, Chain.diam_le_of_refines.** A subset of a bounded set has
no larger diameter (`Metric.diam_mono`).

**Chain.exists_pattern_of_refines.** Let `x := Y.refineIdx Z` (batch 1), so
`Y.link t ⊆ Z.link (x t)`. As in `exists_closure_link_subset`, `x 0 = 0` and `x (N−1) = m−1` because
`P` and `Q` lie only in the first and last links of `Z`; and `x` moves by at most one by
`Chain.pattern_lipschitz`. So `x` is a pattern and `Y.FollowsPattern x Z` by construction.

**Description.exists_homeomorph.** We build data `C : MatchingCovers Δ₁.M Δ₂.M ε'` for a
suitable summable `ε'` and apply batch-2 `MatchingCovers.exists_homeomorph`. The
construction is by recursion on the level, alternating sides. Throughout, a level of the
construction is a pair of chains `X₁,ᵢ : Chain X₁ (N i)`, `X₂,ᵢ : Chain X₂ (N i)` with the same
number of links, each a chain from its `P` to its `Q`, each a consolidation of some level of
its description (possibly a trivial consolidation, i.e. a level itself), and — for `i ≥ 1` —
each following in the level above the *same* pattern as its partner.

*Level 0.* `X₁,₀ := Δ₁.D a` for some `a` with `Δ₁.ε a ≤ 1/2` and `Δ₁.ε a < dist P₁ Q₁` (possible by `ε_tendsto`). Let `N 0 := Δ₁.n a`. By
`n_tendsto_atTop` choose `b` with `Δ₂.n b ≥ N 0`; by batch-1 T6 (`exists_consolidation_isFrom`,
which needs `2 ≤ N 0`, supplied by `two_le_n_of_lt` since `a` is chosen with `Δ₁.ε a < dist P₁ Q₁`), let `X₂,₀` be a consolidation of `Δ₂.D b` from
`P₂` to `Q₂` with `N 0` links.

*Level 2i+1 from level 2i.* (Refine on side 2, match on side 1.) `X₂,₂ᵢ` is a consolidation of
some level `Δ₂.D b`. By `exists_level_refining`, choose `c ≥ b` with `Δ₂.D c` refining `X₂,₂ᵢ`
and `Δ₂.ε c ≤ 1/2^{i+1}`; set `X₂,₂ᵢ₊₁ := Δ₂.D c`, `N (2i+1) := Δ₂.n c`. By
`exists_pattern_of_refines` there is a pattern `x` with `X₂,₂ᵢ₊₁.FollowsPattern x X₂,₂ᵢ`. Now
`X₁,₂ᵢ` is a consolidation of some level `Δ₁.D a'`, hence — *this is where the hypothesis
`h₁` must be applied relative to a consolidation rather than a level.* `PatternFollowing` as
defined applies to patterns in a level `D i`, not in a consolidation of a level. Two ways
through: (a) note that `X₁,₂ᵢ` is either a level (at `i = 0`, and at every level of the form
"refine" on side 1) or follows a pattern in a level, and compose patterns; (b) strengthen the
hypothesis. **Take (a)**, made precise as follows. On side 1 the chains at even indices
`X₁,₂ᵢ` for `i ≥ 1` are *levels* `Δ₁.D a` (they are produced by the refinement step on side 1
at index `2i`, see below), and `X₁,₀` is a level. So at every even index the side-1 chain is a
level, and `h₁` applies directly: there are `j > a'` and `X₁,₂ᵢ₊₁ : Chain X₁ (N (2i+1))` from
`P₁` to `Q₁`, a consolidation of `Δ₁.D j`, with `X₁,₂ᵢ₊₁.FollowsPattern x X₁,₂ᵢ`.

*Level 2i+2 from level 2i+1.* (Refine on side 1, match on side 2.) Symmetric: `X₁,₂ᵢ₊₁` is a
consolidation of `Δ₁.D j`; choose `d ≥ j` with `Δ₁.D d` refining it and `Δ₁.ε d ≤ 1/2^{i+1}`;
set `X₁,₂ᵢ₊₂ := Δ₁.D d`. Get a pattern `x'` of `X₁,₂ᵢ₊₂` in `X₁,₂ᵢ₊₁`. On side 2, `X₂,₂ᵢ₊₁` is
a level, so `h₂` gives `X₂,₂ᵢ₊₂` from `P₂` to `Q₂`, a consolidation of a deeper level,
following `x'` in `X₂,₂ᵢ₊₁`.

So: side 1 has levels at even indices and pattern-followers at odd; side 2 has a
consolidation at index 0, levels at odd indices, pattern-followers at even indices `≥ 2`. At
every index `i ≥ 1`, both `X₁,ᵢ` and `X₂,ᵢ` follow the same pattern in the chains at index
`i − 1`.

*Mesh.* Define `μ₁ i`, `μ₂ i` as follows. Side 1: `μ₁ (2i) = 1/2^{i+1}` (levels, by choice of
`a`, `d`); `μ₁ (2i+1) = μ₁ (2i)` by `diam_le_of_followsPattern`. Side 2: `μ₂ 0 = diam` of
`X₂` — take `μ₂ 0 := Metric.diam (Set.univ : Set X₂) + 1`, finite since `X₂` is compact
hence bounded, and every link is contained in `univ`; `μ₂ (2i+1) = 1/2^{i+1}`;
`μ₂ (2i+2) = μ₂ (2i+1)` by `diam_le_of_followsPattern`. Set `ε' i := 2 · max (μ₁ i) (μ₂ i)`.
Then `ε' i > 0`, `ε'` is summable (it is eventually bounded by `4/2^{⌊i/2⌋}`, a geometric
tail; the first term is finite), and every link at index `i` on either side has diameter
`≤ ε' i / 2 < ε' i`.

*The four conditions of `MatchingCovers`.* Openness: consolidations and levels have open
links. (1) cover: each `X_n,ᵢ` is a consolidation of a level `Δ_n.D k`, so its union equals
`(Δ_n.D k).union ⊇ Δ_n.M` by `M_subset_union`. (2) meets: each link of `X_n,ᵢ` is a union of
links of `Δ_n.D k` (nonempty union, since a consolidation's link is nonempty), each of which
meets `M` by `link_inter_M_nonempty`. (3) bounded with `diam ≤ ε' i`: links of a consolidation are
finite unions of bounded sets, hence bounded; the diameter bound is the mesh computation
above. (4): for `i ≥ 1`, both sides follow the same pattern at index `i` in index `i − 1`;
apply `Chain.pattern_matching` with `ε := ε' (i−1)`, whose hypothesis `diam < ε'(i−1)` holds
since `diam ≤ ε'(i−1)/2`. For the direction from side 2 to side 1, apply the same lemma with
the roles exchanged. (The index shift: `MatchingCovers` indexes conditions by the *lower*
level `i` and the *upper* level `i+1`; our construction's index `i+1` follows a pattern in
index `i`, matching this.)

*Applying Theorem 11.* `Δ₁.M`, `Δ₂.M` are compact (`isCompact_M`). Batch-2
`MatchingCovers.exists_homeomorph` gives `T` with the tracking clause.

*Tracking `P` and `Q`.* At every index and on both sides, `P_n` lies in link `0` (each `X_n,ᵢ`
is a chain from `P_n` to `Q_n`). So the constant index sequence `a i := 0` tracks `P₁` on side
1 and `P₂` on side 2, and the tracking clause gives `T P₁ = P₂`. Likewise the sequence
`a i := N i − 1` tracks `Q₁` and `Q₂`, giving `T Q₁ = Q₂`.

## 4. Deliverables

1. Census.
2. Both files compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step, and any statement that did not go through, with
   the point of failure.

## 5. Not in this batch

Theorem 6 (the `PatternFollowing` hypothesis), Theorems 3, 4, 5; the reduction in Bing 1951;
the D8/D9 gap.
