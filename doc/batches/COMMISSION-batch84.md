# Commission: batch 84 — Bing 1951 (*Snake-like continua*), part one: Theorem 4, and the pseudo-arc in the plane

**Go!** Runs on top of the batch-83 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch84.md` — this text (also pasted into the prompt);
* `Snake51.lean` — a skeleton of four definitions and five statements, all `sorry`, all work
  items. Save it as `HPC/Plane/Snake51.lean` (new directory) and add `import HPC.Plane.Snake51` at
  the end of the root `HPC.lean`. Nothing else is to be replaced. Shapes of the auxiliary
  statements and of the definitions of rectangle chains may be adjusted with the change
  recorded; `theorem4`, `exists_description_plane` and `pseudoArc_exists` keep their conclusions.

The report names the commission read in its first line.

## 0. On batch 83, and why this batch is not Theorem 14

Audited: `exists_irreducible`, `irreducible_unique`, `theorem15_of_theorem14` proved as stated;
`exists_description_covering` reduced to the one-level `covering_step`, which is open; `theorem14`
open; standard axioms on everything proved; no counterexample. The finding stands as recorded:
Bing's "such sequences exist as a consequence of Theorem 9" (p. 741) is not a proof, and
`covering_step` is the precise statement his argument needs. Theorems 14 and 15 are **parked**
(their `sorry`s stay; `theorem3_end` stays parked too). Neither is on the path to the
classification. The 1951 paper is.

## 1. What this batch establishes

Bing 1948 Theorems 12 and 13, machine-checked in batches 80–81, say that a continuum admitting a
*description* is unique up to homeomorphism and is homogeneous — in any compact metric space.
What the repository does not yet have is that a description **exists in the plane**. The 1948
paper posits it ("Description of M", with a figure); the 1951 paper's Theorem 4 supplies the
planar construction in general: every snake-like continuum is homeomorphic to a plane continuum,
and the proof builds, in the plane, chains of open rectangles following prescribed patterns. That
construction is what this batch formalizes, and it is used twice:

* for Bing 1951 **Theorem 4** as stated (item 3 below), via Bing 1948 Theorem 11
  (`MatchingCovers.exists_homeomorph`, already in the repository); and
* for the **existence of a description in the plane** (item 4), by realizing Bing's crooked
  pattern `bingPattern` (batch 82: `bingF`, `bingF_crooked`, `crooked_of_tight`) level by level —
  and hence (item 5) for the sentence *the pseudo-arc is a homogeneous, hereditarily
  indecomposable, nondegenerate plane continuum*, with `theorem10`, `theorem13` closing it.

Item 5 is the milestone. Item 4 is the mathematical content; item 3 is Bing's theorem.

## 2. Bing's text (pp. 653–654), transcribed

**Definitions (§1).** A *chain* is a finite collection of open sets `d_1, …, d_j` such that `d_i`
intersects `d_j` if and only if `i = j − 1, j, or j + 1`. We do not impose the condition that the
`d_i`'s are connected. If the links of a chain are of diameter less than `ε`, the chain is called
an *`ε`-chain*. A compact continuum is called *snake-like* if for each positive number `ε` it can be
covered by an `ε`-chain. [The term was suggested by Choquet. An arc is snake-like; a triod is not;
a pseudo-arc is.]

Theorems 1–3 of the paper (any two nondegenerate snake-like hereditarily indecomposable continua
are homeomorphic; "most" compact continua in Euclidean or Hilbert space are snake-like; snake-
likeness is preserved by monotone maps) are **quoted from Bing's *Concerning hereditarily
indecomposable continua*, Pacific J. Math. 1 (1951), 43–51**, not proved here. They are not in
this batch.

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch84.md, 2. Bing's text (pp. 653–654); batch 204.]

[The paper's Theorem 5 — uncountably many disjoint plane copies — rests on Roberts [10] and is
not in this batch.]

## 3. Facts about the text, and what the skeleton does with them

### 3.1 The planar construction is the whole content

"It can be shown that in the plane there is a sequence of chains `D_1, D_2, …` …" is the only
step Bing does not carry out, and it is the one this batch is about. The skeleton isolates it as
one lemma about a single step, `exists_rect_chain_following`: *given a chain `D` of `m` open
rectangles with room (§3.2), a pattern `x : Fin n → Fin m` with unit steps and onto, and `ε > 0`,
there is a chain `D'` of `n` open rectangles with room, of mesh `< ε`, with the closure of `D'_t`
inside `D_{x t}`, and* tight: *`D'_t` meets `D_l` only for `l = x t'` with `t'` within one of `t`.*
Onto gives "each element of `D_i` contains the closure of an element of `D_{i+1}`". The tightness
clause is not in Bing; it costs nothing in the construction (keep each fine rectangle away from
the closures of the coarse rectangles other than `D_{x t}`, `D_{x(t±1)}`) and is exactly what
`crooked_of_tight` (batch 82) needs to turn a crooked *pattern* into a crooked *chain* (§3.4).

The picture: `D_{x t}` is a rectangle; the fine rectangles `D'_t` with the same `x t` are laid
along a path inside it, in the order of `t`; where `x` steps up, the path crosses through the
overlap rectangle `D_{x t} ∩ D_{x t + 1}`; where `x` turns (goes up then down), the path makes a
U-turn inside `D_{x t}`, using the room of §3.2. Rectangles need not be connected to their
neighbours by anything but overlap, and the metric on `ℝ × ℝ` in the skeleton is the sup metric
of the product, which changes no topology; if Euclidean distance is preferred, state the change.

### 3.2 Room

A chain of rectangles must leave room for the next level's U-turns and for the tightness clause.
The skeleton's `HasRoom D`: every link contains a point outside the closures of all other links.
For a chain of open rectangles this says the middle of each rectangle is free of its neighbours.
It is an invariant of the construction (the fine chain must have it too). If a different
invariant is more convenient (e.g. explicit overlap rectangles, or rectangles of the form
`Ioo a b ×ˢ Ioo c d` with the overlap of consecutive links a rectangle of positive size and
non-adjacent closures disjoint), replace it, recording the change.

### 3.3 Bing's "nine links"

"No subchain of `C_{i+1}` of less than nine links intersects two nonadjacent links of `C_i`" is
not used by the skeleton. With the pattern `x` defined by refinement (`Chain.refineIdx`), unit
steps are automatic (`Chain.pattern_lipschitz`), and the matching condition (4) of Theorem 11 in
the repository's form (`Chain.pattern_matching`, batch 3) holds for two chains following the same
pattern with `ε_i` any bound on the mesh. What the nine-link clause buys in Bing's argument is
not clear to the commission; possibly it is what lets *him* draw the rectangle chain (a U-turn
needs a few links). The report says whether the construction of §3.1 needs any such quantitative
clause; if it does, add it as a hypothesis of `exists_rect_chain_following`, and then it must be
arranged on the `C`-side in `theorem4` (by passing to a deeper level, as `eventually_thick` does).

### 3.4 The pseudo-arc in the plane (`exists_description_plane`, `pseudoArc_exists`)

Take `D^{(0)}` any chain of three open rectangles with room (or any `n_0 ≥ 3`), and for each `i`
let `D^{(i+1)}` be the rectangle chain of §3.1 following `bingPattern n_i` (`Fold.bingPattern`,
`Fold/Theorem7.lean`; its values are `bingF (n_i − 1)`, onto `[0, n_i − 1]`, unit steps
`bingF_lip`, `bingF 0 = 0`, top value at the last index `bingF_top`), with `n_{i+1} = z (n_i − 1)`
and mesh `< 1/2^{i+1}`. Then:

* `D^{(i+1)}` is crooked in `D^{(i)}`: `crooked_of_tight` from `bingF_crooked` and the tightness
  clause;
* closures nest: the clause of §3.1;
* end points: a description needs each level to be a chain *from `P` to `Q`* (`Chain.IsFrom`),
  with `P` in the first link only and `Q` in the last only, the same `P`, `Q` at every level.
  `bingF (n − 1) 0 = 0` and `bingF (n − 1) (last) = n − 1`, so first links nest in first links and
  last in last. Choose the first rectangle of each level inside the first rectangle of the
  previous level *and away from the closure of the previous level's second link* (room), and take
  `P` in the intersection of the nested closed first rectangles; then `P` lies in every first link
  and in no second link. Likewise `Q`. This is an extra clause on `exists_rect_chain_following`
  when `x 0 = 0` and `x last = m − 1`, or a separate lemma; the skeleton leaves the choice.
* `P ≠ Q`: the first and last links of `D^{(0)}` are disjoint (three links).

That gives `Δ : Description (ℝ × ℝ) P Q` with `P ≠ Q`. Then `pseudoArc_exists` is
`Δ.isContinuum_M`, nontriviality from `P ≠ Q`, `theorem10` for hereditary indecomposability, and
`theorem13` for homogeneity. Uniqueness among all described continua is `theorem12` and needs no
new statement.

### 3.5 Theorem 4 (`theorem4`)

The `C`-side. From `IsSnakeLike M` (every `ε` has an `ε`-chain covering `M`; the skeleton's
`ε`-chain has bounded links of diameter `< ε`) build `C_0, C_1, …` with, at every level: mesh
`< 1/2^{i+1}`; `C_i` covers `M` and no proper subchain of it does (cut any covering chain down to
a minimal covering subchain `C(a, b)`); `C_{i+1}` refines `C_i`. Two consequences of minimality,
both to be proved:

* **every link of `C_i` meets `M`** — if an interior link `c_j` misses `M`, then `M` lies in the
  union of the links before `j` and the union of the links after `j`, two disjoint open sets
  (links at index distance `≥ 2` are disjoint), each meeting `M` by minimality; that contradicts
  connectedness of `M`; an end link that misses `M` contradicts minimality directly;
* **the pattern is onto** — the pattern `x_i = refineIdx` of `C_{i+1}` in `C_i` has unit steps
  (`Chain.pattern_lipschitz`); if it missed the value `k`, it would stay on one side of `k`, so `M`
  (covered by `C_{i+1}`) would lie in the links of `C_i` before `k`, or in those after `k` — a
  proper subchain of `C_i` covering `M`.

Refinement is arranged as Bing does: a Lebesgue number `δ` of the cover of the compact `M` by the
links of `C_i`; a chain of mesh `< δ` all of whose links meet `M` has each link inside a ball of
radius `< δ` about a point of `M`, hence inside a link of `C_i`. (Cutting to a minimal subchain
keeps refinement and mesh.)

The `D`-side. `D_0` any rectangle chain with room and `n_0` links; `D_{i+1}` from §3.1 following
`x_i`, mesh `< 1/2^{i+1}`. `N := ⋂_i D_i^*`, compact (as in `Description.isClosed_M`: the closures
nest).

Theorem 11. `MatchingCovers` with `x¹_{i} = C_i`, `x²_i = D_i`, `ε_i = 1/2^i` (summable, positive),
`M₁ = M`, `M₂ = N`: (1) covers — `M ⊆ C_i^*` by choice, `N ⊆ D_i^*` by definition; (2) meets — every
link of `C_i` meets `M` by choice; every link of `D_i` meets `N` because it contains the closure
of a link of `D_{i+1}`, which contains the closure of a link of `D_{i+2}`, …, a nested sequence of
nonempty compact sets whose common point is in `N` (`Description.link_inter_M_nonempty` is the
same argument); (3) diameters `< ε_i`; (4) matching — `Chain.pattern_matching` in both directions,
since `C_{i+1}` and `D_{i+1}` follow the same `x_i` in `C_i` and `D_i`, and both coarse chains
have mesh `< ε_i`. Then `MatchingCovers.exists_homeomorph` gives `M ≃ₜ N`. `N` is connected
because `M` is; it is a plane continuum.

### 3.6 Implicit hypotheses

* Snake-like continua are *compact* by definition (Bing: "a compact continuum"); the skeleton's
  `IsSnakeLike` is `IsContinuum ∧ …` with `IsContinuum` already compact, in a metric space that
  need not be compact.
* Theorem 4 is stated for nonempty `M` (a continuum is nonempty by `IsConnected`).

## 4. Deliverables

1. `exists_rect_chain_following`, `theorem4`, `exists_description_plane`, `pseudoArc_exists`
   (and `HasRoom`, `IsSnakeLike`, the rectangle predicates), `sorry`-free, with `#print axioms` in
   `axioms-batch84.txt`; every reshaped statement recorded with its reason.
2. Report: first line names the commission read; counterexamples first; then the targets in
   order; then §3.1–3.6 claim by claim, in particular §3.3 (whether a quantitative clause is
   needed) and §3.5 (minimal covering subchains).
3. Not attempted: `covering_step`, `theorem14`, `theorem3_end` (parked).

## 5. Not in this batch

Bing 1951 §3 (tree-like continua, Theorems 6–7), §4 (hereditarily decomposable snake-like
continua, Theorems 8–11), §5 (end points, Theorems 12–16); Theorem 5 (needs Roberts). Theorems
1–3 are not proved in the paper.
