Commission read: COMMISSION-batch124.md (batch 124 — the only-clauses (pair form of Theorem 3); Fugate's Corollary 1 as stated; survey for discharging `PlaneFacts`).

# Report, batch 124

**Outcome.**

| item | verdict |
|---|---|
| Q1. `Theorem3Pair` | **proved** (`HPC.Fold.theorem3_pair`, `theorem3Pair_holds`), by Bing's induction with the basepoint replaced by the pair; four changes against `bing_main`, one of them exactly at `r = 5` |
| Q2. levels `a, a+1, a+2` | the case **can occur**, but the only-clause holds there for *every* admissible consolidation (`onlyIn_of_no_common`) |
| Q3. Theorem 3 as printed | **proved**, every clause (`HPC.Fold.theorem3_literal`, `Recon121.theorem3LiteralOr_holds`) |
| Q3. Theorem 4 as printed (`Theorem4LiteralND`) | **refuted** with three coarse links and `r < s` (`HPC.Fold.not_theorem4LiteralND`); with at least four coarse links **open** (`Theorem4LiteralGe4`; obstruction below; no failure in the census) |
| Q4. (U) / `fugate_cor1` | **open, with the obstruction stated**. (U) is shown *equivalent* to the sufficiency half of the corollary (`fugateU_iff_cor1Sufficiency`); `fugate_cor1` keeps its `sorry` |
| Q5–Q8 | survey below (no proofs) |

Build: `lake build HPC` succeeds. `axioms.txt` regenerated (482 lines); `sorryAx` occurs in **one
line**, `HPC.Plane.fugate_cor1` (unchanged since batch 123). Every other line shows
`[propext, Classical.choice, Quot.sound]` or a subset. Per-batch audit:
`doc/batches/audits/axioms-batch124.{lean,txt}` (every theorem of the five new files, plus
`fugate_cor1`); the previous `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch124.txt`.

New Lean files (all imported at the end of `HPC.lean`, no `sorry`):

* `HPC/Fold/Theorem3PairModel.lean`, `HPC/Fold/Theorem3PairInduction.lean`: the pair form in the
  model of batch 122;
* `HPC/Fold/Theorem3Pair.lean`: the move to chains, Q2, Theorem 3 as printed (the file the
  commission named for item 1);
* `HPC/Fold/Theorem4Only.lean`: the counterexample to `Theorem4LiteralND`, and the open `Prop`
  `Theorem4LiteralGe4`;
* `HPC/Plane/Fugate66Cor1.lean`: (U) as the open `Prop` `FugateU`, its equivalence with the
  corollary (the file the commission named for item 2).

`HPC/Plane/Fugate66.lean` is not edited (`fugate_cor1` is not closed).

---

## Q1. The pair form of Theorem 3 — proved

**Statement proved** (`HPC.Fold.theorem3_pair`, `HPC/Fold/Theorem3Pair.lean`). If `E` is crooked
(1948) in `D` and `E.link i`, `E.link i'` are equal or adjacent links lying in a common link of `D`,
there is a block consolidation with `E.link i` in the first block, `β i' = β i`, every block in two
adjacent links of `D`, and Bing's end clause ("or" reading). `theorem3Pair_holds : Theorem3Pair`
(the batch-123 `Prop`).

**Proof.** In the model of batch 122 (`ρ`, `σ` the least and greatest coarse levels of a fine link,
`T t j` "fine link `t` meets coarse link `j`"), Bing's conclusion is generalised from a basepoint `i`
to a *set* `Z` of fine links that must all go to time 0 (`BConclZ`); `pair_main` proves it for
`Z = {i, i'}` with `i, i'` equal or adjacent and in a common coarse link (`CommonC`), by strong
induction on the number `K` of coarse links, following `bing_main`. Bing's induction goes through
with four changes; nothing else resists:

1. **Base case `K ≤ 4`** (`zbase`). Bing groups the links in `e₁ + e₂` against the rest (by `ρ`).
   If the pair straddles the level `ρ = 1 | 2` (one link in `e₁ + e₂`, the other not), the grouping
   by `σ` is used instead: the links in `e₁` and not in `e₂` against the rest; the common coarse
   link of the pair makes one of the two groupings put both links in the same group.
2. **The end cases** ("`d_i ⊆ e₁ + e₂`", "`d_i ⊆ e_{m−1} + e_m`", `zlow`, `zhigh`) are taken only
   when *both* links of the pair lie there. Otherwise neither link meets `e₁` or `e_m`, and the
   general case applies, with either link of the pair as the anchor of `D(h, k)`.
3. **The general and cut constructions** (`genF`, `cutF` of batch 122) already send every link of
   the first block of the inductive `H` to time 0; only the bookkeeping changes (`genF_conclZ`,
   `cutF_specZ`, `cutF_conclZ`).
4. **The special case at `r = 5`** (`special_fiveZ`). This is exactly where the commission looked.
   Bing's explicit grouping (`special_five`) puts the links up to `d_k` lying in `e₁ + e₂` in one
   block. If the pair straddles that block boundary, the explicit grouping fails. The fix is a
   **second explicit grouping**, the mirror image of `special_five`, with the links "in `e_{m−1}`,
   not in `e_{m−2}`" free, plus a free choice for the links in `e₂ ∩ e₃`
   (`special_fiveZ_fwd` and its reverse-flip). One of the forward and the mirror grouping always
   applies. The reason: in the straddling configuration the link `d_r` (which is in `e₄`) comes
   before the link `d_{r'}` (which is in `e₂`), and these two cannot be adjacent.

   For `r ≥ 6` the pair lies in `D(1, h)`, in `D(h, k)` or in `D(k, n)`, taking *closed*
   intervals (the pair may contain `d_h` or `d_k`). Bing's three branches go through unchanged
   (`special_branch1Z`, `special_middleZ`, `special_caseZ`).

The move from the model to chains (`chain_of_bconclZ`) is batch 122's `chain_of_bconcl` with `Z` in
place of `{i}`.

**Census** (`doc/census/recon-batch124-pair.cpp`, mode `pair`; log
`doc/census/recon-batch124-pair.log`; not Lean-checked, and superseded by the proof). There were 0
failures for `K = 5`, `n ≤ 12`; `K = 6`, `n ≤ 12`; `K = 7`, `n ≤ 10`. In the special case alone
(`K = 5`, `n ≤ 14`) there were also 0 failures. Together that is about 1.8 · 10⁸ instances.

## Q2. Levels `a, a+1, a+2` — possible, harmless

The configuration is not excluded by crookedness. The commission's observation that
`E.link i ⊆ (D_a ∩ D_{a+1}) ∪ (D_{a+1} ∩ D_{a+2})` does not contradict 1948-crookedness, which
constrains meetings. Instead of excluding it, the only-clause is proved there for **every** block
consolidation whose blocks lie in two adjacent links of `D`:

`HPC.Fold.onlyIn_of_no_common` (`HPC/Fold/Theorem3Pair.lean`). Suppose `E.link i` shares a link of
`D` with neither neighbour. Then each of `E.link i` and its neighbours lies in exactly one link of
`D` (`single_in_two`, `subset_link_iff`), and the neighbours lie one level above or below. A block
lying in two adjacent links of `D` cannot contain one neighbour from above and one from below. So if
`E.link i` were inside another block, it would be covered by neighbours all in one link of `D`
(`link_subset_neighbours`), and that link would then contain `E.link i`, a contradiction.

The model census (mode `only`, `doc/census/recon-batch124-only.log`; not Lean-checked, and
superseded by Q3) found no failure of the only-clause at any covered interior basepoint (`K = 5`,
`n ≤ 11`).

## Q3. The statements as printed

**Theorem 3 — proved** (`HPC.Fold.theorem3_literal`; `Recon121.theorem3LiteralOr_holds :
Theorem3LiteralOr`). Two cases:

* `E.link i` shares a link of `D` with a neighbour `t₀`: use the pair form, then
  `onlyIn_of_neighbour`;
* otherwise: use `theorem3_bing`, then `onlyIn_of_no_common`.

OPEN item 2 is closed for Theorem 3.

**Theorem 4 with three coarse links — refuted** (`HPC.Fold.not_theorem4LiteralND`,
`HPC/Fold/Theorem4Only.lean`). This is a new failure, outside the degenerate case of batch 123.
The space is `ℕ`, which is discrete, so every set is open.

* Coarse links: `{0,1,5}`, `{1,2,4,5}`, `{2,3,4}`.
* Fine links: `{5}`, `{4,5}`, `{2,3,4}`, `{1,2}`, `{0,1}`.
* Basepoints: `r = 0`, `s = 1`, so `d₀ ⊆ d₁`.

The fine chain is crooked in the coarse one (`onlyFine_crooked`, by `decide`). `D(0, 1)` meets the
first coarse link (via `5`) and the last (via `4`). Suppose `F` has `d₁` in its last link and `d₀`
in only its first link. Since `d₀ ⊆ d₁`, the first and last links of `F` coincide, so `F` has a
single link: the union of all fine links, `{0,…,5}`. That set lies in no two adjacent coarse links.

The model census (mode `thm4`, `doc/census/recon-batch124-thm4.log`) finds failures with `K = 3` for
every `n ≥ 5` tried (4, 40, 252 and 1316 failing instances at `n = 5, 6, 7, 8`). It finds 0 failures
for `K = 4`, `n ≤ 9` and for `K = 5`, `n ≤ 11`.

**Theorem 4 with at least four coarse links — open** (`Theorem4LiteralGe4`, a `Prop` in
`Theorem4Only.lean`). Obstruction: `theorem4_two` builds `F` from two applications of the core
construction, one at each end (`two_core`). The only-clauses at `d_r` and `d_s` need the pair form
at **both ends at once**: the companion of `d_r` (a neighbour sharing a coarse link) in the first
block, and the companion of `d_s` in the last.

* `K ≥ 5`: a pair version of `two_core` looks routine. The companion sits at `hh + 1` or `kk − 1`
  of `two_core`'s notation, where the corresponding offset is 0.
* `K = 4`: a new grouping is needed (time 1 for the links in the `G`-block of `kk`, otherwise time
  0 when `ρ ≤ 1`).
* There is a genuine conflict when the two companions are the same link (`s = r + 2`, companion
  `r + 1`). This can only happen with `m ≤ 4`.

None of this is formalized.

**Ledger text (only-clauses)**, as entered in `LEDGER.md` §1:

> *Theorem 3 as printed (Bing 1948).* The statement as printed, every clause including the
> only-clause, is **proved** in batch 124: `HPC.Fold.theorem3_literal`,
> `HPC.Fold.Recon121.theorem3LiteralOr_holds`, through the pair form `HPC.Fold.theorem3_pair`.
>
> *Theorem 4 as printed (Bing 1948, p. 733), only-clauses, `m = 3`, `r < s`.* Refuted:
> `HPC.Fold.not_theorem4LiteralND`. In `ℕ`: coarse links `{0,1,5}`, `{1,2,4,5}`, `{2,3,4}`; fine
> links `{5}`, `{4,5}`, `{2,3,4}`, `{1,2}`, `{0,1}`; `r = 0`, `s = 1`. `d₁` in the last link of `F`
> with `d₀` only in the first forces a one-link `F`, which lies in no two adjacent links. The
> two-link form without the only-clauses holds (`theorem4_two`); with `m ≥ 4` the statement as
> printed is open (`Theorem4LiteralGe4`).

## Q4. Fugate's Corollary 1 and (U) — open, with the obstruction

**Lean** (`HPC/Plane/Fugate66Cor1.lean`, over a compact metric space as `fugate_cor1`):

* `FugateU S` (open `Prop`): a finite chain of snake-like continua, consecutive ones meeting, whose
  union is atriodic and unicoherent, has a hereditarily unicoherent union.
* `FugateCor1Sufficiency S` (open `Prop`): the sufficiency half of Corollary 1 as stated.
* `fugateU_iff_cor1Sufficiency : FugateU S ↔ FugateCor1Sufficiency S` (proved). (U) is *exactly*
  the missing step, no more and no less: `→` by `fugate_cor1'`, `←` because a snake-like continuum
  is hereditarily unicoherent. Refuting (U) would therefore refute Corollary 1 as stated, and
  proving it would prove the corollary.
* `fugate_cor1_of_fugateU` (proved): Corollary 1 as stated, under (U).

**Informal analysis** (not formalized). Suppose (U) fails for `A₀, …, A_k`, and let `p` be least
with `U_p = A₀ ∪ ⋯ ∪ A_p` not unicoherent. Then `p ≥ 1`. By induction with
`isHereditarilyUnicoherent_union`, `B₀ := U_{p−1}` is hereditarily unicoherent, and
`B₀ ∩ B₁` is disconnected, where `B₁ := A_p`. Since the whole union is unicoherent, `p < k`; put
`B₂ := A_{p+1} ∪ ⋯ ∪ A_k`, a continuum meeting `B₁`. Unicoherence of the whole union gives:

* `P₀ := B₀ ∩ (B₁ ∪ B₂)` is connected.
* `B₀` meets `B₂`: otherwise `P₀ = B₀ ∩ B₁` would be connected.
* Hence `P₁ := B₁ ∩ (B₀ ∪ B₂)` and `B₂ ∩ (B₀ ∪ B₁)` are connected.

Then `N := P₀ ∪ P₁` is a continuum with `P₀ ∩ P₁ = B₀ ∩ B₁` disconnected, so `N` is **not
unicoherent**, and `N ⊆ (B₀ ∩ B₁) ∪ B₂`.

* If `B₀ ∩ B₁` has empty interior in `N`, then `N ⊆ B₂` (`B₂` is closed). So when the tail `B₂` is
  hereditarily unicoherent, in particular when `p = k − 1` (then `B₂ = A_k` is snake-like), a
  counterexample must have `B₀ ∩ B₁` **thick in `N`**.
* In general this only pushes a non-unicoherent subcontinuum into the tail. The tail is atriodic
  but need not be unicoherent, so an induction on the number of pieces does not close. This is the
  obstruction.
* Miller's Theorem 1.5 (in the corrected form `miller_1_5_of_hu`) does not help: its hypothesis is
  hereditary unicoherence, which is the conclusion sought.
* With arcs, and more generally locally connected pieces, a counterexample is impossible. The union
  is then a one-dimensional Peano continuum, and a unicoherent one is a dendrite (classical,
  informal here). A counterexample would need non-locally-connected snake-like pieces whose
  intersections have interior in `N` in the sense above. I could not construct one, nor rule one
  out.

**Ledger text (Corollary 1)**, as entered in `LEDGER.md` §1 (Fugate 1966 table), *not refuted*:

> *Corollary 1 (Fugate 1966, p. 467), sufficiency, as stated.* Not refuted, open (`OPEN.md`
> item 1). Fugate gives no proof; the one-line induction through Theorem 1 that he presumably
> intends needs every partial union `A₀ ∪ ⋯ ∪ A_p` unicoherent, condition (U), which is exactly
> what is missing: `HPC.Plane.fugateU_iff_cor1Sufficiency`. True under hereditary unicoherence of
> the union (`fugate_cor1'`, `fugate_cor1_iff`) and under (U) (`fugate_cor1_of_fugateU`).

---

## Q5–Q8. Survey for discharging `PlaneFacts`

Units: one "batch" means a batch of this project's typical size, a few hundred to about 1500
lines of Lean (for example `Tree6Local.lean` with `Tree6Arcs.lean`, about 1500 lines, or the
lattice cycle of batch 110, about 950 lines). All estimates are rough.

### Q5 — `jct`

**Mathlib** (the pinned commit). A search of `.lake/packages/mathlib/Mathlib` for `Jordan curve`,
`JordanCurve`, `windingNumber`, `winding number` and `Janiszewski` finds nothing; the hits for
"Jordan" are Jordan–Hölder, Jordan decomposition, Jordan–Chevalley and Jordan algebras. What is
there:

* `Mathlib/Geometry/Polygon/Basic.lean`: a 2026 file with *definitions only* (`Polygon P n`,
  `edgePath`, `edgeSet`, `boundary`), and no results on complements;
* complements of countable sets in dimension ≥ 2 (`Set.Countable.isPathConnected_compl_of_one_lt_rank`
  in `Analysis/Normed/Module/Connected.lean`);
* covering-space path and homotopy lifting (`Topology/Homotopy/Lifting.lean`: `exists_path_lifts`,
  `monodromy_theorem`) and `AddCircle` covering maps. A winding-number route could start from
  these, but no winding number of plane loops is defined.

There is no form of the JCT, no polygonal case and no ray-crossing parity.

**Repository.** Present:

* the local structure of a simple closed polygon: `polygon_local_rays` (near each point it is two
  rays) and `ball_diff_rays` (a small square minus two rays is at most two preconnected pieces);
* `local_side_of_split`, `sides_of_split` and `isPreconnected_biUnion_of_local_meet`. These give
  connected one-sided strips along `Γ`, but they **assume** a split as a hypothesis;
* general position (`Tree7GP.lean`: `exists_mem_ball_notMem_lines`, `segment_inter_subsingleton`);
* polygonal arcs and paths in open connected sets (`exists_vpath_of_isConnected`,
  `exists_sarc_of_vpath`, `IsSimplePolyArc.*`, `TwoArcs`), and connectedness of the polygon minus
  points.

**Missing, by the parity argument:**

* (a) the crossing number of a ray from `x` with `Γ`, in a direction avoiding the finitely many
  vertex directions (general position exists), and its independence of the direction mod 2;
* (b) parity is locally constant on `Γᶜ`;
* (c) parity is 0 far away and differs on the two sides of an edge, so there are at least two
  components, one bounded and one unbounded;
* (d) at most two components: each component meets one of the two strips along `Γ`. This is the
  argument of `sides_of_split` rebuilt without the split hypothesis, by a local side choice that is
  consistent along edges and through vertices;
* (e) `frontier U = frontier V = Γ`, from (c) and (d) locally.

(a)–(b) are the delicate part, because the crossing count changes when the ray passes a vertex.
Estimate **2–3 batches**.

### Q6 — `enclose`

**Repository.** Present:

* grids (`gridSq`, `gridVertices`, `exists_grid_offset` for an offset whose vertices avoid a closed
  set with empty interior, `finite_gridSq_meeting`, `mem_gridSq_floor`);
* the notched squares and their polygonal boundaries (`notched`, `notchedPoly`, `frontier_notched'`,
  `strongStar_notched`, `exists_notched_cover`; batches 117–119);
* polyomino combinatorics (`PolyConnected`, `exists_connected_enumeration`,
  `squaresMeeting_connected`, the lattice cycle of batch 110). That cycle runs *through* the squares
  and is not their boundary, so it does not give `J`;
* polygonal paths in open connected sets.

**Missing:**

* (a) The boundary of a finite union `Q` of closed grid squares, as a set of grid edges with every
  vertex of even degree (2 or 4). Degree-4 vertices (two squares meeting at a corner) can be
  avoided by the commission's thickening, or resolved by a turning rule.
* (b) The classification: a 2-regular finite set of grid edges is a disjoint union of simple closed
  lattice polygons. This is the 1-manifold classification that the general-position route of batch
  119 avoided.
* (c) For connected `Q`, the frontier of the unbounded component of `Qᶜ` is **one** of these
  polygons. This is a combinatorial "outer boundary of a polyomino" lemma (for example by filling
  the holes and inducting on squares). Without it, it is again a unicoherence-type statement.
* (d) `polyInterior J ⊆ G`: the holes of `Q` must lie in `G`. This uses that `M` does not separate.
  Choose finitely many polygonal paths in `Mᶜ` (`exists_vpath_of_isConnected`) joining the compact
  set `closedBall ∖ G` to a far point. Their union is compact and at positive distance `d` from
  `M`. With mesh below `d/2` it misses `Q` and lies in the unbounded component of `Qᶜ`, so no hole
  meets it.
* (e) `jct` (Q5), to identify `polyInterior J` with the bounded side.

Estimate **2–4 batches** on top of Q5: (b) and (c) are the bulk, (a), (d) and (e) are short.

### Q7 — `janiszewski` for compacta

**The uses:**

1. `PlaneFacts.exists_theta_point` (batch 118), called from `compFamily_no_circular` (Theorem 6).
   The sets are `A ∪ Γ` and `B ∪ Γ`, where `A = closure C ∩ frontier h₁` and
   `B = closure C ∩ frontier h₂`. They are disjoint compacta, `C` is a component of
   `U ∩ h₁ ∩ h₂`, `U` is the interior of the simple closed polygon `Γ`, and the intersection is
   `Γ`. `A` and `B` are **not** polygonal as the lemma is stated, since `h₁`, `h₂` are arbitrary
   open sets there. In the actual call, however, `h₁` and `h₂` are components of
   `polyInterior J ∩ d` with `d` a notched (polygonal) square. So their frontiers lie in finite
   unions of segments, and `A`, `B` are compact subsets of finite unions of segments; with more
   bookkeeping they are finite unions of segments and points.
2. `PlaneFacts.crosscut'` (batch 119): `Γ₁`, `Γ₂` simple closed polygons with `Γ₁ ∩ Γ₂` a polygonal
   arc. Both sets are polygonal; their union is a polygonal θ-curve.

**Assessment.** A polygonal Janiszewski is within reach from the parity machinery of Q5, by mod-2
cycles of plane straight-line graphs:

* (i) Crossing parity for an *even subgraph* (every vertex of even degree) of a finite plane
  straight-line graph: well defined and locally constant, as in Q5 (a)–(b), with the same proof.
* (ii) If a finite straight-line graph `G` separates `x` from `y`, some even subgraph of `G` has odd
  parity at `x` against `y`. Take the edges having the component of `x` on exactly one side. At a
  vertex the graph is a star of rays, and going round its sectors, membership in the component
  changes an even number of times, so the subgraph is even; parity counts the changes of membership
  along a general-position path.
* (iii) Mayer–Vietoris for graphs: if `A ∩ B` is a connected subgraph, every even subgraph of
  `A ∪ B` is the sum of an even subgraph of `A` and one of `B`. Pair the odd vertices of `z ∩ A`
  (they lie in `A ∩ B`) by paths in `A ∩ B`. This needs a common subdivision of the segments.
* With (i)–(iii), parity is additive, so `A` or `B` separates.

Use 2 is covered directly. Use 1 is covered if `exists_theta_point` is restated for polygonal
`h₁`, `h₂` (as in its only call) and `A`, `B` are shown to be finite unions of segments.
Alternatively, the step "`A ∪ Γ` separates `x` from `y`" could be replaced by a parity argument
inside `U`.

Estimate **2–3 batches** on top of Q5 for (i)–(iii), plus about **1 batch** for the restatement of
use 1. The general Janiszewski for compacta (through Alexander duality, Borsuk or unicoherence of
the plane) is not needed if this route is taken, and is considerably larger.

### Q8 — `treeLike_nonseparating`

I see no route from the three fields alone, so a new field is needed:

* The classical proofs that a tree-like continuum `K` does not separate the plane go through
  Borsuk's criterion: a compactum separates the plane iff it admits an essential map to the circle,
  and maps of tree-like continua to the circle are inessential because they factor approximately
  through trees. Alternatively they go through a duality or unicoherence statement of the same
  strength.
* Janiszewski needs **connected** intersections. The traces `K ∩ closure(link)` of a tree chain on
  `K` are in general disconnected, so an induction over the leaves of the tree chain does not apply.
* `enclose` and `jct` produce polygons around non-separating sets. They do not help to show
  non-separation.

A discharge of `PlaneFacts` would therefore not give `treeLike_nonseparating`. That needs a new
field, Borsuk's separation criterion (or the plane's unicoherence in the Phragmén–Brouwer form for
compacta), or a different, chain-based argument specific to Bing's tree chains, which I do not
have.

---

## Housekeeping

* `LEDGER.md` §1:
  * the Theorem 3 rows now record the proof of the statement as printed;
  * the Theorem 4 row points to a new row for `not_theorem4LiteralND`;
  * a Fugate 1966 row records Corollary 1 as not refuted, with the note on (U).
* `not_theorem4LiteralND` is also listed in the *Refutations* group of `Axioms.lean`.
* `OPEN.md`:
  * item 1 has a batch-124 paragraph;
  * item 2 is narrowed to Theorem 4 with `m ≥ 4` (`Theorem4LiteralGe4`);
  * Theorem 3's only-clause is added to the closed items.
* `README.md`: batch count 124, and the Bing 1948 line updated (Theorem 3 as printed proved,
  Theorem 4 as printed false with three coarse links and open with four or more).
* `doc/census/README.md`: the batch-123 files (`recon-batch123-only.py`,
  `recon-batch123-{only,pair,nocontain}.log`) and the batch-124 files (`recon-batch124-pair.cpp`,
  `recon-batch124-{pair,only,thm4}.log`) listed.
* The notes `theorems-3-4-scheduling(30).md` were moved to `doc/theorems-3-4-scheduling.md`,
  replacing the previous version, and the commission to `doc/batches/COMMISSION-batch124.md`. There
  are no stray copies at the root.
