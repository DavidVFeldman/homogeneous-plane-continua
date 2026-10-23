Commission read: `doc/batches/COMMISSION-batch153.md` (batch 153 — Part F, Jones 1949 V: Whyburn 1939, Corollary 1).

# Report, batch 153

**Status: all six items proved; nothing open.** `lake build HPC` succeeds with `import HPC.Jones.Jones49E`
added at the end of `HPC.lean`. The new files contain no `sorry`. Every new theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.

**Files.**

| file | content |
|---|---|
| `HPC/Jones/Jones49E.lean` | the skeleton items A–F |
| `HPC/Jones/Jones49EArc.lean` | items A and B: polygonal arcs are arcs; the arc theorem for connected open subsets of Peano continua |
| `HPC/Jones/Jones49ETheta.lean` | item E: splitting a simple closed curve at two points; a simple closed curve, then a θ-curve, in a cyclic Peano continuum |
| `HPC/Jones/Jones49EAcc.lean` | item C: accessibility |
| `HPC/Jones/Jones49EPlane.lean` | item D, and the θ-curve lemma used in item F |

**Housekeeping.**
* The uploads are moved off the root: the commission is now `doc/batches/COMMISSION-batch153.md` and
  the skeleton is `doc/batches/skeletons/Jones49E-batch153.lean`.
* `Axioms.lean` has the new group "Whyburn 1939 Corollary 1 (batch 153)".
* `axioms.txt` is regenerated: 1196 lines, no `sorryAx`. The previous version is kept in
  `doc/batches/audits/axioms-before-batch153.txt`.
* `OPEN.md` is unchanged, since nothing is left open.

## 1. The items

**A. `tarc_of_isSimplePolyArc` — proved, statement verbatim.**
* The proof passes to the vertex-function form (`isSimplePolyArc_iff`) and inducts on the number of
  vertices (`tarc_vpath`).
* A nondegenerate segment is an arc (`tarc_segment`, via `AffineMap.lineMap`).
* Each new segment meets the previous path only in the shared vertex, by the `IsSArc` conditions, so
  it is glued on by `TArc.union`.
* Corollary used later: `exists_tarc_of_isOpen_plane`, an arc between two points of a connected open
  plane set.

**B. `exists_tarc_of_locallyConnected` — proved, statement verbatim.**
* *Route:* neither `exists_tarc_of_seq` nor a new chain construction. Moore's nested-simple-chain
  proof of F.A. Theorem 15 is already formalized as `HPC.Moore.exists_irreducible` (batch 137). It
  works in any metric space with a family of "regions" that are connected open sets with compact
  closures, small ones inside every neighbourhood of every point.
* Taking the regions to be all connected open sets of a compact, locally connected metric space
  meets those conditions. The theorem then gives a compact connected subset of `U` irreducible
  between `a` and `b`, and `isIrreducibleConnected_iff_arc` makes it an arc.
* The general form is `exists_tarc_in_open`: two points of a connected open `U` are joined by an
  arc in `U`. Item E needs this form, with `U = X − c`.

**C. `accessible_of_cyclic` — proved, statement verbatim**, by the route of REPORT-batch152 §8.
1. `local_join_of_noncut` applies at `p`, because `M` is cyclic. It gives a function `δ(ε)` such that
   two points of `R` within `δ(ε)` of `p` lie in one component of the open set `R ∩ V_ε(p)`, and
   hence on a polygonal arc in that set (item A).
2. A recursion on states `(xₙ, ρₙ, ρₙ₊₁)` chooses points `xₙ₊₁ ∈ R` with `xₙ₊₁ ≠ xₙ`, close to `p`,
   and arcs `βₙ` from `xₙ` to `xₙ₊₁` in `R ∩ V_{ρₙ}(p)`.
3. The radii are set by `ρₙ₊₂ = min (ρₙ₊₁/2) (dist(p, βₙ))`, which is positive because `βₙ` is
   compact and misses `p`. The `ρₙ` decrease, so `βₘ` misses `βₙ` whenever `m ≥ n + 2`. Also
   `ρ₁ ≤ dist(x₀, p)`, so `x₀ ∉ β₁`, and `ρₙ ≤ 2⁻ⁿ`, so the arcs converge to `p`.
4. `exists_tarc_of_seq` gives an arc from `x₀` to `p` lying in `R + p`.
5. An arc in `R` from `y` to `x₀` is attached by `TArc.join`.

**D. `frontier_cyclic` — proved, statement verbatim, by a route different from the commission's.**
* The commission asked for the two-sided Jordan-curve construction. A shorter argument by
  Janiszewski's theorem proves the same statement; it is `frontier_cyclic'`.
* Suppose `B − z = U ∪ V` is a separation, given by open sets `u`, `v` of the plane. Put
  `P = (B − v) + z` and `Q = (B − u) + z`. These are compact, `P ∪ Q = B` and `P · Q = z`.
* Let `R_P`, `R_Q` be the components of `Pᶜ`, `Qᶜ` containing `R`. Since `P · Q` is connected,
  Janiszewski's theorem (`janiszewski_compact`) gives `R_P · R_Q ⊆ R`.
* `V ⊆ R_P`, since `V ⊆ R̄ ⊆ R_P + P` and `V` misses `P`. Likewise `U ⊆ R_Q`.
* Then `R_Q` and the complement of the closure of `M · R_Q` separate `M − z`: points of `V` lie in
  `R_P`, an open set missing `M · R_Q`. One side contains `U` and the other contains `V`, so `M − z`
  is disconnected, against cyclicity.
* Nondegeneracy (`frontier_diff_nonempty`): if `B ⊆ {z}` then `{z}ᶜ ⊆ R`, so `M ⊆ {z}`, which
  contradicts cyclicity.
* Accessibility, `jordan_curve_theorem` and `tscc_homeomorph_circle` are not used. The hypotheses
  `hMc` and `hS` are kept as in the skeleton but are unused, which gives two unused-variable
  warnings. Only compactness and cyclicity of `M` are needed.

**E. `theta_of_cyclic_peano` — proved, shape chosen.**
* *Shape:* `X` is a compact, connected, locally connected metric space; no point cuts `X`
  (`∀ z, IsConnected {z}ᶜ`); and `¬ TSCC univ`. Then `X` contains three arcs from `a` to `b`
  (`a ≠ b`), any two of which meet only in `{a, b}`.
* Connectedness of `X` is needed: a two-point discrete space has no cut points in this sense.
* *Choice of route:* the θ route rather than the plane route. The θ route closes in three
  first-point trims once item B is available for open sets. The plane route needs every point of
  `B` to have finite order (for `menger_order_two`), and nothing available supplies that.
* *A simple closed curve* (`exists_scc_of_cyclic`):
  1. Take an arc `α` from `a` to `b`, a point `c` inside it, and an arc `β` from `a` to `b` in
     `X − c` (item B, open form).
  2. Let `s` be the last point of `β` on `α[a, c]` and `t` the first point after it on `α[c, b]`;
     both come from `TArc.first_point`.
  3. Then `β[s, t]` and a sub-arc of `α` from `s` to `t` meet only in `{s, t}`.
* *The third arc* (`exists_theta_of_cyclic`):
  1. Take a point `w` off the curve `J` and an arc from `w` to its first point `c₁` on `J`.
  2. Take an arc from `w` to a point `d ≠ c₁` of `J` inside `X − c₁`.
  3. Trim it to its last point `s'` on the first arc, then its first point `t'` on `J`. This gives an
     arc from `c₁` to `t' ≠ c₁` meeting `J` only in its ends.
* `J` is cut at `c₁` and `t'` into two arcs (`tscc_split`, by two rotations `tscc_rot`).

**F. `whyburn39_corollary1` — proved, statement verbatim.**
1. `B = ∂R` is a compact, connected, locally connected subspace (`whyburn39_theorem14`,
   `isConnected_frontier_complDomain`) without cut points (item D).
2. If `B` is a simple closed curve, `tscc_homeomorph_circle` gives the conclusion.
3. Otherwise item E, applied in the subspace `B`, gives a θ-curve in `B`; it is carried to the plane
   by `TArc.subtype_val`.
4. Contradiction from `theta_not_subset_closure`: three such arcs cannot all lie in the closure of
   a connected set `D` that misses them. Here `D = R`.
5. Proof of the θ-curve lemma:
   * Each `Kᵢ + Kⱼ` is a Jordan curve, and `jordan_curve_theorem` gives its two sides.
   * The open third arc lies on one side, `Sₖ`. `D` must lie in `Sₖ`, since otherwise its closure
     misses that arc.
   * The other side `T₃` of `K₁ + K₂` lies in `S₂` and in `S₁`, since its closure contains `K₁ + K₂`.
   * So a point `z ∈ D` and a point `u ∈ T₃` are not separated by `K₁ + K₃` (both in `S₂`) or by
     `K₂ + K₃` (both in `S₁`). These two curves meet in the arc `K₃`, which is connected, so by
     Janiszewski's theorem their union, the whole θ-curve, does not separate `z` from `u`.
   * But it does: `K₁ + K₂` alone separates them, since `z ∈ S₃` and `u ∈ T₃`.
6. Moore's `th26`, which is set in his axiomatic framework, was not needed.

## 2. Ledger entries (`LEDGER.md` §6, "Jones 1949 V")

1. **Corollary 1 is stated without proof.**
   * *Classification:* stated without proof; true.
   * The formal proof uses Theorem 14, Brouwer's boundary theorem, item D (Janiszewski), the arc
     theorem and the θ-curve lemma.
   * The equivalence in footnote 16 (for cyclic continua, semi-local-connectedness is equivalent to
     Wilder's local 0-avoidability) is **not used**. It is not proved in Whyburn 1939, which only
     says it "follows by the argument given under (6. 2)". It is recorded as an unargued remark, not
     used and not decided.
2. **Wilder 1938, Theorem 8a and its first corollary** ("In the plane, if M is a continuum all of
   whose points are locally 0-avoidable, then the boundaries of the complementary domains of M are
   simple closed curves").
   * The conclusion is the same as Corollary 1's.
   * The hypothesis is local 0-avoidability in place of "semi-locally connected and cyclic". The two
     statements agree only through footnote 16's claim, which is not decided here.
   * Wilder's homological proof is not formalized, as instructed.
3. **Degenerate cases.**
   * A single point is not cyclic, and the empty set is excluded by `IsConnected M`.
   * No nondegeneracy hypothesis beyond cyclicity is needed: the theorem is proved with exactly the
     printed hypotheses, and cyclicity keeps `B` nondegenerate (`frontier_diff_nonempty`).
   * A simple closed curve and a closed disc are instances of the theorem; no separate formal check
     was made.

No defective proof is added; the count stays at fourteen.

## 3. Axioms per theorem

All 26 theorems of the new files depend on exactly `[propext, Classical.choice, Quot.sound]`; the
full list is in `doc/batches/audits/axioms-batch153.txt`. The deliverables:

| theorem | axioms |
|---|---|
| `tarc_of_isSimplePolyArc` | propext, Classical.choice, Quot.sound |
| `exists_tarc_of_locallyConnected` | propext, Classical.choice, Quot.sound |
| `accessible_of_cyclic` | propext, Classical.choice, Quot.sound |
| `frontier_cyclic` | propext, Classical.choice, Quot.sound |
| `theta_of_cyclic_peano` | propext, Classical.choice, Quot.sound |
| `whyburn39_corollary1` | propext, Classical.choice, Quot.sound |

## 4. Shape and route changes

* **E:** shape chosen, as above (`theta_of_cyclic_peano`).
* **B:** route recorded (Moore's `exists_irreducible`), proved in the stronger open-set form
  `exists_tarc_in_open`.
* **D:** route changed from the two-sided Jordan-curve construction to Janiszewski's theorem.
  Accessibility (item C) is still proved, by the planned route, as a deliverable in its own right,
  but no other item depends on it.
* Statements A, B, C, D and F are verbatim.

## 5. Reading plan for batch 154: Jones 1949 Theorem 1, Cases 1 and 2

This follows REPORT-batch148 §(v) and the A.18 gaps listed there.

**Setting.** `M` is a homogeneous, aposyndetic, nondegenerate plane continuum.
* It is semi-locally connected: `semiLocConn_of_isAposyndetic`.
* It is cyclic: a nondegenerate continuum has non-cut points (`exists_two_nonCutPoints`), and by
  homogeneity every point is then a non-cut point.
* So **`whyburn39_corollary1` applies to every complementary domain**. This is Jones's "Hence each
  element of `G` is a simple domain … Let the simple closed curve `J` denote the boundary of an
  element `D` of `G`."
* By `whyburn_3_2`/`whyburn_9_2` and `jones49_some_order_two` it is enough to find one point of
  order 2. Assume, for a contradiction, that no point of `M` has order 2.
* `G` is countable: each complementary domain is open, so it contains a point with rational
  coordinates.

**Case 1 (`M − J` connected).**
* *Every point lies on such a curve:* the images of `J` under the homeomorphisms of `M` that come
  with homogeneity.
* *Passage to the boundary of an element of `G`* (gap A.18), via `jordan_curve_theorem`:
  * `M − J′` is connected, so it lies on one side of `J′`.
  * The other side `D′` misses `M`, and its closure adds only points of `J′ ⊆ M`.
  * So `D′` is open and closed in `Mᶜ`, hence a component of `Mᶜ`, with frontier `J′`.
  * This is short, using `conn_sub_of_frontier`.
* *Baire:* `M` is the union of countably many curves `Jᵢ`, so some `Jᵢ` has nonempty interior in
  `M`. Mathlib's Baire category theorem (`BaireSpace` for complete metric spaces) gives this.
* *Limit points:* a point of `Jᵢ` with a neighbourhood in `M` lying in `Jᵢ` has an arc neighbourhood
  in `M`, hence order 2. This is elementary given the arcs of `J ≃ Circle`; it contradicts the case
  hypothesis.

**Case 2 (`M − J = H + K` separated).**
* *The arc `T`:*
  * `H` and `K` lie in the side `E` of `J` other than `D`. `E` is a connected open plane set, so
    `exists_tarc_of_isOpen_plane` (item A) gives an arc from a point of `H` to a point of `K` in `E`.
  * Trimming at the last point on `H̄` and then the first point on `K̄` (`TArc.first_point`) gives an
    arc whose interior misses `M`.
  * The interior is connected and lies in `Mᶜ`, so it lies in one element `U` of `G`.
* *`C ∩ J ≠ ∅`:*
  * The boundary `C` of `U` is a simple closed curve by `whyburn39_corollary1`.
  * `C` contains both ends of `T`, one in `H` and one in `K`, and `C` is connected.
  * `H` and `K` are separated, so `C` meets `J`.
  * The component `AxB` of `C − C·J` containing `x` is an open arc with ends `A`, `B` on `J`; this
    uses `tscc_split` and a first-point trim.
* *"`M − (A + B)` is not connected"* (gap A.18; the main new work):
  * `J + AxB` is a θ-curve with vertices `A` and `B`. `jordan_side` and the θ-curve lemma of this
    batch give the needed side information: each complementary piece of the θ-curve lies on
    determined sides of the three Jordan curves `Kᵢ + Kⱼ`.
  * The plan is to split `M − {A, B}` along the two arcs of `J` from `A` to `B`. `M` misses `D`, and
    `M` misses the side of `AxB + (arc of J)` that contains points of `U` near `T`.
  * The separation of `M − {A, B}` should then come from a Janiszewski argument like the one in
    item D, with `P` and `Q` the two arcs of `J` together with the pieces of `M` attached to them.
    This step has not been worked out in detail.
* *The local separating point:*
  * `M − B` is connected because `M` is cyclic.
  * So `A` separates the open connected set `M − B`, which makes `A` a local separating point
    (Whyburn p. 61; `IsLocalSepPoint`).
* *`jones49_some_order_two`:* `M` is uncountable (a nondegenerate continuum) and homogeneous, so
  some point has order 2, against the case hypothesis.

**Final assembly.**
* `jones49_theorem1 : Jones49Thm1`: in both cases some point has order 2. Then `whyburn_3_2`/(8.4)
  makes every point of order 2, and `menger_order_two` makes `M` a circle.
* Discharge of `h49`: `jones55_circle`, `jones55_theorem2` and `jones55_two_domains`
  (`HPC/Jones/Jones55T2.lean`) take `h49 : Jones49Thm1` as a hypothesis. Applying them to
  `jones49_theorem1` gives unconditional versions of Jones 1955 Theorem 2 and its closing remarks.
* Expected new work, roughly in decreasing order of size:
  1. The θ-curve separation step of Case 2.
  2. The Baire step of Case 1.
  3. The arc `T` and the arc `AxB`.
  4. The final assembly.
