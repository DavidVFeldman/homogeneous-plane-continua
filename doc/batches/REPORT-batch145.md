Commission read: `doc/batches/COMMISSION-batch145.md` (batch 145 — Part E, Moore 1925 I: the space of elements, Theorems 1–4).

# Report, batch 145

`lake build HPC` succeeds with `import HPC.Moore.M25A` added at the end of `HPC.lean`. The skeleton is
kept verbatim at `doc/batches/skeletons/Moore1925I.lean` and the commission at
`doc/batches/COMMISSION-batch145.md` (both moved from the root). The sources are
`doc/sources/moore1925.pdf` (Trans. AMS 27, pp. 416–428; §I is pp. 416–420) and
`doc/sources/moore1925-primeparts.pdf` (Math. Z. 22, pp. 307–315). Nothing new is at the root.
The skeleton is split under `HPC/Moore/` (table below); its definitions are verbatim in
`M25Defs.lean`. The new files contain no `sorry`. `axioms.txt` (regenerated, 1028 lines = 996 + 32)
has `sorryAx` in no line. `OPEN.md` is unchanged.

**Outcome in one line.** Items A (the quotient), B (Theorem 1), C (Brouwer, Janiszewski), D
(Theorem 2), E (Theorem 3), F (Theorem 4) and G (Axioms 1, 2, 4, 5 and F.A. Theorem 4; the region
topology is the quotient topology; the corollary `m25_FA_1_15`) are all **proved**. Nothing is left open.
The Jordan curve theorem is not used anywhere.

| file | content |
|---|---|
| `HPC/Moore/M25Defs.lean` | the skeleton's definitions, verbatim: `elt`, `ptsOf`, `MooreDecomp`, `IsLimitElt`, `mooreRegion`, `spaceOfElts` |
| `HPC/Moore/M25Plane.lean` | plane facts by logarithms: `exists_log_pt`, **`plane_unicoherent`** (closed preconnected sets, not necessarily bounded), `frontier_connectedComponentIn_subset`, **`brouwer_boundary`**, Borsuk's criterion (`exists_log_of_mem_component`, `no_log_of_bounded_component`), **`janiszewski_compact`** |
| `HPC/Moore/M25Quot.lean` | the quotient: tubes, **`isClosedMap_mk_plane`**, **`usc_of_isClosedMap`** (the converse), `mem_nhds_iff_tube`, **`isLimitElt_iff`**, **`m25_domain_iff`**, T1/regular/second countable, **`quotient_metrizable_plane`**, `isProperMap_mk`, connectedness of point sets, `ptsOf_connectedComponentIn`, local connectedness, `frontier_eq_image`, `quot_brouwer`, **`m25_theorem1`** |
| `HPC/Moore/M25Thm.lean` | `exists_region_in_tube`, **`m25_theorem3`**, `exists_region_subset`, `isTopologicalBasis_mooreRegion`, **`spaceOfElts_topology`**, **`m25_theorem4`**, `cl_eq_closure_quot`, **`m25_boundary_iff`** (added), **`m25_unbounded_unique`** |
| `HPC/Moore/M25Thm2.lean` | `not_mem_component_of_separates`, **`m25_theorem2`** |
| `HPC/Moore/M25Ax.lean` | laying finite families end to end (`blockStart`, `levelOf`), **`m25_axiom1`**, **`m25_axiom2`**, **`m25_axiom4`**, **`m25_axiom5`**, **`m25_region_infinite`** (F.A. Theorem 4), **`m25_axioms1245`** |
| `HPC/Moore/M25FA.lean` | **`m25_fa_theorem15`**, **`m25_FA_1_15`** |
| `HPC/Moore/M25A.lean` | umbrella (imports the above) |

All names below are in namespace `HPC.Moore`.

## Items

**A. The quotient — proved.**
* `isClosedMap_mk_plane` (statement as in the skeleton). A closed set `F` missing the element of `x`
  misses a thickening of it (compactness of the element); Moore's u.s.c. gives `d` such that every
  element meeting the `d`-ball about `x` lies in that thickening. Only compactness and the u.s.c. are
  used. The converse is added: `usc_of_isClosedMap` (compact elements and a closed quotient map give
  Moore's u.s.c.). So the two forms are equivalent for compact elements (check 10).
* `quotient_metrizable_plane` (as in the skeleton): T1 (elements closed), regular, second countable
  (tubes of finite unions of sets of a countable basis), hence metrizable by Urysohn. The general form for a
  proper metric space was not attempted: the proofs use only that `Pt` is a proper metric space and
  that the elements are compact, but they are stated for `Pt`.
* `isLimitElt_iff` (as in the skeleton): the tubes `{q | q̄ ⊆ thickening e p̄}` form a neighbourhood
  basis of `p` (`mem_nhds_iff_tube`), and "upper distance `< e` from `p`" is membership in that tube
  (`upper_iff_mem_tube`).
* `m25_domain_iff` (as in the skeleton).

**B. Theorem 1 — proved** (`m25_theorem1`, as in the skeleton). The closed part is the closed map; the
connected part is the continuity of the quotient map. Checks 1 and 2: below.

**C. Plane facts — proved.** Both by logarithms (Eilenberg's method); no Jordan curve theorem, and no
polygonal approximation.
* `plane_unicoherent`: if `ℝ² = A ∪ B` with `A`, `B` closed and preconnected, then `A ∩ B` is
  preconnected (batch 101's argument for `isUnicoherent_univ_of_contraction`, without compactness).
* `brouwer_boundary`: the frontier of a component `D` of the complement of a closed connected `M` is
  connected: `ℝ² = D̄ ∪ (ℝ² − D)`, both closed and connected.
* `janiszewski_compact`: Borsuk's criterion in the two directions (`exists_log_of_mem_component`,
  `no_log_of_bounded_component`; the second by Tietze extension and a large circle), and gluing the
  logarithms of `(z − x)/(z − y)` on `A` and on `B` along the connected `A ∩ B`.
* **Shape change** (both): the skeleton states them inside the section with `hG : MooreDecomp r`
  included; they do not depend on any decomposition and are stated without `hG`. Recorded at each
  statement.
* The batch 131 / Tree67 material was not used. Batch 101's `exists_exp_lift` and
  `sub_const_of_exp_eq` were.

**D. Theorem 2 — proved** (`m25_theorem2`, statement as in the skeleton). Moore's argument, in the
quotient topology: `D` the component of `Mᶜ` containing `x`, `E` the component of `(∂D)ᶜ` containing
`y` (unbounded), `K = ∂E`. `K` is connected by Brouwer twice (`quot_brouwer`). `D ∩ E = ∅`, since
otherwise `E ⊆ D`, and `E` is unbounded. `K − p ≠ ∅`. If `K − p = H ∪ N` with `H`, `N` separated and
nonempty, then `H + p` and `N + p` are closed, and neither separates `X` from `Y`: this is Moore's
argument with `Dₓ` and `q ∈ N` (`side`). Their point sets are compact and meet in the element `p̄`.
So by `janiszewski_compact` their union `K̄` does not separate `X` from `Y`. But it does: the component
of `K̄ᶜ` containing `X` would meet `E`, so it would lie in `E`, and `D ∩ E = ∅`.
`m25_unbounded_unique` is **proved**. **Shape change:** the skeleton's `hH : IsClosed H` and the
section hypothesis `hG` are not used, and are dropped. The complement of a large closed ball is
connected and lies in a single component. Recorded at the statement.

**E. Theorem 3 — proved** (`m25_theorem3`, statement as in the skeleton, with `p ∈ R`). Moore's
construction (`exists_region_in_tube`):
1. a polygon `J` enclosing `p̄` with its interior inside the tube (`planeFacts_holds.enclose`);
2. `H = [J]`, closed (closed map) and connected;
3. `R` the component of `Hᶜ` containing `p`.

Then `R̄` is the component of `H̄ᶜ` containing `p̄` (`ptsOf_connectedComponentIn`), which is Moore's
`D`. So `R` is Moore's `R`; it is open (local connectedness), bounded (inside `J`), and its boundary is
connected (`quot_brouwer`).

**F. Theorem 4 — proved** (`m25_theorem4`, as in the skeleton). It follows from `isLimitElt_iff`, from
Theorem 3 in tube form (`exists_region_subset`), and from the openness of regions. In the same way
the regions form a basis of the quotient topology (`isTopologicalBasis_mooreRegion`), and
**`spaceOfElts_topology`** follows. Moore's `M'` is the quotient closure (`cl_eq_closure_quot`).

**G. The claim of p. 420 — proved** (`m25_axioms1245`, statement as in the skeleton).
* **Axiom 1** (`m25_axiom1`). Fix a metric for the quotient topology. At level `k`, cover the compact
  set of elements meeting the disc `‖x‖ ≤ k` by finitely many Moore regions, each inside a ball of
  radius `1/(k+1)` (Theorem 3). Lay the levels end to end (`blockStart`, `levelOf`). Then (1) every
  element is in the cover of every level `k ≥ ‖x‖`, and (2) once `P ∈ Kₙ` with `n` past the level
  where `2/(k+1) < min(ε, dist P P')`, `Kₙ' = closure Kₙ` lies in `ball P ε ⊆ R` and misses `P'`. This
  is Moore's Theorem 13 of the Math. Z. paper.
* **Axiom 2** (`m25_axiom2`): regions are connected in the quotient, and with Axiom 1, Moore's
  connectedness is quotient connectedness (`isConn_iff`, batch 137), through `spaceOfElts_topology`.
* **Axiom 4** (`m25_axiom4`): `R' = closure R` (quotient) is a closed subset of the compact
  `[closure R̄]`. Heine–Borel by Moore regions is compactness in the region topology
  (`heineBorel_iff`), which is the quotient topology.
* **Axiom 5** (`m25_axiom5`): the elements of the points `(n, 0)` form an infinite set, because the
  quotient map is proper and the points are unbounded. It has no limit element: a tube about any
  element contains only finitely many of them, and points are closed (T1).
* **F.A. Theorem 4** (`m25_region_infinite`, nonempty regions, as in the skeleton): a finite nonempty
  region would have a compact, open, nonempty point set, hence the whole (connected) plane, which is
  unbounded.
* **`spaceOfElts_topology`**: item F.
* **Corollary `m25_FA_1_15`** (added): F.A. Theorem 3 (Axiom 1), Theorem 6 (Axiom 1), Theorem 13
  (Axioms 1, 4), Theorem 14 (Axioms 1, 4; with batch 137's nonemptiness hypothesis), and Theorem 15
  (`m25_fa_theorem15`) for the space of elements.

**Which F.A. Theorems 1–15 need more than Axioms 1, 2, 4, 5** (as formalized in batches 137–138):
* Theorems 1, 10: no axioms.
* Theorems 2, 3, 6–9: Axiom 1.
* Theorems 11–14: Axioms 1, 4.
* **Theorem 4** (regions infinite) and **Theorem 5** (nested regions closing down on `P`): Axioms 1,
  3, 5₁ in batch 137. Moore's p. 420 lists Theorem 4 *alongside* the axioms for exactly this reason.
  For the space of elements, Theorem 4 is `m25_region_infinite`. Theorem 5 follows from Theorem 4 and
  Axiom 1 by batch 137's own proof (`fa_theorem5` uses Axioms 3 and 5₁ only through `exists_ne_of_region`, i.e. Theorem 4). An
  instance was not stated.
* **Theorem 15** (and 16): Axioms 1, 2, 4 and metrizability, which batch 137 draws from Axioms 3 and
  5₁. For the space of elements, metrizability comes from the quotient, and `m25_fa_theorem15` applies
  batch 137's construction (`exists_irreducible`) as it stands. Theorem 16 needs Axiom 3 for its
  exterior half (batch 147).

## Ledger entries (`LEDGER.md` §6, subsection *batch 145*)

1. **Theorem 1, I** ("a subsequence of distinct points"): recorded, harmless (a constant subsequence
   does the job). Our proof uses no sequences.
2. **Theorem 1, II** ("that element of `H₁` which contains `p`"): recorded, typographical (`P`).
3. **Boundary** (p. 417): as printed ("elements `[x]` of `H`") the second clause is empty. Read with
   "of `G`", it is the quotient frontier: `m25_boundary_iff`, **proved**.
4. **Complementary domain** (p. 417): under the literal definition "the" unbounded complementary
   domain is not unique, and **Theorem 2 fails**. This is an informal argument, not formalized: take
   the decomposition into points, `M` a closed disc, `D` the open disc minus a radius, and as `E` the
   plane minus the radius, whose boundary, a segment, is cut by each of its interior points. Read as
   components (the skeleton), Theorem 2 holds and the unbounded component is unique.
5. **Theorem 2's proof**:
   * "`B` is a closed and connected set" is supplied by Brouwer twice (`∂D`, then `∂E`).
   * "Clearly `Dₓ` contains `D`" and "`q` does not belong to the boundary of `Dₓ`" are supplied.
   * Only the closedness of `H + p`, `N + p` is used, not their connectedness.
   * `K − p ≠ ∅` is supplied.
6. **Theorem 3's statement**: `p ∈ R` added (skeleton). Moore's proof gives it.
7. **Theorem 3's proof**: all four sentences are supplied (`isConnected_ptsOf`, `quot_brouwer`,
   `isOpen_connectedComponentIn_quot`, `frontier_eq_image`). The interior of the enclosing polygon is
   used for the last sentence.
8. **Theorem 4**: supplied. It uses `isLimitElt_iff` (u.s.c. ⇒ tubes form a neighbourhood basis),
   Theorem 3 in tube form, and the openness of regions.
9. **p. 420**: proved. What "methods largely analogous" amounts to, from the Math. Z. paper §§1–2
   (pp. 307–313):
   * Theorem 13 there (finite covers by regions of radius `< 1/n`, laid end to end) is our Axiom 1.
   * Theorem 12 (Heine–Borel for closed sets, by circles and Theorem 7) is the model for Axiom 4.
   * Theorems 10 and 11 are the analogues of 1925 Theorems 4 and 1.
   * Axiom 2 is immediate there from the definition of `R_pe`.

   The Math. Z. paper argues neither Axiom 5 nor F.A. Theorem 4. In its own setting (a bounded
   continuum) the space of prime parts is compact by its Theorem 12, so Axiom 5 as transcribed
   (an infinite set with no limit point) cannot hold there once there are infinitely many prime parts.
   This is an informal remark, not formalized. In the 1925 setting Axiom 5 holds (`m25_axiom5`).
10. **u.s.c. vs. open-set form**: equivalent for compact elements (`isClosedMap_mk_plane`,
    `usc_of_isClosedMap`). Compactness is used in both directions.

## Axioms

Every theorem declared in the batch-145 files depends on `[propext, Classical.choice, Quot.sound]`
or a subset of it: 85 theorems, listed by `doc/batches/audits/axioms-batch145.txt` (generated by
`axioms-batch145.lean`). The main ones (group *Moore 1925 §I, Theorems 1–4 (batch 145)* of
`Axioms.lean`) are `plane_unicoherent`, `frontier_connectedComponentIn_subset`, `brouwer_boundary`,
`no_log_of_bounded_component`, `janiszewski_compact`, `isClosedMap_mk_plane`, `usc_of_isClosedMap`,
`quotient_metrizable_plane`, `isProperMap_mk`, `isLimitElt_iff`, `m25_domain_iff`,
`ptsOf_connectedComponentIn`, `locallyConnectedSpace_quot`, `quot_brouwer`, `m25_theorem1`,
`exists_region_in_tube`, `m25_theorem3`, `isTopologicalBasis_mooreRegion`, `spaceOfElts_topology`,
`m25_theorem4`, `cl_eq_closure_quot`, `m25_boundary_iff`, `m25_unbounded_unique`, `m25_theorem2`,
`m25_axiom1`, `m25_axiom2`, `m25_axiom4`, `m25_axiom5`, `m25_region_infinite`, `m25_axioms1245`,
`m25_fa_theorem15`, `m25_FA_1_15`. All of them show `[propext, Classical.choice, Quot.sound]`.

## Reading plan for batch 146: Theorems 5–11 (pp. 420–424)

Definitions to note first. The 1925 *simple continuous arc* (p. 417) is the **cut-point**
definition of Moore 1920: a closed, connected, bounded set containing `A`, `B`, disconnected by the
omission of any element other than `A` and `B`. F.A.'s arc (batch 137's `Space.IsArc`) is Lennes'
**irreducibility** definition. The 1925 *simple closed curve* is "disconnected by the omission of any
two of its elements". F.A.'s is "the union of two arcs with only their ends in common". So
Theorems 5, 6, 7 and 10 are, in substance, the equivalence of these definitions in the space of
elements. The Math. Z. paper (p. 313) says the same: "in the presence of Axioms 1 … and 4 of F.A.,
this definition is equivalent to another definition", citing Moore 1920, p. 340.

What batches 137–144 (and earlier) already contain:
* `isIrreducibleConnected_iff_arc` (`HPC/Moore/ArcChar.lean`, Mathlib only): in a metrizable space,
  an irreducible continuum between `a ≠ b` is an embedded `[0, 1]`, and conversely.
* `isArc_iff_topological` (Axioms 1, 4): F.A. arcs are the compact connected sets irreducible
  between their ends.
* `exists_two_nonCutPoints` (batch 94, `HPC/Plane/NonCut51Gen.lean`, Mathlib only): Moore's
  non-cut-point theorem.
* `fa_sec5_*`, `fa_scc_two_arcs` (`HPC/Moore/Arcs.lean`): the p. 139–140 arc facts, for F.A.'s
  definitions, with Axioms 1, 3, 4, 5₁, i.e. through metrizability.

For the space of elements the metrizability is supplied by `quotient_metrizable_plane`. So:

* **Theorem 5** (no arc is disconnected by the omission of an extremity). The analogous argument
  (F.A. p. 139; Moore 1920 p. 342): a cut-point arc is irreducible between its ends, hence an embedded
  `[0, 1]`, and `[0, 1]` minus an endpoint is connected.
  * Missing piece: *cut-point arc ⇒ irreducible*. If a cut point `p` left `A` and `B` on one side
    `U`, then the other side plus `p` is a continuum with two non-cut points (batch 94), one of them
    `≠ p`; it would be a non-cut point of the whole arc other than `A`, `B`.
  * This is general continuum theory (Mathlib plus batch 94). It is not in batches 137–144 for an
    abstract space with Axioms 1, 2, 4, 5, and it is **not** inherited through `m25_FA_1_15`.
* **Theorem 6** (closed connected subsets of an arc with more than one element are arcs). Once arcs
  are embedded `[0, 1]`'s, these are subintervals. Batches 137–138 contain this for F.A. arcs
  (`eq_image_uIcc_of_isArc_subset`, `fa_sec5_interval_unique`), so it is inherited after Theorem 5's
  identification, through quotient metrizability.
* **Theorem 7** (limit elements along an arc via sub-arcs containing `x`). This is F.A. p. 139's
  limit-point statement; batch 137 proved the corrected form (`fa_sec5_limitPt_iff`) and refuted the
  printed one at the endpoints (`not_fa_sec5_limitPt_printed`). In 1925 `x` is distinct from `p` and
  `q`, so the endpoint defect does not arise. But the printed "then `p` is a limit element of the set
  `H`" should read "`x`" (a slip to record). Inherited after the identification.
* **Theorem 9** (`G − pq` is connected), "by an argument largely similar to that used in the proof of
  Lemma 8" of P.C.S., with Theorems 2 and 6.
  * The plan: if `p̄q̄` had a bounded complementary domain `D`, its outer boundary `K ⊆ pq` would be a
    continuum of elements with `K − r` connected for every `r ∈ K` (Theorem 2). By Theorem 6 it would
    be a sub-arc, which is cut by its interior elements, unless `K` has at most two elements.
  * This is plane-specific. It is not in batches 137–144 (in F.A. it would follow from Axioms 1–8,
    i.e. from `m19_plane`, which is not available here). It uses `m25_theorem2` and Theorem 6.
* **Theorem 10** (a simple closed curve of elements is the union of two arcs from `p` to `q`), "a
  consequence of Theorem 4 of" Moore 1920: a continuum disconnected by the omission of any two points
  is a simple closed curve. This is the cut-point characterization of the circle, general continuum
  theory, and **not** in batches 137–144 (`fa_scc_two_arcs` presupposes Lennes' definition). The
  likely route: `C − {p, q} = U ⊔ V`, and `U ∪ {p, q}` is a cut-point arc from `p` to `q` (Theorem 5's
  machinery).
* **Theorem 11** (the Jordan curve theorem for curves of elements) uses Theorems 9 and 10 and
  **Mullikin's theorem**: two continua neither of which separates the plane, whose common part is two
  disjoint continua, have a union whose complement is exactly two domains.
  * The separation half is the Phragmén–Brouwer property, and follows from `plane_unicoherent` and
    the logarithm machinery of `M25Plane.lean`.
  * "Exactly two" needs Eilenberg's counting argument: the number of complementary domains is at most
    the number of components of the common part.
  * Neither half needs the general Jordan curve theorem. The polygonal JCT and Janiszewski in the
    repository are not needed either.

**The shortcut, weighed.** The alternative is to verify Axioms 3, 6, 7, 8 for the quotient topology
directly by plane topology, using `spaceOfElts_topology`.
* Axiom 3 is Brouwer-type and already within reach: `m25_unbounded_unique`, `quot_brouwer`, Theorem
  12's argument.
* Axiom 8 needs the JCT for simple closed curves of elements in the quotient, i.e. Theorems 9–11 in
  substance. The shortcut does not avoid Mullikin's theorem; it only reorders.
* Recommendation: follow Moore's order, but prove the two cut-point characterizations (arcs and
  simple closed curves) once, for compact metric continua (Mathlib + batch 94 + `ArcChar`). Then
  Theorems 5–7 and 10 are short instances, and the plane-specific work is concentrated in Theorem 9
  (via `m25_theorem2`) and Mullikin's theorem (via the logarithms of `M25Plane.lean`).
* `m25_FA_1_15` alone does not deliver Theorems 5–7, 9, 10. The abstract theorems of batches
  137–144 that would deliver them are stated for F.A.'s definitions of arc and closed curve, and the
  1925 definitions differ.
