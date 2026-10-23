# The classification of homogeneous plane continua: the whole path, minimally

This is a reading guide to the proof of the classification that is formalized in this repository.
It follows the dependency graph of the two final theorems, `BJ59.ho16_classification₄` and
`BJ59.ho16_classification_plane₄` (`HPC/BJ59/BJ59E.lean`), and nothing else: every result stated
below is used, directly or indirectly, by those two theorems. Results that the repository proves
but the classification does not use are not mentioned, even when they come from the same papers.
For example, Bing 1948 Theorems 3, 7–9 and 13–15, Bing–Jones Theorems 2, 6 and 9, and the
refutations of printed statements are left out.

"First principles" means the standard point-set topology and analysis available in Mathlib:
compact metric spaces, connectedness and components, the Baire category theorem, Polish spaces,
Urysohn functions, Lebesgue numbers, Hausdorff limits, the complex exponential, and the circle
`Circle ⊂ ℂ`. Everything else is proved on the way.

Each section gives the statements and, for each one, the idea of the proof. Lean names are given in
backticks without the leading `HPC.`, so `Jones.jones55_c` means `HPC.Jones.jones55_c`. Where the
formal proof takes a different route from the source paper, a short note says so.

**Conventions.** The plane is `Pt = ℝ × ℝ`. A *continuum* is a compact connected metric space; in
the Lean code it may be a single point, and "nondegenerate" is stated separately where it is needed.
A continuum is *decomposable* if it is the union of two proper subcontinua, and *indecomposable*
otherwise. It is *hereditarily indecomposable* (HI) if every subcontinuum is indecomposable. A space
is *homogeneous* if for all points x, y some self-homeomorphism carries x to y. A *simple closed
curve* is a space homeomorphic to the circle S¹.

---

## 0. The theorem and the shape of its proof

**Classification theorem** (`BJ59.ho16_classification₄`). A nondegenerate plane continuum M is
homogeneous if and only if M is a simple closed curve, a pseudo-arc, or a circle of pseudo-arcs.

**Plane form** (`BJ59.ho16_classification_plane₄`). There are plane continua C₁, C₂, C₃ such that
C₁ is a simple closed curve, C₂ is a pseudo-arc and C₃ is a circle of pseudo-arcs. Each of them is
homogeneous, no two of them are homeomorphic, and a nondegenerate plane continuum is homogeneous if
and only if it is homeomorphic to one of them.

The three classes are defined as follows.

* A continuum is *snake-like* (chainable) if for every ε > 0 it is covered by a chain of open sets
  of diameter < ε (§2). A *pseudo-arc* is a nondegenerate, snake-like, hereditarily indecomposable
  continuum (`Plane.IsPseudoArc`).
* A *circle of pseudo-arcs* (`BJ59.IsCircleOfPA`, Bing–Jones 1959) is a circle-like continuum X
  with a continuous, open, surjective map f : X → S¹ all of whose fibres are pseudo-arcs.

The proof has five parts.

1. **The pseudo-arc** (Part III). From Bing 1948 and 1951: a pseudo-arc exists in the plane, any
   two pseudo-arcs are homeomorphic, and a pseudo-arc is homogeneous.
2. **The indecomposable case** (Part IV). An indecomposable homogeneous plane continuum is a
   pseudo-arc. It is HI (Hagopian 1976), it has span zero (Theorem C of Hoehn–Oversteegen, via
   Oversteegen–Tymchatyn 1982), and an HI continuum of span zero is snake-like (Hoehn–Oversteegen
   2016, Theorem 1).
3. **The decomposable case** (Part V). A decomposable homogeneous plane continuum is either a
   simple closed curve or has an open atomic map onto the circle with pseudo-arc fibres. This
   uses Jones's aposyndetic decomposition (Jones 1955), Jones 1949 and the indecomposable case.
4. **Circles of pseudo-arcs** (Part VI). Bing–Jones Theorem 10: two "arcs of pseudo-arcs" are
   homeomorphic by a fibre-preserving homeomorphism extending given homeomorphisms of the end
   fibres. It follows that any two circles of pseudo-arcs are homeomorphic, that each one is
   homogeneous, and that every continuum with an open atomic pseudo-arc map onto the circle is a
   circle of pseudo-arcs. A circle of pseudo-arcs in the plane is constructed explicitly.
5. **Assembly** (Part VII).

Parts III–VI rest on the general theory of continua (Part I) and on plane topology (Part II). Two
foundations need the most work. The first is Moore's characterization of the plane, which shows
that a decomposition of the plane into non-separating continua is again a plane (Moore 1925). The
second is the Effros theorem for homogeneous compacta.

```
      Part I (continua, chains, Effros, decompositions)    Part II (plane topology, Moore)
                 |                                                  |
   +-------------+-----------------+---------------------+----------+------------+
   |                               |                     |                       |
 Part III                       Part IV                Part V                  Part VI
 pseudo-arc:                    indecomposable ⇒       decomposable ⇒          Bing–Jones Thm 10;
 exists, unique,                HI (Hagopian),         circle, or atomic       circles of pseudo-arcs:
 homogeneous                    span 0 (O–T),          pseudo-arc map onto     unique, homogeneous,
                                snake-like (H–O)       the circle (Jones)      one in the plane
   +-------------------------------+---------------------+-----------------------+
                                             |
                                     Part VII: assembly
```

---

# Part I. Foundations

## 1. Continua

**1.1 Boundary bumping.** Let L be a continuum and F a proper closed subset. Every component of F
meets the boundary of F in L. In open form: if O is open and L ⊄ O, every component of a closed
neighbourhood inside O reaches its frontier. A compact piece of a connected set behaves the same
way. (`Plane.exists_continuum_bump_closed`, `Plane.exists_continuum_bump_open`,
`Jones.exists_continuum_bump_compact`, `T13.clopen_meets_closure_diff`.) *Proof:* components of a
compact Hausdorff space are quasi-components, so a component missing the frontier is cut off from it
by a clopen set. This contradicts the connectedness of L.

**1.2 The cut-wire theorem.** If no subcontinuum of the compact set F meets both of the disjoint
closed sets A and B, then F = F₁ ⊔ F₂ with F₁, F₂ closed, A ⊆ F₁ and B ⊆ F₂
(`Plane.exists_split_of_no_continuum`, `Jones.exists_clopen_of_connectedComponentIn_disjoint`).
*Proof:* components equal quasi-components; cover by finitely many clopen sets. Moore's Theorem 44
is the same statement for a compact set with no preconnected set meeting both pieces
(`Plane.exists_closed_split_of_no_connected`).

**1.3 Brouwer reduction and irreducible continua.** A property of subcontinua that passes to
intersections of decreasing chains has minimal elements (`Plane.exists_minimal_of_seq`,
`Span.brouwer_reduction`, `Span.isContinuum_sInter_chain`). In particular, a continuum containing
two points (or two closed sets) contains a subcontinuum that is irreducible between them
(`exists_irreducible`).

**1.4 Non-cut points.** A nondegenerate continuum has at least two non-cut points
(`Plane.exists_two_nonCutPoints`, `Plane.exists_nonCutPoint_of_cut`; Moore, Nadler 6.6).
*Proof:* if p is a cut point, write X ∖ p = A ∪ B with A, B separated; then A ∪ {p} is a continuum,
and a nested argument (or boundary bumping and compactness) finds a non-cut point of X in each side.
The elementary tools are `Plane.exists_separated_of_not_isPreconnected` (Nadler 6.2),
`Plane.isContinuum_union_piece` and `Plane.isPreconnected_union_of_separated` (Nadler 6.3), and
`Plane.subset_side_of_isPreconnected`.

**1.5 Indecomposability and composants.** The *composant* of x in M is the union of the proper
subcontinua of M that contain x. In a nondegenerate indecomposable continuum M:

* a proper subcontinuum has empty interior in M (`T13.false_of_interior`; otherwise M would be the
  union of it and the closure of its complement);
* every composant is dense (Moore 135, `Hagopian.composant_dense`) and meagre (Moore 136–137,
  `Hagopian.composant_isMeagre'`);
* two composants are equal or disjoint (Moore 138, `Hagopian.composant_eq_or_disjoint`);
* there are uncountably many composants (Moore 139, `Hagopian.uncountable_composants`; each is a
  countable union of nowhere dense proper subcontinua, so by Baire they cannot be countably many);
* in particular each composant is a proper subset (`composant_ne_of_indecomposable`), and some point
  lies in no proper subcontinuum through a given point (`T13.exists_not_mem_proper_subcontinua`).

**1.6 Monotone maps.** Under a continuous map of compacta with connected fibres, preimages of
connected sets are connected (`Plane.Mono.isConnected_inter_preimage`,
`BJ59.isPreconnected_preimage_of_monotone'`).

**1.7 Triods.** A *triod* is a continuum T with a subcontinuum H such that T ∖ H is the union of
three nonempty pairwise separated sets; a continuum is *atriodic* if it contains none. A continuum
is *unicoherent* if the intersection of any two subcontinua whose union is the whole is connected,
and *hereditarily unicoherent* if every subcontinuum is unicoherent. The bridge used later is "a
triod is a weak triod": an essential sum of three continua with a common point
(`Plane.IsTriod`, `Plane.IsWeakTriod`, `Plane.isWeakTriod_of_isTriod`; Nadler 11.23–11.25).

## 2. Chains, snake-like and circle-like continua

**2.1 Chains.** A *chain* of length n is a sequence of open sets L₀, …, L_{n−1} (*links*) with
Lᵢ ∩ Lⱼ ≠ ∅ exactly when |i − j| ≤ 1 (`Chain`). It is an *ε-chain* if every link is bounded of
diameter < ε (`Plane.IsEpsChain`). A chain E *refines* D if every link of E lies in a link of D
(`Chain.Refines`). E *follows the pattern* x : {0..m−1} → {0..n−1} in D if Eᵢ ⊆ D_{x(i)}
(`Chain.FollowsPattern`). F is a *consolidation* of D if each link of F is a union of links of D
(`Chain.IsConsolidationOf`). A *circular chain* is the same with indices read modulo n
(`Plane.CircChain`, `Plane.IsCircEpsChain`).

Two elementary facts are used throughout. A preconnected set inside the union of a chain that
meets links i and j meets every link between them (`Chain.inter_link_nonempty_between`). A set of
diameter d covered by an ε-chain needs at least d/ε links (`Chain.diam_le_length_mul`).

**2.2 Crookedness** (Bing 1948, `Chain.IsCrookedIn'`). E is *crooked in* D if E refines D and,
whenever links Eᵢ, Eⱼ meet D_h and D_k with k > h + 2, there are indices r, s between i and j, in
the order i, r, s, j, with E_r ⊆ D_{k−1} and E_s ⊆ D_{h+1}. In words: to get from D_h to D_k, E must
go almost all the way, come almost all the way back, and go again.

**2.3 Snake-like and circle-like.** A continuum is *snake-like* if it is covered by an ε-chain for
every ε > 0 (`Plane.IsSnakeLike`), and *circle-like* if it is covered by ε-circular chains
(`Plane.IsCircleLike`). Facts used:

* *ε-map criterion*: a compact connected metric space with, for every ε, a map onto [0, 1] with
  fibres of diameter < ε is snake-like (`Plane.isSnakeLike_univ_of_epsMap`,
  `Plane.isSnakeLike_of_epsMap`). Conversely, an ε-chain gives an ε-map by weighted means of
  distance functions (`BJ59.exists_epsMap_of_chain`). Hence snake-likeness and hereditary
  indecomposability are topological, and so is being a pseudo-arc
  (`BJ59.isSnakeLike_of_homeomorph`, `BJ59.isHereditarilyIndecomposable_of_homeomorph`,
  `BJ59.isPseudoArc_of_homeomorph`). Circle-likeness also passes along homeomorphisms
  (`BJ59.isCircleLike_univ_of_homeomorph`).
* A snake-like continuum is unicoherent, and its subcontinua are snake-like
  (`Plane.isUnicoherent_of_isSnakeLike_aux`, `Plane.isSnakeLike_of_subcontinuum_aux`; Nadler 12.2,
  12.5).
* A proper subcontinuum of a circle-like continuum is snake-like (`Plane.isSnakeLike_of_subset_circleLike`,
  Nadler 12.51). *Proof:* pick x outside it and a link containing x that misses it; the remaining
  links, read cyclically from the next one, form a chain.
* A *weak chain* (non-consecutive links disjoint) can be trimmed to a chain
  (`Plane.exists_chain_of_weak`).
* Limits of finely chained connected sets are connected (`T13.isPreconnected_limSup`).

## 3. Homogeneity and the Effros theorem

**3.1 The homeomorphism group.** For a compact metric space Y, the group H(Y) of self-homeomorphisms,
with the topology of uniform convergence of maps and inverses, is a Polish topological group acting
continuously on Y (`Effros.homeoGroup`, `Effros.homeoTopology`).

**3.2 The open mapping principle** (Effros 1965, in van Mill's 2004 proof; `Effros.effros_open_mapping`).
If a Polish group G acts continuously and transitively on a nonempty metric Baire space X, then for
every x and every neighbourhood U of 1, U·x is a neighbourhood of x.
*Proof (van Mill):* U·x is not meagre, because countably many translates of U cover G (Lindelöf)
(`Effros.vanMill_3_2`). Analytic nowhere-meagre sets that are dense in one another meet
(`Effros.inter_nonempty_of_nowhereMeagre`, Proposition 2.2, by a nested Cantor-scheme
construction). From this, x lies in the interior of the closure of U·x and the interior of the
closure of U_{n+1}·x lies in U_n·x (Lemmas 3.3–3.5, `Effros.vanMill_3_5`), which gives the claim.

**3.3 Effros for homogeneous compacta** (`Effros.effros_homogeneous`). Let Y be a homogeneous compact
metric space. For every ε > 0 there is δ > 0 such that any two points at distance < δ are carried
one to the other by a homeomorphism that moves every point by less than ε.
*Proof:* apply 3.2 to U = {h : sup-displacement < ε/2} and take a Lebesgue number of the cover by
the interiors of the sets U·z.

This is the only way homogeneity enters the local arguments of Parts IV and V. Its consumers are
Hagopian's Lemma 1 (1984) and Lemma 4 (1975), Jones 1975, Jones's aposyndesis lemma (§18), and
Oversteegen–Tymchatyn's Theorem 3.6 and Corollary 3.5.

## 4. Decompositions

Let r be an equivalence relation on a compact metric space X with closed classes.

* r is *upper semicontinuous* (u.s.c.) if the saturation of every closed set is closed
  (`Jones.IsUSCDecomp`). A closed relation on a compact metric space is u.s.c.
  (`Jones.isUSCDecomp_of_isClosed`).
* r is *continuous at a class* g if it is also lower semicontinuous there (`Jones.LSCAt`), and
  *continuous* if it is so at every class (`Jones.IsContinuousDecomp`).
* The quotient of a u.s.c. decomposition of a compact metric space is compact metrizable
  (`Jones.metrizableSpace_quotient`).
* **Residual continuity** (Kuratowski, Fort; used without statement by Jones 1955): a u.s.c.
  decomposition is continuous at the classes of a residual subset of the quotient
  (`Jones.residual_lscAt`).
* A homeomorphism of X that permutes the classes descends to the quotient
  (`Jones.exists_homeomorph_quotient`).
* The quotient map of a continuous decomposition is open (`BJ59.isOpenMap_quotient_mk_of_continuous`):
  the saturation of an open set is open by lower semicontinuity.

---

# Part II. Plane topology

## 5. Logarithms, separation and polygons

Separation in the plane is handled almost everywhere by continuous logarithms rather than by the
Jordan curve theorem.

**5.1 Lifting.** On a space that contracts to a point by a homotopy, every continuous map into ℂ∖0
has a continuous logarithm, and two logarithms on a preconnected set differ by a constant
(`Plane.exists_exp_lift`, `Plane.sub_const_of_exp_eq`, `Moore.exists_exp_lift_of_homotopy`).
In particular every nonvanishing map of the plane has a logarithm (`Moore.exists_log_pt`).

**5.2 Separation by logarithms.** For a closed K ⊂ ℝ²:

* if y lies in the component of x in Kᶜ, then (z − x)/(z − y) has a logarithm on K
  (`Moore.exists_log_of_mem_component`);
* if x lies in a bounded component of Kᶜ, then no power of z − x has a logarithm on K
  (`Moore.no_log_of_bounded_component`, `Moore.no_log_pow_of_bounded_component`);
* **Borsuk** (the direction used): if K is compact and Kᶜ is connected, every nonvanishing map on K
  has a logarithm (`Moore.borsuk_exists_log`).

Consequences:

* **Janiszewski's theorem** (`Moore.janiszewski_compact`). Let A, B be compact with A ∩ B connected
  or empty. If neither A nor B separates x from y, then A ∪ B does not. *Proof:* glue the
  logarithms of (z − x)/(z − y) on A and on B; they differ by a constant on A ∩ B.
* **Brouwer's boundary theorem** (`Moore.brouwer_boundary`). The frontier of a complementary
  domain of a closed connected plane set is connected.
* **Separation is a topological invariant** of compact plane sets
  (`Jones.separatesPlane_of_homeomorph`). If A separates, z − x has no logarithm on A for x in a
  bounded component; transported to B by the homeomorphism, the same map would have one if B did
  not separate.
* **Weak invariance** for continua (`Hagopian.exists_separating_subcontinuum_of_homeomorph`): if K
  separates and the continuum K′ is homeomorphic to K, then some subcontinuum of K′ separates. On a
  tree-like plane continuum every nonvanishing map has a logarithm
  (`Hagopian.exists_log_of_isTreeLike`), and §8.2 makes a continuum with no separating subcontinuum
  tree-like.

**5.3 Polygons.** For a closed polygon (not necessarily simple), the parity of the number of
crossings of the half-open ray to the east (`Plane.CrossesEast`, `Plane.crossesEast_jump`) is locally
constant off the polygon and vanishes far away (`Plane.parity_eventually_eq`, `Plane.parity_far`).
From this:

* the **Jordan curve theorem for simple closed polygons** (`Plane.jct_polygon`);
* **Janiszewski's theorem for polygonal sets** (`Plane.janiszewski_polygonal`);
* a connected open set is polygonally connected, and a polygonal path contains a simple polygonal
  arc (`Plane.exists_vpath_of_isConnected`, `Plane.exists_simplePolyArc_of_polyPath`);
* a simple polygonal arc is a topological arc (`Jones.tarc_of_isSimplePolyArc'`);
* an open connected plane set minus a point is connected (`Plane.isConnected_diff_singleton_of_isOpen`);
* no logarithm exists on a simple closed polygon around p (`Plane.no_log_on_polygon`), and
  polygons can be drawn around points inside open sets (`Plane.exists_polygon_around`);
* **enclosing polygons**: a continuum M that does not separate the plane lies, inside any open
  G ⊇ M, in the interior of a simple closed polygon in G that misses M (`Plane.enclose_holds`).

These three plane facts (polygonal Jordan, polygonal Janiszewski, enclosing polygons) are bundled
as `Plane.PlaneFacts` and proved as `Plane.planeFacts_holds`.

## 6. Moore's axioms characterize the plane (Moore 1916, 1919)

This section is needed for one theorem only: Moore 1925 (§7), which shows that certain
decomposition spaces are planes. Moore's route works with "points" and "regions" satisfying
Axioms 1–8 of *On the foundations of plane analysis situs* (1916):

1. there is a sequence of regions K₁, K₂, … from which small regions about any point can be
   chosen, with closures inside any given region (`Moore.Space.Axiom1`);
2. regions are connected;
3. the complement of the closure of a region is connected;
4. closures of regions are compact;
5. there is an infinite set without limit point, and there are at least three points;
6. and 7. two conditions on boundary points of regions (accessibility by arcs from inside and from
   outside);
8. every simple closed curve bounds a region (`Moore.Space.Axiom8`).

**6.1 The bridge to topology.** The regions form a basis of a regular T₁, metrizable topology, and
Moore's notions (limit point, closure, connected, arc) are the topological ones
(`Moore.isTopologicalBasis_region`, `Moore.fa_theorem6`, `Moore.t1Space`, `Moore.regularSpace`,
`Moore.cl_eq_closure`). Two points of a connected open set lie in an irreducible continuum inside
it (Theorem 15, by nested simple chains of regions, `Moore.exists_irreducible`). **Arc
characterization:** in a metrizable space, a compact connected set irreducible between A ≠ B is an
embedded [0, 1] from A to B, and conversely (`Moore.isIrreducibleConnected_iff_arc`,
`Moore.ac_homeomorph`, `Moore.isArc_iff`). The order of a cut-point arc is constructed and mapped
monotonically onto [0, 1]. Arcs glue at a common end point (`Moore.Gen.TArc.union`).

**6.2 Closed curves and interiors (Moore 1916 §§5–7).** Every boundary point of a region is a limit
point of its exterior (Theorem 20, `Moore.fa_theorem20`). Every closed curve has exactly one interior
(`Moore.existsUnique_interior`). The θ-curve theorems (24–27) say that a cross-cut divides an
interior into two interiors (`Moore.split_interior_of`). Arcs into and out of regions (28, 31, 32)
and the connectedness of R − AB (33, 34) follow. There are closed curves about points and inside
regions (35, 36). If two interiors meet, some closed curve on J₁ ∪ J₂ has an interior containing
both (Theorem 41, by replacing a null family of arcs of J₂ by chords of J₁, `Moore.fa_theorem41`),
and likewise for a finite family with connected union of interiors (Theorem 42,
`Moore.fa_theorem42`).

**6.3 From the axioms to ℝ² (Moore 1919).** *Double rulings* subdivide the interior of a closed
curve ABCDA into cells. Theorem D (`Moore.m19_theoremD`) says that if every point on or inside ABCDA
lies inside some curve of a family G, the interior can be ruled into cells each inside a curve of
G; the formal proof takes a route different from Moore's. Nested rulings of vanishing mesh give a
grid, and a compact set carrying a grid of two families of lines is a closed square, sides to sides
(`Sq.Grid.exists_square`). This proves the **Schoenflies theorem** in Moore's space: the closure of
the interior of a closed curve is a closed disc with the curve as boundary
(`Moore.exists_square_of_interior`). The **annulus lemma** (`Moore.exists_collar`) says that the
closed region between nested closed curves is a collar J × [0, 1] of the inner one; it is proved by
cutting it into two quadrilaterals by two cross-cuts. **Theorem F** (`Moore.m19_theoremF_proof`)
gives an exhaustion of the space by nested closed curves J₀, J₁, … whose interiors cover it.

**Main theorem** (`Moore.m19_plane`, `Moore.m19_plane_exhaust`). A space satisfying Axioms 1–8 is
homeomorphic to ℝ². *Proof:* paste the square of J₀ and the collars between consecutive Jₙ onto
the squares [−(n+1), n+1]² (`Sq.plane_of_collars`).

## 7. Decompositions of the plane into non-separating continua (Moore 1925)

**Standing hypothesis** (`Moore.MooreDecomp`). G is a u.s.c. decomposition of ℝ² into compact
connected sets, none of which separates the plane. A closed quotient map gives Moore's u.s.c. in
distance form (`Moore.usc_of_isClosedMap`).

**7.1 Arcs and closed curves of elements.** In the quotient space G, Moore's simple continuous arcs
and simple closed curves of elements are the topological arcs and circles (`Moore.isArcElt_iff_tarc`,
`Moore.isSCCElt_iff_tscc`; via cut-point arcs, `Moore.IsCutArc.exists_embedding`). Theorem 2
(`Moore.m25_theorem2`) describes the outer boundary of a bounded complementary domain, and
Theorems 4 and 6 (`Moore.m25_theorem4`, `Moore.m25_theorem6`) treat limit elements and subarcs.
Theorem 9 (`Moore.m25_theorem9`): the complement of an arc of elements is connected. Theorem 10
(`Moore.m25_theorem10`): two points split a closed curve of elements into two arcs.

**7.2 Mullikin's theorem** (corrected form, `Moore.mullikin_theorem5`). If M₁, M₂ are non-separating
plane continua and M₁ ∩ M₂ is the union of two disjoint closed connected sets, then the complement of
M₁ ∪ M₂ has exactly two components. *Proof:* at least two (`Moore.not_isConnected_compl_union`):
the function equal to 1 on M₁ and to exp(2πiφ) on M₂, with φ an Urysohn function separating the two
pieces, has no logarithm on M₁ ∪ M₂, whereas Borsuk would give one if the complement were connected.
At most two (`Moore.compl_union_two_components`): Eilenberg's bound for two pieces.

**7.3 Theorem 11** (`Moore.m25_theorem11`). A simple closed curve J of elements has exactly two
complementary domains, and J is the boundary of each (`Moore.frontier_eq_of_scc`). *Proof:* split J
into two arcs (Theorem 10), each with connected complement (Theorem 9); apply Mullikin's theorem to
the two point sets.

**The Jordan curve theorem** (`Jones.jordan_curve_theorem`). A simple closed curve in ℝ² has two
complementary components, one bounded and one unbounded, and is the frontier of each. *Proof:*
Theorem 11 for the decomposition into points.

**7.4 Theorems 19, 21, 22.** About every point of a region there is a simple closed curve of
elements whose interior lies in the region (`Moore.m25_theorem19`). With the interiors of such
curves as restricted regions, the space of elements satisfies Axioms 1–8 (Theorem 21,
`Moore.m25_theorem21`; Axioms 6 and 7 are proved directly, e.g. `Moore.m25r_axiom6`).

**Moore's theorem** (Theorem 22, `Moore.m25_theorem22`). Under the standing hypothesis, the space of
elements is homeomorphic to ℝ². *Proof:* Theorem 21 and §6.

**Corollary used three times** (`Hagopian.exists_plane_quotient_of_monotone`). Let q : M → Y be a
monotone map of a plane continuum onto a compact metric space whose fibres do not separate the
plane. Then Y is homeomorphic to a compact plane set. *Proof:* decompose the plane into the fibres
of q and the points off M. This is u.s.c. by compactness alone, and Theorem 22 applies. The same
construction is used by Jones 1955 (§19) and by Hagopian (§13).

## 8. Further plane tools

**8.1 Arcs in the plane** (Hagopian 1976, IV). The cross-cut theorem (`Hagopian.plane_split`) and
the Schoenflies theorem with one side prescribed (`Hagopian.plane_schoenflies_aux`,
`Moore.m19_schoenflies_boundary_proof`) are obtained by transporting Moore 1919 to ℝ². Every arc
in the plane has a two-sided collar (`Hagopian.exists_collar`), glued from a Schoenflies half-collar
and one obtained by inversion.

**8.2 Bing 1951, Theorem 6** (`Plane.theorem6_1951`). A bounded plane continuum none of whose
subcontinua separates the plane is tree-like (`Plane.IsTreeLike`: covered for every ε by a tree chain
of bounded links of diameter < ε). *Proof:* Bing's Theorem 7 (`Plane.theorem7_1951_rel`): such a
continuum is covered by tree chains whose links are interiors of small simple closed polygons. The
polygons come from enclosing polygons (§5.3) and a notched grid. The tree property comes from the
polygonal Jordan and Janiszewski theorems.

**8.3 Simple closed curves.** Two arcs glued along their ends form a circle (`Jones.glue_circle`),
and a topological simple closed curve is homeomorphic to `Circle` (`Jones.tscc_homeomorph_circle`).

---

# Part III. The pseudo-arc

## 9. Bing 1948: descriptions, hereditary indecomposability, uniqueness

**9.1 Descriptions** (`Description`). A description of a continuum from P to Q is a sequence of
chains D₀, D₁, … such that

1. each Dᵢ goes from P to Q: P lies in the first link only and Q in the last link only (`Chain.IsFrom`);
2. D_{i+1} is crooked in Dᵢ (§2.2);
3. the closure of each link of D_{i+1} lies in a link of Dᵢ;
4. the links of Dᵢ are bounded, of diameter ≤ εᵢ, with εᵢ → 0.

The described set is M = ⋂ᵢ ⋃ Dᵢ (`Description.M`). If all links lie in a fixed compact set, M is
a continuum (`Description.isContinuum_M_of`), and every link of every level meets M
(`Description.link_inter_M_nonempty`).

**9.2 Bing's Theorem 10: described continua are HI** (`Description.theorem10`). *Proof*
(`Description.theorem10_core`): suppose a subcontinuum K = A ∪ B with A, B proper subcontinua. Take
p ∈ K ∖ A and q ∈ K ∖ B, and go to a level D fine enough that p and q lie in links D_h and D_k with
k > h + 2, where D_{h+1} misses A and D_{k−1} misses B. A finer level E is crooked in D, and K is
connected inside ⋃E. Crookedness forces a passage of E from D_h to D_k that returns to D_{h+1} after
reaching D_{k−1}. Following this passage inside A or B (`Chain.inter_link_nonempty_between`) gives a
contradiction.

Hence: **if P ≠ Q and the links lie in a compact set, M is a pseudo-arc**
(`Plane.isPseudoArc_of_description`).

**9.3 Bing's Theorem 4** (`Fold.theorem4_pair`). Let E be crooked in a chain D of k ≥ 3 links, and
consider a stretch of E from link r to link s that meets the first and the last link of D. Then the
stretch can be consolidated by a block map into a chain each of whose links lies in the union of three
consecutive links of D, with the end blocks at the ends. *Proof:* a greedy zig-zag reading of the
index walk of E in D (`Fold.Z77.main_up` and its companions); crookedness, read in both directions,
guarantees that no phase of the zig-zag gets stuck. Applied to a subchain from R to S, this gives
`Chain.exists_blockChain`.

**9.4 Bing's Theorem 6: pattern following** (`Description.PatternFollowing`,
`Description.patternFollowing`, `Description.theorem6Pos_shift`, `Description.theorem6Pos_of_ne`).
Let Δ be a description from P ≠ Q of a compact space. For every level i and every pattern x in Dᵢ (a
walk with steps of size ≤ 1 from the first link to the last), some deeper level Dⱼ has a
consolidation E from P to Q that follows x in Dᵢ. *Proof:* the combinatorial core
(`PatCore.realize`). If a fine reading σ is crooked and a coarse reading τ is slow enough relative to
the length N of the pattern, then σ can be lifted along x by a map that moves by at most one step.
The geometric input is "thick readings" (`Description.eventually_thick`): at deep enough levels,
every window of w consecutive links lies in a single link of D₀.

**9.5 Bing's Theorem 11: matching covers** (`MatchingCovers`, `MatchingCovers.exists_homeomorph`).
Let M₁, M₂ be compact, and suppose that for each level i there are finite open covers of M₁ and M₂
indexed by the same set, with elements meeting the spaces and of diameter ≤ εᵢ, where Σεᵢ < ∞.
Suppose also the matching condition: if the j-th element of level i + 1 meets the k-th element of
level i on one side, the corresponding elements on the other side come within εᵢ. Then there is a
homeomorphism T : M₁ → M₂ such that T(p) = q whenever one index sequence tracks both p and q.
*Proof:* T(p) is the limit point of the nested fattened elements along a tracking sequence of p.
The nesting lemma (`closure_fat_subset_fat`) makes T well defined. T is continuous, surjective and
injective (`MatchingCovers.continuous_toMap`, `MatchingCovers.surjective_toMap`,
`MatchingCovers.injective_toMap`), hence a homeomorphism of compacta.

**9.6 Bing's Theorem 12** (`theorem12`, `Description.exists_homeomorph`). If Δ₁, Δ₂ describe compact
spaces from P₁ ≠ Q₁ and from P₂ ≠ Q₂, there is a homeomorphism Δ₁.M → Δ₂.M taking P₁ to P₂ and Q₁
to Q₂. *Proof:* build a ladder of "rungs" (`Rung`, `Rung.exists_next`). At each step, the side that
can follow patterns follows the pattern that the other side's new level traces in its old one
(Theorem 6; consolidations from P to Q of any length exist by `Chain.exists_consolidation_isFrom`). The two
new chains then follow the same pattern in the two old chains, so the matching condition holds
(`Chain.pattern_matching`). Theorem 11 gives the homeomorphism. The end links track P₁, P₂ and Q₁, Q₂.

## 10. A pseudo-arc in the plane

**Theorem** (`Plane.isPseudoArc_plane`, `Plane.exists_description_plane`). There is a description
in ℝ² with P ≠ Q and all links in a compact set, so the plane contains a pseudo-arc.

*Construction* (`Plane.planeDescription`, `Plane.exists_description_plane'`). Use *tame chains*:
images of standard chains of rectangles under homeomorphisms of the plane (`Plane.tameChain`). The
*planar step* (`Plane.real_step`, via `Plane.std_step`) says the following. Let x be a pattern with
unit steps that is slow, meaning it stays a long time near each value (`Plane.Joints.UnitSteps`,
`Plane.Joints.Slow`). Then x is realized by a tame chain whose link closures lie in the prescribed
links of the given tame chain, which is *tight* (a link meets only links named by x at nearby
positions), and whose links are small or lie in old zones. The patterns used are stuttered copies
of Bing's crooked pattern `Fold.bingF`, which is crooked (`Fold.bingF_crooked`, by induction on its
recursive three-part definition). Tightness transfers crookedness of the pattern to crookedness of
the chains. The two end boxes shrink to points P ≠ Q.

## 11. Bing 1951: uniqueness and homogeneity of the pseudo-arc

**11.1 Crookedness is automatic in HI chainable continua** (`Plane.PA51.eventually_crookedIn`). In a
compact HI space, chains refining a covering chain C with mesh → 0 are eventually crooked in C.
*Proof:* a failure of crookedness at a fixed pair of links (h, k), repeated along a sequence,
yields in the limit (`T13.isPreconnected_limSup`) a decomposable subcontinuum
(`Plane.PA51.limit_false`).

Iterating (`Plane.PA51.exists_crooked_next`, `Plane.PA51.exists_preDesc`), a compact chainable HI
space carries a sequence of covering chains, each crooked in the previous one, with nested closures
and mesh → 0.

**11.2 Descriptions of a given pseudo-arc** (`Plane.PA51.exists_description_univ`,
`Plane.PA51.exists_description_sub`). If M is a pseudo-arc and p, q ∈ M lie in different composants,
M has a description from p to q describing all of M. *Proof:* at each step
(`Plane.PA51.PreDesc.exists_step`), take a deep level of the sequence of 11.1 and its subchain from p
to q. That subchain meets the first and the last link of the current level; otherwise a limit of
such subchains would be a proper subcontinuum containing p and q (the limit step, via
`T13.isPreconnected_limSup`), against the choice of p and q. Theorem 4 (`Chain.exists_blockChain`)
then consolidates it into a chain from p to q whose links are small and have closures inside the
current links.

**11.3 Bing 1951, Theorem 1** (`Plane.theorem1_HIC`, `Plane.theorem1_HIC'`). Let M, M′ be pseudo-arcs,
p, q ∈ M in different composants, and p′, q′ ∈ M′ in different composants. Then some homeomorphism
M → M′ sends p to p′ and q to q′. In particular **any two pseudo-arcs are homeomorphic**.
*Proof:* 11.2 gives descriptions; Theorem 12 (9.6) gives the homeomorphism. Points in different
composants exist by §1.5 (`Plane.exists_not_mem_composant`).

**11.4 Homogeneity** (`Plane.homogeneous_of_isPseudoArc`, `HO16.ho16_pseudoArc_indec_homogeneous`).
A pseudo-arc is homogeneous (and indecomposable). *Proof:* given x, z, choose r outside the
composant of x and s outside the composant of z, and apply 11.3 with (p, q, p′, q′) = (x, r, z, s).

---

# Part IV. The indecomposable case

**Goal** (`HO16.isPseudoArc_of_indec_homogeneous`, `HO16.ho16_indec_homogeneous_iff`). A
nondegenerate indecomposable homogeneous plane continuum is a pseudo-arc. Conversely, a pseudo-arc is
homogeneous and indecomposable (§11.4).

Throughout this part, M is a nondegenerate indecomposable homogeneous plane continuum.

## 12. First consequences of homogeneity in the plane (Hagopian 1975, 1976)

**12.1 Hagopian 1975, Lemma 1** (`Hagopian.hagopian75_lemma1`). M is atriodic and hereditarily
unicoherent.

* *Atriodic* (`Hagopian.atriodic_of_homogeneous_indecomposable`). If M contained a triod, then by
  homogeneity every composant would contain one. The composants are uncountably many and pairwise
  disjoint (§1.5), so the plane would contain uncountably many disjoint triods. This contradicts
  **Moore's triod theorem** (Moore 1962, Theorem 84; `Hagopian.MooreTriodStatement`,
  `Hagopian.moore_triod_theorem'`): every family of pairwise disjoint triods in the plane is
  countable. That theorem is proved through Moore's Theorem 73 for separating cores
  (`Hagopian.countable_of_separating`) and Theorems 76, 78, 79 for non-separating cores
  (`Hagopian.countable_of_nonseparating`), with an interlacing lemma proved from Janiszewski's
  theorem (`Hagopian.interlace`).
* *Hereditarily unicoherent* (`Hagopian.hereditarilyUnicoherent_of_homogeneous_indecomposable`,
  `Hagopian.hagopian75_lemma1_hu`). If H ∪ K is a subcontinuum with H ∩ K not connected, then H ∪ K
  separates the plane (Borsuk, §5.2). Copies of this configuration in uncountably many composants
  would give uncountably many disjoint complementary domains meeting M, which is impossible in the
  separable plane (`Hagopian.disjoint_components_missing`). A single proper subcontinuum with two
  complementary domains meeting M also contradicts the density of composants.

**12.2 No proper subcontinuum of M separates the plane** (`Hagopian.no_proper_subcontinuum_separates`).
*Proof:* the 1975 argument with one step supplied. The homeomorphic copies h[K] of a separating K in
the uncountably many composants each contain a separating subcontinuum
(`Hagopian.exists_separating_subcontinuum_of_homeomorph`, §5.2, which uses Bing's Theorem 6, §8.2).
This replaces Borsuk's invariance theorem. The rest is as in 12.1.

**12.3 Effros neighbourhoods** (Hagopian 1975 Lemma 4, 1976 Lemma 2, 1984 Lemma 1;
`Hagopian.hagopian75_lemma4`, `Hagopian.hagopian76_lemma2`, `Hagopian.hagopian84_lemma1`). For
ε > 0 and x ∈ M, the set W(x, ε) of images of x under homeomorphisms moving points less than ε is
open. *Proof:* Effros (§3.3).

## 13. Type λ continua and Hagopian's decomposition (Hagopian 1975, 1976, 1984)

This section proves: **if M is not HI, then M has a monotone decomposition whose quotient is a
homogeneous continuum containing an arc** (`Hagopian.hagopian84_decomp : Hagopian.Hagopian84Decomp`).

**13.1 Type λ (type A′) continua.** A continuum E is of *type λ* if it is irreducible between two
points and has an *admissible* map k : E → [0, 1] (continuous, onto, with connected fibres, the
*layers*) all of whose layers have empty interior in E (`Hagopian.IsTypeA'`,
`Hagopian.IsAdmissibleMap`, `Hagopian.IsMinimalAdmissible`, `Hagopian.layer`). The end sets are
k⁻¹(0) and k⁻¹(1). The facts used come from Kuratowski §48 VII:

* sufficiency: an irreducible continuum all of whose indecomposable subcontinua have empty interior
  is of type λ (`Hagopian.exists_typeA'_map`, `Hagopian.isTypeA'_of_decomposable`; built from
  Kuratowski's subcontinuum lemma and "no jumps", `Hagopian.isDElt_closure_interior`,
  `Hagopian.IsDElt.exists_between`, `Hagopian.irr_compl_continuum`);
* uniqueness of the decomposition (`Hagopian.hagopian75_lemma3_unique`, `Hagopian.fibre_subset_fibre`);
* the interval lemma: a subcontinuum meeting two layers is a union of layers over an interval
  (`Hagopian.layer_subset_of_meets'`), and a subcontinuum meeting both end sets is E
  (`Hagopian.end_sets_aux`).

**13.2 Existence** (Hagopian 1975, Theorem 1, ¶¶1–3; `Hagopian.hagopian75_exists_typeA'`). Every
decomposable subcontinuum of M contains a type λ continuum. *Proof:* take an irreducible
decomposable subcontinuum (§1.3). By homogeneity and Effros, none of its indecomposable subcontinua
has interior in it. Then apply sufficiency (13.1).

**13.3 Hagopian 1976, Lemmas 3–6.** Fix a type λ continuum (E, k) in M.

* *Lemma 3* (`Hagopian.hagopian76_lemma3`). A homeomorphism of M that carries an interior layer of
  E onto a set meeting an interior layer U of another type λ continuum F, while avoiding the end
  sets appropriately, maps that layer exactly onto U. *Proof:* the triod argument (atriodicity) puts
  the image inside F, and the empty-interior condition does the rest.
* *Lemma 4* (`Hagopian.hagopian76_lemma4`, `Hagopian.ext_chain`, `Hagopian.hagopian76_lemma4_seq`).
  The extensions of E away from an end set (`Hagopian.IsExtensionAway`: type λ continua F ⊇ E with
  that end set as an end set) are linearly ordered by inclusion and have no maximal element. The
  step that Hagopian leaves unargued, "no maximal element", is supplied.
* *Lemma 5* (`Hagopian.hagopian76_lemma5`). The decomposition of E into layers is continuous.
  *Proof:* lower semicontinuity at interior layers by Lemma 3; at the end sets, pass to an extension
  in which they are interior layers.
* *Lemma 6, first part* (`Hagopian.hagopian76_lemma6_X`). The closure of the union of the
  extensions of E away from an end set is indecomposable.

**13.4 Hagopian 1984 (with N = M).**

* *Lemma 6* (`Hagopian.hagopian84_lemma6`). An essential subcontinuum H of E (one meeting two layers)
  is a union of layers over an interval, is of type λ, and its layers are layers of E.
* *Lemma 7* (`Hagopian.hagopian84_lemma7_aux`), proved by a different route from the printed one.
  Atriodicity excludes a third arm at an interior layer (`Hagopian.no_arm_at_interior_layer`), and
  common layers of two type λ continua agree (`Hagopian.layers_agree`).
* *Lemma 11* (`Hagopian.hagopian84_lemma11`). It is 13.3 Lemma 6 in this setting.
* *Lemmas 12–13* (`Hagopian.hagopian84_lemma12`, `Hagopian.hagopian84_lemma13`). E "runs straight"
  through a free, normal, regular chain of five open sets P₁, …, P₅ of M with Cl(P₁ ∪ P₅) inside a
  given neighbourhood of the end sets. The closure of each component of the middle part is an
  essential subcontinuum of an ε-translate h[E]. *Proof:* links W(k⁻¹[x_{3i}, x_{3i+3}], δ) (12.3),
  a fold-free sweep of the parameter sets (`Hagopian.exists_fold`), and Moore's Theorem 44 (§1.2)
  for the refinement.
* *Lemmas 14–16′* (`Hagopian.hagopian84_lemma14`, `Hagopian.hagopian84_lemma15`,
  `Hagopian.strand_layer_of_extension`). The decomposition Δ(𝒫) of the middle part into layers of
  the strands is continuous (Lemma 14, through Lemma 3). Small homeomorphisms carry members of Δ(𝒫)
  onto members (Lemma 15). End layers of strands are members (Lemma 16′).
* *The decomposition* (`Hagopian.CoverData84`, `Hagopian.exists_coverData84`,
  `Hagopian.hagopian84_cover`, `Hagopian.exists_finite_cover84`). Finitely many chains 𝒫(Z) cover
  the rest of M; the members of their decompositions together with Δ(𝒫) form a partition 𝔇.
* *The package* (`Hagopian.IsJonesDecomp84`, `Hagopian.CoverData84.isJonesDecomp`). 𝔇 is u.s.c.
  (Lemma 14), its classes are connected and proper, it is respected by every δ-homeomorphism for
  some δ > 0 (Lemma 15), and it has an arc of classes (`Hagopian.exists_interval_in_delta`).
* *Quotient* (`Hagopian.hagopian84Decomp_of_package`). M/𝔇 is compact metrizable (§4). It is
  homogeneous: compositions of δ-homeomorphisms respect 𝔇, their orbits are clopen by 12.3, hence
  there is one orbit, and homeomorphisms descend (§4). It contains an arc, the image of the arc of
  classes. So `Hagopian.Hagopian84Decomp` holds.

## 14. No arc (Bing 1960; Jones 1975)

**Theorem** (`Hagopian.jones75_noArc : Hagopian.NoArcIndecHomPlane`). No indecomposable homogeneous
plane continuum contains an arc.

*Setting* (`Hagopian.JonesSetting`, `Hagopian.jonesSetting_of_plane`). A compact metric space Y that
is homogeneous, hereditarily unicoherent and atriodic and contains an arc. An indecomposable
homogeneous plane continuum with an arc is such a Y, by 12.1.

*Structure of arcs in the setting* (Jones (a)–(d), corrected). Two arcs with a common end point are
nested or their union is an arc (`Hagopian.JonesSetting.union_arc`, `Hagopian.JonesSetting.nested`).
Every point is interior to an arc (`Hagopian.JonesSetting.exists_arc_through`). Every arc component
is a *line*, a continuous injective image of ℝ (`Hagopian.IsLine`,
`Hagopian.JonesSetting.exists_line`, `Hagopian.JonesSetting.line_arc`,
`Hagopian.JonesSetting.homeo_on_line`). Jones's defective step (f) is replaced by two properties
(`Hagopian.JonesSetting.no_reversal_arc`, `Hagopian.JonesSetting.exists_no_reversal`,
`Hagopian.JonesSetting.local_no_reversal`, `Hagopian.JonesSetting.orientation`):

* (R) a small homeomorphism fixing a point does not reverse the line through it;
* (O) a small homeomorphism carrying a point of a line into that line is increasing on it.

*Recurrence* replaces the second half of Jones's (d) (`Hagopian.JonesSetting.line_recurrent`,
`Hagopian.JonesSetting.omegaLim_saturated`): every line lies in its own forward limit set. *Proof:*
Effros.

*The planar core* (`Hagopian.jones75_contra`). An arc ℓ[0, 1] of a line has a two-sided collar
(`Hagopian.exists_collar`, §8.1). In the collar coordinates, the returns of the line form *passes*
(`Hagopian.IsPass`). Three tools control them:

* the shadow lemma (`Hagopian.shadow_pass`, by Effros and (O));
* the flow box in the middle band (`Hagopian.flow_box`);
* late thin passes (`Hagopian.scale_two`, `Hagopian.exists_late_thin_pass`, from recurrence).

Take the first thin pass after ¾, above or below the base arc. The region under it
(`Hagopian.region_lemmaA`) and a Jordan curve formed by a cross-cut and a piece of the line
(`Hagopian.trap_jordan`, `Hagopian.two_sides`, with the Jordan curve theorem of §7.3) trap the line:
no later pass enters the low strip (`Hagopian.trap_pass`). Recurrence brings the line back near the
base point on both sides, which gives a contradiction (`Hagopian.jones75_final_aux`). This route
replaces Jones's accessibility assumption, his choice of η and his final limit argument.

## 15. Hereditary indecomposability (Hagopian 1976, Theorem 1)

**Theorem** (`Hagopian.hagopian76_theorem1 : Hagopian.Hagopian76Thm1`). Every indecomposable
homogeneous plane continuum is hereditarily indecomposable.

*Proof* (Hagopian 1984, Corollary 3, by Jones's plan; `Hagopian.hagopian76_theorem1_of_jones`,
`Hagopian.hagopian76_theorem1_jones`). Suppose M has a decomposable subcontinuum, and let
q : M → Y be the decomposition of §13. Its fibres are proper subcontinua of M, so they do not
separate the plane (12.2). By Moore's theorem (§7.4,
`Hagopian.exists_plane_quotient_of_monotone`), Y is homeomorphic to a compact plane set Q. Q is
connected, homogeneous and indecomposable (a monotone image of an indecomposable continuum,
`Hagopian.indecomposable_of_monotone_image`), and it contains an arc. This contradicts §14.

## 16. Span zero (Theorem C; Oversteegen–Tymchatyn 1982)

**Definitions** (`Span.HOSpanZero`, `Span.SemiSpanZero`, `Span.SurjSpanPos`, `Span.SurjSemiSpanPos`).
X has *span zero* (in Hoehn–Oversteegen's sense) if every subcontinuum Z ⊆ X × X with π₁(Z) ⊆ π₂(Z)
meets the diagonal. A set A has *positive surjective span* if some continuum Z ⊆ A × A off the
diagonal has both projections onto A, and *positive surjective semi-span* if the first projection
is onto A. O–T's semi-span zero is H–O's span zero (`Span.semiSpanZero_iff_hoSpanZero`).

**Theorem C** (`Span.theoremC : Span.TheoremC`). Every homogeneous indecomposable plane continuum has
span zero.

The proof runs Theorem 3.2 ⇒ Corollary 3.5 ⇒ Theorem 3.6 ⇒ Theorem C (`Span.theoremC_of_thm32`).

**16.1 Two general tools.**

* **Cook 1967, Theorem 4** (`Span.cook67_theorem4`). A map of a continuum onto an HI continuum is
  confluent: every subcontinuum Q of the image is the image of a component of its preimage. *Proof:*
  boundary bumping in one closed neighbourhood of the component.
* **Davis's Theorem 1.1 for HI continua** (`Span.exists_surjSpanPos_of_surjSemiSpanPos`). In an HI
  continuum, positive surjective semi-span of A gives a subcontinuum B ⊆ A of positive surjective
  span. *Proof:* Brouwer reduction (§1.3) and Cook's theorem.

**16.2 Theorem 3.6 from Corollary 3.5** (`Span.ot82_theorem36_of_cor35`, `Span.theoremC_of_cor35`,
`Span.not_surjSemiSpanPos_univ`). Assume (Corollary 3.5, `Span.OTCor35`) that every proper
subcontinuum of M has zero surjective semi-span. Then M has semi-span zero. *Proof:*

1. M is HI (§15). Suppose Z ⊆ M × M is a continuum off the diagonal with π₁(Z) = M, and let 3ε be
   the minimum distance on Z.
2. Reduce (`Span.exists_reduced_witness`, Brouwer reduction): either π₂(Z) ≠ M, or no proper
   subcontinuum of Z maps onto M under π₂.
3. Effros gives δ for ε.
4. Some proper subcontinuum K of M is δ-dense (`Span.exists_dense_proper_subcontinuum`: proper
   subcontinua through a point are directed by union and have dense union).
5. By Cook, K = π₁(C) for a subcontinuum C ⊊ Z.
6. Pick y ∈ π₂(C) and x ∈ K with d(x, y) < δ, and let h be the Effros homeomorphism with h(x) = y.
7. h(K) and π₂(C) are proper subcontinua that meet, so they are nested (HI).
8. {(h(π₁c), π₂c) : c ∈ C} (or its swap) witnesses positive surjective semi-span of the larger of
   the two. This contradicts Corollary 3.5.

**16.3 Corollary 3.5 from Theorem 3.2** (`Span.ot82_cor35_of_thm32`, `Span.cor35_core`).
Let A₀ ⊊ M have positive surjective semi-span.

1. By Davis, some A₁ ⊆ A₀ has positive surjective span (`Span.SurjSpanPos.image` carries this
   along embeddings).
2. Re-embed M so that it lies in {x ≥ 0} with a unique point x₀ on x = 0
   (`Span.exists_homeomorph_unique_leftmost`).
3. Move A₁ by homogeneity to a continuum A ∋ x₀. A does not separate the plane (12.2), so
   {x > 0} ∖ A is connected (`Span.isConnected_rightHalf_diff`, by Janiszewski). A finger move
   (`Span.exists_homeomorph_push`) then puts a point q of M to the right of A.
4. Effros gives δ. Indecomposability gives an uncountable family 𝒦 of disjoint subcontinua
   crossing a thin strip near x = 0 (`Span.exists_crossing_subcontinuum`,
   `Span.exists_uncountable_crossing`, by the cut-wire theorem and the uncountably many
   composants).
5. For each K ∈ 𝒦, an Effros homeomorphism h_K moves x₀ into K, and hereditary indecomposability
   gives h_K(A) ⊆ K.
6. The continua h_K⁻¹(K) are nested; their intersection gives one continuum B ⊇ A with a point y
   whose images lie beyond all of h_K(A).
7. Uncountably many disjoint crossing continua then carry copies h_K(A) of positive surjective
   span. This contradicts Theorem 3.2.

**16.4 Theorem 3.2, strip form** (`Span.OTThm32`, `Span.ot82_theorem32`). Let h_λ (λ ∈ Λ) map a
continuum Y into the strip [0, 1] × ℝ, with images inside pairwise disjoint continua crossing the
strip, h_λ(x) on the left line, and a point y beyond X ⊆ Y. Then only countably many h_λ(X) have
positive surjective span. *Proof* (a route that needs no Jordan curve theorem):

* *Parity* of closed polygons (`Span.parity_eq_zero_of_not_mem_convex`,
  `Span.parity_eq_of_perturb`). The parity vanishes off a convex set containing the polygon and is
  stable under small vertex moves.
* *Common zeros* (`Span.common_zero_rect`). Two functions on a rectangle with O–T's sign pattern
  have a common zero, by a winding count.
* *The strip lemma* (`Span.strip_lemma`, with `Span.plPath`, `Span.plPath_piece`, `Span.stripPoly`,
  `Span.StripInner`, `Span.stripSign`). A continuum W in a thin strip between two PL paths, with a
  span witness Z ⊆ W × W, has a pair (h(u), k(u)) on a common short segment B_t. Hence its
  surjective span is at most the strip width.
* *Ordering* (`Span.crossing_traces_separated`). Disjoint continua crossing a strip have strictly
  ordered traces on its left side.
* *Counting.* If uncountably many images had positive surjective span, one bound would serve
  uncountably many of them. Separability clusters three of them; ordering puts one between the
  other two; the strip lemma bounds its span; contradiction.

## 17. Snake-likeness: Hoehn–Oversteegen 2016, Theorem 1

**Theorem** (`HO16.ho16_theorem1_plane`, with `HO16.ho16_theorem20 : HO16.HOThm20`). A hereditarily
indecomposable plane continuum X with span zero is snake-like.

Hence §15 + §16 + §17 give `HO16.isPseudoArc_of_indec_homogeneous`, and with §11.4,
`HO16.ho16_indec_homogeneous_iff`.

**17.1 The proof of Theorem 1, given Theorem 20.** Given ε > 0:

1. **Theorem 4** (`HO16.ho16_theorem4`). For X compact with span zero there is δ > 0 with the
   following property. For every compact G ⊆ B_δ(X) and every path γ on [0, 1] that is δ-close to X
   in both directions, the set {(x, t) ∈ G × (0, 1) : d(x, γ(t)) < ε/6} separates G × {0} from
   G × {1}. *Proof:* otherwise the cut-wire theorem (§1.2) gives continua in {d ≥ ε/6} joining the
   two ends. Their Hausdorff limit as δ → 0 is a continuum Z ⊆ X × X off the diagonal with
   π₁(Z) ⊆ π₂(Z) = X, against span zero.
2. **A graph and a map** (`HO16.exists_plGraph_approx`). An HI plane continuum has empty interior
   (`HO16.interior_eq_empty_of_hi`). Radial projection in the squares of a fine grid maps X into a
   PL graph G ⊆ B_δ(X) by a map f with d(f(x), x) < δ.
3. **A path** (`HO16.exists_path_approx`): a polygonal path through a fine chain of points of X.
4. **Theorem 20** gives h : X → U ∩ (G × [0, 1]) with d(f(x), π(h(x))) < ε/6.
5. The t-coordinate of h is an ε-map onto [0, 1], so X is snake-like (§2.3).

**17.2 PL graphs and folds** (`HO16.IsPLGraph`). PL graphs are finite unions of segments. They have
common subdivisions and refinements (`HO16.Subdiv.exists_common_subdivision`,
`HO16.IsPLGraph.exists_refinement`). A *simple fold* of G along a triple G₁, G₂, G₃
(`HO16.IsFoldTriple`, `HO16.IsSimpleFoldOf`) is a PL graph F = F₁ ∪ F₂ ∪ F₃ in G × ℝ. Each Fᵢ projects
injectively onto Gᵢ, and the sheets are glued over the relative frontiers of G₁ and G₃. Folds exist
for every triple (`HO16.exists_simpleFold`). Lemma 6 (`HO16.ho16_lemma6`) and Proposition 7
(`HO16.ho16_prop7`: a component of the fold maps onto G) are proved as in H–O.

**17.3 Theorem 8: maps lift to folds** (`HO16.ho16_theorem8_core`, `HO16.ho16_theorem8`). A map
f : X → G of an HI compactum is ε-approximated by φ ∘ g with g : X → F. *Proof:* the
Krasinkiewicz–Minc lemma for HI compacta (`HO16.km77_lemma2`). Disjoint closed A ⊆ U and B ⊆ V
admit a closed cover X₁ ∪ X₂ ∪ X₃ with A ⊆ X₁, B ⊆ X₃, X₁ ∩ X₃ = ∅, X₁ ∩ X₂ ⊆ V and X₂ ∩ X₃ ⊆ U.
On each piece, push f towards the fan vertices by an explicit Urysohn interpolation, then lift
through the inverse of φ on each sheet.

**17.4 Stairwells** (`HO16.IsStairwellStr`, `HO16.IsBrokenStairwellStr`, `HO16.IsStraight`,
`HO16.HasConsCompl`, `HO16.sideOf`, `HO16.IsGeneric`). A stairwell structure of height k is a sequence
of straight sheets S₁, …, S_k over G, with end sets satisfying H–O's conditions (S1)–(S5):
sides, consistent complements, and generic end points over ordinary points. The workhorse for
sides is `HO16.IsPLGraph.sideOf_char_aux`. The proof chain is:

* Proposition 17 (`HO16.ho16_prop17`) lowers the height by two at the cost of a pit;
* the remarks of p. 201 (`HO16.ho16_rem17_gamma`, `HO16.ho16_rem17_P1`) handle degenerate pits;
* Lemma 18 (`HO16.ho16_lemma18`) pulls straight sets back to a fold;
* Proposition 19 (`HO16.ho16_prop19 : HO16.HOProp19`) turns a broken structure over G into a
  stairwell structure over a connected fold. Ordinary points of folds are characterized by
  `HO16.IsSimpleFoldOf.isOrdinaryPt_iff`. One false sentence of H–O (p. 208) is replaced by a case
  split.

**17.5 Theorem 20 from Theorem 15** (`HO16.ho16_lift_aux`, `HO16.ho16_theorem20_of_thm15`). Use strong
induction on (k + 1)² (plus the pit position), quantified over the ambient space E ↦ E × ℝ. At
height 1, the sheet is a section (`HO16.ho16_height_one`). Otherwise apply Proposition 17, then
Proposition 19, then Theorem 8 on the fold, and then the induction hypothesis. Theorem 20 for a
disconnected G is reduced to components.

**17.6 Theorem 15** (`HO16.ho16_theorem15 : HO16.HOThm15`). For every M ⊆ G × (0, 1) separating
G × {0} from G × {1}, and every open U ⊇ M, some S ⊆ U has a stairwell structure of odd height.
*Proof by ladders* (`HO16.IsLadder`, `HO16.exists_ladder`, `HO16.ho16_stairwell_of_ladder`). A
Lipschitz sign function (`HO16.exists_sign_fn`) is positive near the top and non-positive near the
bottom, and changes sign only inside U. On a fine subdivision of G, the midpoints of the sign changes
along each vertical give lists of odd length. Along edges these lists change by moving one curve, or
by creating or removing two curves at a wedge. The resulting sheets satisfy (S1)–(S5); the parity
argument for (S4) is `HO16.ladder_S4`.

---

# Part V. The decomposable case

**Goal** (`BJ59.circle_or_atomic_of_decomposable`). Let M be a decomposable homogeneous plane
continuum. Then M is a simple closed curve, or there is a continuous, open, surjective map
f : M → S¹ whose fibres are pseudo-arcs and which is *atomic*: every subcontinuum that meets a
fibre either lies in that fibre or contains it (`BJ59.IsAtomicMap`, `BJ59.IsAtomicCircPAMap`).

The map is the quotient map of Jones's aposyndetic decomposition (Jones 1955). Its quotient is a
circle by Jones 1949, and its elements are pseudo-arcs by Part IV.

## 18. Aposyndesis

**Definition** (`Jones.AposAt`). X is *aposyndetic at x with respect to y* if some continuum
H ⊆ X ∖ {y} contains a neighbourhood of x. X is *aposyndetic* (`Jones.IsAposyndetic`) if this holds
for all x ≠ y. Write U_x = {z ≠ x : X is aposyndetic at z with respect to x} (`Jones.aposSet`).

**18.1 Openness** (Jones 1948, Theorem 1; `Jones.isOpen_setOf_aposAt`). The set of pairs (x, y) with
X aposyndetic at x with respect to y is open. *Proof:* the same continuum H works for all pairs
near (x, y), because H contains a neighbourhood of x and misses a neighbourhood of y.

**18.2 Jones 1948, Theorem 3** (`Jones.theorem3`). For a continuum X and y ∈ X, the set
L_y = {y} ∪ {x ≠ y : X is not aposyndetic at x with respect to y} is a continuum.
*Proof:* L_y is closed (`Jones.isClosed_not_aposAt_left`). Suppose L_y = A ∪ B with y ∈ A and A, B
disjoint, closed and nonempty. Take an open V ⊇ B whose closure misses A. The frontier of V misses
L_y, so X is aposyndetic at the points of B with respect to y (`Jones.aposAt_of_frontier`). This contradicts B ⊆ L_y.

**18.3 Jones 1948, Theorem 8** (`Jones.theorem8`). A continuum is decomposable iff it is
aposyndetic at some x with respect to some y ≠ x. *Proof:* if X = A ∪ B with A, B proper
subcontinua, take x ∈ X ∖ B and y ∈ X ∖ A; then A contains the neighbourhood X ∖ B of x and misses y.
Conversely, let H ∌ y be a continuum
containing a neighbourhood of x. If X ∖ H is connected, H and the closure of X ∖ H are two proper
subcontinua covering X. Otherwise split X ∖ H into two separated pieces A and B. Then H ∪ A and H ∪ B
are proper subcontinua covering X (`Plane.isContinuum_union_piece`).

**18.4 Jones 1941, Theorem 4** (`Jones.semiLocConn_of_isAposyndetic`). An aposyndetic continuum is
semi-locally connected (`Jones.SemiLocConnAt`): every point has arbitrarily small open
neighbourhoods whose complement has finitely many components. *Proof:* by Jones's
Theorem 0 (`Jones.theorem0`, a Heine–Borel argument), X is semi-locally connected at p iff X is
aposyndetic at every other point with respect to p.

**18.5 Spreading** (`Jones.aposAt_of_isContinuum_interior`). In a homogeneous compact metric space,
if a continuum K with nonempty interior contains o and misses x, then X is aposyndetic at o with
respect to x. *Proof:* let b be an interior point of K and choose ε smaller than the radius of a ball
around b inside K and than half the distance from x to K. Let Z be the closure of the union of the
sets K ∪ h(K), over all homeomorphisms h that move points by less than ε. Each h(b) lies in K, so Z
is a continuum. Z stays within ε of K, so it misses x. By the Effros theorem (§3.3), every point
near o is h(o) for such an h, so Z contains a neighbourhood of o.

**18.6 Jones 1951, Lemma** (`Jones.jones51_lemma`). If X is homogeneous, U_y is never a proper subset
of U_x. *Proof:* the formal proof replaces Jones's transfinite recursion. A lower semicontinuous
function that strictly increases along proper inclusions of the sets U_x
(`Jones.exists_lsc_strictMono_aposSet`) attains its minimum on the compact space. Homogeneity moves
any point to a minimizer.

## 19. Jones's aposyndetic decomposition (Jones 1955)

Throughout this section, M is a homogeneous plane continuum and L_x is as in 18.2 (`Jones.Lset`).

**19.1 Theorem 1 (b)** (`Jones.jones55_b`, `Jones.mem_Lset_iff_Lset_eq`). y ∈ L_x iff L_y = L_x. So
the sets L_x partition M (`Jones.lSetoid`; the classes are the L_x, `Jones.cls_lSetoid`).
*Proof:* by spreading (18.5) and the Lemma of Jones 1951 (18.6), not by Jones's case argument on
p. 738.

**19.2 Theorem 1 (c): elements are terminal** (`Jones.jones55_c`). A subcontinuum K that meets both
L_x and its complement contains L_x. *Proof* (`Jones.Lset_subset_of_meets`): let
a ∈ K ∩ L_x and b ∈ K ∖ L_x, and suppose y ∈ L_x ∖ K. Then L_y = L_x, so b ∉ L_y, and some continuum
B ∌ y contains a neighbourhood of b. K ∪ B is a continuum with nonempty interior that contains a and
misses y. By spreading (18.5), M is aposyndetic at a with respect to y, against a ∈ L_y. Also M ∖ L_x = U_x (`Jones.jones55_prop_e`).

**19.3 Theorem 1 (a)** (`Jones.jones55_a`). If M is decomposable, the quotient G = M/{L_x} is a
nondegenerate, homogeneous, aposyndetic, compact metric continuum.
*Proof:* the decomposition is u.s.c. and the quotient is compact metrizable (§4). Homeomorphisms of M
permute the elements (aposyndesis is topological), so G is homogeneous (`Jones.exists_homeomorph_quotient`).
G is nondegenerate by 18.3, since M is decomposable. Jones does not argue aposyndesis. The formal proof
goes as follows: for g ≠ g′ and points x ∈ g, y ∈ g′, a continuum K containing a neighbourhood of y and
missing x misses g by (c). By lower semicontinuity at g′, its image in G is a continuum missing g that
contains a neighbourhood of g′.

**19.4 G is continuous** (`Jones.jones55_continuous`). By residual continuity (§4,
`Jones.residual_lscAt`, `Jones.exists_lscAt`) the decomposition is continuous at some element.
Homeomorphisms of M permuting the elements carry continuity at one element to continuity at its image
(`Jones.lscAt_homeomorph`), and M is homogeneous.

**19.5 Each element is homogeneous** (`Jones.isHomogeneous_Lset`, `Jones.jones55_elements`). If M is
not aposyndetic, every L_x is nondegenerate, any two are homeomorphic, and each is homogeneous,
because a homeomorphism of M carrying a ∈ L_x to b ∈ L_x maps L_x onto L_b = L_x. If M is aposyndetic,
the elements are points (`Jones.Lset_eq_singleton_of_isAposyndetic`).

**19.6 Elements do not separate the plane.**

* M ∖ L_x is connected (`Jones.jones55_compl_connected`). By Jones's claim (5), two points of U_x lie
  in a continuum missing x (`Jones.exists_continuum_of_mem_aposSet`). Such a continuum misses L_x by
  (c), and M ∖ L_x = U_x.
* No element separates the plane (`Jones.jones55_elt_not_separates`). In the non-aposyndetic case the
  elements are homeomorphic, so if one separates, all do (`Jones.separatesPlane_of_homeomorph`).
  Since M ∖ g is connected, some complementary domain W_g of g misses M. For g ≠ h, the domain W_g is
  a connected subset of ℝ² ∖ h, so W_g and W_h are either disjoint or equal. If they are equal, the
  common domain is open and closed in the plane, which is absurd. So the W_g are disjoint open sets,
  and there are uncountably many of them (`Jones.uncountable_quotient`), which is impossible in the
  plane.

**19.7 G lies in a plane** (`Jones.mooreDecomp_gPrime`, `Jones.jones55_plane`,
`Jones.jones55_embedding`). Let G′ be the decomposition of ℝ² into the elements of G and the points
of ℝ² ∖ M (`Jones.gPrime`). Its quotient map is closed (`Jones.isClosedMap_mk_gPrime`), so G′ is
upper semicontinuous in Moore's sense. Its elements are continua that do not separate the plane
(19.6). By Moore 1925, Theorem 22 (§7.4, `Moore.m25_theorem22`), G′ is a plane. So G is homeomorphic
to a compact connected subset of ℝ² (`Jones.jones55_embedding_data`).

**19.8 Theorem 2** (`Jones.jones55_circle`, `Jones.jones55_theorem2'`). If M is decomposable, G is a
continuous decomposition, M/G is a simple closed curve, and each element is a homogeneous plane
continuum that does not separate the plane. *Proof:* G is a nondegenerate homogeneous aposyndetic
plane continuum (19.3, 19.7), hence a simple closed curve by Jones 1949 (§20).

**19.9 Elements are indecomposable** (`Jones.jones55_two_domains`,
`Jones.jones55_elements_indecomposable'`). A decomposable homogeneous plane continuum has exactly two
complementary domains. *Proof:* in the plane G′, the image of M is a simple closed curve (19.8). The
Jordan curve theorem (`Jones.jordan_curve_theorem`, §7.3) gives two domains of elements, and their
point sets are disjoint connected open sets with union ℝ² ∖ M. Now if an element L_x were
decomposable, it would be a decomposable homogeneous plane continuum (19.5), so it would separate the
plane, against 19.6.

## 20. Homogeneous aposyndetic plane continua are circles (Jones 1949)

**Theorem** (`Jones.jones49_theorem1 : Jones.Jones49Thm1`). A nondegenerate homogeneous aposyndetic
plane continuum M is a simple closed curve.

**20.1 Order** (`Jones.OrderLE`, `Jones.HasOrder`). p has order ≤ n if it has arbitrarily small open
neighbourhoods whose frontier has at most n points. p has order n if it has order ≤ n but not ≤ n − 1.
A *local separating point* separates some open set (`Jones.IsSepPointOf`, `Jones.IsLocalSepPoint`).

**20.2 Menger's theorem** (`Jones.menger_order_two`). A nondegenerate continuum in which every point
has order 2 is a simple closed curve. *Proof:* such a continuum is hereditarily locally connected
(`Jones.locallyConnectedSpace_of_orderLE`), so any two of its points are joined by arcs. Take a
non-cut point u (§1.4) and a small connected open V ∋ u with exactly two frontier points. A triod
argument shows that the closure of V and the complement of V are arcs. Two arcs glued along their
ends form a circle (§8.3).
With homogeneity, one point of order 2 is enough (`Jones.jones49_order_two`).

**20.3 Whyburn's separating point–order theorem** (`Jones.countable_sepPoint_not_hasOrder_two`,
`Jones.whyburn_9_1`, `Jones.whyburn_9_2`, `Jones.whyburn_3_2`). In a separable locally compact metric
space, only countably many points separate an open set R without having order 2. A separating point
of R also separates every smaller open neighbourhood (9.1). With a countable basis, only countably
many local separating points fail to have order 2 (9.2). For cut points of a continuum this is (3.2).
*Consequence* (`Jones.jones49_some_order_two`, `Jones.jones49_some_order_two_of_whyburn_9_2`): an
uncountable homogeneous continuum with a local separating point has a point of order 2, since by
homogeneity all of its points are local separating points.

**20.4 The setting** (`Jones.jones49_setting`). M is cyclic, since no point cuts M: some point does
not (§1.4), so by homogeneity none does. By 18.4, M is semi-locally connected.

**20.5 Whyburn 1939** (`Jones.whyburn39_theorem14`, `Jones.whyburn39_corollary1`). Let M be a compact
semi-locally connected plane continuum. The boundary of each complementary domain is locally
connected. If M is also cyclic, each such boundary is a simple closed curve.
*Proof of Theorem 14:* suppose the boundary B is not locally connected
(`Jones.locallyConnectedSpace_of_cikAt`). Then disjoint subcontinua of B cross an annulus. On every
circle of radius ρ in the middle third, this produces a point of B that has no finite order and cuts
M. That gives uncountably many cut points not of order 2, which contradicts 20.3.
*Proof of the Corollary:* B is a locally connected continuum without cut points. If B is not a
circle, it contains a θ-curve. All three arcs of the θ-curve lie in the closure of the complementary
domain, which is connected and misses them. This is impossible by the θ-curve lemma
(`Jones.theta_not_subset_closure`, from the Jordan curve theorem and Janiszewski's theorem). So B is a
simple closed curve (`Jones.tscc_homeomorph_circle`).

**20.6 Proof of the Theorem.** If some point has order 2, apply 20.2. Otherwise no point has order 2.
Take x ∉ M, and let J be the boundary of its complementary domain; J is a simple closed curve by 20.5.

* *Case 1: M ∖ J is connected* (`Jones.jones49_case1_core`). By homogeneity every point of M lies on
  the boundary of some complementary domain (`Jones.exists_frontier_through`, via
  `Jones.frontier_cc_of_jordan`). There are only countably many complementary domains
  (`Jones.countable_complDomains`). By Baire, one of their boundaries contains a nonempty open
  subset of M. That boundary is a simple closed curve (20.5), so a point of the open subset is a local
  separating point (`Jones.isLocalSepPoint_of_open_sub_tscc`). By 20.3 some point has order 2, a
  contradiction.
* *Case 2: M ∖ J is not connected* (`Jones.jones49_case2_core`). Choose a domain U meeting the two
  pieces (`Jones.exists_domain_meeting`). Its boundary C is a simple closed curve meeting J. An arc of
  C between two points A, B of J (`Jones.exists_theta_arcs`) completes a θ-curve. The θ-curve
  separates M ∖ {A, B} (`Jones.theta_separation`). Since M ∖ B is connected, A is a local separating
  point (`Jones.isLocalSepPoint_of_separation`). M is uncountable (`Jones.uncountable_of_nontrivial`),
  so 20.3 gives a point of order 2, a contradiction.

## 21. The decomposable case

**21.1 Elements are pseudo-arcs** (`BJ59.isPseudoArc_Lset'`). If M is decomposable and homogeneous,
every nondegenerate element L_x is a pseudo-arc. *Proof:* L_x is a homogeneous (19.5), indecomposable
(19.9) plane continuum, so it is a pseudo-arc by Part IV (`HO16.isPseudoArc_of_indec_homogeneous`).

**21.2 Proof of the Goal** (`BJ59.circle_or_atomic_of_decomposable`). Let q : M → S¹ be the quotient
map followed by the homeomorphism M/G ≅ S¹ of 19.8; its fibres are the L_x.

* If M is aposyndetic, the elements are points (19.5). Then q is a continuous bijection from a
  compact space, hence a homeomorphism, and M is a simple closed curve.
* Otherwise q is continuous and surjective. It is open because the decomposition is continuous
  (19.4, §4 `BJ59.isOpenMap_quotient_mk_of_continuous`). Its fibres are pseudo-arcs (21.1, the
  elements being nondegenerate by 19.5), and it is atomic because the elements are terminal (19.2).

**21.3 The circle-like form** (`BJ59.circle_or_circPAMap_of_decomposable`). The same proof gives
q with `BJ59.IsCircPAMap` (open, surjective, pseudo-arc fibres, with M circle-like) whenever M is
known to be circle-like. Circle-likeness is supplied in §24.4.

---

# Part VI. Circles of pseudo-arcs (Bing–Jones 1959)

**Definitions.** An *arc of continua* (`BJ59.IsArcOfContinua`) is a continuous surjection
f : X → [0, 1] whose fibres are continua. It is a *continuous arc of pseudo-arcs*
(`BJ59.IsContArcPA`) if f is also open and its fibres are pseudo-arcs. A *circle of pseudo-arcs*
(`BJ59.IsCircleOfPA`) is a circle-like continuum X with a continuous, open, surjective map
f : X → S¹ whose fibres are pseudo-arcs. Equivalently, X carries a map with `BJ59.IsCircPAMap`
(`BJ59.isCircleOfPA_iff`).

For f : X → S¹, the two *halves* `BJ59.halfSet f (±1)` are the preimages of the closed upper and
lower semicircles from 1 to −1. Each half carries the induced map `BJ59.halfMap` onto [0, 1], with
end fibres f⁻¹(1) and f⁻¹(−1) (`BJ59.halfFibreEquiv`).

## 22. Atomic maps have snake-like halves

**22.1 Bing 1951, Theorem 11 for atomic maps** (`BJ59.isSnakeLike_of_atomic'`). Let f : X → [0, 1]
be continuous and atomic, with snake-like HI fibres. Then X is snake-like.
*Proof.* X is hereditarily unicoherent (`BJ59.isHereditarilyUnicoherent_of_atomic`). A subcontinuum
lying in a fibre inherits this from the snake-like fibre (§2.3). Otherwise, in a splitting K = H ∪ L
into subcontinua, a piece lying in a fibre lies in the other piece, and pieces lying in no fibre are
unions of fibres (`BJ59.subset_fibre_or_saturated`). Their intersection is then the preimage of an
interval, which is connected (`BJ59.isPreconnected_preimage_of_fibres`). Now suppose X is not ε-coverable (`Plane.EpsCoverable`). Bing's minimal
counterexample (`Plane.exists_minimal_notCoverable`, Brouwer reduction §1.3) gives a subcontinuum S
that is not ε-coverable, while all of its proper subcontinua are. S lies in no fibre, since fibres are
snake-like. So S = f⁻¹[a, b] with a < b. Split S at c = (a + b)/2 into A = f⁻¹[a, c] and
C = f⁻¹[c, b]. These are proper subcontinua, hence ε-coverable. Fugate's Lemma 1
(`Plane.fugate_lemma1`, for the terminal subcontinuum f⁻¹(c), `Plane.IsTerminalSub`) gives ε-chains
covering A and C whose last links contain a common point μ ∈ f⁻¹(c). Fugate's gluing of the two
chains (`Plane.epsCoverable_of_halves`) covers S by an ε-chain, a contradiction.

**22.2 Halves** (`BJ59.isAtomicMap_halfMap`, `BJ59.isContArcPA_halfMap_of_atomic`,
`BJ59.isSnakeLike_halfSet_of_atomic`). If f : X → S¹ is open, atomic and has pseudo-arc fibres, each
half is a continuous arc of pseudo-arcs and is snake-like, by 22.1. If instead f has `BJ59.IsCircPAMap`, each
half is a proper subcontinuum of the circle-like X, hence snake-like by Nadler 12.51 (§2.3,
`BJ59.isSnakeLike_halfSet`, `Plane.isSnakeLike_of_subset_circleLike`). Both cases give
`BJ59.IsSnakeHalvesMap`: continuous, open, surjective, pseudo-arc fibres and snake-like halves
(`BJ59.IsAtomicCircPAMap.isSnakeHalvesMap`, `BJ59.IsCircPAMap.isSnakeHalvesMap`).

## 23. Bing–Jones Theorem 10

**Theorem** (`BJ59.bjThm10 : BJ59.BJThm10`). Let f : X → [0, 1] and g : Y → [0, 1] be continuous arcs
of pseudo-arcs with X, Y compact and snake-like. Let h₀ : f⁻¹(0) → g⁻¹(0) and h₁ : f⁻¹(1) → g⁻¹(1) be
homeomorphisms. Then there is a homeomorphism H : X → Y with g ∘ H = f that extends h₀ and h₁.

**23.1 Chains and chain maps.** A chain in Bing–Jones's sense (`BJ59.IsBJChain`) has non-adjacent
links at positive distance. A *chain map* (`BJ59.IsChainMap`) is a map of link indices that sends
adjacent links to adjacent or equal links. A chain has *private points* (`BJ59.HasPrivatePoints`) if
each link has a point outside the closures of the others. Every chain properly covering a
nondegenerate continuum can be shrunk to have them (`BJ59.exists_privatePoint_shrink`).

**23.2 The homeomorphism from a zigzag** (Bing–Jones pp. 188–189; `BJ59.zigzag_homeomorph`,
`BJ59.zigzag_fibre`). Suppose we are given:

* chains D_i on X and E_i on Y with meshes tending to 0;
* chain maps H_i of D_i onto E_i, and K_i of E_{i+1} into D_i;
* *Conditions B and B′*: each link of D_{i+1} lies in the link of D_i named by K_i ∘ H_{i+1}, and
  each link of E_{i+1} lies in the link of E_i named by H_i ∘ K_i.

Then the point h(p) defined by h(p) ∈ closure(H_i(links of D_i containing p)) for all i is a
homeomorphism X → Y (`BJ59.starImage`). The sets decrease by B and B′, and their diameters tend to 0.
If the H_i preserve fibres (Condition A below), h preserves fibres.

**23.3 Tools from Bing–Jones §§3–5.**

* **Theorem 3** (`BJ59.theorem3_arc`). A snake-like arc of continua has ε-chains from the fibre over 0
  to the fibre over 1.
* **Theorem 4** (`BJ59.bj_theorem4`). A nonempty open set missing the two end fibres separates them.
  It is used in its located form `BJ59.bj_cut`.
* **Theorem 5, repaired** (`BJ59.theorem5_repaired`). If f is open with indecomposable fibres, and no
  fibre meets a link of a chain E only inside the closure of U, then the separation of Theorem 4 can
  be chosen so that each fibre meets every link of E on one side. The printed statement is false; the
  formal proof uses this repaired form, applied on a window f⁻¹[a, b] (`BJ59.bj_theorem5_window`,
  `BJ59.bj_theorem5_window_aux`, `BJ59.exists_window_set`).
* **Theorem 7, second sentence** (`BJ59.bj_theorem7_ends'`, `BJ59.bj7_ends_compact`). Let D be a
  chain of n ≥ 3 links properly covering a pseudo-arc P, and let H be a chain map onto D. Then there
  is a chain E in Bing–Jones's sense covering P that follows H, with prescribed closed sets in
  prescribed end links. The proof folds chains along walks (`BJ59.foldChain`), uses the shrinking
  step `BJ59.exists_bjChain_shrink`, and uses crookedness of the pseudo-arc (§11.1).
* **Theorem 8** (`BJ59.bj_theorem8`, via `BJ59.bj_theorem8_ends`). Let f be a continuous snake-like
  arc of pseudo-arcs, D a chain of n ≥ 3 links each meeting every fibre, and H a chain map onto D.
  Then there is a chain E in Bing–Jones's sense, each link meeting every fibre, with each link of E
  inside the link of D named by H. The proof uses a uniform grid under a Lebesgue number, Theorem 4
  (as `BJ59.bj_cut`), and Theorem 7 on the fibres.
* **Corollary to Theorem 8** (`BJ59.bj_theorem8_cor`, with the discrete intermediate-value lemma
  `BJ59.walk_core`). Its form on a sub-arc (`BJ59.bj_theorem8_cor_sub`,
  `BJ59.bj_theorem8_cor_sub_three`, `BJ59.window_transfer`, `BJ59.exists_fibre_spread`) is the one
  used.
* **Step 1(b)** (`BJ59.bj_step1b`). Over a short enough interval, a minimal covering subchain has
  every link meeting every fibre.

**23.4 The conditions carried by the induction** (`BJ59.IsFibreChainMap`, `BJ59.EndCompat`,
`BJ59.IsFibreFine`).

* *Condition A*: a link meeting a fibre f⁻¹(t) goes to a link meeting g⁻¹(t), and a run of links
  properly covering f⁻¹(t) goes onto links covering g⁻¹(t).
* *Condition C*: compatibility with h₀ and h₁ on the end fibres.
* *Fibre-fineness*: either the chain has one link, or every run of links covering a fibre has at
  least three links (`BJ59.isFibreFine_of_isEpsChain`).

**23.5 The step** (`BJ59.BJStep`, `BJ59.bj_step`). Suppose H is a chain map of D (on X) onto E (on Y)
with Conditions A and C, where D has private points and E is fibre-fine. Then for every δ > 0 there
are a chain E′ on Y in Bing–Jones's sense, of mesh < δ and with private points, and a chain map K of
E′ onto D. K satisfies Conditions A and C in the reverse direction, and each link of E′ lies in the
link of E named by H ∘ K. *Construction:*

* (a) Cut [0, 1] into short sub-arcs, using Step 1(b).
* (b) Map fine chains of the end fibres by the pattern of h₀, h₁ (`BJ59.exists_pattern`: a fine
  chain covering a fibre maps into a run of D following the homeomorphism, each link of the run being
  the image of three consecutive links, `BJ59.exists_point_only_of_minimal`).
* (c) Map the sub-arcs by the corollary to Theorem 8 (`BJ59.exists_subarc_piece`,
  `BJ59.exists_end_piece`, `BJ59.exists_tau_run`).
* (d) Glue the pieces along windows given by the repaired Theorem 5 (`BJ59.bj_glue`).

Theorem 6 of Bing–Jones enters only in the form `BJ59.adjacent_of_properCover`. The homeomorphisms
on cut fibres and Theorem 9 are not needed.

**23.6 Theorem 10 from the step** (`BJ59.bjThm10_of_step`, `BJ59.BJStage`). Start from one-link
chains and alternate the step on the two sides, with meshes tending to 0. This produces the data
of 23.2. Then `BJ59.zigzag_homeomorph` and `BJ59.zigzag_fibre` give a fibre-preserving homeomorphism,
and Condition C makes it agree with h₀ and h₁.

## 24. Uniqueness, homogeneity and recognition

**24.1 Gluing two halves** (`BJ59.exists_half_homeomorph`, `BJ59.exists_homeomorph_glue`, and the
primed versions `BJ59.exists_half_homeomorph'`, `BJ59.exists_homeomorph_glue'` for
`BJ59.IsSnakeHalvesMap`). Let f : X → S¹ and g : Y → S¹ both have snake-like halves, and let
k₊ : f⁻¹(1) → g⁻¹(1) and k₋ : f⁻¹(−1) → g⁻¹(−1) be homeomorphisms. Apply Theorem 10 to each half
with end homeomorphisms k₊ and k₋. The two half homeomorphisms agree on the common fibres, so they
glue to Φ : X → Y with g ∘ Φ = f and Φ = k₊ on f⁻¹(1).

**24.2 Any two circles of pseudo-arcs are homeomorphic** (`BJ59.homeomorph_of_isCircPAMap`,
`BJ59.homeomorph_of_isCircleOfPA`). The fibres over 1 are pseudo-arcs, hence homeomorphic (§11.3,
`Plane.theorem1_HIC'`), and likewise the fibres over −1. Then apply 24.1.

**24.3 Every circle of pseudo-arcs is homogeneous** (`BJ59.isHomogeneous_of_isCircPAMap`,
`BJ59.isHomogeneous_of_isCircleOfPA`). Given x, y, rotate f so that f(x) = 1, and separately so that
f(y) = 1 (`BJ59.IsCircPAMap.mul_left`). A homeomorphism of the fibres over 1 sending x to y comes from
§11.3 followed by homogeneity of the pseudo-arc (§11.4). Gluing (24.1) gives a self-homeomorphism
carrying x to y.

**24.4 Recognition: open atomic maps** (`BJ59.dp22_theorem61`, `BJ59.homeomorph_of_isSnakeHalvesMap`,
`BJ59.isCircleOfPA_of_atomic`). Let X be compact with an open atomic map onto S¹ with pseudo-arc
fibres, and let Y be any circle of pseudo-arcs. Then X ≅ Y (Domokos–Prajs Theorem 6.1, "if" direction).
*Proof:* both maps have snake-like halves (22.2), so 24.1 applies. Hence X is circle-like
(`BJ59.isCircleLike_univ_of_homeomorph`), and X is a circle of pseudo-arcs.

**24.5 Circle-likeness of decomposable homogeneous plane continua** (`BJ59.hoCircleLike`,
`BJ59.HOCircleLike`). Let M be a decomposable homogeneous plane continuum. If M is a simple closed
curve, it is circle-like (`BJ59.isCircleLike_circle`). Otherwise it has an open atomic pseudo-arc map
onto S¹ (§21.2). By 24.4 it is then homeomorphic to the plane circle of pseudo-arcs of §25, so it is
circle-like.

## 25. A circle of pseudo-arcs in the plane

**Theorem** (`BJ59.bjPlaneExample : BJ59.BJPlaneExample`). Some plane continuum is a circle of
pseudo-arcs. Bing–Jones §7 states this without a full construction. The formal proof uses a
different route, which runs parallel to the construction of the plane pseudo-arc in §10.

**25.1 Circular descriptions** (`BJ59.CircDescr`). Level k is a circular chain of N_k ≥ 4 open
connected links in a fixed compact set, indexed by ℤ mod N_k, with mesh → 0. Level k + 1 refines level
k along a lifted pattern of degree one with unit steps. Link closures are nested (`nest`), and the
refinement is *tight*: a new link meets only old links named by the pattern at nearby positions
(`tight`). Each link t of level k carries the label of a closed arc of ℝ/ℤ of length λ_k → 0,
centred at o_k + t/N_k. The arcs of new links lie in the arcs of the old links they map to
(`arcNest`). Every point of a slightly shrunk arc lies in the shrunk arc of some child (`surv`). The
patterns are crooked on every window that a run of level k + 1 can occupy (`crook`).

**25.2 Recognition** (`BJ59.CircDescr.isCircleOfPA`). The set M = ⋂_k (union of level k)
(`BJ59.CircDescr.M`, `BJ59.CircDescr.isCompact_M`) is a circle of pseudo-arcs. *Proof:* for y ∈ ℝ/ℤ,
the links whose arcs contain y form runs, and these runs are chains. A run of level k + 1 is crooked
in the run of level k (`crook` with tightness). So the fibre over y, the intersection of the runs
(`BJ59.CircDescr.fib`), is described by crooked chains and is a pseudo-arc, as in §9. The map
`BJ59.CircDescr.fmap` : M → S¹ sending a point to its label is continuous and surjective. It is open by
survival. The traces of the circular chains on M make M circle-like.

**25.3 Sweep patterns** (`BJ59.sweep_lemma`, `BJ59.sweepX`, `BJ59.exists_sweepPattern`). For m ≥ 5 and
S ≥ 1 there is an explicit lifted pattern x : ℤ → ℤ of degree one. It has unit steps and is S-slow
(values two apart are at distance at least S). It satisfies the nesting and survival estimates of
25.1, and it is crooked on every window of the required length. Crookedness comes from the sweep
lemma: blocks of fixed length that run alternately up and down through windows moving one end at a
time are crooked on any interval containing at most two window changes.

**25.4 The circular planar step** (`BJ59.circ_step`). This is the analogue of `Plane.real_step` for
circular chains. Fix a tame circular chain, the image under a plane homeomorphism Φ of the standard
circular chain `BJ59.stdCircLink` (with its intersection pattern `BJ59.stdCircLink_meet_iff`). Every
sufficiently slow lifted pattern of degree one with bounded drift is then realized by a tame circular
chain of QN links with closures nested, tight, and with links small or inside old zones. The proof
transports the joint positions of §10 through a shear on the universal cover and descends it by the
map E(u, v) = exp(v + iπu/N) (`BJ59.circExp`).

**25.5 Assembly** (`BJ59.planeDescr`, `BJ59.exists_circDescr_plane`). Start from the standard circular
chain of 16 links and alternate 25.3 and 25.4 to obtain a circular description in ℝ². By 25.2 its
set M is a plane circle of pseudo-arcs.

---

# Part VII. Assembly

## 26. The classification

**26.1 The decomposable case** (`BJ59.circle_or_circleOfPA_of_decomposable`). A decomposable homogeneous
plane continuum M is a simple closed curve or a circle of pseudo-arcs. *Proof:* M is circle-like by
§24.5. Then §21.3 gives a homeomorphism to S¹ or a map with `BJ59.IsCircPAMap`, that is, a circle of
pseudo-arcs (`BJ59.isCircleOfPA_iff`).

**26.2 The classification with its inputs as hypotheses** (`BJ59.ho16_classification`). Assume
Theorem 10 and `BJ59.HOCircleLike`. A nondegenerate plane continuum M is homogeneous iff it is a
simple closed curve, a pseudo-arc, or a circle of pseudo-arcs.

* (⇒) If M is decomposable, use 26.1. If M is indecomposable, M is a pseudo-arc by Part IV
  (`HO16.ho16_indec_homogeneous_iff`).
* (⇐) The circle is homogeneous, since rotations act transitively (`BJ59.isHomogeneous_circle`,
  `BJ59.isHomogeneous_circle'`), and homogeneity passes along homeomorphisms. A pseudo-arc is
  homogeneous by §11.4 (`HO16.ho16_pseudoArc_indec_homogeneous`). A circle of pseudo-arcs is
  homogeneous by §24.3 (`BJ59.isHomogeneous_of_isCircleOfPA`).

**26.3 The plane form with its inputs as hypotheses** (`BJ59.ho16_classification_plane`). Assume
Theorem 10, `BJ59.HOCircleLike` and `BJ59.BJPlaneExample`. Take the following plane continua:

* C₁: a plane simple closed curve (`BJ59.exists_plane_circle`);
* C₂: a plane pseudo-arc (§10, `Plane.isPseudoArc_plane`);
* C₃: a plane circle of pseudo-arcs.

Each is homogeneous by 26.2 (for C₂ directly by `Plane.homogeneous_of_isPseudoArc`). No two are
homeomorphic:

* C₁ and C₃ are decomposable (`BJ59.isDecomposableSpace_circle`; for C₃,
  `BJ59.isDecomposableSpace_of_isCircPAMap`, the two halves of §22). C₂ is indecomposable, being HI.
  So C₂ is not homeomorphic to C₁ or to C₃.
* If Φ : C₁ → C₃ were a homeomorphism, the fibre of C₃ over 1 would be carried to a pseudo-arc in
  S¹. That pseudo-arc misses the image of any point over −1, so it is a proper subset of S¹
  (`BJ59.circle_exp_pi_ne_one`). No proper subset of the circle is a pseudo-arc
  (`BJ59.not_isPseudoArc_of_ne_univ_circle`): if K misses a point z, the argument measured from z
  embeds K in ℝ, so K would be a nondegenerate compact interval, which is decomposable.

For a nondegenerate plane continuum M, if M is homogeneous then 26.2 says that M is a circle, a
pseudo-arc or a circle of pseudo-arcs. Then M is homeomorphic to C₁, to C₂ (any two pseudo-arcs are
homeomorphic, §11.3, `Plane.theorem1_HIC'`) or to C₃ (§24.2, `BJ59.homeomorph_of_isCircleOfPA`).
Conversely, a continuum homeomorphic to C₁, C₂ or C₃ is homogeneous.

**26.4 Discharging the inputs.**

* `BJ59.ho16_classification₂`, `BJ59.ho16_classification_plane₂`: `BJ59.HOCircleLike` is replaced
  by Theorem 10 and the plane example, via §24.5 (`BJ59.hoCircleLike`).
* `BJ59.ho16_classification₃`, `BJ59.ho16_classification_plane₃`: Theorem 10 is discharged by
  `BJ59.bjThm10` (§23).
* `BJ59.ho16_classification₄`, `BJ59.ho16_classification_plane₄`: the plane example is discharged by
  `BJ59.bjPlaneExample` (§25).

The two final theorems carry no hypotheses beyond those in their statements. Their proofs depend
only on the results described above and on Mathlib.
