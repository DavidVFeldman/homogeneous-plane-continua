# Commission: batch 194 — H–O Theorem 1, II: PL graphs; simple folds; Lemma 6, Theorem 8, Prop. 7

**Go!** This batch runs on top of the batch-193 work. Three files come with it, as separate
uploads:

* `COMMISSION-batch194.md`: this text, also pasted into the prompt.
* `HO16B.lean`: the skeleton.
  * Save it as `HPC/HO16/HO16B.lean`. You may split it under `HPC/HO16/`.
  * Add `import HPC.HO16.HO16B` at the end of `HPC.lean`. It imports `HPC.HO16.HO16A`.
* `lelek1979.pdf`: save as `doc/sources/lelek1979.pdf` (Lelek, *The span of mappings and spaces*,
  Topology Proc. 4 (1979), 631–633; H–O's [31]; PDF page 1 is a cover page).

Page numbers are the journals'. H–O = Hoehn–Oversteegen, Acta Math. 216 (2016); PDF page `n` of
`doc/sources/hoehn-oversteegen2016.pdf` is journal page `176 + n`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before: for every theorem whose hypotheses include a named
  `Prop` or a structure, the two checks in the report.
* **Quotations (standing rule, restated).** Check every quotation and every reading of a formula
  against page images rendered at 200 dpi or more (400 dpi for subscripts, primes and bars), not
  against the text layer: the text layer drops overlines and primes (§0).
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "H–O Theorem 1, II (batch 194)");
  * `README.md`;
  * `LEDGER.md`: the section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)",
    and the counts if §9 changes them;
  * `OPEN.md`;
  * `doc/notes/ho16.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 193

* **Delivery.** The download was current (its `axioms.txt` equals the tarball's). Keep publishing
  the tarball and manifest (§11.4).
* **Copies.** The skeleton, the commission and both PDFs are byte-identical to what I sent.
* **Audit.** `axioms.txt` has 2712 lines (2658 + 54 added, none removed), with `sorryAx` in none;
  all 54 new theorems use exactly the three standard axioms. The seven new files contain no
  `sorry`, `admit` or `axiom` outside comments. All 16 definitions and statements match the
  skeleton.
* **Results.** `homeomorph_pseudoArc_of_indec_homogeneous` with `HOThm20` as the only open input.
  The correction toward the fan vertex in `ho16_theorem8_core` (instead of a Tietze extension on
  each piece) is accepted; it gives `h = y` exactly on `X₂ ∩ X₃`, which §6 below uses.
* **Ledger: one correction.** HO.4's "further observation" is a misreading of the text layer.
  The page image of p. 188 (400-dpi crop) prints the closure bar in both places:
  "Let Kᵢ = f⁻¹(cl(Gᵢ \ G₂))" and "f⁻¹(yⱼ¹) ⊂ f⁻¹(cl(G₁ \ G₂)) = K₁ ⊂ X₁" (bars over `Gᵢ \ G₂`).
  Remove the observation from HO.4 and say why. (The same thing happened in batch 134 with van
  Mill; hence the restated rule above.)
* HO.1–HO.3 and HO.5–HO.8 are adopted. HO.2 can now be checked against `lelek1979.pdf` (§9).

## 1. The plan

The open input is `HOThm20`. H–O prove Theorem 20 from Theorem 8 (lifting through simple folds),
Theorem 15 (a separator contains a set with a stairwell structure) and Propositions 17 and 19
(unfolding stairwells by simple folds). This batch does the simple folds.

**Folds as sets.** H–O build a fold as a quotient (pp. 185–186). Here a fold on a PL graph
`G ⊆ E` lives in `E × ℝ` with projection `φ = Prod.fst`: `F₁`, `F₂`, `F₃` are graphs of height
functions over `G₁`, `G₂`, `G₃` (`IsSimpleFoldOf`, §2). The fold `F₁ ∪ F₂ ∪ F₃` is again a PL
graph, now in `E × ℝ`, so the later induction runs over normed spaces `E, E × ℝ, (E × ℝ) × ℝ, …`.
H–O's uniqueness remark (p. 186) is not needed: Theorem 8 is proved for every fold in this sense,
and Proposition 19 will construct its folds by §4. (For later: the straight sets of Definition 12
will be graphs of continuous functions over PL subgraphs; only their projections are PL graphs.)

**This batch.**
1. Definitions: `relFrontier`, `IsFoldTriple`, `IsSimpleFoldOf` (§2).
2. A library for PL graphs (§3).
3. Folds exist: the construction of pp. 185–186 (§4).
4. Lemma 6 ("left to the reader") (§5).
5. Theorem 8, (1) ⇒ (2), for folds, from `ho16_theorem8_core` (§6).
6. Proposition 7 (§7).
7. Certificates for Theorem 1 as restated on p. 211 and Theorem 1′ (§8).

If the whole does not fit, do §2, §3, §4, §6 first: Theorem 8 for folds is the item later batches
need most.

## 2. Definitions

1. **`relFrontier G A = cl A ∩ cl (G \ A)`**, H–O's `∂A` for `A ⊆ G`. For closed `A` it is
   `A ∩ cl (G \ A)`. The general form is needed in Lemma 6 (2), where `A = G₁ \ G₂`.
2. **`IsFoldTriple G G₁ G₂ G₃`**: H–O's (F1)–(F3), with "regular" read as "PL graph":
   `G₁`, `G₂`, `G₃` nonempty PL graphs, `G₁ ∪ G₃ = G`, `G₂ = G₁ ∩ G₃`, and
   `cl(G₁ \ G₂) ∩ cl(G₃ \ G₂) = ∅`. (H–O p. 184: "A subset A of G will be called regular if A is
   closed and has finitely many components, each of which is non-degenerate". For subsets of a PL
   graph this is the same as being a PL graph. Only "PL graph ⇒ regular" is used here; "a regular
   subset of a PL graph is a PL graph" needs "a subcontinuum of a PL graph is a PL graph" and is not
   asked for now, though Definition 12 and Theorem 15 may need it later.)
3. **`IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃`** (`Fᵢ ⊆ E × ℝ`): the triple condition; each `Fᵢ` a PL
   graph on which `Prod.fst` is injective with image `Gᵢ` (so `φ|Fᵢ` is a homeomorphism onto `Gᵢ`,
   H–O's (F4)); `φ(F₁ ∩ F₂) = ∂G₁`, `φ(F₂ ∩ F₃) = ∂G₃`, `F₁ ∩ F₃ = ∅` (H–O's (F5)). The fold is
   `F = F₁ ∪ F₂ ∪ F₃`.

## 3. A library for PL graphs

The skeleton states nine lemmas (`IsPLGraph.exists_refinement`, `isPLGraph_biUnion`,
`IsPLGraph.union`, `IsPLGraph.closure_diff`, `IsPLGraph.relFrontier_finite`,
`IsPLGraph.connectedComponentIn`, `IsPLGraph.finite_components`,
`IsPLGraph.inter_connectedComponentIn`, `IsPLGraph.image_fst`); their order in the files is yours.
Further lemmas are shape left to you; the batches after this one will lean on the library, so
build it for reuse. Expected later: boundaries of subgraphs; for finite `B`, the components of
`G \ B` have PL closures and frontiers inside `B` (Propositions 10–11); branch points and endpoints
of `G` in a form that does not change under refinement ("generic", Definition 12).

**The core: decompositions and refinement.** A decomposition of `G` is a finite set `S` of pairs as
in `IsPLGraph`; its vertices are the endpoints. **§3.0, `IsPLGraph.exists_refinement`:** for a PL
graph `G`, PL graphs `A₁, …, A_k ⊆ G` and a finite `P ⊆ G`, there is a decomposition `S` of `G` in
which every `Aᵢ` is the union of the edges it contains, an edge not contained in `Aᵢ` meets `Aᵢ`
only at its endpoints, and every point of `P` is a vertex. Then frontiers are vertex sets,
components are unions of edge classes, and most of H–O §4 becomes finite combinatorics.
(`isPLGraph_biUnion` alone forgets the edges, so the later items should be derived from §3.0.)
Keeping "each piece once" needs an explicit choice of orientation (for example through `Sym2 E`).

**§3.1, `isPLGraph_biUnion`** (proof sketch). The intersection of two segments of a real vector
space is empty or a segment `[p, q]` (a convex subset of a line), possibly a point. Let `V` be the
finite set of all endpoints of the given segments and of all these pairwise intersections.
Subdivide each segment at the points of `V` on it, ordered along it, and keep each resulting piece
once (one orientation). Two different pieces share no point other than common endpoints: if pieces
of `t` and `t'` share a point `x` that is not an endpoint of both, then `x ∈ t ∩ t' = [p, q]` with
`p, q ∈ V`, and both pieces are cut at the same points `V ∩ [p, q]`, so they coincide. (The mixed
case, `x` an endpoint of one piece and interior to the other, cannot occur: endpoints lie in `V`,
and no piece has a point of `V` in its interior.)

The other lemmas follow from §3.1 and refinement: `closure (G \ A)` is the union of the edges not
in `A`; the frontier of a subgraph consists of vertices; a component of `G` is the union of a class
of edges under "share a vertex"; an edge of `A` meeting a component lies in it; `Prod.fst` maps a
segment on which it is injective to a nondegenerate segment.

## 4. Simple folds exist (H–O pp. 185–186)

**Statement** (`exists_simpleFold`): every `IsFoldTriple G G₁ G₂ G₃` has `F₁, F₂, F₃` with
`IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃`.

**Construction.** Write `B₃ = ∂G₁` and `B₁ = ∂G₃` (finite by §3.4; disjoint, since
`∂G₁ ⊆ cl(G₃ \ G₂)` and `∂G₃ ⊆ cl(G₁ \ G₂)`; both inside `G₂`, which step 4 uses to put `(b, 1)`
in `F₂`).
1. Take a decomposition `S` of `G` in which `G₁, G₂, G₃` are unions of edges (§3.0; the points of
   `B₁ ∪ B₃` are then vertices); then subdivide every edge at its midpoint (a midpoint is never an
   old vertex). Now no edge has both endpoints in `B₃`, nor both in `B₁`, which is all the
   midpoint step is for.
2. Heights at vertices: `h₁ v = 1` for `v ∈ B₃`, `h₁ v = 0` otherwise; `h₃ v = 1` for `v ∈ B₁`,
   `h₃ v = 2` otherwise.
3. `F₁` = union over the edges `[a, b] ⊆ G₁` of the segments `[(a, h₁ a), (b, h₁ b)]`;
   `F₂` = union over the edges `[a, b] ⊆ G₂` of `[(a, 1), (b, 1)]`;
   `F₃` = union over the edges `[a, b] ⊆ G₃` of `[(a, h₃ a), (b, h₃ b)]`.
4. **Checks.**
   * Lifts of different edges meet only over common vertices, where the heights agree; so each
     `Fᵢ` is a PL graph, `Prod.fst` is injective on it, and its image is `Gᵢ`.
   * Over a point `x` of an edge `[a, b] ⊆ G₂`, the `F₁`-height is `≤ 1`, with equality only if
     `x` is a vertex in `B₃` (an interior point has height `< 1`, since at most one end is in
     `B₃`); the `F₂`-height is `1`; the `F₃`-height is `≥ 1`, with equality only at vertices in
     `B₁`. Hence `φ(F₁ ∩ F₂) = B₃ = ∂G₁`, `φ(F₂ ∩ F₃) = B₁ = ∂G₃`, and `F₁ ∩ F₃ = ∅`
     (`B₁ ∩ B₃ = ∅`).

## 5. Lemma 6

H–O p. 185: "We record here some basic properties of simple folds. The proofs of these properties
are left to the reader." The skeleton states items (1), (2), (4), (5), (6), (7) for every
`IsSimpleFoldOf`; item (3) ("F₁, F₂, and F₃ are regular subsets of F") is part of the definition.

**Proof sketch.**
* **(1), (2).** Set algebra: `G \ G₁ = G₃ \ G₂` and `G \ G₃ = G₁ \ G₂`; `cl(G₁ \ G₂) ⊆ G₁`,
  `cl(G₃ \ G₂) ⊆ G₃` (the `Gᵢ` are closed); so `∂G₁ = G₂ ∩ cl(G₃ \ G₂)`,
  `∂G₃ = G₂ ∩ cl(G₁ \ G₂)`, `∂G₂ = ∂G₁ ∪ ∂G₃`, and (F3) gives `∂G₁ ∩ ∂G₃ = ∅`. For (2):
  `cl(G \ (G₁ \ G₂)) = G₃`, so `relFrontier G (G₁ \ G₂) = cl(G₁ \ G₂) ∩ G₃ = ∂G₃`.
* **(4).** `Prod.fst` is injective on `F₁` and maps `F₁ ∩ F₂` into the finite set `∂G₁`.
* **(5).** `F₁ ∩ (F₂ ∪ F₃) = F₁ ∩ F₂` is finite. A point of `F₁ \ F₂` is at positive distance from
  the compact `F₂ ∪ F₃`, so it is not in `cl(F \ F₁)`. A point of `F₁ ∩ F₂` is a limit of points of
  `F₂ \ F₁` (a PL graph has no isolated points, and `F₁ ∩ F₂` is finite). Likewise for `F₃` and
  `F₂`.
* **(6).** Take `U = (F₂ ∪ F₃)ᶜ`, `V = F₁ᶜ` in the definition of `SeparatesIn` (for the second,
  `U = (F₁ ∪ F₂)ᶜ`, `V = F₃ᶜ`).
* **(7).** For `p ∈ F₁ \ F₂`: `φ(p) ∉ ∂G₁` (the `F₁`-point over a point of `∂G₁` lies in `F₂`), so
  `φ(p)` has a neighbourhood in `G` inside `G₁`, and `φ|F₁` is a homeomorphism onto `G₁`. For
  `p ∈ F₂ \ (F₁ ∪ F₃)`: `φ(p) ∉ ∂G₂`. Likewise for `F₃`.

## 6. Theorem 8, (1) ⇒ (2), for folds

**Statement** (`ho16_theorem8`): for a hereditarily indecomposable compact metric `X`, a fold
`IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃`, continuous `f : X → G` and `ε > 0`, there is a continuous
`g : X → F₁ ∪ F₂ ∪ F₃` with `dist (f x) (g x).1 < ε`. (H–O p. 187, (2): "for any map f : X → G to a
graph G, for any simple fold φ : F → G, and for any ε > 0, there exists a map g : X → F such that
d_sup(f, φ∘g) < ε".)

**Proof.**
1. `ho16_theorem8_core` applies: `G₁, G₃` are closed; `cl(G₁ \ G₂) ∩ G₂ = ∂G₃` and
   `cl(G₃ \ G₂) ∩ G₂ = ∂G₁` are finite (§5 (1), (2), §3.4); fans exist in the PL graph `G₂`
   (`IsPLGraph.exists_fan`). It gives `h` and closed `X₁, X₂, X₃`.
2. `ψᵢ = (φ|Fᵢ)⁻¹ : Gᵢ → Fᵢ` is continuous (a continuous injection of a compact space). Put
   `g = ψᵢ ∘ h` on `Xᵢ`.
3. On `X₁ ∩ X₂`, `h x ∈ ∂G₁ = φ(F₁ ∩ F₂)`; the unique `F₁`-point and the unique `F₂`-point over
   `h x` are the same point of `F₁ ∩ F₂`. Likewise on `X₂ ∩ X₃`. `X₁ ∩ X₃ = ∅`. So `g` is well
   defined and continuous (finitely many closed pieces), and `φ ∘ g = h`.

## 7. Proposition 7

**Statement** (`ho16_prop7`), as on p. 186: "Suppose that G is connected, and that ∂G₁ ≠ ∅ ≠ ∂G₃.
Then there is a component C of F such that φ(C) meets ∂G₁ and ∂G₃. Moreover, for any such
component, φ(C) = G, and if we let F′ᵢ = Fᵢ ∩ C for i = 1, 2, 3, then F′ = F′₁ ∪ F′₂ ∪ F′₃ is also
a simple fold on G, with projection map φ|F′ : F′ → G."

**Proof** (H–O pp. 186–187; record the unargued steps, §9):
1. **A component `K` of `G₂` meeting `cl(G₁ \ G₂)` and `cl(G₃ \ G₂)`.** H–O: "By (F2) and (F3), and
   since G is connected". `G₂` has finitely many components (§3.5); if none meets both closures,
   group them by which closure they meet and split `G` into two disjoint nonempty closed sets.
   Then `K` meets `∂G₃` and `∂G₁` (§5 (2)); the `F₂`-copy of `K` is connected and lies in a
   component `C` with `φ(C) ⊇ K`.
2. **Claim 7.1.** A connected `C' ⊆ C` with `φ(C') ⊆ G₂` meeting `∂G₁` and `∂G₃` has
   `φ⁻¹(φ(C')) ⊆ C`: the three copies of `φ(C')` are connected, the `F₁`-copy meets the `F₂`-copy
   over `∂G₁`, and the `F₂`-copy meets the `F₃`-copy over `∂G₃`.
3. **`φ(C)` is open in `G`**, hence `= G` (it is closed, and `G` is connected). At `p ∈ C` with
   `p ∉ ∂F₂`: §5 (7) (a component of a PL graph is open in it). At `p ∈ ∂F₁`, H–O write "Let C′ be
   the closure of the component of C\φ⁻¹(∂G₃) containing p"; boundary bumping gives
   `C′ ∩ φ⁻¹(∂G₃) ≠ ∅`, and Claim 7.1 puts the `F₃`-point over `φ(p)` in `C`, where §5 (7)
   applies.
   * **Unargued (my reading):** Claim 7.1 needs `φ(C′) ⊆ G₂`, which H–O do not argue. It holds
     because `F \ φ⁻¹(∂G₃)` splits into three relatively closed, pairwise disjoint sets:
     `(F₁ ∪ F₂) ∩ φ⁻¹(G₂)`, `F₁ ∩ φ⁻¹(G₁ \ G₂)` and `F₃ \ φ⁻¹(∂G₃)` (use
     `F₃ ∩ (F₁ ∪ F₂) = F₂ ∩ F₃` and `cl(G₁ \ G₂) ∩ G₂ = ∂G₃`); the component of `p` lies in the
     first, and so does its closure.
   * **Preferred route (no boundary bumping):** let `K` be the component of `G₂` containing
     `φ(p)` and `Kᵢ` its copy in `Fᵢ`. If `K ∩ ∂G₃ = ∅`, then `K` is a component of `G₁` and
     `K₁ ∪ K₂` is clopen in `F`; since `p ∈ K₂ ∩ C`, `C ⊆ K₁ ∪ K₂` and `φ(C) ⊆ K` misses `∂G₃`, a
     contradiction. So `K` meets `∂G₃`, and Claim 7.1 applies to `C′ = K₂`.
4. **`F′` is a simple fold on `G`.** H–O: "It is straightforward to check from the definition of a
   simple fold that if C ⊂ F is a component with φ(C) = G, then F′ … is a simple fold on G". Check
   every clause of `IsSimpleFoldOf` for `Gᵢ' = φ(Fᵢ ∩ C)`; §3.5 and §3.6 give the PL clauses.
   Note: `Gᵢ'` may be a proper subset of `Gᵢ` ("note that it may well happen that G′ᵢ = φ(F′ᵢ) is a
   proper subset of Gᵢ"). The other clauses rest on a lemma H–O do not state:
   * **Lemma (L).** Let `C` be a component with `φ(C)` meeting `∂G₁` and `∂G₃`, `K` a component of
     `G₂`, `Kᵢ` its copies.
     (a) If `K ∩ ∂G₁ = ∅`, then `K` is a component of `G₃` and `K₂ ∪ K₃` is clopen in `F` and
     disjoint from `C` (symmetrically if `K ∩ ∂G₃ = ∅`).
     (b) Hence `K₂ ⊆ C` implies `K₁ ∪ K₃ ⊆ C`.
     (c) `K` cannot miss both `∂G₁` and `∂G₃` (it would be clopen in `G`, so `K = G` and
     `∂G₁ = ∅`).
   * Then `G₂' = G₁' ∩ G₃'` follows from (b) and (c); `G₁' ∪ G₃' = G`; `G₁'`, `G₃'` are nonempty
     (they are closed with union the connected `G`, and `G₃' = ∅` would force `G₁ = G`); (F3) for
     the `Gᵢ'` because the component `K(·)` is locally constant near a point of `G₂'`; and (F5):
     a point of `G₃' \ G₂'` in `G₂` lies in some `K` that is, by (a), a component of `G₁` disjoint
     from `G₁'`, so near `G₁'` the set `G₃' \ G₂'` lies in `G₃ \ G₂`.
   * Regression tests (the referee's): `G = [0, 4]`, `G₁ = [0, 3]`, `G₃ = [½, 1] ∪ [2, 4]`,
     `G₂ = [½, 1] ∪ [2, 3]` (a circle component `F₂[½, 1] ∪ F₃[½, 1]`; the other component
     restricts to `([0, 3], [2, 3], [2, 4])`); and `G = [0, 3]`, `G₁ = [0, 1] ∪ [2, 3]`,
     `G₃ = [½, 3]`, `G₂ = [½, 1] ∪ [2, 3]` (the glue point over `2 ∈ ∂G₁` is not in `C`; the
     restriction is `([0, 1], [½, 1], [½, 3])` with `∂G₁' = {1}`).
   If a clause fails, give the counterexample.

## 8. Theorem 1 and Theorem 1′ as printed

Ledger HO.1 and HO.8 record that the restatement of Theorem 1 on p. 211 and Theorem 1′ on p. 212
omit "non-degenerate". H–O define "continuum" on p. 177 ("by a continuum, we mean a compact
connected metric space. A continuum is non-degenerate if it contains more than one point"), so a
one-point space is a continuum; and on p. 178 "A continuum is hereditarily decomposable
(hereditarily indecomposable) if every non-degenerate subcontinuum is decomposable
(indecomposable, respectively)", so it is hereditarily indecomposable in their sense too. The
`ConnectedSpace` instance for the one-point type may have to be supplied by hand.

Prove the two certificates `ho16_theorem1_printed_false` and `ho16_theorem1prime_printed_false`
with `X` a one-point space: it is hereditarily indecomposable, every subcontinuum of `X × X` meets
the diagonal, and it is not homeomorphic to a pseudo-arc (`IsPseudoArc` includes nontriviality).
`SurjSemiSpanZero` is H–O's definition on p. 212 ("every subcontinuum Z ⊆ X × X with π₂(Z) = X
meets the diagonal").

## 9. Places to check (ledger)

In the section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)":
1. **HO.4:** remove the "further observation" (§0) and record that the bar is printed.
2. **HO.2:** check against `doc/sources/lelek1979.pdf` (pp. 631–633): the paper is an announcement
   ("The purpose of the present paper⁽¹⁾ is to announce some results … A complete version will be
   published elsewhere"); Lemma 5 and Theorem 6 have no proof; how Corollary 10 is obtained
   (p. 633). The referee of this commission adds: Corollary 9 is stated for compact `X` without
   `dim X ≤ 1`, which Theorem 6 and Corollaries 7–8 assume; p. 633 supplies dimension one only for
   non-degenerate continua (citing [4]) and passes from `T` to all one-dimensional polyhedra by
   citing [3] without argument. Record what you find.
3. **HO.1 and HO.8, classification.** I propose: Theorem 1′ (p. 212) is a false printed statement
   at a degenerate case, counted as the ledger counts Jones 1949 Theorems 1–2 and Moore 1920
   Theorem 4 (one-point continuum or set), with the certificate of §8; Theorem 1 as restated on
   p. 211 stays a misprint, since p. 180 states it correctly, with its certificate as supporting
   evidence. Say plainly in the ledger that the two omissions are counted differently, and why
   (Theorem 1 is stated correctly on p. 180; Theorem 1′ is stated correctly nowhere, although p. 212
   presents it as what "our proof of Theorem 1 in fact establishes"). If you agree, update the count
   of false printed statements in `LEDGER.md`; if not, argue otherwise.
4. **Lemma 6 (p. 185, "left to the reader").** If §5 is proved: stated without proof; items (1),
   (2), (4)–(7) verified for folds in the sense of `IsSimpleFoldOf`; (3) by definition.
5. **pp. 185–186:** "It is straightforward to see that this is a well defined simple fold": the
   existence is verified in the form of §4 (not by a quotient). The uniqueness clause ("if F′ is
   another simple fold on G with projection φ′ such that φ′(F′ᵢ) = Gᵢ … then there is a
   homeomorphism θ") is not used; record "not formalized, not used".
6. **Proposition 7 (pp. 186–187):** the existence of `K` ("By (F2) and (F3), and since G is
   connected") — unargued, supplied; the application of Claim 7.1 (`φ(C′) ⊆ G₂`, §7 step 3) —
   unargued, supplied; "It is straightforward to check … F′ … is a simple fold" — unargued (it
   rests on Lemma (L) of §7 step 4), supplied or refuted.
7. **p. 186:** "In general, even if G is connected, a simple fold F on G need not be connected" and
   "Note that if G is connected and ∂G1=∅, then G1=G, F is disconnected, and φ|F1 is a
   homeomorphism of F1 onto G": record whether each is right (an example for the first suffices in
   words).

## 10. Order

§2, then §3, then §4 and §5, then §6 and §7; §8 any time.

## 11. Deliverables

1. **The items of §2–§8.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch194.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** §9.
3. **Notes:** `doc/notes/ho16.md`: the fold representation and the library, in a few paragraphs.
4. **Publish the changes, as in batch 193.** At the end of the run:
   * create `doc/batches/batch194-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch194-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `homeomorph_pseudoArc_of_indec_homogeneous` (unchanged: `HOThm20` the
     only open input) and the list of what in `HOThm20`'s proof is now in place;
   * comments on the plan for the stairwell batches (Definitions 9, 12, 13, 16; Propositions 10,
     11, 17, 19; Lemma 18; Theorem 15) given the library you built.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   * Nothing is left at the root.
