Commission read: `doc/batches/COMMISSION-batch149.md` (batch 149, Part F, Jones 1949 I: order, Menger's theorem, Whyburn (9.2)).

# Report, batch 149

**Outcome.**

| item | outcome |
|---|---|
| A, B, C | **proved** |
| D: `whyburn_9_1` | **proved** |
| D: `whyburn_9_2` | **open**, obstruction in `OPEN.md` |
| D: `jones49_some_order_two` | **open**; reduced to (9.2) (`jones49_some_order_two_of_whyburn_9_2`, proved) |

The commission allows this split: deliver (i) complete and leave the items of (iv) open.

**Build and axioms.**
* `lake build HPC` succeeds with `import HPC.Jones.Jones49A` at the end of `HPC.lean`.
* No new file contains `sorry`. The two open statements are kept verbatim as comments in
  `HPC/Jones/Jones49A.lean`.
* Every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`. The audit is
  `doc/batches/audits/axioms-batch149.txt`, produced by `axioms-batch149.lean`.
* `axioms.txt` is regenerated, with `sorryAx` in no line. The previous version is kept as
  `doc/batches/audits/axioms-before-batch149.txt`.
* `Axioms.lean` has the new group *Jones 1949: order, Menger, Whyburn 9.2 (batch 149)*.

**Uploads.**
* The commission is at `doc/batches/COMMISSION-batch149.md`.
* The skeleton is kept verbatim at `doc/batches/skeletons/Jones49A-batch149.lean`.
* The two sources are at `doc/sources/menger-kurventheorie.pdf` and `doc/sources/wilder1938.pdf`.
  They are not committed, since `*.pdf` is in `.gitignore`, as for the earlier sources.
* Nothing is left at the root.

**Files.**

| file | content |
|---|---|
| `HPC/Jones/Jones49Order.lean` | item A: `OrderLE`, `HasOrder`, `hasOrder_homeomorph`; `orderLE_subtype`, `not_orderLE_two_of_triod`, `locallyConnectedSpace_of_orderLE` |
| `HPC/Jones/Jones49Circle.lean` | item B: `glue_circle`, `tscc_homeomorph_circle` |
| `HPC/Jones/Jones49Menger.lean` | item C: `exists_continuum_of_isOpen`, `exists_tarc_of_orderLE`, `tarc_halves`, `arc_eq_of_legs`, `menger_order_two`, `jones49_order_two` |
| `HPC/Jones/Jones49Why.lean` | item D: `IsSepPointOf`, `IsLocalSepPoint`, `exists_continuum_bump_compact`, `isPreconnected_side`, `whyburn_9_1_side`, `whyburn_9_1` |
| `HPC/Jones/Jones49A.lean` | umbrella: `IsSepPointOf.homeomorph`, `IsLocalSepPoint.homeomorph`, `jones49_some_order_two_of_whyburn_9_2`; the open `whyburn_9_2` and `jones49_some_order_two` as comments |

**Statements.**
* Ten skeleton declarations are delivered. Eight are verbatim: `OrderLE`, `HasOrder`,
  `hasOrder_homeomorph`, `tscc_homeomorph_circle`, `menger_order_two`, `jones49_order_two`,
  `IsSepPointOf` and `IsLocalSepPoint`.
* **One shape change**: `whyburn_9_1` drops the hypothesis `(hR : IsOpen R)`, which the proof does
  not use. The theorem is therefore stronger. The change is recorded at the statement.
* The remaining two, `whyburn_9_2` and `jones49_some_order_two`, are open and kept verbatim as
  comments.

## Items

### A. Order: proved

`hasOrder_homeomorph`: a homeomorphism carries open sets to open sets and frontiers to frontiers
(`Homeomorph.image_frontier`), and it preserves `ncard`.

**Check against the books.** Both definitions agree with `OrderLE`/`HasOrder` when the set is the
whole space, as it is in every use here.
* **Menger** (*Kurventheorie*, **Ch. III**, *Die Verzweigungsordnung der Kurvenpunkte*, p. 97; the
  commission's "Ch. IV" is Ch. III):
  > Wir sagen, der Punkt p sei ein Punkt von höchstens n-ter Ordnung der Menge M … wenn p in
  > beliebig kleinen Umgebungen enthalten ist, deren Begrenzungen mit M höchstens n Punkte gemein
  > haben.

  Menger defines "von n-ter Ordnung" (p. 97) as "von höchstens n-ter, aber nicht von höchstens
  (n−1)-ter Ordnung", which is `HasOrder`.
  * *Difference 1:* Menger's set `M` lies in an ambient space. The neighbourhoods are ambient, and
    their ambient boundaries are intersected with `M`. `OrderLE` uses neighbourhoods and frontiers
    in `M` itself.
  * Since the relative frontier of `U ∩ M` lies in `(boundary of U) ∩ M`, Menger's order is at
    least `OrderLE`. Conversely, for a metric ambient space, a relatively open `V` extends to an
    ambient open `U` with the same trace of the boundary, so the two agree. This is not formalized
    and not needed.
  * *Difference 2:* Menger also has "von nullter Ordnung" (p. 98), which is `HasOrder p 0`.
* **Whyburn** (Ch. III §2, p. 48) defines the order of a *set* `X` *relative to a collection* `G`:
  > a subset X of M is said to be of order less than or equal to n in M relative to G provided that
  > if V is any neighborhood of X in M there exists a neighborhood U of X in M with U ⊂ V and such
  > that F(U) is contained in the sum of at most n elements of G.

  For `X = {p}` and `G` the collection of points, this is `OrderLE p n`: Whyburn's
  "neighborhood" is an open set, and `F(U)` is the frontier. Whyburn's plain "order" is this case.

### B. `tscc_homeomorph_circle`: proved

`glue_circle`: two continuous injective arcs `f₁, f₂ : [0, 1] → X` with the same ends, meeting only
in their ends, are glued into the loop `g t = f₁(2t)` on `[0, 1/2]` and `g t = f₂(2 − 2t)` on
`[1/2, 1]`.
* `g 0 = g 1`, so `g` descends to `AddCircle 1` (`AddCircle.liftIco`).
* The induced map onto `range f₁ ∪ range f₂` is a continuous bijection from a compact space to a
  Hausdorff space, hence a homeomorphism.
* `AddCircle 1 ≃ₜ Circle` is `AddCircle.homeomorphCircle`.

This is the converse of batch 148's `tscc_circle`.

### C. Menger's theorem: proved

**`menger_order_two`.** Neither of the commission's two routes is taken in full.
* The theorem on p. 267 rests on the *Kennzeichnung der gewöhnlichen Kurven* (p. 266), the
  `n`-Beinsatz (p. 214) and the classification of ordinary curves (pp. 64 f.). That is longer.
* The route through `circle_char` needs "every two points separate". That turned out to be the hard
  global step, and it is not needed.

Instead, the proof is **Menger's own second argument** on p. 267, used twice. Menger states it for
the arc: the first point of an arc from outside on a curve is a branch point.
1. `locallyConnectedSpace_of_orderLE` (local connectedness from finite order, the commission's first
   step). For `p ∈ V` open with finite frontier, every component of `V̄` meets the frontier of `V`
   by boundary bumping (batch 133's `exists_continuum_bump_closed`). So `V̄` has finitely many
   components, and the one containing `p` is a neighbourhood of `p`. The proof uses only finiteness
   of the frontier.
2. `orderLE_subtype`: order does not increase in a subspace. So **every subcontinuum** of `X` is
   locally connected.
3. `exists_tarc_of_orderLE`: two points of a subcontinuum `K` are joined by an arc in `K`.
   * Take a subcontinuum `W ⊆ K` irreducible between them (batch 83's `exists_irreducible`).
   * `W` is locally connected, so two points of a connected open subset of `W` lie in a continuum
     inside it (`exists_continuum_of_isOpen`).
   * So each other point cuts `W`, i.e. `W` is a cut-point arc, and it is an embedded `[0, 1]`
     (batch 146's `IsCutArc.exists_embedding`).
4. `not_orderLE_two_of_triod`: three connected sets through `p`, pairwise meeting only in `p`, each
   with a further point, give every small open set about `p` three frontier points.
5. `arc_eq_of_legs`: an arc `B ⊆ K` from `a` to `b` fills the continuum `K`, given connected
   nondegenerate legs at `a` and at `b` meeting `K` only there.
   * Otherwise take an arc in `K` from a point of `K − B` to `B`, and its first point `P` on `B`
     (batch 138's `TArc.first_point`).
   * This gives a triod at `P`: two halves of `B` and the new arc if `P` is interior to `B`, or the
     new arc, `B` and the leg if `P = a` or `P = b`.
6. **Main proof.**
   * Take a non-cut point `u` of `X` (batch 94's `exists_two_nonCutPoints`).
   * Take a small open connected `V ∋ u` with frontier `{a, b}`. The frontier has exactly two
     points because `u` is not of order `≤ 1`; connectedness comes from the component of a
     two-point-frontier open set (`frontier_connectedComponentIn_subset`).
   * `a` and `b` are limit points of `X − V̄`: otherwise `V ∪ {a}` would be an open set about `u`
     with frontier `⊆ {b}`.
   * Step 5 with `K = V̄` shows that `V̄` is an arc. The legs are the parts outside `V` of connected
     neighbourhoods of `a` and of `b` (`isPreconnected_diff_of_frontier`).
   * `X − V` is connected: a separation of it would separate `X − u`, using the two halves of the
     arc `V̄` at `u`.
   * Step 5 with `K = X − V` shows that `X − V` is an arc, with the two halves of `V̄` at `u` as legs.
   * So `X` is a `TSCC`, and item B applies.

**`jones49_order_two`**: homogeneity and `hasOrder_homeomorph` make every point of order 2.

### D. Whyburn

**Reading of "separating point of an open set `R`" (`IsSepPointOf`).** Whyburn, p. 61:
> A point p of a locally compact separable metric space L will be called a local separating point
> of L provided p is a separating point of some open set in L.

The proof of (9.1) uses it as follows:
> We have a separation R − p = R_a + R_b, where a and b belong to the component Q of R containing p.

The skeleton's reading matches this. A separation of `R − p` is given by open `A`, `B` covering
`R − p` and disjoint on `R − p`, i.e. relatively open, and it has points on both sides in the
component of `R` containing `p`. §8 uses the same notion for compact `K`: (8.32) characterizes "a
point p of a component C of K be a separating point of K" through "a separation of C − p = C_a + C_b".

**`whyburn_9_1`: proved**, with `hR` dropped. Let `Q` be the component of `R` containing `p`, and
`D = Q − (B − p)`, i.e. Whyburn's `Q·R_a + p`.
* `D` is connected (`isPreconnected_side`) and closed in `R`.
* For a compact neighbourhood `K ⊆ U` of `p`, either `D ⊆ K`, or a continuum through `p` inside
  `D ∩ K` reaches the frontier of `K`. The second case is `exists_continuum_bump_compact`, boundary
  bumping for a compact piece of a connected set.
* Either way, the component of `U` containing `p` meets `A − p` (`whyburn_9_1_side`), and
  symmetrically `B − p`. The same `A`, `B` then separate `U − p`.

**`whyburn_9_2`: open.** **`jones49_some_order_two`: open, reduced to (9.2).** See `OPEN.md`.
* **(9.2)** rests on (8.41) and (8.4), and so on Ch. III §§1–3 and §8: the natural ordering of
  separating points, non-separated cuttings, the cut point-order theorem (3.2), and (8.2), (8.3).
  None of this is in the repository.
* **`jones49_some_order_two_of_whyburn_9_2`** (proved) takes the conclusion of (9.2) for the space
  as a hypothesis. By homogeneity every point is a local separating point
  (`IsLocalSepPoint.homeomorph`, with `Homeomorph.image_connectedComponentIn`), and an uncountable
  space is not countable.
* **A direct proof of `jones49_some_order_two` is not shorter.** One point of order 2 makes every
  point of order 2, by homogeneity, and then `jones49_order_two` makes `X` a circle. So the
  statement already says that `X` is a simple closed curve.
* **Remark (not formalized).** Local separating points have order at least 2 under the skeleton's
  reading. If `p ∈ V` with `V` small and frontier `⊆ {c}`, then both connected sets `Q·R_a + p` and
  `Q·R_b + p` reach the frontier, so `c` lies in both, which is absurd. So the exceptions in (9.2)
  are points of order `> 2`. The statement of (9.2) is not affected.

## Ledger entries (`LEDGER.md` §6, new subsection)

1. **Jones 1949, p. 113:**
   > If a point of M is of order 2 in M, then M is a simple closed curve [4].

   [4] is "Karl Menger, Kurventheorie, Teubner, 1932, p. 267". Menger's theorem needs *all* points
   of order 2. **Homogeneity and the invariance of order are tacit; harmless** (`jones49_order_two`,
   from `menger_order_two` and `hasOrder_homeomorph`).
2. **Menger, p. 267.** The theorem is derived in one sentence ("so ergibt sich aus dem
   Kennzeichnungstheorem folgendes") from three things:
   * the *Kennzeichnung der gewöhnlichen Kurven* (p. 266: a continuum with finitely many branch
     points is an ordinary curve);
   * the remark that the only ordinary curves without branch points are arcs and circles (pp. 64 f.);
   * the characterization of these by their end points.

   The proof of the Kennzeichnung (p. 266) rests on:
   * p. 64 (ordinary curves have finitely many points of order `≠ 2`);
   * p. 127 (an irregular curve has infinitely many irregular points);
   * the `n`-Beinsatz (p. 214);
   * the Lemma of p. 260 (a sub-arc whose interior has no branch point is free).

   **Unargued:**
   * The sharpening of the Lemma of p. 260 to `n`-Beine is only asserted ("folgende Verschärfung
     desselben bewiesen werden kann"). It is the step that makes the `n`-Bein minus its end points
     open.
   * "Je zwei Bogen B′ … haben offenbar höchstens Endpunkte gemein" is asserted as obvious.
   * The finiteness of the components of `B_i′` gets one sentence.

   pp. 262–265 (*beständig reguläre Kurven*) are not used for p. 267 beyond the Lemma of p. 260.
   **The formalization avoids all of this.** It uses Menger's *second* argument on p. 267 (the arc
   characterization by the "Lemma" there: an arc from outside meets the curve first in a point of
   higher order), applied twice in item C.
3. **Whyburn (9.1), proof:**
   > since Q·R_a + p and Q·R_b + p are generalized continua, it follows by [I, (10.2)] that the
   > components V₁ and V₂ of U·(Q·R_a + p) and U·(Q·R_b + p), respectively, containing p are
   > nondegenerate.

   **A boundary-bumping step whose hypotheses are not arranged.** [I, (10.2)] (p. 16) reads:
   > If N is a generalized continuum and G is an open set such that N·G is nonvacuous and different
   > from N and N·G is compact, F(G) contains at least one limit point of each component of N·G.

   * It needs **`N·G` compact**, and `U·(Q·R_a + p)` need not be compact. It also needs `N·G ≠ N`,
     a case not treated (it is trivial).
   * That `Q·R_a + p` is a generalized continuum is asserted. Its connectedness is the classical
     "one side of a cut point, with the point, is connected", and its local compactness holds
     because it is closed in the locally compact `R`.
   * **Supplied:** `isPreconnected_side`, and `exists_continuum_bump_compact` in a compact
     neighbourhood `K ⊆ U` of `p`, which repairs the compactness.
   * The openness of `R` is not used (shape change).
4. **Whyburn (9.2), proof (pp. 61–62).** The steps are:
   * `R₁, R₂, …` is a fundamental (countable) sequence of neighbourhoods.
   * `G_i`, the set of separating points of `R_i`, lies in `G`.
   * Every `p ∈ G` lies in some `G_i`, by (9.1), choosing `p ∈ R_i ⊆ T`.
   * By (8.41), applied to the locally compact `R_i`, all but countably many points of `G_i` are of
     order 2 in `R_i`, "and hence also of order 2 in L".

   **Unargued but routine:** order 2 in the open set `R_i` gives order 2 in `L`, since small
   neighbourhoods with closure in `R_i` have the same frontier in `R_i` and in `L`. **The weight is
   in (8.41)/(8.4)**, which rest on (8.2), (8.3) and the cut point-order theorem (3.2). Not
   formalized: see `OPEN.md`.
5. **Whyburn (8.41):**
   > For we can write L = Σ L_i, where each L_i is open and L̄_i is compact. Then each separating
   > point of L lies in some L_i and is a separating point of L̄_i.

   **Checked; true under the skeleton's reading, but unargued.** A separating point of `L` need not
   obviously separate the compact set `L̄_i` in Whyburn's sense, which requires points of both sides
   in the *component of `p` in `L̄_i`*. It does, by the boundary-bumping argument of (9.1) run in the
   compact neighbourhood `L̄_i` of `p ∈ L_i`:
   * if `D = Q·L_a + p ⊄ L̄_i`, a continuum through `p` in `D ∩ L̄_i` reaches the frontier of
     `L̄_i`, so it is nondegenerate;
   * otherwise `D` itself is such a continuum.

   This uses that `p` is interior to `L̄_i`. Not formalized separately: it is the argument of
   `whyburn_9_1_side`.

## Axioms

`doc/batches/audits/axioms-batch149.txt` lists all 28 theorems declared in the five new files
(including the generated equation lemma `OrderLE.eq_1`). Each uses exactly `propext`,
`Classical.choice` and `Quot.sound`:
* `Jones49Order`: 8 theorems;
* `Jones49Circle`: 2;
* `Jones49Menger`: 10;
* `Jones49Why`: 5;
* `Jones49A`: 3.

`axioms.txt` now has 1128 lines. The only change is 15 added lines, from the new group of
`Axioms.lean`, and `sorryAx` is in none.

## Reading plan for batch 150

**Whyburn 1939, §14** (Theorem, p. 747; Corollary 1, p. 749; `doc/sources/whyburn1939.pdf`). The
Theorem says that the boundary of each complementary domain of a compact semi-locally-connected
plane continuum is locally connected. The proof shows that each complementary domain `R` has
**property S** and then concludes: "by a theorem of R. L. Moore's [Fund. Math. 3 (1922),
pp. 232–237] the boundary of R is locally connected". It also uses:
* Whyburn 1939 (6.22). Not in the repository; batch 136 has (6.1), (6.2), (6.21). It "results at
  once from the proof of (6.2) together with §3".
* "a theorem of R. L. Moore" from F.A. (Trans. AMS 17 (1916)), a simple closed curve `C ⊆ J + C_δ`
  bounding a small region. F.A. §§2–7 is in the repository.
* For a nondegenerate continuum `H` of cut points, **"there exists a point p′ of H·V(p) which is of
  order 2 in M"** (footnote 6: Whyburn, Trans. AMS 33 (1931)). This is the cut point-order theorem,
  the same ingredient (Analytic Topology Ch. III (3.2)) that blocks (9.2) here.

Corollary 1 (cyclic `M`: each boundary is a simple closed curve) is stated without proof. Footnote 16
identifies it with the first corollary of Wilder's Theorem 8a.

**Wilder 1938, Theorem 8a and its first corollary** (p. 196; `doc/sources/wilder1938.pdf`).
* The first corollary reads: "In the plane, if M is a continuum all of whose points are locally
  0-avoidable, then the boundaries of the complementary domains of M are simple closed curves."
* The proof of Theorem 8a is "similar to the proof just given" for Theorem 8. That proof shows the
  domain `D` uniformly locally `i`-connected by the **Alexander Addition Theorem** (Čech/Vietoris
  homology and linking), and concludes by **"Principal Theorem C of G. C. M."** (Wilder, *Generalized
  closed manifolds in n-space*, Annals 1934).
* For `n = 2` this replaces Moore 1922 by Wilder's own boundary theorem plus homological duality in
  the plane. Neither is in the repository, and both are longer than Moore 1922 is likely to be.

**Answer to the question: neither route avoids a "uniformly locally connected domain ⇒ locally
connected boundary" theorem.**
* Whyburn's route cites Moore 1922 (property S) explicitly.
* Wilder's route uses GCM Principal Theorem C with homology, which is heavier.

**Please find Moore 1922** (*Fund. Math.* 3, pp. 232–237). Its content (a bounded plane domain with
property S has a locally connected boundary) is classical, so a direct proof from the repository's
plane topology is a fallback. The commission should say which it prefers.

**Common ingredient.** Whyburn's §14 (footnote 6) and (9.2) both need the **cut point-order theorem**
(Analytic Topology Ch. III, §§1–3: (1.31), (2.2)–(2.22), (3.1)–(3.2)). I propose to formalize
Ch. III §§1–3 and (8.2)–(8.41) once, in batch 150. That closes (9.2) and `jones49_some_order_two`
and supplies footnote 6 of Whyburn 1939 §14. Estimated size:
* about 800–1200 lines for Ch. III §§1–3 and §8;
* about 400 lines for §14 given Moore 1922;
* Moore 1922 (or a direct proof of its theorem): about 400–600 lines.
