# Commission: batch 198 — Part G, I: the circle of pseudo-arcs (Bing–Jones 1959), top down

**Go!** This batch runs on top of the batch-197 work. Three files come with it, as separate
uploads:

* `COMMISSION-batch198.md`: this text, also pasted into the prompt.
* `BJ59A.lean`: the skeleton.
  * Save it as `HPC/BJ59/BJ59A.lean`. You may split it under `HPC/BJ59/`.
  * Add `import HPC.BJ59.BJ59A` at the end of `HPC.lean`. Adjust the skeleton's imports as needed.
  * Save copies under `doc/batches/` (`COMMISSION-batch198.md`, `skeletons/BJ59A.lean`) and
    include them in the tarball, as in batch 197.
* `bingjones1959.pdf`: **new source**, R. H. Bing and F. B. Jones, *Another homogeneous plane
  continuum*, Trans. AMS 90 (1959), 171–192. Save it as `doc/sources/bing-jones1959.pdf`. PDF
  page `n` is journal page `169 + n` (PDF page 1 is a JSTOR cover).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before, including the test of every named `Prop` on
  degenerate inputs.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more (400 dpi for subscripts, primes, tildes and bars), not
  against the text layer.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Bing–Jones 1959, I (batch 198)");
  * `README.md`;
  * `LEDGER.md`: a new section "Bing–Jones 1959 (batch 198)";
  * `OPEN.md`;
  * a new note `doc/notes/bj59.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 197

* **Delivery.** The download was current (`axioms.txt` 3385 lines, equal to the tarball's). The
  commission and skeleton copies are byte-identical to what I sent.
* **Audit.** 209 new theorems (209 lines): 201 on exactly the three standard axioms, eight list
  lemmas on a subset of them; `sorryAx` in none; the eleven new files contain no `sorry`, `admit`
  or `axiom` outside comments; all seventeen skeleton declarations are textually the skeleton's.
* **Results.** Everything proved, stretch included: Theorem 15, Theorem 20, and
  `ho16_indec_homogeneous_pseudoArc` with no named hypothesis, with the two-way form
  `ho16_indec_homogeneous_iff`. **Part F is complete.** Your route changes (a Lipschitz `u`, a
  uniform subdivision, events read off the lists) are improvements. Thank you.
* **Ledger.** HO.29–HO.35 adopted as written; nothing counted; the counts stay at 22 false printed
  statements and 17 defective proofs.

## 1. The plan for Part G

What remains of the classification is the decomposable case. By Jones 1955 Theorem 2 (verified,
`jones55_theorem2'`) a decomposable homogeneous plane continuum `M` has a continuous decomposition
over a circle whose elements are homogeneous indecomposable plane continua; by Part F each
non-degenerate element is a pseudo-arc. Three things are missing, and Bing–Jones supply two:
1. **Uniqueness and homogeneity of circles of pseudo-arcs**: Bing–Jones Theorem 10 and a gluing
   argument that Bing–Jones do not write (§4).
2. **A plane circle of pseudo-arcs**: Bing–Jones §7 (a sketch).
3. **Circle-likeness of `M`**: not in Bing–Jones. Bing–Jones's definition of a circle of
   pseudo-arcs includes circle-likeness, and their uniqueness proof uses it. A continuous
   decomposition into pseudo-arcs over a circle is not enough: Prajs, *A continuous circle of
   pseudo-arcs filling up the annulus*, Trans. AMS 352 (2000), Theorem 8 (p. 1753), gives "a plane
   s-circle of pseudo-arcs", a plane curve with such a decomposition that is triodic, hence not
   circle-like (p. 1753: "the examples constructed here are triodic"). The route I expect goes
   through the terminality of Jones's elements (`jones55_c`) and Lewis, *Continuous curves of
   pseudo-arcs*, Houston J. Math. 11 (1985), which I do not yet have.

This batch works **top down**, as batch 191 did for Theorem C: the three missing pieces become
named `Prop`s (`BJThm10`, `BJPlaneExample`, `HOCircleLike`), and the classification in both
directions is proved from them. Then it starts bottom up on Theorem 10: Bing–Jones §3 and
Theorem 6.

## 2. Definitions (skeleton)

Bing–Jones p. 173: "A continuum G is called an arc of continua {g_x|0≦x≦1} if there is a map f of
G onto [0, 1] such that f⁻¹(x) is the continuum g_x." ; "If in addition, the collection {g_x} is
continuous (f is open), then G is called a continuous snake-like arc of pseudo-arcs."; and of the
circle of pseudo-arcs: "It is a circle-like continuum M such that there is a continuous
decomposition of M into pseudo-arcs such that the decomposition space is a simple closed curve.
Hence, there is an open map f of M onto a circle such that the inverse of each point of the circle
is a pseudo-arc."
* `IsArcOfContinua f` and `IsContArcPA f`, for `f : X → unitInterval`. Snake-likeness of `X` is a
  separate hypothesis (`IsSnakeLike (univ : Set X)`, Bing 1951's notion, in the library).
* `IsCircleOfPA X`: `IsCircleLike (univ : Set X)` (the library's, batch 132) and an open
  continuous map onto `Circle` with pseudo-arc fibres.
* `IsChainMap H` for `H : Fin m → Fin n`: images of adjacent links are adjacent ("A chain map H of
  a chain E into a chain D is a single valued function that assigns a link of D to each link of E
  such that the images of adjacent links are adjacent").

Two differences from Bing–Jones, to be recorded in the ledger and bridged where they matter:
* **Chains.** Bing–Jones require nonadjacent links to be "a positive distance apart" (p. 172), and
  the proof of Theorem 10 uses "chains whose nonadjacent links do not have closures that intersect"
  (p. 189). The library's `Chain` only makes nonadjacent links disjoint.
* **Circle-like.** Bing–Jones: "A compact nonsnake-like continuum which for each positive number ε
  can be covered by an ε-circular chain is called circle-like." The library's `IsCircleLike` omits
  "nonsnake-like". For a circle of pseudo-arcs it is automatic: a snake-like continuum is
  unicoherent (`isUnicoherent_of_isSnakeLike`), and the preimages of two arcs that cover the circle
  are continua meeting in two disjoint fibres. Optional: prove `¬ IsSnakeLike (univ : Set X)` for
  `IsCircleOfPA X`.

## 3. The named inputs (skeleton)

* **`BJThm10`**: Bing–Jones Theorem 10 (pp. 181–182): "Suppose P, Q are continuous snake-like arcs
  of pseudo-arcs {p_x}, {q_x} (0≦x≦1). Then each homeomorphism h that takes the sum of the ends of
  P onto the sum of the ends of Q may be extended to a homeomorphism taking P onto Q. In fact, if
  h(p₀)=q₀, the extended homeomorphism h may be chosen so that h(p_x)=q_x." The skeleton states the
  last sentence: given homeomorphisms of the end fibres, `h₀` over `0` and `h₁` over `1`, there is
  a homeomorphism `H` with `g ∘ H = f` extending both. (The case `h(p₀) = q₁` is the same after
  reversing `g`.)
* **`HOCircleLike`**: a decomposable homogeneous plane continuum is circle-like.
* **`BJPlaneExample`**: some `C ⊆ Pt` is a circle of pseudo-arcs.

Test each on degenerate inputs and say whether any could be refuted as stated. I expect: in
`BJThm10` the hypotheses force `X`, `Y` non-empty with non-degenerate fibres; in `HOCircleLike` a
point is not decomposable (`IsDecomposableSpace` needs two proper subcontinua) and `ConnectedSpace`
excludes `∅`. Do not try to prove these three here.

## 4. From Theorem 10: homogeneity and uniqueness

Bing–Jones p. 173: "It follows from Theorem 10 that any two circles of pseudo-arcs are
topologically equivalent and that each is homogeneous." (Again on p. 189.) Not argued. My route:
1. **Halves.** Let `f : X → Circle` witness `IsCircleOfPA X`, and let `A` be a closed arc of the
   circle with end points `z ≠ z′` (say the image of `[θ, θ + π]` under `Circle.exp`). Then
   `f⁻¹(A)`, with `f` followed by the inverse parametrization of `A`, is a continuous arc of
   pseudo-arcs:
   * the restriction of an open map to the full preimage of a set is open onto that set;
   * `f⁻¹(A)` is a continuum (`f` is monotone and closed);
   * its fibres are those of `f`.
   It is snake-like: it is a proper subcontinuum of the circle-like `X` (it misses the fibres over
   the open complementary arc), so `isSnakeLike_of_subset_circleLike` (Nadler 12.51, batch 132)
   applies. Shape of this lemma left to you (transfers between `Set X` and subtypes included).
2. **Gluing.** Two circles of pseudo-arcs `(X, f)`, `(Y, g)`: cut both circles at `1` and `−1`.
   Pick homeomorphisms `h₊ : f⁻¹{1} ≃ₜ g⁻¹{1}`, `h₋ : f⁻¹{−1} ≃ₜ g⁻¹{−1}`; any two pseudo-arcs are
   homeomorphic (`theorem1_HIC'`). Apply `BJThm10` to the upper halves and to the lower halves
   with these end maps, oriented so that the same end maps are used on both. The two
   homeomorphisms agree on the two cut fibres, so they glue (closed cover) to a continuous
   bijection `X → Y`, a homeomorphism since `X` is compact. That gives
   `homeomorph_of_isCircleOfPA`.
3. **Homogeneity.** Given `x ∈ f⁻¹(z)` and `y ∈ f⁻¹(w)`, cut `X` at `z`, `−z` and the target copy
   of `X` at `w`, `−w`. Over the first cut use a homeomorphism `f⁻¹{z} ≃ₜ f⁻¹{w}` taking `x` to `y`
   (a homeomorphism between the pseudo-arcs composed with one of `f⁻¹{w}` given by
   `homogeneous_of_isPseudoArc`), over the second any homeomorphism. Glue as in step 2: a
   homeomorphism of `X` covering the rotation by `w z⁻¹`, taking `x` to `y`. That gives
   `isHomogeneous_of_isCircleOfPA`.

If you see a simpler route, take it and say so.

## 5. The decomposable case and the classification (skeleton)

* **`isHomogeneous_circle`**: by left multiplication.
* **`isPseudoArc_Lset`** (unconditional): each non-degenerate element `Lset x` of Jones's
  decomposition of a decomposable homogeneous plane continuum is a pseudo-arc. Sketch:
  `jones55_theorem2'` gives `Lset x` connected, homogeneous and non-separating, and
  `jones55_elements_indecomposable'` gives indecomposability, and `jones55_isContinuum` that
  `Lset x` is a continuum. `isPseudoArc_of_indec_homogeneous ho16_theorem20` takes a set in `Pt`:
  apply it to `Subtype.val '' Lset x` and transfer the result back to `Lset x ⊆ M`.
* **`circle_or_circleOfPA_of_decomposable`** (from `HOCircleLike`).
  * By homogeneity either every `Lset x` is a point or none is (`jones55_b`, and homeomorphisms
    permute the `Lset`s).
  * If every one is a point, the quotient map is a continuous bijection onto the quotient, and
    `jones55_theorem2'` makes that a circle.
  * Otherwise the quotient map, followed by the homeomorphism onto `Circle`, is open (continuity of
    the decomposition; say which library fact gives openness) with pseudo-arc fibres
    (`isPseudoArc_Lset`). `HOCircleLike` supplies circle-likeness.
* **`ho16_classification`** (from `BJThm10`, `HOCircleLike`).
  * Forward: indecomposable gives a pseudo-arc (`ho16_indec_homogeneous_iff`); decomposable gives
    the previous item.
  * Backward: the circle (`isHomogeneous_circle` and `isHomogeneous_of_homeomorph`), the pseudo-arc
    (`ho16_pseudoArc_indec_homogeneous`), circles of pseudo-arcs (§4).
* **`ho16_classification_plane`** (from all three): `C₁` any plane simple closed curve, `C₂` the
  plane pseudo-arc (`isPseudoArc_plane`), `C₃` from `BJPlaneExample`. The rest is
  `ho16_classification` and `homeomorph_of_isCircleOfPA`, with three distinctness facts:
  * a pseudo-arc is indecomposable, while the circle and a circle of pseudo-arcs are decomposable
    (two arcs, resp. the preimages of two arcs);
  * the circle is not a circle of pseudo-arcs (its proper non-degenerate subcontinua are arcs,
    while a fibre of a circle of pseudo-arcs is a proper non-degenerate subcontinuum containing no
    arc).
  State the distinctness lemmas as you find convenient.

## 6. Bing–Jones §§3–4, first part (skeleton)

* **Theorem 1** (p. 174), "Each snake-like continuum is unicoherent", is in the library as
  `isUnicoherent_of_isSnakeLike` (`HPC/Plane/Theorem11.lean`, Nadler 12.2), with the recorded
  shape change that the ambient space is compact. Add it to this batch's audit file and record it
  in the ledger; nothing else to do.
* **Theorem 2** (p. 174), `bj_theorem2`. The printed proof leaves one step: "If j<i<t, G(b, c)
  intersects d_i because G(b, c) is connected and intersects each of d_j and d_t." That `G(b, c)`
  meets `d_t` holds if `D′`, `D″` are all the links meeting `G(0, b)`, `G(c, 1)`: `d_t` then meets
  `G` (the links meeting the connected `G` are consecutive) and meets neither of those two sets.
* **Theorem 3** (pp. 174–175), `bj_theorem3`. The printed construction ends "Use A to denote the
  sum of the elements of F(1, v) and B to denote the sum of the elements of F(v, m). Then the
  elements of D are A·e_i, A·e_{i+1}, ⋯, A·e_j, f_{v+1}, f_{v+2}, ⋯, f_{w−1}, B·e_r, B·e_{r+1},
  ⋯, B·e_s." My reading (400-dpi crop): `F(v, m)` is a misprint for `F(w, m)`, by the symmetry
  with `A` (`F(1, v)`) and the preceding sentence, "E(r, s) covers each link of F(w, m)". Even so
  `D` is not a chain as written: `A·e_{j−1}` can meet `f_{v+1}` (through `f_v ∩ f_{v+1} ∩ e_{j−1}`,
  as `f_v ⊆ e_j`), and they are not adjacent in `D`; the same happens at `B·e_{r+1}` and `f_{w−1}`.
  So the construction needs repair at both junctions, and that `D` is an `ε`-chain from `g₀` to
  `g₁` is not argued. The statement is not in doubt; any proof will do.
* **Theorem 4** (p. 175), `bj_theorem4`: "each neighborhood of p which does not intersect g₀+g₁
  separates g₀ from g₁ in G", for any point `p` of `U`. Bing–Jones's proof splits `G − U` at a link
  `d_i ⊆ U` of a chain from Theorem 3.
* **Theorem 6** (p. 176), `bj_theorem6`: the fixed-point lemma for chain maps, on indices. As
  printed, each map "takes a link of D into e_{m−1}", the next-to-last link (index `m − 2`).
* **Theorem 5** (pp. 175–176): "Suppose G is a snake-like arc of indecomposable continua
  {g_x|0≦x≦1} and E is a chain covering G such that E properly covers each g_x. Then if U is an
  open set such that U·G≠0, U·(g₀+g₁)=0, and Ū lies in a link of E, then G−U may be expressed as
  the sum of two mutually separated sets A, B such that g₀⊂A, g₁⊂B, and for each x (0≦x≦1),
  either A·g_x intersects each link of E or B·g_x intersects each link of E." **As printed this is
  false**, and not only in degenerate cases (found by the independent check of this commission):
  * *Degenerate.* `X = [0, 1]`, `f = id` (a point is an indecomposable continuum in the library's
    sense, `Fold.Q78.IsIndecomposable`), `E` one link, `U = (1/4, 3/4)`, `x = 1/2`: `A·g_x` and
    `B·g_x` are empty.
  * *General.* Take any instance with `n ≥ 3` links properly covering every fibre. Merge the last
    two links: `e_k = e′_k` (`k ≤ n − 2`), `e_{n−1} = e′_{n−1} ∪ e′_n`, `e_n = e′_n`. This is
    still a chain (in Bing–Jones's sense too), covering `G` and properly covering every fibre, and
    `cl(e_n) ⊆ e_{n−1}`. For `0 < c < 1` let `U` be a small neighbourhood of `cl(g_c ∩ e_n)` with
    `Ū ⊆ e_{n−1}` and `U` missing `g₀ + g₁`. Then `g_c − U` misses `e_n`, so the conclusion fails
    at `x = c` for every separation. No fibre lies in `U`, so neither "four links" nor "no fibre in
    `U`" repairs it: the failure is that a fibre meets a link only inside `Ū`.
  * *The printed proof* passes from separations of `G − d_j` to separations of `G − U`; `A₁·g_x`
    can meet `e_n` only inside `U`. Bing–Jones's use on p. 185 is existential ("By Theorem 5 there
    is an open set U_i in P(i/n, i/n+ε)·f_y such that …"), so a repaired form serves.
  * *The skeleton's repair*, `bj_theorem5` (stretch): `f` open (the application is inside a
    continuous arc), and `hEU`: no fibre meets a link only inside `Ū` (this implies proper
    covering). Proof sketch (from the check): suppose it fails; take Theorem-3 chains `D_j` of mesh
    tending to `0` with links `d_j ∋ p`, `d_j ⊆ U`; each separation of `G − U` by the links before
    and after `d_j` fails at some `c_j`; pass to a subsequence with `c_j → c`, the two failing link
    indices fixed and the before/after parts of `g_{c_j} − d_j` convergent; openness gives
    `g_{c_j} → g_c`; the limits are continua covering `g_c`, so one of them is `g_c`
    (indecomposability); `hEU` gives a point of `g_c ∩ e_α` off `Ū`, near which the before-part
    meets `e_α` off `U`, a contradiction. Report what you find; a refutation is as welcome as a
    proof.
  * *Certificates*: `bj_theorem5_printed_false` (skeleton; the degenerate example), and, optional,
    the general construction as a lemma: from any instance with `n ≥ 3`, a chain and an open set
    meeting the printed hypotheses for which the printed conclusion fails.

## 7. Ledger: Bing–Jones 1959

New section "Bing–Jones 1959 (batch 198)", items BJ.1, BJ.2, …, each with the printed text quoted
from the page images. My second reading (200 dpi; the items marked (400) checked on 400-dpi crops)
gives the list below; confirm or correct each, and add what you find. Theorems 7–10 and §7 are not
formalized yet: record those items now as readings, to be revisited when those sections are done.
1. **p. 173 (400)**: "In Theorem 10 we show that any two continuous snake-like arcs of pseudo-arcs
   of homeomorphic": `of` for `are`.
2. **pp. 173, 189**: the passage from Theorem 10 to circles, unargued (§4 supplies it).
3. **p. 174, Theorem 2**: the step about `d_t` (§6).
4. **p. 175, Theorem 3 (400)**: `F(v, m)` for `F(w, m)`; the chain needs repair at both junctions
   and is left to the reader (§6).
5. **pp. 175–176, Theorem 5**: false as printed, in general (§6). The printed proof confuses
   separations of `G − d_j` with separations of `G − U`. **A candidate for the count** (a false
   printed statement, the twenty-third), pending your certificate and your judgement; Theorem 10,
   which uses it existentially, is not affected.
6. **p. 177, Theorem 7 (400)**: "Let p₁, p₂ be points of different components of P in d₁−d₂,
   d_n−d_{n−1}": `components` for `composants` (`P` is connected; Bing 1948's descriptions run
   between points of different composants; compare p. 179: "p₁, p₂ belong to different composants
   of P" and "q₁, q₂ are points of different composants of Q in e₁−e₂ and e_n−e_{n−1}").
7. **p. 178, Theorem 8 (400)**: "Let U_A, U_B be open sets with closures in d₁, d₂ respectively":
   `d_n` for `d₂` (the proof needs `Ū_B·p_a⊂e(a)_m` with `H(y_m)=d_n`). Unargued: "It follows from
   Theorem 4 that P is covered by open sets U₁, U₂, ⋯, U_t such that U_i·U_j=U_A+U_B if i≠j and if
   p_x·(U_i−(U_A+U_B))≠0, then x∈I_{a_i}" (Theorem 4 gives one separation at a time), and "Then the
   chain E whose kth link e_k=e(a₁)_k·U₁+e(a₂)_k·U₂+ ⋯ +e(a_t)_k·U_t is the required chain". My
   reading: for `i ≠ j` the sets `e(a_i)_k·U_i` and `e(a_j)_l·U_j` can meet inside `U_A+U_B` for
   nonadjacent `k`, `l` (when `H` sends `y_k` and `y_l` into the same end link), so the links may
   need shrinking. To be checked when Theorem 8 is formalized.
8. **p. 180, Theorem 9 (400)**: "`and the links of G with closures in e_{n−1}·e_n are combined to
   form e′_{4n−6}, e′_{4n−5}, e′_{4n−4}`": `F` (the chain covering `Q`) for `G` (the chain covering
   `P`, introduced in the next paragraph). (Quotations with a prime before a subscript are in code
   spans only so that Markdown keeps the underscores.) In the next paragraph: "`d₂′ is the sum of
   the other links of G in e₁−e₂; d₄′, d₅′, d₆′ are formed by combining links of G in e₂−(e₁+e₃),
   ⋯, d′_{4n−4} is the sum of the other links of G in e_n−e_{n−1}`": `d` for `e` throughout (`G`
   covers `P` and refines `D`). Unargued: the last display ends "`⊂ē_i`", where the claim is
   "h(P·d_i)⊂e_i".
9. **p. 181 (400)**: "Let E₂ be any G_i of mesh less than 1/3 that refines E_i and H₂ be any chain
   map of E₂ onto E₁ such that e²_j⊂H₁(e²_j)": `E₁` for `E_i`, `H₁` for `H₂` (by (3), `H_i` maps the
   `(i+1)`-st chains onto the `i`-th). Also "d²_j⊂d¹_k=H₁(d²_j) if H₁(e²_j)=d¹_k": `e¹_k` for the
   last `d¹_k` (compare "e³_j⊂e²_k=H₂(e³_j) if H₂(d³_j)=d²_k" below and (3)). Unargued: "That h is a
   homeomorphism of P onto Q follows from an argument similar to that contained at the end of the
   proof of Theorem 10 of this paper or in Theorem 11 of [3]."
10. **p. 182 (400)**: "E₁, D₁, H₁, E₂, K₁, D₂, H₂, E₃, K₃, ⋯": `K₂` for `K₃`.
11. **p. 185 (400)**: "R_{(2i+1)/n}(f_y)" for `R_{(2i+1)/2n}(f_y)`; "`P(0, 1/n−ε)⊂A′_i`" for
   `P(0, i/n−ε)`.
12. **p. 186 (400)**: "link of the subchain of E_k that irreducibly covers Q(i/n, (i+1)/n)": `E₁`.
13. **pp. 187–188, Theorem 10**: Step 3, Conditions I and II "similar to" Step 2; "Steps 4, 5, ⋯.
    These steps are essentially repetitions of Step 3." Unargued by analogy. (p. 187, "intesects":
    typography.)
14. **p. 189 (my reading)**: "so ρ(p, q)<4/2^i": the meshes give `8/2^i`. Harmless.
15. **§7, pp. 189–191**: a sketch. "Now there exists a sequence D₁, D₂, D₃, ⋯ of circular chains of
    simple domains in the plane such that" (1)–(9): asserted, not constructed; "With the addition of
    (9) one may see with the help of [3] that each element of G is a pseudo-arc. It follows from
    Theorem 10 that M is homogeneous." Covering `M` by fine circular chains follows from (1)–(3);
    not argued: that `M` is not snake-like, that `G` is a continuous decomposition over a circle,
    and that each element is a pseudo-arc.
16. **Definitions**: the two differences of §2.

Count nothing yet unless something printed is false about the objects of a proof (as HO.25); say
which items, if any, you would count.

## 8. Non-vacuity

* `BJThm10`: its hypotheses are met by the halves of any circle of pseudo-arcs (§4, step 1), so by
  `BJPlaneExample`; no unconditional example is asked for.
* `circle_or_circleOfPA_of_decomposable`, `ho16_classification`: hypotheses met by a plane circle
  (decomposable, homogeneous).
* `isPseudoArc_Lset`: a plane circle does not meet its hypotheses (the circle is aposyndetic, so
  `Lset x = {x}`); only a circle of pseudo-arcs does, so a witness is conditional on
  `BJPlaneExample` and on identifying its Jones elements with its fibres. No witness is asked for;
  say what it would take.
* `bj_theorem2`–`bj_theorem4`: `X = [0, 1]` with `f = id` (fibres points) meets every hypothesis;
  give it as an example.
* `bj_theorem5` (repaired): with point fibres `hEU` fails for any non-empty `U`, so the
  hypotheses need non-degenerate indecomposable fibres; the halves of a circle of pseudo-arcs, with
  `U` small, would do (so `BJPlaneExample`). No unconditional example is asked for; say if you find
  a simple one.
* `bj_theorem6`: a two-map example with `n = m = 3`.

## 9. Order

§2–§3 first (definitions, named `Prop`s and their tests), then §5's unconditional items
(`isHomogeneous_circle`, `isPseudoArc_Lset`), §4, the rest of §5, and §6 (Theorems 2, 3, 4, 6, then
5). §7 alongside.

## 10. Deliverables

1. **The items of §2–§8.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch198.txt`, with
     `isUnicoherent_of_isSnakeLike` added (§6).
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section of §7.
3. **Notes:** `doc/notes/bj59.md`: the plan of Part G and what this batch proved, in a few
   paragraphs.
4. **Publish the changes, as in batch 197**: `doc/batches/batch198-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies and the new source) and
   `doc/batches/batch198-MANIFEST.txt`.
5. **The report.** Its first line names the commission it read. It covers the items in order, the
   non-vacuity notes, the ledger entries, the axioms used by each theorem, the dependency map of
   `ho16_classification_plane`, and comments on the three named inputs: what each will need, and
   whether anything in the library already bears on `HOCircleLike`.
