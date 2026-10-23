# Commission: batch 197 — H–O Theorem 1, V: Theorem 15 (ladders), and the end of Part F

**Go!** This batch runs on top of the batch-196 work. Two files come with it, as separate uploads:

* `COMMISSION-batch197.md`: this text, also pasted into the prompt.
* `HO16E.lean`: the skeleton.
  * Save it as `HPC/HO16/HO16E.lean`. You may split it under `HPC/HO16/`.
  * Add `import HPC.HO16.HO16E` at the end of `HPC.lean`. It imports `HPC.HO16.HO16D`.
  * Save copies under `doc/batches/` (`COMMISSION-batch197.md`, `skeletons/HO16E.lean`) and
    include them in the tarball, as in batch 196.

No new sources. Page numbers are the journal's; PDF page `n` of
`doc/sources/hoehn-oversteegen2016.pdf` is journal page `176 + n`. H–O print the star as a
subscript; the quotations below write it on the line.

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
  * `Axioms.lean` and `axioms.txt` (new group "H–O Theorem 1, V (batch 197)");
  * `README.md`;
  * `LEDGER.md`: the section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)";
  * `OPEN.md`;
  * `doc/notes/ho16.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 196

* **Delivery.** The download was current (`axioms.txt` 3176 lines, equal to the tarball's). The
  commission and skeleton are now under `doc/batches/`, byte-identical to what I sent. Thank you.
* **Audit.** 232 new theorems (234 lines; one wrapped), all on exactly the three standard axioms;
  `sorryAx` in none; the fourteen new files contain no `sorry`, `admit` or `axiom` outside
  comments; all ten skeleton declarations are textually the skeleton's.
* **Results.** Everything proved, stretch included: Proposition 19, the certificate of p. 208,
  and Theorem 20 and the classification step from `HOThm15`. Discharging the auxiliary `HOProp19`
  inside the batch is fine.
* **Ledger.** HO.23–HO.28 adopted; HO.25 counted (the seventeenth defective proof). Two
  additions for HO.23 and HO.24, both confirmed on 400-dpi crops of p. 207: in the (S4) paragraph,
  "`Also, we have C⊂F₃\φ⁻¹(π(S_{i₀})), since S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆`": the second
  `φ⁻¹`, the one applied to `S_{i₀}`, is a third `φ⁻¹` for `φ⋆⁻¹`; and the start of the line in
  (S3) does read "`P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂) agree`", `P′₂` for `π(P′₂)`. Please record both.
  (The quotations are in code spans only so that Markdown keeps the underscores.)

## 1. The plan

`HOThm15` (H–O Theorem 15, for connected PL graphs) is the only open input of Part F. This batch
proves it by a route that replaces H–O's Claim 15.1 and makes their zig-zag construction
explicit:
1. **Ladders** (§2): a combinatorial description of a separator-like set over a decomposition of
   `G`, with at most one "wedge" per edge.
2. **A ladder carries a stairwell structure of odd height** (§3, `ho16_stairwell_of_ladder`):
   H–O pp. 196–198 (the sheets `S_i^{[a,b]}`, the zig-zags, (S1)–(S5)) in explicit form.
3. **Stretch** (§5): inside any open `U` containing a separator there is a ladder
   (`exists_ladder`, replacing Claim 15.1); then `ho16_theorem15 : HOThm15`,
   `ho16_theorem20 : HOThm20`, and **`ho16_indec_homogeneous_pseudoArc` with no hypothesis**: every
   indecomposable non-degenerate homogeneous plane continuum is a pseudo-arc (H–O p. 180); with
   the converse (Bing), `ho16_indec_homogeneous_iff`.

§3 first; §5 if time remains.

## 2. Ladders

**H–O's construction** (pp. 196–197). After Claim 15.1 they fix a finite `Z′ ⊆ G` such that "the
closure of every component of G\Z′ is an arc", and such that over each arc `[a, b]` the
separator `M′` consists of graphs of functions over `[a, b]` and at most one side wedge `W`. At
each `a ∈ Z′`, "Let M′∩{a}⋆={(a,y₁), ..., (a,y_j)}, where j⩽k is odd, and y₁<y₂<...<y_j"; the
sheets are built so that `S_i` passes through `(a, yᵢ)`. Over an arc with a wedge (H–O take
`a ∈ π(W)`), the curves above the wedge change their rank by two between `a` and `b`, and each
gets a "zig-zag": "For each i=m+2, ..., j, let J_i⊂[a,b] be a closed subarc such that
J_i∩π(W)=∅, and J_{i+1} is between J_i and b for each i=m+2, ..., j−1. For each i=m+2, ..., j, in
a small neighborhood of C_i in U, define three arcs C_i¹, C_i², and C_i³ such that • π is
one-to-one on C_i^p for each p=1, 2, 3; • C_i¹ and C_i² have a common endpoint, and C_i² and C_i³
have a common endpoint, but these three arcs are otherwise pairwise disjoint;
• C_i¹∩{a}⋆=C_i∩{a}⋆ and C_i³∩{b}⋆=C_i∩{b}⋆; • π(C_i²)=J_i=π(C_i¹)∩π(C_i³)." The wedge
halves `W_m`, `W_{m+1}` start `S_m`, `S_{m+1}`; then `C_i¹` goes into `S_i`, `C_i²` into `S_{i−1}`
and `C_i³` into `S_{i−2}` (p. 197).

**The ladder** (`IsLadder G S y ev`) records exactly the data this construction needs, with the
wedge put at the second end of its edge (we orient edges as we like):
* `S` a decomposition of `G` (as in `IsPLGraph`, oriented: `s = (s.1, s.2)`);
* at each vertex `v`, a list `y v` of heights in `(0, 1)` of **odd** length `j(v)` (not
  necessarily sorted: nothing below needs the order);
* on each edge `s`, either `ev s = none` (then `j(s.1) = j(s.2)`), or `ev s = some (m, λ, h)`: a
  wedge at `s.2`, `j(s.2) = j(s.1) + 2`, `1 ≤ m ≤ j(s.1) + 1`, the wedge taking places `m`, `m + 1`
  at `s.2`, its tip `(lineMap s.1 s.2 λ, h)` over the point of parameter `λ ∈ (0, 1)` of `s`, at
  height `h ∈ (0, 1)`.

**The sheets** (`ladderPiece`, `ladderSheet`), with `j = j(s.1)`, `yᵢ(v) = ladderY y v i`:
* no event: the segment from `(s.1, yᵢ(s.1))` to `(s.2, yᵢ(s.2))`, for `1 ≤ i ≤ j`;
* wedge `(m, λ, h)`:
  * `i < m`: the segment from `(s.1, yᵢ(s.1))` to `(s.2, yᵢ(s.2))`;
  * the curve of rank `i ≥ m` at `s.1` is the line `Lᵢ` from `(s.1, yᵢ(s.1))` to
    `(s.2, yᵢ₊₂(s.2))`, with zig-zag interval `[lᵢ, rᵢ]` in parameters,
    `lᵢ = λ(2(j − i) + 1)/(2(j − m) + 3)`, `rᵢ = λ(2(j − i) + 2)/(2(j − m) + 3)`, so that
    `0 < l_j < r_j < l_{j−1} < … < l_m < r_m < λ`;
  * `C¹ᵢ = Lᵢ[0, rᵢ]` goes into sheet `i`, `C²ᵢ = Lᵢ[lᵢ, rᵢ]` into sheet `i + 1`,
    `C³ᵢ = Lᵢ[lᵢ, 1]` into sheet `i + 2`;
  * the wedge halves, segments from the tip to `(s.2, y_m(s.2))` and to `(s.2, y_{m+1}(s.2))`,
    go into sheets `m` and `m + 1`.

So the ladder is H–O's picture mirrored (wedge at the end of the edge, zig-zags before the tip),
with two simplifications: the three arcs of a zig-zag lie **on one line** (they overlap;
Definitions 12–13 do not forbid sheets to meet; compare the caption of Figure 11, p. 204, for a
broken stairwell structure: "Note that S′₁ and P′₁ overlap in a segment in (F₂)⋆"), and nothing
needs to separate: the end sets come out of the construction (§3). Because the sheets overlap,
H–O's choice "β_i=α_{i+1}=S_i∩S_{i+1}" (p. 198) is not available; the `α` is given explicitly
(§3). The height is `ladderHeight S y`, the longest list.

## 3. A ladder has a stairwell structure of odd height

`ho16_stairwell_of_ladder`: if `IsLadder G S y ev` and `S ≠ ∅`, then `k = ladderHeight S y` is
odd and `⟨ladderSheet 1, …, ladderSheet k⟩` is a stairwell structure of height `k` for their
union, for some `α`. My reading, checked by hand (and on the example of §6, below):
* **The `α`.** On a wedge edge, with `L_i(μ)` the point of `Lᵢ` at parameter `μ`:
  `α_i` collects `L_{i−1}(r_{i−1})` (the common right end of `C¹_{i−1}` and `C²_{i−1}`; if
  `m ≤ i − 1 ≤ j`), `L_{i−2}(l_{i−2})` (the common left end of `C²_{i−2}` and `C³_{i−2}`; if
  `m ≤ i − 2 ≤ j`) and the tip (if `i = m + 1`); no other points, and no points on edges without
  events. Then `α₁ = ∅` and `α_{k+1} = ∅` (a wedge edge has `j(s.1) ≤ k − 2`).
* **(S1).** Over an edge, the pieces of sheet `i` lie over the parameter intervals `[0, rᵢ]`,
  `[l_{i−1}, r_{i−1}]`, `[l_{i−2}, 1]` and (for `i ∈ {m, m + 1}`) `[λ, 1]`, which are pairwise
  disjoint; over a vertex `v`, every edge at `v` contributes the same point `(v, yᵢ(v))` when
  `i ≤ j(v)`, and none otherwise. So `π` is injective on each sheet; `π(S_i)` is a finite union
  of nondegenerate segments (`isPLGraph_biUnion`); a vertex with `j(v) = k` gives every sheet a
  point. No segment of a piece is vertical (its ends lie over different parameters).
* **(S2).** A vertex `v` is interior to `π(S_i)` if `i ≤ j(v)` (every edge at `v` has a piece of
  sheet `i` starting at `v`) and outside it otherwise; so `∂π(S_i)` consists of the parameters
  where pieces stop inside edges: the `rᵢ`, the `l_{i−1}`, `r_{i−1}`, the `l_{i−2}` and the tip.
  These are exactly the points of `α_i ∪ α_{i+1}`, and they lie in `S_i`.
* **(S3).** At each point of `β_i = α_{i+1}`, the two sheets leave in the same direction:
  `C¹ᵢ` and `C²ᵢ` both end at `rᵢ` from the left; `C²_{i−1}` and `C³_{i−1}` both start at
  `l_{i−1}` to the right; the two wedge halves both start at the tip. Every other piece of the two
  sheets on that edge is at positive distance.
* **(S4).** Components `C` of `G \ π(S_i)`. Inside one edge: the gaps `(rᵢ, l_{i−1})` (both ends
  in `β_i`), `(r_{i−1}, l_{i−2})` (both in `α_i`), and, when `m ≤ j`, for `i = m`, `m + 1` the gaps
  next to the tip (both ends in `β_m`, resp. both in `α_{m+1}`; when the piece before the tip is
  missing, the gap belongs to the component of `s.1`, treated next). A component containing a
  vertex contains only vertices with `j(v) < i`; its frontier lies on wedge edges `s` with `s.1`
  such a vertex and `j(s.1) < i ≤ j(s.1) + 2`, at the first piece of sheet `i` from `s.1`; that
  end point is in `β_i` if `i − j(s.1) = 1` and in `α_i` if `i − j(s.1) = 2`. **All `j(v)` are
  odd**, so which of the two occurs depends only on the parity of `i`: the frontier of `C` lies in
  `π(β_i)` (`i` even) or in `π(α_i)` (`i` odd). This is H–O's parity argument of p. 198 ("Then
  j_p is odd for all p=1, ..., n … we must have that j₁ and j_n have the same parity and, hence,
  j₁=j_n"). Since
  `π(α_i)` and `π(α_{i+1})` are disjoint and every frontier lies in one of them, both halves of
  (S4) (`HasConsCompl` for `π(α_i)` and for `π(α_{i+1})`) follow.
* **(S5).** All end points lie over interior points of edges, which are ordinary
  (`isOrdinaryPt_iff_order`), at pairwise different parameters.

Connectedness of `G` is not needed. The lists need not be sorted, and the heights need not be
distinct.

## 4. Ledger: H–O's proof of Theorem 15 (pp. 194–198)

New items from HO.29 on:
1. **Claim 15.1** (p. 195): "We leave it to the reader to show that there exists a set M′ having
   properties (1), (3), (5), and (6), and which separates G×{0} from G×{1}." The main construction
   of the proof, unargued. Then: "Replacing M′ by a subset (which, by abuse of notation, we also
   denote by M′) which irreducibly separates G×{0} from G×{1} in G⋆ accomplishes (2)"; that the
   subset keeps (1) and (3) is not argued. Replaced on this route by `exists_ladder` (§5).
   Also on p. 195, in the definition of a side wedge: "C₂ are arcs which both have x as an
   endpoint but are otherwise disjoint" (400-dpi crop): `x` for `(x, y)` (the arcs lie in `G⋆`).
   A misprint. And in the paragraph on property (4): "Note that (x,y) cannot be an endpoint of M′,
   because x is not an endpoint of G by (5), and π(M′∩V) is open for some neighborhood V of (x,y)
   by (3)": here `(x, y) ∈ T`, and (3) speaks only of points of `M′\T`, so it does not give the
   openness at `(x, y)`; irreducible separation does (an end of `M′` could be trimmed). A wrong
   reason for a true step.
2. **pp. 195–196, branch points of `M′`.** "Because M′ is an irreducible separator, the
   complementary regions of M′ in D alternate between R₀ and R₁. It follows that n is even.";
   "Obviously this can be done without compromising properties (1), (5), and (6), and without
   leaving U."; "It is easy to see that the resultant M′ still irreducibly separates G×{0} from
   G×{1} in G⋆." Unargued; not used on this route (a ladder has no branch points other than over
   vertices of `G`, where it is straight).
3. **p. 196**: "Observe that since Z′∩π(T)=∅ and since M′ irreducibly separates G×{0} from G×{1},
   for each point a∈Z′, the set M′∩{a}⋆ contains an odd number of points." Unargued; on this route
   the odd counts come from sign changes (§5).
4. **p. 197**: "Clearly W∩{a}⋆ consists of two consecutive points"; "Observe that M′∩{b}⋆ contains
   exactly j−2 points"; "Observe that S is in U, and clearly S irreducibly separates G×{0} from
   G×{1}, because M′ does." The last is not argued (`S` is not `M′`: the zig-zags are added) and is
   not needed: H–O use it on p. 198 for "there are no other points in the end sets of the S_i's
   because S irreducibly separates G×{0} from G×{1} in G⋆", which on this route follows from the
   construction (§3, (S2)).
5. **p. 198**: "It is clear that S_i^{[a,b]} is straight"; "Properties (S3) and (S5) are immediate
   from the construction."; "It is now easy to see that each of x₁ and x₂ corresponds to the tip
   point of a side wedge or a turning point of a zig-zag joining S_{j₁−1} and S_{j₁}." Unargued;
   supplied in explicit form by §3. The construction itself is right (the independent check of
   this commission agrees: the `J_i` ordered from `π(W)` toward `b`, `C¹_i`, `C²_i`, `C³_i` into
   `S_i`, `S_{i−1}`, `S_{i−2}`), with one unstated condition: nothing excludes `b ∈ J_j`, and then
   `C¹_j` reaches `{b}⋆`, against "S_i^{[a,x]}∩{a}⋆=∅ if i>j" and possibly (S5); the `J_i` must
   lie in the open arc. In the (S4) argument, "Since a_i∈C for p=2, ..., n−1" has `a_i` for `a_p`
   (a misprint); the case split ("If C⊂[a,b] …"; "Suppose, on the other hand, that x₁,x₂∈∂C do not
   belong to the same component of G\Z′") omits a component not inside one arc whose frontier
   points lie on one arc (around a cycle of `G`); the same chain argument covers it. And
   "|M′∩{z}_*|<i" prints an asterisk for the star (400-dpi crop); typography only. Record your own
   judgement of each.
6. **p. 198, Figure 8**: "We leave it to the reader to observe that this set S irreducibly separates
   G×{0} from G×{1}." Figure-based; optional, in words.
7. **The cited theorem** (pp. 194–195): "It is well known (see e.g. [26, Theorems 46.VII.3 and
   49.V.3]) that for any set S⊂G×(0,1) which separates G×{0} from G×{1}, there is a closed set
   S′⊆S which irreducibly separates G×{0} from G×{1}." Not used on this route; record.

## 5. Stretch: a ladder inside `U`, Theorem 15, and the end of Part F

**`exists_ladder`** (replacing Claim 15.1). Data: `G` a connected PL graph, `M ⊆ G × (0, 1)`
separating `G × {0}` from `G × {1}` in `G⋆` (open sets `O₀ ⊇ G × {0}`, `O₁ ⊇ G × {1}` of
`SeparatesIn`), `U` open with `M ⊆ U`. My route:
1. **A sign function.** `K = G⋆ \ (U ∩ (E × Ioo 0 1))` is compact, `K ⊆ G⋆ \ M ⊆ O₀ ∪ O₁`; put
   `K₀ = K \ O₁ ⊇ G × {0}` and `K₁ = K \ O₀ ⊇ G × {1}`: disjoint, compact, `K = K₀ ∪ K₁`. Let
   `u = infDist · K₀ − infDist · K₁`. Then `u < 0` on `K₀`, `u > 0` on `K₁`, and
   `ω = min_K |u| > 0`, so `{p ∈ G⋆ : |u p| < ω} ⊆ U ∩ G × (0, 1)`.
2. **A grid.** By uniform continuity on `G⋆`, take `δ > 0` with `|u p − u p′| < ω/2` when
   `dist p p′ < δ`. Take a decomposition `S₀` of `G` with edges shorter than `δ` (subdivide) and
   `N` with `1/N < δ`, heights `t_q = q/N`. Then every rectangle `s₀ × [t_q, t_{q+1}]` with a
   corner where `u ≤ 0` and a corner where `u > 0` lies in `{|u| < ω}`, hence in `U`. Put
   `σ(v, q) = −1` if `u(v, t_q) ≤ 0`, else `+1`; so `σ(v, 0) = −1` and `σ(v, N) = +1` (`u < 0` on
   `K₀`, `u > 0` on `K₁`).
3. **Heights at vertices.** `y v` = the midpoints `(t_q + t_{q+1})/2` of the `q` with
   `σ(v, q) ≠ σ(v, q + 1)`, in increasing order: an odd number (the signs go from `−` to `+`).
   Ranks below refer to this order (§3 does not need it; this construction does).
4. **One flip per edge.** For an edge `s₀ = (v, w)` of `S₀`, let `q₁ < … < q_r` be the `q` with
   `σ(v, q) ≠ σ(w, q)` (`0 < q < N`). Subdivide `s₀` into `r` edges (one edge if `r = 0`); the
   sign sequence at the `p`-th new vertex is that of `v` with `q₁, …, q_p` flipped, and its list is
   given by step 3. Each new edge flips one `q`, which changes the sign changes at `q − 1|q` and
   `q|q + 1`:
   * one appears and the other disappears: one curve moves from `(t_{q−1} + t_q)/2` to
     `(t_q + t_{q+1})/2` or back, no other curve moves, ranks are kept: `ev = none`;
   * two appear: a wedge at the far end, `ev = some (m, ½, t_q)` with `m` the rank of the new lower
     curve there;
   * two disappear: a wedge at the near end; orient the edge backwards.
   Every curve not involved keeps its height, so every piece of a sheet lies in a rectangle
   `s₀ × [t_q, t_{q+1}]` whose corners carry both signs, or (near a flip at `q`) in
   `s₀ × [t_{q−1}, t_{q+1}]`, where `(v, t_q)` and `(w, t_q)` carry both signs. (At every vertex
   of the subdivision the sign at each `q` is that of `v` or of `w`, so a curve at
   `(t_q + t_{q+1})/2` forces the four corners to carry both signs.) Each point of such a set is
   within `max(|s₀|, 1/N) < δ` of each of those corners, so `|u| < ω` there. Hence every sheet
   lies in `U ∩ G × (0, 1)`.

If you see a simpler route, take it and say so. Then:
* **`ho16_theorem15 : HOThm15`**: `exists_ladder`, then `ho16_stairwell_of_ladder`.
* **`ho16_theorem20 : HOThm20`**: `ho16_theorem20_of_thm15 ho16_theorem15`.
* **`ho16_indec_homogeneous_pseudoArc`**: `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`
  applied to `ho16_theorem15`. This is H–O p. 180: "every indecomposable non-degenerate
  homogeneous plane continuum is a pseudo-arc", **with no named hypothesis**. Run `#print axioms`
  on it and report the line.
* **`ho16_pseudoArc_indec_homogeneous`** (not part of the stretch; do it with §3): if
  `univ : Set M` is a pseudo-arc, then `M` is homogeneous (`homogeneous_of_isPseudoArc`, stated
  pointwise for a set; transfer along `Homeomorph.Set.univ`) and not decomposable (`hPA.2.1` gives
  the indecomposability of `univ`; then `not_isDecomposableSpace_of_isIndecomposable`, or
  directly).
* **`ho16_indec_homogeneous_iff`**: for a non-degenerate plane continuum `M`, homogeneous and
  indecomposable iff `univ : Set M` is a pseudo-arc. Forward: `isPseudoArc_of_indec_homogeneous`
  (batch 193) with `ho16_theorem20`; backward: `ho16_pseudoArc_indec_homogeneous`. This is the
  indecomposable case of the classification in both directions.

## 6. Non-vacuity

* `ladder_example` (skeleton): `G = [0, 2] ⊆ ℝ`, vertices `0`, `1`, `2` with lists `[½]`, `[½]`,
  `[¼, ½, ¾]`; edge `(0, 1)` without event, edge `(1, 2)` with a wedge at `2` at place `1`, tip at
  parameter `½`, height `⅜`. Prove `IsLadder` for it, and apply `ho16_stairwell_of_ladder` to
  obtain a stairwell structure of height 3. By my hand computation the end sets are: over `[1, 2]`
  (parameter `μ`), `l₁ = 1/6`, `r₁ = 1/3`; `π(S₁) = [0, 4/3] ∪ [3/2, 2]`, `π(S₂) = [7/6, 4/3] ∪
  [3/2, 2]`, `π(S₃) = [7/6, 2]`; `π(α₂) = {4/3, 3/2}`, `π(α₃) = {7/6}`.
* `exists_ladder`: a segment `G = [0, 1]` with `M = G × {½}` and `U` a thin neighbourhood of `M`
  meets every hypothesis.
* `ho16_indec_homogeneous_pseudoArc` has no named hypothesis, and its hypotheses are met
  (`exists_indec_homogeneous_plane`, skeleton): by the plane pseudo-arc (`isPseudoArc_plane`),
  homogeneous by `homogeneous_of_isPseudoArc` (Bing 1951, batch 88; Bing 1948 Theorem 13 is
  `Description.theorem13`, batch 81), indecomposable as a hereditarily indecomposable continuum
  (`HPC.Hagopian.not_isDecomposableSpace_of_isIndecomposable`, which gives the statement for the
  subtype; a small transfer is needed either way). `homogeneous_of_isPseudoArc` is already
  pointwise for `M₀ ⊆ Pt`, so no transfer is needed for homogeneity; going through
  `ho16_pseudoArc_indec_homogeneous` would need `IsPseudoArc M₀ → IsPseudoArc (univ : Set M₀)`,
  which I did not find in the library. Neither item needs §5's stretch.

## 7. Order

§2 and §3 first (`ho16_stairwell_of_ladder`, `ladder_example`), with
`ho16_pseudoArc_indec_homogeneous` and `exists_indec_homogeneous_plane`; §4 alongside; the rest
of §5 last.

## 8. Deliverables

1. **The items of §2–§6.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch197.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** §0 (two additions) and §4.
3. **Notes:** `doc/notes/ho16.md`: ladders and the proof of Theorem 15, in a few paragraphs.
4. **Publish the changes, as in batch 196**: `doc/batches/batch197-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies) and
   `doc/batches/batch197-MANIFEST.txt`.
5. **The report.** Its first line names the commission it read. It covers the items in order, the
   non-vacuity notes, the ledger entries, the axioms used by each theorem, the dependency map of
   `ho16_indec_homogeneous_pseudoArc` (if §5 is done; otherwise of `ho16_stairwell_of_ladder`), and
   comments on what remains of the classification (Part G, the decomposable case: the circle of
   pseudo-arcs; its converse: the circle of pseudo-arcs is homogeneous (Bing–Jones 1959); and the
   final statement with all three cases).
