# Commission: batch 200 — Part G, III: Bing–Jones's homeomorphism (pp. 188–189), Theorems 8 and 9

**Go!** This batch runs on top of the batch-199 work. Two files come with it, as separate uploads:

* `COMMISSION-batch200.md`: this text, also pasted into the prompt.
* `BJ59C.lean`: the skeleton.
  * Save it as `HPC/BJ59/BJ59C.lean`. You may split it under `HPC/BJ59/`.
  * Add `import HPC.BJ59.BJ59C` at the end of `HPC.lean`. Adjust the skeleton's imports as needed.
  * Save copies under `doc/batches/` (`COMMISSION-batch200.md`, `skeletons/BJ59C.lean`) and
    include them in the tarball, as in batch 199.

No new source: Bing–Jones is `doc/sources/bing-jones1959.pdf` (PDF page `n` is journal page
`169 + n`). The project's copy there is missing; restore it first (§0).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before, including the test of every new definition on
  degenerate inputs.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more (400 dpi for subscripts, primes, tildes and bars), not
  against the text layer.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Bing–Jones 1959, III (batch 200)");
  * `README.md`;
  * `LEDGER.md`: a new section "Bing–Jones §§4–6 (batch 200)";
  * `OPEN.md`;
  * `doc/notes/bj59.md` (append);
  * `doc/sources/` (the restored sources of §0).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 199

* **Delivery.** The download was current (`axioms.txt` 3624 lines, equal to the tarball's). Its
  `doc/` is behind the tarballs:
  * it lacks the batch-199 copies of the commission and skeleton (the tarball has them,
    byte-identical to what I sent);
  * `doc/sources/` lacks eight sources that earlier tarballs carry: `bing-jones1959.pdf`,
    `cook1967.pdf`, `domokos-prajs2022.pdf`, `hagopian1984.pdf`, `hoehn-oversteegen2016.pdf`,
    `jones1975.pdf`, `lelek1979.pdf`, `oversteegen-tymchatyn1982.pdf`. The project root has your
    uploaded copies (Bing–Jones as `bingjones1959-1.pdf`), byte-identical to mine.

  Please restore the eight under `doc/sources/` before the quotation checks, and make sure the
  project itself carries `doc/` this time.
* **Audit.** 114 new theorems (96 on the three standard axioms, 16 on `propext` and `Quot.sound`,
  2 on none) and the three batch-198 `@[simp]` lemmas, now audited; `sorryAx` in none; the thirteen
  new files contain no `sorry`, `admit` or `axiom` outside comments (the two `OPEN` blocks of
  `BJ59B.lean`). The 31 delivered declarations of the skeleton are textually the skeleton's.
* **Results.** Everything except the stretch item (Theorem 9) and the optional atriodicity, plus
  both other optional items. Your route for Theorem 7 (folding along a walk, no special case; a
  collar chain for the second sentence) is better than Bing–Jones's and than mine. Thank you.
* **Ledger.** BJ.17–BJ.20 and DP.1–DP.4 adopted.
  * **Counted:** BJ.18. Theorem 7's second sentence is the twenty-fourth false printed statement.
  * **BJ.19 (Theorem 7's proof):** the `n = 3` failure is so far argued by hand only. The
    certificate is §6 below; once it is verified, BJ.19 is counted as a defective proof.
  * **DP.2:** the "only if" direction is supplied for the plane example under `BJThm10` and
    `BJPlaneExample`; the transport to every circle of pseudo-arcs is §6 below.
  * **Counts:** 24 false printed statements, 17 defective proofs.

## 1. The plan

Theorem 10 (pp. 181–189) builds a homeomorphism from two interleaved sequences of chains. Its
outline (p. 182, 200 dpi):

> "We shall get a sequence of chains D₁, D₂, ⋯ covering P and a sequence of chains E₁, E₂, ⋯
> covering Q and use these sequences to define our homeomorphism h. Also, we obtain sequences of
> chain maps H₁, H₂, ⋯ and K₁, K₂, ⋯ such that H_i takes D_i onto E_i and K_i takes E_{i+1} onto
> D_i."

The chains come from Steps 1, 2, 3, ⋯ (pp. 182–188), which use Step 1(b), Theorem 5 (repaired,
batch 198), Theorem 6, the corollary to Theorem 8, and Theorem 9 (Step 2(i), p. 187). The
homeomorphism is defined from the sequences alone (pp. 188–189).

This batch does:
* **§2** the definition of the homeomorphism (pp. 188–189), as a lemma about any two sequences
  with Conditions B and B′. It serves Theorem 9 as well (Bing–Jones, p. 181, 200 dpi: "That h is a
  homeomorphism of P onto Q follows from an argument similar to that contained at the end of the
  proof of Theorem 10 of this paper or in Theorem 11 of [3].");
* **§3** two tools: private points, and Step 1(b) of Theorem 10;
* **§4** Theorem 8 and its corollary;
* **§5** Theorem 9, through §2 and Theorem 7 (batch 199);
* **§6** two small items.

Steps 2 and 3 of Theorem 10, the induction and the assembly come in the next batches; then the
plane example (§7 of the paper).

## 2. The homeomorphism of pp. 188–189 (skeleton §2)

Bing–Jones (p. 188, 400 dpi), for the sequences of Theorem 10:

> "A. For each x (0≦x≦1), H_n takes any subchain of D_n properly covering p_x onto a subchain of
> E_n properly covering q_x.
> B. d_i⊂K_{n−1}H_n(d_i) for each link d_i of D_n.
> ⋯
> B′. e_i⊂H_nK_n(e_i) for each link e_i of E_{n+1}."

and (pp. 188–189, 400 dpi): "DEFINITION OF HOMEOMORPHISM h. For each point p of P let d(p, i)
denote the sum of the elements of D_i containing p and H_id(p, i) denote the sum of the images
under H_i of the elements of D_i in d(p, i). … Of course, d(p, i+1)⊂d(p, i). … For each point p of
P, let h(p) be the intersection of the closures of the decreasing sequence of open sets
H₁(d(p, 1)), H₂(d(p, 2)), H₃(d(p, 3)), ⋯."

* `starImage D E H p` is `H_i d(p, i)`.
* `zigzag_homeomorph` (**main item**): the homeomorphism, characterized by
  `h p ∈ closure (H_i d(p, i))` for every `i`. Bing–Jones's proof, p. 188 to p. 189:
  1. *Nested.* `d(p, i + 1) ⊆ d(p, i)` by Condition B (Bing–Jones: "Of course"), and
     `H_{i+1} d(p, i + 1) ⊆ H_i d(p, i)` by B and B′.
  2. *A point.* `H_i d(p, i)` is one link or two adjacent ones, of diameter `< 2 ε_i`; each meets
     `Q`, so the closures meet `Q` and shrink to one point of `Q`.
  3. *Continuous.* For `q ∈ P ∩ d(p, i)` the two image sets share a link: distance `≤ 3 ε_i`.
  4. *Onto.* `H_i` is onto and each link of `D_i` meets `P`, so `h(P)` is dense in `Q`; it is
     compact.
  5. *One-to-one* (p. 189, 400 dpi): "Since the closures of H_id(p, i) and H_id(q, i) intersect and
     we are dealing in this paper only with chains whose nonadjacent links do not have closures
     that intersect, then H_id(p, i) intersects H_id(q, i). Since K_{i−1} is a chain map, the set
     K_{i−1}H_id(p, i) intersects the set K_{i−1}H_id(q, i). But the closures of these two sets
     contain p and q respectively so ρ(p, q)<4/2^i." The bound is `4 ε_{i−1}` (BJ.14).
* Slip, p. 188 (400 dpi): "Also, e_j^{i+1}⊂H_iK_i(e_j^{i+1}) by Condition B′ and
  H_iK_i(e_j^{i+1}) = H_i(d_k^{i+1})⊂H_id(p, i)." `H_i` is applied to `d_k^{i+1}`, a link of
  `D_{i+1}`; what is meant is `H_i(K_iH_{i+1}(d_k^{i+1}))`.
* `zigzag_fibre`: the consequence of Condition A that Theorem 10 uses (`h(p_x) = q_x`): `h p` is a
  limit of points of the fibre over `φ p`. Proof: `h p` lies in the closure of one link `E_{H j}`
  with `p ∈ D_j` (the closure of a finite union is the union of the closures); `hA` gives `q` in
  that link with `ψ q = φ p`, so `dist (h p, q) ≤ ε_i`; the fibre is closed.
* Condition C (agreement with a given homeomorphism on `p₀ + p₁`) follows from the
  characterization; no separate lemma is asked for.

The skeleton carries no hypothesis that these proofs leave unused: `IsBJChain` is assumed for `E`
only (step 5 uses it), and `zigzag_fibre` assumes neither `P ⊆ ⋃ D_i` nor that `H_i` is a chain
map. If you find another unused hypothesis, say so.

## 3. Private points; Step 1(b) (skeleton §3)

A *private point* of a link is a point of the covered set outside the closures of the other links.

* `exists_privatePoint_interior`. In a chain in Bing–Jones's sense properly covering a connected
  set `P`, every interior link `dᵢ` has a private point. Otherwise
  `P ∩ dᵢ ⊆ cl d_{i−1} ∪ cl d_{i+1}` (nonadjacent links are at positive distance), and
  `P ∩ ⋃_{j<i} cl d_j`, `P ∩ ⋃_{j>i} cl d_j` are closed in `P`, disjoint, non-empty, and cover `P`.
  So only end links can lack private points; Bing–Jones ask for them there only (§5).
* `exists_privatePoint_shrink`. My proof:
  * pick `zᵢ ∈ K ∩ dᵢ`, distinct (a connected non-degenerate set has no isolated points);
  * choose `r > 0` with `B(zᵢ, 2r) ⊆ dᵢ` and `r < ½ min_{i≠j} dist(zᵢ, z_j)`, so that the closed
    balls `B̄(zᵢ, r)` are pairwise disjoint;
  * remove `B̄(zᵢ, r)` from `d_{i−1}` and `d_{i+1}`. Nonadjacent links are already at positive
    distance from `zᵢ`. A point of `B̄(zᵢ, r)` stays in `dᵢ`, so the links still cover `K`, and
    `zᵢ` stays in `dᵢ`; adjacency follows from connectedness (`adjacent_meet_of_cover`).

  Compactness of `K` is not used; you may weaken the hypothesis to connected and non-degenerate.
  Used in §5 to make refinement maps onto: if each link of `E` has a private point, a fine enough
  chain refining `E` maps onto `E`.
* `bj_step1b`. Bing–Jones (p. 182, 400 dpi): "(b) It follows from the continuity of the collection
  {p_x} and the bicompactness of an arc that there is a positive integer n such that if
  0≦b−a≦1/n, then the subchain of E₁ that irreducibly covers Q(a, b) properly covers each element
  of {q_x/a≦x≦b}." Unargued.
  * *Irreducibly.* Bing–Jones define it (p. 172, 400 dpi; BJ.17): "Also, D *irreducibly covers* X
    of each link of D contains a point of X that is not covered by any other link of D." The
    skeleton asks only that neither end link can be dropped. For a connected set such as `Q(a, b)`
    the two agree: an interior link whose points of `Q(a, b)` all lie in its neighbours would
    split `Q(a, b)` into two disjoint open pieces.
  * *Proof,* by contradiction and compactness. A failure gives `a_k ≤ b_k` with `b_k − a_k → 0`,
    a fixed subchain `[u, v]` and fibres `q_{x_k}` missing an end link, say `e_u` (a fibre meeting
    both end links meets all of `[u, v]`, being connected).
  * Since `e_u` cannot be dropped, there are `z_k ∈ Q(a_k, b_k)` outside `e_{u+1} ∪ ⋯ ∪ e_v`. Pass
    to `z_k → z`, `x_k → c`, so `z ∈ q_c`.
  * `z` lies in some link `e_w`, and lower semicontinuity (`f` open) gives points `y_k ∈ q_{x_k}`
    tending to `z`, eventually in `e_w`. Since `q_{x_k}` misses `e_u`, `y_k` lies in some `e_j`
    with `u < j ≤ v`, so `|w − j| ≤ 1`.
  * If `u < w ≤ v`: `z_k ∈ e_w` eventually, against the choice of `z_k`. If `w = u`: `y_k ∈ e_u`,
    against `q_{x_k} ∩ e_u = ∅`. If `w < u`: impossible, as `j ≥ u + 1`. If `w > v`: then
    `w = v + 1`, and `z_k ∈ e_{v+1}` eventually; `z_k` lies in `e_u` (it is covered by `[u, v]` but
    not by `e_{u+1}, …, e_v`), so `e_u` meets `e_{v+1}`, `u = v`, and `q_{x_k} ⊆ e_u`, against
    `q_{x_k} ∩ e_u = ∅`.

  Needed in Theorem 10 (Steps 1 and 2) and for the non-vacuity of Theorem 8.

## 4. Theorem 8 and its corollary (skeleton §4)

Quotations number links from 1, as printed. The steps below number them from 0, as in Lean:
Bing–Jones's `d₁`, `d_n`, `y₁`, `y_m` are `d₀`, `d_{n−1}`, `y₀`, `y_{m−1}`.

**Theorem 8** (p. 177, 400 dpi):

> "THEOREM 8. *Suppose P is a snake-like arc of pseudo-arcs {p_x|0≦x≦1}, D = d₁, d₂, ⋯, d_n is a
> chain covering P such that each link of D intersects each p_x, and H is a chain map of a chain
> Y = y₁, y₂, ⋯, y_m onto D. Then there is a chain E = e₁, e₂, ⋯, e_m covering P such that each p_x
> intersects each link of E and e_i⊂d_j if H(y_i) = d_j.*"

Shape of `bj_theorem8`, four changes:
* `f` open (a continuous arc of pseudo-arcs, as Theorem 10 needs);
* `n ≥ 3`;
* the conclusion a chain in Bing–Jones's sense;
* `D` (and `E` in the corollary) a chain in the library's sense, which asks less than
  Bing–Jones's (p. 172: nonadjacent links at a positive distance). This strengthens both theorems.

The proof (p. 178, 400 dpi) begins: "First we consider the case where H(y₁) = d₁, H(y_m) = d_n.
Let U_A, U_B be open sets with closures in d₁, d₂ respectively such that U_A, U_B intersect each
element of {p_x}." (Printed `d₂`, read `d_n`: BJ.7.) Bing–Jones give no argument for these sets.
For a continuous collection they exist (step 1 below); for an upper semicontinuous one, as
printed, I do not know. With `n ≥ 3`, `d₀ ∩ d_{n−1} = ∅`, so `Ū_A ∩ Ū_B = ∅`.

The printed construction (p. 178, 400 dpi): "It follows from Theorem 4 that P is covered by open
sets U₁, U₂, ⋯, U_t such that U_i·U_j = U_A+U_B if i≠j and if p_x·(U_i−(U_A+U_B))≠0, then x∈I_{a_i}.
Then the chain E whose kth link e_k = e(a₁)_k·U₁+e(a₂)_k·U₂+ ⋯ +e(a_t)_k·U_t is the required
chain." The cover is not derived. The `e_k` need not form a chain (argued, not certified):
`e(a_i)_k` is controlled only over `I_{a_i}`; over a fibre outside `I_{a_i}` it can reach into
`U_A ⊆ U_i ∩ U_j` and meet `e(a_j)₀` there, for any `k ≥ 2` with `H(y_k) ∈ {d₀, d₁}`.

My repair, for `H(y₀) = d₀`, `H(y_{m−1}) = d_{n−1}`:
1. **`U_A`, `U_B`.** `x ↦ sup {dist(z, d₀ᶜ) : z ∈ p_x ∩ d₀}` is positive and lower semicontinuous
   (`f` open), so it has a positive minimum `2ρ`; take `U_A = {z ∈ d₀ : dist(z, d₀ᶜ) > ρ}`. Same
   for `U_B` in `d_{n−1}`.
2. **`E(a)`.** `bj_theorem7_ends` on `p_a`, with `A = Ū_A ∩ p_a`, `B = Ū_B ∩ p_a`, `r = 0`,
   `s = m − 1`.
3. **`I_a`.** By upper semicontinuity, an open interval `I_a ∋ a` of `[0, 1]` such that for
   `x ∈ I_a`, `p_x ⊆ ⋃ E(a)`, `Ū_A ∩ p_x ⊆ e(a)₀` and `Ū_B ∩ p_x ⊆ e(a)_{m−1}`. Take a minimal
   finite subcover `I_{a_1}, …, I_{a_t}`, ordered by left end points. Then the right end points
   increase too, and each overlap `I_{a_i} ∩ I_{a_{i+1}}` lies in `(0, 1)` and to the left of the
   next one.
4. **The cover.**
   * Cuts `c₁ < ⋯ < c_{t−1}` with `c_i ∈ I_{a_i} ∩ I_{a_{i+1}}`, and open intervals `J_i ∋ c_i`
     with closures in `I_{a_i} ∩ I_{a_{i+1}} ∩ (0, 1)`, pairwise disjoint and increasing
     (`sup J_i < inf J_{i+1}`).
   * `V_i = (U_A ∪ U_B) ∩ f⁻¹(J_i)` misses `p₀ ∪ p₁`, and `bj_theorem4` splits `X − V_i` into
     disjoint closed `L_i ⊇ p₀` and `R_i ⊇ p₁`. Fibres left of `J_i` lie in `L_i` (the preimage of
     `[0, s]` is connected and misses `V_i`) and fibres right of it in `R_i`, so
     `L_i ⊆ f⁻¹[0, sup J_i)` and `R_i ⊆ f⁻¹(inf J_i, 1]`.
   * Put `U_i = (R_{i−1} ∩ L_i) ∪ U_A ∪ U_B` for `i = 1, …, t` (`R₀ = L_t = X`). It equals
     `((X − L_{i−1}) ∩ (X − R_i)) ∪ U_A ∪ U_B`, so it is open. The `U_i` cover `X` (take the least
     `i` with the point in `L_i`); for `i < k`, `U_i ∩ U_k ⊆ U_A ∪ U_B`, as `L_i ∩ R_{k−1} = ∅`;
     and `U_i − (U_A ∪ U_B)` lies over `(inf J_{i−1}, sup J_i) ⊆ I_{a_i}`.
5. **The links.** `e_k = ⋃ᵢ e(a_i)_k ∩ U_i ∩ f⁻¹(I_{a_i})`. They cover `X`, `U_A ⊆ e₀`,
   `U_B ⊆ e_{m−1}`, and `e_k ⊆ d_{H(k)}`. Nonadjacent links are disjoint: two pieces from the same
   `i` are disjoint, and pieces from `i ≠ j` meet only in `U_A ∪ U_B`. At a point of `U_A` over
   `x ∈ I_{a_i} ∩ I_{a_j}`, both `e(a_i)₀` and `e(a_j)₀` contain the point, so `k, l ≤ 1`. `U_B`
   is symmetric, with `m − 2`, `m − 1`.
6. **Each fibre meets each link.** `p_x` meets `U_A ⊆ e₀` and `U_B ⊆ e_{m−1}` and is connected.
7. **Bing–Jones's sense.** Shrink with `exists_bjChain_shrink`, keeping inside `e₀` the compact
   set `cl U′_A`, where `U′_A = {z ∈ d₀ : dist(z, d₀ᶜ) > 3ρ/2}` still meets every fibre and
   `cl U′_A ⊆ U_A ⊆ e₀`; likewise inside `e_{m−1}`. Then step 6 again.

The general case (Bing–Jones: "suppose H(y_r) = d₁, H(y_s) = d_n. Then alter Y as was done in the
proof of Theorem 7 …"): take `r ≤ s` (otherwise reverse `Y`; `unfoldIdx_last` needs `r ≤ s`,
BJ.19 (f)), follow the pattern along the walk `r, r − 1, …, 0, 1, …, m − 1, m − 2, …, s` and fold,
as in your Theorem 7 (`unfoldFin`, `foldChain`). Folding keeps every fibre meeting every link.

**Corollary to Theorem 8** (p. 178, 400 dpi):

[Quotation moved to doc/sources/transcriptions/bingjones59.md, §doc/batches/COMMISSION-batch200.md, Corollary to Theorem 8 (p. 178); batch 204.]

Bing–Jones's proof (p. 178, 400 dpi): Theorem 8 with "Y be a chain with four times as many links as
D(r, s), and H be a chain map that takes links of Y numbered 4i+1, 4i+2, 4i+3, 4i+4 into the image
under H₁ of the ith link of D(r, s). Then ε is a number so small that any ε-chain properly
covering Q(i/k, (i+1)/k) is a refinement of the chain E promised by Theorem 8."
* Numbered from 1, as everywhere in the paper, links 1–4 of `Y` get no image and the last block
  runs past `4ℓ`: read `4i−3, …, 4i`. (The letter `i` also names the sub-arc `Q(i/k, (i+1)/k)`.)
* "properly covering" where the statement has "irreducibly covering" is harmless: an irreducible
  cover is a proper one.
* The three consecutive links are not argued.

My argument, numbering from 0: let `G` be the chain from Theorem 8 (`4ℓ` links,
`g_{4i+c} ⊆ e_{H₁(i)}` for `c < 4`) and `R(f) = ⌊a/4⌋` for a link `g_a ⊇ f`. A subchain
`f_v, …, f_w` covering `q_x` has links containing points of `q_x ∩ g₀` and of `q_x ∩ g_{4ℓ−1}`, so
the indices `a` along it run from `≤ 1` to `≥ 4ℓ − 2` in steps of at most one; crossing block `i`
takes at least three consecutive links (four for interior blocks). Take `ε` below a Lebesgue
number of the cover `G` (so `F` refines `G`) and, for `ℓ = 1`, below a third of the least fibre
diameter (positive, `f` being open).

Shape of `bj_theorem8_cor`: the arc is the whole space; `F` need not be irreducible, and the
three-link property is asked of every covering subchain (both are what the argument gives).
`n ≥ 3` is assumed; in Theorem 10 it holds once the chains are finer than half the least fibre
diameter. The transfer to sub-arcs `Q(i/k, (i+1)/k)` of a larger space is for the next batch;
if a sub-arc form is more convenient, adjust the shape and say so.

## 5. Theorem 9 (skeleton §5)

Statement as in commission 199 §6 (p. 179). It is no longer a stretch item: Theorem 10 uses it in
Step 2(i) (p. 187, 200 dpi: "Theorem 9 assures us that h can be extended in this fashion"). The
route, with §2 doing the work of pp. 180–181.

**Notation.** `m` is the number of links of `E` (Bing–Jones's `n` after the first simplification),
so `D′` and `E′` have `4m − 3` links, numbered from 1 as in the paper. `G` is Bing–Jones's fine
chain on `P` (p. 180), `F` the fine chain on `Q`, and `π_i` the refinement maps of step 3
(Bing–Jones's `G_i` on p. 181 are chains on `Q`).

1. **First simplification** (p. 179; part of `bj9_base`).
   * `d″_j` is the union of the links of `D` that `H` sends to `e_j`. `D″` is a chain in
     Bing–Jones's sense properly covering `P`, with `m` links, and each of its links has a private
     point: the end links by the hypothesis, as Bing–Jones say; the interior links automatically
     (`exists_privatePoint_interior`).
   * Shrink `E` first with `exists_privatePoint_shrink`. Theorem 9 assumes nothing of the kind for
     `E`, and `e₁ ⊆ e₂` is possible. Bing–Jones do the same (p. 179, 400 dpi): "If there are not
     already such points, points may be deleted from e₂ and e_{n−1} to make the condition
     satisfied." The last clause of `bj9_base` for the shrunk `E` implies it for `E`.
2. **Second simplification** (pp. 179–180, Figure 1; the rest of `bj9_base`). Write `D`, `E` for
   the chains after step 1: `m` links each, `H(d_i) = e_i`, every link with a private point.
   * **`D′`.** Take `δ` with nonadjacent links of `D` more than `5δ` apart, and `G` a `δ`-chain
     properly covering `P` and refining `D` (p. 180, 200 dpi: "Let G be a δ-chain properly
     covering P and refining D.").
     * `d′_{4i−1}` is the union of the links of `G` that meet `d_i ∩ d_{i+1}`; every point of such
       a link lies in `d_i ∪ d_{i+1}`.
     * Each other link of `G` lies in some `d_i − (d_{i−1} ∪ d_{i+1})`. Those for `d_i` make up the
       links between `d′_{4i−5}` and `d′_{4i−1}`: the ones meeting a link of `d′_{4i−5}` go to
       `d′_{4i−4}`, the ones meeting a link of `d′_{4i−1}` to `d′_{4i−2}`, the rest to `d′_{4i−3}`.
       At the ends there are two such links: `d′₁`, `d′₂` and `d′_{4m−4}`, `d′_{4m−3}`.
     * These links of `G` need not be consecutive in `G`. No link of `G` meets both `d′_{4i−5}` and
       `d′_{4i−1}` (that would bring `d_{i−1}` within `3δ` of `d_{i+1}`).
     * For small `δ`, the link of `G` through the private point of `d_i` goes to the middle group
       (`d′₁`, `d′_{4m−3}` at the ends); connectedness of `P` gives the other groups. So no link
       of `D′` is empty.
   * **`E′`.** Take `F` a fine chain properly covering `Q`, with the closure of every link inside a
     link of `E`. Each closure lies in one or two links (`e_{i−1} ∩ e_{i+1} = ∅`).
     * `e′_{4i−3}` is the union of the links of `F` whose closures lie in `e_i` only.
     * The links with closures in `e_i ∩ e_{i+1}` form `e′_{4i−2}`, `e′_{4i−1}`, `e′_{4i}`: the ones
       meeting a link of `e′_{4i−3}` go to `e′_{4i−2}`, the ones meeting a link of `e′_{4i+1}` to
       `e′_{4i}`, the rest to `e′_{4i−1}`.
   * **Why `E′` is a chain for small mesh.** Unlike the case of `D′`, the separation does not come
     from the distance between nonadjacent links: `e_i − e_{i+1}` and `e_{i+1} − e_i` can come
     arbitrarily close.
     * `Q` misses `Z_i = cl(e_i − e_{i+1}) ∩ cl(e_{i+1} − e_i)`. A point of `Q` lies in some link,
       which meets `e_i` and `e_{i+1}` if the point is in `Z_i`; so the link is `e_i` or
       `e_{i+1}`, a neighbourhood of the point missing one of the two sets.
     * Suppose that for meshes tending to 0 there are links `f`, `f′` of `F`, joined through at
       most two further links, with points `a ∈ cl f − e_{i+1}` and `b ∈ cl f′ − e_i`, where
       `cl f ⊆ e_i` and `cl f′ ⊆ e_{i+1}`. Every link meets `Q` and `Q` is compact, so a
       subsequence of the pairs `(a, b)` converges to one point of `Q ∩ Z_i`.
     * So for small mesh: no link of `e′_{4i−3}` meets a link of `e′_{4i+1}`; no link with closure
       in `e_i ∩ e_{i+1}` meets links of both; and `e′_{4i−2}` misses `e′_{4i}`. Other
       nonadjacent pairs are disjoint because `e_i ∩ e_{i+2} = ∅`.
     * No link of `E′` is empty for small mesh: the private points give the middles; a point of
       `Q ∩ e_i ∩ e_{i+1}` (at positive distance from `e_i − e_{i+1}` and `e_{i+1} − e_i`) gives
       `e′_{4i−1}`; connectedness of `Q` gives `e′_{4i−2}` and `e′_{4i}`.
   * **Bing–Jones's choice** (pp. 179–180, 400 dpi): "Suppose that ε is a positive number so small
     that each subset of Q of diameter less than 5ε lies in one link of E. Let F be an ε-chain
     properly covering Q. Then e′₁ is the sum of all links of F whose closures intersect e₁−e₂, e′₅
     is the sum of all links of F whose closures intersect e₂−(e₁+e₃), …". The condition on `ε`
     concerns subsets of `Q`; the links of `F` are not subsets of `Q`. It secures neither the
     separation above nor that every link of `F` falls under one of the rules.
   * **The last clause.** `closure (e′_j) ⊆ e_i` whenever `d′_j` contains a point of `P ∩ d_i`:
     check index by index. Bing–Jones's display ends "⊂ē_i" (BJ.8).
   * Finally shrink both chains to private points (`exists_privatePoint_shrink`).
   * Known slips (BJ.8): printed "links of G", read "links of F" (`e′_{4n−6}`, …); printed `e`,
     read `d`, in "d₂′ is the sum of the other links of G in e₁−e₂" and the next two clauses.
   * Any other construction meeting the statement is welcome.
3. **Alternation.** Keep pairs `(D_i, E_i)` with the same number of links matched by index, chains
   in Bing–Jones's sense, properly covering, with private points, and refinement maps `π_i` with
   `d^{i+1}_j ⊆ d^i_{π_i j}` and `e^{i+1}_j ⊆ e^i_{π_i j}`.
   * On even steps, take `E_{i+1}` fine on `Q`, with private points. Its refinement map `π_i` onto
     `E_i` is onto, by the private points of `E_i`.
   * Then `D_{i+1}` comes from `bj_theorem7` on `P`, the chain `D_i` and the pattern `π_i`, shrunk
     to private points.
   * On odd steps the roles are exchanged.
   * The side that is not refined keeps the mesh of the previous step, so both meshes tend to
     zero.

   Bing–Jones use Bing 1948 Theorems 6 and 13 here; Theorem 7 does the same work for us.
4. **Assembly.** `zigzag_homeomorph` with `H_i` the identity and `K_i = π_i` (B and B′ are the
   refinement inclusions). Then `h p ∈ closure (e′_j)` for some `j` with `p ∈ d′_j`, and the last
   clause of `bj9_base` gives `h(P·d_i) ⊆ e_{H(i)}`.

Known slips on p. 181 (BJ.9): printed "refines E_i", read `E₁`; printed "H₂", read `H₁`; printed
"d¹_k", read `e¹_k`.

## 6. Two small items (skeleton §6)

* `dp22_theorem61_iff`. Let `C` be the plane circle of pseudo-arcs that `BJPlaneExample`
  (`∃ C : Set Pt, IsCircleOfPA C`) provides.
  * "⇐" is `isCircleOfPA_of_atomic` with `Y = C`.
  * "⇒": `nonvac_atomic` (`BJ59B.lean`) already gives an atomic map `C → Circle`; its proof is
    this direction for `C` (`isHomogeneous_of_isCircleOfPA`, `isDecomposableSpace_of_isCircPAMap`,
    `circle_or_atomic_of_decomposable`, and an inline argument that `C` is not a simple closed
    curve, as `h13` in `ho16_classification_plane`). For a general `X`,
    `homeomorph_of_isCircleOfPA` gives `X ≃ₜ C`; compose.
  * No lemma yet transports `IsAtomicCircPAMap` along a homeomorphism. Fibres, openness and the
    atomic property all transport; `isPseudoArc_of_homeomorph` needs `[CompactSpace]` on the
    target. Please add the transport lemma.
* `bj_theorem7_proof_n3`: the certificate for BJ.19 (e). Proof, with links numbered from 1 as in
  the paper (`d_k` is `D.link (k − 1)`):
  * if `P·(d₃ − d₂) = ∅`, a point of `U ∩ P` lies in `d₂ ∩ d₃ ⊆ d₂ − d₁`, hence in `V`;
  * otherwise `P·(d₃ − d₂)` is relatively closed in `P` (it and `P·(d₁ − d₂)` are disjoint and
    relatively open in the relatively closed `P − d₂`), non-empty and not all of `P`. So it has a
    point `z` that is a limit of points of `P ∩ d₂ ∩ d₃ ⊆ V`, and `U` is a neighbourhood of `z`.

  For `n = 3` the printed `D′` puts the link `U₂` and the link `U_{n+1} = U₄` at places at least two
  apart, so they must be disjoint.

## 7. Ledger

New section "Bing–Jones §§4–6 (batch 200)". Check each item on page images.

**Convention.** Write each slip as "printed X, read Y", as this commission does. `LEDGER.md` mixes
the two orders: BJ.7–BJ.10 put the reading first (BJ.7, "`d_n` for `d₂`"), BJ.17 the printed text
first ("`of` for `if`"). Say so once at the head of the new section; do not edit the old entries.

1. **Theorem 8, first step (p. 178)**: `U_A`, `U_B` asserted without argument; for continuous
   arcs supplied (§4 step 1); for upper semicontinuous arcs, as printed, not decided. Printed
   `d₂`, read `d_n` (BJ.7).
2. **Theorem 8, the cover `U₁, …, U_t`**: "It follows from Theorem 4": unargued; supplied (§4
   step 4).
3. **Theorem 8, the chain `E`**: "is the required chain": the printed `e_k` need not form a chain
   (argued, not certified); repaired by restricting each piece to the fibres over `I_{a_i}` (§4
   step 5). A defective construction with a one-line repair; I would not count it (as BJ.4).
4. **Theorem 8, the general case**: "alter Y as was done in the proof of Theorem 7": unargued;
   supplied by folding.
5. **Corollary to Theorem 8**: the three consecutive links are not argued; supplied (§4). In the
   proof, printed "4i+1, 4i+2, 4i+3, 4i+4", read `4i−3, …, 4i`. "properly covering" in the proof
   against "irreducibly covering" in the statement: not a defect.
6. **Step 1(b) (p. 182)**: unargued; supplied (§3). Its "irreducibly covers" agrees, for connected
   sets, with the end-link reading.
7. **pp. 188–189**: "Of course, d(p, i+1)⊂d(p, i)" (from Condition B); the slip
   "H_i(d_k^{i+1})" (§2); "ρ(p, q)<4/2^i" (BJ.14, `8/2^i`).
8. **Theorem 9**:
   * BJ.8 and BJ.9, with the repairs used.
   * The choice of `F` on p. 179 does not make `E′` a chain: links of `F` in different middles can
     meet. Repaired by a smaller mesh (§5 step 2). A defective construction repaired in place; I
     would not count it.
   * Interior links of `D″` have private points automatically (`exists_privatePoint_interior`), so
     the first simplification needs them only for the end links, as Bing–Jones say.
   * "points may be deleted from e₂ and e_{n−1}" (p. 179): used, as `exists_privatePoint_shrink`.
9. **Theorem 7's proof for `n = 3`**: the certificate (§6), for BJ.19.

Count nothing yourself; say which items, if any, you would count.

## 8. Non-vacuity

* `starImage` on degenerate inputs: `p` in no link (`∅`), `n = 0` (`∅`), and `D = E`, `H = id`
  (the union of the links through `p`).
* `zigzag_homeomorph`: `nonvac_zigzag` (the interval with dyadic chains), then apply the lemma.
  `zigzag_fibre`: the same with `φ = ψ = id` on `[0, 1]`.
* `exists_privatePoint_interior`, `exists_privatePoint_shrink`: a plane pseudo-arc and the chain of
  `nonvac_bj_chains` (at least three links).
* `bj_step1b`: `[0, 1]`, the identity, any chain covering it.
* `bj_theorem8`, `bj_theorem8_cor`: the hypotheses need a continuous snake-like arc of pseudo-arcs
  and a chain of at least three links each meeting every fibre. I know such arcs only under
  `BJPlaneExample` (the halves of `C`), and such chains only on short sub-arcs (by `bj_step1b`).
  Say what you can prove; a conditional witness is welcome but not required.
* `bj9_base`, `bj_theorem9`: a plane pseudo-arc, `P = Q`, `D = E` the chain of `nonvac_bj_chains`
  shrunk by `exists_privatePoint_shrink` (three links or more, private points), `H = id`; and the
  one-link chain as a degenerate input.
* `bj_theorem7_proof_n3`: a plane pseudo-arc with a chain of three links (consolidate the chain of
  `nonvac_bj_chains`), `V = univ`, `U = D.link 2`.
* `dp22_theorem61_iff`: under the two inputs, `C`.

## 9. Order

§2 first (`zigzag_homeomorph` is the main item), then §3, §4 (Theorem 8, then the corollary), §6,
and §5 last. §7 alongside.

## 10. Deliverables

1. **The items of §§2–6.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch200.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section of §7.
3. **Notes:** append to `doc/notes/bj59.md`.
4. **Sources:** the eight files of §0 under `doc/sources/`.
5. **Publish the changes, as in batch 199**: `doc/batches/batch200-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies) and
   `doc/batches/batch200-MANIFEST.txt`.
6. **The report.** Its first line names the commission it read. It covers the items in order, the
   shape changes, the non-vacuity notes, the ledger entries, the axioms used by each theorem, and
   what remains for Theorem 10.
