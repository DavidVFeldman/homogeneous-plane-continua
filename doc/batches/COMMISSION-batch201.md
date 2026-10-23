# Commission: batch 201 — Part G, IV: Bing–Jones Theorem 10

**Go!** This batch runs on top of the batch-200 work. Two files come with it, as separate uploads:

* `COMMISSION-batch201.md`: this text, also pasted into the prompt.
* `BJ59D.lean`: the skeleton.
  * Save it as `HPC/BJ59/BJ59D.lean`. You may split it under `HPC/BJ59/`.
  * Add `import HPC.BJ59.BJ59D` at the end of `HPC.lean`. Adjust the skeleton's imports as needed.
  * Save copies under `doc/batches/` (`COMMISSION-batch201.md`, `skeletons/BJ59D.lean`) and
    include them in the tarball, as in batch 200.

No new source: Bing–Jones is `doc/sources/bing-jones1959.pdf` (PDF page `n` is journal page
`169 + n`).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule)**, as before, including the test of every new definition and
  every named `Prop` on degenerate inputs.
* **Quotations (standing rule).** Check every quotation and every reading of a formula against
  page images rendered at 200 dpi or more, and at 400 dpi for subscripts, primes, tildes and bars,
  not against the text layer. The quotations of this batch (pp. 176, 181–188) are full of
  subscripts: check them at 400 dpi.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Bing–Jones 1959, IV (batch 201)");
  * `README.md`;
  * `LEDGER.md`: a new section "Bing–Jones §6, Theorem 10 (batch 201)";
  * `OPEN.md`;
  * `doc/notes/bj59.md` (append).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 200

* **Delivery.** The download was current (`axioms.txt` 3710 lines, equal to the tarball's), and
  `doc/` now carries the sources and the batch copies. Thank you. One older discrepancy remains
  (the batch-199 download had it too):
  * the download's `HPC/` lacks 64 Lean files of the project: 54 under `HPC/Hagopian/` (29
    `H76*`, 15 `H84*`, `Hagopian76W`–`Z`, `Hagopian76AA`–`AC`, `Hagopian84A`, `C`, `D`), five under
    `HPC/Jones/` (`Jones75A`, `Jones75Arcs`, `Jones75L`, `Jones75Line`, `Jones75Rev`) and five
    under `HPC/Span/`;
  * it carries older copies of eight files (`Hagopian76P.lean` to `Hagopian76V.lean` and
    `Hagopian84B.lean`); the old `Hagopian76P.lean` still has `sorry` for `hagopian76_theorem1`,
    which `Jones75B.lean` proves.

  Your `axioms.txt` lists the declarations of the missing files and has no `sorryAx`, so the build
  used the current files. Please make sure the download carries them.
* **Audit.** 86 new theorems (82 on the three standard axioms, 1 on `propext` and `Quot.sound`, 1
  on `propext`, 2 on none); `sorryAx` in none; the fourteen new files contain no `sorry`, `admit`
  or `axiom`. All 13 declarations of the skeleton are textually the skeleton's.
* **Results.** Everything, including the main lemma and Theorem 9. Your Lebesgue-number argument
  for the chain `E′` of Theorem 9 is simpler than mine.
* **Quotations.** The report says that pp. 178–181 and 189 were checked at 200 dpi only and that
  pp. 182 and 188 were not re-rendered. The rule asks for 400 dpi wherever subscripts decide the
  reading; please follow it in this batch.
* **Ledger.** BJ.21–BJ.29 adopted, with one correction: BJ.28 (e) cites "Theorem 13 of Bing
  1951"; Bing–Jones's [3] is Bing 1948 (*A homogeneous indecomposable plane continuum*, Duke,
  p. 192 of the paper).
  * **Counted:** BJ.19, Theorem 7's proof, the eighteenth defective proof (its certificate,
    BJ.29, is verified).
  * **Counts:** 24 false printed statements, 18 defective proofs.

## 1. The plan

Theorem 10 (pp. 181–182, 400 dpi):

> "THEOREM 10. *Suppose P, Q are continuous snake-like arcs of pseudo-arcs {p_x}, {q_x} (0≦x≦1).
> Then each homeomorphism h that takes the sum of the ends of P onto the sum of the ends of Q may
> be extended to a homeomorphism taking P onto Q. In fact, if h(p₀)=q₀, the extended
> homeomorphism h may be chosen so that h(p_x)=q_x.*"

The library states the last sentence as `BJThm10`. This batch proves it. The route:

1. **The step.** Steps 2, 3, 4, ⋯ of Bing–Jones (pp. 183–188) are one construction, made
   alternately on the two sides: from a chain map `H` of a chain `D` on `X` onto a chain `E` on
   `Y` satisfying Conditions A and C, a fine chain `E′` on `Y` and a chain map `K` of `E′` onto
   `D` satisfying A′, B′ and C′. With `X` and `Y` exchanged, the same construction gives A, B and
   C. This is `BJStep` (§4), the main item.
2. **The induction.** Start from one-link chains, apply the step alternately, and feed the
   sequences to `zigzag_homeomorph` and `zigzag_fibre` (batch 200). This is `bjThm10_of_step`
   (§5). It does not depend on the proof of the step; prove it early.

Three differences from Bing–Jones:
* **No homeomorphisms on interior fibres.** Bing–Jones extend `h` at each step to the cut fibres
  `p_{i/n}` (Step 1(c), arbitrarily; Step 2(i), by Theorem 9) and build the maps near those fibres
  from `h`. Here `h` is used only on `p₀` and `p₁`, where it is given. At an interior cut the
  construction passes directly from the map of one sub-arc to the map of the next, with sub-arcs
  that overlap. So Theorem 9 is not used in Theorem 10.
* **No separate Step 1 and Step 2.** The induction starts from one-link chains. The corollary to
  Theorem 8 for a one-link chain is the zig-zag map of Step 2(b).
* **Condition I of Step 2 is not carried; Condition C is.** Condition A is carried in the form
  that the construction needs (§2).

## 2. The conditions (skeleton §2)

Bing–Jones (p. 188, 400 dpi):

> "A. For each x (0≦x≦1), H_n takes any subchain of D_n properly covering p_x onto a subchain of
> E_n properly covering q_x.
> B. d_i⊂K_{n−1}H_n(d_i) for each link d_i of D_n.
> ⋯
> A′. For each x (0≦x≦1), K_n takes any subchain of E_{n+1} properly covering q_x onto a subchain
> of D_n properly covering p_x.
> B′. e_i⊂H_nK_n(e_i) for each link e_i of E_{n+1}.
> ⋯
> C. If link d_i of D_n intersects p₀+p₁, then h(d_i·(p₀+p₁))⊂H_n(d_i).
> C′. If link e_i of E_{n+1} intersects q₀+q₁, then h⁻¹(e_i·(q₀+q₁))⊂K_n(e_i)."

* `IsFibreChainMap f g D E H` is Condition A: `H` is a chain map of `D` onto `E`; a link meeting
  `p_x` goes to a link meeting `q_x`; a run of `D` properly covering `p_x` goes to links whose
  union covers `q_x`. The onto clause is needed because `zigzag_homeomorph` asks for it.
* `EndCompat f g h₀ h₁ D E H` is Condition C.
* `HasPrivatePoints D`: every link has a point outside the closures of the others. It makes the
  next chain map onto (§4 (g) 6), and the step restores it for its output.
* `IsFibreFine g E`: one link, or every run covering a fibre has at least three links. It lets
  the corollary to Theorem 8 apply (it needs one link or at least three).

Test each definition on degenerate inputs (one-link chains, `n = 0`).

## 3. Tools (skeleton §3)

Throughout: indices from 0, as in Lean; a *run* is a set of consecutive indices; a family of links
*properly covers* a set if every link meets it and their union contains it.

* Runs: the links meeting a preconnected set `C ⊆ ⋃ D` form a run. This is in the library:
  `HPC.Plane.meets_between`, `HPC.Chain.inter_link_nonempty_between`, `meets_all_of_meets_ends`.
* `exists_point_only_of_minimal`: in a run covering a preconnected `C` from which neither end link
  can be dropped, every link has a point of `C` in no other link of the run. End links: by
  minimality. Interior links: otherwise `C` splits as in the previous item.
* `adjacent_of_properCover` (**Theorem 6 in the form used**). Bing–Jones (pp. 184–185, 400 dpi):
  "Since each of R_{i/n}, R_{(2i+1)/2n}, and R_{(2i−1)/2n} takes f_t, f_{t+1}, ⋯, f_u (and possibly
  more) onto a subchain (possibly a different one) of E₁ that properly covers q_{i/n}, it follows
  from Theorem 6 that there are an f_y and an f_z of f_t, f_{t+1}, ⋯, f_u such that
  R_{(2i+1)/n}(f_y), R_{i/n}(f_y) are adjacent and R_{(2i−1)/2n}(f_z), R_{i/n}(f_z) are adjacent."
  Theorem 6 (p. 176, 400 dpi) is about "two chain maps of D into E such that H_i (i=1, 2) takes a
  link of D into e_{m−1}". Bing–Jones do not say which chain plays `E`. With `E₁` the hypothesis
  fails. With the subchain spanned by the two images it holds: two runs properly covering the same
  set have ends at most one apart (below), so both maps reach its next-to-last link when each
  image has two links or more, and the adjacency is immediate when an image has one link. An
  unargued step, then. The form the skeleton asks for, with a direct proof:
  * Let `v`, `v′` be the least values of `R`, `R′` on the run. The link `d_v` meets `C`, at a
    point lying in some `d_{R′ a}`, so `v ≥ R′ a − 1 ≥ v′ − 1`. Symmetrically `v′ ≥ v − 1`.
  * Put `φ = R′ − R` on the run. Where `R′ = v′`, `φ ≤ v′ − v ≤ 1`; where `R = v`, `φ ≥ −1`.
    Consecutive values of `φ` differ by at most 2, so `|φ| ≤ 1` somewhere.

  No connectedness is needed.
* `exists_pattern` (**Step 2(b)**). Bing–Jones (p. 184, 400 dpi): "Then R_{i/n} is a chain map of
  f_t, f_{t+1}, ⋯, f_u onto e_r. e_{r+1}, ⋯, e_s such that h(f_j·p_{i/n})⊂R_{i/n}(f_j) and for each
  element e_k of e_r, e_{r+1}, ⋯, e_s there are three consecutive elements of f_t, f_{t+1}, ⋯, f_u
  that go into e_k under R_{i/n}. A precaution to take to insure that each e_k is the image of
  three consecutive elements of f_t, f_{t+1}, ⋯, f_u is to decide that R_{i/n}(f_{j−2})
  =R_{i/n}(f_{j−1})=R_{i/n}(f_j)=R_{i/n}(f_{j+1})=R_{i/n}(f_{j+2})=e_k if e_k is the only element
  of E₁ such that h(f_j·p_{i/n})⊂e_k. Condition 3 of Step 2a enables us to do this." That a chain
  map exists is not argued. In the skeleton `φ` is the map (it will be `h₀⁻¹` or `h₁⁻¹`), `W` the
  run `[w₁, w₂]`, and closures are used (needed in §4 (e)). Proof:
  * `λ`: a Lebesgue number of the cover of the compact `φ(Q)` by the links of `W`. `ε`: below a
    third of `diam Q`, and such that `φ` maps subsets of `Q` of diameter `< 5ε` to sets of
    diameter `< λ`. Let `T` be the run of links of `F` meeting `Q` (`meets_between`).
  * For `a ∈ T` let `S_a` be the set of `j ∈ W` with `φ(cl f_a ∩ Q) ⊆ d_j`: non-empty, and a run
    of one or two indices. Five consecutive links of `T` have closures whose union meets `Q` in a
    set of diameter `< 5ε`, so some `j` lies in all five `S_a`.
  * Call `a` *decided* if `S_a = {j}`. If `a` is decided with value `j`, then `j ∈ S_{a′}` for
    every `a′ ∈ T` within distance 4: the closures of the links from `a` to `a′` meet `Q` in a set
    of diameter `< 5ε`, which lies in one link of `W`, and that link is `j`. So two decided
    positions at most four apart have the same value. Put
    `R a = j` if some decided position within distance 2 has value `j`; otherwise `R a = min S_a`.
    Extend `R` outside `T` by its values at the ends of `T`.
  * `R a ∈ S_a` in both cases. `R` is a chain map: two runs `S_a`, `S_{a+1}` of length at most two
    that meet have least elements at most one apart, and a decided value lies in every `S_{a′}`
    within distance 4.
  * For `j ∈ W`, take `z` with `φ z` in `d_j` and in no other link of `W`, and `a ∈ T` with
    `z ∈ f_a`: `a` is decided with value `j`, so `R = j` on the positions of `T` within distance 2
    of `a`, three of them at least (`T` has at least four links).
* `bj_theorem8_cor_sub` (**the corollary on a sub-arc**, as Step 3 (4) uses it, p. 187). For
  `n ≥ 3`: transfer `bj_theorem8_cor` to the space `Q(a, b)` with `g` rescaled. The links of `E`
  restricted to `Q(a, b)` form a chain there (adjacent links meet inside every fibre, fibres being
  connected); so do the links of `F` meeting `Q(a, b)`, restricted (`meets_between` and the
  same splitting argument). Library lemmas for the transfer: `isSnakeLike_of_subcontinuum`,
  `isSnakeLike_univ_of_isSnakeLike`, `isPreconnected_preimage_Icc`,
  `isPseudoArc_subtype_of_image`; you also need that the restriction of an open map to
  `g⁻¹(S) → S` is open. For `n = 1`: `R` the zig-zag of Step 2(b) ("send the first three
  elements … into e_r; the next three into e_{r+1}, ⋯, the next three into e_s, the next three
  into e_{s−1}, ⋯", p. 184), with `ε` so small that every run covering a fibre has at least
  `6ℓ + 3` links. If a form with the run's links required to meet the fibre is easier, adjust and
  say so.
* `bj_theorem5_window`: transfer `bj_theorem5` (repaired, batch 198) to `Q(a, b)` with the run as
  the chain, and put `A ∪ g⁻¹[0, a]`, `B ∪ g⁻¹[b, 1]`.
* `exists_window_set`. The repaired Theorem 5 needs `U` to contain no set `F.link k ∩ q_s`.
  Bing–Jones (p. 185) choose `U_i` without this condition, as the printed Theorem 5 (false, BJ.5)
  allows. Proof:
  * There is `ρ > 0` with `diam(f_k ∩ q_s) ≥ ρ` for all `s ∈ [a, b]` and `k` in the run.
    Otherwise take `s_ν → s` and a fixed `k` with diameters tending to 0. Pick `z ∈ f_k ∩ q_s`
    and `r > 0` with `B(z, 2r) ⊆ f_k` and `2r` below the spread `κ` of the fibres
    (`exists_fibre_spread`). Lower semicontinuity (`g` open) gives `z_ν ∈ q_{s_ν}` tending to `z`.
    For large `ν`, `z_ν ∈ B(z, r/2)`; the connected `q_{s_ν}` leaves `B(z, r)`, so it meets the
    sphere of radius `r` about `z`, inside `f_k`. So `diam(f_k ∩ q_{s_ν}) ≥ r/2`.
  * Take `U` the intersection of `g⁻¹((a, b))` with a ball inside `f_y` about a point of
    `f_y ∩ g⁻¹((a, b))`, of radius below `ρ/2` and below its distance to the complement of `f_y`.
* `isFibreFine_of_isEpsChain`: two adjacent links of mesh `< κ/3` have a union of diameter
  `< 2κ/3`, so they cannot cover a fibre of spread `κ`.

## 4. The step (skeleton §4) — main item

`BJStep`: given `X`, `Y`, `f`, `g` as in Theorem 10, homeomorphisms `h₀`, `h₁` of the end fibres,
chains `D` on `X` (private points) and `E` on `Y` (fibre-fine) covering, `H` with Conditions A
and C, and `δ > 0`, there are a chain `E′` on `Y` in Bing–Jones's sense, covering, of mesh `< δ`,
with private points, and a chain map `K` of `E′` onto `D` with A′ (`IsFibreChainMap g f E′ D K`),
C′ (`EndCompat g f h₀.symm h₁.symm E′ D K`) and B′ (`e′_k ⊆ e_{H(K k)}`). It is Bing–Jones's
Step 3 (pp. 187–188, "much like Step 2"), with Steps 2(c)–(h) (pp. 184–186) adapted as in §1.
Notation: `p_x`, `P(J)` on `X`; `q_x`, `Q(J)` on `Y`. A superscript `c ∈ {0, 1}` marks an end
(`T⁰`, `W¹`, …); subscripts `i` mark sub-arcs and cuts. `N₀` is the number of sub-arcs (the
skeleton's `N` is the number of links of `E′`).

**(a) Sub-arcs.**
* `bj_step1b` for `f` and `D` gives `δ_D`. Take `N₀ ≥ 1` and `η > 0` with `1/N₀ + 2η ≤ δ_D` and
  `η < 1/(4N₀)`.
* For `i ≤ N₀` put `c_i = i/N₀`; for `i < N₀` put `J_i = [c_i − η, c_{i+1} + η] ∩ [0, 1]`.
* `[r_i, s_i]`: a run of `D` covering `P(J_i)` from which neither end link can be dropped. By
  `bj_step1b` it properly covers every `p_x`, `x ∈ J_i`.

**(b) Targets.** `H([r_i, s_i])` is a run `[a_i, b_i]` of `E`.
* By A, its links meet every `q_x` (`x ∈ J_i`) and cover `Q(J_i)`.
* By `IsFibreFine g E`, it has one link or at least three.
* `bj_theorem8_cor_sub` on `J_i`, with this run as `E` and `H` restricted as `H₁`, gives `ε_i`.

**(c) End runs.** For `c ∈ {0, 1}`:
* `W^c`: a run of `D` covering `p_c` from which neither end link can be dropped.
* `exists_point_only_of_minimal` gives the hypothesis `hpriv` of `exists_pattern`, with
  `φ = h_c⁻¹`.
* `exists_pattern` gives `ε^c`.

**(d) The chain `F` and the maps.**
* `ε`: below every `ε_i`, `ε⁰` and `ε¹`, and so small that every link of `F` has a `g`-image of
  diameter `< η/4`.
* `F`: an `ε`-chain covering `Y`.
* `R_i : F → [r_i, s_i]` from (b):
  * **(R1)** `f_a ∩ Q(J_i) ⊆ e_{H(R_i a)}`;
  * **(R2)** for `x ∈ J_i`, every `j ∈ [r_i, s_i]` is `R_i` of three consecutive links of any run
    of `F` covering `q_x`.
* `R^c` from (c), a chain map of `F` into `D` with values in `W^c` on the links meeting `q_c`:
  * **(R3)** for `f_a` meeting `q_c`, `h_c⁻¹(cl f_a ∩ q_c) ⊆ d_{R^c a}`; each `j ∈ W^c` is `R^c`
    of three consecutive links meeting `q_c`.

**(e) Windows.**
* Runs: `T⁰`, `T¹` are the runs of `F` meeting `q₀`, `q₁`; `T_i` (`1 ≤ i ≤ N₀ − 1`) the run
  meeting `q_{c_i}`. Write `Q^c_τ` for `g⁻¹ {x : |x − c| ≤ τ}`.
* `τ ∈ (0, η/4)` so small that:
  * `T^c` properly covers `q_x` and `W^c` properly covers `p_x` whenever `|x − c| ≤ τ`;
  * `T_i` properly covers `q_x` whenever `|x − c_i| ≤ τ`;
  * for every `f_a ∈ T^c`, `cl f_a ∩ Q^c_τ ⊆ e_{H(R^c a)}`.

  The last holds for `x = c`: by (R3) and C, `cl f_a ∩ q_c ⊆ h_c(p_c ∩ d_{R^c a}) ⊆ e_{H(R^c a)}`.
  Then use compactness. Bing–Jones's version is the sentence of p. 188 in §6 item 6.
* Windows: `L⁰ = [τ/4, τ/2]`, `L¹ = [1 − τ/2, 1 − τ/4]`, `L_i = [c_i, c_i + τ/2]`.
* Transition links: `adjacent_of_properCover`, with `C = p_c` or `p_{c_i}`, gives:
  * `y⁰ ∈ T⁰` with `R⁰(y⁰)`, `R_0(y⁰)` adjacent. `R⁰` carries `T⁰` onto `W⁰` and `R_0` carries it
    onto `[r_0, s_0]` (by (R3), and (R2) at `x = 0`). Both properly cover `p₀`.
  * `y¹ ∈ T¹` likewise (`R_{N₀−1}`, `R¹`).
  * `y_i ∈ T_i` (`R_{i−1}`, `R_i`): `c_i ∈ J_{i−1} ∩ J_i`.
* Transition sets: `exists_window_set` gives `U⁰ ⊆ f_{y⁰}` over the interior of `L⁰`, `U¹`, and
  `U_i ⊆ f_{y_i}` over the interior of `L_i`. `bj_theorem5_window` gives closed sides `A`, `B`
  for each.
* Regions:
  * `Z⁰ = A⁰ ⊆ Q[0, τ/2)`, map `R⁰`;
  * `Z_i = B_i ∩ A_{i+1}` (`i < N₀`), map `R_i`, with `B_0 := B⁰` and `A_{N₀} := A¹`;
  * `Z¹ = B¹`, map `R¹`.

  The regions are closed, pairwise disjoint, and cover the complement of the transition sets.
  `Z_i ⊆ Q(J_i)`. At each transition set the *left map* is the map of the region on its `A` side
  and the *right map* that of the region on its `B` side.

**(f) `E′` and `K`.**
* `μ > 0`, below:
  * `δ`, and a Lebesgue number of `F`;
  * the distances between distinct regions, and from each transition set to the regions not next
    to it;
  * the distance between the two sides `A`, `B` of each window;
  * the distance from each closed transition set to the complement of its link `f_y`;
  * a number such that a set of diameter `< μ` has a `g`-image of diameter `< τ/4`; meeting
    `Q[0, τ/2]`, it lies in a link of `T⁰` (likewise at 1); meeting `Z_i` or `U_i`, it lies in
    `Q(J_i)` or `Q(J_{i−1} ∩ J_i)`.

  The windows are more than `τ/4` apart, so a set of diameter `< μ` meets at most one transition
  set; and a set meeting `q_c` has its `g`-image within `τ/4` of `c`, so it meets no transition
  set.
* `G`: a `μ`-chain in Bing–Jones's sense covering `Y`.
* For a link `e″` of `G`:
  * if `e″` meets a transition set `U` (link `f_y`), then `e″ ⊆ f_y`, and `K(e″)` is the left map
    at `y` if `e″` meets the side `A`, otherwise the right map at `y`;
  * otherwise `e″` meets exactly one region; take a link `f_a ⊇ e″` of `F` (of `T^c` in `Z^c`),
    and `K(e″)` is the region's map at `a`.

**(g) Verification.**
1. **Chain map** (Step 2(f), p. 185):
   * two adjacent links in one region lie in adjacent or equal links of `F`;
   * a link meeting `U` and an adjacent link not meeting it meet on the same side, so both use
     the same map, at `f_y` and at a link of `F` meeting `f_y`;
   * two links meeting `U` both lie in `f_y`, and the two maps are adjacent at `y`.
2. **B′.**
   * In `Z_i`: (R1), since `e″ ⊆ f_a ∩ Q(J_i)`.
   * In `Z^c`: the choice of `τ`.
   * At a transition: `e″ ⊆ f_y ∩ Q(J_{i−1} ∩ J_i)`, where both maps satisfy (R1); at the ends,
     (R1) or the choice of `τ`.
3. **C′.** A link meeting `q_c` meets no transition set (the choice of `μ`), so it lies in `Z^c`.
   There `K = R^c(a)` with `e″ ⊆ f_a`, and (R3) applies.
4. **A′, first clause.** If `e″` meets `q_x`, then `x` lies in the range of the map used (`J_i`,
   or `[0, τ]` at 0), and the value lies in `[r_i, s_i]` (or `W^c`), whose links all meet `p_x`.
5. **A′, second clause** (Step 2(h), p. 186). Let `C″` be a run of `G` properly covering
   `q_x`. It suffices to find a run `S` of `D` properly covering `p_x` with every `j ∈ S` equal to
   `K` of a link of `C″`. Choose a map `M`, a run `T` of `F`, and `Γ ⊆ q_x` such that:
   * every `j ∈ S` is `M` of three consecutive links `f_{a−1}, f_a, f_{a+1}` of `T`;
   * `Γ` meets every link of `T`;
   * every link of `G` meeting `Γ` takes its value from `M`.

   For `j ∈ S`, take `z ∈ Γ ∩ f_a` and `e″ ∈ C″` containing `z`. The `F`-link used for `e″`
   contains `z`, so it is `f_{a−1}`, `f_a` or `f_{a+1}`, and `K(e″) = j`. The cases:
   * `x ∈ [0, τ/4)`: `M = R⁰`, `T = T⁰`, `Γ = q_x`, `S = W⁰`.
   * `x ∈ L⁰`: by the window dichotomy, either every link of `T⁰` meets `A⁰ ∩ q_x` (`M = R⁰`,
     `Γ = A⁰ ∩ q_x`, `S = W⁰`), or every link meets `B⁰ ∩ q_x` (`M = R_0`, `S = [r_0, s_0]`; (R2)
     at `x = 0`).
   * `x` strictly between consecutive windows: `q_x` lies in one region `Z_i`. Take `M = R_i`,
     `T` the run of `F` meeting `q_x`, `Γ = q_x`, `S = [r_i, s_i]`.
   * `x ∈ L_i`: as at `L⁰`, with `T_i`, `R_{i−1}` on the side `A_i` and `R_i` on the side `B_i`,
     by (R2) at `x = c_i`. For `x ∈ L_i`, `A_i ∩ q_x ⊆ Z_{i−1}` and `B_i ∩ q_x ⊆ Z_i`.
   * At 1, symmetrically.
6. **`K` onto.** Let `z` be a private point of `d_j`, and `x = f(z)`. The run `S` of item 5 for
   `x` covers `z`, so `j ∈ S`, and `j` is a value of `K`.
7. **Private points.** Shrink `G` with `exists_privatePoint_shrink` (`Y` is a non-degenerate
   continuum) and keep `K`. Every property above survives: the links only shrink, and a run of
   shrunk links properly covering `q_x` comes from a run of `G` properly covering `q_x`.

**(h) If the step resists**, state which part, and prove what you can of it as separate lemmas.
`bjThm10_of_step` stands without it.

## 5. Theorem 10 and the classification (skeleton §5)

`bjThm10_of_step`:
* **Spreads.** `κ_X`, `κ_Y` from `exists_fibre_spread`.
* **Stages.** A stage is `(D, E, H)`:
  * `D` on `X` and `E` on `Y` cover, are chains in Bing–Jones's sense and have private points;
  * `D` is fibre-fine for `f` and `E` for `g`;
  * `H` satisfies A and C;
  * both meshes are `< ε`.
* **Stage 0.** The one-link chains `{X}`, `{Y}`, `H = id`, `ε₀ = diam X + diam Y + 1`.
* **From stage `i` to `i + 1`.** Apply `BJStep` to `(X, Y, D, E, H)` with `δ_i`, getting
  `(E′, K_i)`. Then apply it to `(Y, X, E′, D, K_i)` with `h₀.symm`, `h₁.symm`, getting
  `(D′, H_{i+1})`. Take `δ_i = min(1/2^{i+1}, κ_X/3, κ_Y/3)`, so that the new chains are
  fibre-fine (`isFibreFine_of_isEpsChain`). Conditions B and B′ of `zigzag_homeomorph` are the
  inclusions of the two steps.
* **The homeomorphism.** `zigzag_homeomorph` with `P = univ`, `Q = univ`.
  * `zigzag_fibre` with `φ = f`, `ψ = g`: its `hA` is A's first clause.
  * The ends: by C, `h₀ x ∈ H_i d(x, i)` for every `i`, so `h₀ x = h x` by the characterization.
    Likewise for `h₁`.
  * Pass from `univ ≃ₜ univ` to `X ≃ₜ Y`.

Then `bjThm10`, and the corollaries of the skeleton:
* the classification with Domokos–Prajs's third class, with no named hypothesis;
* homogeneity and uniqueness of circles of pseudo-arcs;
* the classification with Bing–Jones's third class and its plane form, given only
  `BJPlaneExample`.

## 6. Ledger

New section "Bing–Jones §6, Theorem 10 (batch 201)", in the convention "printed X, read Y". Check
each item at 400 dpi.

1. **Step 3 (3), p. 187**: "The image under h⁻¹ of any subset of q₀+q_{1/k}+ ⋯ +q₁ of diameter
   less than 5ε lies in an element of E₁." Printed `E₁`, read `D₁` (`h⁻¹` maps into `P`).
2. **Step 2(b), p. 184**: the existence of `R_{i/n}` is argued only through the "precaution";
   supplied (`exists_pattern`).
3. **Step 2(c), pp. 184–185**: Theorem 6 cited without saying which chain plays `E`. With `E₁`
   its hypothesis fails; with the subchain spanned by the two images it holds (§3). Unargued
   step; supplied (`adjacent_of_properCover`). (Its printed `R_{(2i+1)/n}` is already BJ.11's
   misprint.)
4. **Step 2(c), p. 185**: "By Theorem 5 there is an open set U_i in P(i/n, i/n+ε)·f_y such that
   Ū_i⊂f_y and P−U_i is the sum of two mutually exclusive closed sets A_i, B_i …". Theorem 5 as
   printed is false (BJ.5); the repaired form needs `U_i` small (`exists_window_set`), which
   Bing–Jones do not provide.
5. **Step 2(i), p. 187**: "Theorem 9 assures us that h can be extended in this fashion." The
   hypothesis of Theorem 9 (a link with a private point mapped to each link) is not checked for
   `D₁`, `H₁` on `p_{i/k}`. Not needed on this route.
6. **Step 3, p. 188**: "In the analogue to Step 2c we pick ε so small that the Q_i, V_i, U_i we
   obtain will have the property that if f_j is an element of the subchain of F irreducibly
   covering q_{i/k}, then (V_i+Q_i+U_i)·f_j⊂H₁R_{i/k}(f_j)." Unargued. The reason they give,
   `q_{i/k}·f_j ⊂ H₁R_{i/k}(f_j)`, needs the closures, `q_{i/k}·f̄_j ⊂ H₁R_{i/k}(f_j)` (§4 (e)).
7. **Steps 4, 5, ⋯, p. 188** (BJ.13): "These steps are essentially repetitions of Step 3." The
   induction is left to the reader; supplied (`bj_step`, `bjThm10_of_step`).
8. **Route**: the homeomorphisms on cut fibres (Step 1(c), Step 2(i)) are not needed, and Theorem
   9 is not used in Theorem 10 (§1). Not a defect.
9. **"the subchain … that irreducibly covers"** (pp. 182–188): a minimal covering run of a set
   is unique when it has two links or more; two different ones occur only when the set lies in two
   adjacent links, each covering it alone. Any one serves. Harmless.
10. **Step 3, p. 187**: "It takes the subchain f_t, f_{i+1}, ⋯, f_u of F that irreducibly covers
    Q(i/k, (i+1)/k) …": printed `f_{i+1}`, read `f_{t+1}`.
11. **Step 3, p. 187**: condition "(1) f_j⊂H₁R_{(2i+1)/2k}(f_j)" asks for the whole link `f_j`,
    while the corollary to Theorem 8, read with `Q(i/k, (i+1)/k)` as the space, controls only
    `f_j·Q(i/k, (i+1)/k)`. The construction needs only that part ((R1) in §4).

Add any other defect of Steps 2(d)–(h) you meet. Count nothing yourself; say which items, if any,
you would count.

## 7. Non-vacuity

* Definitions: one-link chains (all four conditions hold when `f` and `g` are onto), `n = 0`, and
  `nonvac_conditions`.
* `exists_point_only_of_minimal`, `adjacent_of_properCover`: chains on `[0, 1]` with at least
  three links.
* `exists_pattern`: a plane pseudo-arc `Q`, `φ` the inclusion into the plane, `D` the chain of
  `nonvac_bj_chains` shrunk to private points (`exists_privatePoint_shrink`).
* `isFibreFine_of_isEpsChain`: `[0, 1]²` with the first projection (`κ = 1`) and a chain of
  small open squares along one fibre.
* `bj_theorem8_cor_sub`, `bj_theorem5_window`, `exists_window_set`, `BJStep`, `BJThm10`: their
  hypotheses need a continuous snake-like arc of pseudo-arcs. Under `BJPlaneExample` the halves of
  the plane circle of pseudo-arcs give one. A conditional witness is welcome, not required.
* `BJStep` and `BJThm10` as named `Prop`s: say what the degenerate inputs give (one-link chains;
  `h₀`, `h₁` arbitrary).

## 8. Order

§2 with the tests; §3; `bjThm10_of_step` (§5); then `bj_step` (§4, the main item); then the
corollaries. §6 alongside.

## 9. Deliverables

1. **The items of §§2–5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch201.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section of §6.
3. **Notes:** append to `doc/notes/bj59.md`.
4. **Publish the changes, as in batch 200**: `doc/batches/batch201-files.tar.gz` with every file
   added or changed (including the commission and skeleton copies) and
   `doc/batches/batch201-MANIFEST.txt`.
5. **The report.** Its first line names the commission it read. It covers the items in order, the
   shape changes, the non-vacuity notes, the ledger entries, the axioms used by each theorem, and
   what remains (the plane example, `BJPlaneExample`).
