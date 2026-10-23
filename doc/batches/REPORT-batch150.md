Commission read: `doc/batches/COMMISSION-batch150.md` (batch 150, Part F, Jones 1949 II: Whyburn's order theorems; Moore 1922).

# Report, batch 150

**Outcome.**

| item | outcome |
|---|---|
| A: `whyburn_3_2` | **proved** (statement verbatim) |
| A: `whyburn_8_4` | **proved** (statement verbatim) |
| A: `whyburn_8_41` | **proved** (statement verbatim) |
| A: `whyburn_9_2` (open in batch 149) | **proved** (statement verbatim) |
| A: `jones49_some_order_two` (open in batch 149) | **proved** (statement verbatim) |
| B: Moore 1922, Theorems 1, 2, 3 | **proved** (statements verbatim) |
| B: Moore 1922, Theorem 4 (both directions) | **open**, obstruction in `OPEN.md`. Proved parts: the boundary is a continuum; the PNAS step is reconstructed |

**Build and axioms.**
* `lake build HPC` succeeds with `import HPC.Jones.Jones49B` at the end of `HPC.lean`.
* No new file contains `sorry`. The one open statement, Moore's Theorem 4, is kept verbatim as a
  comment at the end of `HPC/Jones/Moore22T4.lean`.
* Every theorem of the five new files uses only `propext`, `Classical.choice` and `Quot.sound`
  (77 theorems). The audit is `doc/batches/audits/axioms-batch150.txt`, produced by
  `axioms-batch150.lean`.
* `axioms.txt` is regenerated (1155 lines: 1128 + 27 new), with `sorryAx` in no line. The previous version is kept as
  `doc/batches/audits/axioms-before-batch150.txt` (1128 lines).
* `Axioms.lean` has the new group *Whyburn Ch. III; Moore 1922 (batch 150)*, before the group of
  `*_false` helper names. The batch-149 comment calling (9.2) and `jones49_some_order_two` open is
  updated in place.

**Uploads.**
* The commission is at `doc/batches/COMMISSION-batch150.md`.
* The skeleton is kept verbatim at `doc/batches/skeletons/Jones49B-batch150.lean`.
* The two PDFs are at `doc/sources/moore1922.pdf` and `doc/sources/moore1922-transcription.pdf`.
  They are not committed, since `*.pdf` is in `.gitignore`, as for the earlier sources.

**Files.**
* `HPC/Jones/Jones49Chain.lean`: separation chains (`SepChain`).
* `HPC/Jones/Jones49Sep.lean`: the separating point-order theorem for open sets, and the two
  recorded definitions.
* `HPC/Jones/Jones49B.lean`: the skeleton's Whyburn items.
* `HPC/Jones/Moore22.lean`: Moore's four definitions and Theorems 1–3. The skeleton's Moore section
  is moved here; the commission allows splitting.
* `HPC/Jones/Moore22T4.lean`: the proved parts of Theorem 4, and Theorem 4 as a comment.

**Edits to existing files.**
* `HPC.lean`: one import.
* `HPC/Jones/Jones49A.lean`: the two commented statements are deleted, nothing else. Its module
  docstring still says that (9.2) and `jones49_some_order_two` "are left open". The rules allow only
  the deletion, so that sentence is now stale; `OPEN.md` and this report are authoritative.
* `Axioms.lean`, `axioms.txt`, `README.md`, `LEDGER.md` §6 (new subsection at the end) and `OPEN.md`.

---

## 1. Item A: Whyburn, Ch. III

### Route

Not Whyburn's. One theorem gives all five items:

> **`countable_sepPoint_not_hasOrder_two`** (`Jones49Sep.lean`). In a locally compact separable
> metric space, for an open set `R`, the set `{p | IsSepPointOf p R ∧ ¬ HasOrder p 2}` is countable.

**The proof.**
1. **Countably many families.** A separating point `p` of `R`, with separation `A ∪ B` of `R − p`,
   has a basic open set `U ⊆ A` and a basic open set `W ⊆ B`, each meeting the component `Q` of
   `p` in `R`. For each of the countably many pairs `(U, W)`, the points so obtained, `sepT R U W`,
   all lie in one component of `R` (`sepT_mem_component`). Together with their separations they form
   a `SepChain`.
2. **The chain is linearly ordered** by Whyburn's natural order (1.31): `p < q` iff `q ∈ B p`
   (`lt_total`, `lt_trans`, `lt_asymm`; sides nested, `B_sub`, `A_sub`, Whyburn's (1.2)).
3. **Two countable exceptional sets:**
   * the points that are not limits of the chain from both sides (`countable_not_good`; Whyburn's
     (2.1), via `countable_not_mem_closure_of_lt`);
   * the two-sided limits whose *residue* is nonempty, i.e. some point of `Q − p` is not separated
     from `p` by two points of the chain on either side (`countable_res`). This is the step of
     (2.2) that discards the cuttings `H` containing no dense point `pₕ` separated from `H`; the
     residues of distinct points are disjoint open sets.
4. **Order `≤ 2` at every other point.** The intervals `M x y` about `p` are preconnected and closed
   in `R` (`M_isPreconnected`, `M_closed`). With empty residue, some interval lies in a given small
   compact ball (`exists_small_interval`). A cut-wire argument in that ball
   (`exists_clopen_of_connectedComponentIn_disjoint`) gives an open `V ∋ p` inside the ball with
   `frontier V ⊆ {x, y}` (`exists_open_frontier_pair`). Hence `OrderLE p 2` (`orderLE_two`).
5. **Not order `≤ 1`.** A separating point is not of order `≤ 1`
   (`not_orderLE_one_of_isSepPointOf`), so order `≤ 2` gives order exactly 2
   (`hasOrder_two_of_isSepPointOf`).

**What is not used:** (8.2), (8.3) with its corollaries, the non-separated cuttings and potential
order of §2 ((2.2)–(2.22)), and (3.1). The order of §1 is used as `SepChain.lt`, as far as (3.2)
needs it, which the commission asked for. §2 is not needed beyond the two steps named in 3.

### The items

* **`whyburn_3_2`** (`[CompactSpace X] [ConnectedSpace X]`): `{p | ¬ IsConnected {p}ᶜ ∧ ¬ HasOrder p
  2}` is countable. A cut point is a separating point of `univ`. The one-point space, where
  `{p}ᶜ = ∅` is not connected, contributes at most one point.
* **`whyburn_8_4`, `whyburn_8_41`**: the case `R = univ`.
* **`whyburn_9_2`**: Whyburn's own proof. A local separating point `p ∈ R` separates every basic
  open `U` with `p ∈ U ⊆ R`, by `whyburn_9_1` (batch 149). Then apply the theorem to each of the
  countably many basic open sets. No passage of order from `Rᵢ` to `L` is needed: `HasOrder` is
  stated in `X` throughout.
* **`jones49_some_order_two`**: `jones49_some_order_two_of_whyburn_9_2 hX hp whyburn_9_2`. As in
  the skeleton, `[ConnectedSpace X]` is not used. It is kept, and this is noted at the statement.

**Definitions recorded** (commission A), in `Jones49Sep.lean`, not used in proofs:
* `IsGeneralizedContinuum Y`: locally compact, separable, connected metric (Ch. I).
* `PotentialOrderLE 𝒬 X₀ n`: Whyburn's p. 45 definition. `X₀` is closed, and there are open sets
  `U₁ ⊃ Ū₂ ⊃ U₂ ⊃ ⋯` with `X₀ = ⋂ Uᵢ` and each `F(Uᵢ)` in the sum of at most `n` elements of `𝒬`.

**Shape changes:** none. All five statements are the skeleton's, character for character.

---

## 2. Item B: Moore 1922

All definitions and Theorems 1–3 are verbatim from the skeleton. They are in
`HPC/Jones/Moore22.lean`, over `Pt = ℝ × ℝ` with its sup metric. Property S, connectedness im
kleinen and uniform connectedness im kleinen are unchanged under the uniformly equivalent
Euclidean metric.

* **Theorem 1** (`moore22_theorem1`): **proved**. Moore takes the limiting set of the sets `tₙ`. The
  proof instead builds an explicit chain:
  * connected sets of summable diameters (`ε/16 · 2⁻ᵏ`) join points `Pₖ → P` and points
    `Xₖ → X`, and join `X₀` to `P₀`;
  * the union, with `X` and `P`, is connected, lies in `M̄` and has diameter `< ε`.

  This avoids both the `K*`/`K̄` slip and the connectedness of a limiting set (ledger, check 1).
* **Theorem 2** (`moore22_theorem2`): **proved**, by Moore's argument. Some piece `M_s` has `P` in
  its closure, so `M_s ∪ {P}` is connected with the same diameter. It is run with the finitely many
  pieces whose closure contains `P`.
* **Theorem 3** (`moore22_theorem3`): **proved**, by Moore's argument with `ε/3` (ledger, check 3).
* **Theorem 4**: **open**, both directions. The statement is kept verbatim as a comment
  (`Moore22T4.lean`). **Proved** (`Moore22T4.lean`):
  * `isPreconnected_compl_of_mooreSimplyConnected`: the complement of a bounded open set that is
    simply connected in Moore's sense is connected;
  * `isConnected_frontier_of_mooreSimplyConnected`: with unicoherence of the plane
    (`plane_unicoherent`), the boundary of a bounded connected open Moore-simply-connected set is a
    continuum. So "continuous curve" in Theorem 4 means "locally connected", and property S is
    needed for nothing else;
  * `locallyConnectedSpace_of_cikAt`: connected im kleinen at each point implies locally
    connected;
  * `exists_crossing_continua`: **the PNAS step, reconstructed** (commission B). If a compact
    connected plane set `M` is not connected im kleinen at `P ∈ M`, there are radii `r₁ < r₂` and
    pairwise disjoint continua `tₙ ⊆ M` lying in `r₁ ≤ d(·, P) ≤ r₂` and meeting both squares.

  **What the PNAS step needs.** Two boundary-bumping arguments, about 130 lines in total.
  * Let `ε` witness the failure, `r₂ = ε/3`, `r₁ = ε/6`. Points of `M` arbitrarily near `P` lie
    outside the component `Γ` of `P` in `M ∩ B̄(P, r₂)`.
  * Their components there are infinitely many, since a finite union of them is closed and misses
    `P`. They are pairwise disjoint, and each meets the outer square by boundary bumping.
  * In each, a second boundary bumping, from a point on the outer square within the part outside
    `B(P, r₁)`, gives `tₙ`.

  The argument is short, and **PNAS 4 is not needed** for this step.

  **The obstruction (`OPEN.md`).** What is missing is one plane-separation theorem that the
  repository lacks: a *sector theorem* for two disjoint continua crossing an annulus.
  * The two continua and the two circles bound two pieces of the annulus. A connected set too
    small to reach either circle, joining points of different pieces, meets one of the continua.
  * Together with it: the cyclic order on the middle circle of the points where infinitely many
    disjoint crossing continua meet it.

  Sufficiency (p. 236, "must clearly contain a point either of `kₙ₋₁` or of `kₙ₊₁`") needs it
  directly. Necessity (p. 237) needs it twice: for the continua `R̄ₙ` in the boundaries of the
  components `Rₙ`, whose existence is a further plane step, and for "It can easily be seen that no
  two of the sets `R̄₂, R̄₄, …` …". The repository has the θ-curve theorems of F.A. §6 for *arcs*
  (`HPC/Moore/Sec6Th26.lean` and neighbours), Janiszewski's theorem (`janiszewski_compact`) and
  unicoherence, but not the theorem for continua. It is a sizeable plane-topology development, and
  it does not need PNAS 4.

---

## 3. Ledger entries (`LEDGER.md` §6, new subsection)

Every quotation was checked against the scan `doc/sources/moore1922.pdf`, rendered at 170 dpi,
and at 400 dpi for p. 234. Whyburn was checked against `doc/sources/whyburn1942.pdf`.

1. **p. 233, Theorem 1:** "lies wholly within K*". **Confirmed slip**, read `K̄`. Harmless.
2. **p. 234, Theorem 2:** `M_s` / `M_t`. **Not settled.** The two subscripts are printed with
   different glyphs, but both are damaged. Notational at most. The step "`M_t + P` is a connected
   subset of `M`, of diameter less than `ε`" is unargued but correct.
3. **pp. 234–235, Theorem 3:** "But these connected point-sets are all of diameter less than ε".
   **Confirmed slip** (`≤ 2ε`). Harmless with `ε/3`.
4. **p. 236:** "the point-set tₘ contains at least one point Aₘ on K*". **Confirmed**: the bar is
   missing here and present elsewhere. "For each positive integer m(1 ≤ m ≤ n)": **confirmed
   misprint** for `4ⁿ`.
5. **p. 237:** "Let ε = (b − c)/4". **Confirmed**: negative, since `c = 3b`. Read `(c − b)/4`. The
   three unargued steps are confirmed and quoted in the ledger:
   * limit point on `T_m̄`: true, by an easy argument not given;
   * `R̄ₙ` in the boundary of `Rₙ`: a plane step;
   * "It can easily be seen …": the sector theorem.

   **New, not in the commission's list:** the points `Yₘ`, `Yₙ` used for the final contradiction
   lie in `R`, not in `M`. So "there exists no connected subset of M of diameter less than ε that
   contains both Yₘ and Yₙ" is vacuous. Also, small connected subsets of `M` through points of
   `H_m̄` need not stay in `I`. The ledger gives a repair:
   * points of `R̄ₙ` on the square midway between `K_m̄` and `H_m̄`;
   * `ε/2`;
   * failure of connectedness im kleinen at a limit point.

   **A defective step, repairable within the proof.**
6. **p. 237** (not p. 236): "there must exist at least one value m̄ … such that no two of the
   connected sets R_{m̄P₁}, R_{m̄P₂}, … have a point in common". **Confirmed unargued.** It needs
   that for fixed `m` the sets `R_{mP}` are equal or disjoint, which holds because they are
   components. Harmless.
7. **Typographical, all confirmed:** "fie" (p. 233), "curce" (p. 235), "a sumed" (p. 234,
   footnote 1).
8. **Whyburn:**
   * **(3.1)–(3.2):** (3.1) is stated without proof ("Thus we have") from (2.2) and (2.22). The
     unargued steps are listed in the ledger. Harmless, and not used.
   * **(8.4):** "since N is ordered as in (1.31), there exist points x and y of N … such that
     δ[Q₂(x)·Q₁(y)] < ε/4". This is **unargued and does not follow from what is cited**. It needs
     two-sided limits and trivial residue, which come from inside the proof of (2.2), not from the
     statement of (3.2). The formalization proves it (`exists_small_interval`) off a countable set.
   * "R·Q = Q₂(x)·Q₁(y) and F(R)·Q = x + y": routine, unargued.
   * **(8.3) as stated:** its hypothesis on "convergent sequence\[s\] of components" is never
     satisfied if the constant sequence `C` is allowed. Read "distinct components", as (8.4) does.
     Harmless.

**Classification.** Only the new item in check 5, Moore's final step of necessity, is a defective
step in a proof. It is repairable within the proof. The others are slips, misprints or unargued
steps. Whether to count it with the twelve defective proofs is the commissioner's call: the
argument is right in outline, but the sentence as printed proves nothing.

---

## 4. Axioms by theorem

All of the following, and every other theorem of the five files, depend on exactly
`[propext, Classical.choice, Quot.sound]` (`doc/batches/audits/axioms-batch150.txt`):

* `whyburn_3_2`, `whyburn_8_4`, `whyburn_8_41`, `whyburn_9_2`, `jones49_some_order_two`;
* `countable_sepPoint_not_hasOrder_two`, `countable_sepPoint_not_orderLE_two`, `countable_sepT`,
  `sepT_mem_component`, `not_orderLE_one_of_isSepPointOf`, `hasOrder_two_of_isSepPointOf`,
  `OrderLE.mono`;
* `SepChain.countable_not_good`, `SepChain.countable_res`, `SepChain.exists_small_interval`,
  `SepChain.exists_open_frontier_pair`, `SepChain.orderLE_two`,
  `SepChain.countable_of_not_orderLE_two`, `countable_not_mem_closure_of_lt`,
  `exists_clopen_of_connectedComponentIn_disjoint` (and the 44 order and interval lemmas of
  `Jones49Chain.lean`);
* `moore22_theorem1`, `moore22_theorem2`, `moore22_theorem3`;
* `isPreconnected_compl_of_mooreSimplyConnected`, `isConnected_frontier_of_mooreSimplyConnected`,
  `locallyConnectedSpace_of_cikAt`, `exists_crossing_continua`.

---

## 5. Reading plan for batch 151: Whyburn 1939 §14 (`doc/sources/whyburn1939.pdf`, pp. 747–749)

**The Theorem** (p. 747): "If M is a compact semi-locally-connected plane continuum, the boundary
of each complementary domain of M is locally connected." The proof shows that `R` has property S
(pp. 747–748) and ends: "Thus R has property S and hence by a theorem of R. L. Moore's [Fund. Math.
3] the boundary of R is locally connected."

### (a) The unbounded complementary domain

Whyburn: "Clearly we may suppose R bounded, since an inversion of the plane can be used to throw R
into a bounded region complementary to the image of M."
* **The inversion needs a centre `O` outside `M ∪ R`.**
  * A centre in `R` keeps the image of `R` unbounded: `ι(∞) = O` and `ι(O) = ∞` both stay in the
    image of `R ∪ {∞}`.
  * A centre in `M` makes the image of `M` noncompact.
* So the reduction works **only when `M` has a bounded complementary domain**. It fails, for
  example, for a closed disk, which is a compact, cyclic, semi-locally-connected plane continuum
  whose only complementary domain is unbounded. This is a gap in the printed proof, not in the
  Theorem.
* **Recommended route.** Avoid the inversion and Moore's global property S. What Whyburn's
  contradiction actually produces is local: points `pᵢ → p ∈ M` of `R`, no two of which can be
  joined in `R` by a connected set of diameter `< 4ε`.
* Moore's sufficiency argument (p. 236) uses exactly the negation of this local condition. It does
  not use boundedness or simple connectivity of `R`. The `Cₘ`, `Cₙ` are near the boundary points
  `Bₘ`, `Bₙ`, and the connected sets joining them lie in `R`.
* Batch 151 should therefore state Moore's sufficiency in local form:
  * a domain `R`, bounded or not;
  * with connected boundary;
  * such that near each boundary point no infinite set of points of `R` is pairwise "far" in `R`;

  has a locally connected boundary. Theorem 4's sufficiency, global property S on a bounded domain,
  is the special case.
* The connectedness of the boundary of any complementary domain of a continuum is needed for
  `exists_crossing_continua`. It follows from unicoherence, as in
  `isConnected_frontier_of_mooreSimplyConnected`, once `Rᶜ` is known to be connected; see (b).

### (b) Are bounded complementary domains simply connected in Moore's sense?

**Yes**, and the argument is short. Let `R` be a bounded complementary domain of a continuum `M`.
1. `F = Rᶜ` is connected: `M` is connected, and the closure of every other complementary domain
   meets `M`. `F` is also unbounded.
2. If `H` is bounded with `frontier H ⊆ R`, then `F` misses `frontier H`. So `F ⊆ interior H ∪
   interior Hᶜ`, a separation unless `F` lies in one of the two.
3. `F` is unbounded and `H` is bounded, so `F ⊆ interior Hᶜ`, i.e. `H ⊆ R`.

`isPreconnected_compl_of_mooreSimplyConnected` is the converse. Both should be stated in batch 151.
Under the local form recommended in (a), simple connectivity is not needed for the Theorem at all.

### (c) What (6.22) and the F.A. theorem require

* **(6.22)** (p. 737): "If x is a non-cut-point of M, … there exists an arbitrarily small
  neighborhood U of x such that M − U is connected"; "This results at once from the proof of (6.2)
  together with § 3."
  * **§14 uses a variant:** "there exists a δ > 0 and a component N of M − M·V_δ(p) which contains
    M − M·V_ε(p)".
  * **It needs:** semi-local connectedness at `p`, so that `M − V_ε(p)` lies in finitely many
    components of `M − V_δ(p)`; and (6.2) for the non-cut point `p`: any two points of
    `M − V_ε(p)` lie in a continuum missing `p`, hence missing some `V_δ'(p)`.
  * With compactness, finitely many such continua join the finitely many components, after
    shrinking `δ`.
  * The repository has `SemiLocConnAt`, `whyburn_6_1`, `whyburn_6_2` and `whyburn_6_21`
    (`HPC/Jones/Whyburn.lean`, batch 136). The §14 form is a short corollary of `whyburn_6_2`.
  * The reference "§ 3" is not needed.
* **The F.A. theorem** (footnote 14: Trans. AMS 17 (1916), pp. 131–164, no theorem number):
  "there exists a simple closed curve C ⊂ J + C_δ such that if E is the complementary region of C
  containing O, then E ⊂ I·V_δ(p)".
  * Here `J = xy + xuy` is a simple closed curve and `C_δ` a circle.
  * In substance this is **F.A. Theorem 43, corrected** (`G = {C_δ}`): a closed curve on
    `J + C_δ` whose interior is within both interiors. It was proved in batch 140
    (`HPC.Moore.fa_theorem43`, `HPC/Moore/M43.lean`) for spaces satisfying Axioms 1–8.
  * **Batch 151 must either** transport it to `ℝ²` or prove the needed instance directly. The
    instance is the component of `I ∩ V_δ(p)` containing `O`, whose boundary is a simple closed
    curve in `J ∪ C_δ`.
  * **Transport needs** that `ℝ²` with its Jordan curves satisfies Axioms 1–8. The repository has
    the converse (`m19_plane`); whether this direction is available should be checked first.
* **The second half of the proof (p. 748) also uses:**
  * **footnote 6:** a point of order 2 among uncountably many cut points. This is now
    `whyburn_3_2`, batch 150: `H` is a nondegenerate continuum of cut points of `M`, so all but
    countably many of its points are of order 2 in `M`;
  * **"Hence there exists a simple closed curve K in V_ε(p) such that K·M = c + d … and the
    complementary region D of K containing p′ lies in V_ε(p)":** the passage from order 2 in `M`
    (an intrinsic notion) to a plane Jordan curve meeting `M` in exactly two points. This is
    **unargued, and a real plane step**. It needs a Jordan curve through the two frontier points
    of a small neighbourhood, built in the complement of `M`, and arcs in complementary domains.
    It should be a separate item of batch 151;
  * the pigeonhole on the two components of `K − (c + d)`, which is routine.

### (d) Corollary 1 (stated without proof)

"If M is a compact plane semi-locally-connected cyclic continuum, the boundary of every
complementary domain of M is a simple closed curve." Footnote 16 points to Wilder's Theorem 8a,
not to an argument. A route for `B = ∂R`:
1. **`B` is a locally connected continuum**, by the Theorem and (a).
2. **Every cut point of `B` is a cut point of `M`.**
   * If `x` cuts `B`, take points of `B − x` on the two sides. Their accessibility from `R` by
     arcs follows from the local form of property S, the same condition as in (a).
   * Build an arc in `R ∪ {x}` from `x` back to `x`, through `R`: a simple closed curve `J` with
     `J ∩ M = {x}` that separates the two parts. This uses `jordan_curve_theorem`.
   * Then `M − x` meets both complementary domains of `J`, so `x` cuts `M`.
   * `M` is cyclic, so `B` has no cut point.
3. **A cyclic locally connected continuum that bounds one of its complementary domains is a
   simple closed curve.**
   * Otherwise `B` contains a θ-curve: a cyclic Peano continuum that is not a circle contains
     one. With batch 149, `menger_order_two` gives a point of `B` not of order 2; the θ-curve
     itself has to be built (arcs in Peano continua, Menger's `n`-Beinsatz). This is not in the
     repository.
   * The θ-curve has three complementary domains (F.A. Theorems 24–28, `HPC/Moore/Sec6Th26.lean`).
   * `R` lies in one of them. The open arc of the θ-curve not on that domain's boundary has a
     neighbourhood missing `R`, against `B = ∂R`.
4. **Hence `B` is a simple closed curve**, homeomorphic to `Circle` by `tscc_homeomorph_circle`.

**Inventory.** Steps 2–3 are the classical Torhorst-type argument. The ingredients:
* already present: the θ-curve separation for arcs, the Jordan curve theorem, Menger's theorem;
* to be built: arc-accessibility of boundary points from `R`, and the existence of a θ-curve in a
  cyclic Peano continuum that is not a circle.

**Suggested batch-151 items:**
1. Moore 1922 sufficiency in local form, with the sector theorem for crossing continua; this also
   closes Theorem 4's sufficiency.
2. Bounded complementary domains are Moore-simply-connected (b), and boundaries of complementary
   domains of continua are continua.
3. (6.22) in the §14 form.
4. The F.A. curve `C` in `ℝ²`.
5. The Jordan curve `K` from order 2 (c).
6. The Theorem.
7. Corollary 1 via (d).

The sector theorem in item 1 is the main work, and it is shared with Theorem 4's necessity.
