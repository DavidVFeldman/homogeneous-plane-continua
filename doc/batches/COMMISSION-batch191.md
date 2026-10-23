# Commission: batch 191 — Theorem C I: span; Cook 1967; O–T 1982, Theorem 3.6 and Corollary 3.5

**Go!** This batch runs on top of the batch-190 work. Four files come with it, as separate uploads:

* `COMMISSION-batch191.md`: this text, also pasted into the prompt.
* `OT82A.lean`: the skeleton.
  * Save it as `HPC/Span/OT82A.lean`. You may split it under `HPC/Span/`.
  * Add `import HPC.Span.OT82A` at the end of `HPC.lean`. It imports `HPC.Jones.Jones75B`.
* `oversteegen-tymchatyn1982.pdf`: save as `doc/sources/oversteegen-tymchatyn1982.pdf`. Its text
  layer is poor ("forSt asinLemma"); read the page images.
* `cook1967.pdf`: save as `doc/sources/cook1967.pdf`. A scan without a text layer, two journal
  pages per PDF page; Theorem 4 is on p. 243, the right half of the second PDF page.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Theorem C I (batch 191)");
  * `README.md`;
  * `LEDGER.md`: a new section "Oversteegen–Tymchatyn 1982 and Cook 1967", and the two changes
    asked for in §0;
  * `OPEN.md`;
  * a new notes file `doc/notes/ot82.md`.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 190

* **Delivery.** The project download was current again: its `axioms.txt` equals the overlay of
  your tarball on my batch-189 tree (2550 lines). Keep publishing the tarball and manifest (§10.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2550 lines (2479 + 71 added, none removed), with `sorryAx` in none.
  The 71 new theorems use only the standard three axioms. The five new files contain no `sorry`,
  `admit` or `axiom` outside comments.
* **Part E is complete.** `jones75_noArc`, `hagopian76_theorem1`, `bing60_plane_uncond` and
  `hagopian76_theorem2_uncond` are verified with no named hypothesis. Your shape changes
  (`exists_late_thin_pass` with `η ≤ 1`; `trap_pass` on the low strip with (H) in a minimality
  form) are accepted.
* **Ledger.** Your entries J75.6 and J75.7 are adopted. Two changes, both from an independent check
  of my own ledger made during this audit:
  1. **Hagopian 1976, Theorem 1: proof defective, statement true.** The printed proof fails at an
     identified step, the case split at `i = 2` (your certificate `blockLayersMeetSides_false`,
     batch 182), and the statement is now verified by another route. The precedents are Moore 1916
     Theorem 28 (a last step corrected) and Jones 1975's Theorem (a statement proved by a different
     proof). Record this classification in the Hagopian 1976 section of `LEDGER.md`.
  2. **The count of defective proofs.** My count had included Moore 1916 Theorems 33–34 twice,
     although they share one printed proof (Kline's) and my list counts it once. With the
     correction, the count before Hagopian 1976 Theorem 1 is fifteen; with it, sixteen. If
     `LEDGER.md` states a count (your J75.4 entry says "the count stays at sixteen"), correct it in
     the same words.

## 1. The classification after Part E; the plan

Hoehn–Oversteegen (2016, p. 180) obtain the classification from Theorems A, B, C and their
Theorem 1. A (Jones 1955) and B (Hagopian 1976) are verified. What remains:
* **Theorem C** (p. 180): "Every homogeneous indecomposable plane continuum has span zero." They
  cite [45], Oversteegen–Tymchatyn 1982 ("O–T" below), where it is the second sentence of
  Theorem 3.6.
* **Theorem 1** (p. 180): "A non-degenerate continuum X is homeomorphic to the pseudo-arc if and
  only if X is hereditarily indecomposable and has span zero." (Part F, later batches.)
* The circle-of-pseudo-arcs step (Part G, later).

**O–T's proof of Theorem C** runs as follows.
* §2 bounds the span of continua inside thin plane strips (Lemmas 2.1–2.4, Theorems 2.6–2.7).
* §3 shows that among uncountably many disjoint planar images only countably many have positive
  span (Theorems 3.1–3.2).
* Corollary 3.5 applies this to an indecomposable homogeneous plane continuum: its proper
  subcontinua have zero semi-span.
* Theorem 3.6 lifts this to the whole continuum.

The inputs are:
* Davis's equivalence of zero span and zero semi-span (O–T Theorem 1.1);
* Effros's theorem (verified, `HPC.Effros.effros_homogeneous_set`);
* Hagopian 1976 (verified, `hagopian76_theorem1`);
* Cook 1967 Theorem 4 (maps onto hereditarily indecomposable continua are confluent).

**This batch, top down.**
1. Span: definitions and elementary lemmas (§2).
2. Cook's Theorem 4 (§3).
3. Davis's Theorem 1.1 in the case used: hereditarily indecomposable continua (§4).
4. Theorem 3.6 from Corollary 3.5 (§5).
5. Corollary 3.5 from Theorem 3.2 in a strip form, the named claim `OTThm32` (§6).
6. A planar lemma that the proof of Theorem 3.2 will need (§7).

The result is `theoremC_of_thm32 : OTThm32 → TheoremC`. Batches 192– prove `OTThm32` from O–T §2.
The repository's crossing parity for closed polygons (`parity`, `parity_locallyConstant`,
`parity_eq_of_isPreconnected`, `parity_far`, `HPC/Plane/Jct1.lean`) is O–T's Lemma 2.1 in
ray-crossing form; simplicity of the polygon is not needed there.

**Two departures from O–T, both my readings, for you to confirm or refute (ledger, §9).**
* **Davis.** O–T derive Theorem 1.1 from Lelek (span zero ⇒ atriodic tree-like) and
  Grispolakis–Tymchatyn (maps onto atriodic tree-like continua are weakly confluent), "by a
  Brouwer reduction type argument" (p. 130). Corollary 3.5 applies it only to a proper subcontinuum
  of a hereditarily indecomposable continuum. There Cook's theorem gives confluence, and the
  Brouwer reduction is ten lines (§4). Davis's paper is not needed.
* **Tree-likeness.** The proof of Theorem 3.6 opens "Since X is atriodic tree-like" (the source
  is p. 139: "It is known (see Jones [13] and Rogers [20]) that a homogeneous plane continuum is
  either indecomposable and tree-like or ..."). In the indecomposable case the proof uses neither
  property: the reduction it introduces needs only Corollary 3.5 and a Brouwer reduction (§5.2).
  So Rogers 1981 and Jones 1969 are not needed.

## 2. Span

**O–T, p. 129** (transcribed from the page image):
> Let (X,d) be a metric space. For i = 1,2 let πᵢ: X × X → X be the iᵗʰ coordinate projection.
> Following Lelek [15] and [16] we define the *surjective span* σ\*(X) [respectively, the
> *surjective semi-span* σ₀\*(X)] of X to be the least upper bound of the set of real numbers
> α ≥ 0 with the following property: there exists a connected set C_α ⊂ X × X such that
> d(x,y) ≥ α for (x,y) ∈ C_α and π₁(C_α) = X = π₂(C_α) [respectively, π₁(C_α) = X]. The *span*
> σ(X) [respectively, *semi-span* σ₀(x)] of X is defined by
> σ(X) = sup{σ\*(A) | A ⊂ X, A ≠ φ connected}
> [respectively, σ₀(X) = sup{σ₀\*(A) | A ⊂ X, A ≠ φ connected}].

("σ₀(x)" for σ₀(X) is a misprint.)

**Hoehn–Oversteegen, p. 184:**
> As in the introduction, a continuum X has *span zero* if whenever f, g: C → X are maps of a
> continuum C to X with f(C) ⊆ g(C), there is a point p ∈ C such that f(p) = g(p). This can
> equivalently be formulated as follows: X has span zero if every subcontinuum Z ⊆ X × X with
> π₁(Z) ⊆ π₂(Z) meets the diagonal ΔX = {(x, x) : x ∈ X} ...

Only positivity matters in what follows, so the skeleton uses topological forms (`SurjSpanPos`,
`SurjSemiSpanPos`, `SpanZero`, `SemiSpanZero`, `HOSpanZero`). For a compact `A`, a continuum
`Z ⊆ A × A` missing the diagonal has `d ≥ α > 0` on it, with `α` the minimum of `d` on `Z`.
`OTSpanPos` and `OTSemiSpanPos` are O–T's definitions read literally.

**2.1** `otSemiSpanPos_iff`, `otSpanPos_iff` (compact `X`).
* (⇒) Given `A`, `C` and `α`, take `A' = cl A`, `C' = cl C`. They are compact and connected, and
  `C' ⊆ A' × A'`. The bound `d ≥ α` passes to `C'`, so `C'` misses the diagonal. Finally
  `π₁(C') = cl π₁(C) = A'`: `π₁(C')` is compact, contains `π₁(C)` and lies in its closure.
* (⇐) Take `α` the minimum of `d` on `Z`.

**2.2** `SurjSpanPos.surjSemiSpanPos`, and `SurjSpanPos.image`, `SurjSemiSpanPos.image`. For the
images, use `Z ↦ (f × f)(Z)`: injectivity on `A` keeps it off the diagonal.

**2.3** `semiSpanZero_iff_hoSpanZero` (compact `X`). Use the swap `(a, b) ↦ (b, a)`.
* (⇒) Let `Z` be a continuum, off the diagonal, with `π₁(Z) ⊆ π₂(Z)`. Its swap `Z'` has
  `π₂(Z') ⊆ π₁(Z') = π₂(Z) =: A`. Then `Z' ⊆ A × A` and `π₁(Z') = A`, so `A` has positive
  semi-span.
* (⇐) The swap of a witness for `SurjSemiSpanPos A` is a continuum off the diagonal with
  `π₁ ⊆ π₂`.

**2.4** `hoSpanZero_iff_maps`. Pass between `Z` and `C := Z` (with the two projections); in the
other direction take `Z = range (f, g)`.

## 3. Cook 1967, Theorem 4

**Cook, p. 242:** "If f is a mapping of a topological space X onto a topological space Y such
that, for every subcontinuum Q of Y each component of f⁻¹(Q) is mapped by f onto Q, then f is said
to be *confluent*."

**Cook, p. 243** (transcribed from the page image):
> THEOREM 4. *If f is a mapping of the compact metric continuum X onto the hereditarily
> indecomposable continuum Y, then f is confluent.*
>
> Proof. Suppose that Q is a subcontinuum of Y and C is a component of f⁻¹(Q). Let C₁, C₂,
> C₃, ... be a sequence of subcontinua of X such that (1) for each n, Cₙ₊₁ is a subcontinuum of
> Cₙ; (2) for each n, C is a proper subcontinuum of Cₙ; and (3) C is the common part of continua
> of that sequence. Then, for each n, f(Cₙ) contains a point not in Q and intersects Q; hence,
> f(Cₙ) contains Q. The common part of f(C₁), f(C₂), ... is f(C) and contains Q, but Q contains
> f(C). Then f(C) = Q.

**Proof to formalize** (`cook67_theorem4`; `C = connectedComponentIn (f ⁻¹' Q) x`).
1. If `C = X`, then `f(C) = S ⊇ Q`.
2. Otherwise let `Nₙ` be the closed `1/n`-neighbourhood of `C` and `Cₙ` the component of `x` in
   `Nₙ`.
   * By boundary bumping, `Cₙ ⊋ C`: either `Nₙ = X` and `Cₙ = X`, or `Cₙ` meets the frontier of
     `Nₙ`, which is at distance `1/n` from `C`.
   * The `Cₙ` decrease, and `⋂ Cₙ = C`: the intersection is a continuum containing `C` and
     contained in `⋂ Nₙ = C`.
   * The existence of such a sequence is unstated in Cook (and needs `C ≠ X`).
3. `f(Cₙ)` meets `Q` (at `f(x)`). It is not inside `Q`: otherwise `Cₙ ⊆ f⁻¹(Q)` would be a
   connected set containing `x` and larger than `C`.
4. Two subcontinua of the hereditarily indecomposable `S` that meet are nested; so `Q ⊆ f(Cₙ)`.
5. `⋂ f(Cₙ) = f(⋂ Cₙ) = f(C)` for a decreasing sequence of compact sets (unstated in Cook). So
   `Q ⊆ f(C) ⊆ Q`.

## 4. Brouwer reduction; Davis's Theorem 1.1 for hereditarily indecomposable continua

**O–T, p. 130:**
> Since every map of any continuum C onto an atriodic tree-like continuum is weakly-confluent (see
> [21]), the following theorem follows easily by a Brouwer reduction type argument.
>
> THEOREM 1.1. (Davis [5]). *Let X be a continuum with σ(X) = 0, then σ₀(X) = 0.*

**4.1** `isContinuum_sInter_chain` (a helper; §4.2, §5.2 and §6.4 use it too): the intersection
of a nonempty chain of continua is a continuum, and for a continuous map `φ` into a Hausdorff
space, `φ(⋂ c) = ⋂_{W ∈ c} φ(W)`. Compact, nonempty by the finite intersection property,
connected as a directed intersection of continua in a Hausdorff space. The repository has only
special forms (`iInter_chain_isContinuum`, for `IsExtensionAway`; `isContinuum_iInter_antitone`,
for sequences).

`brouwer_reduction`: Zorn's lemma, with the intersection of a nonempty chain of subcontinua of
`Z` as lower bound (the empty chain has `Z`).

**4.2** `exists_surjSpanPos_of_surjSemiSpanPos`. Let `A` be hereditarily indecomposable and
`Z ⊆ A × A` a continuum off the diagonal with `π₁(Z) = A`.
1. Let `P(W)` be "`π₂(W) ⊆ π₁(W)`". It holds for `Z`, since `π₂(Z) ⊆ A = π₁(Z)`.
2. `P` passes to intersections of chains: for a chain of compact sets,
   `πᵢ(⋂ Wⱼ) = ⋂ πᵢ(Wⱼ)`.
3. By 4.1 there is a minimal subcontinuum `Z₀ ⊆ Z` with `P(Z₀)`. Put `B = π₁(Z₀)`, a subcontinuum
   of `A`, hence hereditarily indecomposable.
4. Suppose `Q := π₂(Z₀) ≠ B`. `Q` is a continuum and `Q ⊆ B`. Apply Cook (§3) to `π₁` on `Z₀`,
   whose range is `B`. Take `w ∈ Z₀` with `π₁(w) ∈ Q`, and let `Z'` be the component of `w` in
   `Z₀ ∩ π₁⁻¹(Q)`.
   * By Cook, `π₁(Z') = Q`.
   * `π₂(Z') ⊆ π₂(Z₀) = Q = π₁(Z')`, so `P(Z')`.
   * `Z' ≠ Z₀`, since `π₁(Z') = Q ≠ B`.

   This contradicts the minimality of `Z₀`.
5. So `π₁(Z₀) = π₂(Z₀) = B`, `Z₀ ⊆ B × B`, and `Z₀ ⊆ Z` misses the diagonal: `SurjSpanPos B`.

`semiSpanZero_of_spanZero` follows.

## 5. Theorem 3.6 (indecomposable case) from Corollary 3.5

**O–T, p. 140** (transcribed from the page image):
[Quotation moved to doc/sources/transcriptions/ot82.md, §doc/batches/COMMISSION-batch191.md, 5. Theorem 3.6 (O–T, p. 140); batch 204.]

Slips, harmless: "f(X) ⊃ g(X)" for `f(C) ⊃ g(C)`; "homomorphism"; "[7]" is Hagopian 1975 in the
list of references, Effros is [6]. The decomposable half of the theorem is not needed for the
classification (its elements are handled by the indecomposable half) and is not commissioned.

**Proof to formalize** (`ot82_theorem36_of_cor35`). Let `M` be an indecomposable homogeneous
plane continuum; `M` is hereditarily indecomposable (`hagopian76_theorem1`). Proper subcontinua
have zero semi-span by `h35`. Suppose `Z ⊆ M × M` is a continuum off the diagonal with
`π₁(Z) = M`. (A one-point `M` has no such `Z`.) Write `f = π₁`, `g = π₂` on `Z`.

**5.1** Let `3ε` be the minimum of `d(f, g)` on `Z`; `ε > 0`.

**5.2 (the reduction).** We may assume: `f(Z) = M`, and either `g(Z) ≠ M` or no proper
subcontinuum of `Z` is mapped onto `M` by `g`.
* If `g(Z) ≠ M`, there is nothing to do.
* Otherwise take, by 4.1, a minimal subcontinuum `Z₀ ⊆ Z` with `g(Z₀) = M`. "`g(W) = M`" passes
  to intersections of chains, as in §4.
  * If `f(Z₀) = M`, replace `Z` by `Z₀`.
  * If `f(Z₀) ≠ M`, replace `Z` by the swap of `Z₀`. Now the first projection is onto `M` and the
    second is not.

Only Corollary 3.5 (through `h35`, already used to get `f(Z) = M`) and 4.1 enter here. Neither
atriodicity nor tree-likeness is used.

**5.3 (Effros).** `δ > 0` such that any point is carried to any point at distance `< δ` by a
homeomorphism of `M` moving every point by `< ε` (`effros_homogeneous_set`).

**5.4 (the sequence `Kᵢ`).** `M` is nondegenerate and indecomposable. Write `Jones.composant`:
inside `namespace HPC.Span` a bare `composant` resolves to `HPC.composant` (two arguments,
`HPC/PseudoArc/Statements79.lean`), as in the existing `HPC.Hagopian` files.
* Take a point `x₁` and a point `q` outside its composant (composants are disjoint and
  uncountably many, `composant_eq_or_disjoint`, `uncountable_composants`).
* For `i ≥ i₀`, where `1/i₀ ≤ d(x₁, q)`, let `Kᵢ` be the component of `x₁` in `M ∖ B(q, 1/i)`.
  (For smaller `i` the set does not contain `x₁`, and Mathlib's component is empty.) The `Kᵢ`
  are proper (they miss `q`), increasing subcontinua.
* Every proper subcontinuum through `x₁` misses `q`, so it lies in some `Kᵢ`. Hence `⋃ Kᵢ`
  contains the composant of `x₁`, which is dense (`composant_dense`).
* By compactness some `Kᵢ` is `δ`-dense, with `δ` from 5.3. Fix that `i`.

**5.5 (Cook).** By §3 applied to `f` (onto the hereditarily indecomposable `M`), a component `Cᵢ`
of `f⁻¹(Kᵢ)` has `f(Cᵢ) = Kᵢ`. `Cᵢ ≠ Z`, since `Kᵢ ≠ M`.

**5.6.** Take `y ∈ g(Cᵢ)` and, by `δ`-density, `x ∈ Kᵢ` with `d(x, y) < δ`. Let `h` be the Effros
homeomorphism with `h(x) = y`.

**5.7.** `h(Kᵢ)` and `g(Cᵢ)` are subcontinua meeting at `y`, so they are nested. Let `Z*` be the
larger one. It is proper (O–T: "since Z is a proper subcontinuum", unargued):
* `h(Kᵢ) ≠ M`, because `Kᵢ ≠ M`;
* `g(Cᵢ) ≠ M`: either `g(Z) ≠ M`, or `g` is irreducible and `Cᵢ ⊊ Z`.

**5.8.** Let `W = {(h(f(c)), g(c)) : c ∈ Cᵢ}`, a continuum. On `W`,
`d ≥ d(f(c), g(c)) − d(f(c), h(f(c))) > 3ε − ε > 0`. The projections of `W` are `h(Kᵢ)` and
`g(Cᵢ)`.
* If `g(Cᵢ) ⊆ h(Kᵢ) = Z*`, then `W ⊆ Z* × Z*` with `π₁(W) = Z*`.
* Otherwise the swap of `W` lies in `Z* × Z*`, with first projection `g(Cᵢ) = Z*`.

Either way `SurjSemiSpanPos Z*`, against `h35`.

**5.9** `theoremC_of_cor35`: Theorem 3.6 and §2.3.

## 6. Corollary 3.5 from Theorem 3.2

**O–T, pp. 139–140** (transcribed from the page images):
[Quotation moved to doc/sources/transcriptions/ot82.md, §doc/batches/COMMISSION-batch191.md, 6. Corollary 3.5 and Theorem 3.2 (O–T, pp. 137, 139–140); batch 204.]

**My reading of the printed proof of Corollary 3.5** (candidate ledger entries, §9):
1. "Without loss of generality ... π₁(A) = [0,1/2] and π₁(X) = [0,1]": unargued, and not a
   matter of scaling. A copy of `A` through the leftmost point may reach as far right as `X`. §6.1
   arranges it by re-embedding `X`.
2. "For each K ∈ 𝒦 we may suppose K ∩ {ε} × R = {x_K}": unargued. Minimality does not give it in
   general: a continuum minimal for meeting both sides of a strip can meet a side in an arc (the
   sin(1/x) continuum with its limit bar on the side; not a hereditarily indecomposable example).
   It is not needed: any `x_K ∈ K ∩ {ε} × R` serves for Effros.
3. The existence of `𝒦`: unargued, true (§6.2).
4. "[0,5/8] ⊂ π₁(h_K(B)) ⊂ [0,3/4)": impossible as printed, since `h_K(B) ⊂ K ⊂ [ε, 3/4] × R`.
   Two readings: `[ε, 5/8] ⊂ π₁(h_K(B))` for each `K`, or `[0, 5/8] ⊂ π₁(B)`. Only the second
   gives what Theorem 3.2 needs, one `y ∈ B` for all `K` (a `y` with `π₁(y) = 5/8`). Either way
   "It is easy to see that there is a continuum B" is unargued; §6.4 step 8 gives `B` and the one
   `y` (hereditary indecomposability makes the `h_K⁻¹(K)` nested).
5. "an indecomposable homogeneous plane": "continuum" is missing. "[7]" for Effros, as in 3.6.

**My reading of Theorem 3.2.** Its proof (pp. 137–138) begins:
> PROOF. We may suppose that for each λ ∈ Λ h_λ(Y) meets {0} × R in a single point and h_λ(Y)
> intersects {1} × R in at most one point. Hence, since h_λ(X) ∩ {0} × R ≠ φ and
> h_λ(Y) ⊂ [0,1] × R, we may suppose that for each λ ∈ Λ neither h_λ(X) nor h_λ(Y) separates the
> plane. Let δ ∈ Λ. We may suppose that π₁(h_δ(y)) > π₁(h_δ(z)) + 1/2 for each z ∈ X. We may also
> suppose that d(h_λ(z), h_γ(z)) < 1/8 for each z ∈ Y and λ, γ ∈ Λ. The proof now proceeds as in
> Theorem 3.1 except that we use Theorem 2.7 instead of Theorem 2.6.

The proof of 3.1 needs three images one of which separates the other two in the strip ("Let
λ₁, λ₂, λ₃ ∈ Λ such that h_λ₂(X) separates h_λ₁(X) from h_λ₃(X)"), and the single-point
supposition. Neither is argued; the single-point supposition can be avoided but not justified
(disjoint crossing arcs can each meet a side in two points). The two "we may suppose" steps about
`δ` are not available together: the cluster of maps within `1/8` of each other need not contain
`δ`, and one rescaling does not fix the gaps of the others. (The non-separation supposition is
correct: disjoint continua meeting `x = 0` have pairwise disjoint bounded complementary domains,
so only countably many separate.) In
Corollary 3.5 the images lie in disjoint continua `K` crossing the strip, and §7 orders those. So
the named claim `OTThm32` is Theorem 3.2 with that extra hypothesis. It is weaker than the printed
statement and is what Corollary 3.5 uses. Whether the printed Theorem 3.2 holds in general is not
decided here.

### 6.1 Re-embedding lemmas

* **(E1)** `exists_homeomorph_unique_leftmost`. Let `x₀ = (u₀, v₀)` be a point of `K` with least
  first coordinate. Take `Φ(u, v) = (u − u₀ + (v − v₀)², v)`, a homeomorphism of the plane with
  inverse `(u, v) ↦ (u + u₀ − (v − v₀)², v)`. For `z ∈ K`, `(Φ z).1 ≥ 0`, with equality only at
  `x₀`. (The metric on `Pt` is the sup metric; it plays no role here.)
* **(E2)** `exists_homeomorph_push` (the finger move).
  * *Ball step.* If the open ball `B(c, r) ⊆ U` and `‖z − c‖ < r/2`, take
    `T(w) = w + β(w)(z − c)` with `β(w) = max(0, 1 − ‖w − c‖/r)`.
    * `w ↦ β(w)(z − c)` is Lipschitz with constant `‖z − c‖/r < 1/2`. So `T` is injective, and
      surjective by the contraction principle (`T w = v` iff `w = v − β(w)(z − c)`). It is
      continuous with continuous inverse.
    * `T(c) = z`, and `T` is the identity off `B(c, r)`.
  * *Chaining.* The set of `q ∈ U` reachable from `p` by such homeomorphisms (fixing the
    complement of `U`) is open, and it is closed in `U` by the ball step. `U` is connected, so
    every `q ∈ U` is reachable.
  * A homeomorphism fixing every point off `U` maps `U` onto `U`.
* **(E3)** `isConnected_rightHalf_diff`. Let `H₀ = {x > 0}`. Let `R'` bound `|v|` on `A`, `u₁` be
  the largest first coordinate on `A`, and `J = {0} × [−R', R']`.
  * Put `F = H₀ ∩ ({v > R'} ∪ {u > u₁} ∪ {v < −R'})`. It is a union of three convex sets, the
    middle meeting the other two, so it is connected; and `F ⊆ H₀ ∖ A`.
  * Every component `C` of the open set `H₀ ∖ A` meets `F`. Otherwise `C` is bounded and its
    frontier lies in `A ∪ J`. Then `C` is open and closed in `(A ∪ J)ᶜ`, so `A ∪ J` separates a
    point of `C` from a far point.
  * But `A ∩ J ⊆ {x₀}` is connected or empty. `A` does not separate the plane, and neither does
    the segment `J`. Janiszewski (`HPC.Moore.janiszewski_compact`) says `A ∪ J` separates no two
    points. Contradiction.
  * So `H₀ ∖ A` is a union of connected sets each meeting the connected `F ⊆ H₀ ∖ A`.

### 6.2 Crossing continua

* `exists_crossing_subcontinuum` (the cut-wire argument). Let `S = [a, b] × ℝ`.
  * Suppose no component of `P ∩ S` meets both lines `x = a` and `x = b`. Then, in the compact
    space `P ∩ S`, a clopen set `F₁` contains `E₁ = P ∩ {x = a}` and misses `E₂ = P ∩ {x = b}`.
    (Components equal quasi-components in compact Hausdorff spaces. For each `e ∈ E₁`, cover
    `E₂` by finitely many complements of clopen sets containing `e`; then cover `E₁` by finitely
    many of the resulting clopen sets.)
  * Put `F₂ = (P ∩ S) ∖ F₁`. The sets `(P ∩ {x ≤ a}) ∪ F₁` and `(P ∩ {x ≥ b}) ∪ F₂` are closed,
    disjoint, nonempty (by `hl`, `hr`), and cover `P`. This contradicts the connectedness of `P`.
  * So some component of `P ∩ S` meets both lines; it is a continuum.
* `exists_uncountable_crossing`. For each composant `κ` of `M`:
  * `κ` is dense, so it contains a point `p` with `p.1 < a`; and `κ = composant(p)` contains a
    point `q` with `q.1 > b`;
  * some proper subcontinuum `P` contains `p` and `q`, and `P ⊆ κ`;
  * the cut-wire lemma gives `K_κ ⊆ P ∩ S`.

  Composants are `Jones.composant` (see 5.4).

  Distinct composants are disjoint and there are uncountably many, so `κ ↦ K_κ` is injective and
  its image is the required family.

### 6.3 The named claim

`OTThm32` (skeleton) is Theorem 3.2 for the strip `[0, 1] × ℝ`, with:
* the extra hypothesis that each `h i` maps `Y` into `K i`, where the `K i` are pairwise disjoint
  continua crossing the strip;
* "`X ⊊ Y`, `y ∈ Y ∖ X`" dropped: `π₁ h(y) > π₁ h(z)` for `z ∈ X` already forces `y ∉ X`;
* the conclusion stated for any index type, uncountable or not.

### 6.4 Proof of `ot82_cor35_of_thm32`

Let `M` be an indecomposable homogeneous plane continuum, and `A₀ ≠ M` a subcontinuum with
`SurjSemiSpanPos A₀`.
1. `M` is hereditarily indecomposable (`hagopian76_theorem1`) and nondegenerate.
2. **(Davis, §4.2.)** Some subcontinuum `A₁ ⊆ A₀` has `SurjSpanPos A₁`. `A₁ ≠ M`.
3. **(E1).** Re-embed: `M' = Φ(M)` has a unique point `x₀'` on the line `x = 0` and lies in
   `x ≥ 0`.
   * `M'` is a plane continuum homeomorphic to `M` (via `Φ`), so it is homogeneous,
     indecomposable and hereditarily indecomposable.
   * Positivity of span is carried by `Φ` (§2.2).
4. **(Homogeneity.)** Move `Φ(A₁)` by a homeomorphism of `M'` to a subcontinuum `A ∋ x₀'`. Then
   `A ≠ M'` and `SurjSpanPos A`.
5. **(E2, E3.)** Set up the finger move.
   * `A` does not separate the plane (`no_proper_subcontinuum_separates`, applied to `M'`). It
     meets `x = 0` only at `x₀'`.
   * By (E3), `U = {x > 0} ∖ A` is open and connected.
   * Take `p ∈ M' ∖ A`; `p ∈ U`. Take `q` with `q.1` greater than every first coordinate on
     `A`; `q ∈ U`.
   * (E2) gives `T` with `T p = q`, fixing every point off `U`.

   Let `M'' = T(M')`.
   * `M'' ⊆ {x ≥ 0}`, and `x₀'` is its unique point on `x = 0`.
   * `A ⊆ M''`, since `T` fixes `A` pointwise.
   * `q ∈ M''` lies to the right of `A`.
   * `M''` is homeomorphic to `M` and `A` is a proper subcontinuum of it with `SurjSpanPos A`.
6. **(Constants.)** Let `s` and `m` be the largest first coordinates on `A` and on `M''`
   (`s < m`). Put `η = (m − s)/8` and `r = s + 4η < m`.
   * Effros for `M''` and `η` gives `δ`.
   * Choose `ε ∈ (0, r)` with `M'' ∩ {x ≤ ε} ⊆ B(x₀', δ)`. This exists by compactness and the
     uniqueness of `x₀'`; O–T need only the line `x = ε`.
7. **(The family.)** `exists_uncountable_crossing` for the strip `[ε, r] × ℝ` gives `𝒦`. The point
   `x₀'` is left of `ε`, and a point of `M''` with first coordinate `m` is right of `r`.
8. **(Effros, hereditary indecomposability, `B`.)** For `K ∈ 𝒦`, pick `x_K ∈ K` with
   `x_K.1 = ε`. Then `d(x₀', x_K) < δ`; let `h_K` be the Effros homeomorphism of `M''` with
   `h_K(x₀') = x_K`.
   * `h_K(A) ⊆ K`. `h_K(A)` and `K` meet at `x_K`, so they are nested. `K ⊆ h_K(A)` is
     impossible: `K` has a point on `x = r`, while `h_K(A) ⊆ {x ≤ s + η}` and `s + η < r`.
   * The continua `B_K = h_K⁻¹(K)` all contain `A`, so they are pairwise nested. Hence
     `B = ⋂_K B_K` is a continuum containing `A`.
   * Each `B_K ∩ {x ≥ r − η}` is nonempty: it contains the preimage of a point of `K` on
     `x = r`. These sets form a chain of nonempty compacta, so their intersection contains some
     `y ∈ B` with `y.1 ≥ r − η`.
   * For `z ∈ A` and `K ∈ 𝒦`:
     `(h_K z).1 < s + η < r − 2η < (h_K y).1`.
9. **(Theorem 3.2.)** Rescale with `ρ(u, v) = ((u − ε)/(r − ε), v)`. Apply `h32` with:
   * `Y := B`, `X := A`, `x := x₀'`, `y`;
   * `ι := 𝒦`, `K ι := ρ(K)`, `h ι := ρ ∘ h_K` on `B`.

   The hypotheses hold by steps 7–8. Every `h ι '' A = ρ(h_K(A))` has positive surjective span,
   by §2.2 (`ρ ∘ h_K` is continuous and injective). So `𝒦` would be countable, which it is not.

**Types.** `A₁`, `A`, `B` live in different subtypes (`M`, `M'`, `M''`, `B`). §2.2 suffices if `Φ`
and `T` are restricted to homeomorphisms of the subtypes and the final map is
`ρ ∘ Subtype.val ∘ h_K`; a helper relating `SurjSpanPos` of `A : Set M''` and of
`Subtype.val '' A` may be convenient. Applying `h32` to `↥B` and `h35` needs `haveI` for
`CompactSpace` and `ConnectedSpace`.

## 7. For Theorem 3.2: disjoint crossing continua are ordered

`crossing_traces_separated`. Let `S = [a, b] × ℝ`, `L_a = {a} × ℝ`, `L_b = {b} × ℝ`.

**Two lemmas from the Jordan curve theorem** (`jordan_curve_theorem`; compare
`rect_domain_crosscut`). Let `β ⊆ S` be an arc meeting `L_a ∪ L_b` only at its ends.
* *(crosscut)* If `β` runs from `u ∈ L_a` to a point of `L_b`, the points of `L_a` above `u` and
  those below `u` lie in different components of `S ∖ β`.
* *(pocket)* If `β` runs from `u ∈ L_a` to `u' ∈ L_a`, the points of `L_a` strictly between `u`
  and `u'` and those outside `[u, u']` lie in different components of `S ∖ β`.

**Proof.**
1. If neither alternative holds, the traces on `L_a` interleave. After exchanging `K` and `K'` if
   needed, there are `p, q ∈ K ∩ L_a` and `w ∈ K' ∩ L_a` with `p.2 < w.2 < q.2`. (Take `p` and `q`
   the lowest and highest points of `K ∩ L_a`, and `w` the lowest point of `K' ∩ L_a`, when the
   lowest point of `K ∩ L_a` is below that of `K' ∩ L_a`.)
2. `K'` lies in one component `W` of `S ∖ K`, and `W` meets `L_b`. `W` is relatively open in `S`.
   Take a polygonal arc `α ⊆ W` from `w` to `L_b`, stopped at its first point on `L_b`.
3. Let `s*` be the last time `α` is on `L_a` at a height in `[p.2, q.2]`. These heights avoid
   `p.2` and `q.2`, since `p, q ∈ K`, so this set of times is closed.
4. If `α` does not return to `L_a` after `s*`, the rest of `α` is a crosscut from a point between
   `p` and `q`. It separates `p` from `q`.
5. Otherwise, let `s**` be the first return after `s*`; its height is outside `[p.2, q.2]`. Then
   `α[s*, s**]` is a pocket arc, and it separates `p` from `q`.
6. In both cases `K` is connected, contains `p` and `q`, and misses `α`. Contradiction.

## 8. Order

§2, §3, §4, §5; then §6.1–§6.2 and §6.4; §7 last. §7 is not used in this batch; if time runs out,
leave it for batch 192.

## 9. Places to check (ledger)

Put these in the new section "Oversteegen–Tymchatyn 1982 and Cook 1967" of `LEDGER.md`, with the
printed sentences quoted from the page images. Confirm or refute each of my readings.
1. Theorem 3.6: "Since X is atriodic tree-like" is not used in the indecomposable case (§5.2).
2. Theorem 3.6: "Z is a proper subcontinuum" is unargued; it rests on the reduction to "g
   irreducible or into" (§5.7). "Hence there exists an index i and points ..." is unargued (§5.4).
3. Corollary 3.5: items 1–5 of §6.
4. Theorem 3.2: quote the suppositions of its proof (§6). The separating triple and the
   single-point supposition are unargued; the two "we may suppose" steps about `δ` are not
   available together (fix: choose one `n` such that uncountably many indices have span witness
   `≥ 1/n` and gap `π₁h(y) − max π₁h(X) > 1/n`, then cluster the maps within `1/(8n)`). Record
   that `OTThm32` adds the crossing continua.
5. Theorem 1.1: proved here only for hereditarily indecomposable continua, through Cook (§4).
6. Cook, Theorem 4: the existence of the sequence `Cₙ` (and the case `C = X`), and
   `⋂ f(Cₙ) = f(C)`, are unstated (§3).
7. Misprints: "σ₀(x)" (p. 129), "f(X) ⊃ g(X)" and "homomorphism" (p. 140), "[7]" for Effros
   (pp. 139, 140).

Notes: `doc/notes/ot82.md` with the transcriptions of pp. 129–130 and 136–140 from the images, and
a short account of O–T §2 (Lemmas 2.1–2.4, Remark 2.5, Theorems 2.6–2.7) for batch 192.

## 10. Deliverables

1. **The items of §2–§7.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch191.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** the new section (§9) and the two changes of §0.
3. **Notes:** `doc/notes/ot82.md`.
4. **Publish the changes, as in batch 190.** At the end of the run:
   * create `doc/batches/batch191-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch191-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes, in particular for `OTCor35` and `OTThm32` (an instance of the
     hypotheses of `OTThm32`, for example horizontal segments `K i` with `Y` an arc);
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `TheoremC`, with every open input marked (`OTThm32` should be the only
     one);
   * a short account of what batch 192 needs from O–T §2 to prove `OTThm32`, with any doubt about
     the claim itself.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   * Nothing is left at the root.
