# Commission: batch 182 — Part E, Hagopian 1976 XXVII: Theorem 1 — the last step; honest claims; saturation; E2.1 and E2.4

**Go!** This batch runs on top of the batch-181 work. Two files come with it, as separate uploads:

* `COMMISSION-batch182.md`: this text, also pasted into the prompt.
* `Hagopian76AA.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76AA.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76AA` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule from now on).** For every theorem whose hypotheses include a named
  `Prop` or a structure standing for open work, the report gives a note with two checks.
  1. *Not refuted by a short argument from the set-up.* Batch 179's `K = {p}` and §1.1 below are
     the kind of failure meant.
  2. *Not equivalent to the conclusion it is used for*, unless the printed argument is itself a
     proof by contradiction. In that case, say so. §2.3 below is the kind of failure meant.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXVII (batch 182)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `H76CapLow.lean`, if §2.1 replaces `cross_strand_near_mirror`;
  * `doc/notes/hagopian76-cases.md`: add the last step (§1.2) and the orientation (§2.2).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 181

* **Delivery.** The tarball and the manifest worked again. Keep doing it (§8.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2115 lines (2051 + 64 added, none removed), with `sorryAx` in none.
  The 62 new declarations use only the standard three axioms.

**Accepted:**
* `hε₃O`, `hε₃S`, `f_mem_O_of_mem_K`, `above_closure_misses_bottom`, `cross_strand_near`;
* 3c through irreducible intervals, and dropping the end-layer clause of commission 178 §3c;
* E0 and E1 (`property4_strand`, `property4_step_unless_setup`, `property4_of_strand_sep`);
* `case1_ending`, `case2_ending`;
* `tip_triod_mirror_rel`, `chunk_edge_case_mirror`;
* your analysis of Case 2 (b) and (e), and of `x₂ᵢ₋₃`.

**Not accepted as a reduction: `hagopian76_theorem1_of_cases`** (§1–§2). The theorem is correct,
but its hypothesis fails for every set-up that has blocks. The fault is partly mine: commission 181
did not restate the non-vacuity rule. It is now a standing rule (above).

**Your §1.1 obstruction is answered by commission 178 §3b.1.** `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` is the
intersection of two continua in a hereditarily unicoherent `M`. So it is a continuum
(`hereditarilyUnicoherent_of_homogeneous_indecomposable`, `isContinuum_inter_of_HU`). It contains
`y`. See §3.

## 1. The last step and the case split

### 1.1 Certificate: the case split fails at `i = 2`

`BlockLayersMeetSides S x m` asks, at `i = 2`, that `d⁻¹(x₂)` meet a side segment. It does not:
1. `IsBlocks` gives `d⁻¹[[0, x₂]] = E`. It also gives `F ≠ E`: otherwise `d⁻¹((x₂, 1]) = ∅`,
   against `x₂ < x₄ ≤ 1` and the surjectivity of `d`.
2. `ext_layers` gives `s` with `d⁻¹[[0, s]] = E` and `d⁻¹(s) = k⁻¹(1)`. The surjectivity of `d`
   gives `x₂ = s`.
3. `k⁻¹(1)` lies over `γ(1) = F(1, 0)` (`hγπ`, `hF`). `F` is injective on the rectangle
   `[0, 1] × [−1, 1]` (`IsCollar`), so `F(1, 0) ∉ F[{3/22, 19/22} × [0, c₁]]`.

Prove `blockLayersMeetSides_false` (skeleton): `S.IsBlocks x m → ¬ BlockLayersMeetSides S x m`.

The text has the same gap. At `i = 2`, `J = [x₁, x₂] = [0, e]`, so `d⁻¹[J] = E`. It misses
`π⁻¹[D]`, so there are no `J`-strands, and neither printed case applies. Yet this is the step that
reaches "`[x₁, x₂]` does not have Property 4".

### 1.2 The last step, separately

At `i = 2` the step must show that `I = [x₃, x₄]` does not have Property 4. Read Case 1 with the
bottom edge in place of the `J`-strand:
* E0 gives an `I`-strand `S_I` with `y₂` and `f(y₂)` on opposite sides. "Between `d⁻¹[I]` and
  `d⁻¹[J]`" becomes "below `S_I`". Nothing in `π⁻¹[D]` lies below `E`.
* `C₁`, `L`, `y₁` and `N` are as in E2.1 (§4).
* The band: `P = d⁻¹[[x₁, x₄]] ∪ Q`. Here `Q` is the segment of the vertical over `15/22`, from the
  bottom edge up to the first point of `d⁻¹[I]`. Then `f(y₁)` is above `S_I` or below `E`, and the
  second is impossible in `π⁻¹[D]`.
* "Above `S_I`" is excluded by the cap lemma and E2.4 (`ρ(y₁, d⁻¹[I]) ≥ ε₃`).

Prove `last_step_ending`: a witness (good point `y`, `I`-strand `S_I`, `y` below `S_I`,
`ρ(y, Cl S_I) ≥ ε₃`, `f(y)` above `S_I`) gives `False`. State the witness's existence, given
Property 4 for `[x₃, x₄]`, as the named `Prop` `LastStepClaims`. This step is a proof by
contradiction, so the second non-vacuity check is met by saying so.

Check also where the gap continuum `d⁻¹[[x₂, x₃]]` closes the band. It starts at `k⁻¹(1)`, to the
right of `D`. Its other end `d⁻¹(x₃)` meets the left or the right side, or neither. That decides
whether the band closes on the right, as in Case 1, or must be closed otherwise, as in Case 2.

### 1.3 The case split for `i ≥ 3`

Restate the case split for `3 ≤ i ≤ m` only. Then decide it. Route to try:
* `x₂ᵢ₋₁` is the left end `u` of a member `[u, v]` of `I` inside the block. Let `C` be the crossing
  component whose irreducible interval is `[u, v]`. Then `d⁻¹(u)` meets `Cl C`.
* Claim: on `Cl C`, `d` attains its least value only over the side segments. Along a crossing
  component, the layers of `F` through points over the middle are translated layers, ordered by
  parameter (`lemma3_half`).
* The same for `x₂ᵢ₋₂`, the right end of a member of `J`.

If the claim fails, give the configuration. In that case consider the weaker split "`d⁻¹(u)` meets
`π⁻¹` of the left region `F[[0, 3/22] × [0, c₁]]` or of the right region `F[[19/22, 1] × [0, c₁]]`".
It covers `d⁻¹(x₂) = k⁻¹(1)` (right region) and `i = 2`. Check whether the band arguments survive
it.

## 2. Honest claims, and the reduction

### 2.1 The mirror cap needs no extra hypothesis

`cross_strand_near_mirror` asks that `a` be `ε₃`-far from the bottom edge. This is not needed. Let
`a ∈ Mid` lie above `W` and `b` below `W`. The segment `[a, b]` contains a point of `V.above W` and
one outside it. So it meets the frontier of `V.above W`, the region above, not the region below.
That frontier lies in `Cl W ∪ π⁻¹[I₂] ∪ π⁻¹(sides)` (`above_closure_misses_bottom`). The exclusions
use only `a ∈ Mid` and the length `< ε₃`. Prove `cross_strand_near_mirror'` (skeleton) without
`hbot`. With it, the four cases of the parenthesis on p. 348 are symmetric where the cap is used.

### 2.2 Orientation

Hagopian: "For convenience we suppose `d⁻¹[J]` is below `d⁻¹[I]` and `f(yᵢ)` is above `d⁻¹[I]`.
(Other cases are handled with similar arguments …)". Let the witnesses carry an orientation, for
example a `Bool` that exchanges `V.above` and `V.below`. Prove `case1_ending` and `case2_ending` for
both orientations with §2.1.

### 2.3 Claims without `¬ Property4 J`

`Case1Claims` and `Case2Claims` ask for a witness only when `J` lacks Property 4. A witness gives
Property 4 for `J` (`case1_ending`), so each `Prop` is equivalent to its own conclusion. It no
longer records the printed claims, and it hides any orientation in which a witness of the fixed
shape cannot exist. Restate:
* drop the antecedent `¬ Property4 J`;
* add the printed case hypothesis that E1 leaves: `yᵢ` between `S_J` and `S_I`, in the orientation
  of §2.2 (`property4_step_unless_setup`'s second alternative);
* keep the witness fields as they are, one per printed claim.

### 2.4 The reduction

Prove `hagopian76_property4_step_cond'` and `hagopian76_theorem1_of_cases'` from:
* `InnerComponentsCross`;
* `LastStepClaims` (for `i = 2`);
* the case split for `3 ≤ i ≤ m` (§1.3);
* the restated `Case1Claims` and `Case2Claims` for `3 ≤ i ≤ m`.

Give the two non-vacuity checks for each hypothesis.

## 3. Saturation: 2e

As commission 181 §1, with:
1. **§1.1, step 1.** `K⁻` is a continuum (§0). Boundary bumping in `K⁻`
   (`exists_mem_closure_component_notMem`) gives the component of `K⁻ ∩ O` through `y`, with closure
   meeting `Fr O`, whenever `K⁻ ⊄ O`.
2. **§1.1, step 3** (`closure_G_diff_E`, skeleton): the closure of `F − E` meets `E` only in
   `k⁻¹(1)`. `F − E = d⁻¹((e, 1])`, and `F` is closed with `d` continuous, so the closure lies in
   `d⁻¹([e, 1])`. Its intersection with `E = d⁻¹[[0, e]]` lies in `d⁻¹(e) = k⁻¹(1)` (`ext_layers`).
3. **§1.2–§1.3**: the points `zⱼ`, and (iii) at `zⱼ`.
4. **§1.4**:
   * step 2, when `F ∩ hⱼ[E]` lies in the tip layer (boundary bumping);
   * step 4, `τ₁ = 1`. Here `Λ₁(zⱼ) ⊇ hⱼ[k⁻¹((τ, 1))]`, so `d⁻¹(1)` contains an end piece of the
     translate. Try the absorption form of Lemma 6 (a continuum missing `X` and meeting an
     extension lies in `R(X, E)`), applied to `d⁻¹(1)`, and Lemma 4. Or describe the configuration.

## 4. E2.1 and E2.4 (shared by Case 1, Case 2 and the last step)

### 4.1 E2.1

Printed (p. 348): "Let `Cᵢ₋₁` be the first component of `M ∩ π⁻¹[D]` (whose closure intersects
`π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]`) that is met by extending `Cl Cᵢ` away from `X` in `M`. The
existence of `Cᵢ₋₁` follows from the indecomposability of `Cl R(X, Cl Cᵢ)` (Lemma 6 (proof)) and an
argument similar to the one for Property 3. Note that `Cl Cᵢ₋₁` is essential to `h[R(E)]`. Let `L`
be the shortest extension of `Cl Cᵢ` away from `X` that contains `Cᵢ₋₁`."
1. Some extension of `Cl Cᵢ` away from `X` meets a crossing component other than `Cᵢ`. Follow the
   printed pointer: Lemma 6 (proof), and the "follows" argument of Property 3.
2. A first one: intersect a chain of extensions (`ExtChainInter`, batch 170).
3. `L`, the shortest extension containing `Cᵢ₋₁`.
4. `L ∩ F = ∅`. `L` is a proper subcontinuum of `M` containing `Cl Cᵢ`, which is essential to
   `h[R(E)]`. Use `strand_misses_F_of_composant`, after checking that `L` passes through a point of
   `h[R(E)]` for the package's `h`.
5. `Cᵢ₋₁` is a crossing piece inside `M`, and `Cl Cᵢ₋₁` is essential to `h[R(E)]`.
6. `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁` (`Thm1Setup.K_meets_crossing`), giving `GoodPoint yᵢ₋₁`.

### 4.2 E2.4

"`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise, a subcontinuum of `L` would violate Property 2." Identify
`H ⊆ L` and its end sets, and check each hypothesis of `Property2At` in turn:
* `H` is essential to `h[R(E)]`;
* `H` has a minimal admissible decomposition;
* its end sets are within `ε₃`;
* some layer is farther than `ε₂` from the first end set.

Then show that the conclusion fails. If one hypothesis cannot be met, give the configuration.

## 5. Case 2, claim (e)

(e): when `yᵢ₋₁` is below `S_J`, is `f(yᵢ₋₁)` above `S_J`? You found nothing printed that decides
it. Two ideas to test before giving it up:
* In Case 2, extend `Cl Cᵢ` away from `Z` instead of `X`, where `Z` is the end set at the side that
  `d⁻¹(x₂ᵢ₋₁)` meets. Does this put the configuration into the form of Case 1?
* Apply Property 2 to `f[N]`, which is essential to `h₁[R(E)]`, rather than to `N`.

If neither works, state (e) as the named `Prop` it is, with the configuration.

## 6. Order

1. §1.1 and §2.1, which are short.
2. §1.2 and §2.2–§2.4, which make the reduction honest.
3. §3 and §4.
4. §1.3 and §5.

## 7. Places to check (candidate ledger entries)

1. **p. 348, "The proof now breaks down into two cases"**: fails at `i = 2` (§1.1); unargued for
   `i ≥ 3` (§1.3).
2. **p. 348, "(Other cases are handled with similar arguments …)"**: symmetric where the cap is
   used (§2.1).
3. **p. 348, "The existence of `Cᵢ₋₁` follows from …"** (§4.1).
4. **p. 348, "for otherwise, a subcontinuum of `L` would violate Property 2"** (§4.2).
5. **p. 349, Case 2 (e)** (§5).
6. **The end layer of `F`** (§3).

## 8. Deliverables

1. The items of §1–§5.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch182.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. `doc/notes/hagopian76-cases.md`: add the last step and the orientation.
4. **Publish the changes, as in batch 181.** At the end of the run:
   * create `doc/batches/batch182-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch182-MANIFEST.txt`;
   * publish both, as you published the report.
5. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
