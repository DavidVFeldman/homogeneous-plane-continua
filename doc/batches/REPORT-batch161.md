Commission read: `doc/batches/COMMISSION-batch161.md` (batch 161 — Part E, Hagopian 1976 VI: Theorem 1 set-up (ε₁, the chain, Properties 1 and 3, T9, T11); Lemma 7; Lemma 9).

# Report, batch 161

**Status.**
* **Proved:**
  * T4: `hagopian76_eps1` (shape adjusted, §1.1), and ledger check 2 as `hagopian76_eps1_chain`;
  * T5: `exists_Gset` (skeleton shape), `hagopian76_chain11` (new), `hagopian76_property1` (shape
    chosen).
* **Partly proved:**
  * T9: `hagopian76_T9`, the first sentence, for any `D` with the one property the proof uses;
  * Property 3: `hagopian76_property3_shift`, the step "By Lemmas 2 and 3";
  * Lemma 7: `hagopian76_lemma7_triod` (the triod) and `hagopian76_lemma7_of_F` (Lemma 7 in the
    skeleton's shape, assuming the continuum `F` exists for two points in one composant of
    `Cl R(E)`; the other case is proved).
* **Open** (commented out with `OPEN (batch 161, …)` notes, no `sorry`; obstructions in `OPEN.md`,
  batch-161 section): T11, Property 3, Lemma 7, Lemma 9.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76F` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76F.lean` | the skeleton: T4, T5 proved; T9, Property 3, Lemma 7 partly; T11, Property 3, Lemma 7, Lemma 9 commented out with `OPEN (batch 161)` notes |
| `H76Eps1.lean` | `piece` (moved from the skeleton, unchanged), `middle`, `IsEps1`, `exists_pos_forall_finset`, `piece_disjoint`, `ends_middle_disjoint`, `exists_isEps1`, `isEps1_thickening_disjoint` |
| `H76Lemma8Sep.lean` | `lemma8_caps_sep`: the batch-159 proof of Lemma 8 with caps, also returning Moore's open set `D` |
| `H76Prop1.lean` | `Wset` (moved from the skeleton, unchanged), `Gset`, `toPt_Wset_eq`, `elev`, `exists_elev`, `exists_elev_between`, `follows_of_elev`, `chainG`, `chainG_isPlaneChain`, `chainG_follows`, `thickChain`, `thickChain_follows`, `property1_aux` and helpers |
| `H76T9.lean` | `subset_Rset`, `T9_aux` |
| `H76Lemma7.lean` | `lemma7_triod`, `Lemma7F`, `mem_closure_of_near`, `lemma7_of_F`, `exists_F_of_not_mem_composant`, `lemma7_of_F_composant` |
| `H76Prop3.lean` | `layer_shift` |

Housekeeping: the commission and skeleton are in `doc/batches/COMMISSION-batch161.md` and
`doc/batches/skeletons/Hagopian76F.lean`. Three stray files at the root were dealt with:
* the root copy of `REPORT-batch160.md` was removed, since it is byte-identical to
  `doc/batches/REPORT-batch160.md`;
* the scheduling note `theorems-3-4-scheduling(8).md` was moved to `doc/notes/`;
* the skeleton was moved to `HPC/Hagopian/Hagopian76F.lean`.

Nothing is left at the root. No statement left commented out in `Hagopian76D.lean` or
`Hagopian76E.lean` was proved here (Lemmas 7 and 9 stay open), so those files are unchanged.

## 1. The items

### 1.1 T4, `ε₁`: proved

`hagopian76_eps1`. **Shape changes:**
* the conclusion also returns `IsEps1 k ε₁`, which records the families of the minimum that the
  later steps use:
  * `sep`: non-adjacent elevenths are `≥ 4ε₁` apart. This is the skeleton's family, not one of
    Hagopian's.
  * `ends`: `ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]]) ≥ 3ε₁`. This is Hagopian's third family.
* `hX` and `hi` are dropped because they are unused.
* The section instances are omitted.

The proof: the elevenths are compact, and non-adjacent ones have disjoint parameter intervals. A
positive bound over finitely many pairs is taken (`exists_pos_forall_finset`). The skeleton's
disjointness follows from `sep` by the triangle inequality (`isEps1_thickening_disjoint`).

Which family each step uses (ledger check 1):

| family | used by |
|---|---|
| `sep` (added) | the chain of ε₁-neighbourhoods (check 2); `{Gᵢ}` being a chain (T5) |
| `ends` (Hagopian's third) | Property 1 (the caps contain the end sets); T9 (`Cl B` misses `h[X ∪ Z]`) |
| `ρ(Aᵢ, Bᵢ)`, `ρ(E, π⁻¹(qᵢ))` | not used by any step proved here; meant for T11 and Property 3 |

**Check 2** ("the chain formed by taking `ε₁`-neighborhoods … follows `h[E]`") is proved as
`hagopian76_eps1_chain` for `ε₁` with `IsEps1`. It does **not** follow from Hagopian's four families.
`ρ(Aᵢ, Bᵢ)` only bounds distances from the verticals, and nothing separates `k⁻¹[[0, 1/11]]` from
`k⁻¹[[2/11, 3/11]]`. The repair is to shrink `ε₁`.

The general tool is `follows_of_elev`. A chain of eleven links follows a type A′ continuum `F` (with
an onto map `b`) as soon as the `(i + 1)`-st eleventh of `F` lies in the `i`-th link. Condition (3) of
"follows" comes from an interpolation over the elevenths (`exists_elev_between`).

### 1.2 T5, `Wₓ`, `Gₓ`, `{Gᵢ}`, `L`, Property 1: proved

* `Wset`: as in the skeleton, moved to `H76Prop1.lean`.
* `Gset M ε x`: the largest open set in the `ε`-ball about `x` whose trace on `M` lies in `Wₓ`. Its
  trace is exactly `Wₓ` (`toPt_Wset_eq`, Lemma 2). `exists_Gset` has the skeleton's shape, unchanged.
* `chainG k ε₁ i = ⋃{Gₓ : x ∈ k⁻¹[[i/11, (i+1)/11]]}`, 0-indexed. `hagopian76_chain11` (new):
  * it is a chain (`IsEps1.sep`);
  * its links lie in the `ε₁`-neighbourhoods of the elevenths;
  * it follows `h[E]` for every `ε₁`-homeomorphism `h`. The reason is that `h(x′) ∈ Gₓ′`, so
    `h[piece i] ⊆ Gᵢ`.

  The links are not collar rectangles, and no step proved here needs them to be (they are needed for
  Lemma 9 and T11; §1.6).
* `hagopian76_property1` (shape chosen). `L` is the Lemma-8 refinement with caps `U = G₁ − Cl G₂` and
  `V = G₁₁ − Cl G₁₀`. `IsEps1.ends` puts the end sets in `U` and `V`, and the caps lie in `G₁ − G₂` and
  `G₁₁ − G₁₀`, as in Hagopian's parenthesis. The statement returns:
  * the shape of `L`;
  * `L` is an ordered refinement of `{Gᵢ}`, follows `E`, and is free;
  * **Property 1**: for every `y ∈ M ∩ Lᵢ` (`2 ≤ i ≤ 10`) there is an `ε₁`-homeomorphism `h` with
    `y ∈ h[E]` and `L` following `h[E]`, where `h[E]` carries the transported map. The stronger
    conclusion `h[piece j] ⊆ Lⱼ` for all `j` is also returned.

  *Proof of Property 1:*
  1. Since `y ∈ Gₓ ∩ M = Wₓ`, there is an `h` with `h(x) = y`.
  2. `h[k⁻¹[[1/11, 10/11]]]` is connected. It lies in `G₂ ∪ … ∪ G₁₀`, so it misses the caps, and it
     meets Moore's set `C` at `y`.
  3. Moore's Theorem 44 gives `M − (A ∪ B) ⊆ C ∪ D` with `C ∩ D = ∅`. So this set lies in `C`, and
     every middle eleventh of `h[E]` lies in `C ∩ Gⱼ = Lⱼ`.

  This needs the set `D`, which `lemma8_caps_aux` (batch 159) does not return. `lemma8_caps_sep` is
  the same proof with the extra conclusion.

### 1.3 T9: first sentence proved for a `D` with property (D)

`hagopian76_T9` (shape chosen). It is stated for any open `O` (Hagopian's `π⁻¹[D]`) with
**(D)**: every point of `M ∩ Cl O` lies in one of `L₂, …, L₁₀`.

It applies to any connected `B ⊆ M ∩ O` meeting one of these links, and to any chain `L` with
Property 1 in the form of `hagopian76_property1`. The conclusions:
* `Cl B ⊆ h[E]`;
* `h⁻¹[Cl B]` is a subcontinuum of `E`;
* it is essential to `R(E)` whenever `Cl B` meets links `Lₐ`, `L_c` with `c ≥ a + 3`, since a layer
  of `h[E]` lies in one link.

The containment argument:
* by (D) and `IsEps1.ends`, `Cl B` misses `h[k⁻¹(0) ∪ k⁻¹(1)]`;
* by the 1975 ¶9 triod (`subset_of_meets_avoids`), `Cl B ⊆ h[E]`.

Hagopian's "Lemma 5" is not needed for this sentence.

**Open part:**
* (D) for `π⁻¹[D]`;
* that `Cl B` reaches far-apart links;
* "`L − {L₁, L₁₁}` follows `Cl B`".

All three need `D` (T8) in collar coordinates.

### 1.4 Property 3: one step proved; open

`hagopian76_property3_shift`, from `layer_shift`. For a type A′ continuum `F`, an interior layer
`d⁻¹(v)`, and `δ > 0`, there are `u ∈ (0, v)` and a `δ`-homeomorphism `g` with `g[d⁻¹(v)] = d⁻¹(u)`.
The proof:
* Lemma 5 (continuity of the decomposition) gives, through every neighbourhood of `z ∈ d⁻¹(v)`, an
  earlier layer. This is because the continuum `d⁻¹[[v/2, v]]` is not a single layer.
* Lemma 2 gives `g` moving `z` into that layer.
* Lemma 3 gives the equality, with `δ` below half of `ρ(d⁻¹[[v/2, v]], d⁻¹(0) ∪ d⁻¹(1))`.

The rest of Property 3 is open. Two things are missing:
* (i) the least `v`, for which no closedness argument is given;
* (ii) that `d⁻¹(u)` again contains a component of `F ∩ π⁻¹[D]` whose closure meets both verticals.

(ii) is a crossing property of `D` under small homeomorphisms. The families `ρ(Aᵢ, Bᵢ)` and
`ρ(E, π⁻¹(qᵢ))` are presumably meant for it.

The property the proof actually uses of `F`: it is an extension of `E` away from `k⁻¹(0)` with
`d⁻¹(0) = k⁻¹(0)`. Irreducibility with respect to (1)–(2) of T13 is not used in the printed proof of
Property 3.

### 1.5 T11: open

The cross-cut `K` separates `π⁻¹[D]`; this is the cross-cut theorem, since `π` is a homeomorphism off
`E` (`plane_split`). The sentence also needs `L₂ ∩ π⁻¹[D]` and `L₁₀ ∩ π⁻¹[D]` on opposite sides of
`K`. The printed `ε₁` keeps `G₂` and `G₁₀` off `A₃ ⊇ K` but does not decide the side, because the sets
`Gₓ` are not connected. A proposed shape is in the comment in `Hagopian76F.lean`; it needs `D`.

### 1.6 Lemma 9: open; configuration checked

Not formalized: the chain of collar rectangles `{G₁, G₂, G₃}` in the quotient, its lift, and
Theorem 28 for `π[G₂]`.

I checked the configuration of report 160 §1.E against the text (ledger check 8). With `U = k⁻¹(1/3)`
and `Y = k⁻¹(1/2)`, the points `b₂` (abscissa `1/3`) and `a₂` (abscissa `1/2`) on the bottom side,
`a₁` on the left side and `b₁` on the right side are interlaced `a₁, b₂, a₂, b₁`, as proposed. Two
corrections:
1. The continuum through `b₁` and `b₂` must be `πh[D]` together with the segment of `A` from
   `πh(u)` down to the bottom side. `πh[D]` alone does not reach `b₂`. The segment misses `π[C ∪ I]`,
   because it lies below the axis at a different abscissa from `π[I]`.
2. **Freeness and the left side** (commission §2): `h[D]` is connected and starts in `L₂`. By
   freeness it can leave `St L` only through `Cl (L₁ ∪ L₃)`. It misses `Cl G₁ ⊇ Cl L₁`, so it reaches
   `Cl L₃` and stays off the left side. The exit point `b₁ ∈ Cl π[L₃]` lies on the right side of
   `π[G₂]` only if the links are collar rectangles. So the rectangles are needed for the freeness
   step as well.

### 1.7 Lemma 7: triod proved; reduced to one composant

**The triod** (`lemma7_triod`, `hagopian76_lemma7_triod`). Let `H` be of type A′, `uⱼ ∈ H` outside
the end layers, `tⱼ ∈ T`, `vⱼ ∈ V`, and `F′` a continuum through `uⱼ` missing `tⱼ` and `vⱼ`. Then
`F′ ⊆ H`. The proof takes three continua through `uⱼ`: `d⁻¹[[0, c]]`, `d⁻¹[[c, 1]]` (with
`c = d(uⱼ)`), and `F′`. One of them lies in the union of the other two (`three_continua`); `tⱼ` and
`vⱼ` exclude the first two, and the third gives `F′ ⊆ H`.

Your reading of §1 is confirmed. The case "`g[F] ∩ Hⱼ` reaches an end layer without containing `tⱼ`
or `vⱼ`" needs no separate treatment, because the arms are taken at the layer of `uⱼ`, not from
`g[F] ∩ Hⱼ`. `uⱼ` is outside both end layers: `ρ(Tⱼ, Uⱼ) > ε` excludes `T`, and for large `j`,
`ρ(Tⱼ, Vⱼ) < ε` excludes `V`.

**The reduction** (`lemma7_of_F`, `lemma7_of_F_composant`, `hagopian76_lemma7_of_F`). This is
Hagopian's argument, formalized: sequences, a convergent subsequence in `M³`, limits `t`, `u`, `p`
in `Cl R(E)`, `ε′ = min(ε/4, ρ(t, F)/2)`, Lemma 2 at `u`, and the choice of `j`. Lemma 7 follows in
the skeleton's shape once, for `p`, `u ≠ t` in `Cl R(E)` and `r > 0`, some continuum contains `u`,
misses `t`, and meets the `r`-ball about `p` (`Lemma7F`). Neither the essentiality of `F` nor its
position in a translate of `R(E)` is used.
* **Different composants** of `Cl R(E)`: `F` exists (`exists_F_of_not_mem_composant`). Boundary
  bumping in `Cl R(E) − B(p, r/2)` gives a proper subcontinuum through `u` that meets `B(p, r)`;
  it misses `t`.
* **One composant: open.** By the triod lemma, a continuum through `uⱼ` not inside `Hⱼ` contains
  all of `Tⱼ` or all of `Vⱼ`. So `F` cannot be found near the `Hⱼ`, including inside a translate of
  the composant `R(E)` as Hagopian's "essential to `fhᵢ[R(E)]`" suggests. The two routes you
  propose (choosing the `uᵢ` so that `u` avoids the composant of `t`, or density of the half
  composants) remain untried.

**Property 2 without Lemma 7?** Property 2 is used twice on p. 348, in Cases 1 and 2. Each time it
is used only to get a point of an essential continuum `N` within `ε₂` of `π⁻¹(p₄)`, a layer of `E`.
So a weaker Lemma 7, with the conclusion only at the points of one interior layer of `E`, would
suffice. I found no independent route to it.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 VI … (batch 161)", checks 1–8:

| check | place | outcome |
|---|---|---|
| 1 | pp. 345–346, `ε₁` | the families used are recorded (§1.1); one family must be added; `ε₁` exists |
| 2 | p. 346, the chain of ε₁-neighbourhoods "follows `h[E]`" | unargued; does not follow from the printed `ε₁`; true after shrinking `ε₁`; proved |
| 3 | p. 346, Property 1 and the parenthesis | unargued; true; proved (needs Moore's `D` from Lemma 8) |
| 4 | p. 346, T9 | first sentence true for `D` with (D), proved; essential if `Cl B` reaches far links; rest open |
| 5 | p. 347, T11 | unargued; the sides of `K` are not controlled by the printed `ε₁`; open |
| 6 | p. 347, Property 3 | "first point" unargued; "By Lemmas 2 and 3" proved; the crossing property open |
| 7 | pp. 343–344, Lemma 7 | triod proved; Lemma 7 reduced to `F`, proved in one case, open in the other |
| 8 | pp. 344–345, Lemma 9, the configuration | interlacing confirmed; two corrections; open |

No statement is refuted, and no defective proof is added. The chain sentence is repaired by a
smaller `ε₁` and is not counted. The count stays at fourteen.

## 3. Axioms

`doc/batches/audits/axioms-batch161.txt` lists `#print axioms` for the 51 new theorems: the 9
skeleton theorems and 42 supporting ones. Every line is `[propext, Classical.choice, Quot.sound]`,
and `sorryAx` appears in none. `axioms.txt` is regenerated with the group "Hagopian 1976 VI
(batch 161)" (1556 lines), and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `hagopian76_eps1`, `hagopian76_eps1_chain` | standard three |
| `exists_Gset`, `hagopian76_chain11`, `hagopian76_property1` | standard three |
| `hagopian76_T9` | standard three |
| `hagopian76_property3_shift` | standard three |
| `hagopian76_lemma7_triod`, `hagopian76_lemma7_of_F` | standard three |
| supporting (`H76Eps1`, `H76Lemma8Sep`, `H76Prop1`, `H76T9`, `H76Lemma7`, `H76Prop3`) | standard three |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 161 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157, 158) |
| T3 (345) | each point of `π[E]` is an end of an arc segment below `π[E]` | Lemma 9 (open: collar-rectangle chain, Theorem 28; configuration checked) |
| T4 (345–346) | `ε₁` | **proved** (`hagopian76_eps1`, `IsEps1`); the `Aᵢ`, `qᵢ` families still to be added with T6–T8 |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; `L`; **Property 1** | **proved** (`hagopian76_chain11`, `hagopian76_property1`) |
| T6 (346) | `I₁` below `(p₁, p₅)` | needs the proof of Lemma 9 |
| T7 (346) | `I₂` above; the region between in `π[St L]` | Property 1 (proved), Lemma 9 (proof) |
| T8 (346) | the bounded domain `D` | Jordan curve theorem, Schoenflies available; needs T6, T7 |
| T9 (346) | components of `M ∩ π⁻¹[D]` | **first sentence proved for `D` with (D)**; (D) and "follows" need T8 |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | Lemma 7 (reduced to one composant) |
| T11 (347) | `K` separates in `π⁻¹[D]` | open: needs T8 and the sides of `K` |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6 (proved), Lemma 2; needs T11 |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6 (proved), Lemma 4; needs T12 |
| T14 (347) | **Property 3** | **"By Lemmas 2 and 3" proved**; the least `v` and the crossing property open |
| T15 (347–348) | `e`, `J`, `xᵢ` | `d⁻¹[[0, e]] = E` proved; Property 3 |
| T16 (348) | **Property 4** | Property 2 |
| T17 (348–349) | the induction | Property 2 (twice), Property 3, Lemma 6 (proved), Lemma 4, Lemma 5 |

**Gateways now.**
1. The collar geometry: Lemma 9's proof, then T6–T8 and `D`. T9 (rest), T11 and Property 3 all wait
   on `D`.
2. Lemma 7 in the one-composant case, for Property 2 (T10, T16, T17).

## 5. Skeleton proposal for the rest of Theorem 1

Common context:
* `M : Set Pt`, compact, connected, homogeneous and indecomposable;
* `E`, `k` with `IsMinimalAdmissible E k`;
* `π`, `γ` as in `exists_quotient_plane'`, and `F` with `IsCollar γ F`;
* `ε₁` with `IsEps1 k ε₁`;
* `L` from `hagopian76_property1`.

For a collar `F`, write `rect a b c := F '' (Ioo a b ×ˢ Ioo (-c) c)`.

```lean
/-- **T4, completed**: the collar families of `ε₁` (verticals `Aᵢ = π⁻¹[F '' ({tᵢ} ×ˢ Icc (-1) 1)]`). -/
structure IsEps1C (k) (π) (F) (t : Fin 5 → ℝ) (ε₁ : ℝ) extends IsEps1 k ε₁ : Prop where
  vert : ∀ i, ∀ x ∈ π ⁻¹' (F '' ({t i} ×ˢ Icc (-1) 1)), ∀ y ∈ toPt (layerSet k (Bset i)),
    3 * ε₁ ≤ dist x y
  top : ∀ i, ∀ x ∈ toPt E, 3 * ε₁ ≤ dist x (π⁻¹-point of F (t i, 1))

/-- **Lemma 9, proof form** (T3, T6): an arc segment below `π[E]` from each point of `γ`, in collar
coordinates; and the horizontal interval `I₁` (T6). -/
theorem hagopian76_lemma9_below … : ∃ hh > 0, Disjoint (F '' (Icc t₁ t₅ ×ˢ Ioc (-hh) 0 \ …)) (π '' M)

/-- **T7**: the arc `I₂` above `(p₁, p₅)` in `π[St L] − π[M]`, with the region between in
`π[St L]`. -/
theorem hagopian76_T7 … : ∃ I₂ : Set Pt, TArc r s I₂ ∧ Disjoint I₂ (π '' M) ∧ I₂ ⊆ π '' ⋃ i, L i ∧ …

/-- **T8**: `D`, the bounded complementary domain of `I₂ ∪ (p₁, p₅) ∪ (p₁, r) ∪ (p₅, s)`, with
property (D) of `hagopian76_T9`. -/
theorem hagopian76_T8 … : ∃ D : Set Pt, IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    frontier D = I₂ ∪ … ∧ ∀ x : M, (x : Pt) ∈ closure (π ⁻¹' D) → ∃ j, 1 ≤ j ∧ j ≤ 9 ∧ (x : Pt) ∈ L j

/-- **T10, Property 2** (from Lemma 7). -/
theorem hagopian76_property2 … (hL7 : <Lemma 7 at ε₂>) : ∃ ε₃ > 0, ε₃ < ε₂ ∧ ∀ h, ε₃-homeo h → …

/-- **T11** (shape in `Hagopian76F.lean`). -/
theorem hagopian76_T11 … : ∀ x ∈ L 1 ∩ M ∩ π ⁻¹' D, ∀ z ∈ L 9 ∩ M ∩ π ⁻¹' D,
    connectedComponentIn (π ⁻¹' D \ K) x ≠ connectedComponentIn (π ⁻¹' D \ K) z

/-- **T12**: `p ∈ K` and `ε₃/2`-homeomorphisms `h`, `h₁` with (1)–(3). -/
theorem hagopian76_T12 … : ∃ (p : M) (h h₁ : M ≃ₜ M), (p : Pt) ∈ K ∧ … ∧
    IsEssential' (h '' Rset k) (closure (connectedComponentIn (M ∩ π ⁻¹' D) p)) ∧
    Separates (π ⁻¹' D) (toPt (Rset k)) p ((h₁.trans h.symm) p)

/-- **T13**: the irreducible `F` (Zorn on the extensions away from `k⁻¹(0)` separating `p` from
`f(p)`; existence from Property 1 and `hagopian76_closure_extUnion`). -/
theorem hagopian76_T13 … : ∃ F d, IsExtensionAway E (layer k 0) F ∧ IsMinimalAdmissible F d ∧
    layer d 0 = layer k 0 ∧ Separates (π ⁻¹' D) (toPt F) p (f p) ∧ ∀ F', … → F ⊆ F'

/-- **T14, Property 3** (shape in `Hagopian76F.lean`, with `F` from T13). -/
theorem hagopian76_property3 … : ∀ Q ∈ crossingComponents F d D, ∀ t, ¬ Q ⊆ layer d t

/-- **T15**: `e` with `d⁻¹[[0, e]] = E`, the finite collection `I` of minimal crossing intervals,
`J = I ∪ {[0, e]}`, and the increasing `xᵢ`. -/
theorem hagopian76_T15 … : ∃ (n : ℕ) (x : Fin (2 * n) → unitInterval), StrictMono x ∧ x 0 = 0 ∧ …

/-- **T16, Property 4** for an interval `[x₂ᵢ₋₁, x₂ᵢ]`. -/
def Property4 (…) (i : ℕ) : Prop := ∃ y ∈ K, IsEssential' … ∧ Separates (π ⁻¹' D) (layerSet d (Icc …)) y (f y)

/-- **T17**: Property 4 passes from `[x₂ᵢ₋₁, x₂ᵢ]` to `[x₂ᵢ₋₃, x₂ᵢ₋₂]` (Cases 1 and 2); `[x₁, x₂]` does
not have it. -/
theorem hagopian76_T17_step … (h4 : Property4 … i) : Property4 … (i - 1)
theorem hagopian76_T17_base … : ¬ Property4 … 1

/-- **Theorem 1** (p. 345). -/
theorem hagopian76_theorem1 : Hagopian76Thm1
```

The final assembly: assume `M` has a decomposable subcontinuum. Then T0 (`hagopian75_typeA'`) and
T1–T2 give the set-up, T13–T15 give `n` and Property 4 for the last interval, and T17 descends to
`[x₁, x₂]`, contradicting the base case. Order proposed for batch 162:
1. Lemma 9's proof in collar rectangles (it gives T3 and T6);
2. T7 and T8 (it gives (D), and so T9 in full);
3. T11 and Property 3;
4. T12 and T13;
5. Lemma 7 in the one-composant case.
