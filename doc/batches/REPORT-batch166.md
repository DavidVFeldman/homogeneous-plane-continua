Commission read: `doc/batches/COMMISSION-batch166.md` (batch 166 — Part E, Hagopian 1976 XI: Theorem 1 — `D`, `K₀`, Property 3, T12, T13; then T15–T17 and the assembly).

# Report, batch 166

**Status.**
* **A. `D` as a Jordan domain: proved.**
  * `rect_domain`: statement unchanged.
  * `hagopian76_D`: in the shape chosen in §1.A.
* **B. `K₀`: proved** (`hagopian76_K0`, shape in §1.B).
  * Added: `hagopian76_K0_crosscut`. `K₀` separates the two side edges of `D`.
* **C. "`L − {L₁, L₁₁}` follows `Cl B`": open.** Step 2 of the suggested route fails as stated (§1.C).
* **D. Property 3: open.** §1.D answers both questions the commission asks.
* **E. T12: open.**
  * "Inaccessible" is not used after `p` and `q` are chosen.
  * Inside `W`, the two composants exist without Mazurkiewicz (`exists_two_composants_in_open`, proved).
  * What is missing is such points on `K`; the obstruction is in §1.E.
* **F. T13, T15–T17, `hagopian76_theorem1`: open** (not reached; the skeleton proposal is in §5).
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76K` at the end of `HPC.lean`.
* No declaration uses `sorry`. The open statements appear only inside the comment block at the end of
  `Hagopian76K.lean`.
* All 18 new theorems use only `propext`, `Classical.choice` and `Quot.sound` (§3).
* The regenerated `axioms.txt` has 1704 lines (1686 + 18), and `sorryAx` appears in none of them.

**Progress lines** (as written during the run):
* `STATUS: A rect_domain proved.`
* `STATUS: A hagopian76_D proved.`
* `STATUS: B hagopian76_K0 proved.`
* `STATUS: B (addition) hagopian76_K0_crosscut proved.`
* `STATUS: C left open — an end of Cl B is part of a layer, so step 2 of the route does not close.`
* `STATUS: D Property 3 left open — the least v needs attainment, the shift needs a margin.`
* `STATUS: E exists_two_composants_in_open proved; T12 left open — points of Cl R(E) on K near x not argued.`
* `STATUS: F T13, T15–T17, theorem 1 left open (not reached).`

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76K.lean` | the skeleton: `rect_domain`, `hagopian76_D`, `hagopian76_K0`, `hagopian76_K0_crosscut`; the open items as a comment block |
| `H76Domain.lean` | `isConnected_compl_rect`, `tarc_frame` (the `U` frame is an arc), `rect_domain_aux`, `rect_domain_low` (the low strip lies in `D′`), `rect_domain_vert` (a vertical segment up to its first point on `I` lies in `D′`) |
| `H76DCollar.lean` | `pi_isClosedMap`, `pi_preimage_isPreconnected`, `tarc_pullback`, `hagopian76_D_aux`, `mem_toPt_layer_of_pi_eq`, `K0_aux` |
| `H76Crosscut.lean` | `rect_domain_crosscut` (collar coordinates), `K0_crosscut_aux` (plane) |
| `H76TwoComposants.lean` | `exists_two_composants_in_open` |

**Edits to existing files** (all allowed by the commission):
* `HPC.lean`: one import.
* `Axioms.lean` and `axioms.txt`: the new group "Hagopian 1976 XI (batch 166)".
* `README.md`, `LEDGER.md` §6, `OPEN.md`.
* `Hagopian76J.lean`: one pointer line in the comment block (`hD` is now `hagopian76_D`). No other
  earlier file has a commented-out copy of a statement proved here.

**Housekeeping.** The commission is now `doc/batches/COMMISSION-batch166.md`. The skeleton is kept
unchanged in `doc/batches/skeletons/Hagopian76K.lean`. Nothing is left at the root.

## 1. The items

### 1.A `D` as a Jordan domain — proved

**`rect_domain` (statement unchanged).**
* `0 < r₂` and `0 < s₂` hold because `I ⊆ [a, b] × (0, c]`.
* The frame `{a} × [0, r₂] ∪ [a, b] × {0} ∪ {b} × [0, s₂]` is an arc from `r` to `s` (`tarc_frame`:
  three segments glued by `TArc.union`).
* `I` meets the frame exactly in `{r, s}`: it misses the bottom edge and meets the side edges only at
  `r` and `s`. So `I ∪ frame` is a simple closed curve.
* `jordan_curve_theorem` gives the bounded domain `D′`.
* The complement of the closed rectangle is connected and unbounded (`isConnected_compl_rect`, by
  four half-planes) and misses the curve. So it lies in the unbounded domain, and `D′` lies in the
  closed rectangle. Since `D′` is open, it lies in the open rectangle.
* The frontier is the curve, as the commission says.

**`hagopian76_D`.** The shape was left to the batch. It starts from any arc `I₂` with the conclusions
of `hagopian76_T7` (over `[a, b] ⊆ (0, 1)`, height `c ≤ 1`).
* **Pull-back.** `I₂ ⊆ F[[a, b] × (0, c]]`, and `F` is an embedding on that set, so `I₂` pulls back
  to an arc `I` from `(a, r₂)` to `(b, s₂)` (`tarc_pullback`, through `IsEmbedding.toHomeomorph`).
  `I` meets the side edges only at its ends, because `F` is injective. `rect_domain` gives `D′`.
* **`D = F[D′]` is open.** `F` is an embedding of the closed rectangle and `F` of the open rectangle is
  open, so `F[D′] = W ∩ F[open rectangle]` for an open `W`.
* **`D` is connected and bounded.**
* **Frontier.** `closure F[D′] = F[closure D′]` (compactness), so the frontier is
  `F[frontier D′] = I₂ ∪ F[[a, b] × {0}] ∪ F[{a} × [0, r₂]] ∪ F[{b} × [0, s₂]]`. That is
  `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩`, so `D` is Hagopian's "bounded complementary domain".
* **`π⁻¹[D]` is open** (continuity).
* **`D` meets `π[M]`.**
  * `I` stays above some height `c₀ > 0`, and the low strip `(a, b) × (0, c₀)` lies in `D′`
    (`rect_domain_low`). The middle of the bottom edge is a frontier point of `D′`, and the strip is
    connected and misses the frontier.
  * `M_meets_above` gives a point of `π[M]` in `F[(a, b) × (0, c₀)]`. Like `M_meets_above`, this needs
    a strip below `γ([a, b])` that misses `π[M]` (hypothesis `hbelow`; `hagopian76_I1` supplies it at
    `[3/22, 19/22]`).
* The collar data are part of the conclusion, for later items: `r₂`, `s₂`, the pulled-back arc and
  its intersection with the side edges, `D′` and its frontier.

### 1.B `K₀` — proved

**`hagopian76_K0`.** The shape was left to the batch. It uses only the collar properties of `D′`
from `hagopian76_D` and takes any `t₀ ∈ (a, b)` (Hagopian's case is `t₀ = 11/22`).
* **`w` exists.** `I` is connected and joins abscissa `a` to abscissa `b`, so it meets the vertical
  over `t₀`. That intersection is compact, and `w` is its lowest point.
* **The segment lies in `D′`.** `{t₀} × (0, w₂)` misses `I` and lies in `D′` (`rect_domain_vert`).
* **`K₀ = π⁻¹F[{t₀} × (0, w₂)]`:**
  * it lies in `π⁻¹[D ∩ F[{t₀} × (0, c)]]`, which is Hagopian's `π⁻¹[D ∩ ⟨p₃, q₃⟩]`;
  * **it is a component of that set**: a connected `S` in the set that meets `K₀` pulls back to a
    connected subset of the vertical inside `D′`; it cannot pass `w`, since `w ∉ D′` because
    `w ∈ frontier D′`; so it lies in `K₀`;
  * **it is connected** (`pi_preimage_isPreconnected`): `π` restricted to `R² − E` is an open
    embedding (`eq_of_pi_eq_off`, `pi_isOpen_image_off`), and the segment misses `π[E] = F[[0, 1] × {0}]`;
  * **it misses `E`**;
  * **its closure meets `π⁻¹(p₃) = k⁻¹(t₀)` and `π⁻¹[I₂]`**: `π` is a closed map (`pi_isClosedMap`:
    the saturation of a closed `A` is `A` together with the union of the layers over the compact
    set `k[A ∩ E]`). So `π[Cl K₀]` is closed and contains `F(t₀, 0) = γ(t₀)` and `F(t₀, w₂) ∈ I₂`.

**Added: `hagopian76_K0_crosscut`.** `K₀` is a cross-cut of `D`: no connected subset of
`π⁻¹[D] − K₀` has closure meeting both `π⁻¹F[{a} × (0, r₂)]` and `π⁻¹F[{b} × (0, s₂)]`.
* The proof (`rect_domain_crosscut`) uses a single Jordan curve, `J_L = I_L ∪ {a} × [0, r₂] ∪
  [a, t₀] × {0} ∪ {t₀} × [0, w₂]`, where `I_L` is the sub-arc of `I` from `r` to `w`.
  * A point of the open right edge lies in the unbounded domain of `J_L`: a horizontal ray to the
    right misses `J_L`.
  * Near a point of the open left edge, `J_L` is the edge alone. So the half-disc to the right of
    the edge lies in the bounded domain, and so do the points of `D′` near that point.
  * A connected set missing `J_L` cannot do both.
* No θ-curve theorem is needed.
* **What this does and does not give.**
  * It is the separation that the single component `K` really has: "a component of `M ∩ π⁻¹[D]`
    whose closure meets both side edges meets `K`". T12 and T17 use it in this form ("Let `yᵢ₋₁` be a
    point of `K ∩ Cᵢ₋₁`").
  * It does **not** give T11's separation of `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]`. A point of
    `L₂` may lie in a channel belonging to the right-hand part. As the commission directs, that
    separation stays with `hagopian76_T11` for the whole section.

### 1.C "`L − {L₁, L₁₁}` follows `Cl B`" — open

The route of commission §1.C, checked step by step:
1. **Correct.** This is `hagopian76_T9_full`.
2. **Fails as stated.**
   * Write `G = h⁻¹[Cl B]` and `u = min k[G]` (`G` meets several layers when `B` meets links three
     apart). The "end" of `Cl B` at `u` is `h[G ∩ k⁻¹(u)]`, which is part of a layer, not a whole
     layer.
   * Suppose a point `x` of it lies in `π⁻¹[D]`. Boundary bumping in the continuum `h[k⁻¹[0, u]]`
     gives a continuum `Q ∋ x` inside `M ∩ π⁻¹[D]`. `B` is closed in `M ∩ π⁻¹[D]`, so `Q ⊆ B ⊆ h[G]`,
     and therefore `Q ⊆ h[G ∩ k⁻¹(u)] ⊆ h[k⁻¹(u)]`.
   * That is a contradiction only if `x` is a limit of `h[k⁻¹[0, u)]`. In a type A′ continuum a point
     of a layer need not be such a limit: layers have empty interior, but a point may be approached
     only from the side `> u`.
   * **Example.** Take a type A′ continuum made of a `sin(1/x)` curve, its limit bar `T`, and an arc
     leaving `T` to the right from one point `t₀ ∈ T`. It is irreducible between the two free ends,
     its layers are the points of the curve, `T`, and the points of the arc, and `T` has empty
     interior. For `G =` curve `∪ T`, the end at `v = max k[G]` is all of `T`, and no point of `T`
     other than `t₀` is a limit of the arc side. If `h[T] − {h(t₀)}` meets `π⁻¹[D]` while `h(t₀)`
     does not, the argument of step 2 finds no continuation of `B`.
   * The sentence "`h[E]` would continue `B` inside `π⁻¹[D]`" is therefore unargued.
   * Two possible repairs:
     * prove that `G ∩ k⁻¹(u) ⊆ Cl k⁻¹[0, u)` for the subcontinua `G` that occur;
     * replace "ends" by the end sets of a type A′ structure on `Cl B` itself. That needs `Cl B` to
       be of type A′ with end sets in `L₂` and `L₁₀`, which is the statement being proved.
3. **Correct** (`I₂` misses `π[M]`; `Cl B ∩ E = ∅`).
4. **The margin.** By link control with `η < 1/22`, a point of `M` over the left edge (abscissa
   `3/22`) lies only in links of Lean index `≤ 2`. Property 1 then puts both ends in `h[piece 1 ∪ … ∪
   piece 4]`. `Cl B` can still reach `L₄`, so it is one link short for components meeting only `L₄`.
   * **Answer to the commission's question:** restrict to components through a point of `K₀`, i.e.
     over abscissa `11/22`. Link control puts such a point in `L₅`, `L₆` or `L₇` (Lean 4–6). T12
     uses only `C` (through `p ∈ K`), and T17 only `Cᵢ₋₁` (through `yᵢ₋₁ ∈ K`), so this restriction
     costs nothing.
5. **Not reached** (it depends on 2).

The shape proposal is at the end of `Hagopian76K.lean` and in §5.

### 1.D Property 3 — open

* **The least `v`.** The sentence after "Let `v` be the first point" applies Lemma 1 and Property 1
  to a crossing component inside `d⁻¹(v)`. So **the infimum must be attained**: the set of
  parameters whose layer contains a crossing component must be closed from above. For the final
  contradiction, a crossing at some `u < v` suffices, whether or not `v` is attained.
  * Attainment is the hyperspace argument. `Z` is a limit of the closures of crossing components in
    `d⁻¹(vₙ)`, with `vₙ ↓ v`.
  * By upper semicontinuity of the layers of `d`, `Z ⊆ d⁻¹(v)`.
  * `Z` misses `π⁻¹[I₂]` (by `ε₂`) and misses `E` (`hagopian76_no_hair`; `Z` reaches the side edges,
    off the axis).
  * `Z` meets both side preimages, now that `D` exists with closed side edges.
  * A component of `Z ∩ π⁻¹[D]` reaching both sides then comes from boundary bumping in `Z`,
    applied from a point over one side.
  * The step still missing is that this component's closure meets both side preimages, and not only
    the frontier of `π⁻¹[D]` at `π⁻¹[I₂]` or at `E`. `Z` misses both, so boundary bumping gives a
    component whose closure meets `Fr π⁻¹[D] ∩ (sides)`. It has to reach the **other** side: a
    component of `Z ∩ π⁻¹[D]` could return to the same side. The cross-cut lemma applies once `Z`
    is known to meet `K₀`. Not formalized.
* **"By Lemma 1 and Property 1, `L` follows a type A′ continuum in `d⁻¹(v)` that meets
  `L₆ ∩ π⁻¹[D]`"**: unargued. It needs item C's "follows" for continua inside a layer of `F`.
* **The crossing property under the shift `g` needs a margin.** `g` is close to the identity, so
  `g[Q]` lies near `Q`. Then:
  1. `g[Q]` misses `π⁻¹[I₂]`, since `ρ(M, π⁻¹[I₁ ∪ I₂]) ≥ ε₂ > ε₃`;
  2. `g[Q]` may meet `E`, since `Q` approaches `E` from above, and so leave `π⁻¹[D]`;
  3. `Cl g[Q]` may fall short of the side edges.

  Proposed shape: crossing means "meets `π⁻¹[D]` on both sides of the side verticals, inside the
  strip of `hagopian76_link_control`", with the margin `ε₃` turned into collar coordinates by
  uniform continuity of `F⁻¹` on the closed strip. Then 3 holds with room to spare. For 2, cut `g[Q]`
  at `E`: the part over the middle third is still crossing by the cross-cut lemma.

### 1.E T12 — open

* **What "inaccessible" is used for.** The text after the choice of `p` and `q` (pp. 347–349) never
  mentions accessibility again. T12 needs only:
  * `p`, `q ∈ K ∩ W`;
  * `p`, `q ∉ R(E)`;
  * `p`, `q` in distinct composants of `Cl R(E)`, so that `C` and the `q`-component are different and
    `R(E)` can lie between them.

  Mazurkiewicz [10] is therefore not needed as a theorem. **Inside `W`**, such points exist by Baire
  (`exists_two_composants_in_open`, proved here in general: composants of an indecomposable
  continuum are meagre, `composant_isMeagre'`).
* **What is missing: such points on `K`.** `K` is an arc in the plane, and `p`, `q` must be points of
  `M` on it, close to `x`, inside `Cl R(E)`.
  * Every component of `M ∩ π⁻¹[D]` that reaches both side edges meets `K₀`
    (`hagopian76_K0_crosscut`). That such components exist near `x` is item C (together with
    `M_meets_above`).
  * Even granting C, such a component meets `K₀` somewhere, possibly high up on `K₀`, not near `x`.
    `x` is any point of `k⁻¹(p₃) ∩ Cl K`, and `π` collapses the whole layer, so a point of `K₀` low
    down need not be near `x`.
  * **Proposed repair:** choose `x ∈ k⁻¹(p₃) ∩ Cl(K₀ ∩ Cl R(E))`. This is nonempty once crossing
    components of `Cl R(E)` reach arbitrarily low on `K₀`, which follows from C and the cross-cut
    lemma.
  * Then `K₀ ∩ Cl R(E)` near `x` has to meet at least two composants other than `R(E)`. This is not
    automatic, because `K₀ ∩ Cl R(E)` is a closed subset of an arc. It holds if `K₀ ∩ Cl R(E) ∩ W`
    is uncountable and meets each composant in a countable set; neither fact is argued.
* **"By Property 1, `R(E)` intersects an arc in `K` that is irreducible between `C` and the
  `q`-component of `M ∩ π⁻¹[D]`, and `R(E)` separates these components in `π⁻¹[D]`"**: unargued.
  * Its content is that between two crossing components on the cross-cut `K₀` there is a crossing
    component of `R(E)`, which then separates them in `π⁻¹[D]`, by the cross-cut lemma applied to the
    two sub-domains.
  * Density of the composant `R(E)` puts points of `R(E)` between them. That those points lie on a
    *crossing* component of `R(E)` is what Property 1 is cited for. It needs item C for `h[E]`'s
    components.

### 1.F T13, T15–T17, Theorem 1 — not reached

## 2. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XI (batch 166)":
1. **p. 346, T8**, "Let `D` be the bounded complementary domain …": true; proved (`hagopian76_D`).
2. **p. 346, T9**, "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`": unargued; open. The
   suggested route fails at step 2 (§1.C). A one-link margin is lost at `L₄`; restricting to
   components through `K` repairs it.
3. **p. 347, Property 3**:
   * "Let `v` be the first point …": needs attainment, which is unargued.
   * "By Lemma 1 and Property 1, `L` follows a type A′ continuum in `d⁻¹(v)` …": unargued.
   * "This contradicts the definition of `v`": needs a margin under `g` (§1.D).
4. **p. 347, T12**:
   * "distinct inaccessible composants [10]": accessibility is not used afterwards. Distinct
     composants off `R(E)` in `W` are proved without [10]. On `K`, open (§1.E).
   * "By Property 1, `R(E)` intersects an arc in `K` …": unargued; open.
   * New: Hagopian's `x` should be taken in `Cl(K ∩ Cl R(E))`.
5. **p. 347, T13**, "The existence of such a continuum `F` follows from Property 1 and …": not
   reached.
6. **pp. 347–349, T15–T17**: not reached.

Nothing is refuted. The count of defective proofs stays at fourteen.

## 3. Axioms

Every one of the 18 new theorems shows `[propext, Classical.choice, Quot.sound]`. The per-theorem
list is in `doc/batches/audits/axioms-batch166.txt`.

| file | theorems |
|---|---|
| `Hagopian76K.lean` | `rect_domain`, `hagopian76_D`, `hagopian76_K0`, `hagopian76_K0_crosscut` |
| `H76Domain.lean` | `isConnected_compl_rect`, `tarc_frame`, `rect_domain_aux`, `rect_domain_low`, `rect_domain_vert` |
| `H76DCollar.lean` | `pi_isClosedMap`, `pi_preimage_isPreconnected`, `tarc_pullback`, `hagopian76_D_aux`, `mem_toPt_layer_of_pi_eq`, `K0_aux` |
| `H76Crosscut.lean` | `rect_domain_crosscut`, `K0_crosscut_aux` |
| `H76TwoComposants.lean` | `exists_two_composants_in_open` |

## 4. Dependency map of Theorem 1, updated

| step (page) | content | status after batch 166 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved |
| — (345) | the reparametrization | proved |
| T3 (345) | arc segments below `π[E]` | proved at interior points |
| T4, T5 (345–346) | `ε₁` (with `EndCtl`); `L`; Property 1 | proved |
| T6 (346) | `I₁` below `⟨p₁, p₅⟩` | proved |
| T7 (346) | `I₂` above; the region between in `π[St L]` | proved |
| T8 (346) | `D` | **proved** (`hagopian76_D`); property (D) proved (`hagopian76_T8`) |
| T9 (346) | components of `M ∩ π⁻¹[D]`; `ε₂` | proved (`hagopian76_T9_full`), except "follows `Cl B`" (**open**, §1.C) |
| T10 (346) | Property 2 | proved |
| T11 (347) | `K` | **`K₀` built** (`hagopian76_K0`); `K₀` separates the side edges (`hagopian76_K0_crosscut`); `L₂` from `L₁₀`: whole section (`hagopian76_T11`) |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | open: points of `Cl R(E)` on `K` near `x`; "R(E) intersects an arc in K …" (needs C) |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | open; needs T12 |
| T14 (347) | Property 3 | "By Lemmas 2 and 3" proved; the least `v` (attainment) and the margin under `g` open |
| T15 (347–348) | `e`, `J`, `xᵢ` | needs Property 3 |
| T16 (348) | Property 4 | needs Property 2 |
| T17 (348–349) | the induction | needs Property 2, Property 3, C, Lemmas 4–6 |

**Gateway.** Item C ("follows `Cl B`" for components through `K`). Property 3 (via the limit
continuum and Lemma 1), T12 (crossing components near `x`) and T17 (`L − {L₁, L₁₁}` follows
`Cl Cᵢ₋₁`) all wait on it.

## 5. Skeleton proposal for what remains

Set-up: `hagopian76_D` at `[3/22, 19/22]` and `hagopian76_K0` at `t₀ = 11/22`, with `D = F[D′]`,
`K₀`, `r₂`, `s₂`. "Crossing" for a set `Q` means
`(closure Q ∩ π⁻¹F[{3/22} × (0, r₂)]).Nonempty ∧ (closure Q ∩ π⁻¹F[{19/22} × (0, s₂)]).Nonempty`.

```
-- C, restricted to components through K₀
theorem hagopian76_T9_follows … (B : Set M) (hB : B ∈ components of M ∩ π⁻¹ D)
    (hBK : (toPt B ∩ K₀).Nonempty) :
    Crossing B ∧ ∃ (H : Set M) (dH : H → unitInterval), closure B = H ∧
      IsMinimalAdmissible H dH ∧ Follows (fun j : Fin 9 => L j.succ.castSucc) dH
-- C′, what T12 needs first
theorem crossing_near … (x ∈ toPt (layer k (11/22))) (ε > 0) :
    ∃ B ∈ components of M ∩ π⁻¹ D, Crossing B ∧ B ⊆ Cl R(E) ∧ (B ∩ K₀ ∩ ball x ε).Nonempty
-- D
theorem hagopian76_property3 … (hF : IsExtensionAway E (layer k 0) F') (hd : IsMinimalAdmissible F' d)
    (hdX : layer d 0 = layer k 0) :
    ∀ v (Q : Set M), Q ∈ components of F' ∩ π⁻¹ D → Crossing Q → ¬ Q ⊆ layer d v
theorem crossing_set_closed … : IsClosed {v | ∃ Q ⊆ layer d v, Q ∈ components … ∧ Crossing Q}
-- E
theorem hagopian76_T12 … : ∃ p ∈ K₀ ∩ M, ∃ h h₁ : M ≃ₜ M, (ε₃/2-close) ∧
    IsEssential (h ∘ k) (closure (component of p in M ∩ π⁻¹ D)) ∧
    Separates (Rset k) p (h₁ (h.symm p)) (π⁻¹ D)
-- F
theorem hagopian76_T13 … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

In this order, `crossing_near` (from C, `M_meets_above` and `hagopian76_K0_crosscut`) comes before
T12, and `crossing_set_closed` (the hyperspace limit) before Property 3.

## 6. Build provenance

* **Fresh checkout:** yes. The run started from the delivered repository, with no local build outputs
  of `HPC`.
* **Mathlib:** the compiled Mathlib files at the pinned commit were already present. They were
  neither downloaded nor rebuilt.
* **First full build:** about 75 minutes wall-clock in two parts:
  * `lake build HPC.Hagopian.Hagopian76J`, the import closure of the batch-165 skeleton: about 47
    minutes;
  * the first `lake build HPC` afterwards (the remaining modules plus the new files): about 27
    minutes.
