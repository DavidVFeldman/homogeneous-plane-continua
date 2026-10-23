Commission read: `doc/batches/COMMISSION-batch158.md` (batch 158 — Part E, Hagopian 1976 III: D1 by lower semicontinuity; Lemmas 5–7; Moore 1962 Theorem 28; Lemma 9).

# Report, batch 158

**Status.**
* **Proved:**
  * item A in full: `hagopian76_far_layer`, `hagopian76_initial_segment` (the strong form
    `d⁻¹[[0, s]] = E`, every layer of `E` a layer of `F`), and from them the re-rendered first
    paragraph of Lemma 4 (`hagopian76_lemma4_layers`) and `hagopian76_no_swallowed_layer`;
  * item B: **Lemma 5** (`hagopian76_lemma5`), by the commission's one-sided route;
  * item E: **Moore 1962, Theorem 28** (`moore62_theorem28`);
  * item F, first part: `exists_quotient_plane'` (the arc `π[E]` with its parametrization `γ`);
    the definitions `AbutSameSide`, `DecompAccessible` are in the build as given.
* **Open** (commented out with `OPEN (batch 158)` notes, no `sorry`; obstructions in `OPEN.md`,
  batch-158 section):
  * B. `hagopian76_two_sided_extension` — not needed (Lemma 5 is proved without it);
  * C. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
    `hagopian76_essential_typeA'`;
  * D. `hagopian76_lemma7`;
  * F. `hagopian76_lemma9`.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76C` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76C.lean` | the skeleton: items A, B (Lemma 5), E, F (first part) proved; the rest commented out with `OPEN (batch 158)` notes |
| `H76Far.lean` | item A: `lemma4_layers_far` (batch 157's bookkeeping with `k⁻¹(1) ⊆ d⁻¹(s)`), `closure_inter_of_preconnected`, `far_layer_aux` (the commission's route) |
| `H76Lemma5End.lean` | items A, B: `ext_layers`, `initial_segment_aux`, `lscAt_of_ext`, `lscAt_end_aux`, `lemma5_aux` |
| `H76Moore28.lean` | item E: `tscc_aposyndetic`, `tscc_cyclic`, `exists_side_arc`, `moore28_core`, `moore62_theorem28_aux` |
| `H76Quot.lean` | item F: `exists_quotient_plane'_aux` |
| `H76Sub.lean` | toward item C: `isTypeA'_of_subcontinuum` (a subcontinuum meeting two layers is `d⁻¹[[a, b]]` and of type A′), with `layerSet_Ioo_subset`, `layer_subset_closure_Ioo`, `layer_subset_closure_Ioo'`, `eq_layerSet_of_subcontinuum` |

The commented-out copies of `hagopian76_lemma4_layers`, `hagopian76_no_swallowed_layer` and
`hagopian76_lemma5` in `Hagopian76B.lean`, and of `hagopian76_lemma5` in `Hagopian76A.lean`, are
replaced by one-line pointers.

**Shape changes.** None to the statements of the skeleton. The proofs of the items of
`Hagopian76C.lean` are one-line applications of the supporting theorems listed above.

## 0. Check of the argument of commission §1

Every step checks; the formal proof is `far_layer_aux` (`H76Far.lean`).

1. *`s = 1`.* Batch 157's step `k⁻¹(1) ⊆ d⁻¹(s)` (`lemma4_layers_far`, last clause) makes `E` meet
   `d⁻¹(1)`; it meets `d⁻¹(0) = k⁻¹(0)`; so `E = F` by the end-set property of `F`. **Correct.**
2. *`0 < s < 1`.* `hagopian76_lemma5_interior` applies to `F`: its hypotheses are only that `F` is a
   type A′ subcontinuum of `M` with a minimal map, in the homogeneous indecomposable `M`. **Correct.**
3. *A limit point `y ∈ W` of `d⁻¹([0, s))`.* `W` is closed and `d⁻¹[[0, s]] = d⁻¹([0, s)) ∪ W` is
   connected, so the closure of `d⁻¹([0, s))` meets `W` (`closure_inter_of_preconnected`).
   **Correct.**
4. *`d⁻¹(uᵢ) = k⁻¹(k yᵢ)`.* The equality clause of `lemma4_layers_aux` for `u < s`; `y ∈ E` since `E`
   is closed and `d⁻¹([0, s)) ⊆ E`. **Correct.**
5. *`W ⊆ k⁻¹(c)`.* Correct. The formal proof uses neighbourhoods instead of sequences, and the
   continuity of `k` at `y` and at the points of `W` instead of the upper semicontinuity of `E` (for
   the decomposition into the fibres of a continuous map on a compact space they say the same): for
   `w ∈ W` and `ε > 0`, lower semicontinuity of `F` at `y` gives a neighbourhood `O` of `W` whose
   points have layers meeting `B(w, ε)`; a point `y′ ∈ d⁻¹([0, s)) ∩ O` near `y` gives a point
   `z ∈ k⁻¹(k y′)` within `ε` of `w`, with `k y′` near `c`. So `w ∈ E` and `k w = c`.
6. *`c = 1`.* `k⁻¹(1) ⊆ W ⊆ k⁻¹(c)`. **Correct.**

The strong form follows: `d⁻¹[[0, s]] = E` (`d⁻¹([0, s)) ⊆ E` and `d⁻¹(s) = k⁻¹(1) ⊆ E`), and every
layer of `E` is a layer of `F` (a layer `k⁻¹(t)` in `d⁻¹(s) = k⁻¹(1)` has `t = 1`). When `F = E`
(`s = 1`) the two decompositions coincide, since each layer of either lies in a layer of the other
(`initial_segment_aux`).

## 1. The items

### A. D1: proved

`hagopian76_far_layer` and `hagopian76_initial_segment` as in §0. The printed and re-rendered forms
follow: `hagopian76_lemma4_layers` (each clause from the strong form) and
`hagopian76_no_swallowed_layer` (from it by batch 157's `no_swallowed_of_lemma4_layers`). The half-bar
model of batch 156 shows that the sentence fails without homogeneity; homogeneity enters through
`hagopian76_lemma5_interior` (Lemmas 2 and 3) applied to the larger continuum `F`.

### B. Lemma 5: proved

`lemma5_aux` (`H76Lemma5End.lean`), the commission's route:
1. At `X = k⁻¹(0)`: the reversed map `1 − k` is minimal admissible
   (`IsMinimalAdmissible.symm_comp`), with `(1 − k)⁻¹(0) = Z`. Lemma 4 (`exists_proper_extension`)
   gives an extension `G ⊋ E` with map `D`, `D⁻¹(0) = Z`.
2. Item A for `(E, 1 − k) ⊆ (G, D)` (`ext_layers`): `0 < s < 1`, `D⁻¹(s) = (1 − k)⁻¹(1) = X`, and the
   layer of `G` through any point of `E` is its layer in `E`.
3. `G` is lower semicontinuous at `X` (`hagopian76_lemma5_interior` for `G`), and this passes to `E`
   (`lscAt_of_ext`: the neighbourhood is intersected with `E`; the layers it meets are layers of `E`).
4. At `Z`: the same with an extension away from `X` and the map `k` itself
   (`lscAt_end_aux` covers both). Then `hagopian76_lemma5_of_ends`.

`hagopian76_two_sided_extension`: **not needed**, and not short. Item A makes `E` an initial segment of
each of the two extensions, but `F₁ ∪ F₂` still needs a glued admissible map, its irreducibility and
`F₁ ∩ F₂ = E` (the tail of `F₁` beyond `Z` disjoint from the tail of `F₂` beyond `X`), which is an
atriodicity argument of the type of `ext_of_branch`. Left commented out.

### C. Lemma 6 and the unnumbered claims: open

The D1 obstruction recorded in report 157 is gone: step 6's "has the decomposition of `E` as a
subcollection" is item A (in the form: the layers of `N` meeting `K` are layers of `K`,
`hagopian76_initial_segment` applied to `K ⊆ N`), and Lemma 5 holds for every extension. Steps 1–8
were not formalized in this batch. What each needs, beyond what is now in the repository:
* steps 1–3: Lemma 1 (`B ∩ E`, `C ∩ E` continua) and the linear order — direct;
* step 5: the limit `c` of the far ends `zᵢ`, a `δ`-homeomorphism `f` with `f(c) = zᵢ`, and the
  argument that `f[L]` is disjoint from `L` and lies in `R(X, E)` — the main work;
* steps 6–7: `ε₁`, `h₁`, `h₂`, and the triod `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]`;
* step 8: the 1975 ¶2 triod with `Q`, `f₁[Q]`, `f₂[Q]`.

`hagopian76_essential_typeA'` additionally needs the containment of an essential continuum in one
extension. The containment is supplied by step 5: if a continuum `H ⊆ R(X, E)` lay in no `Fᵢ`, then
`H ∩ Fᵢ` (a continuum, Lemma 1) would contain the tail `Fᵢ ∖ Fₘ` for infinitely many `i` (item A: `Fₘ`
is an initial segment of `Fᵢ`), so `H` would contain the far ends `zᵢ` and their limit `c`, against
`c ∉ R(X, E)`. Given the containment, the rest is Lemma 5 for that extension (proved): a subcontinuum
meeting two layers `d⁻¹(a)`, `d⁻¹(b)` (`a < b` extreme) contains `d⁻¹((a, b))` by irreducibility, and
`d⁻¹[[a, b]]` by lower semicontinuity at `d⁻¹(a)` and `d⁻¹(b)`; with the map rescaled to `[0, 1]` it
is of type A′. This second part is formalized in `H76Sub.lean` (`isTypeA'_of_subcontinuum`, for any
irreducible `G` with a minimal admissible map whose decomposition is lower semicontinuous at every
element, which Lemma 5 supplies for an extension); the containment is not.

### D. Lemma 7: open

Uses Lemma 5 (now proved) and Lemma 6 (open): the limit points `t`, `u`, `p` in the indecomposable
`Cl R(E)`, and the essential continuum `F` of `fhᵢ[R(E)]` through `u`. Blocked by item C.

### E. Moore 1962 Theorem 28: proved

The excerpt in `doc/sources/moore1962-excerpts.pdf` breaks off inside Moore's proof (p. 171 ends with
"There exist two mutually exclusive domains `D_C` and `D_F` such that", and the next page of the
excerpt is p. 172 of a different section), so Moore's route could not be followed, and the batch-151
crossing results were not needed. **Route** (`moore62_theorem28_aux`):
1. `J = P ∪ Q`, arcs from `a` to `b` meeting only in `a`, `b` (`tscc_split`). If `c`, `f` lie in
   different components of `J − {a, b}`, one lies in `P − {a, b}` and the other in `Q − {a, b}` (each
   is connected).
2. `D` is the bounded side of `J` (Jordan curve theorem, batch 147/148: `D` is open, connected,
   disjoint from `J`, and relatively clopen in the side containing it); `E = (Cl D)ᶜ` is the other
   side.
3. An arc `L` from `a` to `b` with `L − {a, b} ⊆ E` (`exists_side_arc`): a simple closed curve is
   aposyndetic (`tscc_aposyndetic`) and has no cut point (`tscc_cyclic`), so each of its points is
   accessible from each side (`accessible_of_cyclic`, batch 152); two accessing arcs from one point of
   `E` are joined (`TArc.join`).
4. `P ∪ L` is a simple closed curve; its side `S` containing `Q − {a, b}` contains `D`
   (`sub_side_of_closure`), and the other side `T` misses `Cl D`.
5. Take `x ∈ T` near `c` and `y ∈ E ∩ S` near `f`. In the complement of `H ∪ L` they are joined
   through `K`; in the complement of `Cl D` they are joined in `E`; and `(H ∪ L) ∩ Cl D = H` is
   connected. By Janiszewski's theorem (`janiszewski_compact`, batch 146), `L ∪ Cl D` does not
   separate `x` from `y`. But the component of `x` in its complement lies in `T` (`side_eq_cc`), and
   `y ∈ S`. Contradiction.

The skeleton's reading of "`H` and `K` … subset of `D`" as subsets of `D ∪ J` is kept.

### F. The arc parametrization; `AbutSameSide`, `DecompAccessible`; Lemma 9

* `exists_quotient_plane'`: **proved** (`H76Quot.lean`), the construction of
  `exists_quotient_plane_aux` returning `γ` (continuous and injective on `[0, 1]`, hence an
  embedding).
* `AbutSameSide`, `DecompAccessible`: in the build, as in the skeleton.
* `hagopian76_lemma9`: **open.** Its plane-topology input, Moore 1962 Theorem 28, is now proved, and
  `π`, `γ` are available. Missing:
  1. **Arc straightening.** "We assume without loss of generality that `π[E]` is lying on a
     horizontal line `B` in `R²`" needs a homeomorphism of the plane taking an arc onto a segment.
     Neither Moore 1919 nor F.A. in the repository states it for the plane: Moore 1919's
     Schoenflies-type theorem (`m19_schoenflies`, `HPC/Moore/M19EF.lean`) is stated for his abstract
     spaces satisfying Axioms 1–8 and for a simple closed curve with four marked points; using it for
     an arc in `R²` needs `R²` as a model of the axioms and the arc completed to a simple closed curve,
     and then a second homeomorphism straightening an arc of a circle. None of this was done. Since
     `AbutSameSide` builds the straightening into the conclusion, Lemma 9 cannot be stated around
     it; what can be used instead is the side of the simple closed curve formed by `π[E]` and an
     auxiliary arc (as in item E, step 4), with "abut on the same side" read as "both arcs start into
     the same complementary domain of such a curve". That reading would need a change of
     `AbutSameSide`.
  2. **The chain `G` and Lemma 8 with prescribed caps.** Hagopian's three-link chain `G` following
     `E` with `π[Gᵢ]` and `π[Gᵢ] ∩ π[Gᵢ₊₁]` open disks, and the free refinement with `A ⊆ G₁`,
     `B ⊆ G₃` prescribed. Images of saturated open sets under `π` are open (`π` is a quotient map);
     that they can be taken to be disks needs the plane Schoenflies theorem again.
  *Plan:* (i) state and prove arc straightening in `R²` from the Jordan curve theorem and
  accessibility (or change `AbutSameSide` to the side form above); (ii) Lemma 8 with prescribed caps
  (same proof as `hagopian76_lemma8`, `H76Lemma8.lean`); (iii) Lemma 9's argument: the vertical arc
  `π[I]` below `π[E]`, the homeomorphism `h` near the identity with `h(y′) = u′`, and Theorem 28
  applied to `πh[D]` and `π[C ∪ I ∪ Cl G₁]`.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 III … (batch 158)", checks 1–6. In summary:

| check | place | outcome |
|---|---|---|
| 1 | p. 341, Lemma 4, first paragraph, last sentence | reason insufficient (half-bar model); true, even in the strong form; supplied by an argument Hagopian does not give (Lemmas 2, 3 through lower semicontinuity of `F`) |
| 2 | p. 341, Lemma 5: the two-sided `F`; "each element of `A` that is not an end set of `E` is an element of `B`" | second sentence true (item A on each side); the route used takes one extension on each side, never `F`; that `F` is of type A′ remains unargued and is not needed |
| 3 | pp. 342–343, Lemma 6, steps 1–8 | step 6 no longer blocked (item A); all steps true as far as checked; not formalized |
| 4 | pp. 343–344, Lemma 7, the two sentences | unchanged: unargued details, depend on Lemma 6; open |
| 5 | p. 344, Lemma 9, five sentences | the WLOG needs arc straightening (not in the repository); the chain `G`: images of saturated open sets are open, disks unargued; "`I` intersects `Bd G₂` and misses `Cl (G₁ ∪ G₃)`": a choice of `G`; atriodicity sentence true; [13, Theorem 28]: proved (item E) |
| 6 | p. 347, "`d⁻¹[[0, e]] = E`" | true: item A, strong form (`hagopian76_initial_segment`) |

## 3. Axioms

`doc/batches/audits/axioms-batch158.txt` lists `#print axioms` for the new theorems. Every line is
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` appears in none. `axioms.txt` is regenerated
with the group "Hagopian 1976 III (batch 158)", and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `hagopian76_far_layer`, `hagopian76_initial_segment`, `hagopian76_lemma4_layers`, `hagopian76_no_swallowed_layer` | standard three |
| `hagopian76_lemma5` | standard three |
| `moore62_theorem28` | standard three |
| `exists_quotient_plane'` | standard three |
| the supporting theorems (`H76Far`, `H76Lemma5End`, `H76Moore28`, `H76Quot`, `H76Sub`) | standard three |

## 4. Dependency map of Theorem 1, updated

Legend of report 157: **[D1]** needed D1 (or its strong form); **[L5e]** needed Lemma 5 at end sets.
Both are now proved, so these marks no longer block anything. What remains is listed in the last
column.

| step (page) | content | status after batch 158 |
|---|---|---|
| T0–T2 (345) | type A′ `E`; accessibility; `S`, `π`, the arc `π[E]` | proved (batches 155, 157; `exists_quotient_plane'`) |
| T3 (345) | each point of `π[E]` an end of an arc segment below `π[E]` | Lemma 9 (open: arc straightening, Lemma 8 with caps); Theorem 28 proved |
| T4 (345–346) | `ε₁`; `ε₁`-neighbourhoods of `k⁻¹[[(i−1)/11, i/11]]` follow `h[E]` | unblocked; continuity of `k` and compactness |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; ordered free refinement `L`; **Property 1** | unblocked; Lemma 2, Lemma 8 with prescribed caps, Lemma 1 |
| T6 (346) | `I₁` below `(p₁, p₅)` | needs Lemma 9's proof |
| T7 (346) | `I₂` above; the region between in `π[St L]` | Property 1, Lemma 9 (proof), Lemma 2 |
| T8 (346) | the bounded domain `D` | Jordan curve theorem (available) |
| T9 (346) | components `B` of `M ∩ π⁻¹[D]`; `Cl B` an `ε₁`-image of an essential continuum | Lemma 5 (proved); "essential" by name |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | Lemma 7 (open, via Lemma 6) |
| T11 (347) | `K`, the component of `π⁻¹[D ∩ (p₃, q₃)]`; `K` separates in `π⁻¹[D]` | unblocked; Theorem 28 type plane topology (now available), Property 1 |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹` | Lemma 6, Mazurkiewicz 1929; Lemma 5 (proved) |
| T13 (347) | `F` irreducible w.r.t. (1), (2) | Lemma 6 (proof); Lemma 4 |
| T14 (347) | **Property 3** | unblocked; Lemmas 1, 2, 3, Property 1 |
| T15 (347–348) | `e` with `d⁻¹[[0, e]] = E`; `J`, `xᵢ` | **`d⁻¹[[0, e]] = E` proved** (`hagopian76_initial_segment`); Property 3 |
| T16 (348) | **Property 4** | Property 2 / Lemma 7 |
| T17 (348–349) | the induction, Cases 1 and 2 | Lemma 6 (proof), Property 3, Lemma 4, essential continua (Lemma 5 proved; containment from Lemma 6 step 5), Property 2 |

**What is now unblocked.** Everything that was marked only [D1] or [L5e] for those reasons: T15's use
of the strong form is proved, Lemma 5 is available for T9, T12, T17. The remaining blockers are
Lemma 6 (T12, T13, T17, and through Lemma 7 T10, T16), Lemma 9 (T3, T6, T7), and Property 1 (T5,
T7, T11, T14).

## 5. Reading plan for batch 159: Property 1 and steps T4–T9, T11, T14

1. **Lemma 8 with prescribed caps** (`H76Lemma8.lean`): the same proof with `A ⊆ G₁`, `B ⊆ Gₙ`
   given; Property 1 uses `A`, `B` in `G₁ − G₂`, `G₁₁ − G₁₀`.
2. **T4.** `ε₁` with `ε₁`-neighbourhoods of `k⁻¹[[(i−1)/11, i/11]]` following `h[E]` for every
   `ε₁`-homeomorphism `h`: uniform continuity of `k⁻¹` on the decomposition space (Lemma 5 gives the
   continuity of the decomposition; the eleven pieces are compact).
3. **T5, Property 1** (p. 346): the sets `Wₓ = {y ∈ M : an ε₁-homeomorphism takes x to y}` (open,
   Lemma 2) and `Gₓ` with `Wₓ = M ∩ Gₓ`; the chain `Gᵢ`; the ordered free refinement `L` (generalized
   Lemma 8); Property 1 itself (each component of `M ∩ St L` meeting `L₆` is an `ε₁`-image of a
   subcontinuum of `E` …). Read p. 346 lines 1–25.
4. **T6–T7** need Lemma 9's proof; decide first on arc straightening versus a side form of
   `AbutSameSide` (item F above).
5. **T8**: the Jordan curve theorem (`jordan_curve_theorem`) for `I₂ ∪ (p₁, p₅) ∪ (p₁, r) ∪ (p₅, s)`;
   needs the four arcs to form a simple closed curve (`TArc.union`).
6. **T9**: components of `M ∩ π⁻¹[D]` meeting `L₄–L₈`; Lemma 1, Property 1, Lemma 5.
7. **T11**: `K` separates `π⁻¹[D]`; Theorem 28 (proved) and Property 1.
8. **T14, Property 3**: Lemmas 1–3 and Property 1.
In parallel, Lemma 6 (steps 1–8 of report 157 §1.C, step 5 first) remains the gateway to T10,
T12, T13, T16, T17.
