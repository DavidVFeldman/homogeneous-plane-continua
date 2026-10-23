Commission read: `doc/batches/COMMISSION-batch157.md` (batch 157 — Part E, Hagopian 1976 II: the first paragraph of Lemma 4, Lemmas 5–7, the set-up of Theorem 1).

# Report, batch 157

**Status.**
* **Proved:**
  * item E in full: `no_proper_subcontinuum_separates`, `layerSetoid_mooreDecomp`,
    `exists_quotient_plane`, `exists_accessible_typeA'`;
  * item B.1: `hagopian76_lemma5_interior` (the proposed route checks), together with
    `hagopian76_lemma5_usc` and the reduction `hagopian76_lemma5_of_ends` (Lemma 5 holds as soon as
    the decomposition is lower semicontinuous at the end sets);
  * item A, the bookkeeping: `hagopian76_lemma4_layers` (re-rendered) and
    `hagopian76_no_swallowed_layer` are equivalent without homogeneity
    (`hagopian76_lemma4_layers_of_no_swallowed`, `hagopian76_no_swallowed_of_lemma4_layers`).
* **Open** (commented out with `OPEN (batch 157)` notes, no `sorry`; obstructions in `OPEN.md`,
  batch-157 section):
  * A. D1 itself (`hagopian76_lemma4_layers`, `hagopian76_no_swallowed_layer`);
  * B.2 `hagopian76_two_sided_extension`; B.3 `hagopian76_lemma5` (only the end sets remain);
  * C. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
    `hagopian76_essential_typeA'`;
  * D. `hagopian76_lemma7`.
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76B` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (§3).

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76B.lean` | the skeleton items; open items commented out with `OPEN (batch 157)` notes |
| `H76BDefs.lean` | the skeleton's definitions `layerKey`, `layerSetoid`, `IsAccessibleFrom`, verbatim |
| `H76SepInv.lean` | item E: `no_log_of_separates`, `exists_log_of_isTreeLike` (with `LogData`, `branchAt`, `log_mul_near_one`), `exists_separating_subcontinuum_of_homeomorph` |
| `H76NoSep.lean` | item E: `separating_in_copy`, `no_proper_subcontinuum_separates_aux` |
| `H76D1.lean` | item A: `lemma4_layers_of_no_swallowed`, `no_swallowed_of_lemma4_layers`, `layer_param_eq`, `layer_nonempty`, `IsMinimalAdmissible.isCompact` |
| `H76Lemma5.lean` | item B.1: `lemma5_interior_aux`, `isUSCDecomp_ker`, `lemma5_of_ends_aux` |
| `H76Setup.lean` | item E: the elements of `S`, `layer_usc`, `layerSetoid_mooreDecomp_aux`, `exists_quotient_plane_aux`, `exists_accessible_point`, `exists_accessible_typeA'_aux` |

**Statements and shape changes.** Compared with `doc/batches/skeletons/Hagopian76B.lean`:
* `layerKey`, `layerSetoid`, `IsAccessibleFrom` moved, verbatim, to `H76BDefs.lean`, so that the
  supporting files can use them.
* `exists_accessible_typeA'`: the hypothesis `hi` is dropped (only homogeneity is used).
* New, proved, not in the skeleton: `hagopian76_lemma4_layers_of_no_swallowed`,
  `hagopian76_no_swallowed_of_lemma4_layers` (item A's "confirm this"), `hagopian76_lemma5_usc`,
  `hagopian76_lemma5_of_ends` (item B.3's fallback: what remains of Lemma 5 is exactly lower
  semicontinuity at the end sets). The last three carry `omit [CompactSpace M] [ConnectedSpace M]`
  where those instances are unused.
* The open statements are commented out verbatim.

All other statements are verbatim.

**Housekeeping.**
* `REPORT-batch155.md` at the root was byte-identical to `doc/batches/REPORT-batch155.md` and is
  deleted. `REPORT-batch156.md` at the root was likewise byte-identical to its copy in
  `doc/batches/` and is deleted.
* `theorems-3-4-scheduling(1).md` and `(2).md` are moved to `doc/notes/`; so is `(3).md`, which was
  also at the root.
* The commission is `doc/batches/COMMISSION-batch157.md`, the skeleton
  `doc/batches/skeletons/Hagopian76B.lean`, the sources `doc/sources/mazurkiewicz1929.pdf` and
  `doc/sources/bing1960.pdf`. Nothing new is at the root.
* `Hagopian76A.lean`: the commented-out `hagopian76_lemma4_layers` is replaced by a one-line pointer.
  No other commented-out copy there is deleted, since none of those items is proved here.
* `Axioms.lean` has the new group "Hagopian 1976 §2 continued (batch 157)" (9 skeleton theorems, 35
  supporting theorems); `axioms.txt` is regenerated (1383 lines, previously 1339) with `sorryAx` in
  no line; the previous version is kept as `doc/batches/audits/axioms-before-batch157.txt`; the
  per-theorem audit is `doc/batches/audits/axioms-batch157.txt` (44 theorems).
* `README.md`, `LEDGER.md` §6 and `OPEN.md` (a batch-157 section) are updated.

## 1. The items

### A. D1

*Bookkeeping, proved.* `hagopian76_lemma4_layers` (re-rendered) and `hagopian76_no_swallowed_layer`
are equivalent given `lemma4_layers_aux`, without homogeneity:
* (⇐) `lemma4_layers_of_no_swallowed`. From `lemma4_layers_aux`: `s`, `d⁻¹[0, s) ⊆ E ⊆ d⁻¹[0, s]`,
  every `k`-layer in a `d`-layer, and `k`-layers in `d⁻¹(u)`, `u < s`, equal to `d⁻¹(u)`. The step
  supplied: **`k⁻¹(1) ⊆ d⁻¹(s)`**. Otherwise `k⁻¹(1) ⊆ d⁻¹(u)` with `u < s`, so `k⁻¹(1) = d⁻¹(u)`, and
  `d⁻¹[[0, u]]` is a subcontinuum of `E` meeting `X = d⁻¹(0)` and `Z`, hence equal to `E` (end sets),
  which contradicts `d⁻¹((u, s)) ⊆ E` being nonempty. Then `d⁻¹(s) ∩ E ⊇ Z` is nonempty, and a layer
  `k⁻¹(t)`, `t < 1`, that is not a `d`-layer lies in `d⁻¹(s)`, which meets `k⁻¹(1)`: the swallowed
  configuration.
* (⇒) `no_swallowed_of_lemma4_layers`. If `k⁻¹(t) = d⁻¹(u′)` and `k⁻¹(t) ⊆ d⁻¹(u)`, then `u′ = u`, and
  `k⁻¹(1) ∩ d⁻¹(u) ≠ ∅` would make `k⁻¹(1)` meet `k⁻¹(t)`.

*D1 itself: open.* I followed the commission's direction. Let `d⁻¹(s) ∩ E = k⁻¹[[t₀, 1]]`, `t₀ < 1`,
and `x ∈ k⁻¹(c)`, `t₀ < c < 1`. Since `k⁻¹((t₀, 1))` is open in `E` and lies in `d⁻¹(s)`, which has void
interior in `F`, points of `F ∖ d⁻¹(s)`, necessarily in `d⁻¹((s, 1])`, accumulate at `x`. Lemma 2 gives
small `h` with `h(x) ∈ d⁻¹(u)`, `u > s`, and Lemma 3 (`E`, `Y = k⁻¹(c)`; `F`, `U = d⁻¹(u)`) gives
`h[k⁻¹(c)] = d⁻¹(u)` when `d⁻¹(u)` misses `h[X ∪ Z]`; by the same lemma `h` carries `k⁻¹(c′)` onto
layers `d⁻¹(u(c′))` for `c′` near `c`. This shows only that `F` beyond `d⁻¹(s)` is locally a
homeomorphic copy of `E` near `k⁻¹(c)`. As `u ↓ s` the hypothesis `d⁻¹(u) ∩ h[Z] = ∅` can fail
(`Z ⊆ d⁻¹(s)`), and I found no triod and no contradiction with the irreducibility of `F` between
`d⁻¹(s)` and `d⁻¹(1)`. The half-bar model shows that homogeneity must enter beyond what was tried.
**What is missing:** a homogeneity argument that excludes a nowhere dense layer of `F` containing a
subset of `E` with interior in `E`.

### B. Lemma 5

1. **`hagopian76_lemma5_interior`: proved; the route checks.** In neighbourhood form
   (`lemma5_interior_aux`): fix `y ∈ Y = k⁻¹(c)`, `0 < c < 1`, and open `V ∋ y` with `ball y η ⊆ V`. Choose
   `γ` with `[c − γ, c + γ] ⊂ (0, 1)`, `δ₀ = ρ(k⁻¹[[c − γ, c + γ]], X ∪ Z) > 0`, `ε < min(η, δ₀)`. Let `W`
   be the set of `z` with `k z ∈ (c − γ, c + γ)` that are images `h(y′)`, `y′ ∈ Y`, under
   `ε`-homeomorphisms; `W ⊇ Y` is open by Lemma 2. For `z = h(y′) ∈ W`, Lemma 3 with `F := E`,
   `T = X`, `V = Z`, `U = k⁻¹(k z)` applies (`h[Y] ∩ (X ∪ Z) = ∅` and `U ∩ h[X ∪ Z] = ∅` since `h` moves
   points less than `δ₀`), so `h[Y] = k⁻¹(k z)` and `h(y) ∈ k⁻¹(k z) ∩ ball y η`. Neither D1 nor
   Hagopian's `F` is used. Upper semicontinuity (`hagopian76_lemma5_usc`) is the closed-map argument
   for `k`.
2. **`hagopian76_two_sided_extension`: open.** Lemma 4 gives `F₁` (away from `X`) and `F₂` (away from
   `Z`). The natural argument for `F₁ ∪ F₂` (irreducibility between far points, then Kuratowski's
   criterion `hagopian75_lemma2` and the 1975 ¶2 argument, as in `ext_of_branch`) needs the tails
   `C₁ = d₁⁻¹[[s₁, 1]]`, `C₂ = d₂⁻¹[[s₂, 1]]` to meet `E` only in `Z` and `X`, so that `F₁ ∩ F₂ = E`.
   That is D1 for `F₁` at `Z` and for `F₂` at `X`. Without it the tails can overlap inside `E` (in
   `k⁻¹[[t₁, t₂]]`), and I found no type A′ structure on `F₁ ∪ F₂` in that case.
3. **`hagopian76_lemma5`: open at the end sets only.** Hagopian's route needs `Yᵢ ∈ B` (condition
   (2)) for layers `Yᵢ` of `E` near `X`, i.e. D1 at `X` for an extension away from `Z`
   (`lemma4_layers_aux` gives it unless those layers are swallowed). Lemma 3 with `F := E` is not
   available at `X`, since `h[X] ∩ X = ∅` fails for `h` near the identity. **Where continuity at the
   end sets is needed** (the later uses):
   * Lemma 6: the p. 342 remark ("the decomposition of `F` is a continuous collection (Lemma 5)") is
     about every extension `F`. In steps 1–8 I found its essential use only in step 6, and there the
     subcollection half (D1) is what matters (§1.C).
   * "Every continuum essential to `R(E)` is of type A′ (Lemma 5)": needs the essential continuum to
     contain the whole layers at its two ends. That is lower semicontinuity of the extension's
     decomposition at those layers, which can be end sets of the extension. So this needs continuity
     at the end sets (of extensions), or an argument that essential continua avoid them.
   * Lemma 7: uses the type A′ structure of essential continua (previous point) and Lemma 6.
   * Theorem 1, p. 346, "it follows from Property 1 and Lemma 5 that `Cl B` is the image of a
     subcontinuum of `E`": `B` meets `L₄, …, L₈` and `Cl B` is matched with `h[k⁻¹[[a, b]]]`, where
     `a`, `b` lie in `[2/11, 9/11]` (the chain links `L₂`–`L₁₀` follow interior layers). As far as
     checked, **interior continuity (`hagopian76_lemma5_interior`) suffices here**.
   * Theorem 1, p. 347, "it follows from Lemma 5 that `h` maps a subcontinuum of `E` that is
     essential to `R(E)` onto `Cl C`": same as the previous point (interior layers), with the
     essential-continuum claim.

### C. Lemma 6 and the unnumbered claims: open

Steps 1–8 (batch-156 commission §2 F) were worked through. Details are in the ledger, batch 157,
check 4.
* Steps 1, 2: Lemma 1 and the irreducibility of `E` and its extensions.
* Step 3: Lemmas 1 and 4 (the linear order).
* Step 4: `hagopian76_lemma4_seq`, proved in batch 156.
* Step 5: Lemma 2, Lemma 1, irreducibility.
* Step 7: Lemma 1, given step 6.
* Step 8: the 1975 ¶2 triod.
* **Step 6 uses D1.** `ε₁` is chosen so that no `ε₁`-neighbourhood of a layer of `K` contains `K`.
  The argument needs that a layer `Y` of `N ⊇ K` with `h₁⁻¹[Y] ⊇ N` is controlled by `ε₁`, i.e. that
  the layers of `N` meeting `K` are layers of `K`. That is the p. 342 remark "has the decomposition of
  `E` as a subcollection", i.e. D1 for `K ⊆ N`. A layer of `N` swallowing an interval of layers of
  `K` would contain a set with interior in `K` and is not excluded by the choice of `ε₁`. **This is
  the place the commission predicted.**
* `hagopian76_Rset_composant` uses Lemma 6.
* `hagopian76_essential_typeA'` needs the containment of the essential continuum in one extension
  (unargued: `R(X, E)` is an increasing union of closed sets) and continuity at the layers it ends
  in (item B.3).

None of steps 1–8 was formalized: each formal statement would sit on top of step 6.

### D. Lemma 7: open

It uses Lemma 5, through the type A′ decompositions of the essential continua `Hᵢ` and `F` (end sets
`Tᵢ`, `Vᵢ`, the layer `Uᵢ`), and Lemma 6, through the limit points `t`, `u`, `p` in the indecomposable
`Cl R(E)` and the essential continuum `F` of `fhᵢ[R(E)]` through `u` given by "Lemma 2". The triod
`g[F] ∪ Hⱼ` needs the type A′ structure of `Hⱼ`. Blocked by items B and C.

### E. The set-up of Theorem 1: proved

* **`no_proper_subcontinuum_separates`.** I extracted Hagopian 1975 Lemma 1, second paragraph, from
  `H75Lemma1.lean`, but it cannot be used verbatim: it applies to copies `h[K]` of a non-unicoherent
  `K`, which separate the plane because non-unicoherence is intrinsic. For a separating `K`, "each
  copy separates" is the topological invariance of plane separation (Borsuk), which neither paper
  states. It is replaced by a weaker statement that suffices:
  **`exists_separating_subcontinuum_of_homeomorph`**: a plane continuum homeomorphic to a separating
  compactum contains a separating subcontinuum. The proof uses no Borsuk or Brouwer:
  1. `no_log_of_separates`: if `K` separates, `z − p` has no continuous logarithm on `K` for `p` in a
     bounded complementary component. A logarithm on `K` would extend, by Tietze plus a
     principal-branch correction, to a neighbourhood `W`, and a polygon in `W` around `p` carries
     none (`no_log_on_polygon`, batch 133).
  2. `exists_log_of_isTreeLike`: every continuous nonvanishing function on a tree-like continuum has
     a continuous logarithm. Local branches `log(f z / f a) + log(f a)` are glued leaf by leaf along a
     fine tree chain, as in `exists_log_inv` (batch 133). The overlap constants come from
     `log(uv) = log u + log v` for `u`, `v` near `1`.
  3. If no subcontinuum of `K′ ≅ K` separates, `K′` is tree-like (Bing 1951 Theorem 6,
     `theorem6_1951`), so `g⁻¹(z) − p` has a logarithm on `K′`, and pulling it back gives one of
     `z − p` on `K`.

  The 1975 argument then runs with these separating continua in place of the copies:
  disjointness across composants, separability, Baire, and density of composants
  (`no_proper_subcontinuum_separates_aux`).
* **`layerSetoid_mooreDecomp`.** The elements of `S` are the layers of `E` and the points off `E`
  (`elt_layerSetoid_of_mem`, `elt_layerSetoid_of_notMem`). The layers are compact, connected, and
  proper (their interior in `E` is void), so they do not separate; points do not separate either.
  Moore's u.s.c. is `layer_usc`: `k` is a closed map on the compact `E`, and off a neighbourhood of
  `k⁻¹(t)` the distance to `k⁻¹(t)` has a positive minimum. Lemma 5 is not used.
* **`exists_quotient_plane`.** `π` is `Quotient.mk` followed by the homeomorphism of Moore 1925
  Theorem 22 (`m25_theorem22`). `t ↦ π(k⁻¹(t))` is continuous (`k` is a quotient map, being closed)
  and injective on the compact `[0, 1]`, with image `π[E]`, so `π[E] ≅ [0, 1]`.
* **`exists_accessible_typeA'`.** A point `p ∈ M` nearest to a point `x ∉ M` is accessible: the
  segment `[x, p]` meets `M` only in `p`, since its other points are closer to `x` than
  `infDist x M`. A homeomorphism `h` of `M` takes a point of `k⁻¹(1/2)` to `p`, and `h[E]` carries the
  transported minimal admissible map (`exists_image_map`, batch 156). The skeleton's `E′ = h '' E`
  is used as is.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 II … (batch 157)", checks 1–9. In summary:

| check | place | outcome |
|---|---|---|
| 1 | p. 341, D1 | reason insufficient; equivalent to no swallowed layer (proved); truth open |
| 2 | p. 341, Lemma 5: `F`; "each element of `A` … is an element of `B`"; (1)–(3); "`h[U] = Yᵢ`" | union of type A′ unargued, open (D1); first sentence true; second is D1; away from the end sets the step is proved by another route |
| 3 | p. 342, "continuous collection … subcollection" | Lemma 5 + D1; open |
| 4 | pp. 342–343, Lemma 6 steps 1–8 | steps 1–5, 7, 8 true as far as checked; step 6 needs D1 |
| 5 | p. 343, the two unnumbered claims | depend on Lemma 6 / Lemma 5 (end sets) and an unargued containment; open |
| 6 | pp. 343–344, Lemma 7, the two quoted sentences | unargued details; depend on Lemmas 5, 6; open |
| 7 | p. 344, "no proper subcontinuum … separates `R²` [5]"; "we can assume `R²/S` is `R²` [12]" | invariance step unstated, supplied without Borsuk; `π` is a quotient map, not a homeomorphism; proved |
| 8 | p. 345, "we can assume … `k⁻¹[(0, 1)]` is accessible" | weak reading proved; the "each point of `π[E]` … below `π[E]` (Lemma 9)" reading is stronger and is for batch 158 |
| 9 | p. 347, "`d⁻¹[[0, e]] = E`" (new) | the strong form, more than D1; open |

## 3. Axioms

`doc/batches/audits/axioms-batch157.txt` lists `#print axioms` for all 44 new theorems. Every line is
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` appears in none. `axioms.txt` is regenerated
with the group "Hagopian 1976 §2 continued (batch 157)", and `sorryAx` appears in no line.

| theorem | axioms |
|---|---|
| `hagopian76_lemma4_layers_of_no_swallowed`, `hagopian76_no_swallowed_of_lemma4_layers` | standard three |
| `hagopian76_lemma5_interior`, `hagopian76_lemma5_usc`, `hagopian76_lemma5_of_ends` | standard three |
| `no_proper_subcontinuum_separates`, `layerSetoid_mooreDecomp`, `exists_quotient_plane`, `exists_accessible_typeA'` | standard three |
| the 35 supporting theorems (`H76SepInv`, `H76NoSep`, `H76D1`, `H76Lemma5`, `H76Setup`) | standard three |

## 4. Dependency map of Theorem 1 (pp. 345–349)

Legend: **[D1]** needs D1 (or its strong form); **[L5e]** needs Lemma 5 at end sets (through Lemma 5
in full, Lemma 6, Lemma 7 or the essential-continuum claim); **[ok]** needs neither.

| step (page) | content | uses |
|---|---|---|
| T0 (345) | a type A′ `E ⊆ M` ([5, Thm 1 ¶1–3]) | Lemma 1; `hagopian75_exists_typeA'` (batch 155) **[ok]** |
| T1 (345) | WLOG `k⁻¹((0, 1))` accessible | homogeneity; `exists_accessible_typeA'` (proved) **[ok]** |
| T2 (345) | `S`, `π`, `R²/S ≅ R²`, the arc `π[E]` | no separation (proved), Moore 1925 Thm 22; `layerSetoid_mooreDecomp`, `exists_quotient_plane` (proved) **[ok]** |
| T3 (345) | each point of `π[E]` is an end point of an arc segment in `R² − π[M]` below `π[E]` | Lemma 9 (Lemma 2, Lemma 8, Moore 1962 Thm 28); ledger check 8 (side coherence) **[ok]** |
| T4 (345–346) | `ε₁`; `ε₁`-neighbourhoods of `k⁻¹[[(i−1)/11, i/11]]` follow `h[E]` | continuity of `k`, compactness **[ok]** |
| T5 (346) | `Wₓ`, `Gₓ`, `Gᵢ`; ordered free refinement `L`; **Property 1** | Lemma 2; the method of Lemma 8 (with `A`, `B` prescribed in `G₁ − G₂`, `G₁₁ − G₁₀`); Lemma 1 **[ok]** |
| T6 (346) | `I₁` below `(p₁, p₅)` in `R² − π[M]` | proof of Lemma 9 **[ok]** |
| T7 (346) | `I₂` above, irreducible between `(p₁, q₁)`, `(p₅, q₅)`, region between in `π[St L]` | Property 1, Lemma 9 (proof), an accessible point of `M ∩ L₆` above `π[E]` (homogeneity), Lemma 2 **[ok]** |
| T8 (346) | `D`, the bounded domain of `I₂ ∪ (p₁, p₅) ∪ (p₁, r) ∪ (p₅, s)` | Jordan curve theorem (Moore 1919 / F.A., in the repository) **[ok]** |
| T9 (346) | components `B` of `M ∩ π⁻¹[D]` meeting `L₄–L₈`: `Cl B` is an `ε₁`-image of a subcontinuum of `E` essential to `R(E)`; `L − {L₁, L₁₁}` follows `Cl B` | Lemma 1, Property 1, Lemma 5 (interior layers suffice, as far as checked) **[ok]**; "essential" invokes the essential-continuum claim only by name |
| T10 (346) | `ε₂`, `ε₃`; **Property 2** | Lemma 7 **[L5e][D1]** |
| T11 (347) | `K`, the component of `π⁻¹[D ∩ (p₃, q₃)]`; `K` separates in `π⁻¹[D]` | plane topology (Moore 1962 Thm 28 type), Property 1 **[ok]** |
| T12 (347) | `p ∈ K`, `f = h₁h⁻¹`, `h`, `h₁` with (1)–(3) | Lemma 2; Lemma 6 (`Cl R(E)` indecomposable) and **Mazurkiewicz 1929** (distinct inaccessible composants); Lemma 5 + atriodicity ("`h` maps a subcontinuum of `E` essential to `R(E)` onto `Cl C`"); Property 1 **[L5e][D1]** (through Lemma 6) |
| T13 (347) | `F` irreducible w.r.t. (1) extension away from `k⁻¹(0)`, (2) separates `p` from `f(p)` | Property 1; Lemma 6 (proof: `Cl R(E) = Cl R(k⁻¹(0), E)`); Lemma 4 (linear order) **[L5e][D1]** |
| T14 (347) | **Property 3** (no component of `F ∩ π⁻¹[D]` crossing `D` lies in one layer of `F`) | Lemma 1, Property 1, Lemmas 2 and 3 **[ok]** (Lemma 3 as proved) |
| T15 (347–348) | `I` finite; `e` with `d⁻¹[[0, e]] = E`; `J`, `xᵢ` | Property 3, compactness; **`d⁻¹[[0, e]] = E` is the strong form of D1 (ledger check 9)** **[D1]** |
| T16 (348) | **Property 4** for `[x₂ₙ₋₁, x₂ₙ]`; not for `[x₁, x₂]` | Property 2 / Lemma 7, `f` near the identity **[L5e][D1]** |
| T17 (348–349) | the induction (Bing 1960 p. 225), Cases 1 and 2: `Cᵢ₋₁`, the shortest extension `L`, the essential `N`, the continuum `P` | Lemma 6 (proof: indecomposability of `Cl R(X, Cl Cᵢ)`), Property 3, Lemma 4 (linear order), essential continua of type A′ (Lemma 5), Property 2 **[L5e][D1]** |

**How far D1 blocks Theorem 1.** T0–T9, T11 and T14 do not need D1 or end-set continuity:
the set-up, Lemma 9, Property 1, the curve `I₂ ∪ …` and the domain `D`, and Property 3. They are the
work of batches 158–159. Everything from Property 2 onward (T10, T12, T13, T15–T17) needs D1. It
does so directly at T15 (in the strong form) and through Lemma 6 (step 6) and Lemma 7 (essential
continua) elsewhere. So without D1 Theorem 1 can be advanced up to Properties 1 and 3, but not
completed.

## 5. Reading plan for batch 158: Lemma 9 and Property 1

**Bing 1960, p. 215** (`doc/sources/bing1960.pdf`, p. 7 of the file). The definition behind
"decomposably accessible from a side":

> Suppose ab, cd, and ef are arcs in E² such that ab·cd = c and ab·ef = e are interior points of ab.
> Then cd and ef are said to abut on opposite sides of ab if there is a homeomorphism of E² onto itself
> that takes ab onto a horizontal segment and cd, ef onto vertical segments which lie except for their
> points of contact with ab on opposite sides of the line containing ab.

"Abut on the same side" is the same with both vertical segments on one side. Hagopian's `A`, `B` are
arc segments (open arcs) in `R² − π[M]` with `π[U] ∈ Cl A`, `π[Y] ∈ Cl B`; so `Cl A`, `Cl B` are arcs
meeting the arc `π[E]` in one interior point each. **Proposed Lean shape:**

```lean
/-- `C₁`, `C₂` abut on the same side of the arc `α` (Bing 1960, p. 215): a homeomorphism of the plane
takes `α` onto a horizontal segment and `C₁`, `C₂` onto vertical segments lying, except for their
points of contact, in the open upper half-plane. -/
def AbutSameSide (α C₁ C₂ : Set Pt) : Prop :=
  ∃ (φ : Pt ≃ₜ Pt) (a b x₁ x₂ h₁ h₂ : ℝ), a < x₁ ∧ x₁ < b ∧ a < x₂ ∧ x₂ < b ∧ 0 < h₁ ∧ 0 < h₂ ∧
    φ '' α = Icc a b ×ˢ {0} ∧ φ '' C₁ = {x₁} ×ˢ Icc 0 h₁ ∧ φ '' C₂ = {x₂} ×ˢ Icc 0 h₂

/-- **Decomposably accessible from a side** (p. 344), with `γ : unitInterval → Pt` the arc
parametrization `t ↦ π(k⁻¹(t))` of `exists_quotient_plane`: arc segments `A`, `B` in `R² − π[M]` whose
closures are arcs ending at `γ u`, `γ y` and abutting on the same side of `π[E]`. -/
def DecompAccessible (πM : Set Pt) (γ : unitInterval → Pt) (u y : unitInterval) : Prop :=
  0 < u ∧ u < 1 ∧ 0 < y ∧ y < 1 ∧ u ≠ y ∧
    ∃ (A B : Set Pt) (a₀ b₀ : Pt), TArc a₀ (γ u) (closure A) ∧ TArc b₀ (γ y) (closure B) ∧
      A = closure A \ {γ u} ∧ B = closure B \ {γ y} ∧ Disjoint A πM ∧ Disjoint B πM ∧
      AbutSameSide (range γ) (closure A) (closure B)
```

Stating it with `γ` avoids `π '' toPt (layer k u)`, which is a single point. A strengthened
`exists_quotient_plane` that returns `γ` with `range γ = π[E]` and `γ t = π(k⁻¹(t))` is worth adding
first (the proof already constructs it).

**Lemma 9's proof** needs:
* Lemma 8 in a form with prescribed `A`, `B` (for Property 1 as well);
* a chain `G` of three links following `E` with `π[G₁]`, `π[G₁] ∩ π[G₂]`, … open disks (Moore 1925's
  quotient makes images of saturated open sets open);
* Lemma 2;
* **Moore 1962 Theorem 28, p. 156** (`doc/sources/moore1962-excerpts.pdf`). It is the separation
  statement that turns "`πh[D]` contains `πh(u)`, meets `π[G₃]` and misses `π[C ∪ I ∪ Cl G₁]`" into a
  contradiction with freeness. Read it and state it as a plane-topology lemma first.

**Property 1** needs only Lemma 2 (the sets `Wₓ`, `Gₓ` with `Wₓ = M ∩ Gₓ`), the chain of
`ε₁`-neighbourhoods (T4), and the method of Lemma 8. Suggested order: Moore 1962 Thm 28 → the
generalized Lemma 8 → Property 1 → `AbutSameSide` and Lemma 9.
