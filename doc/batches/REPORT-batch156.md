Commission read: `doc/batches/COMMISSION-batch156.md` (batch 156 — Part E, Hagopian 1976 I: §2, Lemmas 2–8; the consequences of Theorem 1).

# Report, batch 156

**Status.**
* **Proved:**
  * items A, B, C (Lemma 3 as printed), H (Lemma 8) and I (all five consequences of
    `Hagopian76Thm1`);
  * from item D, the linear order of Lemma 4, the first paragraph in corrected form, and the
    sequence form given "no maximal element";
  * from item D (continuation), the second half of Hagopian's "no maximal element" step: given a
    continuum `F″` with `∅ ≠ F″ ∩ F ⊆ d⁻¹(1)` and `F″ ⊄ F`, a proper extension exists
    (`ext_of_branch`). So Lemma 4 and its countable form hold as printed under that hypothesis
    (`hagopian76_lemma4_of_branch`, `hagopian76_lemma4_seq_of_branch`). See §5.
  * from item D (continuation), the first half as well: such an extension always exists
    (`exists_proper_extension`). So **Lemma 4 and `hagopian76_lemma4_seq` are proved as printed**
    (`hagopian76_lemma4`, `hagopian76_lemma4_seq`), with the step Hagopian leaves unargued supplied.
    See §5.
* **Open** (commented out, no `sorry`; obstructions in `OPEN.md`, batch-156 section):
  * the first paragraph of Lemma 4 as printed (D1);
  * Lemma 5 (E);
  * Lemma 6 and the two unnumbered claims (F);
  * Lemma 7 (G).
* **Refuted:** nothing.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76A` at the end of `HPC.lean`. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian76A.lean` | the skeleton items; open items commented out with `OPEN (batch 156)` notes |
| `H76Defs.lean` | the skeleton's definitions (item A) and `Hagopian76Thm1`, verbatim |
| `H76Lemma2.lean` | item B: `lemma2_aux`, `end_sets_aux` |
| `H76Lemma3.lean` | item C: `subset_of_meets_avoids`, `lemma3_end_case`, `lemma3_half`, `lemma3_aux` |
| `H76Lemma4.lean` | item D: `ext_chain` (the triod), `exists_strictMono_seq_of_chain` (countable form) |
| `H76Lemma4Layers.lean` | item D: `lemma4_layers_aux` (first paragraph, corrected) |
| `H76Lemma4Ext.lean` | item D (continuation): `ext_of_branch`, `lemma4_of_branch`, `lemma4_seq_of_branch` |
| `H76NoMaxBasic.lean` | item D (continuation): `tail_subset`, `false_of_layer_open`, `three_continua`, `exists_image_map`, `ext_of_irreducible_union`, `layer_one_subset_closure` |
| `H76NoMaxCases.lean` | item D (continuation): `not_subset_layer_of_open`, `ext_of_subset`, `ext_of_side` |
| `H76NoMax.lean` | item D (continuation): `exists_proper_extension` (no maximal element), `lemma4_aux`, `lemma4_seq_aux` |
| `H76Lemma8.lean` | item H: `connected_meets_links`, `component_of_caps`, `lemma8_aux` |
| `H76Cons.lean` | item I: Theorem 2, the 1975 Corollary, Theorems 1 and 2, Bing 1960 for the plane |

**Statements and shape changes.** Compared with `doc/batches/skeletons/Hagopian76A.lean`, the
following changed. Each change is recorded at the statement.
* The definitions and `Hagopian76Thm1` moved, verbatim, to `H76Defs.lean`, so that the supporting
  files can use them.
* `hagopian76_lemma3`: `hu0 : 0 < u` and `hu1 : u < 1` are dropped. They are not used: `U` meets
  `h[Y]`, which misses `T ∪ V`, so `U` is neither end set.
* `hagopian76_lemma4_layers`, as printed, is commented out (open, D1). The new
  `hagopian76_lemma4_layers'` is the corrected form, proved without `hX`, `hi`. It has
  `d⁻¹[0, s) ⊆ E ⊆ d⁻¹[0, s]` in place of `layerSet d (Icc 0 s) = E`. In place of "`∀ t ≠ 1, ∃ u,
  k⁻¹(t) = d⁻¹(u)`" it has two clauses: every `k`-layer lies in a `d`-layer, and a `k`-layer
  inside `d⁻¹(u)` with `u < s` equals `d⁻¹(u)`.
* `hagopian76_lemma4` and `hagopian76_lemma4_seq` are proved with the skeleton's statements
  (continuation, §5). The first half of Lemma 4 is also stated separately as
  `hagopian76_lemma4_chain`, and `hagopian76_lemma4_seq_of_noMax` (the sequence form with "no
  maximal element" as a hypothesis) is kept.
* `hagopian76_lemma5`, `hagopian76_closure_extUnion`, `hagopian76_lemma6`,
  `hagopian76_Rset_composant`, `hagopian76_essential_typeA'` and `hagopian76_lemma7` are commented
  out (open).
* `hagopian76_lemma2`, `hagopian76_end_sets` and `hagopian76_lemma4_layers'` carry
  `omit [ConnectedSpace M]` (and `[CompactSpace M]` for the last two). This is a generalization:
  those instances are not used.

All other statements are verbatim.

**Housekeeping.**
* The commission is `doc/batches/COMMISSION-batch156.md`, the skeleton
  `doc/batches/skeletons/Hagopian76A.lean`, the source `doc/sources/hagopian1976.pdf`.
* `Axioms.lean` has the new group "Hagopian 1976 §2 (batch 156)", with 12 skeleton theorems and 19
  supporting theorems. `axioms.txt` is regenerated (1317 lines, previously 1286), with `sorryAx` in no line. The previous version
  is kept as `doc/batches/audits/axioms-before-batch156.txt`.
* The per-theorem audit is `doc/batches/audits/axioms-batch156.txt` (33 theorems).
* `README.md`, `LEDGER.md` §6 and `OPEN.md` (a batch-156 section) are updated.
* The root still holds `REPORT-batch155.md` and `theorems-3-4-scheduling(1).md`, `(2).md`. They come
  from before this batch, and the rules allow no edits to existing files, so they were left alone.

## 1. The items

**A. Definitions.** These are verbatim from the skeleton. The end set of an extension is
normalized to the layer over `0`.

Lemma 7 reads "essential to `h[R(E)]`" as "`h⁻¹[H]` essential to `R(E)`". This loses nothing. A
homeomorphism `h` of `M` carries type A′ continua, with their minimal decompositions (by
uniqueness, `hagopian75_lemma3_unique`), to type A′ continua. So it carries the extensions of `E`
away from `X` to the extensions of `h[E]` away from `h[X]`. Hence `H` is essential to `R(h[E]) =
h[R(E)]` iff `h⁻¹[H]` is essential to `R(E)`.

**B. Proved.**
* `hagopian76_lemma2`: if `h` is an `ε`-homeomorphism with `h x = y`, its displacement attains a
  maximum `m < ε`. By `hagopian75_lemma4` (Effros), every `y′` near `y` is `g(y)` for an
  `(ε − m)`-homeomorphism `g`. Then `g ∘ h` is an `ε`-homeomorphism taking `x` to `y′`.
* `hagopian76_end_sets` is `admissible_end_sets'`.

**C. Proved; Lemma 3 holds as printed, and the 1975 argument goes through.**
* The hypothesis `h[Y] ∩ (T ∪ V) = ∅` replaces `ε`. By the 1975 ¶9 triod (`subset_of_meets_avoids`:
  a continuum meeting `F` and missing `T ∪ V` lies in `F`), it puts `h[Y]` in `F`.
* With `J = F ∩ h[E]` (a continuum) and `[γ, δ] = k(h⁻¹[J])`, there are two cases:
  * `γ = s` (or `δ = s`): the continuum `h k⁻¹[[0, s]]` (or `h k⁻¹[[s, 1]]`) meets `F` only in
    `h[Y]`. So it lies in `F`, and `h[X] ⊆ h[Y]` (or `h[Z] ⊆ h[Y]`), which is absurd
    (`lemma3_end_case`).
  * `γ < s < δ`: if `h[Y] ⊄ U`, then `h[Y]` contains an open subset of `F` (interval lemma). The ¶10
    neighbourhood argument then gives `Y` interior in `E` (`lemma3_half`).
* Applying this to `h⁻¹`, with `U ∩ h[X ∪ Z] = ∅`, gives the reverse inclusion (`lemma3_aux`).
* Lemma 3 is used in Lemma 5 and in Property 3 on p. 347. Both uses fit the printed hypotheses, so no
  corrected form is needed.

**D. Lemma 4.**
* *Linear order: proved* (`hagopian76_lemma4_chain`, from `ext_chain`). Suppose `F ⊄ H` and
  `H ⊄ F`, with maps `d`, `e`.
  * `J = F ∩ H` is a continuum containing `E`. It misses `d⁻¹(1)` and `e⁻¹(1)` (`eq_of_meets_ends`).
  * Take `z ∈ k⁻¹(1)`. Let `ρ` be the least value of `d` on `F ∩ e⁻¹[e(z), 1]`, let `r = ρ/2`, and
    let `σ` be the largest value of `d` on `J`.
  * Then `N = J ∩ d⁻¹[r, 1]` is the core of a triod with arms `d⁻¹[0, r]`, `d⁻¹[σ, 1]` and
    `e⁻¹[e(z), 1]` (`isTriod_of_core`), against atriodicity. This is Hagopian's "`H ∩ d⁻¹[[s, 1]]`
    would separate `F ∪ H` into three nonempty disjoint open sets".
  * The first paragraph of the proof is not needed.
* *First paragraph, corrected: proved* (`hagopian76_lemma4_layers'`, from `lemma4_layers_aux`).
  Let `s = max d|E`.
  * `d⁻¹(r) ⊆ E` for `r < s` (interval lemma), and `E ⊆ d⁻¹[0, s]`.
  * Each `k⁻¹(t)` lies in one `d`-layer. Otherwise it would contain an open subset `d⁻¹(α, β)` of
    `F` inside `E`, so it would have interior in `E`.
  * A `k`-layer inside `d⁻¹(u)` with `u < s` is all of `d⁻¹(u)`. Otherwise `d⁻¹(u)` would contain
    `k⁻¹(α, β)`, open in `E`, hence open in `F` because `d⁻¹[0, s)` is open in `F`.
* *First paragraph as printed: open* (`OPEN.md`, D1). The reason given ("Since the decompositions of
  `E` and `F` are minimal") does not yield `E = d⁻¹[0, s]` or "each element … (except possibly
  `k⁻¹(1)`) is an element of the decomposition of `F`". Plane configurations satisfying every
  hypothesis except homogeneity break both claims (two `sin (1/x)` rays approaching a common bar,
  one onto half of it), and the failures sit at `d⁻¹(s)`. Inside a homogeneous indecomposable `M`
  no refutation is possible, since Theorem 1 says no type A′ `E` exists.
* *"No maximal element": unargued in the text; supplied in the continuation* (§5; `OPEN.md`, D2,
  closed). "It is a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)"
  is unargued. The notes below are from the first pass.
  * The step would need a continuum `F″ ⊆ h⁻¹[F]` with `F″ ⊄ F` and `∅ ≠ F″ ∩ F ⊆ d⁻¹(1)`.
  * Given `F″`, the union `F ∪ F″` would be of type A′ by Kuratowski's criterion
    (`hagopian75_lemma2`) and the 1975 ¶2 argument.
  * Constructing `F″` from the `ε`-homeomorphism is not done in the text. The continuation does it,
    except in one configuration, which it handles separately (§5).
* *The sequence form.* `exists_strictMono_seq_of_chain` proves that a nonempty chain of closed sets
  with no largest element, in a second-countable space, has a strictly increasing cofinal sequence.
  * For each basic open set met by some member, choose such a member. These countably many members
    are cofinal. Otherwise all of them lie in a member `F`, and a larger member `G ⊋ F` has a point
    `x ∉ F` with a basic neighbourhood `B` missing `F`. But `B` is met by `G`, so the member chosen
    for `B` meets `B`, while lying in `F`: a contradiction.
  * A strictly increasing sequence dominating them is then built using "no maximal element".
  * This avoids the well-ordered-subchain argument of the commission. It gives
    `hagopian76_lemma4_seq_of_noMax` (proved); with §5 it gives `hagopian76_lemma4_seq`.

**E. Lemma 5: open** (`OPEN.md`, E).
* The type A′ continuum `F` "that is the union of two extensions of `E` such that the end sets … miss
  `E` (Lemma 4)" needs "no maximal element" (D2, now proved).
* That such a union is of type A′ is not argued.
* "Each element of `A` that is not an end set of `E` is an element of `B`" is the two-sided D1 claim.
  For layers strictly inside it follows by the argument of `hagopian76_lemma4_layers'`.
* The choice (1)–(3) of `h` (Lemma 2) and the use of Lemma 3 (proved) are routine once `F` exists.

**F. Lemma 6 and the two unnumbered claims: open** (`OPEN.md`, F).
* Steps 1–3 need only Lemma 1 and irreducibility. They were checked but not formalized.
* Step 4 uses the sequence `{Fᵢ}` (D2). The remaining steps use the continuity of the
  decompositions of extensions (Lemma 5).
* "`R(E)` is a composant of `Cl R(E)`" needs Lemma 6. "Every continuum essential to `R(E)` is of type
  A′" needs Lemma 5.

**G. Lemma 7: open** (`OPEN.md`, G). It depends on E and F.

**H. Lemma 8: proved** (`hagopian76_lemma8`, from `lemma8_aux`).
* `A = G₁ − E` and `B = Gₙ − E` (`component_of_caps`). If a continuum `K ⊋ E` of `M` missed
  `A ∪ B`, boundary bumping in `K` away from small neighbourhoods of `X` and `Z` would give a
  continuum through a point of `K − E` that meets `E` and misses `X ∪ Z`. That continuum lies in
  `E` by the ¶9 triod, which is absurd.
* Moore 1962 Theorem 44 (`exists_closed_split_of_no_connected`) and normality give `C` and `D`.
* `L₁ = G₁`, `Lₙ = Gₙ`, and `Lᵢ = C ∩ Gᵢ` otherwise.
  * `L` is a chain, since every overlap of `G` meets `E ⊆ C` (`connected_meets_links`).
  * `L` follows `E`, since every point of `E` in `Gⱼ` is in `Lⱼ`.
  * `L` is free: a point of `M ∩ Bd St L` is not in `A ∪ B`, so it lies in `C ∪ D`. It is not in
    `C`, since a point of `C` would lie in `St L` or outside `St G`. So it lies in `D`, hence in
    `Cl(L₁ ∪ Lₙ) − (L₁ ∪ Lₙ)`.
* *Small `n`.* With one link (`n = 0` in the 0-indexed Lean chain) or two links, `L = G`. `G` is then
  free by definition, since `St G = G₁ ∪ Gₙ`. The general argument covers these cases without
  change.

**I. Proved,** each from `h1 : Hagopian76Thm1`.
* `hagopian76_theorem2`: a decomposable homogeneous plane continuum has two complementary domains
  (`jones55_two_domains'`). So a nonseparating one is indecomposable, and `h1` applies. **Confirmed:
  Gordh 1975 and Jones 1951 are not needed.**
* `hagopian75_corollary`: by `h1`, every subcontinuum of `M` is indecomposable, and a nondegenerate
  hereditarily decomposable one would be decomposable.
* `hagopian75_theorem1`: by `h1`, the hypothesis "`A` decomposable" is impossible.
* `hagopian75_theorem2`:
  * If `M` is indecomposable, the Corollary applies.
  * If `M` is decomposable, Jones's decomposition (`jones55_theorem2'`) has indecomposable elements
    (`jones55_elements_indecomposable'`).
  * An element containing `H` contradicts `h1` applied to the element
    (`isIndecomposable_of_h1_sub`).
  * Otherwise, the element through a point of `H` lies in `H` (`jones55_c`), so it is both
    hereditarily decomposable and indecomposable, hence degenerate.
  * By homogeneity all elements are degenerate, and `M` is homeomorphic to the quotient circle.
* `bing60_plane`: an arc is hereditarily decomposable (`isHereditarilyDecomposable_of_arc`), so
  `hagopian75_theorem2` applies.

## 2. Ledger entries

`LEDGER.md` §6, "Hagopian 1976 I: §2, Lemmas 2–8; the consequences of Theorem 1 (batch 156)",
records the twelve checks of commission §3, each with the printed sentence quoted.

| # | place | outcome |
|---|---|---|
| 1 | p. 339, continuum and type A′ | definitions agree with 1975 |
| 2 | p. 340, end sets | true for the decomposition; fails for arbitrary admissible maps (`not_admissible_end_sets`) |
| 3 | p. 340, Lemma 3 | the 1975 argument adapts; true as printed |
| 4 | p. 341, Lemma 4 | first sentence: the reason given is insufficient, open; triod: true, supplied; "proper subset of an element … in `F ∪ h⁻¹[F]`": unargued, true, supplied (§5) |
| 5 | p. 341, Lemma 5 | depends on open steps; open |
| 6 | p. 342, the sequence | true given Lemma 4; argument supplied |
| 7 | pp. 342–343, Lemma 6 steps 1–8 | depends on Lemmas 4 and 5; open |
| 8 | p. 343, two unnumbered claims | depend on Lemmas 5 and 6; open |
| 9 | pp. 343–344, Lemma 7 | depends on Lemma 5; open; the reading of "essential to `h[R(E)]`" loses nothing |
| 10 | p. 344, Lemma 8 | unargued steps, true, supplied |
| 11 | p. 349, Theorem 2 | citations [4], [6] replaced by `jones55_two_domains'` |
| 12 | p. 339, abstract | is 1975 Theorem 2; proved from `Hagopian76Thm1` |

No defective proof is added while the open steps are unsettled. The counts stay at 21 false as
printed and 14 defective proofs.

## 3. Axioms

Each of the 33 new theorems depends on exactly `[propext, Classical.choice, Quot.sound]`
(`doc/batches/audits/axioms-batch156.txt`). The list:
* the skeleton theorems: `hagopian76_lemma2`, `hagopian76_end_sets`, `hagopian76_lemma3`,
  `hagopian76_lemma4_layers'`, `hagopian76_lemma4_chain`, `hagopian76_lemma4_seq_of_noMax`,
  `hagopian76_lemma8`, `hagopian76_theorem2`, `hagopian75_corollary`, `hagopian75_theorem1`,
  `hagopian75_theorem2`, `bing60_plane`;
* the supporting theorems: `lemma2_aux`, `end_sets_aux`, `subset_of_meets_avoids`,
  `lemma3_end_case`, `lemma3_half`, `lemma3_aux`, `ext_chain`, `exists_strictMono_seq_of_chain`,
  `lemma4_layers_aux`, `connected_meets_links`, `component_of_caps`, `toPt_mono`, `mem_toPt`,
  `lemma8_aux`, `isIndecomposable_of_h1_sub`, `hagopian76_theorem2_aux`, `hagopian75_corollary_aux`,
  `isDecomposableSpace_of_sub`, `hagopian75_theorem2_aux`, `isHereditarilyDecomposable_of_arc`,
  `bing60_plane_aux`.

The open statements are comments, not declarations, so `sorryAx` appears nowhere.

## 4. Reading plan for batch 157 (Lemma 9; Theorem 1 up to Property 1, pp. 344–346)

**A remark first.** Theorem 1's proof uses Lemmas 5, 7 and 8 (p. 346: "it follows from Property 1 and
Lemma 5", "By Lemma 7"). Lemma 9 uses only Lemmas 2 and 8, which are both proved. So batch 157 can
proceed on Lemma 9 and the set-up. Property 2 onwards (batch 158) needs Lemmas 5 and 7, which are
open. The D2 gap ("no maximal element") is now closed (§5); Lemma 5 still needs D1-type work.

1. **The relation `S` and `R²/S = R²`** (p. 344: "Since M is indecomposable and homogeneous, no
   proper subcontinuum of M separates R² [5, Lemma 1 (second paragraph of proof)]. Hence we can
   assume that the quotient space R²/S is R² [12].")
   * Take the setoid on `Pt` whose classes are the layers `k⁻¹(t)` (as subsets of `Pt`) and the
     singletons off `E`. Then check the four fields of `MooreDecomp`:
     * `compact`, `connected`: layers are continua (`isContinuum_layer`), singletons trivially.
     * `nonsep`: a layer is a proper subcontinuum of `M`. A standalone lemma "no proper subcontinuum
       of `M` separates `R²`" has to be extracted from the proof of
       `hereditarilyUnicoherent_of_homogeneous_indecomposable` (`H75Lemma1.lean`), which proves it
       inside a `by_contra`. The commission's reading of the citation is correct.
     * `usc`: Moore's form. It follows from the continuity of `k` and the compactness of `E`: if
       elements meet near `k⁻¹(t)`, their parameters are near `t`, and `k⁻¹[t − η, t + η]` lies
       in a small neighbourhood of `k⁻¹(t)`. Lemma 5 (continuity) is not needed, since upper
       semicontinuity suffices.
   * Then `m25_theorem22` gives `Quotient S ≃ₜ ℝ × ℝ`, and `π` is `Quotient.mk` composed with it.
   * "We can assume" means replacing the plane by the quotient and `M` by `π[M]`. Since `π` is not a
     homeomorphism, statements about `π[M]` must be pulled back. A shape that avoids this keeps
     `π` explicit throughout.
2. **`π[E]` is an arc.** `π|E` factors through `k`: `π[E]` is the continuous injective image of
   `[0, 1]` under `t ↦ π(k⁻¹(t))`, which is continuous by the quotient property and compactness.
   So it is an arc (compact to Hausdorff). This is available now.
3. **"Decomposably accessible from a side"** (Bing 1960, p. 215, to be supplied).
   * Proposed shape:
     * `π[E]` is an arc `α`.
     * A side of `α` is given by extending `α` to a simple closed curve `J ⊇ α` with `π[M] ∩ J = α`,
       or more simply by an open disk `W` with `α ⊆ ∂W` such that `α` cuts `W` into two components.
     * "`Cl A` and `Cl B` abut on the same side" then says that both arc segments, minus their end
       points, lie in the same component of `W − α`, near `α`.
   * A Jordan-curve-free alternative uses an arc `β ⊆ R²` with `β ∩ α` = the end points. This is
     possible since the repository has the Jordan curve theorem and Moore 1919's double rulings.
   * Bing's p. 215 definition should be read before fixing the shape.
4. **Lemma 9's chain** (`G = {G₁, G₂, G₃}`, `π[Gᵢ]` open disks, `π[Gᵢ] ∩ π[Gᵢ₊₁]` open disks).
   * The existence of a chain following `E` with these properties needs the quotient picture of
     step 1. It is an ε-chain along the arc `π[E]`, made of round disks centred on `π[E]`, pulled
     back by `π`.
   * Lemma 8 (proved) gives the free refinement `L`.
   * The final contradiction cites Moore 1962 Theorem 28, p. 156: "no pair of points of H separates
     two points of K from each other on J". It is in `doc/sources/moore1962-excerpts.pdf` but not
     yet in the repository, so it is to be formalized. The repository's crossing-continua results
     (batch 151, `HPC/Jones`) are the likely route.
5. **"Since `M` is homogeneous, we can assume without loss of generality that `k⁻¹[(0, 1)]` is
   accessible from `R² − M`."**
   * Some point of `M` is accessible from `R² − M`. The plane complement of a plane continuum is
     nonempty and open, and a boundary point is accessible from a complementary domain by an arc;
     this needs a "some boundary point is accessible" lemma (Whyburn/Moore).
   * Move such a point into `k⁻¹((0, 1))` by a homeomorphism of `M`, and transport `E`.
   * Accessibility is not a homeomorphism invariant of `M` alone; it concerns the embedding. The step
     replaces `E` by `h⁻¹[E]` for a homeomorphism `h` of `M` taking an interior layer point to the
     accessible point. That is legitimate, since `h⁻¹[E]` is again of type A′.
   * Mazurkiewicz 1929 is cited later (inaccessible composants) and is requested.
6. **Property 1.** "For each point `y` of `M ∩ ⋃{Lᵢ: 2 ≤ i ≤ 10}` there exists an
   `ε₁`-homeomorphism `h` of `M` onto `M` such that `y` belongs to `h[E]` and `L` follows `h[E]`."
   * The sets `Wₓ` are open by Lemma 2 (proved, `hagopian76_lemma2`).
   * The chain `{Gᵢ}` comes from `ε₁`-neighbourhoods, and `L` from "the method described in the proof
     of Lemma 8" with `A ⊆ G₁ − G₂`, `B ⊆ G₁₁ − G₁₀`. This is `component_of_caps` and `lemma8_aux`
     with different caps, so `component_of_caps` should be generalized to caps `A ⊆ G₁`, `B ⊆ Gₙ`
     whose union with `E` is controlled.
   * The note "the chain formed by taking `ε₁`-neighbourhoods … follows `h[E]`" needs the chain to
     be stable under `ε₁`-homeomorphisms. That follows from the choice of `ε₁` (the minimum over
     the listed distances).

## 5. Continuation: the extension step of Lemma 4

Hagopian's sentence "Since `F` is irreducible between `X` and `d⁻¹(1)`, it is a proper subset of an
element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)" has two halves:
1. finding a continuum `F″` (a piece of `h⁻¹[F]`) with `∅ ≠ F″ ∩ F ⊆ d⁻¹(1)` and `F″ ⊄ F`;
2. building a proper extension of `F` inside `F ∪ F″`.

**Half 2 is proved** (`HPC/Hagopian/H76Lemma4Ext.lean`, `ext_of_branch`):
* Take `x₀ ∈ X` and `z ∈ F″ ∖ F`, and let `H ⊆ F ∪ F″` be irreducible between them
  (`HPC.exists_irreducible`).
* `F ⊆ H`. The set `H ∩ F` is a continuum (hereditary unicoherence). Because `H` is connected and lies
  in `F ∪ F″`, `H ∩ F` meets `F″`, hence meets `d⁻¹(1)`. So `H ∩ F = F` by the end-set property.
* `H` is of type A′. This follows from Kuratowski's criterion (`isTypeA'_of_decomposable`) and the
  1975 ¶2 argument (`no_indecomposable_interior_aux` with `B = F`, `C = F″`).
* Let `D` be its minimal map, normalized by `D(x₀) = 0` (reversed if necessary). Then `D⁻¹(0) = X`:
  * `X ⊆ D⁻¹(0)`. If `D` took a value `t > 0` on `X`, then `D⁻¹(0, t) ⊆ X` by the interval lemma.
    That set is open in `H` and lies in `F`, so `X` would have interior in `F`.
  * `D⁻¹(0) ⊆ F`. Otherwise `D⁻¹(0) ∩ F` meets `F″`, hence `d⁻¹(1)`, so `F ⊆ D⁻¹(0)`. But
    `H ∖ F″` is open in `H`, nonempty, and lies in `F`.
  * `D⁻¹(0) ⊆ X`. Otherwise `D⁻¹(0) ⊇ d⁻¹[0, t)` for some `t > 0` (interval lemma in `F`), and
    `d⁻¹[0, t) = H ∖ (F″ ∪ d⁻¹[t, 1])` is open in `H`.
* Consequences, with the existence of `F″` as the hypothesis `hbranch`:
  * `lemma4_of_branch` and `hagopian76_lemma4_of_branch`: Lemma 4 as printed (a chain with no
    maximal element);
  * `lemma4_seq_of_branch` and `hagopian76_lemma4_seq_of_branch`: the sequence form.

**Half 1, first pass** (superseded below). The natural candidates for `F″` are the two halves
`h⁻¹d⁻¹[[0, u]]` and `h⁻¹d⁻¹[[u, 1]]` of `h⁻¹[F]`, where `u = d(q)`.
* An informal case analysis (not formalized) shows that one of them meets `F` only in `d⁻¹(1)`. If
  neither did, both would contain `p` and a point off `d⁻¹(1)`, so both would contain a tail
  `d⁻¹((s, 1])` (interval lemma). That tail would then lie in their intersection, the single layer
  `h⁻¹d⁻¹(u)`.
* That configuration (a layer of `h⁻¹[F]` containing a tail of `F`) is not excluded by minimality,
  Lemma 3, or atriodicity. The text gives no argument against it.

**Half 1 is proved** (`HPC/Hagopian/H76NoMax.lean`, `exists_proper_extension`): in a compact,
homogeneous, hereditarily unicoherent, atriodic space, every continuum `F` with a minimal admissible
map `d` has a proper extension `H ⊋ F` with a minimal admissible map whose end layer at `0` is
`d⁻¹(0)`. Set-up as in the text: `p ∈ d⁻¹(1)`, `ε` the distance from `X = d⁻¹(0)` to `d⁻¹[1/2, 1]`,
`q ∈ d⁻¹((1/2, 1))` and an `ε`-homeomorphism `h` with `h(p) = q` (Lemma 2), `u = d(q)`,
`B = h⁻¹[F]` with the transported map `b` (`exists_image_map`). Cases:
* `F ⊆ B`: `ext_of_subset` (`H76NoMaxCases.lean`). The extension is a continuum irreducible from a
  point of `X` to a point of `B ∖ F` (`ext_of_irreducible_union`); the input used is that
  `b⁻¹[u, 1]` misses `X`.
* `F ⊄ B`: then `B` misses `X` (end-set property). If one of the halves `C₀ = b⁻¹[0, u]`,
  `C₁ = b⁻¹[u, 1]` meets `F` only in `d⁻¹(1)` and is not inside `F`, `ext_of_branch` applies. (`C₀ ⊆ F` is
  impossible since `b⁻¹(0)` misses `d⁻¹[1/2, 1]`; if `C₁ ⊆ F` meets `F` only in `d⁻¹(1)`, a tail
  argument gives a contradiction.)
* Otherwise both halves contain a tail of `F` (`tail_subset`), so the layer `b⁻¹(u)` contains a tail
  `d⁻¹((s, 1])`. Then `F ∩ B` cannot meet both sides of `b⁻¹(u)` (`false_of_layer_open`). Pick
  `s < s' < 1`. The continua `d⁻¹[0, u]`, `d⁻¹[u, 1]` and `h[d⁻¹[0, s']]` share a point of `d⁻¹(u)`,
  so one lies in the union of the other two (`three_continua`, from atriodicity and hereditary
  unicoherence).
  * `h[d⁻¹[0, s']] ⊆ F` would give `F ⊆ B`, excluded.
  * `d⁻¹[0, u] ⊆ d⁻¹[u, 1] ∪ h[d⁻¹[0, s']]` gives `b⁻¹[0, u) ⊆ d⁻¹[0, s']`, and then `F ∩ B` misses
    `b⁻¹(u, 1]`. `ext_of_side` (`H76NoMaxCases.lean`) builds the extension.
  * The remaining case is the same with the map of `B` reversed (`isAdmissibleMap_symm`).
* `lemma4_aux` and `lemma4_seq_aux` combine this with `ext_chain` and
  `exists_strictMono_seq_of_chain`. In `Hagopian76A.lean`, `hagopian76_lemma4` and
  `hagopian76_lemma4_seq` are proved from them, with hereditary unicoherence and atriodicity of `M`
  from `hagopian75_lemma1`.

**Axioms.** All eight new theorems depend only on `[propext, Classical.choice, Quot.sound]`:
`isAdmissibleMap_symm`, `interior_symm_fibre`, `meets_inter_of_cover`, `ext_of_branch`,
`lemma4_of_branch`, `lemma4_seq_of_branch`, `hagopian76_lemma4_of_branch` and
`hagopian76_lemma4_seq_of_branch`. They are listed in `Axioms.lean`, `axioms.txt` and
`doc/batches/audits/axioms-batch156.txt`.

The continuation adds 14 more theorems with the same three axioms: `hagopian76_lemma4`,
`hagopian76_lemma4_seq`, `layer_one_subset_closure`, `tail_subset`, `false_of_layer_open`,
`three_continua`, `exists_image_map`, `ext_of_irreducible_union`, `not_subset_layer_of_open`,
`ext_of_subset`, `ext_of_side`, `exists_proper_extension`, `lemma4_aux` and `lemma4_seq_aux`. `lake build
HPC` succeeds and `axioms.txt` has no `sorryAx`.
