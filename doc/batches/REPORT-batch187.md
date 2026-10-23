Commission read: `doc/batches/COMMISSION-batch187.md` ("Commission: batch 187 — Part E, Hagopian 1984 IV: Lemma 13; Lemma 16′; the bridge `J(Z)`").

# Report, batch 187

## 0. Summary, omissions

**Every item of the commission is proved.** **Lemma 13 is proved** in the batch-186 shape
(`hagopian84_lemma13`), with `chainLinks84_chain`, `chainLinks84_runsStraight` and
`chainLinks84_regular`. **Lemma 16′ is proved** (`strand_layer_of_extension`, with
`strand_layer_mem_delta` and `not_strand_subset_extension_layer`), and **Lemma 16 as printed**
follows from it with normality added (`hagopian84_lemma16`). **The bridge is proved**
(`omega_not_delta_side`, `exists_bridge84`). From §5: **`𝒫(Z)` is proved** with `Z ∈ Δ(𝒫(Z))`
(`exists_chainZ84`, `mem_delta_of_bridge_chain`), and the **finite cover is proved**
(`hagopian84_cover`, `exists_finite_cover84`) by an argument that does not go through the printed
closedness of `⋃𝔅`. That closedness is unargued in print and stays open (§5.2); nothing later needs
it. No `sorry` in any declaration; nothing refuted. `axioms.txt` has **2392 lines** (2306 + 86 added,
none removed), `sorryAx` in none.

Status lines:
* STATUS: §3.2 `strand_layer_mem_delta` proved (shape change: `hn` dropped)
* STATUS: §3.3 the dichotomy (`strand_dichotomy`) proved
* STATUS: §3.4 `not_strand_subset_extension_layer` proved
* STATUS: §3.1 `strand_layer_of_extension` (Lemma 16′) proved
* STATUS: §3.5 printed Lemma 16 proved from Lemma 16′ (`hagopian84_lemma16`, normality added)
* STATUS: §2 chain part `chainLinks84_chain` proved
* STATUS: §2.1 Hagopian's (3) `link_dichotomy84` proved
* STATUS: §2.2 Hagopian's (4) `layer_frontier84` proved
* STATUS: §2.3 Hagopian's (5), kinds D and U, `no_fold84`, `layer_convex84` proved
* STATUS: §2 `chainLinks84_runsStraight` proved (batch-186 shape)
* STATUS: §2 `chainLinks84_regular` proved (batch-186 shape, hypothesis made explicit)
* STATUS: §2 `hagopian84_lemma13` proved (batch-186 shape)
* STATUS: §4.2 `omega_not_delta_side` proved
* STATUS: §4.3 `exists_ext_meeting_P2` proved
* STATUS: §4.4 `exists_bridge84` proved (the skeleton statement)
* STATUS: §5.1 `mem_delta_of_bridge_chain`, `exists_chainZ84` proved
* STATUS: §5.2 the finite cover `exists_finite_cover84`, `hagopian84_cover` proved; the printed
  closedness of `⋃𝔅` open (unargued; not needed)

**Omissions (§0 rule).**
1. **The printed closedness of `⋃𝔅`** (commission §5.2): not stated as a declaration. Reason: no
   argument was found (§5.2 says exactly what is missing), and the finite subcover that the proof
   uses next is proved without it.
2. **The positions of the end sets of `J(Z)` relative to `K(Z)`** ("one end set in
   `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in `(⋃Δ(𝒫))∖K(Z)`"): not claimed in `exists_bridge84`.
   Reason: with the commission's choice of `u*` the second end layer may still be a layer of
   `Cl K(Z)`; neither `𝒫(Z)` nor the cover uses the positions (§4).
3. **The commented-out batch-184 copy of `hagopian84_lemma13` in `Hagopian84A.lean`** is not
   replaced by a pointer. Reason: `Hagopian84A.lean` is not on the commission's list of editable
   files. The batch-186 copies in `Hagopian84B.lean` are replaced by pointers.

## 1. Files and wiring

`HPC/Hagopian/Hagopian84C.lean` (the skeleton, statements; header rewritten). Proofs, split under
`HPC/Hagopian/`:
* `H84Strand.lean` (§3: Lemma 16′, Lemma 16);
* `H84Bridge.lean` (§4 and §5.1's check `Z ∈ Δ(𝒫(Z))`);
* `H84Chain13.lean` (§2: `W(S, δ)`, the segments, the choice of `x`, the chain part);
* `H84Runs13.lean` (§2: gap bounds, (3), (4), the fold, (6));
* `H84Regular13.lean` (§2: regularity in general form);
* `H84Lemma13.lean` (§2: the batch-186 shapes and Lemma 13);
* `H84Cover.lean` (§5.2: the finite cover).

`HPC.lean` ends with `import HPC.Hagopian.Hagopian84C`; `lake build HPC` succeeds. In
`Hagopian84B.lean` the commented-out blocks of `chainLinks84_runsStraight`, `chainLinks84_regular`,
`hagopian84_lemma13` and `hagopian84_lemma16` are replaced by one-line pointers.

## 2. Lemma 13 (proved)

**2.1 The numbers** (`exists_chain84_core`). `x` from `exists_x84` (commission §2.4: upper
semicontinuity gives `η` with `k⁻¹[[0, η] ∪ [1 − η, 1]] ⊆ B`; `x₃ = η`, `x₁₂ = 1 − η`, the rest evenly
spaced). `δ` is the least of: the radius of `chainLinks84_chain_aux` (non-adjacent segments; the end
layers against the segments of `L 1`, `L 3`; `A`; `B`), `ε/2`, and half the least of the fifteen gap
radii `ρ(k⁻¹[[0, xⱼ]], k⁻¹[[xⱼ₊₁, 1]])`, `0 ≤ j ≤ 14` (`exists_gap84`, named `GapBound84`). Hagopian
takes `1 ≤ j ≤ 13`; the two extra bounds shorten the bookkeeping and cost nothing.

**2.2 The chain part** (`chainLinks84_chain`, proved earlier in this batch): the links form a normal
chain in `M∖A`, `Cl(L 0 ∪ L 4) ⊆ B`, and (1)–(2) hold for every `δ`-translate (closure form of (2)).

**2.3 Hagopian's (3)** (`link_dichotomy84`): `h[k⁻¹(r)] ⊆ L i` or `h[k⁻¹(r)] ∩ L i = ∅`, for every
`δ`-homeomorphism `h`. As commission §2.1: a point `h(z) = g(w)` with `k z = r`, `w` over
`[x₃ᵢ, x₃ᵢ₊₃]` gives `dist(z, w) < 2δ` (`close84`), so no gap separates `r` and `s = k w`
(`gapBound84_near`). If `r ∉ [x₃ᵢ, x₃ᵢ₊₃]`, the order lemma `params_inner84` puts `r` and `s` in
`[x₁, x₁₄]` (it uses the gaps `j = 1, 2, 12, 13`); the end-set hypotheses of Lemma 3 for `h⁻¹ ∘ g`
follow from the gaps `j = 0, 14`; Lemma 3 gives `h⁻¹g[k⁻¹(s)] = k⁻¹(r)`, so `h[k⁻¹(r)] = g[k⁻¹(s)] ⊆ L i`.
No uniform continuity.

**2.4 Hagopian's (4)** (`layer_frontier84`): as commission §2.2, with `η = min(ρ(q, Lᵢ), δ − max
dist(v, h v))` (the maximum exists by compactness) and Effros (`effros_homogeneous`).

**2.5 Hagopian's (5)** (`layer_convex84`, `no_fold84`): the parameter sets `V i` are open intervals.
Openness through (3) and `isOpen_params_meeting`; a non-interval gives a fold (`exists_fold`). Kind D
(`q = p + 1`): `C = g[k⁻¹[[0, x₃ₚ₊₃]]] ⊆ L 0 ∪ ⋯ ∪ L p` (`mem_link_le84`) misses the end layers of
`F = h[k⁻¹[[r, t]]]` (which lie in `L q` and miss `L p`), and meets `F`; atriodicity
(`subset_of_meets_avoids`, with `minimalAdmissible_restrict` and `exists_image_map` for the map of
`F`) gives `C ⊆ F`. A point `g(a)`, `k a = 0`, is `h(z′)` with `k z′ ∈ [r, t]`, and the gap `j = 0`
gives `k z′ < x₁`; so `h[k⁻¹(r)] ⊆ L 0`, and `L 0 ∩ L q ≠ ∅` forces `p = 0`, against `r ∉ V p`. Kind
U (`p = q + 1`) is the mirror (`g[k⁻¹[[x₃ₚ, 1]]]`, `mem_link_ge84`, gap `j = 14`, `p = 4`).

**2.6 (6)** (`translate_runsStraight84`): any map `b` of `G = h[E]` whose layers are the images of
those of `k` runs straight. *Shape:* the domain is passed as a set `G` with `G = h[E]`, so the
identity case gives `RunsStraight k 𝔏` directly.

**2.7 `chainLinks84_runsStraight`** (batch-186 shape, unchanged): from 2.1–2.6 with
`exists_image_map`.

**2.8 Regularity** (`strand_of_runsStraight84`, general; `chainLinks84_regular_aux`). For any type λ
`(G, b)` running straight through a normal chain with `b⁻¹(0) ⊆ L 0 ∖ Cl L 1`,
`b⁻¹(1) ⊆ L 4 ∖ Cl L 3`, and any component `K` of `⋃𝔏′` meeting `G`: `Cl K ⊆ G` (atriodicity; the
end layers miss `Cl ⋃𝔏′` by normality); `Cl K` is essential (the layers over a short parameter
interval at a point of `K` form a connected subset of `⋃𝔏′`); `Cl K = b⁻¹[[a, c]]` (Lemma 6); `a`, `c`
are outside `V 1 ∪ V 2 ∪ V 3` (else the layers beyond them would join `K`); and `a ∈ V 4` or
`c ∈ V 0` would make two consecutive parameter sets disjoint, disconnecting `[0, 1]`
(`params_adjacent_meet84`). The restricted map runs straight. For `chainLinks84`, every point of
`⋃𝔏′` is `h(v)` with `v ∈ E` and `h` a `δ`-homeomorphism (definition of `W`).
*Shape change* (`chainLinks84_regular`): the batch-186 text "for `x`, `δ` as in
`chainLinks84_runsStraight`" is made an explicit hypothesis `hrs`, the last clause of
`chainLinks84_runsStraight`; `hE` is not needed.

**2.9 Lemma 13** (`hagopian84_lemma13`, batch-186 shape unchanged): as the batch-186 assembly note.

## 3. Lemma 16′ (proved)

As commission §3, proved earlier in this batch (`H84Strand.lean`): `strand_layer_mem_delta`
(*shape change:* `hn` dropped, unused), `strand_dichotomy` (3.3), `not_strand_subset_extension_layer`
(3.4; step 3 by a single limit point `z ∈ d⁻¹(α) ∩ Cl P 2`, from the closedness of the parameters whose
layer meets `Cl P 2`; Lemma 14 not needed), `strand_layer_of_extension` (3.1).

**Lemma 16 as printed** (`hagopian84_lemma16`). *Shape changes:* normality `hn` added (Lemma 16′
uses it in 3.4 step 2; the chains of Lemma 13 are normal); the hypothesis `Cl K ⊆ F` dropped
(unused); the end set normalized to `d⁻¹(0) = c⁻¹(0)`.

**3.5, Hagopian's own proof.** Yes, 3.4 gives a proof of the printed Lemma 16 (for normal chains),
and it makes Hagopian's interval argument unnecessary rather than completing it. By Lemma 16′, every
layer of `F` that meets `⋃𝒫′` is a layer of a strand, and a strand layer lies in every link it meets
(`layer_subset_link`). A layer meeting three consecutive links `P i, P i+1, P i+2` meets
`P i+1 ⊆ ⋃𝒫′`, so it would lie in `P i ∩ P i+2 = ∅`. Hence Hagopian's set
`S = {r : d⁻¹(r) meets three consecutive links}` is empty, and neither the infimum `s`, nor the
subchain `𝔔`, nor his (1), nor the interval `[t, w]` is needed. Whether his weaker requirement (an
interval of such layers whose union misses some link) could be obtained without Lemma 16′ is not
examined. Lemma 16 without normality is not decided.

## 4. The bridge `J(Z)` (proved)

Reading choices (recorded at the statements):
1. **`K(Z)`** (4.1): the component whose closure has `Z` as a layer, taken from the definition of
   `Ω(𝒫)` (`bridge_setup`).
2. **`X(Z)`** (4.2): `omega_not_delta_side` gives `Z ⊆ Cl P 0` or `Z ⊆ Cl P 4`, and `Z ∩ Cl P 2 = ∅`;
   `X(Z)` is the end layer on the far side (the strand map oriented so that it is over `0`).
3. **`F(Z)`** (4.3): `exists_ext_meeting_P2`, the commission's argument (Lemma 11, strict
   extensions by Lemma 4).
4. **`J(Z)`** (4.4, `exists_bridge84_aux`): `m₂` the largest parameter `≤ z₀` whose layer meets
   `Cl P 2`, `u*` the least parameter `≥ z₀` whose layer meets `Cl P 2` (both exist: the condition is
   closed, `X(Z)` side and `F(Z)` meets `P 2`); `a`, `b` next to them inside the open set of parameters
   whose layer lies in `⋃𝒫′` and misses `Cl(P 0 ∪ P 4)`; Lemma 16′ makes `d⁻¹(a)`, `d⁻¹(b)` members of
   `Δ(𝒫)`. `translate_run` is not needed.

The statement is the skeleton's: `J` type λ, `Z` a layer of `J`, `J ∩ Cl P 2 = ∅`, both end layers
in `Δ(𝒫)`, every layer meeting `⋃𝒫′` a strand layer. Not claimed: the end set positions relative to
`K(Z)` (§0, item 2).

## 5. `𝒫(Z)` and the cover

**5.1 `𝒫(Z)`** (proved; `exists_chainZ84`). Lemma 13 for `J(Z)` with `A = Cl P 2`, `B = ⋃Δ(𝒫)`
(open: `isOpen_sUnion_delta5`; it contains both end layers of `J(Z)`), `ε = 1`. The check
`Z ∈ Δ(𝒫(Z))` (`mem_delta_of_bridge_chain`), as commission §5.1: `Z` lies in `Cl P 0` or `Cl P 4`,
hence misses `⋃Δ(𝒫) ⊇ Cl(P(Z) 0 ∪ P(Z) 4)`, and lies in `⋃𝒫(Z)′`; `j⁻¹(0)` misses `⋃𝒫(Z)′`; Lemma
16′ for `𝒫(Z)` makes `Z` a strand layer of `𝒫(Z)`. The statement also records Hagopian's (2)
(`⋃𝒫(Z)` misses `Cl P₃`) and (3).

**5.2 The cover.** *The printed closedness of `⋃𝔅`: open, obstruction stated.* Freeness of `𝒫` and
of each `𝒫(Z)`, with (3), give `Cl ⋃Δ(𝒫(Z)) ⊆ ⋃Δ(𝒫(Z)) ∪ Cl(P(Z) 0 ∪ P(Z) 4) ⊆ ⋃Δ(𝒫(Z)) ∪ ⋃Δ(𝒫)`
for each `Z` separately (`closure_sUnion_delta5_subset`). For a point that is a limit of points of
`⋃Δ(𝒫(Zₙ))` with pairwise distinct `Zₙ` (the family is uncountable), nothing in the text places it
in `⋃𝔅`; the commission's suggested way around (sharing one `𝒫(Z)` among nearby `Z`) was not
needed.

*The finite subcover: proved* (`exists_finite_cover84`, for any choice of chains with `Z ∈ Δ(𝒫(Z))`,
freeness, regularity and (3); `hagopian84_cover`, with the choice made by `exists_chainZ84`). The set
`C = Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` is compact. Each point of `C` lies in `⋃𝒫′ ∩ Cl(P 0 ∪ P 4)` (freeness), so the
layer `Z` through it of its strand is in `Ω(𝒫) ∖ Δ(𝒫)` and the point lies in `Z ⊆ ⋃Δ(𝒫(Z))`.
Finitely many `⋃Δ(𝒫(Zᵢ))` cover `C`; `U = ⋃Δ(𝒫) ∪ ⋃ᵢ ⋃Δ(𝒫(Zᵢ))` is open, and closed by the inclusion
above for the finitely many `Zᵢ` together with `Cl ⋃Δ(𝒫) ⊆ ⋃Δ(𝒫) ∪ C`. `M` is connected, so
`U = M`. This is the conclusion Hagopian uses next ("there exists a finite subcollection … of `𝔅`
that covers `M`").

## 6. Non-vacuity notes

Named `Prop`s and structures among hypotheses of theorems of this batch, other than the paper's
definitions from batch 184 (`IsChain5`, `IsNormal5`, `IsFree5`, `IsRegular5`, `RunsStraight`,
`IsMinimalAdmissible`, `Omega5`, `Delta5`):

1. **`GapBound84 k x δ`** (hypothesis of `link_dichotomy84`, `layer_frontier84`, `no_fold84`,
   `layer_convex84`, `translate_runsStraight84`).
   1. *Not refuted:* it is discharged; `exists_gap84` gives a radius `ρ > 0` for every strictly
      increasing `x`, and `exists_chain84_core` takes `δ ≤ ρ/2`.
   2. *Not equivalent to the conclusions:* it is a statement about distances inside `E` only; the
      conclusions are about translates `h[E]` and the links, and need Lemma 3, Effros and
      atriodicity besides.
2. **`chainLinks84_regular`, hypothesis `hrs`** (every `δ`-translate runs straight, end layers in
   `L 0 ∖ Cl L 1`, `L 4 ∖ Cl L 3`).
   1. *Not refuted:* it is discharged by `chainLinks84_runsStraight` (in `hagopian84_lemma13_aux`).
   2. *Not equivalent:* the conclusion (regularity, and essential strands) is about the closures of
      the components of `⋃𝔏′`, which `hrs` does not mention; the proof needs atriodicity, Lemma 6
      and the orientation argument.
3. **`mem_delta_of_bridge_chain`, hypotheses `hjs : RunsStraight j Q` and
   `hB : Cl(Q 0 ∪ Q 4) ⊆ ⋃Δ(𝒫)`** (with the chain properties of `Q`).
   1. *Not refuted:* discharged by Lemma 13 in `exists_chainZ84`.
   2. *Not equivalent:* `Z ∈ Δ(Q)` needs Lemma 16′ for `Q`; the hypotheses say nothing about the
      strands of `Q`.
4. **`exists_finite_cover84`, hypothesis `hQ`** (for every `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`, `Q Z` is a free
   regular chain with `Z ∈ Δ(Q Z)` and (3)).
   1. *Not refuted:* discharged by `exists_chainZ84` in `hagopian84_cover`.
   2. *Not equivalent:* `hQ` is about each `Z` separately; the conclusion (a finite cover of `M`)
      needs compactness of `Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)`, freeness of `𝒫` and connectedness of `M`. The argument
      is direct, not by contradiction.

## 7. Ledger entries

`LEDGER.md`, Hagopian 1984 section, new subsection "Hagopian 1984 IV: Lemma 13; Lemma 16′; the
bridge `J(Z)`; `𝒫(Z)`; the cover (batch 187)", entries H84.23–H84.29, each with the printed
sentences quoted:
* **H84.23** Lemma 16 and its use on p. 343: step (1) still unargued; the use proved as Lemma 16′;
  Lemma 16 proved with normality added; gap in exposition.
* **H84.24** `K(Z)`: "the component of `⋃𝒫′` that contains `Z`" can fail to exist; read from the
  definition of `Ω(𝒫)`; slip, harmless.
* **H84.25** `X(Z)`: unargued, true, proved (`omega_not_delta_side`).
* **H84.26** "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`": unargued, true, proved.
* **H84.27** `J(Z)`: unargued; proved without the end set positions relative to `K(Z)`.
* **H84.28** Lemma 13 (3)–(6) and regularity: unargued steps, all true; Lemma 13 proved as printed;
  the orientation argument for regularity is not in the text.
* **H84.29** the cover: closedness of `⋃𝔅` unargued; the finite subcover proved directly; gap in
  exposition.

Nothing refuted; the count of defective proofs stays at fourteen.

## 8. Axioms

`Axioms.lean` group "Hagopian 1984 IV (batch 187)": 86 declarations (every theorem of the eight
files of §1). `axioms.txt` regenerated: **2392 lines** (2306 + 86; none removed; `sorryAx` in no
line). Per-theorem audit: `doc/batches/audits/axioms-batch187.txt`. Every one of the 86 depends on
exactly `[propext, Classical.choice, Quot.sound]`:

* `H84Strand.lean`: `isOpen_params_meeting`, `isOpen_params_disjoint`, `isClosed_params_meeting`,
  `strand_meets_P2_P0`, `strand_layer_subset_mid`, `strand_dichotomy`, `strand_layer_mem_delta_aux`,
  `closure_P2_subset`, `not_strand_subset_extension_layer_aux`, `strand_layer_of_extension_aux`,
  `strand_end_layer_not_mid`, `hagopian84_lemma16_aux`;
* `H84Bridge.lean`: `layer_subset_closure_link`, `omega_not_delta_side_aux`, `meets_P2_of_connects`,
  `bridge_setup`, `exists_ext_meeting_P2`, `exists_bridge84_aux`, `mem_delta_of_bridge_chain_aux`;
* `H84Chain13.lean`: `wsetOf_subset_thickening`, `subset_wsetOf`, `image_subset_wsetOf`,
  `isOpen_wsetOf`, `closure_wsetOf_subset`, `image_subset_thickening`, `chainLinks84_eq`,
  `isCompact_seg84`, `seg84_disjoint`, `seg84_meet`, `seg84_nonempty`, `layer_zero_subset_seg84`,
  `layer_one_subset_seg84`, `mem_some_seg84`, `xf84_strictMono`, `xf84_mem`, `xf84_zero`,
  `xf84_fifteen`, `xf84_three`, `xf84_twelve`, `exists_sep_radius`, `exists_x84`,
  `chainLinks84_chain_aux`;
* `H84Cover.lean`: `isOpen_sUnion_delta5`, `closure_sUnion_delta5_subset`,
  `exists_finite_cover84_aux`;
* `H84Runs13.lean`: `xle84`, `xlt84`, `exists_gap84`, `close84`, `params_inner84`,
  `gapBound84_near`, `image_layer_subset_link84`, `link_dichotomy84`, `layer_frontier84`,
  `mem_seg84_iff`, `mem_link_le84`, `mem_link_ge84`, `no_fold84`, `layer_convex84`,
  `translate_runsStraight84`;
* `H84Regular13.lean`: `mem_layerSet_iff84`, `restrictParam_le84`, `restrictParam_lt84`,
  `params_adjacent_meet84`, `exists_right_Icc84`, `exists_left_Icc84`, `layer_subset_layerSet84`,
  `strand_of_runsStraight84`;
* `H84Lemma13.lean`: `exists_chain84_core`, `chainLinks84_runsStraight_aux`,
  `chainLinks84_regular_aux`, `hagopian84_lemma13_aux`;
* `Hagopian84C.lean`: `chainLinks84_chain`, `chainLinks84_runsStraight`, `chainLinks84_regular`,
  `hagopian84_lemma13`, `strand_layer_mem_delta`, `not_strand_subset_extension_layer`,
  `strand_layer_of_extension`, `hagopian84_lemma16`, `omega_not_delta_side`, `exists_bridge84`,
  `mem_delta_of_bridge_chain`, `exists_finite_cover84`, `exists_chainZ84`, `hagopian84_cover`

(all in namespace `HPC.Hagopian`). In `Hagopian84C.lean` and the seven proof files, `sorry` occurs
in no declaration (the word appears once, in the header comment of `Hagopian84C.lean`).

## 9. Dependency map of `Hagopian84Decomp` (the 1984 route)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_jones                          [proved, batch 184]
   ├─ exists_plane_quotient_of_monotone                  [proved]
   ├─ indecomposable_of_monotone_image                   [proved]
   ├─ NoArcIndecHomPlane (Bing 1960 / Jones 1975)        [OPEN, named Prop; jones75.md]
   └─ Hagopian84Decomp (Theorem 1, N = M)                [OPEN, named Prop]
      └─ hagopian84Decomp_of_package                     [proved, batch 186]
         ├─ exists_comp_small_homeo (orbits)             [proved, batch 186]
         └─ hP: ∀ M, ∃ r, IsJonesDecomp84 r              [OPEN: hagopian84_decomp]
            └─ construction pp. 343–344
               ├─ Lemma 13 (chain 𝒫)                     [proved, batch 187]
               │  ├─ chainLinks84_chain                   [proved, batch 187]
               │  ├─ chainLinks84_runsStraight            [proved, batch 187]
               │  │  ├─ (3) link_dichotomy84 ← Lemma 3    [proved]
               │  │  ├─ (4) layer_frontier84 ← Effros     [proved]
               │  │  └─ (5) exists_fold + no_fold84       [proved]
               │  ├─ chainLinks84_regular                 [proved, batch 187]
               │  └─ Lemma 12 (hagopian84_lemma12)        [proved, batch 186]
               ├─ Lemma 16′ (strand_layer_of_extension)   [proved, batch 187]
               ├─ K(Z), X(Z), F(Z), J(Z): exists_bridge84 [proved, batch 187]
               ├─ 𝒫(Z), Z ∈ Δ(𝒫(Z)): exists_chainZ84      [proved, batch 187]
               ├─ finite cover: hagopian84_cover          [proved, batch 187]
               ├─ 𝔇 := ⋃ᵢ Δ(𝒫(Zᵢ)), disjointness         [OPEN, next]
               ├─ claims (5), (6)                         [OPEN, next]
               ├─ field usc ← Lemma 14                    [proved, batch 186]
               ├─ field invariant ← Lemma 15, (5), (6)    [Lemma 15 proved; (5), (6) open]
               └─ field arc ← exists_interval_in_delta    [proved, batch 186]
   (not needed with N = M: Lemmas 8, 10, claim (4), the solenoid conclusion, the last paragraph)
```

## 10. Skeleton proposal for the next step

```lean
/-- p. 343: the finite family `𝒫(Z₀) = 𝒫, 𝒫(Z₁), …, 𝒫(Zₙ)` of `hagopian84_cover`, and
`𝔇 = ⋃ᵢ Δ(𝒫(Zᵢ))` ("For convenience we define `𝒫(Z₀)` to be `𝒫`"). -/
structure CoverData84 (M : Set Pt) [CompactSpace M] [ConnectedSpace M] where
  P : Fin 5 → Set M
  hP : IsChain5 P ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P
  S : Finset (Set M)
  Q : Set M → Fin 5 → Set M
  hQ : ∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P ∧ IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧
    IsNormal5 (Q Z) ∧ IsRegular5 (Q Z) ∧ Z ∈ Delta5 (Q Z) ∧ (⋃ i, Q Z i) ⊆ (closure (P 2))ᶜ ∧
    closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P
  cover : ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z)

theorem exists_coverData84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hH : ¬ IsHereditarilyIndecomposable (univ : Set M)) : Nonempty (CoverData84 M)
  -- a type λ E (batch 184), Lemma 13 with any A, B, then hagopian84_cover

/-- The members of `𝔇`. -/
def CoverData84.members (D : CoverData84 M) : Set (Set M) :=
  Delta5 D.P ∪ ⋃ Z ∈ D.S, Delta5 (D.Q Z)

/-- p. 344, disjointness: "If `A ∪ B` intersects `⋃Δ(𝒫)`, then, by (2), (3), and Lemma 7, `A = B`
… Thus, by Lemma 3, `A = B`." -/
theorem CoverData84.members_disjoint (D : CoverData84 M) {A B : Set M} (hA : A ∈ D.members)
    (hB : B ∈ D.members) (hAB : (A ∩ B).Nonempty) : A = B

/-- Claim (5): `Ω(𝒫(Zᵢ)) ⊆ 𝔇` (freeness, (3), Lemma 7 / Lemma 16′). -/
theorem CoverData84.omega_subset (D : CoverData84 M) (Z) (hZ : Z ∈ D.S) :
    Omega5 (D.Q Z) ⊆ D.members  -- and Omega5 D.P ⊆ D.members

/-- Claim (6): a `δ`-homeomorphism maps members to members (Lemma 15 and claim (5)). -/
theorem CoverData84.invariant (D : CoverData84 M) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∀ Z ∈ D.members, h '' Z ∈ D.members

noncomputable def CoverData84.setoid (D : CoverData84 M) : Setoid M
  -- x ~ y iff some member contains both (members_disjoint and cover give an equivalence)

theorem CoverData84.isJonesDecomp (D : CoverData84 M) : IsJonesDecomp84 D.setoid
  -- usc: Lemma 14 for each of the finitely many chains; conn: layers are connected;
  -- proper: a member lies in one link; invariant: claim (6); arc: exists_interval_in_delta

theorem hagopian84_decomp : Hagopian84Decomp :=
  hagopian84Decomp_of_package fun M _ _ hX hi hH =>
    ⟨_, (Classical.choice (exists_coverData84 hX hi hH)).isJonesDecomp⟩
```
Points to check before formalizing: Hagopian's disjointness uses "(2), (3), and Lemma 7" when
`A ∪ B` meets `⋃Δ(𝒫)`; Lemma 16′ (for `𝒫`, applied to the strands of `𝒫(Zᵢ)`) should replace Lemma
7 there, as on p. 343. The usc field needs Lemma 14 near points of `⋃Δ(𝒫(Zᵢ))` for each `i`; the
members of `Δ(𝒫(Zᵢ))` near `Cl(P(Zᵢ) 0 ∪ P(Zᵢ) 4)` lie in `⋃Δ(𝒫)`, where the members of `Δ(𝒫)` are
used instead. The shapes above are proposals, not checked.

## 11. Files

New: `HPC/Hagopian/Hagopian84C.lean`, `HPC/Hagopian/H84Strand.lean`, `HPC/Hagopian/H84Bridge.lean`,
`HPC/Hagopian/H84Chain13.lean`, `HPC/Hagopian/H84Runs13.lean`, `HPC/Hagopian/H84Regular13.lean`,
`HPC/Hagopian/H84Lemma13.lean`, `HPC/Hagopian/H84Cover.lean`, `doc/batches/REPORT-batch187.md`,
`doc/batches/audits/axioms-batch187.txt`, `doc/batches/batch187-MANIFEST.txt`,
`doc/batches/batch187-files.tar.gz`. Uploads placed: `doc/batches/COMMISSION-batch187.md`,
`doc/batches/skeletons/Hagopian84C.lean`. Changed: `HPC.lean`, `Axioms.lean`, `axioms.txt`,
`README.md`, `LEDGER.md` (Hagopian 1984 section), `OPEN.md`, `doc/notes/hagopian84.md`,
`HPC/Hagopian/Hagopian84B.lean` (pointers only). The full list is the manifest.
