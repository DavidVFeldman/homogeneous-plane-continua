# Hagopian 1984, *Atriodic homogeneous continua* — transcription, dictionary, route

Source: C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984), 333–347
(`doc/sources/hagopian1984.pdf`; journal page = PDF page + 331). Transcribed in batch 184 from page
images rendered at 200 dpi (not from extracted text). Symbols: script letters are written `𝔇`
(decomposition), `𝔖` (Hagopian's script S of extensions), `𝔏` (a chain), `𝒫`, `𝔅`, `𝔔`; `Cl`,
`Bd` closure and boundary in `M`. Page breaks are marked `[p. n]`.

## A. Transcription

### §1 (p. 333), the definitions used later

> A space is *homogeneous* if for each pair `p, q` of its points there is a homeomorphism of the
> space onto itself that takes `p` to `q`. A *continuum* is a compact connected nondegenerate metric
> space. A continuum `M` is a *triod* if `M` has a subcontinuum `H` such that `M∖H` is the union of
> three nonempty disjoint opens sets. When a continuum does not contain a triod it is *atriodic*. A
> continuum `M` is *tree-like* if for each positive number `ε` there is an open covering of `M` with
> mesh less than `ε` whose nerve is a tree. A continuum is *decomposable* if it is the union of two
> of its proper subcontinua; otherwise, it is *indecomposable*. When a continuum does not have a
> decomposable subcontinuum it is *hereditarily indecomposable*. Note that every hereditarily
> indecomposable continuum is atriodic.

Note: \"continuum\" is *nondegenerate* here (unlike the repository's `Fold.Q78.IsContinuum`, which
allows a point). \"opens sets\" is a slip (§E).

### §2 (pp. 334–335)

[Quotation moved to doc/sources/transcriptions/hagopian84.md, §doc/notes/hagopian84.md, A. Transcription, §2 (pp. 334–335); batch 204.]

### §3 (pp. 335–342)

[Quotation moved to doc/sources/transcriptions/hagopian84.md, §doc/notes/hagopian84.md, A. Transcription, §3 (pp. 335–342) (passage 1); batch 204.]

(In (5) of Lemma 13 the printed `g[k⁻¹(0, x₃ᵢ)]]` has unbalanced brackets, and the next
`g[k⁻¹[0, x₃ᵢ]]` uses `[0, x₃ᵢ]` without the inner brackets used elsewhere; both are transcribed as
printed.)

[Quotation moved to doc/sources/transcriptions/hagopian84.md, §doc/notes/hagopian84.md, A. Transcription, §3 (pp. 335–342) (passage 2); batch 204.]

### §4 (pp. 342–346): Theorem 1 and the Corollary 3 paragraph

[Quotation moved to doc/sources/transcriptions/hagopian84.md, §doc/notes/hagopian84.md, A. Transcription, §4 (pp. 342–346); batch 204.]

The commission's transcription of p. 346 agrees with the page image word for word.

References used (p. 346–347): [4] Bing, *A simple closed curve is the only homogeneous bounded
plane continuum that contains an arc*, Canad. J. Math. 12 (1960), 209–230; [10] Hagopian,
*Homogeneous plane continua*, Houston J. Math. 1 (1975), 35–41; [11] Hagopian, *Indecomposable
homogeneous plane continua are hereditarily indecomposable*, Trans. AMS 224 (1976), 339–350;
[15] Jones 1951; [16] Jones, *Homogeneous plane continua*, Proc. Auburn Topology Conf. (1969),
46–56; [19] Kuratowski, *Topology* II (1968); [20] Mackowiak–Tymchatyn, Dissertationes Math. 225
(1983); [21] Moore 1925, Trans. AMS 27, 416–428; [22] Moore, *Foundations of point set theory*,
rev. ed. 1962; [25] Rogers, Houston J. Math. 8 (1982); [26] Thomas, Rozprawy Mat. 50 (1966).

The transcription above was checked again in batch 184 against the page images rendered at 200 dpi
(PDF pages 2–16). Pages 336, 343 and 346 were compared line by line; no difference was found.

## B. Dictionary with the repository (commission 184 §2.2, checked)

Setting of the repository's results: `M : Set Pt` compact, connected, homogeneous, indecomposable
(a plane continuum). Hagopian's §3 setting ("`M` is an atriodic homogeneous continuum") is reached
by `hagopian75_lemma1` (atriodic and hereditarily unicoherent).

| Hagopian 1984 | repository | check |
| --- | --- | --- |
| type λ (p. 335: irreducible, every indecomposable subcontinuum a continuum of condensation; "continua of type `A′`" in Thomas) | `IsTypeA'`, `IsMinimalAdmissible` | **Corrected.** The repository's definition is the *consequence* quoted on p. 335 (irreducible, with a monotone u.s.c. decomposition onto an arc whose elements have void interior), not Kuratowski's definition. The equivalence ([19, Theorem 3], [26, Theorem 10]) is not formalized and not needed: every type λ continuum the route uses is produced in the decomposition form (`hagopian75_exists_typeA'`, Lemma 4, Lemma 6). |
| "the decomposition of `M`" (p. 335) | the minimal admissible map; uniqueness `hagopian75_lemma3_unique` | Agrees. "`M/𝔇` is an arc" with `𝔇` monotone u.s.c. is a continuous monotone surjection `k : E → [0, 1]`; the orientation is fixed by naming the end set over `0`. |
| extension away; `𝔖(k⁻¹(0), E)`; `⋃𝔖` | `IsExtensionAway`; `{F \| IsExtensionAway E (layer k 0) F}`; `extUnion` | Agrees (the end set is normalized to the layer over `0`). `⋃(𝔖(k⁻¹(0), E) ∪ 𝔖(k⁻¹(1), E))` is `Rset k`. |
| essential subcontinuum of `E` (p. 336) | `IsEssential84` (new, `Hagopian84A.lean`) | Agrees with the commission: not `IsEssential` (essential to `R(E)`, 1976). |
| `W(x, ε)`; Lemma 1 | `Wset84`; `hagopian84_lemma1` (new; from `effros_homogeneous`) | There was no `Wset` in the repository; `hagopian75_lemma4` is the neighbourhood form. Lemma 1 is now proved for any compact homogeneous metric space. |
| Lemma 2 ([20, Theorem 13.8]) | `hagopian75_lemma1_hu` | Agrees, and stronger: every nondegenerate subcontinuum of `M`, `M` included, is unicoherent. |
| Lemma 3 | `hagopian76_lemma3` | Agrees. `Y = k⁻¹(s)` with `0 < s < 1` is "distinct from `k⁻¹(0)` and `k⁻¹(1)`" (the layers are disjoint and nonempty); `U = d⁻¹(u)` with any `u` (the repository drops `0 < u < 1`, which follows from the other hypotheses). |
| Lemmas 4, 5 | `hagopian76_lemma4`, `hagopian76_lemma5` | Agree. |
| Lemma 6 ([26, Theorem 8]) | `hagopian84_lemma6` (new) | Proved from Lemma 5 (`lsc_of_minimalAdmissible`), `isTypeA'_of_subcontinuum` and `minimalAdmissible_restrict`; Thomas's Theorem 8 is not needed. |
| Lemma 9 | `hagopian75_layer_homogeneous` | **Partial.** The repository covers the interior layers (`0 < s < 1`); Lemma 9 claims every element, end sets included. An end set of `E` is an interior layer of an extension of `E` (Lemma 4 with Lemma 6 / `ext_layers`), so the end sets follow; not formalized in this batch. |
| Lemma 11 ("paragraphs 2 through 11 in the proof of Lemma 6 of [11]") | `hagopian76_lemma6_X` (`Cl R(X, E)` indecomposable) | **Corrected.** The right 1976 version is the first part of Lemma 6, `hagopian76_lemma6_X` (one direction), not `hagopian76_lemma6` (`Cl R(E)`). With `N = M` this is `hagopian84_lemma11`. |
| chains, ordered refinement | `IsChain5`, `IsFree5`, `IsNormal5`, `RunsStraight`, `IsRegular5`, `IsOrderedRefinement5`, `Omega5`, `Delta5` (new) | **The 1976 definitions do not fit.** `IsPlaneChain` has links open in `R²`, any length; 1984 links are open in `M`, five of them. The 1976 "free relative to `M`" (`M ∩ Bd St G ⊂ Bd(G₁ ∪ Gₙ)`) differs from the 1984 "free" (`Bd ⋃𝔏 ⊂ Bd(L₁ ∪ L₅)∖Cl ⋃𝔏′`, boundaries in `M`). New definitions. |
| Moore 1962 [22, Theorem 44] (Lemma 12) | `exists_closed_split_of_no_connected` (`HPC/Plane/Fugate66BHU.lean`), used for the 1976 Lemma 8 (`H76Lemma8Sep.lean`) | Present, in the compact form. Lemma 12 applies it to `M∖(A ∪ B)` (compact, `A`, `B` open), as in the 1976 Lemma 8. |
| "paragraphs 1 and 2 in the proof of Theorem 1 of [10]" | `hagopian75_exists_typeA'` | Agrees. |

## C. The route of this project (commission 184 §1)

Let `M` be an indecomposable homogeneous plane continuum with a decomposable subcontinuum.

1. `M` is atriodic and hereditarily unicoherent (`hagopian75_lemma1`).
2. Theorem 1 with `N = M` gives `𝔇` (the named `Prop` `Hagopian84Decomp`: a monotone continuous
   surjection `q : M → Y`, fibres proper, `Y` homogeneous with an arc). Lemma 10 and claim (4) are
   not needed.
3. **Planarity** (proved, `exists_plane_quotient_of_monotone`): the plane is decomposed into the
   fibres of `q` and the points off `M` (`fibreSetoid`). The fibres are proper subcontinua of `M`, so
   they do not separate the plane (`no_proper_subcontinuum_separates`); upper semicontinuity comes
   from compactness alone (`fibre_usc`; the continuity of `𝔇` is not needed for it). Moore 1925
   Theorem 22 (`m25_theorem22`) then makes `Y` homeomorphic to a compact plane set.
4. `Y` is indecomposable (`indecomposable_of_monotone_image`), homogeneous, and contains an arc.
5. The arc step `NoArcIndecHomPlane` (Bing 1960) gives the contradiction
   (`hagopian76_theorem1_of_jones`, proved).

Nothing from Hagopian 1984 pp. 345–349 and nothing from the 1976 pp. 344–349 is used.

## D. The unargued steps (commission 184 §4, §5, §8)

Each is a candidate ledger entry; the outcome is recorded in `LEDGER.md`, section *Hagopian 1984 I*.

* **Lemma 7.** (a) "Since `M` is atriodic, it follows from (1) that there is a point `x` of `F` in
  `H∖k⁻¹(r)`": the triod would be `k⁻¹(r)` with three arms (the two sides of `k⁻¹(r)` in `H` and a
  piece of `F∖H`), if `F ⊄ H`; if `F ⊂ H` the point exists because `F ⊄ k⁻¹(r)` (`F∖E ≠ ∅`).
  Unargued. (b) "this contradicts the fact that `J` is irreducible between `x` and `k⁻¹(r)`":
  `J` is irreducible between `x` and *any point* of `k⁻¹(r)` (the end set) — this is the
  irreducibility of a type λ continuum between its end sets, which holds point-to-set
  (`isTypeA'_of_subcontinuum` gives it in `M`). (c) "Suppose that (2) is false. Then `F ∩ J` does not
  contain `k⁻¹(r)`": unargued; (2) false gives a point of `k⁻¹(r)` in `I∖F`, which is not in
  `F ∩ J`. Correct, one line missing.
* **Lemma 2 applied to unions** (`F ∪ J`, `N ∪ F`, `K ∪ L`): in the repository's `M` every
  nondegenerate subcontinuum is unicoherent (`hagopian75_lemma1_hu`), so properness is not needed.
  For a general atriodic `M` the unions must be proper; in Lemma 7 `F ∪ J ⊂ I ∪ H`, which is not
  argued to be proper.
* **Lemma 8.** "The quotient space `(E ∪ F)/𝔇` is the union of two arcs": unargued (it is the union
  of `E/𝔇` and `F/𝔇`, two arcs meeting in a connected set). "Since `M` is atriodic, `(E ∪ F)/𝔇` is
  atriodic": the monotone preimage of a triod is a triod — true for monotone maps (the preimage of a
  continuum is a continuum, `isContinuum_preimage_of_monotone`), not stated. "It follows from Lemma 2
  that `(E ∪ F)/𝔇` does not contain a simple closed curve", hence an arc: needs that an atriodic union
  of two arcs without a simple closed curve is an arc, unargued.
* **Lemma 12.** The three sentences listed by the commission are unargued; Moore 1962 Theorem 44 is
  available (§B).
* **Lemma 13.** (3)–(5) and the regularity paragraph: the hypotheses of Lemma 3 (`h[k⁻¹(r)]` misses
  the end sets of `g[E]`, and `g[k⁻¹(s)]` misses `h[k⁻¹(0) ∪ k⁻¹(1)]`) follow from the choice of `δ`
  (`r, s ∈ [x₂, x₁₃]` and the `½ρ` bound), but this is not said. (5) has a printing error
  (`g[k⁻¹(0, x₃ᵢ)]]`). The last paragraph ("there is an ε-homeomorphism `h` … such that `Cl K` is an
  essential subcontinuum of `h[E]`") needs that every component `K` of `⋃𝒫′` meets some `h[E]`, `h`
  a δ-homeomorphism: `⋃𝒫′ ⊂ ⋃𝔏′ ⊂ W(k⁻¹[[x₃, x₁₂]], δ)`, so every point of `K` is in some `h[E]`.
  One line missing, correct.
* **Lemmas 14, 15.** `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)` must be positive: `⋃Δ(𝒫)` is not closed, and
  positivity needs `Cl ⋃Δ(𝒫) ⊂ ⋃𝒫′`, which uses freeness and normality (a limit layer touching
  `Cl P₁` lies in `Bd P₁`, hence by freeness in `P₂`). Unargued. The hypotheses of Lemma 3 (the
  image `h[Z]` misses the end sets of `Cl Kᵢ`, which lie in `M∖⋃𝒫′`; the layer `Zᵢ` misses
  `h[ends of Cl K₀]`) are not checked in the text. "`{Zᵢ}` converges to `Z`": in the Hausdorff sense
  (`h[Z] = Zᵢ` with `h` an ε-homeomorphism gives Hausdorff distance `< ε`), which gives upper and
  lower semicontinuity at `Z`.
* **Lemma 16.** "Since `𝔇` is continuous (Lemma 5), `s ∉ S` and `s ≠ 1`": `S` is open in `[0, 1]`
  by lower semicontinuity (meeting three open links is an open condition on layers), so its infimum
  is not in it; `s ≠ 1` because `S ≠ ∅`. "Since `𝒫` is free, there exist a 3-linked subchain `𝔔` …":
  unargued. The final appeal to uniqueness: correct (`hagopian75_lemma3_unique`).
* **Theorem 1.** (i) "the end set of `Cl K(Z)` that is separated from `Z` in `Cl K(Z)` by `P₃`":
  `Z ∉ Δ(𝒫)` meets `Cl(P₁ ∪ P₅)`; by "runs straight" `Z` lies on one side of `P₃`, and `X(Z)` is the
  end set on the other side. Unargued, as the commission says. (ii) Lemma 11 is applied to
  `Cl K(Z) ⊂ h[E]`, not to `E`; with `N = M` this is harmless (Lemma 11 holds for every type λ
  continuum of `M`); for general `N` it needs `Cl K(Z) ⊂ N`, i.e. `h[N]` in place of `N` or Lemma 10.
  (iii) "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`": the commission's reading is right — if not,
  `Cl ⋃𝔖 ∩ P₃` would be a nonempty open subset of `Cl ⋃𝔖` inside `Cl K(Z)`, a proper subcontinuum
  of the indecomposable `Cl ⋃𝔖`, which has void interior in it. (iv) "Hence there is an essential
  subcontinuum `J(Z)`…": from Lemmas 7 and 16; unargued detail. (v) The cover `𝔅` and the
  disjointness of `𝔇`: as printed. (vi) "Since `M/𝔇` is an atriodic homogeneous continuum that
  contains an arc" (p. 344): the arc is not argued (commission §5.7; report §5).
* **p. 346.** "since the elements of `𝔇` are tree-like, if `M` is planar, then `M/𝔇` is planar
  [21]": Moore 1925 needs elements that do not separate the plane; that a tree-like continuum does not
  separate the plane is not stated there. The route uses `no_proper_subcontinuum_separates` instead.

## E. Small slips

* "opens sets" (p. 333), "ε-circluar" (p. 334), "ε-homomorphisms" (p. 338), "subcontinuum `H` and
  `K`" (p. 335, for "subcontinua").
* "In 1968 F. B. Jones [16]" (p. 346) against "(1969)" in the reference list (p. 347).
* Lemma 13 (5): `g[k⁻¹(0, x₃ᵢ)]]`, unbalanced brackets.

## F. Bing 1960, the arc step (commission 184 §6, reconnaissance only)

Bing's proof of Theorem 1 ("The simple closed curve is the only homogeneous bounded plane continuum
that contains an arc"), in the indecomposable case. Statements located from the PDF; no part is
formalized.

| Bing 1960 | uses | repository |
| --- | --- | --- |
| §2 Property 1 (`M` not locally connected) | Mazurkiewicz 1924 (homogeneous locally connected plane continuum is a simple closed curve) | Not present (Mazurkiewicz 1929 is in `doc/sources/`, a different paper). In the indecomposable case Property 1 is immediate (an indecomposable continuum is not locally connected); not formalized. |
| Property 2 (not connected im kleinen anywhere) | Property 1, homogeneity | Not present. |
| Property 3 (open set with uncountably many components) and Theorem 2 | a Baire argument | Not present. |
| Property 4 (no simple triod) | Theorem 4 of §4 | In the indecomposable case: atriodicity, `hagopian75_lemma1` (no triod at all). |
| Property 5 (no simple closed curve) | Cohen 1951 | In the indecomposable case: hereditary unicoherence, `hagopian75_lemma1_hu`. |
| §3 Properties 6–13 (arc components: rays, the closure of an arc component is homogeneous) | Properties 4, 5, homogeneity | Not present; the composant machinery (`uncountable_composants`) is related but not the same. |
| §4 Theorems 3, 3′, 4, 5 (collections of arcs in the plane; arcs converging from opposite sides; accessibility) | plane topology | Not present. |
| §5 Properties 14–16 (the reduced continuum `M′`: every proper subcontinuum is an arc; `M′` indecomposable) | §3, §4 | Not present. |
| §6 Properties 17–19 (chains following arcs; accessibility from a complementary domain) | §5 | Not present; `exists_accessible_point` (`H76Setup.lean`) gives an accessible point. |
| §7 Theorem 6 (no folded sequence of arcs converging to an arc) | homogeneity, chains | Not present. |
| §9 Theorem 8 (homeomorphisms near the identity sending `p` into distinct composants) | separability of the homeomorphism group | Close to `effros_homogeneous` and `uncountable_composants`; not present in this form. |
| §10 Property 20 (a folded sequence in `M′`) and the Special Separating Property | §§4–9, Jordan curve theorem | Not present. |

Conclusion: of Bing's proof only Properties 4 and 5 (in the indecomposable case) and the Effros-type
input are in the repository. The remainder (§§3–7, 9–10) is a separate project; Jones 1975 (not in
the repository) may be shorter and should be read first.

## G. Lemma 7 and the two-sided extension (batch 185)

Formalized in `HPC/Hagopian/H84TwoSided.lean`, `HPC/Hagopian/H84Lemma7.lean`,
`HPC/Hagopian/H84Rigid.lean`; statements in `HPC/Hagopian/Hagopian76AC.lean`. Ledger: *Hagopian 1984
II*, H84.15–H84.16.

**The two-sided extension** (`hagopian84_two_sided`; the `H` of the proof of Lemma 7, "By Lemma 4").
The route of commission 185 §1, with one change in step 3.
1. Lemma 4 gives `F₁ ⊋ E` away from `X = k⁻¹(0)` and `F₂ ⊋ E` away from `Z = k⁻¹(1)`; `E` is an
   initial segment of each.
2. `F₁ ∩ F₂ = E` (`ext_inter_ext_subset`): the intersection is a continuum (hereditary
   unicoherence); a point of it in `F₁∖E` would drag the initial segment of `F₁` along, reaching
   points of `F₂∖E` near `Z`, while the closure of `F₂∖E` meets `E` only in `X`.
3. `H = F₁ ∪ T₂`, where `T₂` is the tail of `F₂` beyond `X` (`F₂∖E` together with `X`): `F₁` and
   `T₂` are type λ continua meeting exactly in the common end set `X`. The gluing lemma
   (`glue_minimalAdmissible`) puts the layers of `T₂` on `[0, ½]` and those of `F₁` on `[½, 1]`; it
   is admissible, its layers have void interior (`interior_layer_of_subset_empty`), and `H` is
   irreducible between its end sets by hereditary unicoherence (step 4 of the commission).
4. `E` is essential in `H` and misses both end sets.

**Lemma 7** (`hagopian84_lemma7`; also the named `Prop` `Hagopian84Lemma7`, `hagopian84Lemma7_holds`).
Not the printed proof. Let `(H, d_H) ⊇ E` and `(I, d_I) ⊇ F` be the two-sided extensions, and
`K = H ∩ F`.
* *`K` inside one layer of `H`.* Then that layer is `k⁻¹(r)`, an interior layer of `H` (Lemma 6),
  and `F ⊄ H` (else `F ⊆ k⁻¹(r) ⊆ E`, against `F∖E ≠ ∅`), so `F` is a third arm at it: a triod
  (`no_arm_at_interior_layer`). Impossible.
* *`K` meets two layers of `H` and two layers of `F`.* Lemma 6 (`hagopian84_lemma6`), applied twice
  (`layer_common_of_essential`), makes the layers agree on `K`; in particular `k⁻¹(r)` is a layer
  of `F`.
* *`K` meets two layers of `H` inside one layer `Y` of `F`.* `Y` is an interior layer of `I`. Then
  `H ∩ I ⊆ Y` (otherwise Lemma 6 twice would make two distinct layers of `H` inside `K ⊆ Y` both
  equal to the layer `Y` of `I`), and `H` is a third arm at `Y` (a point of `E∖F` lies off `Y`).
  Impossible (`no_arm_at_interior_layer`).
The case split itself is `two_layers_or_subset`.
The points `x`, `y` and the continua `J`, `K`, `L` of the printed proof are not used; the three
atriodicity steps of H84.4 are replaced by `no_arm_at_interior_layer`.

**Rigidity and runs** (commission 185 §3.1–§3.2). `layers_agree`: if `E ∩ G` meets two layers of `E`,
either `E` lies in one layer of `G` (the only degenerate case, forcing `E ⊆ G`), or
`E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a′, b′]]` with matching layers. `translate_run`, `translate_run_right`:
an end of the common segment that is not an end of `E` is an end layer of `G`, by atriodicity.

**Effect on the route of §C.** Lemma 7 is no longer an obstruction. Lemma 8 still needs the gluing
of two decompositions onto "the union of two arcs" and "atriodic, no simple closed curve, hence an
arc" (H84.5); Lemmas 12–16, the arc in `M/𝔇` and `NoArcIndecHomPlane` are as in batch 184.

## H. The quotient package; Lemmas 12–16 (batch 186)

Statements in `HPC/Hagopian/Hagopian84B.lean`; proofs in `H84Fold.lean`, `H84Delta.lean`,
`H84Lemma12.lean`, `H84Lemma1415.lean`. Ledger entries H84.17–H84.22.

**The package (§2 of commission 186).** `IsJonesDecomp84 r`: upper semicontinuous, connected classes,
no class `M`, respected by `δ`-homeomorphisms for some `δ > 0`, and an arc of classes
(`c : C → [0, 1]` continuous onto, `c x = c y ↔ r x y`). `hagopian84Decomp_of_package`: the quotient
`M/r` is compact metrizable (`t2Space_quotient`, `metrizableSpace_quotient`); fibres are the classes;
homogeneity: compositions of `δ`-homeomorphisms respect `r` both ways (the inverse of a
`δ`-homeomorphism is one, `dist_symm_lt_of_small`), and their orbits are clopen
(`exists_comp_small_homeo`: open by `hagopian84_lemma1`, the complement open by the same), so one
orbit; `exists_homeomorph_quotient` descends the homeomorphism. Arc: `c` is a closed map from a
compact space, hence a quotient map; the composite `C → M → M/r` factors through a continuous
injection `φ : [0, 1] → M/r`, a closed embedding.

**The chain (Lemma 13, open).** `WsetOf S δ = ⋃_{x ∈ S} Wset84 x δ`, `chainLinks84 k x δ i =
W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`. Shapes chosen for `chainLinks84_runsStraight` (numbers `x`, `δ` exist;
normal chain in `M∖A`; `Cl(L 0 ∪ L 4) ⊆ B`; every `δ`-translate runs straight with end layers in
`L 0∖Cl L 1`, `L 4∖Cl L 3`) and `chainLinks84_regular` (regular; closures of components of `⋃𝔏′`
essential in translates), written in the commented-out blocks. Not formalized: (1)–(4) and the
geometry of the fold.

**The fold.** `exists_fold`: five open sets `V i ⊆ [0, 1]`, covering, non-adjacent ones disjoint,
`0 ∈ V 0∖V 1`, `1 ∈ V 4∖V 3`; if one is not an interval there are `r < s < t` and adjacent `p`, `q`
with `s ∈ V p`, `r, t ∈ V q∖V p`. The proof is a sweep (`FoldAux.sweep_step`): with no fold, if
`a ∈ V p`, no point `< a` lies in a later set and no point `≥ a` in an earlier one, then `V p` is an
interval from `a` and the first point after it outside `V p` lies in `V (p + 1)` with the same two
properties (`left_end`, `right_end` locate the last/first points outside `V p`, which lie in
neighbours by openness and covering). This covers both the printed case and its mirror.

**Lemma 12.** `A = L 0∖Cl L 1`, `B = L 4∖Cl L 3`; Moore 44 (`exists_closed_split_of_no_connected`)
in the compact set `M∖(A ∪ B)` splits it into disjoint closed `K₁ ⊇ E∖(A ∪ B)` and
`K₂ ⊇ M∖⋃𝔏`; the refinement is `refineChain L K₂ = (L 0, L 1∖K₂, L 2∖K₂, L 3∖K₂, L 4)`. Hypothesis
of Moore 44: a connected set meeting `E∖(A ∪ B)` and `M∖⋃𝔏` inside `M∖(A ∪ B)` has a closure that is
a continuum meeting `E` and missing both end layers, hence inside `E` (`subset_of_meets_avoids`),
absurd. Running straight carries over (`runsStraight_refine`); components of `⋃𝒫′` are components
of `⋃𝔏′` (`⋃𝒫′ = midUnion L ∩ K₁` is clopen in `midUnion L`); freeness by the commission's route.

**`Δ(𝒫)` (§4.1).** `delta5_partition`: a layer through a point outside `Cl Pᵢ` misses `Cl Pᵢ`
(`layer_disjoint_closure_of_mem`); a member of `Δ(𝒫)` lies in its component
(`delta_subset_component`: `K ∪ Z` lies between `K` and `Cl K`), so meeting members come from one
component, where the decomposition is unique. `delta5_dist_pos`: `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′`
(`closure_delta_subset_mid`, by freeness), then compactness.

**Lemma 14.** `delta_translate_eq`: for an `ε'`-homeomorphism (`ε' ≤ η` of positivity) taking
`z ∈ Z` to `z' ∈ Z'`, `h[Z] = Z'` by `hagopian76_lemma3`; its hypotheses (the end layers of both
closures lie outside `⋃𝒫′`, `endlayers_not_mid`, hence at distance `≥ η`) are checked explicitly.

**Lemma 15.** `ε` below `η` and below half the distances between non-adjacent link closures
(`exists_far_links`). Then `h[Z]` lies in one component `K′`; `h[Cl K] ∩ Cl K′` meets two layers of
`h[Cl K]` (else `no_arm_at_interior_layer`); `layers_agree` makes `h[Z]` a layer of `Cl K′`; the
degenerate case (`h[Cl K]` in one layer of `Cl K′`) is impossible because `h` keeps the end layers
of `Cl K` near `P 0` and `P 4`, and a layer of `Cl K′` meets no two non-adjacent links.

**The arc (§4.4).** `exists_interval_in_delta`: `Cl K` meets `P 2`; the layer through such a point
lies in `P 2` (`layer_subset_link`), hence misses `Cl(P 0 ∪ P 4)`; the parameters of layers inside
`P 2` form an open set (upper semicontinuity), containing `[a, b]`, `a < b`.

**Lemma 16 (open).** Obstruction in `OPEN.md` and H84.21: the 3-linked subchain sentence. Available:
`s > 0`, `s ∉ S`, uniqueness.

**Effect on the route of §C.** For `Hagopian84Decomp` it remains to prove: Lemma 13 (through
`chainLinks84_runsStraight`), Lemma 16 or its weaker form, and the construction of pp. 343–344
producing an `IsJonesDecomp84` (fields: usc from Lemma 14, invariance from Lemma 15, the arc from
`exists_interval_in_delta`).

## I. Lemma 13; Lemma 16′; the bridge; `𝒫(Z)` and the cover (batch 187)

Files: `HPC/Hagopian/Hagopian84C.lean` (statements), `H84Chain13.lean`, `H84Runs13.lean`,
`H84Regular13.lean`, `H84Lemma13.lean` (Lemma 13), `H84Strand.lean` (Lemma 16′), `H84Bridge.lean`
(the bridge, `Z ∈ Δ(𝒫(Z))`), `H84Cover.lean` (the cover). Report: `doc/batches/REPORT-batch187.md`.

**Lemma 13, the numbers.** `exists_x84`: `x₃` and `x₁₂` from the openness of the parameters whose
layer lies in `B` (upper semicontinuity), the other `xⱼ` evenly spaced (`xf84`). `δ` is below the
radius of `chainLinks84_chain_aux` (non-adjacent segments, the end layers against the segments of
`L 1` and `L 3`, `A`, `B`), below `ε`, and below half of the fifteen gap radii
`ρ(k⁻¹[[0, xⱼ]], k⁻¹[[xⱼ₊₁, 1]])`, `0 ≤ j ≤ 14` (`exists_gap84`; Hagopian uses `1 ≤ j ≤ 13`, which
suffices with his finer bookkeeping; the extra two cost nothing).

**(3)** (`link_dichotomy84`). If `h[k⁻¹(r)]` meets `L i` at `h(z) = g(w)`, `w` over `[x₃ᵢ, x₃ᵢ₊₃]`,
then `dist(z, w) < 2δ`, so no gap `[xⱼ, xⱼ₊₁]` separates `r` from `s = k(w)`. If moreover `r` is not
over `[x₃ᵢ, x₃ᵢ₊₃]`, both lie in `[x₁, x₁₄]` (`params_inner84`, pure order), which gives the end-set
hypotheses of Lemma 3 for `h⁻¹ ∘ g` (again through the gaps `j = 0` and `j = 14`); Lemma 3 gives
`g[k⁻¹(s)] = h[k⁻¹(r)]`, inside `L i`. No uniform continuity is used (commission 187 §2.1).

**(4)** (`layer_frontier84`). As commission 187 §2.2: Effros with `η = min(ρ(q, Lᵢ), δ − max
dist(v, h v))`, `f(p) ∈ Lᵢ`, `f ∘ h` a `δ`-homeomorphism, (3) for it.

**(5)** (`layer_convex84`, `no_fold84`). The parameter sets `V i = {u : h[k⁻¹(u)] ⊆ L i}` are open
(through (3) and `isOpen_params_meeting`), cover, non-adjacent ones are disjoint, `0 ∈ V 0 ∖ V 1`,
`1 ∈ V 4 ∖ V 3`. If one is not an interval, `exists_fold` gives `r < s < t` with `s ∈ V p`,
`r, t ∈ V q ∖ V p`, `q = p ± 1`. Kind D (`q = p + 1`): `C = g[k⁻¹[[0, x₃ₚ₊₃]]]` lies in
`L 0 ∪ ⋯ ∪ L p` (`mem_link_le84`), so it misses the end layers `h[k⁻¹(r)]`, `h[k⁻¹(t)]` (which lie in
`L q` and miss `L p`); it meets `h[k⁻¹[[r, t]]]` at `g(w) = h(z)`; atriodicity
(`subset_of_meets_avoids`, with the restricted map and `exists_image_map`) puts `C` inside. A point
of `g[k⁻¹(0)]` is then `h(z′)` with `k z′ ∈ [r, t]`, and the gap `j = 0` gives `k z′ < x₁`; so
`r < x₁`, `h[k⁻¹(r)] ⊆ L 0`, and `L 0 ∩ L q ≠ ∅` forces `q = 1`, `p = 0`, against `r ∉ V p`. Kind U
is the mirror image (`g[k⁻¹[[x₃ₚ, 1]]]`, gap `j = 14`, `p = 4`).

**Regularity** (`strand_of_runsStraight84`, general: any type λ `(G, b)` running straight through a
normal chain with end layers in `L 0 ∖ Cl L 1`, `L 4 ∖ Cl L 3`). `Cl K` misses the end layers
(normality), so `Cl K ⊆ G`. The layers over a short interval of parameters at `y` form a connected
subset of `⋃𝔏′`, so `Cl K` is essential, `Cl K = b⁻¹[[a, c]]` (Lemma 6). `a`, `c` are not in
`W = V 1 ∪ V 2 ∪ V 3`: otherwise the layer `b⁻¹(a)` lies in `K` (`K ∪ b⁻¹(a)` is between `K` and
`Cl K`), and the layers just below `a` would join `K`. So `a, c ∈ V 0 ∪ V 4`. If `a ∈ V 4`, then
`[a, 1] ⊆ V 4`, the parameter of `y` is in `V 3`, `V 3 ⊆ (a, c) ⊆ V 4`, so `V 2 ∩ V 3 = ∅`, and
`[0, 1]` splits into the disjoint open sets `V 0 ∪ V 1 ∪ V 2` and `V 3 ∪ V 4`
(`params_adjacent_meet84`); `c ∈ V 0` likewise. The restricted map then runs straight.

**Assembly** (`hagopian84_lemma13_aux`): as the batch-186 note; `E` runs straight through `𝔏` by
the identity in (6) (`translate_runsStraight84` takes the domain as a set equal to `h[E]`).

**Lemma 16′** (`strand_layer_of_extension`), as commission 187 §3, with step 3 by a single limit
point (closedness of the parameters whose layer meets `Cl P 2`); Lemma 14 not needed. **Lemma 16 as
printed** follows (normality added): `d⁻¹(0) = c⁻¹(0)` misses `⋃𝒫′`; a layer meeting three
consecutive links meets `⋃𝒫′`, so it is a strand layer, which lies in each link it meets, and two of
the three links are disjoint.

**The bridge** (`exists_bridge84`). `K(Z)` read from the definition of `Ω(𝒫)` (the component whose
closure has `Z` as a layer); `Z ⊆ Cl P 0` or `Z ⊆ Cl P 4` and `Z` misses `Cl P 2`
(`omega_not_delta_side`); `X(Z)` the far end layer; an extension meeting `P 2 ∖ K(Z)` exists
(`exists_ext_meeting_P2`: Lemma 11 and strict extensions); `J(Z)` between the last parameter below
`z₀` and the first above whose layers meet `Cl P 2`, with Lemma 16′ making the end layers members of
`Δ(𝒫)`. The printed positions of the end sets relative to `K(Z)` are not claimed (not needed).

**`𝒫(Z)`** (`exists_chainZ84`): Lemma 13 for `J(Z)`, `A = Cl P 2`, `B = ⋃Δ(𝒫)`; `Z ∈ Δ(𝒫(Z))` by
`mem_delta_of_bridge_chain` (`Z` misses `B ⊇ Cl(P(Z) 0 ∪ P(Z) 4)`, lies in `⋃𝒫(Z)′`; `j⁻¹(0)` misses
`⋃𝒫(Z)′`; Lemma 16′ for `𝒫(Z)`).

**The cover** (`exists_finite_cover84`, `hagopian84_cover`). The printed closedness of `⋃𝔅` is not
used: `C = Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` is compact; each of its points lies in `⋃𝒫′ ∩ Cl(P 0 ∪ P 4)`, so the
layer `Z` through it of its strand is in `Ω(𝒫) ∖ Δ(𝒫)` and the point is in `⋃Δ(𝒫(Z))`; finitely many
of these open sets cover `C`; their union `U` with `⋃Δ(𝒫)` is open, and closed because
`Cl ⋃Δ(𝒫(Z)) ⊆ ⋃Δ(𝒫(Z)) ∪ Cl(P(Z) 0 ∪ P(Z) 4)` (freeness) and (3); `M` is connected.

**Effect on the route of §C.** For `Hagopian84Decomp` it remains to prove: the relation `𝔇` and its
disjointness, claims (5)–(6), and the fields of `IsJonesDecomp84` (usc from Lemma 14, invariance
from Lemma 15, the arc from `exists_interval_in_delta`), then `hagopian84_decomp`.

## J. `𝔇`; claims (5)–(6); the package (batch 188)

File: `HPC/Hagopian/Hagopian84D.lean`. Report: `doc/batches/REPORT-batch188.md`.

**The transfer lemma** (`omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid`). `𝒫` normal regular,
`Q` free normal regular with `⋃Q ⊆ M∖Cl P₃` (Hagopian's (2)); `Z ∈ Ω(𝒫)` through `z ∈ ⋃Q′`. Then `Z`
is the layer through `z` of the strand of `Q` through `z`, and `Z ∈ Δ(Q)` if `z ∉ Cl(Q₁ ∪ Q₅)`.
Proof: `Z = c⁻¹(r)` for the map `c` running straight through `𝒫` (`exists_layer_eq_of_minimal`); the
strand of `Z` meets `P₃`, in a layer `c⁻¹(s) ⊆ P₃` (`layer_subset_link`); `z ∈ ⋃Q` misses `Cl P₃`, so
`s ≠ r`; the piece `c⁻¹[[r, s]]` (or `[[s, r]]`), reparametrized by `minimalAdmissible_restrict` and,
if `r < s`, reversed (`exists_piece_between84`), has end layers `c⁻¹(s)` (missing `⋃Q′`) and `Z`;
Lemma 16′ for `Q` with `u = 1`, `y = z`. Uses (2), not (3).

**Disjointness** (`CoverData84.members_disjoint`). (a) both in `Δ(𝒫)`: `delta5_partition`. (b) `A ∈
Δ(𝒫(Zᵢ))`, `B ∈ Δ(𝒫)`: the common point lies in `⋃𝒫(Zᵢ)′ ∖ Cl(P(Zᵢ)₁ ∪ P(Zᵢ)₅)`, so `B ∈ Δ(𝒫(Zᵢ))`
by the transfer lemma, and `delta5_partition` for `𝒫(Zᵢ)` (`CoverData84.eq_of_meet_delta`). (c) both
from chains `𝒫(Zᵢ)`, `𝒫(Zⱼ)`: if either meets `⋃Δ(𝒫)`, (b) twice; otherwise Lemma 3 with `h` the
identity, the maps of `delta_regular_rep` (interior layers; end layers in `Cl(·₁ ∪ ·₅) ⊆ ⋃Δ(𝒫)` by
(3)).

**(5)** `i = 0` (`CoverData84.omega_subset_members`): a member of `Ω(𝒫)∖Δ(𝒫)` lies in `Cl P₁` or
`Cl P₅` (`omega_not_delta_side`), so a point of it is not in `⋃Δ(𝒫)` and the cover puts it in some
`⋃Δ(𝒫(Zᵢ))`; the transfer lemma. `i ≥ 1`, members `W ⊆ ⋃𝒫(Zᵢ)′` (`CoverData84.omega_mem_members`):
if `W ∉ Δ(Q)`, `W ⊆ Cl(Q₁ ∪ Q₅) ⊆ ⋃Δ(𝒫)`; the member `Y ∈ Δ(𝒫)` through `w ∈ W` is the layer through
`w` of the strand of `Q` through `w` (transfer lemma); `W` lies in the component `K′` of `⋃Q′` it
comes from (`K′ ∪ W` lies between `K′` and `Cl K′`, inside `⋃Q′`), so `K′` is the component through
`w`; `layer_eq_of_common_point` gives `W = Y`.

**(6)** (`CoverData84.invariant`). For each of the finitely many chains `R`, `δ_R = min(ε_R, η_R)`
with `ε_R` from Lemma 15 and `η_R` from `delta5_dist_pos` (`delta_translate_small84`): a
`δ_R`-homeomorphism maps `D ∈ Δ(R)` onto a member of `Ω(R)` inside `⋃R′`; then (5). The common `δ`
over a `Finset` is `exists_pos_forall_finset84`.

**The package** (`CoverData84.isJonesDecomp`). Closed classes: members are layers of compact type λ
continua (`isClosed_layer`). U.s.c.: `{z : cls z ⊆ U}` is open, by Lemma 14 at `z₀` and the openness
of `⋃Δ(R)`. Connected: layers. Proper: a member of `Δ(R)` misses `R₁ ≠ ∅`. Invariance: (6). Arc:
`exists_interval_in_delta` gives `[a, b]` with every layer of a strand of `𝒫` in `Δ(𝒫)`; the map of
`minimalAdmissible_restrict` on `c⁻¹[[a, b]]` has fibres that are members of `𝔇`, hence the traces
of the classes. `hagopian84_decomp` is `hagopian84Decomp_of_package` with the setoid of
`exists_coverData84`; `hagopian76_theorem1_jones` is `hagopian76_theorem1_of_jones hagopian84_decomp`.

**The printed closedness of `⋃𝔅`** (`sUnion_cover84_eq_univ`): for any choice as in
`exists_finite_cover84`, `⋃𝔅 = M`, a corollary of the finite cover.
