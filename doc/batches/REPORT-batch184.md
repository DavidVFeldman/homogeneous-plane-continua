Commission read: `doc/batches/COMMISSION-batch184.md` ("Commission: batch 184 — Part E, Hagopian 1976 XXIX: Theorem 1 by Jones's plan (Hagopian 1984)").

# Report, batch 184

## 0. Summary, omissions

The 1984 route is started. The assembly of Jones's plan is **proved**: `Hagopian76Thm1` follows from
the two named `Prop`s `Hagopian84Decomp` (Theorem 1 of 1984 with `N = M`) and `NoArcIndecHomPlane`
(Bing 1960), through a new plane-quotient theorem (Moore 1925 Theorem 22). Hagopian 1975 Theorem 1 is
proved without the hypothesis `hnd`, from `NoArcIndecHomPlane`. Of §4, Lemmas 1, 6 and 11 (`N = M`)
are proved; Lemmas 7, 8, 10, 12–16 and Theorem 1 with `N = M` are open, each with its obstruction
(§4, §5, `OPEN.md`). No `sorry` is in any declaration; open statements are commented out at the end
of `HPC/Hagopian/Hagopian84A.lean`. Fourteen ledger checks (H84.1–H84.14); no statement refuted.

Status lines:
* STATUS: §2 transcription and dictionary proved (done; `doc/notes/hagopian84.md` §§A–B)
* STATUS: `hagopian76_theorem1_of_jones` proved
* STATUS: `hagopian75_theorem1_of_noArc` proved
* STATUS: Lemma 1 proved; Lemma 6 proved; Lemma 11 (`N = M`) proved
* STATUS: Lemma 7 open (two-sided extension; unargued atriodicity steps)
* STATUS: Lemma 8 open (Lemma 7; "two arcs, atriodic, no closed curve ⇒ arc")
* STATUS: Lemma 10 open (not attempted; not needed with `N = M`)
* STATUS: Lemma 12 open (unargued atriodicity steps feeding Moore 1962 Theorem 44)
* STATUS: Lemma 13 open (Lemma 12; hypotheses of Lemma 3 unchecked)
* STATUS: Lemmas 14, 15 open (positivity of `½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`; hypotheses of Lemma 3)
* STATUS: Lemma 16 open (existence of `𝔔`, `t`, `w` from freeness unargued)
* STATUS: Theorem 1 with `N = M` (`Hagopian84Decomp`) open (Lemmas 7, 8, 13–16)
* STATUS: §6 Bing 1960 reconnaissance done (`doc/notes/hagopian84.md` §F)

**Omissions** (asked for, not done):
* Lemmas 7, 8, 12–16 are not proved; their statements are given (commented out) with obstructions.
  Reason: each depends on unargued steps that need new infrastructure (the two-sided extension,
  quotients of unions of type λ continua, the analysis of 5-link chains in `M`), more than one batch.
* Lemma 10: not attempted (optional; trivial for `N = M`).
* `hagopian84_quotient_arc` (§5.7): no Lean statement; it depends on the decomposition of Theorem 1,
  which is not constructed. The argument is in §5.
* Lemma 9 at the end sets (H84.3): not formalized; the route needs Lemma 9 only for the remark on the
  elements of `𝔇`, not for `Hagopian84Decomp`.
* The transcription (§A of the notes) was spot-checked against the 200-dpi page images on pp. 336,
  343, 346 line by line, and read against the images elsewhere; not every page was re-compared line by
  line in this batch.

**Setting chosen** (commission §4): the plane one. `M : Set Pt` compact, connected, homogeneous,
indecomposable; atriodicity and hereditary unicoherence from `hagopian75_lemma1`, `hagopian75_lemma1_hu`.

**Shape changes.**
* `Hagopian84Decomp`: unchanged from the skeleton.
* `exists_plane_quotient_of_monotone`, `indecomposable_of_monotone_image`,
  `hagopian75_theorem1_of_noArc`, `hagopian84_lemma6`: the skeleton had `True`; the shapes are recorded
  at each statement (docstring "*Shape*") and in §3–§4 below.
* `hagopian84_lemma1`: for any compact homogeneous metric space and any real `ε` (for `ε ≤ 0` the set
  is empty).
* `hagopian84_lemma11`: only `N = M` (the general `N` needs Lemma 10).
* Lemmas 7–16: commented-out shapes as in the file; Lemma 14 states continuity as Hausdorff closeness
  of nearby elements.

## 1. Files

* `HPC/Hagopian/H84Quot.lean` (new): monotone maps (`isPreconnected_preimage_of_monotone`,
  `isContinuum_preimage_of_monotone`, `isDecomposableSpace_of_monotone_image`) and the plane
  decomposition by fibres (`fibreKey`, `fibreSetoid`, `fibre_usc`, `fibreSetoid_mooreDecomp`,
  `exists_plane_quotient_of_monotone_aux`).
* `HPC/Hagopian/Hagopian84A.lean` (the skeleton, filled): the named `Prop`s, the assembly, the
  definitions of §3 of the paper, Lemmas 1, 6, 11, and the open statements.
* `doc/notes/hagopian84.md`: §A transcription, §B dictionary, §C route, §D unargued steps, §E slips,
  §F Bing 1960.
* `HPC.lean` (import), `Axioms.lean`, `axioms.txt`, `README.md`, `LEDGER.md`, `OPEN.md`.
* Uploads moved: `doc/batches/COMMISSION-batch184.md`, `doc/batches/skeletons/Hagopian84A.lean`,
  `doc/sources/hagopian1984.pdf`.

## 2. Transcription and dictionary

`doc/notes/hagopian84.md` §A transcribes the §2 and §3 definitions, Lemmas 1–16 with proofs, Theorem
1 with proof, Theorem 2, and the Corollary 3 paragraph. The commission's transcription of p. 346
agrees with the page image word for word. §B checks the commission's dictionary; corrections:
* **type λ**: the repository's `IsTypeA'`/`IsMinimalAdmissible` is the decomposition form quoted on
  p. 335, not Kuratowski's definition; the route only needs the decomposition form.
* **`W(x, ε)`**: there was no `Wset`; new `Wset84` and `hagopian84_lemma1`.
* **Lemma 6**: proved directly (`hagopian84_lemma6`), not via Thomas's Theorem 8.
* **Lemma 9**: `hagopian75_layer_homogeneous` covers only interior layers (H84.3).
* **Lemma 11**: the right 1976 version is `hagopian76_lemma6_X`, not `hagopian76_lemma6`.
* **chains**: the 1976 definitions do not fit (links open in `R²`, any length, a different "free");
  new `IsChain5`, `IsFree5`, `IsNormal5`, `RunsStraight`, `IsRegular5`, `IsOrderedRefinement5`,
  `Omega5`, `Delta5`.
* **Moore 1962 Theorem 44**: present as `exists_closed_split_of_no_connected`.

## 3. The assembly (proved)

* **`exists_plane_quotient_of_monotone`** (piece 1). `M` a homogeneous indecomposable plane continuum,
  `q : M → Y` continuous onto a compact Hausdorff space, fibres connected and `≠ M`. Then some compact
  `Q ⊆ R²` has `Y ≃ₜ Q`. Proof: the plane is decomposed into the fibres of `q` and the points off `M`
  (`fibreSetoid`). The fibres are proper subcontinua of `M`, so they do not separate the plane
  (`no_proper_subcontinuum_separates`); the decomposition is upper semicontinuous by compactness alone
  (`fibre_usc`); Moore 1925 Theorem 22 (`m25_theorem22`) makes the quotient the plane; `Y` maps
  homeomorphically onto the image of `M`. The continuity of `𝔇` is not needed for this step.
* **`indecomposable_of_monotone_image`** (piece 2), with `isContinuum_preimage_of_monotone`: the
  preimage of a subcontinuum under a closed monotone map is a subcontinuum.
* **`hagopian76_theorem1_of_jones`** (piece 3): by contradiction, `Q` is a homogeneous indecomposable
  plane continuum containing an arc.
* **`hagopian75_theorem1_of_noArc`**: if some interior layer is nondegenerate,
  `hagopian75_theorem1_of_layer`; otherwise `exists_arc_of_degenerate_layers` gives an arc in `M`,
  against `NoArcIndecHomPlane` applied to `M`.

## 4. Lemmas 6–8, 12–16 (and 1, 10, 11)

| Lemma | outcome | obstruction / proof |
| --- | --- | --- |
| 1 | **proved** (`hagopian84_lemma1`) | Effros (`effros_homogeneous`) with the slack of a given ε-homeomorphism. |
| 6 | **proved** (`hagopian84_lemma6`) | Lemma 5 + `isTypeA'_of_subcontinuum` + `minimalAdmissible_restrict` + uniqueness. |
| 7 | open | two-sided extension (Lemma 4 used to put `E`, `F` inside `H`, `I` missing both end sets), open since batch 158; three unargued atriodicity steps (H84.4). |
| 8 | open | Lemma 7; the glued decomposition of `E ∪ F`; "atriodic union of two arcs without a simple closed curve is an arc" (H84.5). |
| 10 | open, not attempted | not needed with `N = M`. |
| 11 | **proved for `N = M`** (`hagopian84_lemma11`) | `hagopian76_lemma6_X`. |
| 12 | open | the hypothesis of Moore 1962 Theorem 44 rests on two unargued atriodicity steps; `𝒫` free, normal, regular unargued (H84.6). |
| 13 | open | Lemma 12; Lemma 3's hypotheses in (3)–(5) unchecked; the regularity sentence (H84.7). |
| 14 | open | `½ρ(⋃Δ(𝒫), M∖⋃𝒫′) > 0` unargued; Lemma 3's hypotheses unchecked (H84.8). |
| 15 | open | as Lemma 14. |
| 16 | open | existence of `𝔔`, `t`, `w` from freeness unargued (H84.9). |

The unargued steps listed by the commission are each recorded in `doc/notes/hagopian84.md` §D and in
the ledger. Lemma 2 applied to unions (commission §4.2) is automatic in the plane setting, since
every nondegenerate subcontinuum of `M` is unicoherent (`hagopian75_lemma1_hu`); for a general
atriodic `M`, properness of `F ∪ J ⊂ I ∪ H` in Lemma 7 is not argued (H84.2).

## 5. Theorem 1 with `N = M`: open

Outcome: **open**; the proved conditional form is `hagopian76_theorem1_of_jones`. The steps of
pp. 342–345 (commission §5):
1. The chain: `hagopian75_exists_typeA'` gives `E`; `𝒫` needs Lemma 13 (open).
2. `K(Z)`, `X(Z)`, `F(Z)`, `J(Z)`, `𝒫(Z)`: (i) `X(Z)` unargued; (ii) Lemma 11 is applied to
   `Cl K(Z) ⊂ h[E]`; with `N = M` this is `hagopian84_lemma11` for the type λ continuum `Cl K(Z)`, so
   no `h[N]` is needed; for general `N` it would be; (iii) the commission's reading of "Thus
   `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`" is right (an indecomposable continuum has no nonempty open
   subset inside a proper subcontinuum); (iv) `J(Z)` from Lemmas 7, 16: detail missing.
3. The cover: as printed, from freeness of `𝒫` and `𝒫(Z)` and (3).
4. The decomposition: disjointness by Lemma 7 and Lemma 3 (hypotheses of Lemma 3 unchecked).
5. Elements: continuity from Lemma 14; points or homogeneous continua (Lemma 9); proper subcontinua,
   being layers of type λ continua (void interior).
6. Homogeneity: from (5), (6) and the chain of sets `W(xᵢ, δ/2)`; Lemma 15 for `δ`.
7. **The arc in `M/𝔇` (proposed argument, not formalized).** Take a component `K` of `⋃𝒫′`; `Cl K` is
   of type λ with decomposition map `c` and runs straight through `𝒫`. Let
   `T = {t : c⁻¹(t) ⊂ P₃}`. `T` is open in `[0, 1]` (upper semicontinuity of the layers, `P₃` open).
   *To be shown:* `T` is nonempty and not a single layer's worth, i.e. contains a nondegenerate
   interval `[a, b]`; this needs that some layer of `Cl K` lies in `P₃` (from (4)–(5) of "runs
   straight" and the remark in Lemma 16 that no layer of `Cl K` meets three consecutive links, itself
   unargued there). Given `[a, b] ⊂ T`: by normality `Cl P₃` misses `Cl(P₁ ∪ P₅)`, so each layer
   `c⁻¹(t)`, `t ∈ [a, b]`, is in `Δ(𝒫) ⊂ 𝔇`. The quotient map restricted to `c⁻¹[[a, b]]` is constant on
   the layers, so it factors through `c` as a continuous map `[a, b] → M/𝔇`, injective because distinct
   layers are distinct elements of `𝔇`. A continuous injection of `[a, b]` into a Hausdorff space is an
   embedding: its image is an arc. Not formalized; needs `𝔇`.

## 6. Bing 1960, reconnaissance

`doc/notes/hagopian84.md` §F lists Bing's Properties 1–20 and Theorems 2–8 used in the indecomposable
case. In the repository: Property 4 (no simple triod; via `hagopian75_lemma1`), Property 5 (no simple
closed curve; via `hagopian75_lemma1_hu`), and Effros-type inputs (`effros_homogeneous`,
`uncountable_composants`) close to Theorem 8; an accessible point (`exists_accessible_point`). The
rest (§§3–7, 9–10: arc components as rays, collections of arcs in the plane, the reduced continuum
`M′`, folded sequences, the Special Separating Property) is absent. Nothing formalized. Jones 1975 is
not in the repository; it should be read before choosing the source.

## 7. Non-vacuity notes

The two checks: (1) not refuted by a short argument from the set-up; (2) not equivalent to the
conclusion it is used for, unless the printed argument is a proof by contradiction.

* **`NoArcIndecHomPlane`** (hypothesis of `hagopian76_theorem1_of_jones`,
  `hagopian75_theorem1_of_noArc`).
  1. It is a published theorem (Bing 1960, the indecomposable case; Jones 1975), independent of
     Hagopian 1976. No short refutation: the pseudo-arc is an indecomposable homogeneous plane continuum
     without arcs, consistent with it.
  2. In `hagopian76_theorem1_of_jones` it is used inside a proof by contradiction about an `M` that
     Theorem 1 says does not exist; it does not imply `Hagopian76Thm1` alone (it says nothing about
     decomposable subcontinua). In `hagopian75_theorem1_of_noArc` it excludes the case of degenerate
     layers; the conclusion (a nondegenerate homogeneous indecomposable subcontinuum) is not it.
* **`Hagopian84Decomp`** (hypothesis of `hagopian76_theorem1_of_jones`).
  1. Its hypotheses describe an `M` that Theorem 1 of 1976 says does not exist, so it is expected to
     hold vacuously once Theorem 1 is known; the point of the check is that its shape asks for nothing
     false in a short argument. It does not ask for nondegenerate fibres (with all fibres points `q` is
     a homeomorphism and `Y ≅ M`); the fibres are only required to be connected and `≠ M`, which the
     layers of type λ continua satisfy; it does not ask for planarity of `Y` (proved in the assembly);
     the arc in `Y` is what Hagopian asserts on p. 344.
  2. It alone does not give `Hagopian76Thm1`: the contradiction needs `NoArcIndecHomPlane` as well.
     The printed argument (p. 346) is a proof by contradiction.

## 8. Ledger entries

`LEDGER.md`, new section "Hagopian 1984 I … (batch 184)" at the end (after Hagopian 1976 XXVIII),
fourteen checks, printed sentences quoted:
1. H84.1, p. 335, the citation [19, Theorem 3] [26, Theorem 10]: as in Hagopian 1975 Lemma 2
   (Kuratowski's Theorem 3 gives the order type); claim true; gap filled there.
2. H84.2, Lemma 2 applied to unions: harmless in the plane setting; properness unargued in general.
3. H84.3, Lemma 6 proved without [26]; Lemma 9's citation covers interior layers only.
4. H84.4, Lemma 7: gaps in exposition; open.
5. H84.5, Lemma 8: gaps in exposition; true; open.
6. H84.6, Lemma 12: unargued; open.
7. H84.7, Lemma 13: gaps in exposition; open.
8. H84.8, Lemmas 14–15: positivity of `ε` unargued; Lemma 3's hypotheses unchecked; open.
9. H84.9, Lemma 16: `s ∉ S` gap (true); existence of `𝔔` unargued; open.
10. H84.10, Theorem 1 steps (i)–(v).
11. H84.11, p. 344, the arc in `M/𝔇`: unargued; argument proposed, one step to be shown (§5.7).
12. H84.12, p. 346, planarity via tree-likeness [21]: citation does not state the claim; gap filled by
    `exists_plane_quotient_of_monotone`.
13. H84.13, Corollary 3 through Theorem 2: "not a solenoid" not checked; the route uses Theorem 1
    with `N = M`.
14. H84.14, slips: "opens sets", "ε-circluar", "ε-homomorphisms", 1968 vs 1969.

No statement of Hagopian's is refuted; the count of defective proofs stays at fourteen.

## 9. Axioms

Every theorem of the group *Hagopian 1984 I (batch 184)* of `Axioms.lean` (17 declarations) uses
exactly `propext`, `Classical.choice`, `Quot.sound`. The output is in
`doc/batches/audits/axioms-batch184.txt`.

| File | Theorems |
| --- | --- |
| `H84Quot.lean` | `isPreconnected_preimage_of_monotone`, `isContinuum_preimage_of_monotone`, `isDecomposableSpace_of_monotone_image`, `fibreKey_of_mem`, `fibreKey_of_notMem`, `elt_fibreSetoid_of_mem`, `elt_fibreSetoid_of_notMem`, `fibre_usc`, `fibreSetoid_mooreDecomp`, `exists_plane_quotient_of_monotone_aux` |
| `Hagopian84A.lean` | `exists_plane_quotient_of_monotone`, `indecomposable_of_monotone_image`, `hagopian76_theorem1_of_jones`, `hagopian75_theorem1_of_noArc`, `hagopian84_lemma1`, `hagopian84_lemma6`, `hagopian84_lemma11` |

`axioms.txt`: 2197 lines (2180 + 17 added, none removed), `sorryAx` in none.

## 10. Dependency maps of Theorem 1

### 10.1 The 1976 route (map of report 183, unchanged)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_cases3                       [proved]
   └─ hagopian76_theorem1_of_cases2                    [proved]
      ├─ hagopian76_theorem1_of_step_tight             [proved]
      ├─ hICC: InnerComponentsCross (2e)               [OPEN]
      │  └─ §3.1 steps 4–5; zⱼ, (iii); τ₁ = 1          [open]
      ├─ stepStrands_of_frame (E0 + E1)                [proved]
      │  └─ StepFrame                                  [OPEN]  (other orientations: §5, open)
      └─ hagopian76_property4_step_cond2               [proved]
         ├─ i = 2: not_property4_x3x4                  [proved]
         │  └─ LastStepClaims                          [OPEN]
         ├─ BlockLayersMeetSides3 (i ≥ 3)              [OPEN]  (replacement split by Γ: §6.3)
         ├─ Case1ClaimsE24 → Case1Claims'              [proved: claims']
         │  ├─ first (E2.1)                            [open]
         │  ├─ between (§3)                            [open]
         │  ├─ far (E2.4) ← E24Data.far                [proved]
         │  │  ├─ e24_pair_between, e24_pair_below     [proved]
         │  │  ├─ minimalAdmissible_restrict           [proved]
         │  │  ├─ property2_violation                  [proved]
         │  │  └─ E24Claims (essential, far layer, FarFrom)  [OPEN]
         │  └─ band                                    [open]
         └─ Case2ClaimsE24 → Case2Claims'              [proved: claims']
            ├─ (a) (§4.1)                              [open]
            ├─ (b), (e) (§4.2)                         [open]
            └─ (d) ← E24Data.far with π⁻¹(p₂)          [proved, from E24Claims]
```

### 10.2 The 1984 route (Jones's plan)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_jones                         [proved]
   ├─ exists_plane_quotient_of_monotone                 [proved]
   │  ├─ fibreSetoid, fibre_usc, fibreSetoid_mooreDecomp [proved]
   │  ├─ no_proper_subcontinuum_separates               [proved, earlier]
   │  └─ m25_theorem22 (Moore 1925)                     [proved, earlier]
   ├─ indecomposable_of_monotone_image                  [proved]
   ├─ NoArcIndecHomPlane (Bing 1960 / Jones 1975)       [OPEN, named Prop; §6 recon]
   └─ Hagopian84Decomp (Theorem 1, N = M)               [OPEN, named Prop]
      ├─ hagopian75_lemma1, _hu (atriodic, HU)          [proved, earlier]
      ├─ hagopian75_exists_typeA' (E of type λ)         [proved, earlier]
      ├─ Lemma 13 (chain 𝒫)                             [open]
      │  ├─ Lemma 1 (hagopian84_lemma1)                 [proved]
      │  ├─ Lemma 3 (hagopian76_lemma3)                 [proved, earlier]
      │  ├─ Lemma 6 (hagopian84_lemma6)                 [proved]
      │  └─ Lemma 12                                    [open]
      │     └─ Moore 1962 Th. 44 (exists_closed_split_of_no_connected) [proved, earlier]
      ├─ K(Z), X(Z), F(Z), J(Z), 𝒫(Z)                    [open]
      │  ├─ Lemma 11, N = M (hagopian84_lemma11)        [proved]
      │  ├─ Lemma 7                                     [open]
      │  │  └─ two-sided extension (Lemma 4)            [open since batch 158]
      │  └─ Lemma 16                                    [open]
      ├─ cover 𝔅, disjointness of 𝔇 (Lemmas 3, 7)       [open]
      ├─ continuity of 𝔇 (Lemma 14)                     [open]
      ├─ homogeneity of M/𝔇 (Lemma 15, (5), (6))        [open]
      └─ arc in M/𝔇 (§5.7)                              [open]
   (not needed: Lemma 10, claim (4), Lemma 8 except in claim (4), "M/𝔇 is a solenoid", tree-likeness)
```

Lemma 8 is used in the printed proof only for claim (4) (the density of `S`), which `N = M` makes
unnecessary; it stays in the commission's list but is off the critical path of this route.

## 11. Skeleton proposal for what remains

```lean
/-- Lemma 4, two-sided: `E` is an essential subcontinuum of a type λ continuum `H` missing both end
sets of `H` (needed by Lemma 7). -/
theorem hagopian84_two_sided (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (H : Set M) (d : H → unitInterval), IsMinimalAdmissible H d ∧ IsEssential84 d E ∧
      Disjoint E (layer d 0) ∧ Disjoint E (layer d 1) := by sorry

/-- The atriodicity step of Lemma 7: a type λ continuum meeting a layer of `E` and not inside `E`
leaves the layer on one side only. -/
theorem layer_one_side (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) … : … := by sorry

/-- Lemma 12, first two sentences: `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`. -/
theorem lemma12_component (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) … :
    connectedComponentIn (A ∪ B)ᶜ x = E \ (A ∪ B) := by sorry

/-- Lemmas 14–15: `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′` for a free normal regular chain, so the distance is positive. -/
theorem closure_delta_subset {P : Fin 5 → Set M} (hP : IsChain5 P) (hf : IsFree5 P)
    (hn : IsNormal5 P) (hr : IsRegular5 P) : closure (⋃₀ Delta5 P) ⊆ midUnion P := by sorry

/-- §5.7: the arc in the quotient, given a decomposition containing `Δ(𝒫)`. -/
theorem quotient_arc_of_delta {P : Fin 5 → Set M} (hr : IsRegular5 P) {Y : Type} [MetricSpace Y]
    {q : M → Y} (hq : Continuous q) (hD : ∀ Z ∈ Delta5 P, ∃ y, q ⁻¹' {y} = Z) :
    ∃ α : Set Y, Nonempty (α ≃ₜ unitInterval) := by sorry
```

## 12. Delivery

* `doc/batches/batch184-MANIFEST.txt` lists `git diff --name-status` against the run's initial commit
  (`179a01a`), plus any uncommitted change, plus the files this report names that the run did not
  change, plus the manifest itself.
* `doc/batches/batch184-files.tar.gz` holds every file of the manifest at its final content (the PDF
  `doc/sources/hagopian1984.pdf` included). The tarball does not contain itself.
