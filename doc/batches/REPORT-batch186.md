Commission read: `doc/batches/COMMISSION-batch186.md` ("Commission: batch 186 — Part E, Hagopian 1984 III: the quotient package; Lemmas 12–16").

# Report, batch 186

## 0. Summary, omissions

**The quotient package is proved** (`hagopian84Decomp_of_package`): `Hagopian84Decomp` follows from
"every `M` has a Jones decomposition" (`IsJonesDecomp84`), with homogeneity by the orbit argument
(`exists_comp_small_homeo`) and the arc by a quotient-map lift. **Lemma 12 is proved** (with the
allowed components clause), the **fold combinatorics** are proved (`exists_fold`), and so are the
**note on p. 341** (`delta5_partition`), **positivity** (`delta5_dist_pos`), **Lemma 14**
(`hagopian84_lemma14`), **Lemma 15** with a smaller `ε` (`hagopian84_lemma15`) and the **interval of
layers** for the arc (`exists_interval_in_delta`). **Lemma 13 and Lemma 16 are open**. §6 (Jones 1975)
was reached: `doc/notes/jones75.md`. No `sorry` in any declaration; nothing refuted.
`axioms.txt` has **2306 lines** (2261 + 45 added, none removed), `sorryAx` in none.

Status lines:
* STATUS: §2 `dist_symm_lt_of_small`, `exists_comp_small_homeo`, `hagopian84Decomp_of_package` proved
* STATUS: §3.1 steps 1–3 (`chainLinks84_runsStraight`) open ((1)–(4) not formalized: parameter
  bounds from `½ρ` bounds; Lemma 1 with Effros for (4))
* STATUS: §3.1 step 4(a) `exists_fold` proved
* STATUS: §3.1 step 4(b) (kinds D and U) open (part of `chainLinks84_runsStraight`)
* STATUS: §3.1 step 5 `chainLinks84_regular` open (needs `chainLinks84_runsStraight`)
* STATUS: §3.1 `hagopian84_lemma13` open (needs the two items above)
* STATUS: §3.2 `hagopian84_lemma12` proved (with the components clause)
* STATUS: §4.1 `delta5_partition`, `delta5_dist_pos` proved
* STATUS: §4.2 `hagopian84_lemma14` proved
* STATUS: §4.3 `hagopian84_lemma15` proved (smaller `ε`)
* STATUS: §4.4 `exists_interval_in_delta` proved
* STATUS: §5 `hagopian84_lemma16` open, and its weaker form open (the printed step "Since `𝒫` is
  free, there exist a 3-linked subchain …" is unargued; no argument found)
* STATUS: §6 reconnaissance written (`doc/notes/jones75.md`)

**Omissions (§0 rule).**
1. **Lemma 13** (`hagopian84_lemma13`): open, commented out with its obstruction. Reason: its
   steps (1)–(4) and the geometry of the fold (kinds D and U) were not formalized this batch.
2. **`chainLinks84_runsStraight`, `chainLinks84_regular`**: the skeleton's `True` placeholders are
   replaced by chosen shapes, written in full inside the `OPEN` comments of `Hagopian84B.lean`
   (§3 below), not compiled. Reason: unproved.
3. **Lemma 16** (`hagopian84_lemma16`): open. Reason: the printed step quoted in §5 below is
   unargued and no argument was found.
4. **The weaker form of Lemma 16** (no layer of `F` contains the closure of a component of
   `midUnion P`): not stated as a declaration. Reason: it meets the same missing step (how `F`
   behaves past the last layer of `Cl K`); no proof was found, and stating it unproved adds nothing to
   the comment in `Hagopian84B.lean`.

## 1. Files and wiring

`HPC/Hagopian/Hagopian84B.lean` (the skeleton, statements), split with proofs in
`HPC/Hagopian/H84Fold.lean` (Mathlib only; folds), `HPC/Hagopian/H84Delta.lean` (layers, `Δ(𝒫)`,
positivity, the interval), `HPC/Hagopian/H84Lemma12.lean`, `HPC/Hagopian/H84Lemma1415.lean`.
`HPC.lean` ends with `import HPC.Hagopian.Hagopian84B`; `lake build HPC` succeeds. In
`Hagopian84A.lean` the commented-out blocks of Lemmas 12, 14, 15 are replaced by one-line pointers
(Lemmas 13 and 16 keep theirs: unproved).

## 2. The quotient package (§2; proved)

* **`IsJonesDecomp84 r`** (structure, as in the skeleton): `usc`, `conn`, `proper`, `invariant`
  (some `δ > 0` such that every `δ`-homeomorphism maps related points to related points), `arc`
  (compact `C`, continuous onto `c : C → [0, 1]`, `c x = c y ↔ r x y`).
* **`dist_symm_lt_of_small`**: the inverse of a `δ`-homeomorphism is one.
* **`exists_comp_small_homeo`**: for any class `Q` of homeomorphisms containing the
  `δ`-homeomorphisms and closed under composition, `Q` acts transitively on `M`. The orbit `O` of
  `x` contains `Wset84 y δ` for each `y ∈ O` (open, `hagopian84_lemma1`); its complement likewise
  (using inverses); `M` connected, so `O = M`.
* **`hagopian84Decomp_of_package`**: route of the commission. `Q` = homeomorphisms `T` with
  `r a b ↔ r (T a) (T b)`, which contains the `δ`-homeomorphisms by `invariant` and its use on the
  inverse. Homogeneity descends by `exists_homeomorph_quotient`. The arc: `c` is a closed map from a
  compact space, so a quotient map (`IsClosedMap.isQuotientMap`); `C → M → M/r` factors through
  `φ : [0, 1] → M/r` (`IsQuotientMap.lift`); `φ` is injective by `arc`; a continuous injection from
  a compact space to a Hausdorff one is a closed embedding.

Shape: unchanged.

## 3. Lemmas 12 and 13 (§3)

### 3.1 Lemma 13 (open)

* `WsetOf`, `chainLinks84`: unchanged.
* **`exists_fold` (step 4(a), proved).** Shape unchanged. The proof is not the commission's
  `π`-argument but a left-to-right sweep (`FoldAux.sweep_step`, `H84Fold.lean`): with no fold, if
  `a ∈ V p`, no point left of `a` lies in a later set and no point `≥ a` in an earlier one, then
  `V p` is an interval from `a` and the first point after it outside `V p` lies in `V (p + 1)` with
  the same two properties. A gap in `V p` would give a point of `V p` with points outside it on both
  sides; the last such point before and the first after lie in neighbours of `V p` (`left_end`,
  `right_end`), and the two properties put both in the same neighbour: a fold. Both the printed case
  and its mirror are covered.
* **`chainLinks84_runsStraight` (open; shape chosen).** Given `ε > 0`, closed `A` missing `E`, open
  `B ⊇ k⁻¹(0) ∪ k⁻¹(1)`: there are strictly increasing `x : Fin 16 → [0, 1]` with `x 0 = 0`,
  `x 15 = 1`, and `0 < δ < ε`, such that `chainLinks84 k x δ` is a normal chain with union in `M∖A`,
  `Cl(L 0 ∪ L 4) ⊆ B`, and every `δ`-homeomorphism `h` gives `h[E]` a minimal admissible map `g`
  that runs straight through the chain with `g⁻¹(0) ⊆ L 0∖Cl L 1` and `g⁻¹(1) ⊆ L 4∖Cl L 3`.
  *Obstruction:* (1)–(4) are not formalized. The positions of `r` and `s` in (3) need the `½ρ` bounds
  converted into parameter bounds (uniform continuity of `t ↦ k⁻¹(t)` in the Hausdorff sense, from
  upper semicontinuity of the layers); (4) needs Lemma 1 with Effros at a boundary point; kinds D and
  U of the fold (step 4(b)) are not formalized.
* **`chainLinks84_regular` (open; shape chosen).** For `x`, `δ` as above: the chain is regular, and
  for each `y ∈ midUnion`, some `δ`-homeomorphism `h` has `Cl(component of y)` essential in `h[E]`.
  *Obstruction:* the item above; the step itself (`Cl K ⊆ h[E]` by `subset_of_meets_avoids`, then
  Lemma 6) has no further gap.
* **`hagopian84_lemma13` (open).** Shape unchanged (skeleton's). *Obstruction:* the two items above.
  Given them: apply Lemma 12 (its end-layer hypotheses come from `chainLinks84_runsStraight` with
  `h = id`); `⋃𝒫 ⊆ ⋃𝔏 ⊆ M∖A`; `P 0 = L 0`, `P 4 = L 4`; each component of `⋃𝒫′` is one of `⋃𝔏′`
  (Lemma 12's added clause), so the last paragraph needs no further argument.

### 3.2 Lemma 12 (proved)

*Shape change:* the conclusion adds `∀ x ∈ midUnion P, connectedComponentIn (midUnion P) x =
connectedComponentIn (midUnion L) x` (allowed by the commission).
*Proof* (`hagopian84_lemma12_aux`): `A = L 0∖Cl L 1`, `B = L 4∖Cl L 3`; Moore 44
(`exists_closed_split_of_no_connected`) inside the compact `M∖(A ∪ B)` gives disjoint closed
`K₁ ⊇ E∖(A ∪ B)`, `K₂ ⊇ M∖⋃𝔏`; `P = refineChain L K₂ = (L 0, L 1∖K₂, L 2∖K₂, L 3∖K₂, L 4)`.
* Step 1 ("Since `𝔏` is regular, `E∖(A ∪ B)` is an essential subcontinuum of `E`") is **not
  needed**: the hypothesis of Moore 44 follows from atriodicity directly (the closure of a connected
  set meeting `E∖(A ∪ B)` and `M∖⋃𝔏` inside `M∖(A ∪ B)` is a continuum meeting `E` and missing both
  end layers, so lies in `E` by `subset_of_meets_avoids`; absurd).
* Running straight carries over (`runsStraight_refine`, using `chain_consecutive_meet` and
  `mem_frontier_diff_iff`); regularity carries over since `⋃𝒫′ = midUnion L ∩ K₁` is a union of
  components of `midUnion L`.
* Freeness by the commission's route.

## 4. Lemmas 14, 15 and the arc (§4; proved)

* **`delta5_partition`.** *Shape change:* `hX`, `hi`, `hn` dropped (unused). Proof: a layer through
  a point outside `Cl Pᵢ` misses `Cl Pᵢ` (`layer_disjoint_closure_of_mem`); a member of `Δ(𝒫)` lies
  in its component (`delta_subset_component`); members that meet come from one component.
* **`delta5_dist_pos`.** *Shape change:* `hX`, `hi`, `hn` dropped. Proof: commission's route,
  `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′` by freeness (`closure_delta_subset_mid`), then compactness.
* **`hagopian84_lemma14`.** *Shape change:* the normality added by the skeleton is dropped (unused).
  Proof: `ε' = min ε η`; Lemma 3 (`hagopian76_lemma3`) through `delta_translate_eq`, its three
  hypotheses checked: the end layers of both closures lie outside `⋃𝒫′` (`endlayers_not_mid`), at
  distance `≥ η` from `Z`, `Z′`, while the translate moves points by `< ε' ≤ η`.
* **`hagopian84_lemma15`.** Shape: skeleton's (normality added there); `ε` smaller than Hagopian's,
  as the commission proposed: below `η` and below the distances between `Cl P 0` and
  `Cl P 2 ∪ Cl P 3 ∪ Cl P 4` and between `Cl P 4` and `Cl P 0 ∪ Cl P 1 ∪ Cl P 2`
  (`exists_far_links`). Proof as in commission §4.3 (`no_arm_at_interior_layer`, `layers_agree`, the
  degenerate case excluded by the end layers).
* **`exists_interval_in_delta`.** *Shape change:* `hX`, `hi`, `hr` dropped. Proof: commission §4.4
  (`exists_interval_in_P2`).

## 5. Lemma 16 (open)

Shape: skeleton's (commented out). The printed sentence

> Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater than
> `s` such that (1) for each number `u` (`t < u < w`), `d⁻¹(u)` intersects each link of `𝔔` and no
> element of `𝒫∖𝔔` that intersects a link of `𝔔` …

is unargued. Freeness says that `Bd ⋃𝒫` misses `Cl ⋃𝒫′` except in `Bd(P 0 ∪ P 4)`; (1) asks that
the layers of `F` just past `s` avoid the links adjacent to `𝔔`, which concerns how `F` leaves
`⋃𝒫`. I did not find an argument. The other steps are available: `s > 0` (a layer of `Cl K` meeting
links `i` and `i + 2` lies in `Bd P (i+1)` by running straight), `s ∉ S` (`S` open by
`lsc_of_minimalAdmissible`), uniqueness (`hagopian75_lemma3_unique`). The weaker form (no layer of
`F` contains some `Cl H`) is not proved either: a layer of `F` beyond the last layer of `Cl K` is not
otherwise constrained, which is the same missing step.

## 6. Jones 1975 (reconnaissance)

`doc/notes/jones75.md`: transcription of pp. 57–61 from 200 dpi page images; map: Effros corollary =
`effros_homogeneous`; (a) = `hagopian75_lemma1_hu`, (b) = `hagopian75_lemma1`; (c), (d), (e), (f)
and the Theorem not in the repository; plane topology per step (accessibility of the ray — an
unargued assumption; straightening by the collars `exists_collar`; the Jordan curve theorem
`jordan_curve_theorem` for the order of `t_a`, `t_b` and the domains `Dᵢ`; the fixed point `t_f` by
the intermediate value theorem along `T`); a skeleton proposal `HPC/Jones/Jones75.lean`. Not
formalized.

## 7. Non-vacuity notes

Named `Prop`s and structures among hypotheses of theorems of this batch:

1. **`hagopian84Decomp_of_package`, hypothesis `hP`** (every `M` as in `Hagopian84Decomp` has a
   Jones decomposition, `IsJonesDecomp84`).
   1. *Not refuted by a short argument.* Each field is consistent with the set-up: Hagopian's
      Theorem 1 (p. 342, with `N = M`) produces exactly such a decomposition (`𝔇`, upper
      semicontinuous by Lemma 14, continua as elements, proper, respected by small homeomorphisms by
      Lemma 15, with an arc of elements by p. 344 and `exists_interval_in_delta`). The proved pieces of
      this batch (Lemmas 14, 15, `exists_interval_in_delta`) supply the fields `usc`, `invariant`, `arc`
      for `Δ(𝒫)` locally. The fields are mutually consistent on every such `M`: the identity setoid
      satisfies fields 1–4 (singletons are connected; `M` is nondegenerate, since it is not
      hereditarily indecomposable; every homeomorphism respects equality), and field 5 for it would
      be an arc in `M`. So the content of `hP` is field 5 together with the others, which Hagopian's
      construction obtains by coarsening; no short argument from the set-up excludes it.
   2. *Not equivalent to the conclusion.* `Hagopian84Decomp` asks for a quotient map with connected
      proper fibres, homogeneous range and an arc; `hP` asks in addition for upper semicontinuity, a
      uniform `δ` of invariance and an arc of classes realized inside `M` by a compact set. The
      reduction is one-way: from `Hagopian84Decomp` one gets a monotone map `q`, but neither the
      `δ`-invariance of its fibres (homogeneity of the quotient gives homeomorphisms of the quotient,
      not small homeomorphisms of `M` respecting the fibres) nor a compact `C ⊆ M` mapping
      bijectively-on-classes onto an arc. So `hP` is strictly stronger structured input, as printed
      Theorem 1 provides; the argument is direct, not by contradiction.
2. No other theorem of this batch has a named `Prop` or open structure among its hypotheses
   (`IsChain5`, `IsNormal5`, `IsRegular5`, `IsFree5`, `RunsStraight`, `IsMinimalAdmissible` are the
   paper's definitions, from batch 184).

## 8. Ledger entries

`LEDGER.md`, Hagopian 1984 section, new subsection "Hagopian 1984 III: the quotient package;
Lemmas 12–16 (batch 186)", entries H84.17–H84.22, each with the printed sentences quoted:
* **H84.17** Lemma 13 (5) printed without `h` (slip found by the commission); the fold reduction
  unargued, mirror case omitted.
* **H84.18** Lemma 13: "Note that `𝔏` is a normal chain in `M∖A`"; positions of `r`, `s` in (3); the
  regularity sentence; the last paragraph — unargued, not formalized; the last paragraph made
  unnecessary by Lemma 12's components clause.
* **H84.19** Lemma 12: the three unargued steps and freeness; lemma proved; the "essential
  subcontinuum" step not needed.
* **H84.20** Lemmas 14–15: the note and positivity unargued, proved; Lemma 14 proved; Lemma 15 —
  "By Lemma 3" does not suffice as printed; proved with smaller `ε`; recorded as a gap in exposition.
* **H84.21** Lemma 16: "Since `𝒫` is free, there exist …" unargued; open.
* **H84.22** p. 344: the arc (proved from an interval of layers); the points `vᵢ` replaced by the
  orbit argument (harmless).

Nothing refuted; the count of defective proofs stays at fourteen.

## 9. Axioms

`Axioms.lean` group "Hagopian 1984 III (batch 186)": 45 declarations. `axioms.txt` regenerated:
**2306 lines** (2261 + 45; none removed; `sorryAx` in no line). Per-theorem audit:
`doc/batches/audits/axioms-batch186.txt`. Every one of the 45 depends on exactly
`[propext, Classical.choice, Quot.sound]`:

`FoldAux.left_end`, `FoldAux.right_end`, `FoldAux.sweep_step`, `FoldAux.exists_fold_nat`,
`exists_fold_aux`, `layer_isPreconnected'`, `layer_nonempty'`, `layer_subset_set`,
`mem_layer_self84`, `exists_layer_eq_of_minimal`, `layer_eq_of_common_point`,
`subset_of_preconnected_meets_open`, `layer_subset_link`, `layer_disjoint_closure_of_mem`,
`chain5_disjoint`, `delta_subset_component`, `delta_subset_diff`, `delta5_partition_aux`,
`closure_delta_subset_mid`, `delta5_dist_pos_aux`, `exists_interval_in_P2`,
`exists_interval_in_delta_aux`, `endlayers_not_mid`, `delta_regular_rep`, `delta_translate_eq`,
`hagopian84_lemma14_aux`, `exists_far_links`, `hagopian84_lemma15_aux`, `chain_consecutive_meet`,
`mem_frontier_diff_iff`, `refineChain_subset`, `refineChain_mid`, `mem_refineChain_of`,
`runsStraight_refine`, `hagopian84_lemma12_aux`, `dist_symm_lt_of_small`,
`exists_comp_small_homeo`, `hagopian84Decomp_of_package`, `exists_fold`, `hagopian84_lemma12`,
`delta5_partition`, `delta5_dist_pos`, `hagopian84_lemma14`, `hagopian84_lemma15`,
`exists_interval_in_delta` (all in namespace `HPC.Hagopian`).

In `Hagopian84B.lean`, `Hagopian84A.lean` and the four new proof files, `sorry` occurs only inside
comments.

## 10. Dependency maps

### 10.1 `Hagopian84Decomp` (the 1984 route)

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
            └─ construction pp. 343–344                  [open, later batch]
               ├─ Lemma 13 (chain 𝒫)                     [open]
               │  ├─ chainLinks84_runsStraight            [open]
               │  │  ├─ (1)–(4)                           [open]
               │  │  └─ fold: exists_fold                 [proved]; kinds D, U [open]
               │  ├─ chainLinks84_regular                 [open; ← runsStraight]
               │  └─ Lemma 12 (hagopian84_lemma12)        [proved, batch 186]
               ├─ K(Z), X(Z), F(Z), J(Z), 𝒫(Z)            [open]
               │  ├─ Lemma 11, N = M                      [proved]
               │  ├─ Lemma 7, two-sided extension         [proved, batch 185]
               │  ├─ layers_agree                         [proved, batch 185]
               │  └─ Lemma 16 or its weaker form          [open]
               ├─ cover 𝔅, disjointness of 𝔇              [open]
               ├─ field usc ← Lemma 14                    [proved, batch 186]
               │  └─ delta5_partition, delta5_dist_pos    [proved, batch 186]
               ├─ field invariant ← Lemma 15              [proved, batch 186 (smaller ε)]
               └─ field arc ← exists_interval_in_delta    [proved, batch 186]
   (not needed with N = M: Lemmas 8, 10, claim (4), the solenoid conclusion, the last paragraph)
```

### 10.2 The 1976 route (open items as of batch 185, unchanged)

* §3.3 `crossing_component_run` (runs of `F` along a translate): open.
* §6 `case1_between_runs` ("between" with runs): open (§3.3).
* The four named `Prop`s of `hagopian76_theorem1_of_cases4`: `StepFrame`, `LastStepClaims`,
  `Case1ClaimsE24`, `Case2ClaimsE24`: open.

The tree of report 185 §10.1 is unchanged.

## 11. Skeleton proposal for the next step

```lean
/-- p. 343: the data attached to a point `Z` (`z ∈ M`): the chain `𝒫(Z)` of Lemma 13 around a
translate of `E`, the component `K(Z)` of `⋃𝒫(Z)′` through `z`, the end set `X(Z)` of `Cl K(Z)`,
the extension `F(Z)` of `Cl K(Z)` away from `X(Z)`, and `J(Z)`. -/
structure PointData84 (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (z : M) where
  P : Fin 5 → Set M
  chain : IsChain5 P ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P
  hz : z ∈ midUnion P
  c : closure (connectedComponentIn (midUnion P) z) → unitInterval
  hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) z)) c
  runs : RunsStraight c P
  F : Set M
  d : F → unitInterval
  hd : IsMinimalAdmissible F d
  hKF : closure (connectedComponentIn (midUnion P) z) ⊆ F
  hd0 : layer d 0 = layer c 0

theorem exists_pointData84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hH : ¬ IsHereditarilyIndecomposable (univ : Set M)) (z : M) : Nonempty (PointData84 M z)

/-- p. 343: a finite cover `𝔅` by the sets `W(K(Z))`, and the relation `𝔇`: `x ~ y` iff some
`F(Z)` has `x`, `y` in one layer (Lemmas 7, 16 and `layers_agree` give transitivity). -/
noncomputable def jonesSetoid84 (D : ∀ z : M, PointData84 M z) (B : Finset M) : Setoid M

theorem jonesSetoid84_disjoint … -- the disjointness of 𝔇 (claims (5), (6))
theorem jonesSetoid84_isJonesDecomp (…) : IsJonesDecomp84 (jonesSetoid84 D B)
  -- usc: Lemma 14; invariant: Lemma 15; arc: exists_interval_in_delta + rescaling

theorem hagopian84_decomp : Hagopian84Decomp :=
  hagopian84Decomp_of_package fun M _ _ hX hi hH => ⟨_, jonesSetoid84_isJonesDecomp …⟩
```
Before the construction: Lemma 13 (through `chainLinks84_runsStraight`, whose shape is written in
`Hagopian84B.lean`), and Lemma 16 or its weaker form. The shapes above are proposals, not checked.

## 12. Files

New: `HPC/Hagopian/Hagopian84B.lean`, `HPC/Hagopian/H84Fold.lean`, `HPC/Hagopian/H84Delta.lean`,
`HPC/Hagopian/H84Lemma12.lean`, `HPC/Hagopian/H84Lemma1415.lean`, `doc/notes/jones75.md`,
`doc/batches/REPORT-batch186.md`, `doc/batches/audits/axioms-batch186.txt`,
`doc/batches/batch186-MANIFEST.txt`, `doc/batches/batch186-files.tar.gz`. Uploads placed:
`doc/batches/COMMISSION-batch186.md`, `doc/batches/skeletons/Hagopian84B.lean`,
`doc/sources/jones1975.pdf`. Changed: `HPC.lean`, `Axioms.lean`, `axioms.txt`, `README.md`,
`LEDGER.md` (Hagopian 1984 section), `OPEN.md`, `doc/notes/hagopian84.md`,
`HPC/Hagopian/Hagopian84A.lean` (pointers only). The full list is the manifest.
