Commission read: `doc/batches/COMMISSION-batch201.md` ("Commission: batch 201 — Part G, IV: Bing–Jones Theorem 10").

# Report, batch 201

## 0. Summary, omissions, shape changes

**Every declaration of the skeleton is proved**, including the main item `bj_step` (`BJStep`),
`bjThm10_of_step`, and hence **Bing–Jones Theorem 10** (`HPC.BJ59.bjThm10 : BJThm10`) and the
corollaries: the classification of homogeneous plane continua with Domokos–Prajs's third class
with no named hypothesis (`ho16_classification_atomic'`), homogeneity and uniqueness of circles of
pseudo-arcs, and the classification with Bing–Jones's third class and its plane form given only
`BJPlaneExample`. Nothing is commented out and no new file contains `sorry`, `admit` or `axiom`.
The skeleton is split under `HPC/BJ59/` (twelve files plus the collector `HPC/BJ59/BJ59D.lean`,
imported at the end of `HPC.lean`). A script check confirms that 20 of the 21 declarations of the
skeleton occur in the library with the skeleton's text up to `:=`; the exception is
`exists_pattern` (shape change below). The 66 new theorems are audited in
`doc/batches/audits/axioms-batch201.txt`; none depends on `sorryAx`. `lake build HPC` succeeds
(8844 jobs).

```
STATUS: HasPrivatePoints, IsFibreChainMap, EndCompat, IsFibreFine defined; tested on degenerate inputs
STATUS: exists_point_only_of_minimal proved
STATUS: adjacent_of_properCover proved
STATUS: exists_pattern proved (shape change: clause 2 for every link; skeleton form exists_pattern_skeleton proved)
STATUS: isFibreFine_of_isEpsChain proved
STATUS: bj_theorem8_cor_sub proved
STATUS: bj_theorem5_window proved
STATUS: exists_window_set proved
STATUS: BJStep defined (as in the skeleton)
STATUS: bj_step proved
STATUS: bjThm10_of_step proved
STATUS: bjThm10 proved
STATUS: ho16_classification_atomic' proved (no named hypothesis)
STATUS: isHomogeneous_of_isCircleOfPA' proved
STATUS: homeomorph_of_isCircleOfPA' proved
STATUS: ho16_classification₃ proved (from BJPlaneExample)
STATUS: ho16_classification_plane₃ proved (from BJPlaneExample)
STATUS: nonvac_conditions proved
```

**Items: proved** — all of the above. **Refuted** — none. **Open** — none of this batch.

**Omissions.**
* Non-vacuity of `bj_theorem8_cor_sub`, `bj_theorem5_window`, `exists_window_set`, `BJStep` and
  `BJThm10` on a non-degenerate input (commission §7): their hypotheses need a continuous
  snake-like arc of pseudo-arcs, known here only under `BJPlaneExample`. A conditional witness was
  not attempted (the commission does not require it). Recorded in `OPEN.md`.

**Shape changes.**
* `exists_pattern` (`HPC/BJ59/Thm10Pattern.lean`): the skeleton's second clause
  `∀ a, (F.link a ∩ Q).Nonempty → w₁ ≤ R a ∧ R a ≤ w₂ ∧ ∀ z : Q, z ∈ closure (F.link a) → φ z ∈ D.link (R a)`
  is strengthened to two unconditional clauses, `∀ a, w₁ ≤ R a ∧ R a ≤ w₂` and
  `∀ a, ∀ z : Q, z ∈ closure (F.link a) → φ z ∈ D.link (R a)` (every link, not only those
  meeting `Q`; the values of `R` stay in the run everywhere). The skeleton's form follows and is
  proved as `exists_pattern_skeleton`. The change is recorded at the statement.
* The skeleton's single file is split; `HPC/BJ59/BJ59D.lean` holds §5's `bjThm10` and the
  corollaries, and a docstring mapping each declaration to its file.

**Unused hypotheses / linter.** The unused-variables linter reports `hw`, `hw₂` of
`exists_point_only_of_minimal` and `hw` of `exists_pattern` (skeleton hypotheses, kept as stated;
the conclusions do not need them). It also reports that the section instance `[CompactSpace Y]` is
included but unused in `exists_window_set` and in the internal lemma `bj_theorem8_cor_sub_one`
(compactness of `Y` is not needed there).

## 1. §2: the conditions (`Thm10Defs.lean`)

`HasPrivatePoints`, `IsFibreChainMap` (Condition A with the onto and refinement clauses),
`EndCompat` (Condition C at the end fibres) and `IsFibreFine` (no fibre lies in fewer than three
consecutive links, unless the chain has one link), as in the skeleton. Tests: §6 below.

## 2. §3: tools (`Thm10Defs.lean`, `Thm10Lib.lean`, `Thm10Runs.lean`, `Thm10Pattern.lean`, `Thm10Sub.lean`, `Thm10Window.lean`)

* `exists_point_only_of_minimal`: by a separation of the preconnected set `C` into the links before
  and after `j`.
* `adjacent_of_properCover`: directly from the discrete steps of the two chain maps
  (`exists_abs_le_one_of_steps`), with no connectedness; this is Theorem 6 in the form Step 2(c)
  uses (ledger BJ.32).
* `isFibreFine_of_isEpsChain`: two points of a fibre at distance `≥ κ` cannot lie in two adjacent
  links of a `κ/3`-chain.
* `exists_pattern` (Step 2(b)): the decided-position construction of commission §3, with closures
  (ledger BJ.31).
* `bj_theorem8_cor_sub`: for `n ≥ 3`, the batch-200 corollary `bj_theorem8_cor` on the window
  `g⁻¹[a, b]` (`window_transfer`), applied to the restriction of `E` and of the run of `F` meeting
  the window (`exists_run_meeting`), with `R` clamped outside the run; for `n = 1`, a zigzag
  `0, …, ℓ−1, ℓ−1, …, 0` with each value repeated three times, using a uniform spread of the fibres
  (`exists_fibre_spread`). Clause (1) is stated on `F.link k ∩ g⁻¹[a, b]` only (ledger BJ.40).
* `exists_window_set` and `bj_theorem5_window`: the transition set, with a uniform lower bound for the
  spread of the links of the run over the fibres near the middle of the window, and the repaired
  Theorem 5 (batch 198) on the window, transferred by `window_transfer` (ledger BJ.33).

## 3. §4: the step (`Thm10Pieces.lean`, `Thm10Glue.lean`, `Thm10Step.lean`)

`BJStep` as in the skeleton (`Thm10Induct.lean`). `bj_step` follows commission §4:
(a)–(e) the sub-arcs, the maps of the sub-arcs (`exists_subarc_piece`, from
`bj_theorem8_cor_sub`), the maps at the ends (`exists_end_piece`, from `exists_pattern`), the fine
chain `F`, and the choice of `τ` with closures (`exists_tau_run`, `exists_tau_incl`; ledger BJ.35);
(f)–(g) the gluing `bj_glue`: the map of a link `e` of the new chain is `R (π e) (β e)`, where
`π e` counts the windows whose right side (with its transition set) contains `e`, and `β e` is the
transition link if `e` meets a transition set, otherwise a link of `F` containing `e`; then A′, B′,
C′, private points (`exists_privatePoint_shrink`) and `K` onto. One step serves for both sides.
The homeomorphisms on cut fibres (Step 1(c), Step 2(i)) and Theorem 9 are not used (ledger BJ.37).

## 4. §5: Theorem 10 and the corollaries (`Thm10Induct.lean`, `BJ59D.lean`)

`bjThm10_of_step`: from the one-link chains `{X}`, `{Y}` and `H = id`, alternate the step on the two
sides with `δ_i = min(1/2^{i+1}, κ_X/3, κ_Y/3)` (fibre-fineness by `isFibreFine_of_isEpsChain`),
then `zigzag_homeomorph` and `zigzag_fibre`; the ends agree with `h₀`, `h₁` by Condition C.
`bjThm10 := bjThm10_of_step bj_step`. The five corollaries are the batch-198–200 results with the
hypothesis `BJThm10` discharged by `bjThm10`.

## 5. Ledger

New section "Bing–Jones §6, Theorem 10 (batch 201)" in `LEDGER.md`, items BJ.30–BJ.40 = commission
§6 items 1–11 in order (BJ.30 `E₁` read `D₁`; BJ.31 Step 2(b); BJ.32 Theorem 6; BJ.33 Theorem 5 on
p. 185; BJ.34 Theorem 9 in Step 2(i); BJ.35 the analogue of Step 2c, closures; BJ.36 Steps 4, 5, ⋯;
BJ.37 route; BJ.38 "irreducibly covers"; BJ.39 `f_{i+1}` read `f_{t+1}`; BJ.40 condition (1)). No
other defect of Steps 2(d)–(h) was met. I would count none: BJ.33 is a consequence of the false
Theorem 5 (BJ.5, already counted); the others are unargued steps, slips or overstatements, all
supplied. Counts unchanged: 24 false printed statements, 18 defective proofs.

**Quotations.** Every quotation of the commission (pp. 176, 181–182, 184, 184–185, 185, 187, 188)
and of the ledger section was checked against crops of page images rendered at 400 dpi and viewed
at full resolution; they agree with the page images in every item.

## 6. Non-vacuity (`NonVac201.lean`, `NonVac201b.lean`)

* Definitions: `nonvac_conditions` (skeleton statement): on `[0, 1]` with the identity, the
  three-link chain `nvChain 0` is a chain in Bing–Jones's sense with private points (the centres),
  and the identity is a fibre chain map of it onto itself. Degenerate inputs:
  `nonvac_conditions_one` (one-link chains: private points, fibre-fine, A and C with the identity
  chain map and `h₀ = h₁ = id`), `nonvac_conditions_zero` (chains with no link: private points
  vacuous; a fibre chain map from an empty chain forces the target empty; an empty chain is
  fibre-fine for any onto map).
* `exists_point_only_of_minimal`, `adjacent_of_properCover`: their hypotheses hold on `[0, 1]` with
  `nvChain 0`, `C = [0, 1]` and the whole run (`nonvac_point_only`, `nonvac_adjacent`, with
  `R = R' = id`).
* `isFibreFine_of_isEpsChain`: `[0, 1]²` with the first projection, `κ = 1`, and the chain
  `nvSquareChain` of 19 small open rectangles along the fibre over `0`, a `1/3`-chain
  (`nonvac_fibreFine`).
* `exists_pattern`: a plane pseudo-arc `Q`, `φ` the inclusion, `D` the chain of `nonvac_bj_chains`
  shrunk to private points, the whole run (`nonvac_pattern`).
* `bj_theorem8_cor_sub`, `bj_theorem5_window`, `exists_window_set`, `BJStep`, `BJThm10`: no witness
  (see §0).
* `BJStep` and `BJThm10` on degenerate inputs: with one-link chains `D = {X}`, `E = {Y}` every
  hypothesis of the step other than the arcs-of-pseudo-arcs hypotheses holds (fibre-fineness by the
  one-link clause, A by the identity map, C for any `h₀`, `h₁` since every point lies in the single
  link; formally checked for `h₀ = h₁ = id` in `nonvac_conditions_one`); this is the start of the
  induction in `bjThm10_of_step`. `BJThm10` puts no condition on `h₀`, `h₁`: for every pair of
  homeomorphisms of the end fibres it gives a fibre-preserving extension.

## 7. Axioms

`doc/batches/audits/axioms-batch201.txt` (66 lines, one per new theorem; added to `Axioms.lean` as
the group "Bing–Jones 1959, IV (batch 201)"): 63 depend on `[propext, Classical.choice, Quot.sound]`,
2 on `[propext, Quot.sound]` (`zigN_lt`, `zigN_hits`), 1 on `[propext]` (`mod_eq_of_decomp`).
`sorryAx`: none. `axioms.txt` is regenerated (3776 lines, 66 more than batch 200's 3710; the first 3710 lines are unchanged and the last 66 are `doc/batches/audits/axioms-batch201.txt`). The theorems of the skeleton:

| theorem | axioms |
| --- | --- |
| `exists_point_only_of_minimal`, `adjacent_of_properCover`, `isFibreFine_of_isEpsChain` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_pattern` (and `exists_pattern_skeleton`) | the same |
| `bj_theorem8_cor_sub`, `bj_theorem5_window`, `exists_window_set` | the same |
| `bj_step`, `bjThm10_of_step`, `bjThm10` | the same |
| `ho16_classification_atomic'`, `isHomogeneous_of_isCircleOfPA'`, `homeomorph_of_isCircleOfPA'` | the same |
| `ho16_classification₃`, `ho16_classification_plane₃`, `nonvac_conditions` | the same |

## 8. Delivery

`doc/batches/batch201-files.tar.gz` with every file added or changed in this batch (the new Lean
files, the edited files, the commission and skeleton copies, this report, the audit and the
manifest), and `doc/batches/batch201-MANIFEST.txt`. As asked in commission §0, the tarball also
carries every Lean file under `HPC/Hagopian/`, `HPC/Jones/` and `HPC/Span/` in its current form
(listed in the manifest as `C`, current copy), so that the download has the 64 files missing from
the batch-199 and batch-200 downloads and the current versions of `Hagopian76P.lean` …
`Hagopian76V.lean` and `Hagopian84B.lean`.

## 9. What remains

The named input `BJPlaneExample` (Bing–Jones §7: a circle of pseudo-arcs in the plane). With it,
`ho16_classification₃` and `ho16_classification_plane₃` become unconditional. Optional, from
batch 199: `isAtriodic_of_atomic` (not attempted).
