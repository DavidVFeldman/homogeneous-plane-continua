Commission read: `doc/batches/COMMISSION-batch199.md` ("Commission: batch 199 — Part G, II: Domokos–Prajs Theorem 6.1; Bing–Jones Theorems 7 and 9").

# Report, batch 199

## 0. Summary, omissions, shape changes

**Every theorem of the skeleton is proved except the stretch item `bj_theorem9` and the optional
`isAtriodic_of_atomic`**, which are commented out in `HPC/BJ59/BJ59B.lean` with their obstructions
in `OPEN.md`. All statements of the skeleton are verbatim (no shape changes). The second sentence of
Bing–Jones's Theorem 7 is refuted as printed for one link (`bj_theorem7_ends_printed_false`) and
proved for `n ≥ 3` (`bj_theorem7_ends`). The 114 new theorems of the batch audited in
`doc/batches/audits/axioms-batch199.txt` (104, plus 10 for the optional items of §7 done in a
continuation of the batch), and the three batch-198 `@[simp]` lemmas of commission §0, depend on at most `[propext, Classical.choice, Quot.sound]`; `sorryAx` occurs in none.

```
STATUS: IsAtomicMap, IsAtomicCircPAMap defined; isAtomicMap_id, not_isAtomicMap_snd proved
STATUS: isHereditarilyUnicoherent_of_atomic proved (unconditional)
STATUS: isSnakeLike_of_atomic' proved (unconditional)
STATUS: isSnakeLike_of_atomic proved (unconditional)
STATUS: isCircleLike_circle, isCircleLike_univ_of_homeomorph proved
STATUS: isSnakeLike_halfSet_of_atomic proved
STATUS: dp22_theorem61 proved (from BJThm10)
STATUS: homeomorph_of_atomic, isHomogeneous_of_atomic, isCircleOfPA_of_atomic proved (from BJThm10)
STATUS: isAtriodic_of_atomic open (optional; commented out; not attempted)
STATUS: circle_or_atomic_of_decomposable proved (unconditional)
STATUS: hoCircleLike proved (from BJThm10, BJPlaneExample)
STATUS: ho16_classification_atomic proved (from BJThm10)
STATUS: ho16_classification₂, ho16_classification_plane₂ proved (from BJThm10, BJPlaneExample)
STATUS: IsBJChain defined; exists_bjChain_shrink, exists_bjChain_three proved
STATUS: bj_theorem7 proved (every n)
STATUS: bj_theorem7_ends proved (n ≥ 3; hypothesis hHs unnecessary, kept)
STATUS: bj_theorem7_ends_printed_false proved
STATUS: bj_theorem9 open (stretch; commented out; not attempted)
STATUS: optional BJ.5 general certificate proved (bj_theorem5_printed_false_general, n ≥ 3)
STATUS: optional IsBJChain ↔ IsTaut proved (isBJChain_iff_isTaut, any metric space)
```

**Omissions.**
* `bj_theorem9` (commission §6, stretch): not attempted. The proof (pp. 179–181) builds a
  homeomorphism by a back-and-forth through two sequences of chains with refining chain maps; it
  needs a two-sided form of `Description.exists_homeomorph` and the bridge from `IsBJChain` chains
  to descriptions.
* `isAtriodic_of_atomic` (commission §4/§7, optional): not attempted. Not used by any theorem.
* The other optional items of §7 (BJ.5 as a lemma; `IsBJChain D ↔ IsTaut D`) are done, in a
  continuation of this batch (§5a).

## 1. §2: atomic maps (`HPC/BJ59/Atomic.lean`)

`IsAtomicMap f`: every continuum meeting two fibres is saturated, as in the skeleton.
`subset_fibre_or_saturated`, `fibre_subset_of_saturated`; tests: `isAtomicMap_id`,
`not_isAtomicMap_snd` (`Prod.snd` on `[0,1]²` is not atomic), `isAtomicMap_const`
(`NonVac199.lean`).

## 2. §3: atomic arcs are snake-like (`HPC/BJ59/Atomic.lean`)

Bing's 1951 argument, as planned in the commission. `nested_of_common_bound`,
`condB_preimage_Icc` (preimages of subintervals under an atomic map are continua),
`isPreconnected_preimage_of_fibres`, `isHereditarilyUnicoherent_of_atomic`,
`isContinuum_univ_of_fibres`; then `isSnakeLike_of_atomic'` (fibres snake-like and hereditarily
indecomposable), and `isSnakeLike_of_atomic` (fibres pseudo-arcs). No shape theory.

## 3. §4: atomic circle maps (`HPC/BJ59/CircleLike.lean`, `HPC/BJ59/AtomicCircle.lean`)

The circle is circle-like (`isCircleLike_circle`, by the arcs `circArc n k`, `n ≥ 4`), invariant
under homeomorphism (`isCircleLike_univ_of_homeomorph`). The half-maps of an atomic map are atomic
(`isAtomicMap_halfMap`); the halves are continuous arcs of pseudo-arcs
(`isContArcPA_halfMap_of_atomic`) and snake-like (`isSnakeLike_halfSet_of_atomic`, by §3). The
gluing of batch 198 is rerun from snake-like halves (`IsSnakeHalvesMap`, with
`IsCircPAMap.isSnakeHalvesMap` and `IsAtomicCircPAMap.isSnakeHalvesMap`; `exists_half_homeomorph'`,
`exists_homeomorph_glue'`, `homeomorph_of_isSnakeHalvesMap`), giving `dp22_theorem61`,
`homeomorph_of_atomic`, `isHomogeneous_of_atomic` (rotations: `IsAtomicCircPAMap.mul_left`) and
`isCircleOfPA_of_atomic`, all from `BJThm10`.

## 4. §5: the decomposable case and the classification (`HPC/BJ59/BJ59B.lean`)

As planned in commission §5: `circle_or_atomic_of_decomposable` (atomicity from `jones55_c`),
`hoCircleLike`, `ho16_classification_atomic`, `ho16_classification₂`,
`ho16_classification_plane₂`.

## 5. §6: Bing–Jones Theorem 7 (`BJChains.lean`, `Thm7Fold.lean`, `Thm7Core.lean`, `Thm7.lean`, `Thm7Ends.lean`, `Thm7Ends2.lean`)

* `IsBJChain` and `exists_bjChain_shrink` (shrink a chain covering a continuum so that nonadjacent
  links are at positive distance), `exists_bjChain_three`.
* Folding (`foldChain`): following a walk with steps of at most one and folding back through a
  section gives a chain.
* `bj_theorem7`: `D` is put in front of a late level of a description of `P` (`prependDesc`), the
  pattern `H` is followed along the walk `r, r − 1, …, 0, …, m − 1, …, s` in a chain from a point
  of one composant to a point of another (`exists_chain_isFrom`), and folded; every `n`, no special
  case.
* `bj_theorem7_ends` (`n ≥ 3`): the printed `D′` is replaced by a collar chain of `n + 4` links
  (`exists_collar_chain`), the walk padded at both ends (`bufIdx`, `bufPat`), then
  `bj7_ends_compact` and `bj_theorem7_ends'`. The surjectivity hypothesis `hHs` is not used (noted
  in the docstring; kept as stated).
* `bj_theorem7_ends_printed_false`: a plane pseudo-arc, one link, `m = 3`, `H` constant,
  `A = B = {p}`, `r = 1`, `s = 3`.

## 5a. §7, optional items (`HPC/BJ59/Thm5Cert.lean`, `HPC/BJ59/Taut.lean`)

* `bj_theorem5_printed_false_general` (BJ.5, the general certificate): from a compact space, a
  continuous map to `[0, 1]` and a chain of `n ≥ 3` links covering the space and meeting every fibre
  in every link (the printed hypotheses on `X`, `f` are untouched and need not be assumed), a chain
  `E′` of `n` links with the same properties and an open `U` meeting the printed hypotheses on `U`,
  with no fibre inside `U`, and with the last link of `E′` meeting `g_{1/2}` only inside `U`, so the
  printed conclusion fails for every `A`, `B` with `A ∪ B = G − U`. Shape: the merge is done in
  place (`chainMergePenult`, last-but-one link enlarged by the last) rather than by
  `chainMergeLast` and re-appending; `U = N_δ(cl(g_{1/2} · e_n)) − cl(e₁)`. The commission's
  "`cl(e_n) ⊆ e_{n−1}` can be arranged" is not needed (`closure_last_subset`: `cl(e_n) ⊆
  e_{n−1} ∪ e_n` for a chain covering the space); removing `cl(e₁)` makes "no fibre in `U`" hold
  for `n = 3`. Hypotheses met with non-degenerate fibres: the unit square, the first projection,
  three horizontal strips (`squareStrips`, `nonvac_bj_theorem5_printed_false_general`).
* `isBJChain_iff_isTaut`, with `infDist'_pos_iff`: in every metric space (compactness, asked by the
  commission, is not needed; the links of a chain are nonempty).

## 6. Non-vacuity

* `isSnakeLike_of_atomic'` and the §3 lemmas: `nonvac_isSnakeLike_of_atomic'` (`[0,1]`, identity).
* `isSnakeLike_of_atomic`, §4, the second alternative of `circle_or_atomic_of_decomposable`:
  `nonvac_atomic` (under `BJThm10` and `BJPlaneExample`). No unconditional witness found.
* `circle_or_atomic_of_decomposable`, `ho16_classification_atomic`: `nonvac_plane_circle`.
* `bj_theorem7`: `nonvac_bj_chains` (a plane pseudo-arc with a Bing–Jones chain of at least three
  links, `H = id`); `bj_theorem7_ends`: `nonvac_bj_theorem7_ends` (`NonVac199.lean`).
* Definitions on degenerate inputs: `isAtomicMap_id`, `isAtomicMap_const`, `not_isAtomicMap_snd`;
  `isBJChain_of_le_two` (chains of at most two links), `not_isBJChain_real3` (the three links
  `(0,2)`, `(1,3)`, `(2,4)` of `ℝ`).
* `bj_theorem9`: not stated in the build (commented out).

## 7. Ledger

New section "Domokos–Prajs 2022 and Bing–Jones §§4–5 (batch 199)" of `LEDGER.md`: DP.1 (atriodicity,
not supplied), DP.2 (the "only if" direction; supplied in the plane), DP.3 (the halves; replaced by
§3), DP.4 (the two definitions), BJ.17 (misprint "of" for "if"), BJ.18 (Theorem 7, second sentence,
false for `n ≤ 2`; certificate), BJ.19 (Theorem 7, proof: nine defects (a)–(i), (e) repaired by the
collar chain), BJ.20 (Theorem 9; not formalized); and, for the optional items, BJ.5 revisited (the general
certificate, now formalized) and a note on `IsBJChain ↔ IsTaut`. Proposed for the count: BJ.18 (a degenerate false
printed statement) and BJ.19 (a defective proof). The counts are left unchanged pending the
commissioner's decision.

## 8. Axioms

`doc/batches/audits/axioms-batch199.txt` (117 lines: 114 theorems of this batch, including the 10 of
the optional items of §7, and the three batch-198 `@[simp]` lemmas, added to `Axioms.lean` under
"Bing–Jones 1959, II (batch 199)"). 99 depend on `[propext, Classical.choice, Quot.sound]`, 16 on
`[propext, Quot.sound]`, 2 on none. `sorryAx`: none. `axioms.txt` is regenerated (3624 entries; the
first 3507 are unchanged from batch 198).

## 9. Dependency map of the named inputs (Parts F–G, after this batch)

* **`BJThm10` only:** `isHomogeneous_of_isCircleOfPA`, `homeomorph_of_isCircleOfPA`,
  `exists_half_homeomorph`, `exists_half_homeomorph'`, `exists_homeomorph_glue`,
  `exists_homeomorph_glue'`, `homeomorph_of_isCircPAMap`, `isHomogeneous_of_isCircPAMap`,
  `homeomorph_of_isSnakeHalvesMap`, `dp22_theorem61`, `homeomorph_of_atomic`,
  `isHomogeneous_of_atomic`, `isCircleOfPA_of_atomic`, `ho16_classification_atomic`.
* **`BJThm10` and `BJPlaneExample`:** `hoCircleLike`, `ho16_classification₂`,
  `ho16_classification_plane₂`, `nonvac_atomic`.
* **`HOCircleLike` (still a hypothesis):** batch 198's `circle_or_circleOfPA_of_decomposable`,
  `ho16_classification` (with `BJThm10`), `ho16_classification_plane` (with `BJThm10`,
  `BJPlaneExample`); each is superseded by the batch-199 version above.
* **None:** Part F (`HPC/HO16`); §§2–3 of this batch; `circle_or_atomic_of_decomposable`; all of
  Theorem 7 (`bj_theorem7`, `bj_theorem7_ends`, the certificate); the optional items of §7
  (`bj_theorem5_printed_false_general`, `isBJChain_iff_isTaut`).
