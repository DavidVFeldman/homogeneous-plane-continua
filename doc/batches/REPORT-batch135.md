Commission read: `doc/batches/COMMISSION-batch135.md` (batch 135 — Part D, foundations: Jones 1948 complete; Jones 1951, the Lemma (and Theorem 1)).

# Report, batch 135

`lake build HPC` succeeds with `import HPC.Jones.Jones48` added at the end of `HPC.lean`. The eight
new files under `HPC/Jones/` (2025 lines) contain no `sorry`. `axioms.txt` is regenerated: it has
750 lines, 33 of them new (the group "Jones 1948, 1951 (batch 135)"), and `sorryAx` occurs in no
line. The per-batch audit `doc/batches/audits/axioms-batch135.{lean,txt}` lists every theorem of the
new files, 93 entries:
* 92 show exactly `[propext, Classical.choice, Quot.sound]`;
* `isHomogeneous_iff_isPretransitive` shows `[Quot.sound]`.

The previous `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch135.txt`.

**Summary.**
* Items A and B are proved: Jones 1948, Theorems 0–19 and the three Corollaries, and Jones 1951's
  `aposSet`, `isOpen_aposSet`, `IsHomogeneous` and the Lemma.
* Two statements are refuted as printed: Theorem 10, and Theorem 6 with `D = ∅`. Both are proved
  with `D` nonempty.
* Item C and `jones51_theorem1` are **open with the obstruction stated** (`OPEN.md`). The statement
  is kept as a comment, so it is not part of the build.

Housekeeping:
* the commission is at `doc/batches/COMMISSION-batch135.md`;
* the skeleton is at `doc/batches/skeletons/Jones48-batch135.lean`, verbatim;
* the three papers are at `doc/sources/jones1948.pdf`, `jones1951.pdf` and `jones1955.pdf`. They are
  git-ignored like the other PDFs there.

Edited files:
* `HPC.lean` (one import);
* `Axioms.lean` and `axioms.txt` (new group);
* `README.md` (a Part D entry, the `HPC/Jones` row, the batch count 135, the sources);
* `LEDGER.md` (§6, new subsection);
* `OPEN.md` (new section: `jones51_theorem1`).

No other existing file is edited.

## Files

| file | content |
|---|---|
| `HPC/Jones/Defs.lean` | the definitions of §1, verbatim from the skeleton; openness of the aposyndesis relation in `X × X`; finite covers (Heine–Borel); boundary bumping (`aposAt_of_frontier`); Baire (`exists_ball_subset_of_closed_cover`) |
| `HPC/Jones/Basic.lean` | equivalences with the repository's definitions; Theorems 0–5, 7–10; the refutation of Theorem 10 as printed |
| `HPC/Jones/Theorem6.lean` | Theorem 6 (Jones's nested construction) and its refutation without "`D` nonempty" |
| `HPC/Jones/Theorem13Aux.lean`, `HPC/Jones/Theorem13.lean` | Theorem 13 |
| `HPC/Jones/CutPoints.lean` | Theorems 11, 12, 14–19 and the three Corollaries |
| `HPC/Jones/Jones51.lean` | Jones 1951: `aposSet`, `isOpen_aposSet`, `IsHomogeneous`, the Lemma; Theorem 1 as a comment with the obstruction |
| `HPC/Jones/Jones48.lean` | the umbrella module (imports and index) |

## A. Jones 1948

All statements are in namespace `HPC.Jones`. The continuum is the whole space `X`: a compact,
connected metric space, as the skeleton asks.

**Definitions.** `AposAt`, `AposyndeticAt`, `IsAposyndetic`, `TotallyNonAposyndetic`,
`SemiLocConnAt`, `CutsPts`, `IsWeakCutPoint`, `IsStrongCutPoint`, `composant` and
`IsDecomposableSpace` are taken verbatim from the skeleton. The repository already has two of these
notions, so the equivalences are proved instead of duplicating them:
* `isDecomposableSpace_iff_not_isIndecomposable`: `IsDecomposableSpace X ↔ ¬ Fold.Q78.IsIndecomposable univ`;
* `composant_eq_composant_univ`: `composant x = HPC.composant univ x`.

| item | Lean | status | shape change / remark |
|---|---|---|---|
| Theorem 0 | `theorem0` | proved | — (proof not printed; see ledger) |
| Theorem 1 | `theorem1` | proved | hypotheses `x ≠ y` and `yᵢ ≠ xᵢ` dropped (not needed) |
| Theorem 2 | `theorem2` | proved | — (no proof printed); compactness not used |
| Theorem 3 | `theorem3` | proved | — (no proof printed) |
| Theorem 4 | `theorem4` | proved | — |
| Theorem 5 | `theorem5` | proved | — ("similar to Theorem 4") |
| Theorem 6 | `theorem6` | proved | `ConnectedSpace` not needed. **Refutation without "`D` nonempty"**: `not_theorem6_printed` |
| Theorem 7 | `theorem7` | proved | — |
| Theorem 8 | `theorem8` | proved | — |
| Theorem 9 | `theorem9` | proved | — |
| Theorem 10 (corrected, `D` nonempty) | `theorem10` | proved | `[Nontrivial X]` dropped (not needed) |
| Theorem 10 as printed | `theorem10_printed_iff`, `not_theorem10_printed_unitInterval` | **refuted** | as printed it says that every continuum is indecomposable; an arc (`unitInterval`, `isDecomposableSpace_unitInterval`) refutes it |
| Theorem 11 | `theorem11` | proved | `hzD : z ∉ D` dropped (it follows from `h2`); connectedness not used |
| Theorem 12 | `theorem12` | proved | — |
| Corollary p. 409 | `totallyNonApos_exists_weakCutPoint` | proved | `[Nonempty X]` dropped (`ConnectedSpace` includes it) |
| Theorem 13 | `theorem13` | proved | — |
| Theorem 14 | `theorem14` | proved | — |
| Theorem 15 | `theorem15` | proved | — |
| Corollary (Theorem 15) | `theorem15_cor` | proved | — |
| Theorem 16 | `theorem16` | proved | `[Nontrivial X]` dropped (the weak cut point `p` gives three points); compactness not used |
| Theorem 17 | `theorem17` | proved | `hp : IsWeakCutPoint p` dropped (unused); connectedness not used |
| Corollary (Theorem 17) | `theorem17_cor` | proved | `[Nontrivial X]` dropped (`hp` gives a point `≠ p`) |
| Theorem 18 | `theorem18` | proved | — |
| Theorem 19 | `theorem19` | proved | — |

Notes on the proofs.
* **Theorems 1 and 2.** The pairs `(x, y)` such that `X` is aposyndetic at `x` with respect to `y`
  form an open subset of `X × X` (`isOpen_setOf_aposAt`). Both theorems follow from this.
* **Theorem 3.** `L` is closed. For connectedness, suppose `L` splits with a piece `B` away from
  `y`. Separate `B` by an open `V` whose frontier misses `L`. Then `aposAt_of_frontier` (finitely
  many continua and boundary bumping) shows that `X` is aposyndetic at the points of `B` with
  respect to `y`, a contradiction.
* **Theorem 6.** This is Jones's construction: `Dₙ` decreasing, `Mₙ` closed with `diam → 0`, and
  `Dₙ₊₁` missing the component of `z` in the complement of a neighbourhood of `Mₙ₊₁`. The one step
  is `theorem6_step`. Footnote 6 allows `D` to meet `M₀`; the skeleton's `D ∩ M₀ = ∅` is kept,
  because it gives `x₀ ≠ y₀`.
* **Theorem 11.** Jones's proof, with `M₀` the points at distance at least `1/(n+1)` from a point
  of a small closed ball at which `X` is not aposyndetic with respect to them. This set is closed
  because it is a projection of a closed set in a compact square. Baire, then Theorem 6.
* **Theorem 12.**
  * Decomposable case: as printed (Theorem 10, then Theorem 11).
  * Indecomposable case: a point `z` outside the composant of `x`, from the repository's
    `HPC.T13.exists_not_mem_proper_subcontinua`, and any third point. The density of composants is
    not needed.
* **Theorem 13.** This is the longest proof. The recursion is one configuration per stage (the
  point `xₙ`, the radius of `Vₙ`, the separation `Wₙ ∪ Qₙ`), with the invariant `T13J.Good` and the
  link `T13J.Rel`. The supporting lemmas are:
  * `exists_split_of_not_aposAt`: "`M − V₁` is the sum of two mutually exclusive closed sets each
    containing a point of `M − U(A, ε)`";
  * `separation_nested`: "`Q₂` contains `Q₁` and `W₁` contains `W₂`".

  Jones's finite families `H_{n1}, …` become a uniform radius (`exists_radius_uniform_apos`). His
  choice of `V₂` is supplemented by `cl V₂ ⊆ W₁`, which his next sentence uses. The point `z` is
  found in `⋂ Wₙ` on the sphere `d(·, A) = ε`, and `y` is a cluster point of the `xₙ`.
* **Theorem 14.** It really is immediate: apply Theorem 13 to each nonempty open set.
* **Theorems 15, 18, 19.** These are proved as sketched; see the ledger. Theorem 18: the set is
  `⋂ₙ (Fₙᶜ ∩ Gₙᶜ)`, with `Fₙ` and `Gₙ` the closed sets of Theorems 4 and 5. Each `Fₙ` and each
  `Gₙ` has empty interior, by Theorems 12 and 15 with no weak cut point. Baire
  (`dense_iInter_of_isOpen`) then gives density.

## B. Jones 1951

| item | Lean | status | remark |
|---|---|---|---|
| `U_x` | `aposSet` | definition | verbatim; `aposSet_eq`: `U_x = {z | AposAt z x}` |
| "`U_x` is open" | `isOpen_aposSet` | proved | — |
| homogeneous | `IsHomogeneous` | definition | verbatim. It is the hypothesis `hom` of `HPC.Effros.effros_homogeneous`, and `isHomogeneous_iff_isPretransitive` identifies it with `MulAction.IsPretransitive (X ≃ₜ X) X` for the repository's evaluation action |
| **Lemma** | `jones51_lemma` | **proved** | `hxy : x ≠ y` dropped (unused; trivial when `x = y`) |
| Theorem 1 | — (comment in `Jones51.lean`) | **open** | obstruction below and in `OPEN.md` |

**The Lemma without transfinite recursion.** Let `B₀, B₁, …` be a countable base and set
`g(w) = ∑ₖ [cl Bₖ ⊆ U_w] · 2⁻ᵏ` (in `ℝ≥0∞`). The proof has four steps:
1. `{w | cl Bₖ ⊆ U_w}` is open. Its complement is the projection of a closed subset of the compact
   space `X × X` (`isOpen_setOf_subset_aposSet`). So `g` is lower semicontinuous.
2. If `U_a ⊊ U_b`, take `v ∈ U_b − U_a` and a `Bₖ ∋ v` with `cl Bₖ ⊆ U_b`. Then `g a < g b`
   (`exists_lsc_strictMono_aposSet`).
3. `g` attains its minimum on the compact `X` at some `w₀`.
4. If `U_y ⊊ U_x`, a homeomorphism `T` with `T x = w₀` gives `U_{T y} = T(U_y) ⊊ T(U_x) = U_{w₀}`
   (`aposSet_homeomorph`), so `g(T y) < g(w₀)`, a contradiction.

The two steps the commission asks to check in Jones's proof:
* **"Evidently `x_ω ≠ xₙ`."** Correct: `U_{x_ω} ⊆ U_{x_{n+1}} ⊊ U_{xₙ}`.
* **The continuation at limit stages.** It works the same way. The formal proof does not need
  either step.

**Theorem 1 (stretch): open.**

The Lemma is available, and so is Jones 1948, Theorem 9. Bing's Corollary 2, which Jones cites, is
in the repository (`HPC.Plane.arcs_corollary2`) up to a transfer by homogeneity. Two things are
missing:
1. The decomposition space (item C). An upper semicontinuous decomposition of a compact metric
   space into closed sets has a compact metrizable quotient, and the quotient map is closed.
2. Whyburn 1939, Theorem 6.21: in an aposyndetic continuum, weak cut points are separating points.
   It is applied in the quotient.

Neither is in Mathlib or the repository, and neither was started in this batch.

## C. What Jones 1955, Theorem 1 will need from the decomposition-space side

Jones 1955 forms `G = {L_x}` and shows that, with its elements as points, it is a homogeneous
aposyndetic continuum. From the decomposition-space side this needs:

1. **Quotient.** For an upper semicontinuous decomposition `G` of a compact metric `X` into closed
   sets, the quotient space `X/G` (Mathlib's `Quotient` of the `Setoid`) satisfies:
   * it is compact;
   * it is `T2`, hence `T3` (being compact);
   * it is second countable;
   * hence it is metrizable (`TopologicalSpace.metrizableSpace_of_t3_secondCountable`);
   * the quotient map is closed, continuous and surjective.

   Connectedness passes to the quotient, so `X/G` is a continuum.
2. **Upper semicontinuity of `{L_x}`.** This is Jones 1955's (f), from Theorem 3 of 1948 (now
   `theorem3`) and Theorem 1 (`theorem1`).
3. **Continuity.** Jones writes "`G` must be continuous at one of its elements". This is the
   unstated theorem that an upper semicontinuous decomposition of a compact metric space is
   continuous at the elements of a residual set (a Baire argument on the decomposition space). With
   homogeneity, `G` is then continuous everywhere.
4. **Homeomorphisms descend.** A homeomorphism of `X` that permutes the elements of `G` induces a
   homeomorphism of `X/G`. This gives homogeneity of `X/G` from that of `X`, since `T(L_x) = L_{T x}`
   (the analogue of `aposSet_homeomorph`).
5. **Aposyndesis passes to the quotient.** Preimages of subcontinua of `X/G` are subcontinua of `X`,
   because the elements are continua and the map is monotone and closed.

Items 1 and 4 are general. They should be stated for an arbitrary upper semicontinuous
decomposition, as the commission suggests.

## Ledger entries (`LEDGER.md` §6, new subsection)

* **Refuted:**
  * Theorem 10 as printed (`theorem10_printed_iff`, `not_theorem10_printed_unitInterval`);
  * Theorem 6 without "`D` nonempty" (`not_theorem6_printed`).
* **Implicit hypotheses:** Theorems 11, 12, 13 and 19 need `D` (resp. `U`) nonempty. Theorem 16
  needs a third point.
* **No proof printed:** Theorems 2, 3, 0 and 5. The ledger says what each proof needs: openness of
  the aposyndesis relation; boundary bumping; finite covers; projections.
* **Sketches:** Theorems 14, 15, 18 and 19. All four go through as indicated.
* **Theorem 16:** "`P`" for "`p`", a misprint.
* **Jones 1951, Lemma:** the checks above, and the proof without transfinite recursion.
* **Jones 1955 citations:** both suspicions of the commission are confirmed on the page images.
  * Theorem 2's last step, "Hence by [5], `G` is a simple closed curve", cites Jones 1951. The
    result used is Jones 1949, which is [3] in the introduction. This is a citation slip.
  * Theorem 1's continuity step uses the unstated residual-continuity theorem.
