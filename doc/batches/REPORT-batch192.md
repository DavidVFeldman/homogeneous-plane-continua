Commission read: `doc/batches/COMMISSION-batch192.md` ("Commission: batch 192 — Theorem C II: the strip theorem; `OTThm32`; Theorem C").

# Report, batch 192

## 0. Summary, omissions

**Every item of commission §3–§7 is proved, ending with `ot82_theorem32 : OTThm32` and
`theoremC : TheoremC`.** `TheoremC` (Hoehn–Oversteegen's Theorem C: every homogeneous indecomposable
plane continuum has span zero) now holds **without hypotheses**. `crossing_traces_separated`
(commission 191 §7) is proved as a live statement (§6). The skeleton is split over five files
under `HPC/Span/`:

* `HPC/Span/OT82Parity.lean` (§3: parity tools),
* `HPC/Span/OT82Zero.lean` (§4: a common zero on a rectangle),
* `HPC/Span/OT82Strip.lean` (§5: `plPath`, `stripPoly`, `StripInner`, `stripSign`, the strip lemma),
* `HPC/Span/OT82Order.lean` (§6: `crossing_traces_separated`),
* `HPC/Span/OT82B.lean` (§7: `ot82_theorem32`, `theoremC`; index of the split).

`HPC.lean` ends with `import HPC.Span.OT82B`; `lake build HPC` succeeds (8737 jobs). The commented-out
copy of `crossing_traces_separated` at the end of `HPC/Span/OT82A.lean` is replaced by a one-line
pointer. No declaration contains `sorry`, `admit` or `axiom` (the word "sorry" occurs only in the
sentence "Nothing in this file or the four files above is `sorry`" of the `OT82B.lean` header).
Nothing is refuted.

`axioms.txt` has **2658 lines** (2595 + 63 added, none removed). `sorryAx` occurs in none of them.
The 63 new theorems (group "Theorem C II (batch 192)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch192.txt`) use only standard axioms (§4).

**Omissions.** None. The three "shape left to you" items of §5 (`strip_basic`,
`parity_strip_eventually`, `strip_sign_continuous`, stated as `True` in the skeleton) are replaced
by real statements (below); this is a shape change, not an omission.

Status lines:
* STATUS: §3.1 `parity_eq_zero_of_not_mem_convex` proved
* STATUS: §3.2 `parity_eq_of_perturb` proved
* STATUS: §3.3 `parity_flip_vertical_edge` proved
* STATUS: §4 `common_zero_rect` proved
* STATUS: §5.1 `strip_basic` proved (as a list of lemmas, see below)
* STATUS: §5.2 `parity_strip_eventually` proved
* STATUS: §5.3 `strip_sign_continuous` proved (as `stripInner_eventually`, `stripSign_continuousOn`
  and the boundary facts)
* STATUS: §5.4 `strip_lemma` proved
* STATUS: §6 `crossing_traces_separated` proved
* STATUS: §7 `ot82_theorem32` proved
* STATUS: §7 `theoremC` proved

## 1. The items

Statements were compared mechanically with `doc/batches/skeletons/OT82B.lean` (whitespace
normalized): `parity_eq_zero_of_not_mem_convex`, `parity_eq_of_perturb`, `common_zero_rect`,
`plPath`, `stripPoly`, `strip_lemma`, `crossing_traces_separated`, `ot82_theorem32` and `theoremC`
are **identical** to the skeleton. The shape changes are listed with each item and are also recorded
at the statements.

### §3 Parity tools (`OT82Parity.lean`)

* **3.1 `parity_eq_zero_of_not_mem_convex`: proved**, as in the commission: the polygon lies in the
  convex `C` (`polygonOf_subset_of_convex`); a half-plane through `z` missing `C`
  (`geometric_hahn_banach_point_closed`) is preconnected and contains far points, where the parity
  is `0`.
* **3.2 `parity_eq_of_perturb`: proved.** Departure in the proof: instead of moving one vertex at a
  time, the difference of the two crossing counts is written at once (by `parity_eq_sum`) as the
  sum over `i` of the parities of the quadrilaterals `[v i, v (i+1), w (i+1), w i]`
  (`parity_four`); each lies in the `ρ`-thickening of the edge `[v i, v (i+1)]`, a compact convex
  set not containing `z`, so its parity vanishes by 3.1. The edges `[v i, w i]` occur twice and
  cancel mod 2. No case `n ≤ 2` is needed.
* **3.3 `parity_flip_vertical_edge`: proved. Shape change:** the skeleton's hypothesis `hr : 0 < r`
  is dropped (it follows from `0 < ξ < r`); a generalization.

`mem_segment_coords` (coordinates of a point of a segment lie between those of the ends) is a
helper in this file.

### §4 A common zero on a rectangle (`OT82Zero.lean`)

* **`common_zero_rect`: proved**, as in the commission: `HPC.Moore.exists_log_of_convex` gives a
  continuous logarithm of `φ + iψ` on the rectangle; its imaginary part on each side lies in a
  single closed interval of length `< 2π` (helper `mem_Ioo_of_avoid`: a continuous function on a
  preconnected set avoiding the points `c + 2πk` stays in one gap); the four sides force
  incompatible branches at `(0, p)`.

### §5 Strips (`OT82Strip.lean`)

* `plPath` and `stripPoly`: **definitions unchanged.**
* **§5.1 `strip_basic` (shape left open): proved as a list of lemmas:** `plPath_zero`, `plPath_one`,
  `continuous_plPath`, `plPath_eq_piece`, `dist_plPath_le`, `stripPoly_edge_cases`,
  `polygonOf_stripPoly_subset`, `parity_stripPoly_zero_of_fst_ne`, `parity_stripPoly_left`.
* **§5.2 `parity_strip_eventually`: proved**, stated for every `t₀` (no `t₀ ∈ [0, 1]` is needed):
  for `z₀ ∉ S_{t₀}`, eventually near `(t₀, z₀)` the point `x.2` is off `S_{x.1}` with the same
  parity. Proof by `parity_eq_of_perturb` (the vertices of `stripPoly` are continuous in `t`).
* **§5.3 `strip_sign_continuous` (shape left open): proved as** `stripInner_eventually` (the
  predicate `StripInner a b t z` — "`z` is on `x = 0`, or off `S_t` with parity `1`" — is locally
  constant near any `(t₀, z₀)` with `z₀` off `f`, `g` and `B_{t₀}`), `stripSign_continuousOn` (the
  sign function `stripSign a b h (t, u) = ∓ dist(h u, B_t)`, with sign `−` when `h u` satisfies
  `StripInner`, is continuous on `[0, 1]²` for a path `h` staying in `{x ≥ 0}` off `f[0, 1]` and
  `g[0, 1]`, meeting `x = 0` only inside `B₀`), and the boundary facts `stripSign_zero_nonneg`,
  `stripSign_nonpos_of_inner`, `stripSign_eq_zero`. **Shape change:** the set `V` of the commission
  is not used; its role is taken by the predicate `StripInner` (new definition).
* **§5.4 `strip_lemma`: proved; statement as in the skeleton.** Departure in the proof: step 1 of
  the commission (`W ∖ L₀ ⊆ U₁`) is `stripInner_one_of_isPreconnected` (`StripInner a b 1` is
  locally constant on the region off `f`, `g`, `B₁`, holds on `W ∩ L₀`, and `W` is connected); no
  boundary bumping. Step 3 (chains) uses `exists_eps_chain` in the span witness `Z` and segments of
  length `< η` between consecutive points (`η` below the distance from `W` to `f ∪ g ∪ B₁` and below
  a third of `min d − ε`); the two paths satisfy the hypotheses of §4 and a common zero gives a
  pair at distance `≤ ε` on one `B_t`.

### §6 Order of disjoint crossing continua (`OT82Order.lean`)

* **`crossing_traces_separated`: proved; statement as in the skeleton** (commission 191 §7). The core
  (`crossing_core`) is the crossing-parity argument of the commission: a polygonal path inside a thin
  neighbourhood of one continuum (`polyReach_of_isPreconnected`) is closed up by a detour outside the
  strip (`detour_edge_cases`), and the parities just left and right of the other continuum's trace
  point are compared using `crossing_ge_of_subset`, `crossesEast_vertical` and
  `ceInd_eq_of_right`. No Jordan curve theorem and no arc.

### §7 Theorem 3.2 (strip form) and Theorem C (`OT82B.lean`)

* **`ot82_theorem32 : OTThm32`: proved; statement as in the skeleton.** Departures in the proof
  (recorded at the statement): the scale is `1/(n+1)` instead of `1/n` (so no `n ≥ 1` case split)
  and the cluster radius is `ρ = 1/(n+1)/4` instead of `1/(16n)`; only `3ρ < 1/(n+1)` is used.
  Steps 1–6 as in the commission; helpers `exists_not_countable_of_cover` (countable cover of an
  uncountable set), `exists_pos_sep` (positive distance between a compact and a disjoint closed
  set) and `exists_between_three` (among three distinct indices in a linear arrangement one lies
  between the other two, used with §6).
* **`theoremC : TheoremC := theoremC_of_thm32 ot82_theorem32`: proved, no hypotheses.**

## 2. Non-vacuity notes

* **`ot82_theorem32 : OTThm32` and `theoremC : TheoremC`** have no hypotheses. `OTThm32` and
  `TheoremC` are named `Prop`s that are now *conclusions*: the hypothesis `OTThm32` of
  `theoremC_of_thm32`, `ot82_cor35_of_thm32` and `cor35_core` (batch 191) is discharged. The
  batch-191 non-vacuity note for `OTThm32` (an instance of its hypotheses: horizontal segments
  `K t = [0, 1] × {t}`) still applies.
* **`strip_lemma`** (hypothesis `Fold.Q78.IsContinuum W`, a structure-like named `Prop`, and the
  strip conditions).
  1. Not refuted: `s = 1`, `a = ![(0, 0), (1, 0)]`, `b = ![(0, 1), (1, 1)]`, `ε = 1`,
     `W = [(0, ½), (½, ½)]` (a segment, a continuum) satisfy every hypothesis: `W` lies in
     `{x ≥ 0}`, meets `x = 0` only at `(0, ½) ∈ openSegment (a 0) (b 0)`, and misses `f[0, 1]`
     (`y = 0`), `g[0, 1]` (`y = 1`) and `B₁` (`x = 1`).
  2. Not equivalent to the conclusion: the hypotheses say nothing about span witnesses `Z`; the
     conclusion (every surjective-span witness of `W` meets `{d ≤ ε}`) is O–T's Theorem 2.7 and is
     proved by contradiction from the printed argument's own route (sign functions and §4).
* **`crossing_traces_separated`** (hypotheses `IsContinuum K`, `IsContinuum K'`).
  1. Not refuted: `K = [a, b] × {0}`, `K' = [a, b] × {1}` satisfy them.
  2. Not equivalent to the conclusion (the hypotheses do not mention the order of traces).
* **`common_zero_rect`**: only continuity and sign hypotheses; satisfied e.g. by
  `φ(t, u) = (1 − t)(u − p) − t`, `ψ(t, u) = (1 − t)(q − u) − t`; the conclusion (a common zero) is
  not among them.
* **`parity_eq_zero_of_not_mem_convex`, `parity_eq_of_perturb`, `parity_flip_vertical_edge`**:
  hypotheses are elementary metric conditions on a polygon, satisfiable by a square around the
  origin; none is a named `Prop` about the conclusion.
* **Helpers of §5 with named-`Prop` hypotheses** (`StripInner` in `stripSign_nonpos_of_inner`,
  `stripInner_one_of_isPreconnected`): `StripInner a b t z` holds for any `z` on `x = 0`, so the
  hypothesis is satisfiable; it is not the conclusion.

## 3. Ledger entries (`LEDGER.md`, section "Oversteegen–Tymchatyn 1982 and Cook 1967")

The "Outcome" bullet of the section now records that the two items open in batch 191 are proved in
batch 192. New checks OT.8–OT.13, with the printed sentences quoted:

* **OT.8 (Theorem 2.7, p. 136, the continua `H` and `K`):** "It is easy to see that the first part of
  Lemma 2.3 is valid even if (π₁ ∘ f)⁻¹(b) ≠ 1 ≠ (π₁ ∘ g)⁻¹(b) so there exists a continuum H in C
  such that (0,p) ∈ H and H meets both I × {0} and I × {1}" and "Clearly, K ∩ H ≠ φ".
  **Both unargued; neither found false** (the first needs a further separation argument to pass
  through `(0, p)`; the second a crossing argument in `I²`, true by a hand argument). **Both
  replaced** by `common_zero_rect`. Gaps; not counted.
* **OT.9 (continuity of `φ` when `(π₁ f)⁻¹(b) ≠ {1}`): confirmed, `φ` can be discontinuous** where
  `h` passes through a point `f(t₀) ∈ B₁`, `t₀ < 1` (on `x ∈ [t₀, 1)` the point is on `S_x`, sign
  `+`, while nearby inner points give sign `−`). Harmless here: `W` misses `B₁`, `f`, `g`, and
  `stripSign_continuousOn` is proved on the set used.
* **OT.10 (Remark 2.5 and Lemma 2.4, pp. 134–135):** "Lemma 2.4 is particularly useful if an
  arbitrary continuum X of positive (semi-)span is embedded in a locally connected continuum Y.
  Moreover, we can choose Y to lie in an arbitrary small neighbourhood of X (cf. the proof of
  Theorem 2.6)." **Not needed;** the `Y` would have to stay inside `U ∪ B₀ ∪ B₁`, impossible in
  general near `B₀` and not argued. Gap in exposition; not counted.
* **OT.11 ("the component of U₁ whose boundary meets each of f(I) and g(I) in a nondegenerate
  continuum"):** presumes uniqueness, unargued; the boundary condition is unused; here `U₁` itself
  (`StripInner a b 1`) serves. Not counted.
* **OT.12 (Theorem 3.1, p. 137):** "Let λ₁,λ₂,λ₃ ∈ Λ such that h_λ₂(X) separates h_λ₁(X) from
  h_λ₃(X) in [0,1] × R." **Unargued;** supplied for crossing images by `crossing_traces_separated`
  and step 3 of §7 (`exists_between_three`). Hilbert-cube arcs not needed.
* **OT.13 (classification):**
  * **Theorem 3.2: proof defective** (identified failure: the two `δ` suppositions of OT.4 are not
    available together); **statement not decided** (only the strip form `OTThm32` is proved).
    I agree with the commission's proposal on the classification, but **the count is not
    raised**: the ledger counts a defective proof only once the statement is verified or refuted
    (Whyburn 1939: "Since Theorem 14 is verified, the inversion (check 8) is now counted"; Hagopian
    1976 I: "No defective proof is added while these are unsettled"). The printed Theorem 3.2 is
    unsettled, so it is recorded as defective but not counted.
  * **Theorem 2.7: unargued steps (OT.8), replaced;** the form used is proved (`strip_lemma`).
  * **Theorem 3.1:** separating triple unargued (OT.12).
  * **Corollary 3.5** (`OTCor35`) is now verified; its gaps (OT.3) are not counted.
  * No statement refuted; no defective proof added; **the count stays at sixteen.**

## 4. Axioms

Every one of the 63 new theorems uses a subset of `[propext, Classical.choice, Quot.sound]`
(62 exactly these three; `exists_between_three`: `[propext]`); the list with one line per theorem is `doc/batches/audits/axioms-batch192.txt`. In
particular:

| theorem | axioms |
|---|---|
| `HPC.Span.ot82_theorem32` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.theoremC` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.strip_lemma` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.crossing_traces_separated` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.common_zero_rect` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.stripSign_continuousOn` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.parity_strip_eventually` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.stripInner_one_of_isPreconnected` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.parity_eq_of_perturb` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.parity_eq_zero_of_not_mem_convex` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.parity_flip_vertical_edge` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.exists_between_three` | `propext` |

## 5. Dependency map of `theoremC`

**No open input.** Every node is proved.

```
theoremC : TheoremC                                           (§7, OT82B)
└─ theoremC_of_thm32 : OTThm32 → TheoremC                     (batch 191, OT82A)
   ├─ ot82_theorem32 : OTThm32                                (§7, OT82B)
   │  ├─ strip_lemma                                          (§5.4, OT82Strip)
   │  │  ├─ common_zero_rect ← exists_log_of_convex           (§4, OT82Zero; Moore/Borsuk)
   │  │  ├─ stripSign_continuousOn ← stripInner_eventually
   │  │  │     ← parity_strip_eventually ← parity_eq_of_perturb (§5.2–5.3; §3.2)
   │  │  │     ← parity_flip_vertical_edge                    (§3.3)
   │  │  ├─ stripInner_one_of_isPreconnected                  (§5.4)
   │  │  ├─ stripSign_zero_nonneg, stripSign_nonpos_of_inner,
   │  │  │     stripSign_eq_zero                              (§5.3)
   │  │  ├─ parity_stripPoly_left, parity_stripPoly_zero_of_fst_ne
   │  │  │     ← parity_eq_zero_of_not_mem_convex             (§5.1; §3.1)
   │  │  └─ exists_eps_chain                                  (§5.4)
   │  ├─ crossing_traces_separated ← crossing_core            (§6, OT82Order)
   │  │     ← polyReach_of_isPreconnected, detour_edge_cases,
   │  │       parity_eq_of_isPreconnected (Plane), parity_eq_zero_of_not_mem_convex
   │  ├─ exists_not_countable_of_cover, exists_pos_sep,
   │  │     exists_between_three                              (§7)
   │  └─ plPath, continuous_plPath, dist_plPath_le            (§5.1)
   ├─ ot82_cor35_of_thm32 : OTThm32 → OTCor35                 (batch 191, OT82A; see its map)
   └─ theoremC_of_cor35 : OTCor35 → TheoremC                  (batch 191, Thm36; see its map)
```

The batch-191 map (report 191 §5) below `ot82_cor35_of_thm32` and `theoremC_of_cor35` is unchanged
and fully proved (`hagopian76_theorem1`, Effros, Cook, the Brouwer reduction, the re-embedding
lemmas, `exists_uncountable_crossing`).

## 6. The classification: verified statements about homogeneous plane continua

Hoehn–Oversteegen (2016, p. 180) obtain the classification from Theorems A, B, C and their
Theorem 1 (commission 191 §1). A, B and C are now proved in the main build, with **no named
hypotheses** and standard axioms only:

* **Theorem A** (Jones 1955, the decomposable case): a decomposable homogeneous plane continuum has a
  continuous decomposition into homogeneous, indecomposable, non-separating continua with quotient a
  simple closed curve (`HPC.Jones.jones55_theorem2'`, with `jones55_two_domains'`,
  `jones55_elements_indecomposable'`, `jones55_three_domains'`; batch 154, Jones 1949 discharged).
* **Theorem B** (Hagopian 1976, Theorem 1): every indecomposable homogeneous plane continuum is
  hereditarily indecomposable (`HPC.Hagopian.hagopian76_theorem1 : Hagopian76Thm1`, batch 190).
* **Theorem C** (Hoehn–Oversteegen p. 180; O–T 1982 Theorem 3.6): every homogeneous indecomposable
  plane continuum has span zero (`HPC.Span.theoremC : TheoremC`, this batch), with O–T Corollary
  3.5 (`ot82_cor35_of_thm32 ot82_theorem32 : OTCor35`) and Theorem 3.6, second sentence
  (`ot82_theorem36_of_cor35`), now unconditional.

Still to come for the classification (not commissioned here): Hoehn–Oversteegen's Theorem 1
(hereditarily indecomposable with span zero ⇔ pseudo-arc) and the circle-of-pseudo-arcs step.

## 7. Delivery

* `axioms.txt`: **2658 lines** (`wc -l axioms.txt`), regenerated with
  `lake env lean Axioms.lean > axioms.txt`; no `sorryAx`.
* `doc/batches/audits/axioms-batch192.txt`: the 63 new lines.
* `doc/notes/ot82.md`: a paragraph "The route of batch 192" appended.
* `LEDGER.md`: checks OT.8–OT.13 in the O–T section; `OPEN.md`: batch-192 entry (nothing open);
  `README.md`: Theorem C II.
* `doc/batches/batch192-files.tar.gz` and `doc/batches/batch192-MANIFEST.txt`: every file added or
  modified in this run (from `git diff --name-status` against the run's initial commit `680e677`),
  including this report.
* The uploads are in `doc/batches/COMMISSION-batch192.md` and `doc/batches/skeletons/OT82B.lean`;
  nothing is left at the root.
