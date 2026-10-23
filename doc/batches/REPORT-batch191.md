Commission read: `doc/batches/COMMISSION-batch191.md` ("Commission: batch 191 — Theorem C I: span; Cook 1967; O–T 1982, Theorem 3.6 and Corollary 3.5").

# Report, batch 191

## 0. Summary, omissions

**Every formal item of commission §2–§6 is proved, ending with
`theoremC_of_thm32 : OTThm32 → TheoremC`.** §7 (`crossing_traces_separated`) is **open** and
commented out (commission §8 allows leaving it for batch 192). The skeleton is split over six files
under `HPC/Span/`:

* `HPC/Span/Defs.lean` (§2: definitions, §2.1–§2.4),
* `HPC/Span/Cook.lean` (§3: Cook 1967 Theorem 4; §4: Brouwer reduction, Davis 1.1 for hereditarily
  indecomposable continua),
* `HPC/Span/Thm36.lean` (§5: `OTCor35`, `TheoremC`, Theorem 3.6 from Corollary 3.5),
* `HPC/Span/Reembed.lean` (§6.1: (E1)–(E3)),
* `HPC/Span/Crossing.lean` (§6.2: crossing continua),
* `HPC/Span/OT82A.lean` (§6.3 `OTThm32`, §6.4, `theoremC_of_thm32`, §7 commented out; index of the
  split).

`HPC.lean` ends with `import HPC.Span.OT82A`; `lake build HPC` succeeds (8732 jobs). No declaration
contains `sorry`; the only occurrence of the word is inside the commented-out §7 statement. Nothing
is refuted.

`axioms.txt` has **2595 lines** (2550 + 45 added, none removed). `sorryAx` occurs in none of them.
The 45 new theorems (group "Theorem C I (batch 191)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch191.txt`) use only standard axioms: 41 use exactly
`[propext, Classical.choice, Quot.sound]`, three (`fst_image_swap`, `snd_image_swap`,
`isHomogeneous_of_homeomorph`) use `[propext, Quot.sound]`, and `offDiag_swap` uses none.

**Omissions.**
* **§7 `crossing_traces_separated`: open, not attempted to completion.** Obstruction: the two
  Jordan-curve lemmas of §7 (*crosscut* and *pocket*, for an arc in the strip `[a, b] × ℝ` meeting
  the side lines only at its ends) are not in the repository in strip form. The nearest results
  (`rect_domain_crosscut`, `rect_domain_crosscut_arc`, the `VFrame` order of
  the existing Hagopian 1976 files) are stated for a domain with a prescribed frontier formula or for
  abstract pieces satisfying separation axioms, and adapting them was not done in this batch. A
  unicoherence route (`separatesPlane_union_of_inter_disconnected` applied to `K` and a polygonal
  loop through `p`, `q` outside the strip) shows that `K ∪ loop` separates the plane, but not which
  component contains `w` and which contains `L_b`; this is where it stopped. The statement is kept,
  as in the skeleton, in a comment at the end of `HPC/Span/OT82A.lean`, and recorded in `OPEN.md`.
  It is not used in this batch.
* Nothing else is omitted.

Status lines:
* STATUS: §2 definitions (unchanged); `otSemiSpanPos_iff`, `otSpanPos_iff`,
  `SurjSpanPos.surjSemiSpanPos`, `SurjSpanPos.image`, `SurjSemiSpanPos.image`,
  `semiSpanZero_iff_hoSpanZero`, `hoSpanZero_iff_maps` proved
* STATUS: §3 `cook67_theorem4` proved
* STATUS: §4 `isContinuum_sInter_chain`, `brouwer_reduction`,
  `exists_surjSpanPos_of_surjSemiSpanPos`, `semiSpanZero_of_spanZero` proved
* STATUS: §5 `ot82_theorem36_of_cor35`, `theoremC_of_cor35` proved
* STATUS: §6.1 `exists_homeomorph_unique_leftmost`, `exists_homeomorph_push`,
  `isConnected_rightHalf_diff` proved
* STATUS: §6.2 `exists_crossing_subcontinuum`, `exists_uncountable_crossing` proved
* STATUS: §6.3 `OTThm32` (named claim) open (batch 192: O–T §2 and Theorem 3.1's argument)
* STATUS: §6.4 `ot82_cor35_of_thm32`, `theoremC_of_thm32` proved
* STATUS: §7 `crossing_traces_separated` open (strip forms of the crosscut and pocket lemmas
  missing)

**Shape changes** (each is also recorded at the statement):
* `semiSpanZero_iff_hoSpanZero`: the skeleton's `[CompactSpace X]` is dropped (not needed; a
  generalization).
* `hoSpanZero_iff_maps`: the skeleton's `[CompactSpace X]` is dropped (not needed; a
  generalization).
* `isConnected_rightHalf_diff`: the skeleton's hypothesis `hA0 : ∀ z ∈ A, 0 ≤ z.1` is dropped (not
  used; a generalization).
* Every other skeleton statement is unchanged (checked mechanically against
  `doc/batches/skeletons/OT82A.lean`). The skeleton is split over six files; definitions are
  unchanged.

**Departures in the proofs** (not shape changes):
* §3: Cook's theorem is proved with one closed neighbourhood instead of the sequence `Cₙ`: if
  `q ∈ Q ∖ f(C)`, a closed neighbourhood `N = cthickening r C` misses `f⁻¹(q)`; the component of
  `x` in `N` is strictly larger than `C` by boundary bumping (`exists_continuum_bump_compact`), or
  `C = X`. So neither the existence of the `Cₙ` nor `⋂ f(Cₙ) = f(C)` is needed.
* §5.4: instead of the sequence `Kᵢ`, one `δ`-dense proper subcontinuum is taken directly
  (`exists_dense_proper_subcontinuum`): the proper subcontinua through a point are directed by
  union (indecomposability, `union_proper_of_indec`) and their union, the composant, is dense
  (`composant_dense`); compactness picks one.
* §5.1/§5.8: the constant `3ε` is replaced by `α`, the minimum of `d` on `Z`
  (`exists_pos_le_dist`); Effros is applied for `α` itself, which already keeps `W` off the diagonal
  (`d(h f(c), g(c)) ≥ α − d(f(c), h f(c)) > 0`).
* Universe: `isContinuum_sInter_chain` has a universe-polymorphic second conjunct; two uses (in
  `brouwer_reduction` and `cor35_core`) fix the universe (`isContinuum_sInter_chain.{_, 0}`).

## 1. The items, in order

### §2. Span (`Defs.lean`)

* Definitions `OffDiag`, `SurjSpanPos`, `SurjSemiSpanPos`, `SpanZero`, `SemiSpanZero`,
  `HOSpanZero`, `OTSemiSpanPos`, `OTSpanPos`: the skeleton's.
* **2.1** `otSemiSpanPos_iff`, `otSpanPos_iff` (compact `X`): as in the commission (closures of `A`
  and `C`; `π₁(cl C) = cl π₁(C)` by compactness; conversely `α` = minimum of `d` on `Z`,
  `exists_pos_le_dist`).
* **2.2** `SurjSpanPos.surjSemiSpanPos`, `SurjSpanPos.image`, `SurjSemiSpanPos.image`
  (`Z ↦ (f × f)(Z)`, continuous `f` injective on `A`). Helpers `isContinuum_swap`, `offDiag_swap`,
  `fst_image_swap`, `snd_image_swap`.
* **2.3** `semiSpanZero_iff_hoSpanZero` (shape above): the swap argument.
* **2.4** `hoSpanZero_iff_maps` (shape above): `C := Z` with the two projections; conversely
  `Z = range (f, g)`.

### §3. Cook 1967, Theorem 4 (`Cook.lean`)

* `cook67_theorem4`: for `f : X → E` continuous from a compact metric continuum with
  `range f = S` hereditarily indecomposable, every subcontinuum `Q ⊆ S` and `x` with `f x ∈ Q`,
  `f '' connectedComponentIn (f ⁻¹' Q) x = Q`. Proof above (§0). Helpers `nested_of_hi` (two meeting
  subcontinua of a hereditarily indecomposable set are nested), `hi_mono`.

### §4. Brouwer reduction; Davis 1.1 (`Cook.lean`)

* **4.1** `isContinuum_sInter_chain`: the intersection of a nonempty chain of continua is a
  continuum, and `φ '' ⋂₀ c = ⋂_{W ∈ c} φ '' W` for continuous `φ` into a metric space. Helpers
  `directed_of_isChain_supset`, `isPreconnected_iInter_directed_compact` (a directed intersection of
  compact connected sets in a Hausdorff space is preconnected), `sInter_chain_inter_nonempty`.
* `brouwer_reduction`: Zorn on the subcontinua of `Z` with property `P`, ordered by `⊇`.
* **4.2** `exists_surjSpanPos_of_surjSemiSpanPos`: steps 1–5 of the commission (minimal `Z₀` with
  `π₂(Z₀) ⊆ π₁(Z₀)`; Cook on `π₁ : Z₀ → B` to cut down to `π₁⁻¹(Q)` if `π₂(Z₀) ≠ π₁(Z₀)`). Helper
  `isClosed_connectedComponentIn_of_isClosed'`.
* `semiSpanZero_of_spanZero`.

### §5. Theorem 3.6 from Corollary 3.5 (`Thm36.lean`)

* `OTCor35`, `TheoremC`: the skeleton's named claims.
* **5.2** `exists_reduced_witness`: the reduction (Brouwer reduction for "`g(W) = univ`", then
  either keep `Z₀` or swap it).
* **5.4** `exists_dense_proper_subcontinuum` (departure above); `union_proper_of_indec`.
* **5.1–5.8** `not_surjSemiSpanPos_univ`: for an abstract compact metric continuum that is
  homogeneous, indecomposable and hereditarily indecomposable, if no proper subcontinuum has
  positive surjective semi-span then neither has the whole space. Steps as in the commission: Effros
  (`HPC.Effros.effros_homogeneous`), Cook for `f = π₁` on `Z`, nesting of `h(K)` and `g(Cᵢ)`, the
  continuum `W = {(h f c, g c)}` or its swap.
* **5.9** `ot82_theorem36_of_cor35` (Theorem 3.6, second sentence: `SemiSpanZero M` for every
  indecomposable homogeneous plane continuum, from `OTCor35`; hereditary indecomposability from
  `hagopian76_theorem1`), `theoremC_of_cor35`.

### §6.1. Re-embedding (`Reembed.lean`)

* **(E1)** `exists_homeomorph_unique_leftmost`: `Φ(u, v) = (u − u₀ + (v − v₀)², v)`.
* **(E2)** `exists_homeomorph_ball_step` (the ball step: `T(w) = w + β(w)(z − c)`, a homeomorphism
  through `ApproximatesLinearOn.toHomeomorph`, Lipschitz constant `< 1/2`) and
  `exists_homeomorph_push` (chaining: the reachable set is open and closed in the connected `U`).
* **(E3)** `isConnected_rightHalf_diff` (shape above), by the commission's argument with
  `janiszewski_compact` and `isConnected_compl_rect`; helper
  `not_separatesPts_of_isConnected_compl`.

### §6.2. Crossing continua (`Crossing.lean`)

* `exists_crossing_subcontinuum`: the cut-wire lemma, through the repository's
  `exists_split_of_no_continuum` (components = quasi-components in compact Hausdorff spaces) and the
  closed cover `(P ∩ {x ≤ a}) ∪ F₁`, `(P ∩ {x ≥ b}) ∪ F₂`.
* `composant_eq_of_mem`, `exists_uncountable_crossing`: one crossing continuum inside each
  composant (`Jones.composant`; `composant_dense`, `composant_eq_or_disjoint`,
  `uncountable_composants`).

### §6.3–§6.4. Corollary 3.5 from Theorem 3.2 (`OT82A.lean`)

* `OTThm32`: the skeleton's named claim.
* `cor35_core` (steps 6–9): a plane continuum `N ⊆ {x ≥ 0}`, homogeneous and indecomposable, with a
  unique point `x₀` on `x = 0`, a continuum `A ∋ x₀` with `SurjSpanPos A` and a point of `N` to the
  right of `A`, contradicts `OTThm32`. As in the commission: constants `s, m, η, r`, Effros for `η`,
  `ε` with `N ∩ {x ≤ ε} ⊆ B(x₀, δ)`, the family `𝒦` for `[ε, r] × ℝ`, `h_K` with
  `h_K(A) ⊆ K`, `B = ⋂ h_K⁻¹(K)` with `y`, rescaling by `ρ`.
* `ot82_cor35_of_thm32` (steps 1–5): Davis (§4.2) gives `A₁ ⊆ A₀` with positive span; (E1)
  re-embeds `M`; homogeneity moves `Φ(A₁)` to `A ∋ x₀'`; `no_proper_subcontinuum_separates` and
  (E3) make `{x > 0} ∖ A` connected; (E2) pushes a point of `M' ∖ A` to the right of `A`.
  Helpers: `isContinuum_preimage_val_iff`, `SurjSpanPos.of_image`, `isHomogeneous_of_homeomorph`,
  `not_isDecomposableSpace_of_homeomorph`, `fst_lt_of_dist_lt`.
* `theoremC_of_thm32`.

### §7. `crossing_traces_separated`

Open; see §0. Statement as in the skeleton, commented out at the end of `OT82A.lean`.

## 2. Non-vacuity

* **`OTCor35`** (hypothesis of `ot82_theorem36_of_cor35`, `theoremC_of_cor35`).
  1. Not refuted by a short argument: it says that proper subcontinua of an indecomposable
     homogeneous plane continuum have zero surjective semi-span. Its instances are the pseudo-arc
     (all its nondegenerate subcontinua are pseudo-arcs, which are chainable and so have span zero;
     a hand remark, not formalized). Nothing in the set-up contradicts it: it is O–T's Corollary
     3.5, and `ot82_cor35_of_thm32` derives it from `OTThm32`.
  2. Not equivalent to the conclusion: `TheoremC` (and `SemiSpanZero M`) is about the whole
     continuum `M`, `OTCor35` only about proper subcontinua. The step from proper subcontinua to `M`
     is the content of `not_surjSemiSpanPos_univ` (Effros, Cook, the reduction); it is not a proof by
     contradiction from `OTCor35`'s own negation.
* **`OTThm32`** (hypothesis of `ot82_cor35_of_thm32`, `theoremC_of_thm32`, `cor35_core`).
  1. **An instance of its hypotheses:** `Y = [0, 1]` (an arc), `X = [0, ½]`, `x = 0`, `y = 1`,
     `ι = ℝ`, `K t = [0, 1] × {t}` (horizontal segments: continua, pairwise disjoint, crossing the
     strip), `h t z = (z, t)`. Then `h t` is continuous, `range (h t) = K t`, `(h t x).1 = 0` and
     `(h t z).1 ≤ ½ < 1 = (h t y).1` for `z ∈ X`. The conclusion holds here (`h t '' X` is an arc,
     which has span zero, so the set is empty). Nothing in the set-up refutes the claim: it is
     weaker than the printed Theorem 3.2.
  2. Not equivalent to the conclusion it is used for: `OTThm32` speaks about families of disjoint
     planar images in a strip; `OTCor35` and `TheoremC` speak about homogeneous continua. The
     derivation (`ot82_cor35_of_thm32`) is O–T's proof by contradiction of Corollary 3.5, which
     produces from a counterexample to Corollary 3.5 an uncountable family violating `OTThm32`; the
     printed argument is a proof by contradiction, as the standing rule allows.
* **Hereditary indecomposability** (hypothesis of `cook67_theorem4`,
  `exists_surjSpanPos_of_surjSemiSpanPos`, `semiSpanZero_of_spanZero`,
  `not_surjSemiSpanPos_univ`): satisfied by the pseudo-arc and by any one-point set; not
  equivalent to the conclusions (confluence, span statements).
* **`not_surjSemiSpanPos_univ`** has `IsHomogeneous`, indecomposability, hereditary
  indecomposability and `h35`; all together are satisfied by a one-point space (where the
  conclusion is also immediate), and no short argument refutes them for nondegenerate spaces (the
  pseudo-arc is the expected example; hand remark).
* **`cor35_core`** has `h32 : OTThm32` and a configuration that it refutes; that is its purpose
  (step 9 of the commission's proof by contradiction).
* The remaining items have only topological hypotheses (compactness, connectedness, continuity),
  which are satisfiable (e.g. by an arc, or a segment in the plane).

## 3. Ledger entries (`LEDGER.md`)

* **§0.1, Hagopian 1976 Theorem 1:** new subsection "Hagopian 1976: Theorem 1 classified (batch
  191)", placed after the last Hagopian 1976 subsection: **proof defective, statement true**; the
  identified failure is the case split at `i = 2` (`blockLayersMeetSides_false`, batch 182); the
  statement is verified by another route (`hagopian76_theorem1`, batch 190); precedents Moore 1916
  Theorem 28 and Jones 1975's Theorem. The sixteenth defective proof of the ledger.
* **§0.2, the count:** J75.1 now reads "the fourteenth defective proof" and J75.4 "the fifteenth"
  (each with the note "batch 191 correction"); the closing line of Jones 1975 I reads "rises from
  thirteen to fifteen", followed by a note: the earlier count had included Moore 1916 Theorems
  33–34 twice although they share one printed proof (Kline's); the figure "fourteen" in the earlier
  subsections reads thirteen; the count before Hagopian 1976 Theorem 1 is fifteen, with it sixteen.
  The closing line of Jones 1975 II ("stays at sixteen") now reads "stays at fifteen (corrected in
  batch 191 from "sixteen")". The older subsections' "fourteen" lines are left as written (only the
  Jones 1975 I and II lines that stated "fifteenth", "sixteenth" or "sixteen" were edited), and the
  note says how to read them.
* **New section "Oversteegen–Tymchatyn 1982 and Cook 1967 (batch 191)"**, checks OT.1–OT.7 with
  the printed sentences quoted from the page images:
  * OT.1 (Theorem 3.6, "Since X is atriodic tree-like"): **confirmed**, not used in the
    indecomposable case.
  * OT.2 (Theorem 3.6, "Z is a proper subcontinuum", "Hence there exists an index i …"):
    **confirmed**, both unargued and true; the first rests on the reduction.
  * OT.3 (Corollary 3.5, items 1–5): **all confirmed**; item 4 is impossible as printed, the second
    reading is the one proved.
  * OT.4 (Theorem 3.2): suppositions quoted; separating triple and single-point supposition
    unargued; the two `δ` steps not available together (the commission's fix adopted for batch
    192); `OTThm32` adds the crossing continua. Hand arguments, not formalized.
  * OT.5 (Theorem 1.1): proved only for hereditarily indecomposable continua, through Cook.
  * OT.6 (Cook, Theorem 4): **confirmed**: the sequence `Cₙ` (absent when `C = X`) and
    `⋂ f(Cₙ) = f(C)` are unstated; the theorem is proved by a proof that needs neither.
  * OT.7 (misprints): confirmed; two more recorded (p. 136 "R²" for "I²" in the proof of Theorem
    2.7; p. 138 "h_λ(Z)" for "h_λ(z)" in (5) of the proof of Theorem 3.3).
  * No statement is refuted; no defective proof is added; the count stays at sixteen.

## 4. Axioms

Every one of the 45 new theorems uses a subset of `[propext, Classical.choice, Quot.sound]` (41
exactly these three; `fst_image_swap`, `snd_image_swap`, `isHomogeneous_of_homeomorph`:
`[propext, Quot.sound]`; `offDiag_swap`: no axioms); the list with one line per theorem is
`doc/batches/audits/axioms-batch191.txt`. In particular:

| theorem | axioms |
|---|---|
| `HPC.Span.theoremC_of_thm32` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.ot82_cor35_of_thm32` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.cor35_core` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.theoremC_of_cor35` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.ot82_theorem36_of_cor35` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.not_surjSemiSpanPos_univ` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.cook67_theorem4` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.exists_surjSpanPos_of_surjSemiSpanPos` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.semiSpanZero_of_spanZero` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.exists_uncountable_crossing` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.exists_homeomorph_push` | `propext, Classical.choice, Quot.sound` |
| `HPC.Span.isConnected_rightHalf_diff` | `propext, Classical.choice, Quot.sound` |

## 5. Dependency map of `TheoremC`

The only open input is **`OTThm32`** (marked OPEN). Everything else is proved.

```
theoremC_of_thm32 : OTThm32 → TheoremC                        (batch 191, OT82A)
├─ OTThm32                                                     OPEN (named claim; batch 192)
├─ ot82_cor35_of_thm32 : OTThm32 → OTCor35                     (§6.4, OT82A)
│  ├─ hagopian76_theorem1                                      (batch 190, Jones75B)
│  ├─ exists_surjSpanPos_of_surjSemiSpanPos  (Davis, §4.2)     (Cook)
│  │  ├─ brouwer_reduction, isContinuum_sInter_chain           (§4.1, Cook)
│  │  └─ cook67_theorem4                                       (§3, Cook)
│  ├─ exists_homeomorph_unique_leftmost  (E1)                  (§6.1, Reembed)
│  ├─ isConnected_rightHalf_diff  (E3) ← janiszewski_compact,
│  │     isConnected_compl_rect                                (§6.1, Reembed)
│  ├─ exists_homeomorph_push  (E2) ← exists_homeomorph_ball_step (§6.1, Reembed)
│  ├─ no_proper_subcontinuum_separates                         (existing, Hagopian76B)
│  ├─ SurjSpanPos.image, SurjSpanPos.of_image                  (§2.2, Defs; OT82A)
│  └─ cor35_core                                               (§6.4, OT82A)
│     ├─ OTThm32                                               OPEN
│     ├─ HPC.Effros.effros_homogeneous                         (batch 134–, Effros)
│     ├─ exists_uncountable_crossing ← exists_crossing_subcontinuum
│     │     ← exists_split_of_no_continuum; composant_dense,
│     │     composant_eq_or_disjoint, uncountable_composants   (§6.2, Crossing; existing)
│     ├─ nested_of_hi, hagopian76_theorem1                     (Cook; batch 190)
│     └─ isContinuum_sInter_chain                              (§4.1, Cook)
└─ theoremC_of_cor35 : OTCor35 → TheoremC                      (§5.9, Thm36)
   ├─ semiSpanZero_iff_hoSpanZero                              (§2.3, Defs)
   └─ ot82_theorem36_of_cor35                                  (§5.9, Thm36)
      ├─ hagopian76_theorem1                                   (batch 190)
      └─ not_surjSemiSpanPos_univ                              (§5.1–§5.8, Thm36)
         ├─ exists_reduced_witness ← brouwer_reduction         (§5.2)
         ├─ HPC.Effros.effros_homogeneous                      (Effros)
         ├─ exists_dense_proper_subcontinuum ← composant_dense (§5.4)
         ├─ cook67_theorem4, nested_of_hi                      (§3)
         └─ exists_pos_le_dist                                 (§2)
```

`crossing_traces_separated` (§7, open) is not on this map: it is an intended input of the batch-192
proof of `OTThm32`.

## 6. What batch 192 needs from O–T §2 to prove `OTThm32`

(A longer account, with the statements of Lemmas 2.1–2.4, Remark 2.5 and Theorems 2.6–2.7, is in
`doc/notes/ot82.md`.)

1. **Theorem 2.7** (p. 135): in an ε-strip bounded by light PL arcs `f, g` with
   `(π₁f)⁻¹(a) = {0} = (π₁g)⁻¹(a)`, `d(f(x), g(x)) < ε` and `f(x) ≠ g(y)` off the ends, a
   continuum `X ⊆ U ∪ B₀ ∪ B₁` with `a ∈ π₁(X)` has `σ*(X) < ε`. Its proof needs Lemma 2.3 in its
   one-sided form: the sign function `φ(x, y) = ±d(B_x, h(y))` is continuous (Lemma 2.2, which
   rests on the parity θ of Lemma 2.1 for the curve `S_t = B₀ ∪ f[0,t] ∪ g[0,t] ∪ B_t`; the
   repository's `parity`, `parity_locallyConstant`, `parity_eq_of_isPreconnected`, `parity_far` are Lemma 2.1 in ray-crossing form) and a continuum in the zero set of a
   function on `I²` changing sign between two opposite sides (unstated in O–T).
2. **From continua to arcs** (Lemma 2.4, Remark 2.5): Theorem 2.7 is proved for maps `h, k` of `I`.
   `SurjSpanPos` provides a continuum `Z` and two maps of `Z` onto `A`. Either Lemma 2.3 is
   generalized to maps of a continuum (the zero-set argument on `C × I`), or `A` is approximated by
   locally connected continua in a thin neighbourhood (Remark 2.5, unargued in O–T).
3. **The strip around the middle image** (proof of Theorem 3.1): three indices with
   `h_λ₂(X)` between `h_λ₁(X)` and `h_λ₃(X)`; in `OTThm32` this is to come from the order of the
   disjoint crossing continua `K i` along the left side (§7, `crossing_traces_separated`, still
   open), and PL arcs `h̃_λ₁|A₁`, `h̃_λ₃|A₁` close to the outer images and disjoint from the middle
   one bounding an ε-strip containing `h_λ₂(X)` (O–T: "Without loss of generality …", unargued; the
   main construction).
4. **Counting:** one `n` with uncountably many indices having span witness `≥ 1/n` and gap
   `π₁h(y) − max π₁h(X) > 1/n`; then (separability of `C(Y, ℝ²)`) uncountably many maps within
   `1/(8n)` of each other; three of them, ordered by §7.

**Doubts about the claim.** None about `OTThm32` itself: it is O–T's Theorem 3.2 with the extra
hypothesis that the images lie in pairwise disjoint continua crossing the strip, which is what
Corollary 3.5 supplies and what makes the separating triple available. Whether the printed Theorem
3.2 (without crossing continua) holds is not decided here (ledger OT.4).

## 7. Delivery

* `axioms.txt`: **2595 lines** (`wc -l axioms.txt`), regenerated with
  `lake env lean Axioms.lean > axioms.txt`; no `sorryAx`.
* `doc/batches/audits/axioms-batch191.txt`: the 45 new lines.
* `doc/notes/ot82.md`: transcriptions of pp. 129–130 and 136–140 from the page images, Cook p. 243,
  and the account of O–T §2.
* `doc/batches/batch191-files.tar.gz` and `doc/batches/batch191-MANIFEST.txt`: every file added,
  modified or moved in this run (from `git diff --name-status` against the run's initial commit
  `8f23aa3`), including this report.
* The uploads are in `doc/batches/COMMISSION-batch191.md`, `doc/batches/skeletons/OT82A.lean`,
  `doc/sources/oversteegen-tymchatyn1982.pdf` and `doc/sources/cook1967.pdf`; nothing is left at the
  root.
