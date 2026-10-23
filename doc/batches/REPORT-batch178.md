Commission read: `doc/batches/COMMISSION-batch178.md` ("Commission: batch 178 — Part E, Hagopian 1976 XXIII: Theorem 1 — the order of strands without Schoenflies; separation along the vertical; the end layer of `F`; unicoherence; the assembly").

# Report, batch 178

## 0. Summary

* **§1, S4 without Schoenflies: proved.** S4a–S4e hold in an abstract vertical frame (`VFrame`),
  and crossing pieces of `π⁻¹[D]` are pieces of the concrete frame (`isPiece_of_isCrossingPiece`).
  Only `crossing_sides` (through its core `crossing_separates_aux`) and `rect_domain_crosscut`
  (through `K0_crosscut_aux`) are used, as the commission said.
* **§2, SSL: proved**, with its converse and the general `SepByCrossing` corollary.
* **§3a, the end layer of `F`: proved** (`T12Data.end_layer_not_subset`).
* **§3b: open**, named `InnerComponentsCross`. **§3c: open.**
* **§4.A: proved** (`strand_misses_F_of_composant`, via the companion `exists_T12Data_comp`).
  **§4.B: open.** **§4.C: proved conditionally** (`sep_by_crossing`, from `InnerComponentsCross`
  and 4.B). `x₂ₙ = 1` and Property 4 for the top block follow from it through the batch-176 chain.
* **§5, unicoherence: proved** (`separatesPlane_union_of_inter_disconnected`, by the commission's
  route through `borsuk_exists_log`; and the domain form `sepIn_iff_separatesPts_union`).
* **§6, the blocks: proved, with one added hypothesis** (`exists_blocks`): the members of `I` are
  nondegenerate. This is a new finding (§1.6).
* **§7: open.** A skeleton is given in §5.
* **§8: open.** `doc/notes/hagopian76-cases.md` reconstructs Cases 1–2 in strand language.
* **Nothing of Hagopian's is refuted.** The count of defective proofs stays at fourteen.

STATUS lines, in order:
* `STATUS: §1 S4a proved (crossing_piece_meets_sigma; isPiece_of_isCrossingPiece)`
* `STATUS: §1 S4b–S4e proved (crossing_piece_sides, crossing_piece_below_iff, crossing_piece_below_trans, crossing_piece_no_pocket)`
* `STATUS: §2 SSL proved (strand_separation, strand_separation_converse, sepByCrossing_of_inner_crossing)`
* `STATUS: §5 proved (separatesPlane_union_of_inter_disconnected, sepIn_iff_separatesPts_union)`
* `STATUS: §3a proved (T12Data.end_layer_not_subset)`
* `STATUS: §3b open (InnerComponentsCross; configuration 3.3 not excluded, §1.3b)`
* `STATUS: §3c open (needs 3b and lemma3_half both ways)`
* `STATUS: §4.A proved (strand_misses_F_of_composant; exists_T12Data_comp)`
* `STATUS: §4.B open (I₂ ∩ π[M] at the ends of I₂; closedness in O)`
* `STATUS: §4.C conditional form proved (sep_by_crossing)`
* `STATUS: §6 proved with nondegeneracy hypothesis (exists_blocks)`
* `STATUS: §7 open (Thm1Setup not written; skeleton §5)`
* `STATUS: §8 open (E0–E2.6; doc/notes/hagopian76-cases.md)`

The build:
* `lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76W` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 2000 lines (1929 + 71), with `sorryAx` in no line; see §3.
* All 71 new theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* No declaration uses `sorry`. The word occurs only in the comment block at the end of
  `Hagopian76W.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76W.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Unicoh.lean`: §5;
* `H76Order.lean`: the abstract frame, S4b–S4e, SSL;
* `H76OrderConcrete.lean`: the concrete frame, crossing pieces, S4a;
* `H76EndLayer.lean`: 3a;
* `H76SepCross.lean`: 4.C (conditional);
* `H76Blocks.lean`: §6;
* `H76Comp.lean`: 4.A.

Earlier files edited, as allowed:
* `Hagopian76V.lean`: the commented-out `strand_order` (S4) is replaced by a one-line pointer. The
  other batch-177 open shapes (`exists_blocks`, `sep_by_crossing`, `hagopian76_property4_step`,
  `hagopian76_theorem1_final`) are not proved as stated there, so they stay.
* `H76Prop4.lean` is unchanged: no field was added to `T12Data` (§4.A uses a companion theorem).

The uploads are in `doc/batches/COMMISSION-batch178.md` and
`doc/batches/skeletons/Hagopian76W.lean`. Nothing is left at the root.

## 1. The items in order

### 1.1 §1: the order of crossing pieces

**Shape.** The order is developed in an abstract **vertical frame** `VFrame` (`H76Order.lean`):
* an open connected `O`;
* a relation `lev P v`, "`P` is the point of `σ` at height `v`". Heights lie in `(0, w)`; there is
  exactly one point at each height; and the points over any connected set of heights form a
  connected set.

A **piece** (`VFrame.IsPiece`) is connected, in `O`, closed in `O`, has a compact nonempty set of
`σ`-heights `hts X`, and has disjoint sides. The sides `A(X) = V.below X` and `B(X) = V.above X`
are commission 178's sets. "Below `m(X)`" is read as "below every height of `Cl X`", and similarly
above. This avoids choosing the parameters `u₁`, `u₂` of `belowSet`/`aboveSet`. `X′ ≺ X` is
`X′ ⊆ V.below X`.

The concrete frame is `lowFrame` (`H76OrderConcrete.lean`):
* `O = π⁻¹[F[D′]]`;
* `lev P v ↔ v ∈ (0, w₂) ∧ π P = F(t₀, v)`.

Its hypotheses (connectedness of `O` and of the parts of `σ` over intervals) follow from
`O ∩ E = ∅` and the connectedness of `D′` (`lowFrame_hyps`). This uses `isPreconnected_preimage_off`
and `pi_preimage_isPreconnected`. Injectivity of `π` over `D` gives one point per height.

`IsCrossingPiece` is commission 178's crossing piece. `isPiece_of_isCrossingPiece` proves three
things:
* **the heights are compact:** the closure misses the two ends of the closed vertical segment (the
  bottom edge and `I₂`);
* **S4a:** if `X` missed `σ`, then `K0_crosscut_aux` (the transported `rect_domain_crosscut`) would
  contradict the closure meeting both open sides; `crossing_piece_meets_sigma` states this directly;
* **the sides are disjoint:** `crossing_separates_aux` (the core of `crossing_sides`), applied with
  `u₁`, `u₂` the heights of the two anchor points.

**S4b–S4e (proved, in the frame):**
* S4b `crossing_piece_sides` (`VFrame.piece_sides`): the commission's argument.
* S4c `crossing_piece_below_iff` (`VFrame.below_iff_above`). The clopen argument is
  `VFrame.not_below_below` and `VFrame.not_above_above`, with `VFrame.clopen_contra`. The step
  "`B(X)` contains `σ`-points above both `M(X)` and `M(X′)`, hence `B(X) ⊆ B(X′)`" uses the
  connected segment of `σ` above `M(X)` (`VFrame.above_subset_above`).
* S4d `crossing_piece_below_trans` (`VFrame.below_trans`). Here `X″` need only be a set.
* S4e `crossing_piece_no_pocket`.

`t₀` is kept general throughout (any abscissa with the hypotheses of `crossing_sides`).

### 1.2 §2: separation along the vertical

* **SSL** `strand_separation` (`VFrame.strand_separation`). Shape changes:
  * `Z` is an arbitrary set; compactness is not used.
  * The closest points of step 2 are chosen as follows: `P′` is the point of `X` at `m(X)`, and `P`
    is the point of `Y` at the greatest height of `Y` below `m(X)`. This needs `m(Y) < m(X)` when
    `Y ≺ X`, which is proved inside `VFrame.exists_sep_point`.
  * The conclusion lists `X ≠ Y`, disjointness, the order, a point `z ∈ Z ∩ σ` in `A(X) ∩ B(Y)` (or
    the symmetric case), and, when `W_z` is a piece, separation by `Cl W_z`. The order facts
    `Y ≺ W_z ≺ X` are in `VFrame.between_of_mem`.
* **Converse** `strand_separation_converse` (`VFrame.sepIn_of_between`).
* **Corollary** `sepByCrossing_of_inner_crossing`. Its conclusion also records that `z` is on `σ`.

### 1.3 §3: the end layer of `F`, saturation

**3a: proved** (`T12Data.end_layer_not_subset`, from `T12Data.end_layer_not_subset_aux`). The
route of §3a, with these details:
* the case `G = E` (the layer lies in `E`, which misses `O`);
* `s₁` is obtained from the compactness of `{g ∈ G : g ∉ O}`, not from a decreasing intersection;
* `Y` need not be connected: Janiszewski needs only `(A ∪ Y) ∩ B = d⁻¹(s₁)`, a continuum.

**3b: open**, named `InnerComponentsCross G π F D′ a b r₂ s₂ I₂ lo hi`: every component of
`G ∩ π⁻¹[D]` through a point over an abscissa in `(lo, hi)` is a crossing piece.

Status of the route:
* **Step 1 and step 2:** sound and routine. Boundary bumping, S0 and no-hair are all available. Not
  formalized.
* **Steps 3.1–3.2 (the tip, the triod):** sound when `τ₁ < k(e)`. Not formalized.
* **Step 3.3 (`τ₁ ≥ k(e)`): the configuration survives the three named tools.** Here
  `Λ₁ = d⁻¹(1) ∩ h[E]` is a continuum (hereditary unicoherence) with parameter interval `[τ′, τ₁]`,
  where `τ′ ≤ τ ≤ k(e) ≤ τ₁`.
  * **The triod:** its three arms can degenerate. `K⁻ − Z` can be empty when `K⁻ ⊆ Λ₁ ∪ h[k⁻¹(τ)]`
    (then `y ∈ d⁻¹(1)`). The arm `d⁻¹(1) − h[E]` can be empty when `d⁻¹(1) ⊆ h[E]`.
  * **3a:** it gives only that `d⁻¹(1) ⊄ O`. That is compatible with `d⁻¹(1) ⊆ h[E]` reaching the
    frontier of `D` beyond `τ₁`.
  * **The void interior of `d⁻¹(1)` in `F`:** it does not exclude a chunk of a translate of `E`
    lying in the end layer, since that chunk has empty interior in `F`.

  What remains to exclude is: `y ∈ d⁻¹(1)`, the component of `F ∩ O` through `y` lies in `d⁻¹(1)`,
  and it reaches only the left side. A possible tool is Lemma 5 for `d` (the layers of `F` are
  nowhere dense and `d` is monotone) together with the essential-continuum argument of
  `strand_essential`. It is not checked.

  This is a gap in the text: "Note that `x₂ₙ = 1`" and Property 4 for the top block both depend on
  3b.

**3c: open.** The route needs 3b, and also that the layer of `F` through a point over the inner
middle of a crossing component is the translated layer (`lemma3_half` both ways).

### 1.4 §4: `SepByCrossing`, `x₂ₙ = 1`, the top block

**4.A: proved.**
* `hagopian76_T12_comp` is `hagopian76_T12_uncond` with the composant conditions exported (they
  come from `exists_generic_pq_comp_aux`).
* `exists_T12Data_comp` is the companion `exists_T12Data′`. It adds the base point `x₀`
  (`D.p = D.h x₀`) and `D.h x₀, D.h₁ x₀ ∉ composant x₀`.
* `strand_misses_of_composant` is the composant argument of §4.A: `F ⊆ composant x₀`, and
  `h[R(E)] ⊆ composant p` is disjoint from it.
* The delivered statement `strand_misses_F_of_composant` says: in the set-up of `exists_T12Data`
  there is a package with every proper subcontinuum through a point of `h[R(E)] ∪ h₁[R(E)]` disjoint
  from `F`. This covers the closures of the strands of `p = h x₀` and `f(p) = h₁ x₀`.
* `T12Data` is unchanged.

**4.B: open.** `strand_crossing` gives that the strands of `p`, `f(p)` are crossing components. For
them to be crossing pieces:
* **closedness in `O`:** a component of the relatively closed `M ∩ O` is relatively closed. This is
  routine but not written.
* **the closures miss `π⁻¹[I₂]`:** this needs `I₂ ∩ π[M] = ∅`. The commission asserts it, but in
  the project only `frontier (F[D′]) ∩ π[M] ⊆` bottom ∪ sides is available (`IsCrossRegion`), and
  the ends `F(3/22, r₂)`, `F(19/22, s₂)` of `I₂` lie on the side segments. Either `I₂` should be
  taken with its ends removed in `crossing_sides`, or the setup should record `I₂ ∩ π[M] = ∅`.
* **the bottom edge:** this is settled by 4.A, because the closure of the strand misses `F ⊇ E`.

**4.C: proved conditionally** (`sep_by_crossing`, from `sepByCrossing_of_sigma_pieces`):
* **hypotheses:** the frame hypotheses, `InnerComponentsCross G … lo hi` with `t₀ ∈ (lo, hi)`, and
  crossing pieces `X ∋ p`, `Y ∋ q` (equal or disjoint) missing `G`;
* **conclusion:** `SepByCrossing G π F c₁ D′ O p q`.

The bridge from components in the plane to the batch-176 `IsCrossingComponent` (components in `M`)
is `image_val_connectedComponentIn` and `toPt_crossSet`. Then:
* `x₂ₙ = 1` is `hagopian76_x2n_eq_one` applied to this `SepByCrossing`;
* Property 4 for the top block is `hagopian76_property4_top`.

These compositions are not stated separately, because their hypothesis lists are the union of the
two. The unconditional forms wait on 3b and 4.B.

### 1.5 §5: unicoherence

* `separatesPlane_union_of_inter_disconnected`: the commission's route. One change: `φ` is an
  Urysohn function (`exists_continuous_zero_one_of_isClosed`) rather than the explicit quotient of
  distances. Statement unchanged.
* `sepIn_iff_separatesPts_union`: shape chosen. For `O` open, `Y` disjoint from `O` with
  `Fr O ⊆ Y`, and `p, q ∈ O − X`: `SepIn O X p q ↔ SeparatesPts (X ∪ Y) p q`. No compactness or
  connectedness is needed.

### 1.6 §6: the blocks

`exists_blocks` (from `blocks_of_finset`, `blocks_of_finite`, `exists_blocks_aux`).

**Inputs, all hypotheses:**
* `e` with `d⁻¹[[0, e]] = E` and `e` below every member of `I` (`hagopian76_J_xs`);
* `I` finite (`hagopian76_I_finite`);
* `x₂ₙ = 1`, as `LastIntervalReachesOne`;
* **nondegeneracy** `∀ r ∈ I, r₁ < r₂`.

**Outputs:** the block data of `hagopian76_T15_T17_cond2`, plus the two clauses of §6:
* every point of a block lies in `[0, e]` or in a member of `I` (each block is a union of members
  of `J`);
* no member of `I` meets a gap.

The proof is an induction that adds the member with the largest left end.

**Finding (ledger check 7).** Without nondegeneracy, a member `[u, u]` lying in no other member
forms its own block. Then `x₂ᵢ₋₁ = x₂ᵢ`, against `StrictMonoOn x`. Such a member would be a crossing
component inside one layer `d⁻¹(u)`. That this is impossible is not proved, and the text does not
discuss it.

### 1.7 §7: the assembly

**Open.** `Thm1Setup` is not written. See the skeleton in §5.

### 1.8 §8: the induction step

**Open.**
* E0 and E1 reduce to SSL and its converse (proved), plus 3c and 4.B (open).
* E2.1 uses `strand_misses_F_of_composant` (`L ∩ F = ∅`), which is proved.
* The cap's tool (§5) is proved. (α), (β) and (γ) are discussed in the notes.
* The local-to-global step needs SSL in `O_L`. The frame is abstract, so it applies once `O_L` and
  its vertical are shown to satisfy the frame axioms.

Full reconstruction: `doc/notes/hagopian76-cases.md`.

## 2. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXIII (batch 178)". Its checks:
1. p. 348, "Note that `x₂ₙ = 1`": gap in exposition, reduced to 3b and 4.B, open.
2. p. 348, Property 4 for the top block: the same.
3. p. 348, "… unless `yᵢ` is above `d⁻¹[J]`": correct in strand form, open (3c, 4.B).
4. p. 348, Case 1, the position sentence, `Q`, "between": gap in exposition, open; (α), (β) decided
   in the notes.
5. p. 349, Case 2: gap in exposition, open; reconstruction in the notes.
6. The end layer of `F`: 3a proved; 3b open (configuration 3.3).
7. New finding: nondegeneracy of the members of `I` is needed for the blocks.

## 3. Axioms

`doc/batches/audits/axioms-batch178.txt` holds `#print axioms` for each of the 71 new theorems
(group *Hagopian 1976 XXIII (batch 178)* of `Axioms.lean`). Every one depends on exactly
`[propext, Classical.choice, Quot.sound]`.

The delivered statements are:
* `separatesPlane_union_of_inter_disconnected`, `sepIn_iff_separatesPts_union`;
* `crossing_piece_meets_sigma`, `crossing_piece_sides`, `crossing_piece_below_iff`,
  `crossing_piece_below_trans`, `crossing_piece_no_pocket`;
* `strand_separation`, `strand_separation_converse`, `sepByCrossing_of_inner_crossing`;
* `T12Data.end_layer_not_subset`, `strand_misses_F_of_composant`, `sep_by_crossing`,
  `exists_blocks`.

The supporting declarations are listed in the group.

## 4. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_T15_T17_cond2 (proved): package, Y discharged; needs
   ├─ SepByCrossing (p, f p)                ← sep_by_crossing (proved, conditional)
   │   ├─ InnerComponentsCross (3b)          OPEN (configuration 3.3)
   │   ├─ p, f p on crossing pieces (4.B)    OPEN (I₂ ends; closedness in O)
   │   │   └─ strands miss F (4.A)           proved: strand_misses_F_of_composant
   │   └─ order of pieces, SSL (§1, §2)      proved
   ├─ blocks (§6)                           ← exists_blocks (proved, conditional)
   │   ├─ e, finiteness                      proved (hagopian76_J_xs, hagopian76_I_finite)
   │   ├─ x₂ₙ = 1                            ← hagopian76_x2n_eq_one + SepByCrossing
   │   └─ nondegeneracy of I                 OPEN
   └─ Property4Step (§8)                    OPEN
       ├─ E0, E1                             SSL + converse (proved); 3c OPEN
       ├─ E2.1–E2.2                          strands miss F (proved); minimal L OPEN
       ├─ E2.3 cap                           unicoherence (proved); (α)(β)(γ) OPEN
       ├─ E2.4                               Property2At (batch 176); H OPEN
       └─ E2.5–E2.6                          Janiszewski (proved); SSL in O_L OPEN
3a (end layer) proved: T12Data.end_layer_not_subset (used by the 3b route)
§7 Thm1Setup                                OPEN (skeleton §5)
```

## 5. Skeleton proposal for what remains

1. **4.B (short).**
   * `isClosed_component_in_O`: a component of `M ∩ O` is closed in `O`.
   * Record `I₂ ∩ π[M] = ∅` in the setup, or remove the ends of `I₂` in `crossing_sides`. The ends
     are on the side segments, so the change is harmless there.
   * Then `p_on_crossing_piece` for `p` and `f(p)`, and "equal or disjoint" (components).
2. **3b (main).** First formalize steps 1, 2 and 3.1–3.2 as stated. For 3.3, state the residual
   configuration as a `Prop` (`EndLayerChunk`: `y ∈ d⁻¹(1)` and the component of `F ∩ O` through `y`
   lies in `d⁻¹(1)`) and try to exclude it with Lemma 5 for `d` and `strand_essential`.
3. **Nondegeneracy.** `crossingIntervals_nondegenerate`: a crossing component is not contained in
   one layer `d⁻¹(u)`. Candidate route: a layer of `F` over the inner middle is the translated layer
   (`lemma3_half`), which has diameter `< ε₁`, while a crossing component has diameter at least
   `16/22 − 4/n`.
4. **§7.** Proposed shape:
   ```
   structure Thm1Setup (M) where
     E k hE                      -- minimal admissible E (Lemmas 1–5)
     π γ hπ hπS hγπ              -- exists_quotient_plane, hagopian76_reparam
     F hF                        -- exists_collar
     ε₁ L hP1                    -- Property 1
     n θ c hS hn                 -- StrandConst, exists_param_sep (n ≥ 15)
     c₁ D' hR hD'c hc₁           -- hagopian76_D (T7), c₁ ≤ min c (I_finite's c)
     r₂ s₂ I₂ hI hIs hIR hDo hDf hFDf t₀ w₂ ...
     ε₂ ε₃ hP2                   -- Property2At ε₂ ε₃
     D : T12Data … ε₃; x₀; hcomp -- exists_T12Data_comp
     e x n hblocks               -- exists_blocks
   theorem hagopian76_theorem1_of_step :
     (∀ S : Thm1Setup M, InnerComponentsCross … → Nondeg … → Property4Step S.D S.x S.n) →
       Hagopian76Thm1
   ```
5. **§8.** In order: E0 (from 3c), E1, E2.4 (identify `H`), E2.1 (minimal `L`), then the cap with
   the two-point intersection lemma, then SSL in `O_L` via a second `VFrame`.
