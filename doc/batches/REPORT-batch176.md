Commission read: `doc/batches/COMMISSION-batch176.md` ("Commission: batch 176 — Part E, Hagopian 1976 XXI: Theorem 1 — the cutting step; positions by `ε₃`; Property 4; the induction").

# Report, batch 176

## 0. Summary

* **A (positions by `ε₃`): proved** (`eps3_positions_middle`, `eps3_image_middle`). For every
  `ε₂ > 0` there is `ε₃ ∈ (0, ε₂)` with Property 2 at `ε₃`, such that every point of `M` within `ε₃`
  of a point over the abscissa `1/2` lies over an abscissa in `(3/8, 5/8)`. Shrinking `ε₃` keeps
  Property 2 (`Property2At.mono`).
* **B (`sep_by_crossing`, `TailCutKeepsSep`, `x₂ₙ = 1`): reduced; the reductions are proved.**
  * `sep_by_crossing` is the named `Prop` `SepByCrossing` (open), for `X = G`.
  * `SepByCrossing → TailCutKeepsSep` (`sep_by_crossing_cut`), hence `x₂ₙ = 1` from `SepByCrossing`
    (`hagopian76_x2n_eq_one`).
  * Route 3, in the form the argument needs, is proved: **Janiszewski's theorem inside a domain**
    (`sepIn_union_cases`).
* **C (`T12Data`, Property 4 for the top block): definitions given; Property 4 for the top block
  proved from `SepByCrossing`** (`hagopian76_property4_top`). The existence of a `T12Data` is open.
* **D (the induction): open.** Recorded as the named `Prop` `Property4Step`.
* **E (the assembly): conditional form proved** (`hagopian76_T15_T17_cond`): on a `T12Data` with the
  blocks of `St J`, `SepByCrossing` and `Property4Step` give `False`.
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

STATUS lines, in order:
* `STATUS: A proved (eps3_positions_middle, eps3_image_middle, Property2At.mono)`
* `STATUS: B open, reduced (SepByCrossing → TailCutKeepsSep → x₂ₙ = 1: sep_by_crossing_cut, hagopian76_x2n_eq_one; sepIn_union_cases proved)`
* `STATUS: C partly proved (T12Data, Property4 defined; hagopian76_property4_top from SepByCrossing; existence of T12Data open)`
* `STATUS: D open (Property4Step)`
* `STATUS: E conditional form proved (hagopian76_T15_T17_cond); hagopian76_theorem1_final open`

The build:
* `lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76U` at the end of `HPC.lean`.
* The regenerated `axioms.txt` has 1901 lines (1880 + 21, one per new theorem), with
  `sorryAx` in none; see §3.
* All 21 new theorems use exactly `propext`, `Classical.choice` and `Quot.sound`.
* No declaration uses `sorry`. The word occurs only in the comment block at the end of
  `Hagopian76U.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76U.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Eps3.lean`: uniform continuity of `π` and of the inverse collar; `Property2At`;
* `H76Cut.lean`: Janiszewski inside a domain; crossing closures and `I`; `SepByCrossing`; the
  cutting step and the separation above a gap;
* `H76Prop4.lean`: `T12Data`, `Property4`, the base case, the top block, the closing contradiction.

No earlier `Hagopian76*.lean` file was edited: none of the commented-out copies there is proved as
stated (the batch-175 `tailCutKeepsSep` and `hagopian76_property4_top` shapes are unconditional; what
is proved here is conditional on `SepByCrossing` and a `T12Data`).

## 1. The items

### 1.A Positions by `ε₃` (proved)

**The check of §1.A.** True as the commission says.
* `π` is uniformly continuous on the compact `M` (`CompactSpace.uniformContinuous_of_continuous`).
* The collar is an embedding of the compact rectangle `R = [0, 1] × [−1, 1]`. Instead of the inverse
  collar, the proof uses the compact set `{(z, z′) ∈ R × R : |z₁ − z′₁| ≥ μ}`, on which
  `dist(F z, F z′)` is continuous and positive (injectivity), hence `≥ η > 0`
  (`collar_abscissa_sep`).
* Together: `M`-close points have `F`-coordinates with close abscissae (`pi_abscissa_close`).

**`eps3_positions_middle`.** For `ε₂ > 0` there is `ε₃ ∈ (0, ε₂)` such that
* `Property2At k ε₂ ε₃` (Property 2, the conclusion of `hagopian76_property2`), and
* for `y, w ∈ M` with `π(y) = F(z)`, `π(w) = F(z′)`, `z, z′ ∈ R`, `z₁ = 1/2`, `dist(y, w) < ε₃`:
  `z′₁ ∈ (3/8, 5/8)`.

`ε₃ = min(ε₃⁰, δ)` with `ε₃⁰` from Property 2 and `δ` from `pi_abscissa_close` at `μ = 1/8`.
`eps3_image_middle` is the form of p. 348: `f(y)` over `D` for an `ε₃`-homeomorphism `f`.

**Shrinking `ε₃` is harmless** (`Property2At.mono`): both the hypothesis on `h` and `ρ(T, V) < ε₃`
become stronger. T12's `ε₃/2`-homeomorphisms are chosen after `ε₃` (in `T12Data` they are fields
with `ε₃/2`; `T12Data.f_small` gives `f` an `ε₃`-homeomorphism).

*Shape:* the position is stated for any `w` within `ε₃` of `y`, with `y` exactly over `1/2`
(Hagopian's `K` is over `p₃`, abscissa `11/22`). It covers `f(yᵢ₋₁)`, `f(yᵢ)`, `p` (= `h(x)`, `x`
over `1/2`) and `q`. So `[3/8, 5/8]` replaces `L₆` at the sentence "`f(yᵢ₋₁)` belongs to
`L₆ ∩ π⁻¹[D]`".

### 1.B `sep_by_crossing`, `TailCutKeepsSep`, `x₂ₙ = 1` (reduced)

**Proved.**
* `sepIn_union_cases` (route 3, "State what is needed"). Let `Y` be compact and connected, with
  `Y ∩ O = ∅` and `Fr O ⊆ Y`. If compact `A`, `B` with `A ∩ B ∩ O = ∅` together separate `p` from
  `q` in `O`, then `A` or `B` does. Proof: `janiszewski_compact` applied to `(A ∩ Cl O) ∪ Y` and
  `(B ∩ Cl O) ∪ Y`, whose intersection is `Y`; a connected set from `p` missing `Y` stays in `O`.
* `closure_crossing_subset_interval`: the closure of a crossing component lies in
  `d⁻¹[[x, y]]` for its irreducible interval `[x, y] ∈ I`. This answers the check of route 1
  ("whether a crossing component of `F` that meets `X` lies in `X`"): for `X = d⁻¹[[0, t]]` with `t`
  beyond every member of `I`, every crossing component lies in `X`, closure included.
* `sep_by_crossing_cut` (`tailCutKeepsSep_of_sepByCrossing`): `SepByCrossing → TailCutKeepsSep`.
* `hagopian76_x2n_eq_one`: hypotheses of `hagopian76_x2n_eq_one_of_cut`, with `SepByCrossing` in
  place of `TailCutKeepsSep`; conclusion `LastIntervalReachesOne` (`x₂ₙ = 1`).

**Named `Prop`:** `SepByCrossing G π F c₁ D' O p q`: if `G` separates `p` from `q` in `O`, so does
the union of the closures of the crossing components of `G ∩ π⁻¹[D]`.

*Shape changes:*
* `X = G` (not every compact `X ⊆ F`). The cutting step applies it to `G` itself.
* Closures of crossing components (a weaker requirement than the union of the components).
* For the given `p`, `q` only; for Hagopian these are `p ∈ K` and `f(p)`, both over the middle by A.
  The statement for arbitrary points of `π⁻¹[D]` is false (a pocket component cuts off the points
  beneath it).

**Obstruction** (`SepByCrossing` itself).
* Route 3 handles two compact pieces that do not meet inside `O`. The crossing components and the
  rest of `G ∩ π⁻¹[D]` are not of that form: they are not divided by a layer of `d` missing `π⁻¹[D]`.
* Route 1's obstruction is the one the commission names: a component of `G ∩ π⁻¹[D]` meeting `d⁻¹(1)`
  and reaching into the middle strip (P3's exception). For `X = G` this case does occur, since
  `d⁻¹(1) ⊆ G`. The commission's remark that `X = d⁻¹[[0, t]]` misses `d⁻¹(1)` is about the
  conclusion of the cutting step. The hypothesis is about `G`.
* Route 2 needs the classification of the components of `π⁻¹[D] − G`. It is not formalized.

### 1.C `T12Data`, Property 4 for the top block

**Definitions.**
* `T12Data E k π F D' ε₃` (structure). Its fields:
  * `K`, `p ∈ K`;
  * `h`, `h₁` (`ε₃/2`-homeomorphisms);
  * `ess` (T12 (2): `h⁻¹[Cl Cₚ]` essential to `R(E)`);
  * `G`, `d`, `hG`, `hEG`, `hX0` (Hagopian's `F`, with `d⁻¹(0) = k⁻¹(0)`);
  * `sep` (`G` separates `p` from `f(p)` in `π⁻¹[D]`) and `irr` (T13).

  `T12Data.f = h₁h⁻¹`. The blocks `xᵢ` are not fields: they are determined by `d` and `I`.
* `Property4 D x y`: some `yₙ ∈ K` has `h⁻¹[Cl C_{yₙ}]` essential to `R(E)` and
  `d⁻¹[[x, y]]` separating `yₙ` from `f(yₙ)` in `π⁻¹[D]`.

**Proved.**
* `sepIn_above_gap`: let `G` be irreducible (T13) and let `O` be surrounded by `Y`. Let `s₁ < s₂` be a
  gap of `St J`: every member of `I` lies in `[0, s₁]` or `[s₂, 1]`, `E ⊆ d⁻¹[[0, s₁]]`, `s₁ > 0`.
  Then `SepByCrossing` gives `d⁻¹[[s₂, 1]]` separating.
  * The crossing closures lie in `d⁻¹[[0, s₁]] ∪ d⁻¹[[s₂, 1]]`, so these disjoint compacta separate.
  * By `sepIn_union_cases`, one of them does.
  * `d⁻¹[[0, s₁]]` is a proper extension of `E` away from `k⁻¹(0)` (`piece_map`, Lemma 5), excluded by
    irreducibility.
* `hagopian76_property4_top` (`property4_top_of_sepByCrossing`): `Property4 D s₂ 1`, with `yₙ = p`,
  clause (1) from `D.ess`. With `s₁ = x₂ₙ₋₂`, `s₂ = x₂ₙ₋₁` and `x₂ₙ = 1` (B) this is Property 4 for
  `[x₂ₙ₋₁, x₂ₙ]`.
* `not_property4_E`: `[x₁, x₂]` does not have Property 4 (from `hagopian76_property4_base`).

**Open: the existence of `T12Data`.**
* `hagopian76_T12_uncond` gives `h`, `h₁`, the separation, and the extension.
* `hagopian76_T12_parts12` gives T12 (2) for another `ε₁`-homeomorphism `h′` (T9's), with
  `Cl Cₚ ⊆ h′[E]`.
* Hagopian's "h maps a subcontinuum of E that is essential to R(J) onto Cl C" (Lemma 5 for the `h`
  with `h(x) = p`) is not formalized for that `h`.
* T13 (`hagopian76_T13_uncond`) gives `G` with `sep` and `irr`.

`Y` (for Hagopian's domain, `π⁻¹[Fr D]`) is carried as a hypothesis: compactness of `π⁻¹` of a
compact set and connectedness of `π⁻¹[Fr D]` are not derived here.

### 1.D The induction (open)

* **"Let `Cᵢ₋₁` be the first component …".** Extensions of `Cl Cᵢ` away from `X` are translates of
  extensions of `E`, or lie in `h[R(E)]`. Transporting Property 3 and `hagopian76_I_finite` by `h`
  needs two things, neither formalized:
  * these extensions must be type A′ continua whose decompositions are compatible with `D`;
  * "first" needs the order of the crossing components along the extension.
* **"`N` does not come within `ε₂` of `π⁻¹(p₄)`".** P3 transported by `h` controls `L` only over the
  middle `[3/8, 5/8]`. `π⁻¹(p₄)` lies over `15/22 > 5/8`, outside that range. So more than P3 is
  needed: control of `L` over the right-hand third.
* **"Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`".** By A, `f(yᵢ₋₁)` is over the
  middle, where `cover_pocket_middle` controls the pockets. The separation by `P ∪ Q` is route 2.

Named `Prop`: `Property4Step D x n` (for `2 ≤ i ≤ n`, Property 4 for `[x₂ᵢ₋₁, x₂ᵢ]` implies it
for `[x₂ᵢ₋₃, x₂ᵢ₋₂]`).

### 1.E The assembly (conditional form)

* `false_of_property4_chain`: Property 4 for the top block, `Property4Step`, and `¬` Property 4 for
  `[x₁, x₂]` give `False` (finite descent).
* `hagopian76_T15_T17_cond`: a `T12Data` `D` with blocks `x₁ < ⋯ < x₂ₙ` (`n ≥ 2`, strictly
  increasing, `x₁ = 0`, `d⁻¹[[0, x₂]] = E`, each member of `I` in a block, `x₂ₙ = 1`), `Y`,
  `SepByCrossing` and `Property4Step` give `False`.

Exactly what remains for `hagopian76_theorem1_final`:
* `SepByCrossing` (B);
* `Property4Step` (D);
* the existence of `T12Data` (C);
* the blocks from the finite `I`;
* `Y`;
* the reduction of `Hagopian76Thm1` to the set-up (T1–T11, proved piecewise and not assembled).

## 2. Ledger entries (`LEDGER.md` §6, batch 176)

1. **p. 348:** "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`." **A stronger position is available
   and proved:** over the abscissae `(3/8, 5/8)` for `ε₃` small (`eps3_positions_middle`).
2. **p. 348:** "Note that … `x₂ₙ = 1`." **Open; reduced** to `SepByCrossing`
   (`hagopian76_x2n_eq_one`). Gap in exposition, not a refutation.
3. **p. 348:** Property 4 for the top block. **Reduced:** proved from `SepByCrossing` and a
   `T12Data` (`hagopian76_property4_top`). The step "only the top block separates" is
   Janiszewski inside `π⁻¹[D]` plus irreducibility.
4. **pp. 348–349, Cases 1–2; "first component"; `N`; "either above or below".** **Open**, with the
   obstructions of §1.D.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XXI (batch 176)* of `Axioms.lean`; per-theorem output in
`doc/batches/audits/axioms-batch176.txt`. Each of the 21 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* skeleton: `eps3_positions_middle`, `eps3_image_middle`, `sep_by_crossing_cut`,
  `hagopian76_x2n_eq_one`, `hagopian76_property4_top`, `hagopian76_T15_T17_cond`;
* `H76Eps3.lean`: `collar_abscissa_sep`, `pi_abscissa_close`, `Property2At.mono`;
* `H76Cut.lean`: `sepIn_union_cases`, `layerSet_subset`, `layerSet_mono`,
  `closure_crossing_subset_interval`, `iUnion_crossing_subset`, `tailCutKeepsSep_of_sepByCrossing`,
  `isCompact_toPt_layerSet`, `sepIn_above_gap`;
* `H76Prop4.lean`: `T12Data.f_small`, `not_property4_E`, `false_of_property4_chain`,
  `property4_top_of_sepByCrossing`.

Named `Prop`s and structures introduced:
* `Property2At` (Property 2 at `ε₃`; proved for small `ε₃`);
* `SepByCrossing` (open; assumed by `sep_by_crossing_cut`, `hagopian76_x2n_eq_one`,
  `hagopian76_property4_top`, `hagopian76_T15_T17_cond`);
* `T12Data` (structure; existence open);
* `Property4`;
* `Property4Step` (open; assumed by `hagopian76_T15_T17_cond`).

## 4. Dependency map of Theorem 1, updated

```
uniform continuity of π, collar embedding ── eps3_positions_middle (A)             [PROVED]
Property 2 (Lemma 7) ── Property2At.mono ──┘
                                │
P3 (batch 175), cover_pocket_middle, tail lemma                                    [PROVED]
janiszewski_compact ── sepIn_union_cases (Janiszewski in a domain)                 [PROVED]
closure_crossing_subset_interval                                                   [PROVED]
                                │
SepByCrossing (separation witnessed by crossing closures)                         [open]
   ├─ sep_by_crossing_cut: → TailCutKeepsSep                                       [PROVED]
   │     └─ hagopian76_x2n_eq_one: → x₂ₙ = 1                                       [PROVED]
   └─ sepIn_above_gap (+ T13 irreducibility, Lemma 5)                              [PROVED]
         └─ hagopian76_property4_top (on T12Data)                                  [PROVED]
T12Data existence (T12 (2) for the h of T12 (3))                                   [open]
Property4Step (Cases 1–2: first component; N vs π⁻¹(p₄); P ∪ Q)                    [open]
not_property4_E (base), false_of_property4_chain                                   [PROVED]
   └─ hagopian76_T15_T17_cond: T12Data + SepByCrossing + Property4Step → False      [PROVED]
set-up of Theorem 1 from ¬HI (T1–T11 assembled), Y = π⁻¹[Fr D]                     [open]
   └─ hagopian76_theorem1_final                                                    [open]
```

## 5. Skeleton proposal for what remains

```
-- B: the separation statement, in the plane picture of D′ (left/right non-crossing components
-- are off the middle by P3; the exceptional components meet d⁻¹(1))
theorem sep_by_crossing … : SepByCrossing G π F c₁ D' (π ⁻¹' (F '' D')) p (f p)

-- C: T12 (2) for the h of T12 (3)
theorem exists_T12Data … : Nonempty (T12Data E k π F D' ε₃)

-- Y for Hagopian's domain
theorem pi_preimage_frontier_D … :
    IsCompact (π ⁻¹' frontier (F '' D')) ∧ IsConnected (π ⁻¹' frontier (F '' D'))

-- the blocks of St J from the finite I
theorem exists_blocks … : ∃ x n, StrictMono x ∧ x 1 = 0 ∧ layerSet d (Icc 0 (x 2)) = E ∧ …

-- D
theorem hagopian76_property4_step … : Property4Step D x n
```
