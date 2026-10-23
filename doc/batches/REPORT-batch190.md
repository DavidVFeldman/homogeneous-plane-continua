Commission read: `doc/batches/COMMISSION-batch190.md` ("Commission: batch 190 — Part E, Jones 1975 II: the planar core; `NoArcIndecHomPlane`").

# Report, batch 190

## 0. Summary, omissions

**Every formal item of the commission (§2–§6) is proved, including §6:
`jones75_noArc : NoArcIndecHomPlane` and `hagopian76_theorem1 : Hagopian76Thm1`.** The files are

* `HPC/Jones/Jones75Pass.lean` (§2: passes, (P1)–(P4), the flip `F̄`),
* `HPC/Jones/Jones75Shadow.lean` (§3: shadow lemma, flow box, scale 2, late thin passes),
* `HPC/Jones/Jones75Region.lean` (§4 and Lemma A of §5; N1, N2, N4),
* `HPC/Jones/Jones75Trap.lean` (§5: N3, Steps 2–6, the trapping lemma),
* `HPC/Jones/Jones75B.lean` (§6: C1–C5, the Theorem, the corollaries; index of the skeleton).

`HPC.lean` ends with `import HPC.Jones.Jones75B`; `lake build HPC` succeeds. No declaration contains
`sorry`, and nothing is left commented out. Nothing is refuted. Nothing is open: `OPEN.md` records
that the route to `Hagopian76Thm1` has no open input.

`axioms.txt` has **2550 lines** (2479 + 71 added, none removed). `sorryAx` occurs in none of them.
The 71 new theorems (group "Jones 1975 II (batch 190)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch190.txt`) all use exactly `[propext, Classical.choice, Quot.sound]`.

**Omissions.** None.

Status lines:
* STATUS: §2 `IsPass`, `PassMon` (definitions, unchanged); (P1) `IsPass.disjoint` proved; (P2)
  `IsPass.finite` proved; (P3) `isPass_base` proved; (P4) `IsPass.above_or_below` proved
* STATUS: §3 `shadow_pass` proved; `flow_box` proved; `scale_two` proved;
  `exists_late_thin_pass` proved; first thin pass `exists_first_pass` proved
* STATUS: §7 N1 `thinPass_arc`, N2 `tarc_lowest`, N3 `two_sides`, N4
  `IsPass.lc_left_mem_closure` proved
* STATUS: §4 (R1) `region_pass`, (R1).3 `region_thin_above`, (R2) `region_cross` proved; (R3) is
  `seg_subset_rect_domain` and `rect_domain_low` (existing), used in `trap_pass`
* STATUS: §5 Lemma A `region_lemmaA` proved; Steps 2–5 `trap_jordan` proved; the trapping lemma
  `trap_pass` proved
* STATUS: §6 C2–C5 `jones75_final_aux` proved; C1 and the contradiction `jones75_contra` proved;
  `jones75_noArc : NoArcIndecHomPlane` proved; `hagopian76_theorem1 : Hagopian76Thm1` proved;
  `bing60_plane_uncond`, `hagopian76_theorem2_uncond` proved; also `hagopian75_corollary_uncond`,
  `hagopian75_theorem2_uncond`, `hagopian75_theorem1_of_noArc_uncond` proved

**Shape changes** (each is also recorded at the statement):
* `IsPass.disjoint`, `IsPass.finite`, `shadow_pass`, `flow_box`, `jones75_noArc`,
  `hagopian76_theorem1`, `bing60_plane_uncond`, `hagopian76_theorem2_uncond`: exactly the skeleton's
  statements (the implicit variables `γ F ℓ` are file-level `variable`s).
* `exists_late_thin_pass`: the extra hypothesis `hη : η ≤ 1` is added. It is needed for (P1), which
  the proof uses to rule out that the thin pass found by recurrence starts before `T`. (The
  commission allowed the shape to be adjusted.) Every use has `η = ½`.
* `IsPass.above_or_below` (skeleton: `True`): for `0 < η ≤ 1`, a continuous injective `ℓ` and a
  pass `(a, b) ≠ (¼, ¾)`, `PassAbove F ℓ a b ∨ PassBelow F ℓ a b`, where `PassAbove` says every
  point of `ℓ[a, b]`, end points included, is `F z` with `z ∈ [0,1] × [−1,1]` and `z.2 > 0`
  (`PassBelow`: `z.2 < 0`).
* `region_of_thin_pass` (skeleton: `True`) is split into `thinPass_arc` (N1), `region_pass` ((R1).1
  and (R1).2), `region_thin_above` ((R1).3), `region_cross` ((R2)) and `region_lemmaA` (Lemma A).
  The region is not packaged as a definition: `D` is any set with `D ⊆ (¼, ¾) × (0, η₂)` and the
  frontier formula `RegionFrontier F ℓ a_m b_m D`, which is what `rect_domain_aux` provides.
  Coordinates are taken through `lc F ℓ t` (the collar coordinates of `ℓ t`, `collarCoord`).
* `trap_pass` (skeleton: `True`): for a thin upper pass `P_m = ℓ[a_m, b_m]` of `Q_{1/2}` with
  `a_m > ¾`, under (FB) for `η₂ < ½`, and under (H) in the form "every thin upper pass of `Q_{1/2}`
  with `a > ¾` has `a ≥ a_m`", there is `h > 0` such that no pass with `a > b_m` has an interior
  point in `F((3/8, 5/8) × (0, h))`.
  * (H) is stated through minimality, which is how §6 uses it. The commission's (H) follows from it
    by (R1).3, and this is how `region_lemmaA` uses it.
  * The conclusion is about the low strip `F((3/8, 5/8) × (0, h))` instead of all of `R_m`. A pass
    meeting `R_m` has its interior in `R_m` (R1), and §6 only ever produces passes through points of
    the low strip, so this is the form used (C3, C5).
* N3 `two_sides` is stated with one set `A` (the union `B_L ∪ B_R` of the commission) and the
  frontier of one component only: if `frontier W′ = J`, `p ∈ J`, `N` is open with `p ∈ N`,
  `N ∖ J ⊆ A ⊆ W`, `W ∩ W′ = ∅` and `W′ ∩ J = ∅`, then `False`.
* (FB) is given a name, `FBProp F η₂ ℓ`, so that it can be passed from §3 to §5–§6 and flipped
  (`FBProp.flip`). `PassThin F η₂ ℓ a b` names "`ℓ[a, b] ⊆ F([¼, ¾] × [−η₂, η₂])`", the thinness of
  §3. `flipC F` is `F̄`, `cRect = [0,1] × [−1,1]`.
* The skeleton is split over five files under `HPC/Jones/`. `IsPass` and `PassMon` moved to
  `Jones75Pass.lean`, unchanged.
* `hagopian75_theorem1` (the conditional Theorem 1 of Hagopian 1975) is the only other theorem
  whose only open hypothesis was `Hagopian76Thm1` and for which no unconditional form was added:
  with `hagopian76_theorem1` its hypothesis "`A` is a decomposable subcontinuum of an indecomposable
  homogeneous plane continuum" can never hold, so the unconditional form would be vacuous. The
  meaningful unconditional statement is `hagopian76_theorem1` itself.
* `trap_jordan` and `trap_pass` carry `set_option maxHeartbeats 1600000 in` (long elaboration, no
  other effect).
* The commented-out copies of `hagopian76_theorem1` / `hagopian76_theorem1_final` left in
  `Hagopian76P`, `Q`, `R`, `S`, `T`, `U`, `V`, `W`, `X`, `Y` and `AB.lean` by earlier batches are
  replaced by one-line pointers to `HPC/Jones/Jones75B.lean`.

## 1. The items, in order

Notation as in the commission: `F` is a collar of `γ = ℓ|[0, 1]` (`IsCollar γ F`, with
`hγ : ∀ t, γ t = ℓ t`), `ℓ` a line (`IsLine ℓ`: continuous, injective, with range the arc component of `ℓ 0`), boxes
`Q_η = F([¼, ¾] × [−η, η])`, `κ = 1/32`, middle band `[9/32, 23/32]`.

### §2. Passes (`Jones75Pass.lean`)

* `IsPass F η ℓ a b`, `PassMon F κ ℓ a b`: the skeleton's definitions.
* **(P1)** `IsPass.disjoint`: for `η ≤ 1`, distinct passes have disjoint closed parameter
  intervals. Forms used: `IsPass.eq_of_le`, `IsPass.eq_of_mem` (passes whose closed intervals meet
  are equal) and `IsPass.lt_of_mem`. The proof is the commission's three cases, through the
  injectivity of `F` on `cRect` (`IsCollar.injOn`) and the coordinates `lc`.
* **(P2)** `IsPass.finite`: only finitely many passes start at most `N` and end at least `−N`.
  Through `IsPass.exists_length` (passes starting in `[−N, N]` have length at least a uniform
  `ρ > 0`, by uniform continuity on `[−N − 1, N + 1]` and `d(L, Rt) > 0`) and (P1). Form used:
  `exists_first_pass` (among passes satisfying a predicate `Q` and starting after `c`, if any,
  one starts first).
* **(P3)** `isPass_base`: `ℓ[¼, ¾]` is a pass of `Q_η` for `η > 0`.
* **(P4)** `IsPass.above_or_below` (shape above). Through `IsPass.eq_base_of` (a pass through a
  point of `F([0, 1] × {0})` is the base pass, by injectivity of `ℓ` and (P1)) and connectedness of
  `ℓ[a, b]` in `cRect ∖ ([0,1] × {0})`. `PassAbove.not_below`: the two cases exclude each other.
* **Nesting** `IsPass.mono`, and the flip: `IsPass.flip`, `PassThin.flip`, `PassMon.flip`,
  `PassAbove.flip`, `PassBelow.flip`, `PassAbove.of_flip`, `IsPass.of_flip`, `PassThin.of_flip`.

### §3. Shadow lemma and flow box (`Jones75Shadow.lean`)

* `shadow_pass` (skeleton statement): there is `δ > 0` such that for `x ∈ [9/32, 23/32]` and
  `d(ℓ u, ℓ x) < δ`, `u` lies in the open interval of a pass of `Q_{η′}` with (Mon). The proof is the
  commission's: `uniform_near_compact` twice, Effros, (O) through `JonesSetting.orientation`, the
  sup/inf construction with `s₁ = 3/16`, `s₂ = 13/16`.
* `flow_box` (skeleton statement), and `FBProp.passMon` ((FB′): any pass of `Q_{1/2}` through a
  point of `F([9/32, 23/32] × [−η₂, η₂])` has (Mon)).
* `IsPass.thin`, `PassThin.mono`; `scale_two`: points of `ℓ` within `δ₂` of `o = ℓ(½)` lie inside
  thin passes of `Q_{1/2}`.
* `exists_late_thin_pass` (shape above), by recurrence (`line_recurrent`, `mem_omegaLim_iff`).

### N1–N4 and §4. The region of a thin pass (`Jones75Region.lean`)

* **N2** `tarc_lowest`: the commission's statement (`TArc r s I`, `I ⊆ [a, b] × (0, c]`, `r.1 = a`,
  `s.1 = b`, `x₀ ∈ (a, b)` give `w > 0` with `(x₀, w) ∈ I` and `{x₀} × (0, w)` disjoint from `I`).
* **N4** `IsPass.lc_left_mem_closure`: the end points of a pass are in the closure of its interior,
  in collar coordinates. `IsPass.lc_injOn`: `lc` is injective on a pass.
* **N1** `thinPass_arc`: for a thin upper pass `P_m` of `Q_{1/2}` (with `η₂ ≤ 1`),
  `I_m = lc(ℓ[a_m, b_m])` is an arc from `(¼, r₂)` to `(¾, s₂)`, `I_m ⊆ [¼, ¾] × (0, η₂]`, and
  `I_m ∩ ({¼, ¾} × [0, η₂]) = {r, s}`. (Stated for passes, which is the only use; the general
  collar form of N1 was not needed.)
* **(R1)** `region_pass`: for `D ⊆ (¼, ¾) × (0, η₂)` with the frontier formula, a pass
  `(a, b) ≠ (¼, ¾), (a_m, b_m)` of `Q_{1/2}` with one interior point in `D` has all its interior in
  `D`, `lc(ℓ a) ∈ {¼} × (0, r₂)` and `lc(ℓ b) ∈ {¾} × (0, s₂)`. `region_thin_above`: such a pass is
  thin and above (R1.3).
* **(R2)** `region_cross`: under the conclusion of (R1), the interior of the pass meets
  `{c} × (0, w)` for every `c ∈ (¼, ¾)` and every lowest height `w` of `I_m` over `c`
  (`rect_domain_crosscut`).
* **(R3)**: `seg_subset_rect_domain` and `rect_domain_low`, applied in `trap_pass`.
* **Lemma A** `region_lemmaA`: under (FB) and (H) (minimality form), no `v ∈ (¾, a_m)` has
  `ℓ v = F z` with `z ∈ D` and `z.1 ∈ [9/32, 23/32]`.

### §5. The trapping lemma (`Jones75Trap.lean`)

* **N3** `two_sides` (shape above).
* `trap_jordan` (Steps 1–5): given the data of §4 and Lemma A, there are a closed `J` and open,
  disjoint `W_L`, `W_R` with `W_L ∪ W_R = Jᶜ`, (J1) in the form "for `v > t_m`, `ℓ v ∈ J` only if
  `ℓ v = F(½, y)` with `0 < y < y_m`", `T_L ⊆ W_L`, `T_R ⊆ W_R` and `ℓ(t_R) ∈ W_R`. `J` is
  `σ ∪ ℓ[½, t_m]`, a two-arc simple closed curve (`TSCC`); its complement is split by
  `jordan_curve_theorem` through `tscc_homeomorph_circle`. Step 4 (`W_L ≠ W_R`) is `two_sides` at `p = F(½, h/2)` with the square
  `S` and `isOpen_collar_image`.
* `trap_pass` (shape above), Step 6 as in the commission (the last point `s*` of `J` on
  `ℓ[t_R, v_L]`, the pass `P*` through it by (FB), `s* < a` by (Mon), and `v_R ∈ (s*, v_L)` in `W_L`
  against Step 4).

### §6. The contradiction and the Theorem (`Jones75B.lean`)

* `exists_ball_box`: a ball about `o` inside `F((3/8, 5/8) × (−h, h))`.
* `jones75_final_aux` (C2–C5), once the first thin pass after `¾` lies above; `jones75_contra` (C1
  and the reduction "otherwise use `F̄`"): under `JonesSetting M`, a line `ℓ` and a collar `F` of
  `ℓ|[0,1]`, `False`.
* `jones75_noArc : NoArcIndecHomPlane`: the bridge from `α ≃ₜ unitInterval` to `TArc`, then
  `jonesSetting_of_plane`, `JonesSetting.exists_line`, `exists_collar`, `jones75_contra`.
* `hagopian76_theorem1 : Hagopian76Thm1 := hagopian76_theorem1_jones jones75_noArc`.
* `bing60_plane_uncond`, `hagopian76_theorem2_uncond` (skeleton statements);
  `hagopian75_corollary_uncond`, `hagopian75_theorem2_uncond`,
  `hagopian75_theorem1_of_noArc_uncond` (the other conditional theorems whose only open hypothesis
  was `Hagopian76Thm1`, resp. `NoArcIndecHomPlane`).

## 2. Non-vacuity

* **§6 and the corollaries** have the hypotheses of their statements only (`IsHomogeneous`,
  compactness, connectedness, …), which are satisfied (e.g. by a circle, for `bing60_plane_uncond`
  and `hagopian75_theorem2_uncond`).
  `jones75_noArc` and `hagopian76_theorem1` have no hypotheses.
* **§3–§6 items with `JonesSetting M`, `IsLine ℓ` and `IsCollar γ F`.** These hypotheses are
  jointly unsatisfiable: that is exactly `jones75_contra`. So every item of §3–§5 that assumes all
  three is vacuously true *a posteriori*; this is unavoidable in a proof by contradiction, and the
  items are the steps of that proof. None of them is proved by a shortcut through unsatisfiability:
  each is proved by the argument of the commission, and `jones75_contra` is the last theorem built.
* **Items without `JonesSetting`** (§2, N1–N4, `region_pass`, `region_cross`, `region_lemmaA`,
  `trap_jordan`, `trap_pass`, `jones75_final_aux`) assume only `IsCollar γ F`, `IsLine ℓ` (or
  continuity and injectivity of `ℓ`) and properties such as `FBProp` and minimality. `IsCollar`,
  `IsLine` and `IsPass` are satisfiable together (any collar of a straight line in the plane, with
  the base pass `isPass_base`). `FBProp` together with the hypotheses of `jones75_final_aux` is
  refuted by `jones75_final_aux` itself, but not by any short argument; the remaining hypotheses of
  §2 and N1–N4 are satisfiable (e.g. N2 by a horizontal segment, N3's hypotheses are refuted by its
  own conclusion, as intended).

## 3. Ledger entries (`LEDGER.md`)

* **J75.4, wording** (§9.1): adopted. The entry now reads "**Unargued.** The hypotheses of the
  Theorem are never satisfied (`jones75_noArc`, batch 190), so the step is not called false; but
  under the hypotheses of the setting it contradicts (O) … Any argument for the step would therefore
  itself finish the proof." The classification of J75.4 as a defective proof (an unargued step) is
  unchanged, so the count stays at **sixteen** defective proofs.
* New subsection **"Jones 1975 II: the planar core; `NoArcIndecHomPlane`; Theorem 1 of 1976
  (batch 190)"**, with the outcome (everything proved, nothing open) and:
  * **J75.6** (§9.2): report 189 §6.3, the repository's own hand proof: its shadow lemma and flow
    box hold only in the middle band, `R ∩ J = σ°` is unsupported, `N_o` had to be chosen after
    `P_{m₂}`; the trap was rebuilt in the column `3/8 ≤ X ≤ 5/8` with (Mon), and is formalized in
    that form. Not counted (not a published proof).
  * **J75.7** (p. 59, the Theorem, quoted): **proved** (`bing60_plane_uncond`), by a proof that is
    not Jones's; the printed steps it replaces are quoted (accessibility and (e); the choice of `η`;
    `[t_a, t_b]`; the domains `Dᵢ`; `[t_c, t_d]` and the fixed point; the final limit argument).
* `doc/notes/jones75.md` §5 records §9.2 and §9.3 (which steps of Jones's proof the route replaces).

## 4. Axioms

Every one of the 71 new theorems uses exactly `[propext, Classical.choice, Quot.sound]`; the list
with one line per theorem is `doc/batches/audits/axioms-batch190.txt`. In particular:

| theorem | axioms |
|---|---|
| `HPC.Hagopian.jones75_noArc` | `propext, Classical.choice, Quot.sound` |
| `HPC.Hagopian.hagopian76_theorem1` | `propext, Classical.choice, Quot.sound` |
| `HPC.Hagopian.jones75_contra` | `propext, Classical.choice, Quot.sound` |
| `HPC.Hagopian.trap_pass` | `propext, Classical.choice, Quot.sound` |
| `HPC.Hagopian.bing60_plane_uncond` | `propext, Classical.choice, Quot.sound` |
| `HPC.Hagopian.hagopian76_theorem2_uncond` | `propext, Classical.choice, Quot.sound` |

## 5. Dependency map of `Hagopian76Thm1`

No input is open.

```
hagopian76_theorem1 : Hagopian76Thm1                         (batch 190, Jones75B)
└─ hagopian76_theorem1_jones                                 (batch 188, Hagopian84D)
   ├─ hagopian76_theorem1_of_jones                           (batch 184, Hagopian84A)
   ├─ hagopian84_decomp : Hagopian84Decomp                   (batch 188, Hagopian84D; 1984 route,
   │                                                          batches 184–188)
   └─ jones75_noArc : NoArcIndecHomPlane                     (batch 190, Jones75B)
      ├─ jonesSetting_of_plane                               (batch 189, Jones75Arcs)
      ├─ JonesSetting.exists_line                            (batch 189, Jones75Line)
      ├─ exists_collar                                       (Hagopian76D, from H76Collar)    
      └─ jones75_contra                                      (batch 190, Jones75B)
         ├─ flow_box, scale_two, exists_late_thin_pass       (§3; shadow_pass ← Effros,
         │                                                    JonesSetting.orientation,
         │                                                    uniform_near_compact)
         ├─ JonesSetting.line_recurrent, mem_omegaLim_iff    (batch 189)
         ├─ exists_first_pass, IsPass.above_or_below         (§2)
         └─ jones75_final_aux                                (§6, C2–C5)
            ├─ trap_pass                                     (§5)
            │  ├─ trap_jordan ← jordan_curve_theorem, two_sides, isOpen_collar_image
            │  ├─ thinPass_arc, tarc_lowest, region_pass, region_cross, region_lemmaA (§4)
            │  └─ rect_domain_aux, rect_domain_low, seg_subset_rect_domain,
            │     exists_height_below                        (existing planar lemmas)
            └─ region_pass, region_thin_above, exists_ball_box
```

## 6. What Part E now gives the classification

Verified statements about homogeneous plane continua (all with axioms
`[propext, Classical.choice, Quot.sound]`; `M` is a compact connected subset of the plane, as a
subtype with `CompactSpace` and `ConnectedSpace`):

* **Hereditary indecomposability** (`hagopian76_theorem1 : Hagopian76Thm1`; Hagopian 1976,
  Theorem 1): every indecomposable homogeneous plane continuum is hereditarily indecomposable. No
  named hypotheses.
* **No arcs in the indecomposable case** (`jones75_noArc : NoArcIndecHomPlane`). No named
  hypotheses.
* **Bing 1960 for plane continua** (`bing60_plane_uncond`): a homogeneous plane continuum that
  contains an arc is a simple closed curve (`M ≃ₜ Circle`).
* **Non-separating case** (`hagopian76_theorem2_uncond`; Hagopian 1976, Theorem 2): a homogeneous
  plane continuum that does not separate the plane is hereditarily indecomposable.
* **Hagopian 1975** (`hagopian75_corollary_uncond`, `hagopian75_theorem2_uncond`): no nondegenerate
  subcontinuum of an indecomposable homogeneous plane continuum is hereditarily decomposable; the
  simple closed curve is the only homogeneous plane continuum with a nondegenerate hereditarily
  decomposable subcontinuum. `hagopian75_theorem1_of_noArc_uncond`: the irreducible-continuum form.
* **The decomposable case** (Jones 1955 Theorem 2 with Jones 1949 discharged,
  `HPC.Jones.jones55_theorem2'`, `jones55_two_domains'`, `jones55_elements_indecomposable'`,
  `jones55_three_domains'`, batch 154): a decomposable homogeneous plane continuum has a continuous
  decomposition into homogeneous, indecomposable, non-separating continua with quotient a simple
  closed curve; its complement has exactly two components; a homogeneous plane continuum whose
  complement has three components is indecomposable.
* **Jones 1949** (`HPC.Jones.jones49_theorem1`, `jones49_theorem2`): a nondegenerate homogeneous
  plane continuum that is aposyndetic, or has no weak cut point, is a simple closed curve.

Together: a homogeneous plane continuum is a simple closed curve, or is hereditarily
indecomposable, or is decomposable into homogeneous hereditarily indecomposable non-separating
continua — the last two clauses by `jones55_theorem2'` combined with
`hagopian76_theorem1`, which is not itself stated as one theorem here. Nothing on these routes is
open.

## 7. Delivery

* `axioms.txt`: **2550 lines** (`wc -l axioms.txt`), regenerated with
  `lake env lean Axioms.lean > axioms.txt`; no `sorryAx`.
* `doc/batches/audits/axioms-batch190.txt`: the 71 new lines.
* `doc/batches/batch190-files.tar.gz` and `doc/batches/batch190-MANIFEST.txt`: every file added,
  modified or moved in this run (from `git diff --name-status` against the run's initial commit),
  including this report.
* The uploads are in `doc/batches/COMMISSION-batch190.md` and
  `doc/batches/skeletons/Jones75B.lean`; nothing is left at the root.
