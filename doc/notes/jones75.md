# Jones 1975 — reconnaissance (batch 186, §6)

Source: F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math. 1 (1975),
57–61 (`doc/sources/jones1975.pdf`; the sixth PDF page is blank). Transcribed from page images
rendered at 200 dpi. Sections 1–3 are the reconnaissance of batch 186; section 4 (batch 189) records
the corrections of commission 189 §7.5 and the route of batches 189 onward, which is formalized in
`HPC/Jones/Jones75*.lean`.

Purpose in the project: the named `Prop` `NoArcIndecHomPlane` (`HPC/Hagopian/Hagopian84A.lean`):
no indecomposable homogeneous plane continuum contains an arc. Jones's Theorem gives it (its
decomposable case is Jones 1955, already in the repository as `HPC/Jones/Jones55*.lean`).

## 1. Transcription

[Quotation moved to doc/sources/transcriptions/jones75.md, §doc/notes/jones75.md, 1. Transcription (pp. 57–61); batch 204.]

References: [1] R H Bing, *A simple closed curve is the only homogeneous bounded plane continuum
that contains an arc*, Canad. J. Math. 12 (1960), 209–230. [2] F. B. Jones, *On a certain type of
homogeneous plane continuum*, Proc. Amer. Math. Soc. 6 (1955), 735–740. [3] G. S. Ungar, *On all
kinds of homogeneous spaces*, Trans. Amer. Math. Soc. (to appear).

Typographical points (as printed): "[(z+1,0), zᵢ₊₁]" should read "[(i+1,0), zᵢ₊₁]"; "the other it
also between" reads "the other is also between"; "a limit point [t₆,t_∞]" reads "a limit point of
[t₆,t_∞]"; "t_{ε₁}, t_{ε₂}" are the points t_e (or t_f) for ε = εₙ; "h(t_e′) = t_g" in the scan
has a stray prime.

## 2. Map to the repository

| Jones 1975 | Repository | Status |
| --- | --- | --- |
| Effros corollary (p. 57) | `effros_homogeneous` (`HPC/Effros/Effros.lean`), and `effros_homogeneous_set` | proved (strict `<` for `δ`; Jones's "≤ δ" on p. 60 follows by halving) |
| (a) hereditary unicoherence | `hagopian75_lemma1_hu` (unconditional), `hagopian75_lemma1` | proved |
| (b) atriodicity | `hagopian75_lemma1` (via `mooreTriodStatement`) | proved |
| (c) union of two meeting arcs is an arc | — | not in the repository; follows from (a), (b): `A ∪ B` is a hereditarily unicoherent atriodic arc-like union; needs "an atriodic, hereditarily unicoherent union of two arcs is an arc" |
| (d) maximal ray `T`, one-to-one image of `[0, ∞)`; points of `ab` limit points of `T − ab` | — | not in the repository. Needs: arcs in `M` as `TArc`; the union of a chain of arcs with a common end; (c); Effros; the triod argument for `T̄ − T` (via (b)) |
| (e) accessible arcs accessible from one side only | `IsAccessibleFrom` (`H76BDefs.lean`); collars `exists_collar` (`Hagopian76D.lean`, the two-sided collar replaces "a homeomorphism of the plane E onto itself which takes ab onto the interval [0,1]"); `exists_accessible_above` (`H76AboveAcc.lean`) | definitions and collars proved; (e) itself not formalized. "w is a limit point of every composant of M" is the density of composants (in the repository for the 1975/1976 work) |
| (f) | — | not in the repository. Pure metric argument plus Effros and the arcs `abc`; no plane topology except "D open, `p ∉ D̄`". |
| "If M is decomposable then M is a simple closed curve [2]" | `jones55_theorem2` etc. (`HPC/Jones/Jones55T2.lean`, conditional on `Jones49Thm1`) | not needed: `NoArcIndecHomPlane` assumes indecomposability |
| Theorem, indecomposable case | `NoArcIndecHomPlane` (named `Prop`, `Hagopian84A.lean`) | proved in batch 190 (`jones75_noArc`, `HPC/Jones/Jones75B.lean`; see §5) |

**Plane topology needed, step by step.**

1. *Accessibility of the ray `T`* ("let us assume that T is accessible from the complement of M"):
   needs an accessible point of `M` on an arc of `M`, and that the accessible arc can be taken as a
   ray. The repository has `IsAccessibleFrom` and `exists_accessible_above` (accessible points in
   collar windows), but not "some arc of `M` contains an accessible point that is not an end
   point". This is an unargued sentence; a later batch must decide whether it follows from (d), (e)
   and the density of accessible points in the boundary of a complementary domain.
2. *Straightening* ("[t₀,t₅] of T lies on the x-axis … accessible from below"): the repository's
   collars (`IsCollar`, `exists_collar`, `exists_collar_adapted`) give coordinates
   `F : [0,1] × [−1,1] → Pt` around an arc, which is what the proof uses; a global plane
   homeomorphism is not needed. Lines `x = n` become the vertical segments `F({n/5} × [−1,1])`.
3. *Choice of η* (from (f)): metric only, inside the collar.
4. *Irreducible subarc `[t_a,t_b]`* between `x = 5` and `x = 0` below `y = 1/η`: compactness of arcs
   and (d) ("every point of [0,5] is a limit point of [t₆,t_∞]"). The order of `t_a`, `t_b`
   ("appeal to the Jordan curve theorem") needs `jordan_curve_theorem` (`Jones55T2A.lean`) for the
   closed curve formed from two arcs of `T` and collar segments; unargued in detail.
5. *Simple domains `Dᵢ`*: each bounded by a simple closed curve made of four arcs; needs the Jordan
   curve theorem (`jordan_curve_theorem`) and, for "between" statements, the side of the collar
   (`plane_schoenflies`, `plane_schoenflies₂` are available if a disk is wanted).
6. *ε and δ*: metric and Effros (`effros_homogeneous`).
7. *The fixed point `t_f`*: "h take [t₀,t_d] onto (approximately) [t_d,t₀]. So there is a fixed
   point" — the intermediate value theorem along the ray `T` (both arcs lie in `T` by (d)/(c), since
   `h[T]` is a maximal ray from `t_d`, which meets `T`), not a plane fixed-point theorem. Unargued:
   that `h[t₀,t_d] ⊆ T` and reverses orientation.
8. *t_f ∉ D̄₁ ∪ D̄₂ ∪ D̄₃, the points t_e, t_g in D₂, and the limit argument*: plane separation by
   the curves of step 5; the final "it is easy to see that p ∉ D̄₂ and property (f) is violated" is
   unargued.

## 3. Skeleton proposal (for a later batch; not formalized)

File `HPC/Jones/Jones75.lean`, importing `HPC.Effros.Effros`, `HPC.Hagopian.Hagopian75`,
`HPC.Hagopian.Hagopian76D`, `HPC.Jones.Jones55T2A`. All statements for `M : Set Pt` compact,
connected, homogeneous, indecomposable.

```lean
-- (c)
theorem jones75_c (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {A B : Set M}
    {a b a' b' : M} (hA : TArc a b A) (hB : TArc a' b' B) (hAB : (A ∩ B).Nonempty) :
    ∃ p q, TArc p q (A ∪ B)

-- (d), the ray: a continuous injection of `[0, ∞)` onto the union of the arcs from `a` containing `ab`
theorem jones75_d_ray … : ∃ γ : ℝ≥0 → M, Continuous γ ∧ Function.Injective γ ∧ range γ = T a A
theorem jones75_d_limit … : ∀ x ∈ A, x ∈ closure (T a A \ A)

-- (e), in collar coordinates `F` around an accessible arc
theorem jones75_e … : (accessible from below at one interior point) →
    ∀ t ∈ Ioo 0 1, (accessible from below at γ t) ∧ ¬ (accessible from above at γ t)

-- (f)
theorem jones75_f (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) (p : M) {D : Set Pt}
    (hD : IsOpen D) (hpD : (p : Pt) ∉ closure D) :
    ∃ ε > 0, ∀ a b c (abc : Set M) (ab bc : Set M), (arc abc with subarcs ab, bc) →
      (a : Pt) ∈ D → (c : Pt) ∈ D → ¬ (p ∈ thickening ε ab ∧ bc ⊆ thickening ε ab)

-- the Theorem, indecomposable case
theorem jones75_noArc : NoArcIndecHomPlane
```

Suggested order: (f) (metric only), (c), (d), then the accessibility sentence of step 1 (decide
first whether it is an unargued gap), (e), and the Theorem with the domains `Dᵢ` built in collar
coordinates. Candidate ledger entries: the accessibility assumption of step 1; "So there is a fixed
point `t_f`"; the final sentence "it is easy to see that p ∉ D̄₂ and property (f) is violated".

## 4. Corrections and the route (batch 189)

**Corrections (commission 189 §7.5).** The paper occupies pp. 57–61; the sixth page of the PDF is
blank (the batch-186 header said 57–62). The Effros corollary is printed with
"`d(h(p), p) ≤ ε`", not "`< ε`" (fixed in §1). Neither changes any use: the repository's
`effros_homogeneous` has the strict inequality.

**What is wrong in the paper (ledger section "Jones 1975", J75.1–J75.4).** The proof of (f) is
defective: its last inference is a non sequitur, and the dyadic solenoid satisfies every property
the proof uses while (f) fails in it. The second half of (d) has an orientation gap and a triod
paragraph that does not give a contradiction as printed. The Theorem's "`h` reverses `T`" is unargued;
under the hypotheses of the setting it contradicts (O) below, so any argument for it would itself
finish the proof (wording of commission 190 §9.1; batch 189 called it false for small `ε`). (c) is true, from (a) and (b).

**The route (commission 189 §§2–6).** All of §2–§5 is formalized and proved, for a compact metric
space `Y` with the structure `JonesSetting Y` (homogeneous, hereditarily unicoherent, atriodic,
containing an arc); `jonesSetting_of_plane` gives it for a homogeneous indecomposable plane
continuum with an arc.

| step | statement | file |
| --- | --- | --- |
| (c) | `JonesSetting.union_arc`, `JonesSetting.nested` | `Jones75Arcs.lean` |
| interior points | `JonesSetting.exists_arc_through` | `Jones75Arcs.lean` |
| lines | `arcComp`, `IsLine`, `JonesSetting.exists_line` (every arc component is a line `ℝ ↪ Y`) | `Jones75Line.lean` |
| arcs of lines | `JonesSetting.line_arc`, `JonesSetting.homeo_on_line` | `Jones75Rev.lean` |
| (R0), (R), (O) | `JonesSetting.no_reversal_arc`, `exists_no_reversal`, `orientation` | `Jones75Rev.lean` |
| recurrence | `omegaLim_saturated`, `line_recurrent`, `jones75_d` | `Jones75A.lean` |
| (L) | `JonesSetting.no_backtrack`, `no_backtrack_in_collar` | `Jones75L.lean` |

(R) and (O) replace (f): no `ε₀`-homeomorphism fixing a point reverses the line through it, and an
`ε₀`-homeomorphism carrying a point of a line into that line is increasing on it. Recurrence (every
line lies in its own forward and backward limit sets) replaces the second half of (d), by Jones's
own `½ d(a, T̄ − T)` device. (L) replaces the choice of `η`.

**What remains** is the planar core, `jones75_noArc : NoArcIndecHomPlane`. The hand proof by the
Poincaré–Bendixson route chosen for the next batches, with the repository material for each step
and a skeleton, is in `doc/batches/REPORT-batch189.md` §6.

## 5. The planar core (batch 190)

**`jones75_noArc : NoArcIndecHomPlane` is proved** (`HPC/Jones/Jones75B.lean`), and with it
`hagopian76_theorem1 : Hagopian76Thm1`, Bing 1960 for plane continua (`bing60_plane_uncond`) and
Hagopian 1976 Theorem 2 (`hagopian76_theorem2_uncond`), unconditionally. The route is that of
commission 190 §2–§6.

**Report 189 §6.3 had an error (commission 190 §0; ledger J75.6).** Its shadow lemma and flow box
were stated for the whole box `F([¼, ¾] × [−η, η])`, but they hold only in the middle band
`X ∈ [¼ + κ, ¾ − κ] = [9/32, 23/32]` (`κ = 1/32`): near an edge, backtracking up to `2κ` is allowed,
so the sup/inf construction can produce a U-turn through one edge instead of a pass. "Every point of
`ℓ` in `R` lies on a pass" and "`R ∩ J = σ°`" were therefore unsupported, and `N_o` had to be
chosen after `P_{m₂}`. The trap was rebuilt by an independent check in the column `3/8 ≤ X ≤ 5/8`,
with the property (Mon) of passes (the first collar coordinate never falls back by `2κ`); it needs
neither a cross-cut lemma nor `R ∩ J = σ°`. That repaired proof is the one formalized.

| step (commission 190) | statement | file |
| --- | --- | --- |
| §2 passes, (P1)–(P4) | `IsPass`, `PassMon`, `IsPass.disjoint`, `IsPass.finite`, `exists_first_pass`, `isPass_base`, `IsPass.above_or_below`; the flip `flipC` | `Jones75Pass.lean` |
| §3 shadow lemma, (FB), scale 2, late thin passes | `shadow_pass`, `flow_box`, `FBProp.passMon`, `scale_two`, `exists_late_thin_pass` | `Jones75Shadow.lean` |
| §7 N1, N2, N4 | `thinPass_arc`, `tarc_lowest`, `IsPass.lc_left_mem_closure` | `Jones75Region.lean` |
| §4 (R1)–(R3), §5 Lemma A | `region_pass`, `region_thin_above`, `region_cross`, `region_lemmaA` (with `rect_domain_aux`, `rect_domain_low`, `seg_subset_rect_domain`, `rect_domain_crosscut`) | `Jones75Region.lean` |
| §5 Steps 2–5, N3 | `trap_jordan`, `two_sides` (with `jordan_curve_theorem`) | `Jones75Trap.lean` |
| §5 Step 6, the trap | `trap_pass` | `Jones75Trap.lean` |
| §6 C1–C5, the Theorem | `jones75_final_aux`, `jones75_contra`, `jones75_noArc`, `hagopian76_theorem1` | `Jones75B.lean` |

**Which steps of Jones's Theorem the route replaces (commission 190 §9.3).**
* *Accessibility* of the ray `T` ("let us assume that T is accessible from the complement of M")
  and *property (e)*: not used. The collar `F` of an arc of a line (`exists_collar`) is all the
  plane structure needed near the arc.
* *The choice of `η`* (from (f)): replaced by the flow box (`flow_box`): in the middle band every
  point of the line in a thin box lies on a pass with (Mon).
* *`[t_a, t_b]`* (the first arc from `x = 5` to `x = 0` low down): replaced by the first thin pass
  after `¾` (`exists_first_pass`), above or below the base arc (`IsPass.above_or_below`; the lower
  case by the flipped collar).
* *`[t_c, t_d]`* and *the fixed point `t_f`*: no fixed point. The trap (`trap_pass`) shows that no
  pass after `P_m` enters the low strip of the region of `P_m`, using the Jordan curve
  `σ ∪ ℓ[½, t_m]` and the two sides `W_L ∋ T_L`, `W_R ∋ T_R`.
* *The domains `Dᵢ`*: replaced by the single region `R_m = F(D_m)` under a thin pass
  (`rect_domain_aux`), with the lowest points `w_m(c)` on the verticals `X = c` (`tarc_lowest`).
* *The final limit argument* ("By appropriately selecting a sequence of values ε₁, ε₂, …"):
  replaced by recurrence (`line_recurrent`): the line comes back near `o = ℓ(½)` after the first
  thin passes above and below the base arc, and the trap for each of them excludes both sides.
