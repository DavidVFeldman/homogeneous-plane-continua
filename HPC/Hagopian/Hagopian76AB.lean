import HPC.Hagopian.H76E24

/-!
# Batch 183: Hagopian 1976, Theorem 1 — Bing's reasons for Cases 1–2; E2.4; the orientation;
# saturation

Commission 183 (`doc/batches/COMMISSION-batch183.md`; skeleton
`doc/batches/skeletons/Hagopian76AB.lean`). Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`),
pp. 348–349; Bing 1960 (`doc/sources/bing1960.pdf`), pp. 225–227. The skeleton is split under
`HPC/Hagopian/`:

| Item | Status | Lean name (file) |
| --- | --- | --- |
| §2 steps 1–2 (the pair `a`, `b`) | proved | `Thm1Setup.cap_point_o`, `Thm1Setup.near_strand_cross_o`, `e24_pair_between`, `e24_pair_below` (`H76E24.lean`) |
| §2 step 3 (`H`) | proved | `minimalAdmissible_restrict_of_lsc`, `minimalAdmissible_restrict` (`H76Restrict.lean`) |
| §2 steps 4–6 | named | `E24Claims`, `Thm1Setup.FarFrom` (`H76E24.lean`) |
| §2 `property2_violation` | proved, conditional | `property2_violation`, `E24Claims.false`, `e24_between_false`, `e24_below_far` (`H76E24.lean`); `Thm1Setup.exists_Rset_over` |
| §2 assembly | proved, conditional | `E24Data`, `E24Data.far`, `Case1WitnessE24`, `Case2WitnessE24`, `hagopian76_theorem1_of_cases3` (here) |
| §3 "between" | open | comment block below; report §3 |
| §4 Case 2 | open | comment block below; report §4 |
| §5 orientation | open (proposal fails as stated) | report §5 |
| §6.1 E2.1 | open | report §6.1 |
| §6.2 saturation | open | report §6.2 |
| §6.3 split by `Γ` | stated in the report, open | report §6.3 |
| Theorem 1 | conditional | `hagopian76_theorem1_of_cases3` (here) |

**Shapes.** The skeleton's items stated as `True` are rendered as follows (report §0): §2 by
`property2_violation` and the assembly here; the others are left open, commented out below with
their obstructions.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section B183

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **The data of E2.4** (commission 183 §2) for the point `y = yᵢ₋₁` and the `I`-strand `S_I`,
given the point `yᵢ` of the step: an extension `L` (minimal admissible) containing `Cl Cᵢ` and
`Cl Cᵢ₋₁` (E2.1, open), both crossing pieces with disjoint sides, and one of the two positions of
commission 183 §2 together with the claims of steps 3–6 (`E24Claims`) at the corresponding point:
* Bing's "`q` above `tu`": `Cᵢ₋₁` between `yᵢ` and `S_I` (`yᵢ` down from `Cᵢ₋₁`, `S_I` up from
  `Cᵢ₋₁`), claims at `yᵢ` for `Cl Cᵢ₋₁`;
* Bing's second case: `yᵢ₋₁` down from `Cᵢ` and `S_I` up from `Cᵢ`, claims at `yᵢ₋₁` for
  `Cl Cᵢ`. -/
structure E24Data (S : Thm1Setup M) (o : Bool) (yi y : M) (SI : Set Pt) where
  L : Set M
  dL : L → unitInterval
  hL : IsMinimalAdmissible L dL
  ci_cross : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ (S.comp yi)
  ci_sides : Disjoint (S.V.below (S.comp yi)) (S.V.above (S.comp yi))
  ci_L : closure (S.comp yi) ⊆ toPt L
  c_cross : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ (S.comp y)
  c_sides : Disjoint (S.V.below (S.comp y)) (S.V.above (S.comp y))
  c_L : closure (S.comp y) ⊆ toPt L
  pos : ((yi : Pt) ∈ S.dn o (S.comp y) ∧ SI ⊆ S.up o (S.comp y) ∧
      E24Claims S dL yi (closure (S.comp y))) ∨
    ((y : Pt) ∈ S.dn o (S.comp yi) ∧ SI ⊆ S.up o (S.comp yi) ∧
      E24Claims S dL y (closure (S.comp yi)))

/-- **E2.4** (p. 348: "The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise, a
subcontinuum of `L` would violate Property 2"): from the data of E2.4, with `yᵢ` down from `S_I`
and `f(yᵢ)` up from it, `ρ(yᵢ₋₁, Cl S_I) ≥ ε₃`. The first position is impossible
(`e24_between_false`); the second gives the bound (`e24_below_far`). -/
theorem E24Data.far {S : Thm1Setup M} {o : Bool} {yi y : M} {SI : Set Pt}
    (w : E24Data S o yi y SI) {u v : unitInterval} (hSI : S.IsBlockStrand u v SI)
    (hyi : S.GoodPoint yi) (hy : S.GoodPoint y) (hydn : (yi : Pt) ∈ S.dn o SI)
    (hfup : ((S.D.f yi : M) : Pt) ∈ S.up o SI) : S.ε₃ ≤ infDist (y : Pt) (closure SI) := by
  rcases w.pos with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact (e24_between_false S o w.hL hSI hyi hydn hfup w.c_cross w.c_sides h1 h2 w.c_L h3).elim
  · exact e24_below_far S o w.hL hSI hy.mem_mid w.ci_cross w.ci_sides h1 h2 w.ci_L h3

/-- **Case 1 witness with E2.4 reduced** (commission 183 §2): the fields of `Case1WitnessO` with
`far` replaced by the data of E2.4 and the facts on `yᵢ` it uses. -/
structure Case1WitnessE24 (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool) where
  yi : M
  y : M
  SI : Set Pt
  SJ : Set Pt
  good_yi : S.GoodPoint yi
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  yi_dn : (yi : Pt) ∈ S.dn o SI
  f_yi_up : ((S.D.f yi : M) : Pt) ∈ S.up o SI
  between : (y : Pt) ∈ S.up o SJ ∧ (y : Pt) ∈ S.dn o SI
  e24 : E24Data S o yi y SI
  band : ((S.D.f y : M) : Pt) ∈ S.up o SI ∨ ((S.D.f y : M) : Pt) ∈ S.dn o SJ

/-- A Case 1 witness with E2.4 reduced gives a Case 1 witness (`far` from `E24Data.far`). -/
def Case1WitnessE24.toO {S : Thm1Setup M} {x : ℕ → unitInterval} {i : ℕ} {o : Bool}
    (w : Case1WitnessE24 S x i o) : Case1WitnessO S x i o where
  y := w.y
  SI := w.SI
  SJ := w.SJ
  first := w.first
  strandI := w.strandI
  strandJ := w.strandJ
  between := w.between
  far := w.e24.far w.strandI w.good_yi w.first w.yi_dn w.f_yi_up
  band := w.band

/-- **Case 2 witness with (d) reduced** (commission 183 §4.4: "(d) as §2, with `π⁻¹(p₂)` in place of
`π⁻¹(p₄)`"): the fields of `Case2WitnessO` with `claim_d` replaced by the data of E2.4 when
`yᵢ₋₁` is up from `S_J`. -/
structure Case2WitnessE24 (S : Thm1Setup M) (x : ℕ → unitInterval) (i : ℕ) (o : Bool) where
  yi : M
  y : M
  SI : Set Pt
  SJ : Set Pt
  good_yi : S.GoodPoint yi
  first : S.GoodPoint y
  strandI : S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI
  strandJ : S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ
  yi_dn : (yi : Pt) ∈ S.dn o SI
  f_yi_up : ((S.D.f yi : M) : Pt) ∈ S.up o SI
  claim_a : (y : Pt) ∈ S.up o SJ → (y : Pt) ∈ S.dn o SI
  claim_b : (y : Pt) ∈ S.up o SJ → (y : Pt) ∈ S.dn o SI →
    ((S.D.f y : M) : Pt) ∉ S.dn o SJ → ((S.D.f y : M) : Pt) ∈ S.up o SI
  e24 : (y : Pt) ∈ S.up o SJ → Nonempty (E24Data S o yi y SI)
  claim_e : (y : Pt) ∈ S.dn o SJ → ((S.D.f y : M) : Pt) ∈ S.up o SJ

/-- A Case 2 witness with (d) reduced gives a Case 2 witness. -/
def Case2WitnessE24.toO {S : Thm1Setup M} {x : ℕ → unitInterval} {i : ℕ} {o : Bool}
    (w : Case2WitnessE24 S x i o) : Case2WitnessO S x i o where
  y := w.y
  SI := w.SI
  SJ := w.SJ
  first := w.first
  strandI := w.strandI
  strandJ := w.strandJ
  claim_a := w.claim_a
  claim_b := w.claim_b
  claim_d := fun hup hlt =>
    let ⟨d⟩ := w.e24 hup
    absurd (d.far w.strandI w.good_yi w.first w.yi_dn w.f_yi_up) (not_le.2 hlt)
  claim_e := w.claim_e

/-- **Named `Prop`: the claims of Case 1 with E2.4 reduced** (`Case1Claims'` with
`Case1WitnessE24` in place of `Case1WitnessO`). -/
def Case1ClaimsE24 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Case1Config S x i → ∀ o yi SI SJ, StepCase S x i o yi SI SJ →
    Nonempty (Case1WitnessE24 S x i o)

/-- **Named `Prop`: the claims of Case 2 with (d) reduced.** -/
def Case2ClaimsE24 (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Case2Config S x i → ∀ o yi SI SJ, StepCase S x i o yi SI SJ →
    Nonempty (Case2WitnessE24 S x i o)

theorem Case1ClaimsE24.claims' {S : Thm1Setup M} {x : ℕ → unitInterval} {m : ℕ}
    (h : Case1ClaimsE24 S x m) : Case1Claims' S x m := fun i hi3 him hc o yi SI SJ hs =>
  let ⟨w⟩ := h i hi3 him hc o yi SI SJ hs
  ⟨w.toO⟩

theorem Case2ClaimsE24.claims' {S : Thm1Setup M} {x : ℕ → unitInterval} {m : ℕ}
    (h : Case2ClaimsE24 S x m) : Case2Claims' S x m := fun i hi3 him hc o yi SI SJ hs =>
  let ⟨w⟩ := h i hi3 him hc o yi SI SJ hs
  ⟨w.toO⟩

end B183

/-- **Theorem 1 (p. 345), the strongest conditional form of batch 183**: as
`hagopian76_theorem1_of_cases2`, with the fields `far` (Case 1) and `claim_d` (Case 2) of the
witnesses replaced by the data of E2.4 (`E24Data`: the extension `L`, the positions of `Cᵢ`,
`Cᵢ₋₁`, and the claims `E24Claims` of steps 3–6), so that E2.4 itself is proved
(`E24Data.far`). Non-vacuity notes: report §2.6. -/
theorem hagopian76_theorem1_of_cases3
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hcases : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsTightBlocks x m → StepFrame S x m ∧ LastStepClaims S x ∧ BlockLayersMeetSides3 S x m ∧
        Case1ClaimsE24 S x m ∧ Case2ClaimsE24 S x m) :
    Hagopian76Thm1 :=
  hagopian76_theorem1_of_cases2 hICC fun M _ _ S x m hx => by
    obtain ⟨hf, hl, hs, h1, h2⟩ := hcases M S x m hx
    exact ⟨hf, hl, hs, h1.claims', h2.claims'⟩

/-! ## Open items (commission 183; obstructions in `OPEN.md`, batch 183, and the report)

**OPEN (§3, `case1_between_bing`).** "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see
that `yᵢ₋₁` is between `d⁻¹[I]` and `d⁻¹[J]`" (p. 348); Bing p. 226: "It follows from the Jordan
curve theorem that `q` lies between …". The two sides, at the exit point `u ∉ F`, of the part `σ` of
the side segment between the points where `Cl S_J` and `Cl S_I` meet it lie in different components
of the complement of `A ∪ σ`, `A = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` (report §3, plane topology, not formalized).
Open: that the outer component misses `π⁻¹[D]` off `σ`. It can fail if `A` has no points outside `D`
near the end of a strand (configuration in the report §3).

theorem case1_between_bing : True := by
  sorry

**OPEN (§4, `case2_bing_a`, `case2_curve`, `case2_gap_side`).** (a): as §3 at the right side
segment. (b), (e): Bing's `J` is a simple closed curve, and the side of `h(q)` follows from the
parity of crossings along the vertical through `a₃`, whatever route the gap arc takes (report §4).
For the continuum `P` no parity argument is available; the Janiszewski form separates the two sides
of `Q`, not the two sides of `S_I` (report §4.2). §4.3: the route of `Γ` around an end of `π[E]` is
not excluded by anything proved, but in Bing's setting it does not break the argument (report §4.3).

theorem case2_bing_a : True := by
  sorry
theorem case2_curve : True := by
  sorry
theorem case2_gap_side : True := by
  sorry

**OPEN (§5, `property4_symm`).** The proposal fails as stated: `f(yᵢ)` need not lie in `Mid` (the
position clause gives only abscissae in `(3/8, 5/8)`, `Mid` asks for `[1/2 − 2/n, 1/2 + 2/n]`), and
the cap from `f(yᵢ)` uses `hε₃S` and `hε₃O`, stated for `Mid`. Also, that `Cl` of the component of
`f(yᵢ)` is essential to `h₁[R(E)]` does not follow from the essentiality of `Cl Cᵢ` to `h[R(E)]`
(report §5).

theorem property4_symm : True := by
  sorry

**OPEN (§6.1, `exists_first_crossing`; §6.2, `half_components_cross`, `chunk_points`; §6.3,
`gap_side_split`; 2e, `innerComponentsCross_hagopian`).** As batch 182 (report §6).

theorem exists_first_crossing : True := by
  sorry
theorem half_components_cross : True := by
  sorry
theorem chunk_points : True := by
  sorry
theorem gap_side_split : True := by
  sorry
-- `innerComponentsCross_hagopian`: proved in batch 185, `Hagopian76AC.lean`.

**OPEN (`hagopian76_theorem1_final`).** The unconditional Theorem 1; the strongest conditional form is
`hagopian76_theorem1_of_cases3`.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
