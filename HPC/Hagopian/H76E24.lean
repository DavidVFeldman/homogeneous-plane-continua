import HPC.Hagopian.H76Restrict

/-!
# Batch 183, §2: E2.4 by Bing's arc `ab`

Commission 183 §2. Hagopian p. 348: "The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`;
for otherwise, a subcontinuum of `L` would violate Property 2." Bing p. 227: "If `q` were above
`tu`, we would take `p = a` and let `b` be a point of `vw` between `p` and `x₂ᵢ₋₁x₂ᵢ`. If `q` were
below `tu` and `ρ(q, x₂ᵢ₋₁x₂ᵢ) < ε₄`, we would take `q` to be `b` and `a` to be a point of `tu`
between `q` and `x₂ᵢ₋₁x₂ᵢ`. Since the existence of such an arc `ab` violates the definition of
`ε₄`, we suppose that `ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄`."

* Steps 1–2 (the pair `a`, `b`): `Thm1Setup.cap_point_o` (the cap lemma returning the point of
  `Cl W` on the segment), `Thm1Setup.near_strand_cross_o`, `e24_pair_between` (Bing: "`q` above
  `tu`", `a = yᵢ`), `e24_pair_below` (Bing's second case, `b = yᵢ₋₁`).
* Step 3 (`H`): `minimalAdmissible_restrict` (`H76Restrict.lean`).
* Step 6: `Thm1Setup.exists_Rset_over` (a point of `R(E)` over `F(r, 0)`, e.g. over `p₄`,
  `r = 15/22`, or `p₂`, `r = 7/22`); `Thm1Setup.FarFrom` (named: `H` does not come within `ε₂` of
  `π⁻¹F(r, 0)`); `property2_violation`.
* Assembly: the named `Prop` `E24Claims` (steps 4–6 for the specific pair) and
  `e24_between_false`, `e24_below_far` (the field `far` of `Case1WitnessO`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section E24

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## Steps 1–2: the pair `a`, `b` -/

/-- **The cap point, oriented** (the cap lemma `cross_strand_near_o`, returning the point): `a ∈ Mid`
down from a crossing piece `W`, `b` up from it, `ρ(a, b) < ε₃`; then the segment `[a, b]` meets
`Cl W` at a point within `ε₃` of `a`. -/
theorem Thm1Setup.cap_point_o (S : Thm1Setup M) (o : Bool) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.dn o W) (hbW : b ∈ S.up o W) (hab : dist a b < S.ε₃) :
    ∃ c ∈ closure W, dist a c < S.ε₃ := by
  cases o
  · obtain ⟨c, hc, hcW⟩ := VFrame.exists_mem_closure_of_preconnected hWs
      (convex_segment a b).isPreconnected (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) haW
      hbW (S.segment_misses_closure_above hW hWs ha hab)
    exact ⟨c, hcW, (VFrame.dist_le_of_mem_segment hc).trans_lt hab⟩
  · obtain ⟨c, hc, hcW⟩ := VFrame.exists_mem_closure_of_preconnected hWs
      (convex_segment a b).isPreconnected (right_mem_segment ℝ a b) (left_mem_segment ℝ a b) hbW
      haW (S.segment_misses_closure_above hW hWs ha hab)
    exact ⟨c, hcW, (VFrame.dist_le_of_mem_segment hc).trans_lt hab⟩

/-- **Crossing on the way to a near strand**: `a ∈ Mid` down from a crossing piece `W`, a nonempty
set `X` up from `W`, `ρ(a, Cl X) < ε₃`; then some point of `Cl W` is within `ε₃` of `a`. -/
theorem Thm1Setup.near_strand_cross_o (S : Thm1Setup M) (o : Bool) {W X : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.dn o W) (hX : X.Nonempty) (hXW : X ⊆ S.up o W)
    (hnear : infDist a (closure X) < S.ε₃) : ∃ c ∈ closure W, dist a c < S.ε₃ := by
  rw [infDist_closure] at hnear
  obtain ⟨w, hwX, hw⟩ := (infDist_lt_iff hX).1 hnear
  exact S.cap_point_o o hW hWs ha haW (hXW hwX) hw

/-- A piece of the low frame is nonempty. -/
theorem Thm1Setup.piece_nonempty (S : Thm1Setup M) {W : Set Pt} (hW : S.V.IsPiece W) :
    W.Nonempty := by
  obtain ⟨_, ⟨P, hP, -⟩⟩ := hW.hts_nonempty
  exact closure_nonempty_iff.1 ⟨P, hP⟩

/-- **§2 step 1** (Bing: "If `q` were above `tu`, we would take `p = a` and let `b` be a point of
`vw` between `p` and `x₂ᵢ₋₁x₂ᵢ`"). `yᵢ` is a good point down from the `I`-strand `S_I` with
`f(yᵢ)` up from it, and `Cᵢ₋₁` (here `C'`) lies between: `yᵢ` down from `C'`, `S_I` up from `C'`.
Then some point `b ∈ Cl Cᵢ₋₁` is within `ε₃` of `a = yᵢ`. -/
theorem e24_pair_between (S : Thm1Setup M) (o : Bool) {u v : unitInterval} {SI C' : Set Pt}
    (hSI : S.IsBlockStrand u v SI) {yi : M} (hy : S.GoodPoint yi) (hydn : (yi : Pt) ∈ S.dn o SI)
    (hfup : ((S.D.f yi : M) : Pt) ∈ S.up o SI)
    (hC' : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ C')
    (hC's : Disjoint (S.V.below C') (S.V.above C')) (hyC' : (yi : Pt) ∈ S.dn o C')
    (hSIC' : SI ⊆ S.up o C') : ∃ b ∈ closure C', dist (yi : Pt) b < S.ε₃ :=
  S.near_strand_cross_o o hC' hC's hy.mem_mid hyC' (S.piece_nonempty hSI.piece) hSIC'
    (cross_strand_near_o S o hSI.crossing hSI.piece.sides_disjoint hy.mem_mid hydn hfup
      (S.dist_f_lt yi))

/-- **§2 step 2** (Bing: "If `q` were below `tu` and `ρ(q, x₂ᵢ₋₁x₂ᵢ) < ε₄`, we would take `q` to
be `b` and `a` to be a point of `tu` between `q` and `x₂ᵢ₋₁x₂ᵢ`"). `yᵢ₋₁` (here `y'`) a point of
`Mid` down from `Cᵢ`, the `I`-strand `S_I` up from `Cᵢ`, and `ρ(yᵢ₋₁, Cl S_I) < ε₃`. Then some
point `a ∈ Cl Cᵢ` is within `ε₃` of `b = yᵢ₋₁`. -/
theorem e24_pair_below (S : Thm1Setup M) (o : Bool) {u v : unitInterval} {SI Ci : Set Pt}
    (hSI : S.IsBlockStrand u v SI) {y' : M} (hy' : (y' : Pt) ∈ midSet M S.π S.F S.D' S.n)
    (hCi : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ Ci)
    (hCis : Disjoint (S.V.below Ci) (S.V.above Ci)) (hy'Ci : (y' : Pt) ∈ S.dn o Ci)
    (hSICi : SI ⊆ S.up o Ci) (hnear : infDist (y' : Pt) (closure SI) < S.ε₃) :
    ∃ a ∈ closure Ci, dist (y' : Pt) a < S.ε₃ :=
  S.near_strand_cross_o o hCi hCis hy' hy'Ci (S.piece_nonempty hSI.piece) hSICi hnear

/-! ## Step 6: a point of `R(E)` over `F(r, 0)`, and the violation of Property 2 -/

/-- **A point of `R(E)` over `F(r, 0)`** for `0 ≤ r ≤ 1` (over `p₄`: `r = 15/22`; over `p₂`:
`r = 7/22`): a point of the layer `k⁻¹(r)` of `E`. -/
theorem Thm1Setup.exists_Rset_over (S : Thm1Setup M) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ∃ z ∈ Rset S.k, S.π (z : Pt) = S.F (r, 0) := by
  obtain ⟨x, hx⟩ := S.hE.2.1.2.1 ⟨r, hr⟩
  refine ⟨x, subset_Rset S.hE x.2, ?_⟩
  have h1 := S.hγπ ⟨r, hr⟩ ((x : M) : Pt) ⟨x, ⟨x, hx, rfl⟩, rfl⟩
  have h2 := S.hF.2.1 ⟨r, hr⟩
  rw [h1, ← h2]

/-- **Named `Prop`: `H` does not come within `ε₂` of `π⁻¹F(r, 0)`** (Hagopian p. 348, T17: "the
continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`", `r = 15/22`; Case 2 with `p₂`, `r = 7/22`,
after Bing's `a₂`). -/
def Thm1Setup.FarFrom (S : Thm1Setup M) (r : ℝ) (H : Set M) : Prop :=
  ∀ q ∈ H, ∀ z : M, S.π (z : Pt) = S.F (r, 0) → S.ε₂ ≤ dist z q

/-- Every parameter of `[s, t]` is `restrictParam s t _ τ` for some `τ`. -/
theorem exists_restrictParam_eq {s t : unitInterval} (hst : s < t) {w : unitInterval}
    (hw : w ∈ Icc s t) : ∃ τ, restrictParam s t hst.le τ = w := by
  have hts : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 hst
  have h1 : (s : ℝ) ≤ w := hw.1
  have h2 : (w : ℝ) ≤ t := hw.2
  refine ⟨⟨((w : ℝ) - s) / (t - s), div_nonneg (by linarith) hts.le,
    (div_le_one hts).2 (by linarith)⟩, Subtype.ext ?_⟩
  show (s : ℝ) + ((w : ℝ) - s) / (t - s) * (t - s) = w
  rw [div_mul_cancel₀ _ hts.ne']
  ring

/-- **§2, `property2_violation`** (the strongest conditional form; Hagopian p. 348: "for otherwise,
a subcontinuum of `L` would violate Property 2"). Let `(L, d)` be minimal admissible in `M`,
`s < t`, `a ∈ d⁻¹(s)`, `b ∈ d⁻¹(t)` with `ρ(a, b) < ε₃`, and `H = d⁻¹[[s, t]]` (step 3). If
* `h⁻¹[H]` is essential to `R(E)` (step 5),
* some layer `d⁻¹(w)`, `s ≤ w ≤ t`, is farther than `ε₂` from one of the end sets of `H` (step 4),
* `H` does not come within `ε₂` of `π⁻¹F(r, 0)` for some `0 ≤ r ≤ 1` (step 6, `FarFrom`),

then Property 2 (`S.hP2`, for `h`) is violated. -/
theorem property2_violation (S : Thm1Setup M) {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {s t : unitInterval} (hst : s < t) {a b : M}
    (ha : a ∈ layer d s) (hb : b ∈ layer d t) (hab : dist a b < S.ε₃)
    (hess : IsEssential S.k (S.D.h ⁻¹' layerSet d (Icc s t)))
    (hfar : ∃ w ∈ Icc s t, (∀ x ∈ layer d s, ∀ z ∈ layer d w, S.ε₂ < dist x z) ∨
      (∀ x ∈ layer d t, ∀ z ∈ layer d w, S.ε₂ < dist x z))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hP : S.FarFrom r (layerSet d (Icc s t))) : False := by
  obtain ⟨e, he, hlay⟩ := minimalAdmissible_restrict S.hX S.hi hL hst
  have hsm : ∀ v, dist v (S.D.h v) < S.ε₃ := fun v => by
    have := S.D.h_small v
    rw [dist_comm]; linarith [S.hε₃]
  have h0 : layer e 0 = layer d s := by rw [hlay, restrictParam_zero]
  have h1 : layer e 1 = layer d t := by rw [hlay, restrictParam_one]
  obtain ⟨z, hzR, hzπ⟩ := S.exists_Rset_over hr
  obtain ⟨w, hw, hfar⟩ := hfar
  obtain ⟨τ, hτ⟩ := exists_restrictParam_eq hst hw
  have hτl : layer e τ = layer d w := by rw [hlay, hτ]
  have hconc : ∃ q ∈ layerSet d (Icc s t), dist z q < S.ε₂ := by
    rcases hfar with hf | hf
    · exact S.hP2 S.D.h hsm _ hess e he ⟨a, h0 ▸ ha, b, h1 ▸ hb, hab⟩
        ⟨τ, fun x hx y hy => hf x (h0 ▸ hx) y (hτl ▸ hy)⟩ z hzR
    · have he' := he.symm_comp
      have h0' : layer (unitInterval.symm ∘ e) 0 = layer d t := by
        rw [layer_symm_comp, unitInterval.symm_zero, h1]
      have h1' : layer (unitInterval.symm ∘ e) 1 = layer d s := by
        rw [layer_symm_comp, unitInterval.symm_one, h0]
      have hτ' : layer (unitInterval.symm ∘ e) (unitInterval.symm τ) = layer d w := by
        rw [layer_symm_comp, unitInterval.symm_symm, hτl]
      exact S.hP2 S.D.h hsm _ hess _ he' ⟨b, h0' ▸ hb, a, h1' ▸ ha, by rw [dist_comm]; exact hab⟩
        ⟨unitInterval.symm τ, fun x hx y hy => hf x (h0' ▸ hx) y (hτ' ▸ hy)⟩ z hzR
  obtain ⟨q, hq, hzq⟩ := hconc
  exact absurd (hP q hq z hzπ) (not_le.2 hzq)

/-! ## Assembly: the field `far` -/

/-- **Named `Prop`: steps 3–6 of commission 183 §2 for the pair at `y₀`.** For every point `b` of
`B ∩ L` within `ε₃` of `y₀ ∈ L`: `y₀` and `b` lie in distinct layers `d⁻¹(s)`, `d⁻¹(t)` of `L`
(either order), and `H = d⁻¹[[s, t]]` satisfies
* (step 5) `h⁻¹[H]` is essential to `R(E)`;
* (step 4) some layer of `H` is farther than `ε₂` from an end set of `H`;
* (step 6) `H` does not come within `ε₂` of `π⁻¹F(r, 0)` for some `r ∈ [0, 1]` (`r = 15/22` in
  Case 1, `r = 7/22` in Case 2).

Used with `y₀ = yᵢ`, `B = Cl Cᵢ₋₁` (Bing: "`q` above `tu`") and with `y₀ = yᵢ₋₁`, `B = Cl Cᵢ`
(Bing's second case). Non-vacuity note: report §2.6. -/
def E24Claims (S : Thm1Setup M) {L : Set M} (d : L → unitInterval) (y₀ : M) (B : Set Pt) : Prop :=
  ∀ b : M, (b : Pt) ∈ B → b ∈ L → dist y₀ b < S.ε₃ →
    ∃ s t : unitInterval, s < t ∧
      ((y₀ ∈ layer d s ∧ b ∈ layer d t) ∨ (b ∈ layer d s ∧ y₀ ∈ layer d t)) ∧
      IsEssential S.k (S.D.h ⁻¹' layerSet d (Icc s t)) ∧
      (∃ w ∈ Icc s t, (∀ x ∈ layer d s, ∀ z ∈ layer d w, S.ε₂ < dist x z) ∨
        (∀ x ∈ layer d t, ∀ z ∈ layer d w, S.ε₂ < dist x z)) ∧
      ∃ r ∈ Icc (0 : ℝ) 1, S.FarFrom r (layerSet d (Icc s t))

/-- `E24Claims` at a pair contradicts Property 2. -/
theorem E24Claims.false (S : Thm1Setup M) {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {y₀ : M} {B : Set Pt} (hcl : E24Claims S d y₀ B) {b : M}
    (hbB : (b : Pt) ∈ B) (hbL : b ∈ L) (hdist : dist y₀ b < S.ε₃) : False := by
  obtain ⟨s, t, hst, hpos, hess, hfar, r, hr, hP⟩ := hcl b hbB hbL hdist
  rcases hpos with ⟨hy, hb⟩ | ⟨hb, hy⟩
  · exact property2_violation S hL hst hy hb hdist hess hfar hr hP
  · exact property2_violation S hL hst hb hy (by rw [dist_comm]; exact hdist) hess hfar hr hP

/-- **E2.4, first configuration impossible** (commission 183 §2.1; Bing: "If `q` were above
`tu` …"). Let `yᵢ` be a good point down from `S_I` with `f(yᵢ)` up from `S_I`, and let `Cᵢ₋₁`
(`C'`, a crossing piece with `Cl Cᵢ₋₁ ⊆ L`) lie between `yᵢ` and `S_I`. If `yᵢ ∈ L` and the claims
of steps 3–6 hold at `yᵢ` for `Cl Cᵢ₋₁`, this configuration does not occur. -/
theorem e24_between_false (S : Thm1Setup M) (o : Bool) {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {u v : unitInterval} {SI C' : Set Pt}
    (hSI : S.IsBlockStrand u v SI) {yi : M} (hy : S.GoodPoint yi) (hydn : (yi : Pt) ∈ S.dn o SI)
    (hfup : ((S.D.f yi : M) : Pt) ∈ S.up o SI)
    (hC' : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ C')
    (hC's : Disjoint (S.V.below C') (S.V.above C')) (hyC' : (yi : Pt) ∈ S.dn o C')
    (hSIC' : SI ⊆ S.up o C') (hC'L : closure C' ⊆ toPt L)
    (hcl : E24Claims S d yi (closure C')) : False := by
  obtain ⟨c, hc, hdist⟩ := e24_pair_between S o hSI hy hydn hfup hC' hC's hyC' hSIC'
  obtain ⟨b, hbL, rfl⟩ := hC'L hc
  exact E24Claims.false S hL hcl hc hbL hdist

/-- **E2.4, the field `far`** (commission 183 §2.2; p. 348: "`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`"). Let
`yᵢ₋₁` (`y'`) be a point of `Mid ∩ L` down from `Cᵢ` (a crossing piece with `Cl Cᵢ ⊆ L`), and the
`I`-strand `S_I` up from `Cᵢ`. If the claims of steps 3–6 hold at `yᵢ₋₁` for `Cl Cᵢ`, then
`ρ(yᵢ₋₁, Cl S_I) ≥ ε₃`. -/
theorem e24_below_far (S : Thm1Setup M) (o : Bool) {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {u v : unitInterval} {SI Ci : Set Pt}
    (hSI : S.IsBlockStrand u v SI) {y' : M} (hy' : (y' : Pt) ∈ midSet M S.π S.F S.D' S.n)
    (hCi : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ Ci)
    (hCis : Disjoint (S.V.below Ci) (S.V.above Ci)) (hy'Ci : (y' : Pt) ∈ S.dn o Ci)
    (hSICi : SI ⊆ S.up o Ci) (hCiL : closure Ci ⊆ toPt L)
    (hcl : E24Claims S d y' (closure Ci)) : S.ε₃ ≤ infDist (y' : Pt) (closure SI) := by
  by_contra hlt
  obtain ⟨c, hc, hdist⟩ := e24_pair_below S o hSI hy' hCi hCis hy'Ci hSICi (not_le.1 hlt)
  obtain ⟨b, hbL, rfl⟩ := hCiL hc
  exact E24Claims.false S hL hcl hc hbL hdist

end E24

end HPC.Hagopian
