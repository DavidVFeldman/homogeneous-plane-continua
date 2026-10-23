import HPC.Hagopian.H76CrossSep

/-!
# Batch 169, item A: above and below a crossing continuum

For a set `Z ⊆ R²` (a crossing continuum `Cl B`), `D = F[D′]` and the vertical over `t₀`:
* `belowSet π F D′ t₀ u Z`: the points of `π⁻¹[D] − Z` joined, by a connected subset of
  `π⁻¹[D] − Z`, to a point over `F(t₀, v)` with `0 < v ≤ u`;
* `aboveSet π F D′ t₀ u w₂ Z`: the same with `u ≤ v < w₂` (`F(t₀, w₂)` is the lowest point of
  `I₂` over `t₀`).

Proved:
* `belowSet_isOpen`, `aboveSet_isOpen`: both are open in `R²`;
* `mem_belowSet`, `mem_aboveSet`, `belowSet_of_preconnected`, `aboveSet_of_preconnected`;
* `crossing_sides_aux`: for a crossing continuum `Z = Cl B` (the hypotheses of `crossing_separates`)
  missing the vertical at heights `(0, u₁]` and `[u₂, w₂)`, `belowSet … u₁ Z` and
  `aboveSet … u₂ w₂ Z` are disjoint.

Not proved (open, commission 169 §1.1): that they cover `π⁻¹[D] − Z`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

/-- The points **below** `Z` in `π⁻¹[D]`, relative to the vertical over `t₀` and the height `u`. -/
def belowSet (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (t₀ u : ℝ) (Z : Set Pt) :
    Set Pt :=
  {P | ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ π ⁻¹' (F '' D') \ Z ∧ P ∈ S ∧
    ∃ P₀ ∈ S, π P₀ ∈ F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u)}

/-- The points **above** `Z` in `π⁻¹[D]`, relative to the vertical over `t₀`, the height `u` and
the lowest point `F(t₀, w₂)` of `I₂` over `t₀`. -/
def aboveSet (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (t₀ u w₂ : ℝ) (Z : Set Pt) :
    Set Pt :=
  {P | ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ π ⁻¹' (F '' D') \ Z ∧ P ∈ S ∧
    ∃ P₀ ∈ S, π P₀ ∈ F '' (({t₀} : Set ℝ) ×ˢ Ico u w₂)}

section Sets

variable {π : Pt → Pt} {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {Z : Set Pt}

/-- A set of points joined by connected subsets of `O − Z` to a set `T` is open, if `O − Z` is. -/
theorem isOpen_joined {O Z T : Set Pt} (hO : IsOpen (O \ Z)) :
    IsOpen {P | ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ O \ Z ∧ P ∈ S ∧ ∃ P₀ ∈ S, P₀ ∈ T} := by
  rw [Metric.isOpen_iff]
  rintro P ⟨S, hS, hSO, hPS, P₀, hP₀S, hP₀T⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO P (hSO hPS)
  refine ⟨r, hr, fun P' hP' => ⟨S ∪ ball P r, ?_, union_subset hSO hball,
    Or.inr hP', P₀, Or.inl hP₀S, hP₀T⟩⟩
  exact hS.union P hPS (mem_ball_self hr) (convex_ball P r).isPreconnected

theorem belowSet_isOpen (hπc : Continuous π) (hFDo : IsOpen (F '' D')) (hZ : IsClosed Z)
    (t₀ u : ℝ) : IsOpen (belowSet π F D' t₀ u Z) :=
  isOpen_joined (T := π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u)))
    ((hFDo.preimage hπc).sdiff hZ)

theorem aboveSet_isOpen (hπc : Continuous π) (hFDo : IsOpen (F '' D')) (hZ : IsClosed Z)
    (t₀ u w₂ : ℝ) : IsOpen (aboveSet π F D' t₀ u w₂ Z) :=
  isOpen_joined (T := π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ico u w₂)))
    ((hFDo.preimage hπc).sdiff hZ)

theorem mem_belowSet {t₀ u : ℝ} {P : Pt} (hP : P ∈ π ⁻¹' (F '' D') \ Z)
    (hπP : π P ∈ F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u)) : P ∈ belowSet π F D' t₀ u Z :=
  ⟨{P}, isPreconnected_singleton, singleton_subset_iff.2 hP, rfl, P, rfl, hπP⟩

theorem mem_aboveSet {t₀ u w₂ : ℝ} {P : Pt} (hP : P ∈ π ⁻¹' (F '' D') \ Z)
    (hπP : π P ∈ F '' (({t₀} : Set ℝ) ×ˢ Ico u w₂)) : P ∈ aboveSet π F D' t₀ u w₂ Z :=
  ⟨{P}, isPreconnected_singleton, singleton_subset_iff.2 hP, rfl, P, rfl, hπP⟩

theorem belowSet_of_preconnected {t₀ u : ℝ} {S : Set Pt} (hS : IsPreconnected S)
    (hSO : S ⊆ π ⁻¹' (F '' D') \ Z) {P Q : Pt} (hP : P ∈ S) (hQ : Q ∈ S)
    (hPb : P ∈ belowSet π F D' t₀ u Z) : Q ∈ belowSet π F D' t₀ u Z := by
  obtain ⟨S', hS', hS'O, hPS', P₀, hP₀, hπP₀⟩ := hPb
  exact ⟨S' ∪ S, hS'.union P hPS' hP hS, union_subset hS'O hSO, Or.inr hQ, P₀, Or.inl hP₀,
    hπP₀⟩

theorem aboveSet_of_preconnected {t₀ u w₂ : ℝ} {S : Set Pt} (hS : IsPreconnected S)
    (hSO : S ⊆ π ⁻¹' (F '' D') \ Z) {P Q : Pt} (hP : P ∈ S) (hQ : Q ∈ S)
    (hPa : P ∈ aboveSet π F D' t₀ u w₂ Z) : Q ∈ aboveSet π F D' t₀ u w₂ Z := by
  obtain ⟨S', hS', hS'O, hPS', P₀, hP₀, hπP₀⟩ := hPa
  exact ⟨S' ∪ S, hS'.union P hPS' hP hS, union_subset hS'O hSO, Or.inr hQ, P₀, Or.inl hP₀,
    hπP₀⟩

end Sets

/-- **A. Above and below a crossing continuum are disjoint** (commission 169 §2.A). For a
crossing continuum `Z = Cl B` as in `crossing_separates` (connected `B ⊆ π⁻¹[D]`, `Cl B` compact,
missing `π⁻¹[I₂]` and the points over the axis, meeting both open side edges), missing the
vertical over `t₀` at the heights `(0, u₁]` and `[u₂, w₂)`, no point is both below and above `Z`. -/
theorem crossing_sides_aux {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hπinj : InjOn π (π ⁻¹' (F '' D')))
    {B : Set Pt} (hB : IsPreconnected B) (hBD : B ⊆ π ⁻¹' (F '' D'))
    (hBc : IsCompact (closure B))
    (hBe : Disjoint (closure B) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))))
    (hL : (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR : (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty)
    {u₁ u₂ : ℝ} (hu₁₂ : u₁ < u₂)
    (hlo : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))))
    (hhi : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂)))) :
    Disjoint (belowSet π F D' x₀ u₁ (closure B)) (aboveSet π F D' x₀ u₂ w₂ (closure B)) := by
  rw [disjoint_left]
  rintro P ⟨S₁, hS₁, hS₁O, hPS₁, P₁, hP₁S, w, ⟨hw1, hw2⟩, hFw1⟩
    ⟨S₂, hS₂, hS₂O, hPS₂, P₂, hP₂S, w', ⟨hw1', hw2'⟩, hFw2⟩
  have hw : w = (x₀, w.2) := Prod.ext hw1 rfl
  have hw' : w' = (x₀, w'.2) := Prod.ext hw1' rfl
  rw [hw] at hFw1
  rw [hw'] at hFw2
  have hlo' : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 w.2))) :=
    hlo.mono_right (preimage_mono (image_mono (prod_mono subset_rfl
      (Ioc_subset_Ioc_right hw2.2))))
  have hhi' : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico w'.2 w₂))) :=
    hhi.mono_right (preimage_mono (image_mono (prod_mono subset_rfl
      (Ico_subset_Ico_left hw2'.1))))
  exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj
    hB hBD hBc hBe hL hR hw2.1 (by linarith [hw2.2, hw2'.1]) hw2'.2 hlo' hhi'
    (hS₁.union P hPS₁ hPS₂ hS₂) (union_subset hS₁O hS₂O) (Or.inl hP₁S) (Or.inr hP₂S)
    hFw1.symm hFw2.symm

end HPC.Hagopian
