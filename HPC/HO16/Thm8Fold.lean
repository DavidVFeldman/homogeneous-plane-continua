import HPC.HO16.Lemma6

/-!
# Batch 194, §6: H–O Theorem 8, (1) ⇒ (2), for simple folds

From `ho16_theorem8_core` (batch 193) and the inverses `ψᵢ = (φ|Fᵢ)⁻¹`, glued along the closed
pieces `X₁, X₂, X₃` (commission 194, §6). H–O p. 187, (2): "for any map f : X → G to a graph G,
for any simple fold φ : F → G, and for any ε > 0, there exists a map g : X → F such that
d_sup(f, φ∘g) < ε".
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane

/-- **H–O Theorem 8, (1) ⇒ (2)** (pp. 187–189): a map of a hereditarily indecomposable compactum
to `G` lifts, up to `ε`, through any simple fold on `G`. -/
theorem ho16_theorem8 {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G G₁ G₂ G₃ : Set E}
    {F₁ F₂ F₃ : Set (E × ℝ)} (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃)
    {f : X → E} (hf : Continuous f) (hfG : ∀ x, f x ∈ G) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → E × ℝ, Continuous g ∧ (∀ x, g x ∈ F₁ ∪ F₂ ∪ F₃) ∧ ∀ x, dist (f x) (g x).1 < ε := by
  classical
  obtain ⟨hT, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃, h12, h23, -⟩ := hF
  have hT' := hT
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, hF3⟩ := hT'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  have hL := relFrontier_left_eq hG₁c hG₃c hcov hG₂
  have hR := relFrontier_right_eq hG₁c hG₃c hcov hG₂
  have hfin₁ : (closure (G₁ \ G₂) ∩ G₂).Finite := hR ▸ hT.relFrontier_right_finite
  have hfin₃ : (closure (G₃ \ G₂) ∩ G₂).Finite := hL ▸ hT.relFrontier_left_finite
  have hfan : ∀ y ∈ (closure (G₁ \ G₂) ∪ closure (G₃ \ G₂)) ∩ G₂, ∀ r : ℝ, 0 < r →
      ∃ Y, IsFanAt G₂ y r Y := fun y hy r hr => hG₂P.exists_fan hy.2 hr
  obtain ⟨h, X₁, X₂, X₃, hh, hdist, hX₁, hX₂, hX₃, hcovX, hX13, hh₁, hh₂, hh₃, hh12, hh23⟩ :=
    ho16_theorem8_core hHI hG₁c hG₃c hcov hG₂ hF3 hfin₁ hfin₃ hfan hf hfG hε
  have hψ : ∀ {F : Set (E × ℝ)} {y : E}, y ∈ Prod.fst '' F →
      Function.invFunOn Prod.fst F y ∈ F ∧ (Function.invFunOn Prod.fst F y).1 = y :=
    fun hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
  set g : X → E × ℝ := fun x =>
    if x ∈ X₁ then Function.invFunOn Prod.fst F₁ (h x) else if x ∈ X₂ then Function.invFunOn Prod.fst F₂ (h x) else Function.invFunOn Prod.fst F₃ (h x) with hgdef
  have hg1 : ∀ x ∈ X₁, g x = Function.invFunOn Prod.fst F₁ (h x) := fun x hx => if_pos hx
  have hg2 : ∀ x ∈ X₂, g x = Function.invFunOn Prod.fst F₂ (h x) := by
    intro x hx
    by_cases hx1 : x ∈ X₁
    · have hm : h x ∈ Prod.fst '' (F₁ ∩ F₂) := by rw [h12, hL]; exact hh12 x ⟨hx1, hx⟩
      obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ := hm
      simp only [hgdef, if_pos hx1]
      rw [← hq, hi₁.leftInvOn_invFunOn hq1, hi₂.leftInvOn_invFunOn hq2]
    · simp only [hgdef, if_neg hx1, if_pos hx]
  have hg3 : ∀ x ∈ X₃, g x = Function.invFunOn Prod.fst F₃ (h x) := by
    intro x hx
    have hx1 : x ∉ X₁ := fun h1 => hX13.ne_of_mem h1 hx rfl
    by_cases hx2 : x ∈ X₂
    · have hm : h x ∈ Prod.fst '' (F₂ ∩ F₃) := by rw [h23, hR]; exact hh23 x ⟨hx2, hx⟩
      obtain ⟨q, ⟨hq2, hq3⟩, hq⟩ := hm
      simp only [hgdef, if_neg hx1, if_pos hx2]
      rw [← hq, hi₂.leftInvOn_invFunOn hq2, hi₃.leftInvOn_invFunOn hq3]
    · simp only [hgdef, if_neg hx1, if_neg hx2]
  have hc1 : ContinuousOn g X₁ :=
    ((continuousOn_invFunOn_fst hP₁.isCompact hi₁).comp hh.continuousOn
      (fun x hx => he₁.symm ▸ hh₁ x hx)).congr hg1
  have hc2 : ContinuousOn g X₂ :=
    ((continuousOn_invFunOn_fst hP₂.isCompact hi₂).comp hh.continuousOn
      (fun x hx => he₂.symm ▸ hh₂ x hx)).congr hg2
  have hc3 : ContinuousOn g X₃ :=
    ((continuousOn_invFunOn_fst hP₃.isCompact hi₃).comp hh.continuousOn
      (fun x hx => he₃.symm ▸ hh₃ x hx)).congr hg3
  have hgx : ∀ x, g x ∈ F₁ ∪ F₂ ∪ F₃ ∧ (g x).1 = h x := by
    intro x
    have hx : x ∈ X₁ ∪ X₂ ∪ X₃ := hcovX ▸ mem_univ x
    rcases hx with (hx | hx) | hx
    · rw [hg1 x hx]
      obtain ⟨h1, h2⟩ := hψ (he₁.symm ▸ hh₁ x hx : h x ∈ Prod.fst '' F₁)
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · rw [hg2 x hx]
      obtain ⟨h1, h2⟩ := hψ (he₂.symm ▸ hh₂ x hx : h x ∈ Prod.fst '' F₂)
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · rw [hg3 x hx]
      obtain ⟨h1, h2⟩ := hψ (he₃.symm ▸ hh₃ x hx : h x ∈ Prod.fst '' F₃)
      exact ⟨Or.inr h1, h2⟩
  refine ⟨g, ?_, fun x => (hgx x).1, fun x => by rw [(hgx x).2]; exact hdist x⟩
  rw [← continuousOn_univ, ← hcovX]
  exact (hc1.union_of_isClosed hc2 hX₁ hX₂).union_of_isClosed hc3 (hX₁.union hX₂) hX₃

end HPC.HO16
