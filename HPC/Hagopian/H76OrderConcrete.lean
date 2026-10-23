import HPC.Hagopian.H76Order
import HPC.Hagopian.H76Crosscut
import HPC.Hagopian.H76DCollar
import HPC.Hagopian.H76Bottom

/-!
# Batch 178, §1: the concrete frame and crossing pieces

* `lowFrame`: the vertical frame of commission 178 §1: `O = π⁻¹[F[D′]]`, and the low vertical
  `σ = π⁻¹F[{t₀} × (0, w₂)]`, with `lev P v ↔ v ∈ (0, w₂) ∧ π P = F(t₀, v)`.
* `lowFrame_hyps`: its hypotheses (connectedness of `O` and of the pieces of `σ`) hold when `O`
  misses `E` (from `isPreconnected_preimage_off` and `pi_preimage_isPreconnected`).
* `IsCrossingPiece`: commission 178's crossing piece (connected, in `O`, closed in `O`, compact
  closure missing `π⁻¹` of the bottom edge and of `I₂`, closure meeting both open side segments).
* `isPiece_of_isCrossingPiece`: **every crossing piece is a piece of `lowFrame`**. Its heights are
  compact (the closure misses the two ends of the closed vertical segment), nonempty (**S4a**, from
  `K0_crosscut_aux`, the transported `rect_domain_crosscut`), and its sides are disjoint (from
  `crossing_separates_aux`, the core of `crossing_sides`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **The concrete frame** (commission 178 §1): `O = π⁻¹[D]`, `σ = π⁻¹F[{t₀} × (0, w₂)]`. -/
def lowFrame (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (t₀ w₂ : ℝ)
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hOc : IsPreconnected (π ⁻¹' (F '' D')))
    (hsub : ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') (hinj : InjOn π (π ⁻¹' (F '' D')))
    (hsurj : Function.Surjective π)
    (hseg : ∀ J : Set ℝ, IsPreconnected J →
      IsPreconnected (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂))))) : VFrame where
  O := π ⁻¹' (F '' D')
  w := w₂
  lev P v := v ∈ Ioo 0 w₂ ∧ π P = F (t₀, v)
  isOpen_O := hOo
  isPreconnected_O := hOc
  lev_mem P v h := ⟨(t₀, v), hsub ⟨rfl, h.1⟩, h.2.symm⟩
  lev_pos _ _ h := h.1
  lev_inj P Q v hP hQ := hinj ⟨(t₀, v), hsub ⟨rfl, hP.1⟩, hP.2.symm⟩
    ⟨(t₀, v), hsub ⟨rfl, hQ.1⟩, hQ.2.symm⟩ (hP.2.trans hQ.2.symm)
  lev_exists v hv := by
    obtain ⟨P, hP⟩ := hsurj (F (t₀, v))
    exact ⟨P, hv, hP⟩
  seg_preconnected J hJ := by
    convert hseg J hJ using 1
    ext P
    constructor
    · rintro ⟨t, htJ, ht, hP⟩
      exact ⟨(t₀, t), ⟨rfl, htJ, ht⟩, hP.symm⟩
    · rintro ⟨q, ⟨hq1, hqJ, hq⟩, hP⟩
      refine ⟨q.2, hqJ, hq, ?_⟩
      rw [← hP]
      congr 1
      exact Prod.ext hq1 rfl

section Hyps

variable {M : Set Pt}

/-- **The hypotheses of `lowFrame`** (connectedness of `O` and of the pieces of `σ`) hold when
`π⁻¹[D]` misses `E` and `D′` is connected. -/
theorem lowFrame_hyps {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {D' : Set (ℝ × ℝ)}
    (hD'R : D' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) (hD'c : IsPreconnected D')
    (hFDo : IsOpen (F '' D')) (hdisj : Disjoint (π ⁻¹' (F '' D')) (toPt E)) {t₀ w₂ : ℝ}
    (hsub : ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') :
    IsPreconnected (π ⁻¹' (F '' D')) ∧
      ∀ J : Set ℝ, IsPreconnected J →
        IsPreconnected (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)))) := by
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  refine ⟨isPreconnected_preimage_off hπ hπS hFDo (hD'c.image F (hFc.mono hD'R)) hdisj,
    fun J hJ => ?_⟩
  have hJ' : IsPreconnected (({t₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)) :=
    isPreconnected_singleton.prod
      ((isPreconnected_iff_ordConnected.1 hJ).inter ordConnected_Ioo).isPreconnected
  have hsub' : ({t₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂) ⊆ D' :=
    (prod_mono subset_rfl inter_subset_right).trans hsub
  refine pi_preimage_isPreconnected hE hπ hπS (hJ'.image F (hFc.mono (hsub'.trans hD'R))) ?_
  rw [disjoint_left]
  rintro _ ⟨q, hq, rfl⟩ ⟨e, he, hπe⟩
  exact disjoint_left.1 hdisj (show e ∈ π ⁻¹' (F '' D') from ⟨q, hsub' hq, hπe.symm⟩) he

end Hyps

/-- **A crossing piece** (commission 178 §1): a connected `X ⊆ O`, closed in `O`, with compact
closure missing `π⁻¹` of `I₂` and of the bottom edge, and meeting both open side segments. -/
structure IsCrossingPiece (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (a b r₂ s₂ : ℝ)
    (I₂ : Set Pt) (X : Set Pt) : Prop where
  preconnected : IsPreconnected X
  subset_O : X ⊆ π ⁻¹' (F '' D')
  closure_inter : closure X ∩ π ⁻¹' (F '' D') ⊆ X
  compact : IsCompact (closure X)
  miss : Disjoint (closure X) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0})))
  left : (closure X ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty
  right : (closure X ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty

/-- **Every crossing piece is a piece of the low frame** (commission 178 §1, S4a and the
disjointness of the sides): its `σ`-heights are compact and nonempty (S4a, `K0_crosscut_aux`), and
its sides `A(X)`, `B(X)` are disjoint (`crossing_separates_aux`). -/
theorem isPiece_of_isCrossingPiece {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
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
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hOc : IsPreconnected (π ⁻¹' (F '' D')))
    (hsub : ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') (hπinj : InjOn π (π ⁻¹' (F '' D')))
    (hsurj : Function.Surjective π)
    (hsegc : ∀ J : Set ℝ, IsPreconnected J →
      IsPreconnected (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)))))
    {X : Set Pt} (hX : IsCrossingPiece π F D' a b r₂ s₂ I₂ X) :
    (lowFrame π F D' x₀ w₂ hOo hOc hsub hπinj hsurj hsegc).IsPiece X := by
  set V := lowFrame π F D' x₀ w₂ hOo hOc hsub hπinj hsurj hsegc with hV
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hx₀R : ∀ v ∈ Icc 0 w₂, ((x₀, v) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    fun v hv => ⟨⟨by linarith [hx₀.1], by linarith [hx₀.2]⟩, by linarith [hv.1],
      by linarith [hv.2, hw₂.2]⟩
  have hhts : V.hts X = {v | ∃ P ∈ closure X, v ∈ Ioo 0 w₂ ∧ π P = F (x₀, v)} := rfl
  -- the heights are compact
  have hcomp : IsCompact (V.hts X) := by
    have heq : V.hts X = Icc 0 w₂ ∩ (fun v => F (x₀, v)) ⁻¹' (π '' closure X) := by
      rw [hhts]
      ext v
      constructor
      · rintro ⟨P, hP, hv, hπP⟩
        exact ⟨Ioo_subset_Icc_self hv, P, hP, hπP⟩
      · rintro ⟨hv, P, hP, hπP⟩
        refine ⟨P, hP, ⟨lt_of_le_of_ne hv.1 fun h => ?_, lt_of_le_of_ne hv.2 fun h => ?_⟩, hπP⟩
        · have h0 : π P = F (x₀, 0) := by rw [h]; exact hπP
          exact disjoint_left.1 hX.miss hP
            (Or.inr ⟨(x₀, 0), ⟨⟨hx₀.1.le, hx₀.2.le⟩, rfl⟩, h0.symm⟩)
        · have h1 : π P = F (x₀, w₂) := by rw [← h]; exact hπP
          exact disjoint_left.1 hX.miss hP (Or.inl (show π P ∈ I₂ by rw [h1]; exact hFw))
    rw [heq]
    have hcl : IsClosed (Icc 0 w₂ ∩ (fun v => F (x₀, v)) ⁻¹' (π '' closure X)) :=
      ContinuousOn.preimage_isClosed_of_isClosed
        (hFc.comp (continuousOn_const.prodMk continuousOn_id) fun v hv => hx₀R v hv)
        isClosed_Icc (hX.compact.image hπc).isClosed
    exact isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  -- S4a: the heights are nonempty
  have hne : (V.hts X).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    refine K0_crosscut_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg
      hX.preconnected (fun P hP => ⟨hX.subset_O hP, ?_⟩) hX.left hX.right
    rintro ⟨q, ⟨hq1, hq2⟩, hπP⟩
    have hq : q = (x₀, q.2) := Prod.ext hq1 rfl
    have : q.2 ∈ V.hts X := ⟨P, subset_closure hP, hq2, by rw [← hπP, ← hq]⟩
    rw [hno] at this
    exact this
  refine ⟨hX.preconnected, hX.subset_O, hX.closure_inter, hcomp, hne, ?_⟩
  -- the sides are disjoint
  rw [disjoint_left]
  rintro P ⟨S₁, hS₁, hS₁O, hPS₁, P₁, hP₁S, v, ⟨hv, hπP₁⟩, hvu⟩
    ⟨S₂, hS₂, hS₂O, hPS₂, P₂, hP₂S, v', ⟨hv', hπP₂⟩, hvu'⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hvv' : v < v' := (hvu u₀ hu₀).trans (hvu' u₀ hu₀)
  have hlo : Disjoint (closure X) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 v))) := by
    rw [disjoint_left]
    rintro Q hQ ⟨q, ⟨hq1, hq2⟩, hπQ⟩
    have hq : q = (x₀, q.2) := Prod.ext hq1 rfl
    have hmem : q.2 ∈ V.hts X :=
      ⟨Q, hQ, ⟨hq2.1, hq2.2.trans_lt hv.2⟩, by rw [← hπQ, ← hq]⟩
    exact (hvu _ hmem).not_ge hq2.2
  have hhi : Disjoint (closure X) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico v' w₂))) := by
    rw [disjoint_left]
    rintro Q hQ ⟨q, ⟨hq1, hq2⟩, hπQ⟩
    have hq : q = (x₀, q.2) := Prod.ext hq1 rfl
    have hmem : q.2 ∈ V.hts X :=
      ⟨Q, hQ, ⟨hv'.1.trans_le hq2.1, hq2.2⟩, by rw [← hπQ, ← hq]⟩
    exact (hvu' _ hmem).not_ge hq2.1
  exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj
    hX.preconnected hX.subset_O hX.compact hX.miss hX.left hX.right hv.1 hvv' hv'.2 hlo hhi
    (hS₁.union P hPS₁ hPS₂ hS₂) (union_subset hS₁O hS₂O) (Or.inl hP₁S) (Or.inr hP₂S)
    hπP₁ hπP₂

end HPC.Hagopian
