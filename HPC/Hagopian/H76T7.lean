import HPC.Hagopian.H76NoHair
import HPC.Hagopian.H76Crossing

/-!
# Batch 165, item A.4: T7 by the crossing argument

`hagopian76_T7_aux` (commission 165 §1, step 4): a thin collar rectangle over `[a, b]` lies in
`π[U]` (`U` open, `U ⊇ E`, so `U` is saturated and `π[U]` is open), and in every thinner rectangle
the crossing lemma, applied to `K = {z : F(z) ∈ π[M]}`, gives `I₂`. A connected part of `K` from the
bottom to the top would pull back (`preimage_pi_isContinuum_aux`) to a continuum of `M` meeting `E`
and missing both end sets, hence inside `E` (`no_hair_aux`), whereas it reaches the top edge.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section T7

variable {M : Set Pt}

/-- An open set containing `E` is saturated, so its `π`-image is open. -/
theorem isOpen_pi_image {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {U : Set Pt}
    (hU : IsOpen U) (hEU : toPt E ⊆ U) : IsOpen (π '' U) := by
  rw [← hπ.isOpen_preimage]
  convert hU using 1
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    by_cases hp : p ∈ toPt E
    · exact hEU hp
    · have h := (hπS q p).1 hqp
      change q ∈ HPC.Moore.elt (layerSetoid k) p at h
      rw [elt_layerSetoid_of_notMem k hp, mem_singleton_iff] at h
      rw [← h]; exact hq
  · intro hp; exact ⟨p, hp, rfl⟩

/-- A positive height below a compact set of the closed upper half plane missing the axis. -/
theorem exists_height_below {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q) (hQ0 : ∀ z ∈ Q, 0 < z.2) :
    ∃ c > 0, c ≤ 1 ∧ ∀ z ∈ Q, c < z.2 := by
  rcases Q.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, le_rfl, fun z hz => by rw [h] at hz; exact hz.elim⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn h continuous_snd.continuousOn
    have h0 := hQ0 z₀ hz₀
    refine ⟨min 1 (z₀.2 / 2), lt_min one_pos (by linarith), min_le_left _ _, fun z hz => ?_⟩
    have := isMinOn_iff.1 hmin z hz
    have := min_le_right 1 (z₀.2 / 2)
    linarith

variable [CompactSpace M] [ConnectedSpace M]

/-- **T7** (commission 165 §1, step 4). -/
theorem hagopian76_T7_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {U : Set Pt} (hU : IsOpen U)
    (hEU : toPt E ⊆ U) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc a b ×ˢ Icc 0 c) ⊆ π '' U ∧
      ∀ c', 0 < c' → c' ≤ c → ∃ (r s : Pt) (I₂ : Set Pt), TArc r s I₂ ∧
        I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c') ∧ Disjoint I₂ (π '' M) ∧
        I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c') = {r, s} ∧
        r ∈ F '' (({a} : Set ℝ) ×ˢ Ioc 0 c') ∧ s ∈ F '' (({b} : Set ℝ) ×ˢ Ioc 0 c') := by
  obtain ⟨hFemb, hF0, -⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hsurj : Function.Surjective k := hE.2.1.2.1
  have hπc : Continuous π := hπ.continuous
  have hγM : ∀ t : unitInterval, γ t ∈ π '' M := fun t => by
    obtain ⟨x, hx⟩ := layer_nonempty hsurj t
    exact ⟨x, x.2, hγπ t x ⟨x, hx, rfl⟩⟩
  have hγU : ∀ t : unitInterval, γ t ∈ π '' U := fun t => by
    obtain ⟨x, hx⟩ := layer_nonempty hsurj t
    exact ⟨x, hEU ⟨x, img_subset _ hx, rfl⟩, hγπ t x ⟨x, hx, rfl⟩⟩
  have hsub : ∀ {c : ℝ}, 0 ≤ c → c ≤ 1 → Icc a b ×ˢ Icc 0 c ⊆ R1 :=
    fun h0 h1 z ⟨⟨h2, h3⟩, h4, h5⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hF0' : ∀ t : ℝ, t ∈ Icc a b → F (t, 0) ∈ π '' M := fun t ht => by
    have := hF0 ⟨t, by linarith [ht.1], by linarith [ht.2]⟩
    rw [this]; exact hγM _
  -- the thin rectangle in `π[U]`
  have hVo : IsOpen (π '' U) := isOpen_pi_image hπ hπS hU hEU
  set Q := (Icc a b ×ˢ Icc (0 : ℝ) 1) ∩ F ⁻¹' (π '' U)ᶜ with hQd
  have hQc : IsCompact Q :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      ((hFc.mono (hsub zero_le_one le_rfl)).preimage_isClosed_of_isClosed
        (isClosed_Icc.prod isClosed_Icc) hVo.isClosed_compl) inter_subset_left
  have hQ0 : ∀ z ∈ Q, 0 < z.2 := by
    rintro ⟨t, h⟩ ⟨⟨ht, h0, -⟩, hFz⟩
    rcases eq_or_lt_of_le h0 with h' | h'
    · exfalso
      apply hFz
      have h'' : h = 0 := h'.symm
      subst h''
      have := hF0 ⟨t, by linarith [ht.1], by linarith [ht.2]⟩
      show F (t, 0) ∈ π '' U
      rw [this]; exact hγU _
    · exact h'
  obtain ⟨c, hc, hc1, hcQ⟩ := exists_height_below hQc hQ0
  refine ⟨c, hc, hc1, ?_, ?_⟩
  · rintro _ ⟨z, ⟨hz1, hz2, hz3⟩, rfl⟩
    by_contra hn
    have := hcQ z ⟨⟨hz1, hz2, hz3.trans hc1⟩, hn⟩
    linarith
  -- the crossing arc
  intro c' hc' hc'c
  have hc'1 : c' ≤ 1 := hc'c.trans hc1
  set K := (Icc a b ×ˢ Icc 0 c') ∩ F ⁻¹' (π '' M) with hKd
  have hπM : IsCompact (π '' M) := (isCompact_iff_compactSpace.2 ‹_›).image hπc
  have hKc : IsClosed K := (hFc.mono (hsub hc'.le hc'1)).preimage_isClosed_of_isClosed
    (isClosed_Icc.prod isClosed_Icc) hπM.isClosed
  have hKR : K ⊆ Icc a b ×ˢ Icc 0 c' := inter_subset_left
  have hbot : Icc a b ×ˢ {0} ⊆ K := by
    rintro ⟨t, h⟩ ⟨ht, h0⟩
    have h0' : h = 0 := h0
    subst h0'
    exact ⟨⟨ht, le_rfl, hc'.le⟩, hF0' t ht⟩
  have hno : ∀ C ⊆ K, IsConnected C → (C ∩ Icc a b ×ˢ {c'}).Nonempty →
      (C ∩ Icc a b ×ˢ {0}).Nonempty → False := by
    rintro C hCK hC ⟨z₁, hz₁C, -, hz₁T⟩ ⟨z₀, hz₀C, hz₀a, hz₀B⟩
    have hz₁T' : z₁.2 = c' := hz₁T
    have hz₀B' : z₀.2 = 0 := hz₀B
    have hDK : closure C ⊆ K := closure_minimal hCK hKc
    have hDR : closure C ⊆ R1 := hDK.trans (hKR.trans (hsub hc'.le hc'1))
    have hDc : IsCompact (closure C) :=
      (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure (hDK.trans hKR)
    have hFD : Fold.Q78.IsContinuum (F '' closure C) :=
      ⟨hDc.image_of_continuousOn (hFc.mono hDR), hC.closure.image _ (hFc.mono hDR)⟩
    have hFDM : F '' closure C ⊆ π '' M := by
      rintro _ ⟨z, hz, rfl⟩; exact (hDK hz).2
    have hQ := preimage_pi_isContinuum_aux hE hπc hπS hFD hFDM
    -- `Q` meets `E`
    set t₀ : unitInterval := ⟨z₀.1, by linarith [hz₀a.1], by linarith [hz₀a.2]⟩
    obtain ⟨x₀, hx₀⟩ := layer_nonempty hsurj t₀
    have hx₀Q : x₀ ∈ {x : M | π (x : Pt) ∈ F '' closure C} := by
      refine ⟨z₀, subset_closure hz₀C, ?_⟩
      rw [hγπ t₀ x₀ ⟨x₀, hx₀, rfl⟩]
      have : z₀ = ((t₀ : ℝ), 0) := Prod.ext rfl hz₀B'
      rw [this, hF0]
    have hQE : ({x : M | π (x : Pt) ∈ F '' closure C} ∩ E).Nonempty :=
      ⟨x₀, hx₀Q, img_subset _ hx₀⟩
    -- `Q` misses the end sets
    have hend : ∀ s : unitInterval, ((s : ℝ) < a ∨ b < (s : ℝ)) →
        Disjoint {x : M | π (x : Pt) ∈ F '' closure C} (layer k s) := by
      intro s hs
      rw [disjoint_left]
      rintro x ⟨z, hzD, hz⟩ hxs
      have hπx : π x = γ s := hγπ s x ⟨x, hxs, rfl⟩
      have hzs : z = ((s : ℝ), 0) := hFinj (hDR hzD) ⟨⟨s.2.1, s.2.2⟩, by norm_num, by norm_num⟩
        (by rw [hz, hπx, hF0])
      have h1 := (hDK hzD).1.1
      rw [hzs] at h1
      rcases hs with hs | hs
      · exact absurd h1.1 (not_le.2 hs)
      · exact absurd h1.2 (not_le.2 hs)
    have hQsub := no_hair_aux hX hi hE hQ hQE
      (hend 0 (Or.inl (by show (0 : ℝ) < a; exact ha)))
      (hend 1 (Or.inr (by show b < (1 : ℝ); exact hb)))
    -- but it reaches the top edge
    obtain ⟨p, hpM, hp⟩ := (hCK hz₁C).2
    set x₁ : M := ⟨p, hpM⟩
    have hx₁Q : x₁ ∈ {x : M | π (x : Pt) ∈ F '' closure C} := by
      show π p ∈ F '' closure C
      rw [hp]; exact ⟨z₁, subset_closure hz₁C, rfl⟩
    have hx₁E := hQsub hx₁Q
    set e : E := ⟨x₁, hx₁E⟩
    have hπp : π p = γ (k e) := hγπ (k e) p ⟨x₁, ⟨e, rfl, rfl⟩, rfl⟩
    have hz₁R : z₁ ∈ R1 := hsub hc'.le hc'1 (hCK hz₁C).1
    have := hFinj hz₁R (⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩ :
      (((k e : unitInterval) : ℝ), (0 : ℝ)) ∈ R1) (by rw [← hp, hπp, hF0])
    have h2 := congrArg Prod.snd this
    simp only at h2
    linarith
  obtain ⟨r, s, I, ⟨hrs, f, hf, hfI, hf0, hf1⟩, hIsub, hr1, hs1, hIends⟩ :=
    rect_crossing_aux hab hc' hKc hKR hbot hno
  have hIR : I ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hIsub hz).1
    exact hsub hc'.le hc'1 ⟨⟨h1, h2⟩, h3.le, h4⟩
  have hSR : ({a, b} : Set ℝ) ×ˢ Icc 0 c' ⊆ R1 := by
    rintro z ⟨h1, h2, h3⟩
    rcases h1 with h1 | h1 <;>
      exact ⟨⟨by rw [h1]; linarith, by rw [h1]; linarith⟩, by linarith, by linarith⟩
  have hrI : r ∈ I := by
    have : r ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c') := by rw [hIends]; exact Or.inl rfl
    exact this.1
  have hsI : s ∈ I := by
    have : s ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c') := by rw [hIends]; exact Or.inr rfl
    exact this.1
  have hfR : ∀ t, f t ∈ R1 := fun t => hIR (hfI ▸ mem_range_self t)
  refine ⟨F r, F s, F '' I, ?_, image_mono fun z hz => (hIsub hz).1, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun h => hrs (hFinj (hIR hrI) (hIR hsI) h), F ∘ f, ?_, ?_, ?_, ?_⟩
    · have : F ∘ f = R1.restrict F ∘ codRestrict f R1 hfR := rfl
      rw [this]
      exact hFemb.comp (hf.codRestrict R1 hfR)
    · rw [range_comp, hfI]
    · simp [hf0]
    · simp [hf1]
  · rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hzM
    obtain ⟨⟨h1, h2, h3⟩, hzK⟩ := hIsub hz
    exact hzK ⟨⟨h1, h2.le, h3⟩, hzM⟩
  · rw [← (hFinj.mono (union_subset hIR hSR)).image_inter subset_union_left subset_union_right,
      hIends, image_pair]
  · obtain ⟨-, h2⟩ := (hIsub hrI).1
    exact ⟨r, ⟨hr1, h2⟩, rfl⟩
  · obtain ⟨-, h2⟩ := (hIsub hsI).1
    exact ⟨s, ⟨hs1, h2⟩, rfl⟩

end T7

end HPC.Hagopian
