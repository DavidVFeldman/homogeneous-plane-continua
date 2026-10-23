import HPC.Hagopian.H76NoBelowCore

/-!
# Batch 163, item B: from the core to `no_M_below`

* `no_M_below_left`: the strip below `γ[[a, b]]`, `[a, b]` to the left of `y`. If no strip works,
  points of `M` over the strips accumulate at a point `u` of a layer `k⁻¹(a′)`, `a ≤ a′ ≤ b`, and
  `no_M_below_core` at `u` is contradicted.
* The mirror image (`[a, b]` to the right of `y`) by reversing the parameter: `k ↦ 1 − k`,
  `γ ↦ γ ∘ (1 − ·)`, `F(x, s) ↦ F(1 − x, s)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Main

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **No `π[M]` just below `γ[[a, b]]`**, for `[a, b]` to the left of `y`. -/
theorem no_M_below_left (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    (hFc : Continuous F) {y : unitInterval} (hy1 : y < 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hvert : F '' ({(y : ℝ)} ×ˢ Ico (-c₀) 0) ∩ π '' M = ∅)
    {a b : ℝ} (ha : 0 < a) (hby : b < y) :
    ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  by_contra hne
  push_neg at hne
  have hseq : ∀ n : ℕ, ∃ m : M, ∃ x s : ℝ, x ∈ Icc a b ∧ -(1 / ((n : ℝ) + 1)) ≤ s ∧ s < 0 ∧
      π m = F (x, s) := by
    intro n
    have := hne (1 / ((n : ℝ) + 1)) (by positivity)
    rw [Set.not_disjoint_iff] at this
    obtain ⟨p, ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩, ⟨m, hmM, hm⟩⟩ := this
    exact ⟨⟨m, hmM⟩, x, s, hx, hs.1, hs.2, hm⟩
  choose m x s hx hs1 hs2 hms using hseq
  obtain ⟨⟨u, x'⟩, ⟨-, hx'⟩, φ, hφ, hlim⟩ :=
    (isCompact_univ.prod isCompact_Icc : IsCompact ((univ : Set M) ×ˢ Icc a b)).tendsto_subseq
      (x := fun n => (m n, x n)) (fun n => ⟨mem_univ _, hx n⟩)
  have hmlim : Tendsto (fun n => m (φ n)) atTop (𝓝 u) := (continuous_fst.tendsto _).comp hlim
  have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 x') := (continuous_snd.tendsto _).comp hlim
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hs1 fun n => (hs2 n).le
  have hslim : Tendsto (fun n => s (φ n)) atTop (𝓝 0) := hs0.comp hφ.tendsto_atTop
  have hx'I : x' ∈ Icc (0 : ℝ) 1 := ⟨ha.le.trans hx'.1, hx'.2.trans (hby.le.trans y.2.2)⟩
  set a' : unitInterval := ⟨x', hx'I⟩ with ha'
  have hπu : π u = F (x', 0) := by
    have h1 : Tendsto (fun n => π (m (φ n))) atTop (𝓝 (π u)) :=
      (hπ.continuous.tendsto _).comp ((continuous_subtype_val.tendsto _).comp hmlim)
    have h2 : Tendsto (fun n => F (x (φ n), s (φ n))) atTop (𝓝 (F (x', 0))) :=
      (hFc.tendsto _).comp (hxlim.prodMk_nhds hslim)
    refine tendsto_nhds_unique h1 ?_
    simpa only [hms] using h2
  have hu : u ∈ layer k a' := by
    refine mem_layer_of_pi_eq hE.2.1.2.1 hπS hγπ ?_
    rw [hπu]; exact hF.2.1 a'
  obtain ⟨ζ, hζ, hcore⟩ := no_M_below_core hX hi hE hπ hπS hγ hγπ hF hFc hy1 hc₀ hvert
    (a' := a') (show (0 : ℝ) < x' from lt_of_lt_of_le ha hx'.1)
    (show x' < (y : ℝ) from lt_of_le_of_lt hx'.2 hby) hu
  have e1 : ∀ᶠ n in atTop, dist (m (φ n)) u < ζ := hmlim (ball_mem_nhds u hζ)
  have e2 : ∀ᶠ n in atTop, dist (x (φ n)) x' < ζ := hxlim (ball_mem_nhds x' hζ)
  have e3 : ∀ᶠ n in atTop, dist (s (φ n)) 0 < ζ := hslim (ball_mem_nhds 0 hζ)
  obtain ⟨n, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  rw [Real.dist_eq] at h2 h3
  rw [sub_zero, abs_lt] at h3
  exact hcore (m (φ n)) h1 (x (φ n)) (s (φ n)) h2 h3.1 (hs2 _) (hms _)

omit [CompactSpace M] [ConnectedSpace M] in
/-- Reversing the parameter of a minimal admissible map. -/
theorem IsMinimalAdmissible.symm' {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) :
    IsMinimalAdmissible E (fun e => unitInterval.symm (k e)) := by
  have hpre : ∀ t, (fun e => unitInterval.symm (k e)) ⁻¹' {t} = k ⁻¹' {unitInterval.symm t} := by
    intro t
    ext e
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; rw [← h, unitInterval.symm_symm]
    · intro h; rw [h, unitInterval.symm_symm]
  refine ⟨hE.1, ⟨unitInterval.continuous_symm.comp hE.2.1.1, fun t => ?_, fun t => ?_⟩,
    fun t => ?_⟩
  · obtain ⟨e, he⟩ := hE.2.1.2.1 (unitInterval.symm t)
    exact ⟨e, by simp only [he, unitInterval.symm_symm]⟩
  · rw [hpre]; exact hE.2.1.2.2 _
  · rw [hpre]; exact hE.2.2 _

omit [CompactSpace M] [ConnectedSpace M] in
theorem layer_symm {E : Set M} (k : E → unitInterval) (t : unitInterval) :
    layer (fun e => unitInterval.symm (k e)) t = layer k (unitInterval.symm t) := by
  ext m
  simp only [layer, mem_image, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, by rw [← he, unitInterval.symm_symm], rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, by rw [he, unitInterval.symm_symm], rfl⟩

omit [CompactSpace M] [ConnectedSpace M] in
theorem layerSetoid_symm {E : Set M} (k : E → unitInterval) (p q : Pt) :
    layerSetoid (fun e => unitInterval.symm (k e)) p q ↔ layerSetoid k p q := by
  have hkey : ∀ r, layerKey (fun e => unitInterval.symm (k e)) r =
      Sum.map unitInterval.symm id (layerKey k r) := by
    intro r
    simp only [layerKey]
    split_ifs <;> rfl
  change layerKey _ p = layerKey _ q ↔ layerKey k p = layerKey k q
  rw [hkey, hkey]
  constructor
  · intro h
    have hinj : Function.Injective (Sum.map unitInterval.symm (id : Pt → Pt)) :=
      Sum.map_injective.2 ⟨unitInterval.symm_involutive.injective, Function.injective_id⟩
    exact hinj h
  · intro h; rw [h]

/-- A collar read backwards is a collar of the reversed arc. -/
theorem IsCollar.reverse {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) :
    IsCollar (fun t => γ (unitInterval.symm t)) (fun q => F (1 - q.1, q.2)) := by
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hmaps : MapsTo (fun q : ℝ × ℝ => (1 - q.1, q.2)) K K := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [mem_Icc] at ha
    exact ⟨by simp only [mem_Icc]; constructor <;> linarith [ha.1, ha.2], hb⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hfl : IsEmbedding (hmaps.restrict _ K K) := by
    refine (Continuous.isClosedEmbedding ?_ ?_).isEmbedding
    · exact ((continuous_const.sub continuous_fst).prodMk continuous_snd).restrict hmaps
    · rintro ⟨⟨a, b⟩, _⟩ ⟨⟨a', b'⟩, _⟩ e
      simp only [MapsTo.restrict, Subtype.map, Subtype.mk.injEq, Prod.mk.injEq,
        sub_right_inj] at e
      exact Subtype.ext (Prod.ext e.1 e.2)
  refine ⟨hemb.comp hfl, fun t => ?_, ?_⟩
  · simp only
    rw [← h0 (unitInterval.symm t), unitInterval.coe_symm_eq]
  · have : (fun q : ℝ × ℝ => F (1 - q.1, q.2)) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) =
        F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
      ext z; constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        simp only [mem_Ioo] at ha
        exact ⟨(1 - a, b), ⟨by simp only [mem_Ioo]; constructor <;> linarith [ha.1, ha.2], hb⟩,
          rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        simp only [mem_Ioo] at ha
        exact ⟨(1 - a, b), ⟨by simp only [mem_Ioo]; constructor <;> linarith [ha.1, ha.2], hb⟩,
          by simp⟩
    rw [this]; exact hopen

/-- **No `π[M]` just below `γ[[a, b]]`**, both sides, for a continuous collar. -/
theorem no_M_below_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    (hFc : Continuous F) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hvert : F '' ({(y : ℝ)} ×ˢ Ico (-c₀) 0) ∩ π '' M = ∅)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hy : (y : ℝ) ∉ Icc a b) :
    ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  rcases not_and_or.1 hy with h | h
  · -- `[a, b]` to the right of `y`: reverse
    push_neg at h
    have hy1' : unitInterval.symm y < 1 := by
      show (unitInterval.symm y : ℝ) < 1
      rw [unitInterval.coe_symm_eq]; have : (0 : ℝ) < y := hy0; linarith
    have hvert' : (fun q : ℝ × ℝ => F (1 - q.1, q.2)) ''
        ({((unitInterval.symm y : unitInterval) : ℝ)} ×ˢ Ico (-c₀) 0) ∩ π '' M = ∅ := by
      rw [← hvert]
      congr 1
      ext p; constructor
      · rintro ⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩
        refine ⟨((y : ℝ), b₁), ⟨rfl, hb₁⟩, ?_⟩
        simp only [mem_singleton_iff] at ha₁
        rw [ha₁, unitInterval.coe_symm_eq]; simp
      · rintro ⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩
        refine ⟨((unitInterval.symm y : ℝ), b₁), ⟨rfl, hb₁⟩, ?_⟩
        simp only [mem_singleton_iff] at ha₁
        rw [ha₁, unitInterval.coe_symm_eq]; simp
    obtain ⟨c, hc, hdisj⟩ := no_M_below_left hX hi hE.symm' hπ
      (fun p q => (hπS p q).trans (layerSetoid_symm k p q).symm)
      (hγ.comp ((unitInterval.continuous_symm.isClosedEmbedding
        unitInterval.symm_involutive.injective).isEmbedding))
      (fun t x hx => hγπ _ x (by rw [← layer_symm]; exact hx)) hF.reverse
      (hFc.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)) hy1' hc₀ hvert'
      (a := 1 - b) (b := 1 - a) (by linarith)
      (by rw [unitInterval.coe_symm_eq]; linarith)
    refine ⟨c, hc, ?_⟩
    convert hdisj using 1
    ext p; constructor
    · rintro ⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩
      refine ⟨(1 - a₁, b₁), ⟨⟨by linarith [ha₁.2], by linarith [ha₁.1]⟩, hb₁⟩, ?_⟩
      simp
    · rintro ⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩
      exact ⟨(1 - a₁, b₁), ⟨⟨by linarith [ha₁.2], by linarith [ha₁.1]⟩, hb₁⟩, rfl⟩
  · push_neg at h
    exact no_M_below_left hX hi hE hπ hπS hγ hγπ hF hFc hy1 hc₀ hvert ha h

omit [CompactSpace M] [ConnectedSpace M] in
/-- **An adapted collar from an accessible layer** (the set-up of Lemma 9, p. 345: "We assume without
loss of generality that `π[E]` is lying on a horizontal line `B` in `R²` and `π[I − {y}]` is below `B`
on a vertical line"). If a point of the interior layer `k⁻¹(y)` is accessible from `R² − M` by an arc
`I`, then `π[I]` is an arc meeting `π[E]` only in `γ y`, and in the collar of `exists_collar_adapted`
the vertical below `γ y` misses `π[M]`. -/
theorem exists_collar_vertical {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Ico (-c) 0) ∩ π '' M = ∅ := by
  obtain ⟨p, hp, x, I, hI, hIM⟩ := hacc
  have hk := hE.2.1.2.1
  have hπc := hπ.continuous
  have hpI : (p : Pt) ∈ I := hI.right_mem
  have hoff : ∀ q ∈ I, q ≠ (p : Pt) → q ∉ M := fun q hq hqp hqM => by
    have : q ∈ I ∩ M := ⟨hq, hqM⟩
    rw [hIM] at this
    exact hqp this
  have hpE : (p : Pt) ∈ toPt E := by
    obtain ⟨e, -, he⟩ := hp
    exact ⟨p, he ▸ e.2, rfl⟩
  have hkey_off : ∀ q ∈ I, q ≠ (p : Pt) → layerKey k q = Sum.inr q := fun q hq hqp =>
    layerKey_of_notMem k fun ⟨m, _, hm⟩ => hoff q hq hqp (hm ▸ m.2)
  have hkey_p : ∃ t, layerKey k (p : Pt) = Sum.inl t := by
    obtain ⟨e, he⟩ := mem_toPt_iff.1 hpE
    exact ⟨k e, by rw [← he, layerKey_of_mem]⟩
  -- `π` is injective on `I`
  have hinj : InjOn π I := by
    intro q₁ h₁ q₂ h₂ he
    have hrel := (hπS q₁ q₂).1 he
    change layerKey k q₁ = layerKey k q₂ at hrel
    obtain ⟨t, ht⟩ := hkey_p
    by_cases e₁ : q₁ = (p : Pt) <;> by_cases e₂ : q₂ = (p : Pt)
    · rw [e₁, e₂]
    · rw [e₁, ht, hkey_off q₂ h₂ e₂] at hrel; exact absurd hrel Sum.inl_ne_inr
    · rw [e₂, ht, hkey_off q₁ h₁ e₁] at hrel; exact absurd hrel Sum.inr_ne_inl
    · rw [hkey_off q₁ h₁ e₁, hkey_off q₂ h₂ e₂] at hrel; exact Sum.inr_injective hrel
  have hπp : π (p : Pt) = γ y := hγπ y _ ⟨p, hp, rfl⟩
  have hπI : TArc (π x) (γ y) (π '' I) := by
    have := tarc_image_of_injOn hπc.continuousOn hinj hI subset_rfl
    rwa [hπp] at this
  -- a point of `I` over `π[E]` is `p`
  have hoverE : ∀ q ∈ I, ∀ m : M, π q = π m → q = (p : Pt) := by
    intro q hq m hqm
    by_contra hqp
    have hrel := (hπS q m).1 hqm
    change layerKey k q = layerKey k (m : Pt) at hrel
    rw [hkey_off q hq hqp] at hrel
    by_cases hmE : (m : Pt) ∈ toPt E
    · obtain ⟨e, he⟩ := mem_toPt_iff.1 hmE
      rw [← he, layerKey_of_mem] at hrel
      exact Sum.inr_ne_inl hrel
    · rw [layerKey_of_notMem k hmE] at hrel
      have := Sum.inr_injective hrel
      exact hoff q hq hqp (this ▸ m.2)
  have hπIγ : π '' I ∩ range γ = {γ y} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨q, hq, rfl⟩, ⟨t, ht⟩⟩
      obtain ⟨e, he⟩ := hk t
      have hm : π q = π ((e : M) : Pt) := by rw [← ht, hγπ t _ ⟨e, ⟨e, he, rfl⟩, rfl⟩]
      rw [hoverE q hq _ hm]; exact hπp
    · rintro _ rfl
      exact ⟨⟨p, hpI, hπp⟩, mem_range_self y⟩
  obtain ⟨F, hF, c, hc, hFI⟩ := exists_collar_adapted_aux hγ hy0 hy1 hπI hπIγ
  refine ⟨F, hF, min c 1, lt_min hc one_pos, ?_⟩
  rw [eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨⟨x₁, s₁⟩, ⟨hx₁, hs₁⟩, rfl⟩, ⟨m, hm, hme⟩⟩
  have hx₁' : x₁ = y := hx₁
  subst hx₁'
  obtain ⟨q, hq, hqe⟩ := hFI ⟨((y : ℝ), s₁), ⟨rfl, ⟨le_trans (neg_le_neg (min_le_left _ _)) hs₁.1,
    hs₁.2.le⟩⟩, rfl⟩
  have hqp := hoverE q hq ⟨m, hm⟩ (hqe.trans hme.symm)
  rw [hqp, hπp] at hqe
  -- `F (y, s₁) = γ y = F (y, 0)` with `s₁ < 0`
  obtain ⟨hemb, h0, -⟩ := hF
  have hK1 : ((y : ℝ), s₁) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨y.2, by linarith [hs₁.1, min_le_right c 1], by linarith [hs₁.2]⟩
  have hK2 : ((y : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := ⟨y.2, by norm_num, by norm_num⟩
  have := congrArg Subtype.val (hemb.injective (a₁ := ⟨_, hK1⟩) (a₂ := ⟨_, hK2⟩)
    (show F ((y : ℝ), s₁) = F ((y : ℝ), 0) by rw [← hqe, h0]))
  have := congrArg Prod.snd this
  simp only at this
  linarith [hs₁.2]

end Main

end HPC.Hagopian
