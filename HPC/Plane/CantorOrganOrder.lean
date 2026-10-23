import HPC.Plane.CantorOrganCont
import HPC.Plane.NonCut51Gen

/-!
# Batch 97: the Cantor organ, part four — the linear order

Each subcontinuum meets each layer in a connected set (`isPreconnected_inter_layer`). Ordering
the points by `(F s, position of s in its layer)` lexicographically, every subcontinuum is
order-convex (`ordConvex_of_continuum`) and every order-convex set is connected
(`isPreconnected_of_ordConvex`). Hereditary unicoherence, atriodicity and hereditary
decomposability follow in `HPC/Plane/CantorOrganBing.lean`.
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-! ## Extending to a side -/

/-- A subcontinuum reaching left of the layer `t` contains its left strand. -/
theorem strand_lft_subset {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {h₀ h : Organ} (hh₀ : h₀ ∈ H) (hh : h ∈ H) (h₀t : F h₀ < t)
    (hht : F h = t) : strand (lft t) ⊆ H := by
  obtain ⟨hl1, hl2⟩ := lft_spec ht
  have hpos : 0 < lam (lft t) := by rw [hl1]; linarith [(F_mem h₀).1]
  rintro _ ⟨y, -, rfl⟩
  have := pt_mem_closure_left (frequently_true hl2 hpos) (show F h₀ < lam (lft t) by
    rw [hl1]; exact h₀t) y
  refine closure_minimal (fun p hp => ?_) hH this
  exact mem_of_F_between hH hHc hh₀ hh hp.1 (by rw [hht, ← hl1]; exact hp.2)

/-- A subcontinuum reaching right of the layer `t` contains its right strand. -/
theorem strand_rgt_subset {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {h₀ h : Organ} (hh₀ : h₀ ∈ H) (hh : h ∈ H) (h₀t : t < F h₀)
    (hht : F h = t) : strand (rgt t) ⊆ H := by
  obtain ⟨hr1, hr2⟩ := rgt_spec ht
  have hlt : lam (rgt t) < 1 := by rw [hr1]; linarith [(F_mem h₀).2]
  rintro _ ⟨y, -, rfl⟩
  have := pt_mem_closure_right (frequently_false hr2 hlt) (show lam (rgt t) < F h₀ by
    rw [hr1]; exact h₀t) y
  refine closure_minimal (fun p hp => ?_) hH this
  exact mem_of_F_between hH hHc hh hh₀ (by rw [hht, ← hr1]; exact hp.1) hp.2

theorem strand_lft_subset_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : strand (lft t) ⊆ layer t := by
  rw [layer_eq ht]; exact subset_union_left

theorem strand_rgt_subset_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : strand (rgt t) ⊆ layer t := by
  rw [layer_eq ht]; exact subset_union_right

theorem strands_meet {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (strand (lft t) ∩ strand (rgt t)).Nonempty := by
  rcases lft_eq_or_pair ht with h | h
  · exact ⟨pt (lft t) 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [h]⟩⟩
  · exact ⟨pt (lft t) (gh t), ⟨gh t, gh_mem t, rfl⟩, ⟨gh t, gh_mem t, (pt_lft_gh h).symm⟩⟩

theorem isClosed_layer (t : ℝ) : IsClosed (layer t) := isClosed_singleton.preimage continuous_F

/-! ## A subcontinuum meets a layer in a connected set -/

/-- A preconnected set inside `T₁ ∪ T₂` (closed), missing `T₁ ∩ T₂`, lies in one of them. -/
theorem subset_or_subset_of_closed {S T₁ T₂ : Set Organ} (hS : IsPreconnected S)
    (h1 : IsClosed T₁) (h2 : IsClosed T₂) (hcov : S ⊆ T₁ ∪ T₂) (hdis : S ∩ (T₁ ∩ T₂) = ∅) :
    S ⊆ T₁ ∨ S ⊆ T₂ := by
  by_contra hno
  push_neg at hno
  obtain ⟨⟨a, haS, haT⟩, ⟨b, hbS, hbT⟩⟩ := (show (∃ a ∈ S, a ∉ T₁) ∧ ∃ b ∈ S, b ∉ T₂ from
    ⟨not_subset.mp hno.1, not_subset.mp hno.2⟩)
  have hS1 : (S ∩ T₁).Nonempty := ⟨b, hbS, (hcov hbS).resolve_right hbT⟩
  have hS2 : (S ∩ T₂).Nonempty := ⟨a, haS, (hcov haS).resolve_left haT⟩
  have := isPreconnected_closed_iff.mp hS _ _ h1 h2 hcov hS1 hS2
  rw [hdis] at this; exact this.ne_empty rfl

theorem inter_layer_aux {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H) {t : ℝ}
    {A B : Set Organ} (hA : IsClosed A) (hB : IsClosed B) (hcov : H ∩ layer t ⊆ A ∪ B)
    (hA' : (H ∩ layer t ∩ A).Nonempty) (hB' : (H ∩ layer t ∩ B).Nonempty)
    (hdis : H ∩ layer t ∩ (A ∩ B) = ∅)
    (hl : closure (H ∩ F ⁻¹' Iio t) ∩ layer t ⊆ A)
    (hr : closure (H ∩ F ⁻¹' Ioi t) ∩ layer t ⊆ A) : False := by
  set X := H ∩ layer t ∩ B
  set Y := (H ∩ layer t ∩ A) ∪ closure (H ∩ F ⁻¹' Iio t) ∪ closure (H ∩ F ⁻¹' Ioi t)
  have hX : IsClosed X := (hH.inter (isClosed_layer t)).inter hB
  have hY : IsClosed Y :=
    (((hH.inter (isClosed_layer t)).inter hA).union isClosed_closure).union isClosed_closure
  have hcovH : H ⊆ X ∪ Y := by
    intro s hs
    rcases lt_trichotomy (F s) t with h | h | h
    · exact Or.inr (Or.inl (Or.inr (subset_closure ⟨hs, h⟩)))
    · rcases hcov ⟨hs, h⟩ with h' | h'
      · exact Or.inr (Or.inl (Or.inl ⟨⟨hs, h⟩, h'⟩))
      · exact Or.inl ⟨⟨hs, h⟩, h'⟩
    · exact Or.inr (Or.inr (subset_closure ⟨hs, h⟩))
  have hHX : (H ∩ X).Nonempty := by
    obtain ⟨s, hs⟩ := hB'; exact ⟨s, hs.1.1, hs⟩
  have hHY : (H ∩ Y).Nonempty := by
    obtain ⟨s, hs⟩ := hA'; exact ⟨s, hs.1.1, Or.inl (Or.inl hs)⟩
  obtain ⟨s, -, hsX, hsY⟩ := isPreconnected_closed_iff.mp hHc _ _ hX hY hcovH hHX hHY
  have hsA : s ∈ A := by
    rcases hsY with (hs | hs) | hs
    · exact hs.2
    · exact hl ⟨hs, hsX.1.2⟩
    · exact hr ⟨hs, hsX.1.2⟩
  have : s ∈ H ∩ layer t ∩ (A ∩ B) := ⟨hsX.1, hsA, hsX.2⟩
  rw [hdis] at this; exact this

/-- **A subcontinuum meets every layer in a connected set.** -/
theorem isPreconnected_inter_layer {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : IsPreconnected (H ∩ layer t) := by
  rw [isPreconnected_closed_iff]
  intro T₁ T₂ h1 h2 hcov hT₁ hT₂
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  -- a strand inside `H ∩ layer t` lies in `T₁` or in `T₂`
  have hside : ∀ S, S ⊆ H ∩ layer t → IsPreconnected S → S ⊆ T₁ ∨ S ⊆ T₂ := by
    intro S hS hSc
    refine subset_or_subset_of_closed hSc h1 h2 (hS.trans hcov) ?_
    rw [← subset_empty_iff, ← hne]
    exact inter_subset_inter_left _ hS
  obtain ⟨h, hhH, hht⟩ := hT₁.mono inter_subset_left |>.mono (subset_refl _) |> fun ⟨s, hs⟩ =>
    (⟨s, hs.1, hs.2⟩ : ∃ s, s ∈ H ∧ s ∈ layer t)
  -- which side the left and right limits go to
  have hL : (H ∩ F ⁻¹' Iio t).Nonempty →
      strand (lft t) ⊆ H ∩ layer t ∧ closure (H ∩ F ⁻¹' Iio t) ∩ layer t ⊆ strand (lft t) := by
    rintro ⟨h₀, hh₀H, hh₀⟩
    refine ⟨fun p hp => ⟨strand_lft_subset hH hHc ht hh₀H hhH hh₀ hht hp,
      strand_lft_subset_layer ht hp⟩, ?_⟩
    exact (inter_subset_inter_left _ (closure_mono inter_subset_right)).trans
      (closure_left_inter_layer ht)
  have hR : (H ∩ F ⁻¹' Ioi t).Nonempty →
      strand (rgt t) ⊆ H ∩ layer t ∧ closure (H ∩ F ⁻¹' Ioi t) ∩ layer t ⊆ strand (rgt t) := by
    rintro ⟨h₀, hh₀H, hh₀⟩
    refine ⟨fun p hp => ⟨strand_rgt_subset hH hHc ht hh₀H hhH hh₀ hht hp,
      strand_rgt_subset_layer ht hp⟩, ?_⟩
    exact (inter_subset_inter_left _ (closure_mono inter_subset_right)).trans
      (closure_right_inter_layer ht)
  have hT₁' : (H ∩ layer t ∩ T₁).Nonempty := hT₁
  have hT₂' : (H ∩ layer t ∩ T₂).Nonempty := hT₂
  have hne' : H ∩ layer t ∩ (T₁ ∩ T₂) = ∅ := hne
  have hdis' : H ∩ layer t ∩ (T₂ ∩ T₁) = ∅ := by rw [inter_comm T₂]; exact hne
  have hcov' : H ∩ layer t ⊆ T₂ ∪ T₁ := by rw [union_comm]; exact hcov
  -- the strands meet, so they go to the same side
  obtain ⟨q, hqL, hqR⟩ := strands_meet ht
  have same : ∀ {U V : Set Organ}, H ∩ layer t ∩ (U ∩ V) = ∅ →
      (H ∩ F ⁻¹' Iio t).Nonempty → (H ∩ F ⁻¹' Ioi t).Nonempty →
      strand (lft t) ⊆ U → strand (rgt t) ⊆ V → False := by
    intro U V hUV hl hr hU hV
    have hq : q ∈ H ∩ layer t ∩ (U ∩ V) := ⟨(hL hl).1 hqL, hU hqL, hV hqR⟩
    rw [hUV] at hq; exact hq
  by_cases hl : (H ∩ F ⁻¹' Iio t).Nonempty
  · rcases hside _ (hL hl).1 (isPreconnected_strand _) with hs | hs
    · apply inter_layer_aux hH hHc h1 h2 hcov hT₁' hT₂' hne' ((hL hl).2.trans hs)
      by_cases hr : (H ∩ F ⁻¹' Ioi t).Nonempty
      · rcases hside _ (hR hr).1 (isPreconnected_strand _) with hs' | hs'
        · exact (hR hr).2.trans hs'
        · exact (same hne' hl hr hs hs').elim
      · rw [not_nonempty_iff_eq_empty.mp hr, closure_empty, empty_inter]; exact empty_subset _
    · apply inter_layer_aux hH hHc h2 h1 hcov' hT₂' hT₁' hdis' ((hL hl).2.trans hs)
      by_cases hr : (H ∩ F ⁻¹' Ioi t).Nonempty
      · rcases hside _ (hR hr).1 (isPreconnected_strand _) with hs' | hs'
        · exact (same hdis' hl hr hs hs').elim
        · exact (hR hr).2.trans hs'
      · rw [not_nonempty_iff_eq_empty.mp hr, closure_empty, empty_inter]; exact empty_subset _
  · rw [not_nonempty_iff_eq_empty] at hl
    have hl' : closure (H ∩ F ⁻¹' Iio t) ∩ layer t = ∅ := by
      rw [hl, closure_empty, empty_inter]
    by_cases hr : (H ∩ F ⁻¹' Ioi t).Nonempty
    · rcases hside _ (hR hr).1 (isPreconnected_strand _) with hs' | hs'
      · exact inter_layer_aux hH hHc h1 h2 hcov hT₁' hT₂' hne' (by rw [hl']; exact empty_subset _)
          ((hR hr).2.trans hs')
      · exact inter_layer_aux hH hHc h2 h1 hcov' hT₂' hT₁' hdis' (by rw [hl']; exact empty_subset _)
          ((hR hr).2.trans hs')
    · rw [not_nonempty_iff_eq_empty] at hr
      exact inter_layer_aux hH hHc h1 h2 hcov hT₁' hT₂' hne' (by rw [hl']; exact empty_subset _)
        (by rw [hr, closure_empty, empty_inter]; exact empty_subset _)

/-! ## The order -/

/-- The position of a point in its layer (the parameter of `gam`). -/
noncomputable def pos (s : Organ) : ℝ := Function.invFunOn (gam (F s)) (Icc 0 2) s

theorem pos_spec (s : Organ) : pos s ∈ Icc (0 : ℝ) 2 ∧ gam (F s) (pos s) = s := by
  have hs : s ∈ gam (F s) '' Icc 0 2 := by rw [image_gam (F_mem s)]; rfl
  exact ⟨Function.invFunOn_mem hs, Function.invFunOn_eq hs⟩

theorem F_gam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (τ : ℝ) : F (gam t τ) = t := gam_mem_layer ht τ

theorem pos_gam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 2) :
    pos (gam t τ) = τ := by
  have h := (pos_spec (gam t τ)).2
  rw [F_gam ht] at h
  have hm := (pos_spec (gam t τ)).1
  exact gam_injOn ht hm hτ h

theorem eq_of_F_pos {a b : Organ} (hF : F a = F b) (hp : pos a = pos b) : a = b := by
  rw [← (pos_spec a).2, ← (pos_spec b).2, hF, hp]

/-- The lexicographic key of a point. -/
noncomputable def key (s : Organ) : Lex (ℝ × ℝ) := toLex (F s, pos s)

theorem key_le_iff {a b : Organ} : key a ≤ key b ↔ F a < F b ∨ (F a = F b ∧ pos a ≤ pos b) :=
  Prod.Lex.toLex_le_toLex

theorem key_injective : Function.Injective key := by
  intro a b h
  have h' := congrArg ofLex h
  simp only [key, ofLex_toLex, Prod.mk.injEq] at h'
  exact eq_of_F_pos h'.1 h'.2

theorem F_le_of_key_le {a b : Organ} (h : key a ≤ key b) : F a ≤ F b := by
  rcases key_le_iff.mp h with h | h
  · exact h.le
  · exact h.1.le

/-- Order-convex sets. -/
def OrdConvex (X : Set Organ) : Prop :=
  ∀ a ∈ X, ∀ c ∈ X, ∀ b, key a ≤ key b → key b ≤ key c → b ∈ X

/-- Closed order intervals. -/
def Iv (a c : Organ) : Set Organ := {b | key a ≤ key b ∧ key b ≤ key c}

theorem isPreconnected_Iv (a c : Organ) : IsPreconnected (Iv a c) := by
  by_cases hac : key a ≤ key c
  swap
  · convert isPreconnected_empty
    ext b; simp only [Iv, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2; exact hac (h1.trans h2)
  rcases key_le_iff.mp hac with hlt | ⟨heq, hle⟩
  · -- different layers
    set tx := F a
    set tz := F c
    have htx : tx ∈ Icc (0 : ℝ) 1 := F_mem a
    have htz : tz ∈ Icc (0 : ℝ) 1 := F_mem c
    set Y := F ⁻¹' Ioo tx tz
    have hY : IsPreconnected Y := isPreconnected_preimage_F isPreconnected_Ioo
    have h2 : gam tx 2 ∈ closure Y := by
      obtain ⟨y, -, hy⟩ := (gam_two_mem (t := tx))
      rw [← hy]
      obtain ⟨hr1, hr2⟩ := rgt_spec htx
      have hlt1 : lam (rgt tx) < 1 := by rw [hr1]; linarith [htz.2]
      have := pt_mem_closure_right (frequently_false hr2 hlt1)
        (show lam (rgt tx) < tz by rw [hr1]; exact hlt) y
      rwa [hr1] at this
    have h0 : gam tz 0 ∈ closure Y := by
      obtain ⟨y, -, hy⟩ := (gam_zero_mem (t := tz))
      rw [← hy]
      obtain ⟨hl1, hl2⟩ := lft_spec htz
      have hpos : 0 < lam (lft tz) := by rw [hl1]; linarith [htx.1]
      have := pt_mem_closure_left (frequently_true hl2 hpos)
        (show tx < lam (lft tz) by rw [hl1]; exact hlt) y
      rwa [hl1] at this
    set Y' := Y ∪ {gam tx 2, gam tz 0}
    have hY' : IsPreconnected Y' := hY.subset_closure subset_union_left (union_subset subset_closure
      (insert_subset_iff.mpr ⟨h2, singleton_subset_iff.mpr h0⟩))
    have hP1 : IsPreconnected (gam tx '' Icc (pos a) 2) :=
      isPreconnected_Icc.image _ (continuous_gam htx).continuousOn
    have hP3 : IsPreconnected (gam tz '' Icc 0 (pos c)) :=
      isPreconnected_Icc.image _ (continuous_gam htz).continuousOn
    have hpa := (pos_spec a).1
    have hpc := (pos_spec c).1
    have hU : IsPreconnected (gam tx '' Icc (pos a) 2 ∪ Y') :=
      hP1.union (gam tx 2) ⟨2, ⟨hpa.2, le_rfl⟩, rfl⟩ (Or.inr (Or.inl rfl)) hY'
    have hU' : IsPreconnected ((gam tx '' Icc (pos a) 2 ∪ Y') ∪ gam tz '' Icc 0 (pos c)) :=
      hU.union (gam tz 0) (Or.inr (Or.inr (Or.inr rfl))) ⟨0, ⟨le_rfl, hpc.1⟩, rfl⟩ hP3
    convert hU' using 1
    ext b
    constructor
    · rintro ⟨hab, hbc⟩
      rcases key_le_iff.mp hab with h1 | ⟨h1, h1'⟩
      · rcases key_le_iff.mp hbc with h3 | ⟨h3, h3'⟩
        · exact Or.inl (Or.inr (Or.inl ⟨h1, h3⟩))
        · refine Or.inr ⟨pos b, ⟨(pos_spec b).1.1, h3'⟩, ?_⟩
          have := (pos_spec b).2; rwa [h3] at this
      · refine Or.inl (Or.inl ⟨pos b, ⟨h1', (pos_spec b).1.2⟩, ?_⟩)
        have := (pos_spec b).2; rwa [← h1] at this
    · rintro ((⟨τ, hτ, rfl⟩ | hY | hY) | ⟨τ, hτ, rfl⟩)
      · have hτ' : τ ∈ Icc (0 : ℝ) 2 := ⟨hpa.1.trans hτ.1, hτ.2⟩
        refine ⟨key_le_iff.mpr (Or.inr ⟨(F_gam htx τ).symm, by rw [pos_gam htx hτ']; exact hτ.1⟩),
          key_le_iff.mpr (Or.inl (by rw [F_gam htx]; exact hlt))⟩
      · exact ⟨key_le_iff.mpr (Or.inl hY.1), key_le_iff.mpr (Or.inl hY.2)⟩
      · rcases hY with hY | hY
        · rw [hY]
          refine ⟨key_le_iff.mpr (Or.inr ⟨(F_gam htx 2).symm, by
            rw [pos_gam htx ⟨by norm_num, le_rfl⟩]; exact hpa.2⟩),
            key_le_iff.mpr (Or.inl (by rw [F_gam htx]; exact hlt))⟩
        · rw [mem_singleton_iff] at hY
          rw [hY]
          refine ⟨key_le_iff.mpr (Or.inl (by rw [F_gam htz]; exact hlt)),
            key_le_iff.mpr (Or.inr ⟨F_gam htz 0, by
              rw [pos_gam htz ⟨le_rfl, by norm_num⟩]; exact hpc.1⟩)⟩
      · have hτ' : τ ∈ Icc (0 : ℝ) 2 := ⟨hτ.1, hτ.2.trans hpc.2⟩
        refine ⟨key_le_iff.mpr (Or.inl (by rw [F_gam htz]; exact hlt)),
          key_le_iff.mpr (Or.inr ⟨F_gam htz τ, by rw [pos_gam htz hτ']; exact hτ.2⟩)⟩
  · -- the same layer
    set t := F a
    have ht : t ∈ Icc (0 : ℝ) 1 := F_mem a
    convert (isPreconnected_Icc (a := pos a) (b := pos c)).image _
      (continuous_gam ht).continuousOn using 1
    have hpa := (pos_spec a).1
    have hpc := (pos_spec c).1
    ext b
    constructor
    · rintro ⟨hab, hbc⟩
      have hFb : F b = t := le_antisymm (heq ▸ F_le_of_key_le hbc) (F_le_of_key_le hab)
      have hpb1 : pos a ≤ pos b := by
        rcases key_le_iff.mp hab with h | h
        · exact absurd hFb (ne_of_gt h)
        · exact h.2
      have hpb2 : pos b ≤ pos c := by
        rcases key_le_iff.mp hbc with h | h
        · rw [hFb, heq] at h; exact absurd h (lt_irrefl _)
        · exact h.2
      refine ⟨pos b, ⟨hpb1, hpb2⟩, ?_⟩
      have := (pos_spec b).2; rwa [hFb] at this
    · rintro ⟨τ, hτ, rfl⟩
      have hτ' : τ ∈ Icc (0 : ℝ) 2 := ⟨hpa.1.trans hτ.1, hτ.2.trans hpc.2⟩
      refine ⟨key_le_iff.mpr (Or.inr ⟨(F_gam ht τ).symm, by rw [pos_gam ht hτ']; exact hτ.1⟩),
        key_le_iff.mpr (Or.inr ⟨by rw [F_gam ht τ, heq], by rw [pos_gam ht hτ']; exact hτ.2⟩)⟩

/-- **Order-convex sets are connected.** -/
theorem isPreconnected_of_ordConvex {X : Set Organ} (hX : OrdConvex X) : IsPreconnected X := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  rcases le_total (key x) (key y) with h | h
  · exact ⟨Iv x y, fun b hb => hX x hx y hy b hb.1 hb.2, ⟨le_rfl, h⟩, ⟨h, le_rfl⟩,
      isPreconnected_Iv x y⟩
  · exact ⟨Iv y x, fun b hb => hX y hy x hx b hb.1 hb.2, ⟨h, le_rfl⟩, ⟨le_rfl, h⟩,
      isPreconnected_Iv y x⟩

/-- Inside one layer, a subcontinuum contains everything between two of its points. -/
theorem mem_of_intra {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {p q b : Organ} (hp : p ∈ H) (hq : q ∈ H) (hpt : F p = t)
    (hqt : F q = t) (hbt : F b = t) (h1 : pos p ≤ pos b) (h2 : pos b ≤ pos q) : b ∈ H := by
  set e : Icc (0 : ℝ) 2 → Organ := fun τ => gam t τ
  have he : Continuous e := (continuous_gam ht).comp continuous_subtype_val
  have hinj : Function.Injective e := fun τ τ' h => Subtype.ext (gam_injOn ht τ.2 τ'.2 h)
  have hemb := he.isClosedEmbedding hinj
  have himg : e '' (e ⁻¹' H) = H ∩ layer t := by
    ext s
    constructor
    · rintro ⟨τ, hτ, rfl⟩; exact ⟨hτ, gam_mem_layer ht τ⟩
    · rintro ⟨hsH, hst⟩
      have hs : F s = t := hst
      refine ⟨⟨pos s, (pos_spec s).1⟩, ?_, ?_⟩
      · show gam t (pos s) ∈ H
        have := (pos_spec s).2; rw [hs] at this; rw [this]; exact hsH
      · show gam t (pos s) = s
        have := (pos_spec s).2; rwa [hs] at this
  have hP : IsPreconnected (e ⁻¹' H) := by
    rw [← hemb.isInducing.isPreconnected_image, himg]
    exact isPreconnected_inter_layer hH hHc ht
  have hP' : IsPreconnected (Subtype.val '' (e ⁻¹' H)) :=
    hP.image _ continuous_subtype_val.continuousOn
  have hmem : ∀ s, s ∈ H → F s = t → pos s ∈ Subtype.val '' (e ⁻¹' H) := by
    intro s hsH hs
    refine ⟨⟨pos s, (pos_spec s).1⟩, ?_, rfl⟩
    show gam t (pos s) ∈ H
    have := (pos_spec s).2; rw [hs] at this; rw [this]; exact hsH
  obtain ⟨τ, hτ, hτb⟩ := hP'.ordConnected.out (hmem p hp hpt) (hmem q hq hqt) ⟨h1, h2⟩
  have : e τ = b := by
    show gam t τ = b
    rw [hτb]; have := (pos_spec b).2; rwa [hbt] at this
  rw [← this]; exact hτ

/-- **Subcontinua are order-convex.** -/
theorem ordConvex_of_continuum {H : Set Organ} (hH : IsClosed H) (hHc : IsPreconnected H) :
    OrdConvex H := by
  intro a ha c hc b hab hbc
  rcases key_le_iff.mp hab with h1 | ⟨h1, h1'⟩ <;> rcases key_le_iff.mp hbc with h2 | ⟨h2, h2'⟩
  · exact mem_of_F_between hH hHc ha hc h1 h2
  · -- `F a < F b = F c`
    have ht := F_mem b
    have hg : gam (F b) 0 ∈ H :=
      strand_lft_subset hH hHc ht ha hc h1 h2.symm gam_zero_mem
    exact mem_of_intra hH hHc ht hg hc (F_gam ht 0) h2.symm rfl
      (by rw [pos_gam ht ⟨le_rfl, by norm_num⟩]; exact (pos_spec b).1.1) h2'
  · -- `F a = F b < F c`
    have ht := F_mem b
    have hg : gam (F b) 2 ∈ H :=
      strand_rgt_subset hH hHc ht hc ha h2 h1 gam_two_mem
    exact mem_of_intra hH hHc ht ha hg h1 (F_gam ht 2) rfl h1'
      (by rw [pos_gam ht ⟨by norm_num, le_rfl⟩]; exact (pos_spec b).1.2)
  · exact mem_of_intra hH hHc (F_mem b) ha hc h1 h2.symm rfl h1' h2'

end HPC.Plane.Org
