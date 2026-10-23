import HPC.Jones.Jones75A

/-!
# Jones 1975 II (batch 190), part 1: collar coordinates and passes

Commission 190 §2. Collar coordinates (`collarCoord`), passes of a box (`IsPass`), the property
(Mon) (`PassMon`), thin, upper and lower passes, and the facts (P1) (`IsPass.disjoint`),
(P2) (`IsPass.finite`, `exists_first_pass`), (P3) (`isPass_base`), (P4) (`IsPass.above_or_below`),
and the transfer of all of these to the flipped collar `F̄(x, y) = F(x, −y)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- The closed rectangle `[0, 1] × [−1, 1]` on which a collar is an embedding. -/
abbrev cRect : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

/-- Collar coordinates of a point of `F([0, 1] × [−1, 1])`. -/
noncomputable def collarCoord (F : ℝ × ℝ → Pt) (p : Pt) : ℝ × ℝ :=
  Function.invFunOn F cRect p

section Coord

variable {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt}

theorem IsCollar.injOn (hF : IsCollar γ F) : InjOn F cRect := fun _ hz _ hw h =>
  collar_injOn hF hz hw h

theorem IsCollar.contOn (hF : IsCollar γ F) : ContinuousOn F cRect :=
  continuousOn_iff_continuous_restrict.2 hF.1.continuous

theorem collarCoord_mem {p : Pt} (hp : p ∈ F '' cRect) : collarCoord F p ∈ cRect :=
  Function.invFunOn_mem hp

theorem collarCoord_apply {p : Pt} (hp : p ∈ F '' cRect) : F (collarCoord F p) = p :=
  Function.invFunOn_eq hp

theorem collarCoord_eq (hF : IsCollar γ F) {p : Pt} {z : ℝ × ℝ} (hz : z ∈ cRect)
    (h : p = F z) : collarCoord F p = z := by
  subst h
  exact hF.injOn (collarCoord_mem ⟨z, hz, rfl⟩) hz (collarCoord_apply ⟨z, hz, rfl⟩)

theorem continuousOn_collarCoord (hF : IsCollar γ F) :
    ContinuousOn (collarCoord F) (F '' cRect) := by
  rw [continuousOn_iff_continuous_restrict]
  set g : F '' cRect → cRect := fun p => ⟨collarCoord F p, collarCoord_mem p.2⟩ with hg
  have hgc : Continuous g := by
    rw [hF.1.continuous_iff]
    have : (cRect.restrict F) ∘ g = fun p : F '' cRect => (p : Pt) := by
      funext p
      simp only [Function.comp, restrict, hg]
      exact collarCoord_apply p.2
    rw [this]
    exact continuous_subtype_val
  exact continuous_subtype_val.comp hgc

/-- Two points of the closed rectangle with different first coordinates have different images. -/
theorem IsCollar.ne_of_fst_ne (hF : IsCollar γ F) {z w : ℝ × ℝ} (hz : z ∈ cRect) (hw : w ∈ cRect)
    (h : z.1 ≠ w.1) : F z ≠ F w := fun e => h (congrArg Prod.fst (hF.injOn hz hw e))

theorem IsCollar.base (hF : IsCollar γ F) {ℓ : ℝ → Pt} (hγ : ∀ t : unitInterval, γ t = ℓ t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ℓ t = F (t, 0) := by
  have := hF.2.1 ⟨t, ht⟩
  rw [hγ] at this
  exact this.symm

end Coord

/-- An arc from a continuous injective map on a closed interval. -/
theorem tarc_of_injOn {X : Type*} [TopologicalSpace X] [T2Space X] {f : ℝ → X} {s t : ℝ}
    (hst : s < t) (hf : ContinuousOn f (Icc s t)) (hi : InjOn f (Icc s t)) :
    TArc (f s) (f t) (f '' Icc s t) := by
  have hts : 0 < t - s := sub_pos.mpr hst
  have hmem : ∀ u : unitInterval, s + (u : ℝ) * (t - s) ∈ Icc s t := fun u =>
    ⟨by nlinarith [u.2.1], by nlinarith [u.2.2]⟩
  set g : unitInterval → X := fun u => f (s + u * (t - s)) with hg
  have hgc : Continuous g :=
    hf.comp_continuous (by fun_prop) hmem
  have hgi : Function.Injective g := by
    intro u v h
    have := hi (hmem u) (hmem v) h
    apply Subtype.ext
    have h2 : (u : ℝ) * (t - s) = v * (t - s) := by linarith
    exact mul_right_cancel₀ hts.ne' h2
  have := TArc.of_inj hgc hgi
  have h0 : g 0 = f s := by simp [hg]
  have h1 : g 1 = f t := by simp [hg]
  rw [h0, h1] at this
  convert this using 1
  ext y
  constructor
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    refine ⟨⟨(w - s) / (t - s), div_nonneg (by linarith) hts.le,
      (div_le_one hts).mpr (by linarith)⟩, ?_⟩
    simp only [hg]
    congr 1
    field_simp
    ring
  · rintro ⟨u, rfl⟩
    exact ⟨_, hmem u, rfl⟩

section Passes

variable {M : Set Pt}

/-! ## §2. Passes -/

/-- A *pass* of the box of height `η`: `ℓ[a, b]` from the left edge `F({¼} × [−η, η])` to the right
edge `F({¾} × [−η, η])`, its interior in the open box `F((¼, ¾) × (−η, η))`. -/
def IsPass (F : ℝ × ℝ → Pt) (η : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  a < b ∧ (∃ y ∈ Icc (-η) η, (ℓ a : Pt) = F (1 / 4, y)) ∧
    (∃ y ∈ Icc (-η) η, (ℓ b : Pt) = F (3 / 4, y)) ∧
    ∀ s ∈ Ioo a b, (ℓ s : Pt) ∈ F '' (Ioo (1 / 4) (3 / 4) ×ˢ Ioo (-η) η)

/-- *(Mon)*: along `ℓ[a, b]` the first collar coordinate never falls back by `2κ` or more. -/
def PassMon (F : ℝ × ℝ → Pt) (κ : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ v' v, a ≤ v' → v' < v → v ≤ b → ∀ p' p : ℝ × ℝ,
    p' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
      (ℓ v' : Pt) = F p' → (ℓ v : Pt) = F p → p'.1 - 2 * κ < p.1

/-- A pass is *thin* (for the height `η₂`) if it lies in `F([¼, ¾] × [−η₂, η₂])`. -/
def PassThin (F : ℝ × ℝ → Pt) (η₂ : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, (ℓ s : Pt) ∈ F '' (Icc (1 / 4) (3 / 4) ×ˢ Icc (-η₂) η₂)

/-- `ℓ[a, b]` lies, end points included, in the upper half `F([0, 1] × (0, 1])`. -/
def PassAbove (F : ℝ × ℝ → Pt) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∃ z ∈ cRect, 0 < z.2 ∧ (ℓ s : Pt) = F z

/-- `ℓ[a, b]` lies, end points included, in the lower half `F([0, 1] × [−1, 0))`. -/
def PassBelow (F : ℝ × ℝ → Pt) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∃ z ∈ cRect, z.2 < 0 ∧ (ℓ s : Pt) = F z

variable {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} {ℓ : ℝ → M}

theorem box_sub_cRect {η : ℝ} (hη : η ≤ 1) :
    Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Icc (-η) η ⊆ cRect := fun z ⟨⟨h1, h2⟩, h3, h4⟩ =>
  ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Every point of a pass has collar coordinates in the closed box. -/
theorem IsPass.mem_box {η : ℝ} {a b : ℝ} (h : IsPass F η ℓ a b) {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ z ∈ Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Icc (-η) η, (ℓ s : Pt) = F z := by
  obtain ⟨hab, ⟨ya, hya, ha⟩, ⟨yb, hyb, hb⟩, hint⟩ := h
  rcases eq_or_lt_of_le hs.1 with rfl | h1
  · exact ⟨_, ⟨⟨le_rfl, by norm_num⟩, hya⟩, ha⟩
  rcases eq_or_lt_of_le hs.2 with rfl | h2
  · exact ⟨_, ⟨⟨by norm_num, le_rfl⟩, hyb⟩, hb⟩
  obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := hint s ⟨h1, h2⟩
  exact ⟨z, ⟨Ioo_subset_Icc_self hz1, Ioo_subset_Icc_self hz2⟩, hz.symm⟩

theorem IsPass.mem_rect {η : ℝ} (hη : η ≤ 1) {a b : ℝ} (h : IsPass F η ℓ a b) {s : ℝ}
    (hs : s ∈ Icc a b) : (ℓ s : Pt) ∈ F '' cRect := by
  obtain ⟨z, hz, e⟩ := h.mem_box hs
  exact ⟨z, box_sub_cRect hη hz, e.symm⟩

/-- Collar coordinates of the points of the line. -/
noncomputable abbrev lc (F : ℝ × ℝ → Pt) (ℓ : ℝ → M) (t : ℝ) : ℝ × ℝ := collarCoord F (ℓ t : Pt)

theorem lc_eq (hF : IsCollar γ F) {t : ℝ} {z : ℝ × ℝ} (hz : z ∈ cRect) (h : (ℓ t : Pt) = F z) :
    lc F ℓ t = z :=
  collarCoord_eq hF hz h

theorem continuousOn_lc (hF : IsCollar γ F) (hℓ : Continuous ℓ) {T : Set ℝ}
    (hT : ∀ t ∈ T, (ℓ t : Pt) ∈ F '' cRect) : ContinuousOn (lc F ℓ) T :=
  (continuousOn_collarCoord hF).comp (continuous_subtype_val.comp hℓ).continuousOn hT

theorem IsPass.lc_box (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b : ℝ} (h : IsPass F η ℓ a b)
    {s : ℝ} (hs : s ∈ Icc a b) :
    lc F ℓ s ∈ Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Icc (-η) η ∧ F (lc F ℓ s) = ℓ s := by
  obtain ⟨z, hz, e⟩ := h.mem_box hs
  rw [lc_eq hF (box_sub_cRect hη hz) e]
  exact ⟨hz, e.symm⟩

theorem IsPass.lc_left (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b : ℝ}
    (h : IsPass F η ℓ a b) : (lc F ℓ a).1 = 1 / 4 := by
  obtain ⟨y, hy, e⟩ := h.2.1
  rw [lc_eq hF (box_sub_cRect hη ⟨⟨le_rfl, by norm_num⟩, hy⟩) e]

theorem IsPass.lc_right (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b : ℝ}
    (h : IsPass F η ℓ a b) : (lc F ℓ b).1 = 3 / 4 := by
  obtain ⟨y, hy, e⟩ := h.2.2.1
  rw [lc_eq hF (box_sub_cRect hη ⟨⟨by norm_num, le_rfl⟩, hy⟩) e]

theorem IsPass.lc_int (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b : ℝ}
    (h : IsPass F η ℓ a b) {s : ℝ} (hs : s ∈ Ioo a b) :
    lc F ℓ s ∈ Ioo (1 / 4 : ℝ) (3 / 4) ×ˢ Ioo (-η) η := by
  obtain ⟨z, hz, e⟩ := h.2.2.2 s hs
  rw [lc_eq hF (box_sub_cRect hη ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩) e.symm]
  exact hz

theorem IsPass.continuousOn_lc (hF : IsCollar γ F) (hℓ : Continuous ℓ) {η : ℝ} (hη : η ≤ 1)
    {a b : ℝ} (h : IsPass F η ℓ a b) : ContinuousOn (lc F ℓ) (Icc a b) :=
  HPC.Hagopian.continuousOn_lc hF hℓ fun _ ht => h.mem_rect hη ht

/-- The core of (P1): a pass starting inside another one is that pass. -/
theorem IsPass.eq_of_le (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b a' b' : ℝ}
    (h : IsPass F η ℓ a b) (h' : IsPass F η ℓ a' b') (haa : a ≤ a') (hab : a' ≤ b) :
    (a, b) = (a', b') := by
  have hl := h.lc_left hF hη
  have hl' := h'.lc_left hF hη
  have hr := h.lc_right hF hη
  have hr' := h'.lc_right hF hη
  rcases eq_or_lt_of_le haa with rfl | hlt
  · rcases lt_trichotomy b b' with hbb | rfl | hbb
    · have := (h'.lc_int hF hη ⟨h.1, hbb⟩).1.2
      rw [hr] at this; exact absurd this (lt_irrefl _)
    · rfl
    · have := (h.lc_int hF hη ⟨h'.1, hbb⟩).1.2
      rw [hr'] at this; exact absurd this (lt_irrefl _)
  · rcases eq_or_lt_of_le hab with rfl | hlt2
    · rw [hl'] at hr; norm_num at hr
    · have := (h.lc_int hF hη ⟨hlt, hlt2⟩).1.1
      rw [hl'] at this; exact absurd this (lt_irrefl _)

/-- **§2.1, (P1)**: distinct passes have disjoint closed parameter intervals. -/
theorem IsPass.disjoint (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b a' b' : ℝ}
    (h : IsPass F η ℓ a b) (h' : IsPass F η ℓ a' b') (hne : (a, b) ≠ (a', b')) :
    Disjoint (Icc a b) (Icc a' b') := by
  rw [Set.disjoint_left]
  rintro t ⟨ht1, ht2⟩ ⟨ht1', ht2'⟩
  rcases le_total a a' with haa | haa
  · exact hne (h.eq_of_le hF hη h' haa (by linarith))
  · exact hne (h'.eq_of_le hF hη h haa (by linarith)).symm

/-- (P1), the form used most: passes whose closed intervals meet are equal. -/
theorem IsPass.eq_of_mem (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b a' b' : ℝ}
    (h : IsPass F η ℓ a b) (h' : IsPass F η ℓ a' b') {t : ℝ} (ht : t ∈ Icc a b)
    (ht' : t ∈ Icc a' b') : (a, b) = (a', b') := by
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint hF hη h' hne) ht ht'

/-- (P1): a pass through `u` and a different pass ending before `u` are ordered. -/
theorem IsPass.lt_of_mem (hF : IsCollar γ F) {η : ℝ} (hη : η ≤ 1) {a b a' b' : ℝ}
    (h : IsPass F η ℓ a b) (h' : IsPass F η ℓ a' b') {u : ℝ} (hu : u ∈ Icc a b) (hub : b' < u) :
    b' < a := by
  by_contra hle
  push_neg at hle
  have := h.eq_of_mem hF hη h' ⟨hle, by linarith [hu.2]⟩ ⟨by linarith [h'.1], le_rfl⟩
  simp only [Prod.mk.injEq] at this
  linarith [hu.2, this.2]

/-- **§2.1, (P3)**: the base pass `ℓ[¼, ¾]`. -/
theorem isPass_base (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) {η : ℝ}
    (hη : 0 < η) : IsPass F η ℓ (1 / 4) (3 / 4) := by
  have hb := fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
    hF.base (ℓ := fun t => (ℓ t : Pt)) (fun t => hγ t) ht
  refine ⟨by norm_num, ⟨0, ⟨by linarith, hη.le⟩, hb _ ⟨by norm_num, by norm_num⟩⟩,
    ⟨0, ⟨by linarith, hη.le⟩, hb _ ⟨by norm_num, by norm_num⟩⟩, fun s hs => ?_⟩
  exact ⟨(s, 0), ⟨hs, by linarith, hη⟩,
    (hb s ⟨by linarith [hs.1], by linarith [hs.2]⟩).symm⟩

/-- A pass through a point of the base arc `F([0, 1] × {0})` is the base pass. -/
theorem IsPass.eq_base_of (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) (hℓ : Function.Injective ℓ)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1) {a b : ℝ} (h : IsPass F η ℓ a b) {s x : ℝ}
    (hs : s ∈ Icc a b) (hx : x ∈ Icc (0 : ℝ) 1) (e : (ℓ s : Pt) = F (x, 0)) :
    (a, b) = (1 / 4, 3 / 4) := by
  have hb := hF.base (ℓ := fun t => (ℓ t : Pt)) (fun t => hγ t) hx
  have hsx : s = x := hℓ (Subtype.ext (e.trans hb.symm))
  subst hsx
  obtain ⟨z, hz, ez⟩ := h.mem_box hs
  have := hF.injOn (box_sub_cRect hη hz) ⟨hx, by norm_num, by norm_num⟩ (ez.symm.trans e)
  have h1 : s = z.1 := by rw [this]
  have hz1 := hz.1
  rw [← h1] at hz1
  exact h.eq_of_mem hF hη (isPass_base hF hγ hη0) hs hz1

/-- **§2.1, (P4)**: a pass other than the base pass lies, end points included, strictly above or
strictly below the base arc. (Shape: the skeleton left this as `True`.) -/
theorem IsPass.above_or_below (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t)
    (hℓ : Continuous ℓ) (hℓi : Function.Injective ℓ) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1)
    {a b : ℝ} (h : IsPass F η ℓ a b) (hne : (a, b) ≠ (1 / 4, 3 / 4)) :
    PassAbove F ℓ a b ∨ PassBelow F ℓ a b := by
  set f : ℝ → ℝ := fun s => (lc F ℓ s).2 with hf
  have hfc : ContinuousOn f (Icc a b) :=
    continuous_snd.comp_continuousOn (h.continuousOn_lc hF hℓ hη)
  have hcoord := fun s (hs : s ∈ Icc a b) => h.lc_box hF hη hs
  have hf0 : ∀ s ∈ Icc a b, f s ≠ 0 := fun s hs e => by
    obtain ⟨hz, hF'⟩ := hcoord s hs
    have hx : (lc F ℓ s).1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have e' : (ℓ s : Pt) = F ((lc F ℓ s).1, 0) := by
      rw [← hF']; congr 1; exact Prod.ext rfl e
    exact hne (h.eq_base_of hF hγ hℓi hη0 hη hs hx e')
  have hab : a ∈ Icc a b := ⟨le_rfl, h.1.le⟩
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, 0 < f s → 0 < f t := fun s hs t ht hs0 => by
    by_contra hneg
    push_neg at hneg
    have hlt : f t < 0 := lt_of_le_of_ne hneg (hf0 t ht)
    have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
    obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (hfc.mono hsub)
      (show (0 : ℝ) ∈ uIcc (f s) (f t) from mem_uIcc.2 (Or.inr ⟨hlt.le, hs0.le⟩))
    exact hf0 c (hsub hc) hc0
  have mk : ∀ s ∈ Icc a b, ∃ z ∈ cRect, z.2 = f s ∧ (ℓ s : Pt) = F z := fun s hs =>
    ⟨lc F ℓ s, box_sub_cRect hη (hcoord s hs).1, rfl, (hcoord s hs).2.symm⟩
  rcases lt_or_gt_of_ne (hf0 a hab) with ha | ha
  · right
    intro s hs
    obtain ⟨z, hz, hz2, e⟩ := mk s hs
    refine ⟨z, hz, ?_, e⟩
    rw [hz2]
    rcases lt_or_gt_of_ne (hf0 s hs) with h1 | h1
    · exact h1
    · have := key s hs a hab h1; linarith
  · left
    intro s hs
    obtain ⟨z, hz, hz2, e⟩ := mk s hs
    exact ⟨z, hz, hz2 ▸ key a hab s hs ha, e⟩

theorem PassAbove.not_below (hF : IsCollar γ F) {a b : ℝ} (hab : a ≤ b) (h : PassAbove F ℓ a b)
    (h' : PassBelow F ℓ a b) : False := by
  obtain ⟨z, hz, hz0, e⟩ := h a ⟨le_rfl, hab⟩
  obtain ⟨w, hw, hw0, e'⟩ := h' a ⟨le_rfl, hab⟩
  have := hF.injOn hz hw (e.symm.trans e')
  rw [this] at hz0
  linarith

/-! ### (P2): passes in a bounded parameter interval -/

/-- Passes starting in `[−N, N]` have length at least some `ρ > 0`. -/
theorem IsPass.exists_length (hF : IsCollar γ F) (hℓ : Continuous ℓ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (N : ℝ) :
    ∃ ρ > 0, ∀ a b, IsPass F η ℓ a b → a ∈ Icc (-N) N → ρ ≤ b - a := by
  set EL : Set Pt := F '' ({1 / 4} ×ˢ Icc (-η) η) with hEL
  set ER : Set Pt := F '' ({3 / 4} ×ˢ Icc (-η) η) with hER
  have hsubL : ({1 / 4} ×ˢ Icc (-η) η : Set (ℝ × ℝ)) ⊆ cRect := fun z ⟨h1, h2⟩ => by
    simp only [mem_singleton_iff] at h1
    exact box_sub_cRect hη ⟨⟨by rw [h1], by rw [h1]; norm_num⟩, h2⟩
  have hsubR : ({3 / 4} ×ˢ Icc (-η) η : Set (ℝ × ℝ)) ⊆ cRect := fun z ⟨h1, h2⟩ => by
    simp only [mem_singleton_iff] at h1
    exact box_sub_cRect hη ⟨⟨by rw [h1]; norm_num, by rw [h1]⟩, h2⟩
  have hELc : IsCompact EL :=
    (isCompact_singleton.prod isCompact_Icc).image_of_continuousOn (hF.contOn.mono hsubL)
  have hERc : IsCompact ER :=
    (isCompact_singleton.prod isCompact_Icc).image_of_continuousOn (hF.contOn.mono hsubR)
  have hmemL : F (1 / 4, 0) ∈ EL := ⟨(1 / 4, 0), ⟨rfl, by linarith, hη0⟩, rfl⟩
  have hmemR : F (3 / 4, 0) ∈ ER := ⟨(3 / 4, 0), ⟨rfl, by linarith, hη0⟩, rfl⟩
  obtain ⟨⟨p0, q0⟩, ⟨hp0, hq0⟩, hmin⟩ := (hELc.prod hERc).exists_isMinOn
    ⟨(F (1 / 4, 0), F (3 / 4, 0)), hmemL, hmemR⟩ continuous_dist.continuousOn
  have hd0 : 0 < dist p0 q0 := by
    refine dist_pos.2 fun e => ?_
    obtain ⟨z, hz, rfl⟩ := hp0
    obtain ⟨w, hw, hw'⟩ := hq0
    refine hF.ne_of_fst_ne (hsubL hz) (hsubR hw) ?_ (e.trans hw'.symm)
    rw [hz.1, hw.1]; norm_num
  have hℓ' : Continuous fun t => (ℓ t : Pt) := continuous_subtype_val.comp hℓ
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -N) (b := N + 1)).uniformContinuousOn_of_continuous hℓ'.continuousOn)
    _ hd0
  refine ⟨min δ 1, lt_min hδ one_pos, fun a b h ha => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hb : b ∈ Icc (-N) (N + 1) :=
    ⟨by linarith [h.1, ha.1], by linarith [ha.2, min_le_right δ 1]⟩
  have hd := hδu a ⟨ha.1, by linarith [ha.2]⟩ b hb (by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [h.1])]
    linarith [min_le_left δ 1])
  obtain ⟨ya, hya, ea⟩ := h.2.1
  obtain ⟨yb, hyb, eb⟩ := h.2.2.1
  have := isMinOn_iff.1 hmin ((ℓ a : Pt), (ℓ b : Pt))
    ⟨⟨(1 / 4, ya), ⟨rfl, hya⟩, ea.symm⟩, ⟨(3 / 4, yb), ⟨rfl, hyb⟩, eb.symm⟩⟩
  simp only at this
  linarith

/-- **§2.1, (P2)**: only finitely many passes meet a bounded parameter interval. -/
theorem IsPass.finite (hF : IsCollar γ F) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1)
    (hℓ : Continuous ℓ) (N : ℝ) :
    {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 ≤ N ∧ -N ≤ ab.2}.Finite := by
  obtain ⟨ρ, hρ, hlen⟩ := IsPass.exists_length hF hℓ hη0.le hη N
  have hsplit : {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 ≤ N ∧ -N ≤ ab.2} ⊆
      {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 < -N ∧ -N ≤ ab.2} ∪
      {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 ∈ Icc (-N) N} := by
    rintro ⟨a, b⟩ ⟨h, h1, h2⟩
    rcases lt_or_ge a (-N) with h3 | h3
    · exact Or.inl ⟨h, h3, h2⟩
    · exact Or.inr ⟨h, h3, h1⟩
  refine Set.Finite.subset (Set.Finite.union ?_ ?_) hsplit
  · refine Set.Subsingleton.finite ?_
    rintro ⟨a, b⟩ ⟨h, h1, h2⟩ ⟨a', b'⟩ ⟨h', h1', h2'⟩
    exact h.eq_of_mem hF hη h' ⟨h1.le, h2⟩ ⟨h1'.le, h2'⟩
  · have key : ∀ a b a' b', IsPass F η ℓ a b → IsPass F η ℓ a' b' → a ∈ Icc (-N) N → a < a' →
        ⌊a / ρ⌋ < ⌊a' / ρ⌋ := by
      intro a b a' b' h h' ha haa
      have hba : b < a' := by
        by_contra hle
        push_neg at hle
        have := h.eq_of_le hF hη h' haa.le hle
        simp only [Prod.mk.injEq] at this
        linarith [this.1]
      have := hlen a b h ha
      have h1 : a / ρ + 1 < a' / ρ := by
        rw [div_add_one hρ.ne', div_lt_div_iff_of_pos_right hρ]
        linarith
      have h2 := Int.floor_le (a / ρ)
      have h3 := Int.lt_floor_add_one (a' / ρ)
      have : (⌊a / ρ⌋ : ℝ) < ⌊a' / ρ⌋ := by linarith
      exact_mod_cast this
    refine Set.Finite.of_finite_image (f := fun ab : ℝ × ℝ => ⌊ab.1 / ρ⌋) ?_ ?_
    · refine (Set.finite_Icc ⌊-N / ρ⌋ ⌊N / ρ⌋).subset ?_
      rintro _ ⟨⟨a, b⟩, ⟨h, h1, h2⟩, rfl⟩
      exact ⟨Int.floor_mono (div_le_div_of_nonneg_right h1 hρ.le),
        Int.floor_mono (div_le_div_of_nonneg_right h2 hρ.le)⟩
    · rintro ⟨a, b⟩ ⟨h, ha⟩ ⟨a', b'⟩ ⟨h', ha'⟩ e
      simp only at e
      rcases lt_trichotomy a a' with hl | rfl | hl
      · exact absurd e (key a b a' b' h h' ha hl).ne
      · exact h.eq_of_mem hF hη h' ⟨le_rfl, h.1.le⟩ ⟨le_rfl, h'.1.le⟩
      · exact absurd e (key a' b' a b h' h ha' hl).ne'

/-- (P2), the form used: among the passes satisfying `Q` and starting after `c` (if any) there is
one that starts first. -/
theorem exists_first_pass (hF : IsCollar γ F) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1)
    (hℓ : Continuous ℓ) (Q : ℝ → ℝ → Prop) (c : ℝ)
    (h : ∃ a b, IsPass F η ℓ a b ∧ Q a b ∧ c < a) :
    ∃ a b, IsPass F η ℓ a b ∧ Q a b ∧ c < a ∧
      ∀ a' b', IsPass F η ℓ a' b' → Q a' b' → c < a' → a ≤ a' := by
  obtain ⟨a₀, b₀, h₀, hQ₀, hc₀⟩ := h
  set N := max |a₀| |c| + 1 with hN
  set T := {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ Q ab.1 ab.2 ∧ c < ab.1 ∧ ab.1 ≤ a₀} with hT
  have hTf : T.Finite := by
    refine (IsPass.finite hF hη0 hη hℓ N).subset ?_
    rintro ⟨a, b⟩ ⟨h, -, h2, h3⟩
    refine ⟨h, ?_, ?_⟩
    · have := le_abs_self a₀; have := le_max_left |a₀| |c|; simp only; linarith
    · have := neg_abs_le c; have := le_max_right |a₀| |c|; have := h.1; simp only at h2 ⊢
      linarith
  obtain ⟨⟨a, b⟩, ⟨h, hQ, hc, -⟩, hmin⟩ :=
    Set.exists_min_image T Prod.fst hTf ⟨(a₀, b₀), h₀, hQ₀, hc₀, le_rfl⟩
  refine ⟨a, b, h, hQ, hc, fun a' b' h' hQ' hc' => ?_⟩
  rcases le_total a' a₀ with h1 | h1
  · exact hmin (a', b') ⟨h', hQ', hc', h1⟩
  · exact le_trans (hmin (a₀, b₀) ⟨h₀, hQ₀, hc₀, le_rfl⟩) h1

/-! ### The flipped collar -/

/-- The collar turned upside down, `F̄(x, y) = F(x, −y)` (`IsCollar.flip`). -/
abbrev flipC (F : ℝ × ℝ → Pt) : ℝ × ℝ → Pt := fun q => F (q.1, -q.2)

theorem flipC_flipC (F : ℝ × ℝ → Pt) : flipC (flipC F) = F := by
  funext q; simp [flipC]

theorem flipC_image (F : ℝ × ℝ → Pt) {B : Set (ℝ × ℝ)} (hB : ∀ q ∈ B, (q.1, -q.2) ∈ B) :
    flipC F '' B = F '' B := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨(q.1, -q.2), hB q hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨(q.1, -q.2), hB q hq, by simp [flipC]⟩

theorem symm_prod {A : Set ℝ} {η : ℝ} (B : Set ℝ) (hB : B = Icc (-η) η ∨ B = Ioo (-η) η) :
    ∀ q ∈ A ×ˢ B, (q.1, -q.2) ∈ A ×ˢ B := by
  rintro q ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rcases hB with rfl | rfl
  · exact ⟨by linarith [h2.2], by linarith [h2.1]⟩
  · exact ⟨by linarith [h2.2], by linarith [h2.1]⟩

theorem IsPass.flip {η : ℝ} {a b : ℝ} (h : IsPass F η ℓ a b) : IsPass (flipC F) η ℓ a b := by
  obtain ⟨hab, ⟨ya, hya, ea⟩, ⟨yb, hyb, eb⟩, hint⟩ := h
  refine ⟨hab, ⟨-ya, ⟨by linarith [hya.2], by linarith [hya.1]⟩, by simp [flipC, ea]⟩,
    ⟨-yb, ⟨by linarith [hyb.2], by linarith [hyb.1]⟩, by simp [flipC, eb]⟩, fun s hs => ?_⟩
  rw [flipC_image F (symm_prod _ (Or.inr rfl))]
  exact hint s hs

theorem PassThin.flip {η₂ : ℝ} {a b : ℝ} (h : PassThin F η₂ ℓ a b) :
    PassThin (flipC F) η₂ ℓ a b := by
  intro s hs
  rw [flipC_image F (symm_prod _ (Or.inl rfl))]
  exact h s hs

theorem PassMon.flip {κ : ℝ} {a b : ℝ} (h : PassMon F κ ℓ a b) : PassMon (flipC F) κ ℓ a b := by
  intro v' v h1 h2 h3 p' p hp' hp e' e
  have hsym : ∀ q ∈ cRect, (q.1, -q.2) ∈ cRect := symm_prod _ (Or.inl rfl)
  exact h v' v h1 h2 h3 (p'.1, -p'.2) (p.1, -p.2) (hsym p' hp') (hsym p hp) e' e

theorem PassBelow.flip {a b : ℝ} (h : PassBelow F ℓ a b) : PassAbove (flipC F) ℓ a b := by
  intro s hs
  obtain ⟨z, hz, hz0, e⟩ := h s hs
  exact ⟨(z.1, -z.2), symm_prod _ (Or.inl rfl) z hz, by simp only; linarith, by simp [flipC, e]⟩

theorem PassAbove.flip {a b : ℝ} (h : PassAbove F ℓ a b) : PassBelow (flipC F) ℓ a b := by
  intro s hs
  obtain ⟨z, hz, hz0, e⟩ := h s hs
  exact ⟨(z.1, -z.2), symm_prod _ (Or.inl rfl) z hz, by simp only; linarith, by simp [flipC, e]⟩

theorem PassAbove.of_flip {a b : ℝ} (h : PassAbove (flipC F) ℓ a b) : PassBelow F ℓ a b := by
  have := h.flip; rwa [flipC_flipC] at this

end Passes

end HPC.Hagopian
