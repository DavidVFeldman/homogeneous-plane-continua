import HPC.Plane.Tree6Arcs

/-!
# Batch 118, auxiliary: cutting and splitting simple polygonal arcs

Parametrised segments, initial and final parts of a simple arc (`IsSArc.take`, `IsSArc.drop`,
`IsSArc.cut_left`, `IsSArc.cut_right`), and splitting a simple arc at a point (`IsSArc.split`).
-/

namespace HPC.Plane

open Set Metric

/-! ### Splitting a simple arc at a point -/

theorem segment_split_param {a b x : Pt} (hx : x ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a) := by
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hx
  exact ⟨t, h0, h1, rfl⟩

theorem mem_segment_left_part {a d : Pt} {t s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ t) :
    a + s • d ∈ segment ℝ a (a + t • d) := by
  rcases hs.lt_or_eq with h | h
  · rw [segment_eq_image']
    refine ⟨s / t, ⟨div_nonneg hs0 (by linarith), (div_le_one (by linarith)).2 hs⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ _ (by linarith)]
  · rw [h]; exact right_mem_segment _ _ _

theorem mem_segment_right_part {a d : Pt} {t s : ℝ} (ht : t ≤ s) (hs : s ≤ 1) :
    a + s • d ∈ segment ℝ (a + t • d) (a + d) := by
  rcases ht.lt_or_eq with h | h
  · rw [segment_eq_image']
    refine ⟨(s - t) / (1 - t), ⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
    have h1t : (1 : ℝ) - t ≠ 0 := by linarith
    simp only
    match_scalars <;> field_simp <;> ring
  · rw [← h]; exact left_mem_segment _ _ _

/-- A point of a segment splits it into two segments. -/
theorem segment_eq_union_of_mem {a b x : Pt} (hx : x ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a x ∪ segment ℝ x b := by
  apply subset_antisymm
  · obtain ⟨t, ht0, ht1, rfl⟩ := segment_split_param hx
    intro y hy
    obtain ⟨s, hs0, hs1, rfl⟩ := segment_split_param hy
    rcases le_total s t with h | h
    · exact Or.inl (mem_segment_left_part hs0 h)
    · right
      have := mem_segment_right_part (a := a) (d := b - a) h hs1
      rwa [add_sub_cancel] at this
  · exact union_subset ((convex_segment a b).segment_subset (left_mem_segment _ _ _) hx)
      ((convex_segment a b).segment_subset hx (right_mem_segment _ _ _))

theorem segment_param_inj {a d : Pt} (hd : d ≠ 0) {s s' : ℝ} (h : a + s • d = a + s' • d) :
    s = s' :=
  smul_left_injective ℝ hd (add_left_cancel h)

/-- The two parts of a segment at a point meet only there. -/
theorem segment_inter_of_mem {a b x : Pt} (hx : x ∈ segment ℝ a b) :
    segment ℝ a x ∩ segment ℝ x b = {x} := by
  apply subset_antisymm
  · obtain ⟨t, ht0, ht1, rfl⟩ := segment_split_param hx
    rintro y ⟨hy1, hy2⟩
    obtain ⟨s, hs0, hs1, rfl⟩ := segment_split_param hy1
    obtain ⟨s', hs0', hs1', hs'⟩ := segment_split_param hy2
    by_cases hd : b - a = 0
    · simp [hd]
    · have e1 : a + s • (a + t • (b - a) - a) = a + (s * t) • (b - a) := by
        module
      have e2 : a + t • (b - a) + s' • (b - (a + t • (b - a))) =
          a + (t + s' * (1 - t)) • (b - a) := by module
      rw [e1] at hs' ⊢
      rw [e2] at hs'
      have := segment_param_inj hd hs'
      have h1 : s * t ≤ t := by nlinarith
      have h2 : t ≤ t + s' * (1 - t) := by nlinarith
      have : s * t = t := by linarith
      rw [this]; rfl
  · rintro y rfl; exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- The start of a segment is not on the part after an interior point. -/
theorem left_not_mem_segment_part {a b x : Pt} (hx : x ∈ segment ℝ a b) (hxa : x ≠ a) :
    a ∉ segment ℝ x b := by
  obtain ⟨t, ht0, ht1, rfl⟩ := segment_split_param hx
  intro ha
  obtain ⟨s, hs0, hs1, hs⟩ := segment_split_param ha
  by_cases hd : b - a = 0
  · exact hxa (by simp [hd])
  · have e2 : a + t • (b - a) + s • (b - (a + t • (b - a))) =
        a + (t + s * (1 - t)) • (b - a) := by module
    rw [e2] at hs
    have := segment_param_inj hd (a := a) (s := 0) (s' := t + s * (1 - t)) (by simpa using hs)
    have ht : t = 0 := by nlinarith
    exact hxa (by simp [ht])

/-- The end of a segment is not on the part before an interior point. -/
theorem right_not_mem_segment_part {a b x : Pt} (hx : x ∈ segment ℝ a b) (hxb : x ≠ b) :
    b ∉ segment ℝ a x := by
  rw [segment_symm] at hx ⊢
  exact left_not_mem_segment_part hx hxb

theorem IsSArc.take {v : ℕ → Pt} {n k : ℕ} (h : IsSArc v n) (hk : 2 ≤ k) (hkn : k ≤ n) :
    IsSArc v k :=
  ⟨hk, fun i j hij hj => h.2.1 i j hij (by omega), fun i hi => h.2.2.1 i (by omega),
    fun i j hij hj => h.2.2.2 i j hij (by omega)⟩

theorem IsSArc.drop {v : ℕ → Pt} {n j : ℕ} (h : IsSArc v n) (hj : j + 2 ≤ n) :
    IsSArc (fun m => v (m + j)) (n - j) := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  refine ⟨by omega, fun a b hab hb => hd _ _ (by omega) (by omega), fun a ha => ?_,
    fun a b hab hb => ?_⟩
  · simp only
    rw [show a + 1 + j = a + j + 1 by omega, show a + 2 + j = a + j + 2 by omega]
    exact hc _ (by omega)
  · simp only
    rw [show a + 1 + j = a + j + 1 by omega, show b + 1 + j = b + j + 1 by omega]
    exact hnc _ _ (by omega) (by omega)

theorem vpath_drop_seg (v : ℕ → Pt) (j m : ℕ) :
    segment ℝ (v (m + j)) (v (m + 1 + j)) = segment ℝ (v (m + j)) (v (m + j + 1)) := by
  rw [show m + 1 + j = m + j + 1 by omega]

/-- Cutting a simple arc at a point `x` of its segment `i` (not a vertex up to `v i`): the part
from `v 0` to `x`. -/
theorem IsSArc.cut_left {v : ℕ → Pt} {n i : ℕ} (h : IsSArc v n) (hi : i + 1 < n) {x : Pt}
    (hx : x ∈ segment ℝ (v i) (v (i + 1))) (hxv : ∀ m, m ≤ i → x ≠ v m) :
    IsSArc (fun m => if m ≤ i then v m else x) (i + 2) := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  have hsub : segment ℝ (v i) x ⊆ segment ℝ (v i) (v (i + 1)) :=
    (convex_segment _ _).segment_subset (left_mem_segment _ _ _) hx
  set u : ℕ → Pt := fun m => if m ≤ i then v m else x with hu
  have hseg_u : ∀ m, m + 1 < i + 2 → segment ℝ (u m) (u (m + 1)) ⊆
      segment ℝ (v m) (v (m + 1)) := by
    intro m hm
    by_cases hm' : m + 1 ≤ i
    · simp [hu, hm', show m ≤ i by omega]
    · have : m = i := by omega
      subst this
      simpa [hu] using hsub
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro m m' hmm' hm'
    by_cases h' : m' ≤ i
    · simp only [hu, h', show m ≤ i by omega, if_true]
      exact hd m m' hmm' (by omega)
    · simp only [hu, h', show m ≤ i by omega, if_true, if_false]
      exact fun h'' => hxv m (by omega) h''.symm
  · intro m hm
    have h1 := hseg_u m (by omega)
    have h2 := hseg_u (m + 1) (by omega)
    have hum : u (m + 1) = v (m + 1) := by simp [hu, show m + 1 ≤ i by omega]
    rw [hum] at h1 h2 ⊢
    exact (inter_subset_inter h1 h2).trans (hc m (by omega))
  · intro m m' hmm' hm'
    exact (hnc m m' hmm' (by omega)).mono (hseg_u m (by omega)) (hseg_u m' (by omega))

/-- Cutting a simple arc at a point `x` of its segment `i` (not a vertex from `v (i+1)` on): the
part from `x` to the end. -/
theorem IsSArc.cut_right {v : ℕ → Pt} {n i : ℕ} (h : IsSArc v n) (hi : i + 1 < n) {x : Pt}
    (hx : x ∈ segment ℝ (v i) (v (i + 1))) (hxv : ∀ m, i + 1 ≤ m → m < n → x ≠ v m) :
    IsSArc (fun m => if m = 0 then x else v (m + i)) (n - i) := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  have hsub : segment ℝ x (v (i + 1)) ⊆ segment ℝ (v i) (v (i + 1)) :=
    (convex_segment _ _).segment_subset hx (right_mem_segment _ _ _)
  set u : ℕ → Pt := fun m => if m = 0 then x else v (m + i) with hu
  have hseg_u : ∀ m, m + 1 < n - i → segment ℝ (u m) (u (m + 1)) ⊆
      segment ℝ (v (m + i)) (v (m + i + 1)) := by
    intro m hm
    by_cases hm' : m = 0
    · subst hm'
      simpa [hu, show 1 + i = i + 1 by omega] using hsub
    · simp [hu, hm', show m + 1 + i = m + i + 1 by omega]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro m m' hmm' hm'
    by_cases h' : m = 0
    · simp only [hu, h', if_true, show m' ≠ 0 by omega, if_false]
      exact hxv _ (by omega) (by omega)
    · simp only [hu, h', show m' ≠ 0 by omega, if_false]
      exact hd _ _ (by omega) (by omega)
  · intro m hm
    have h1 := hseg_u m (by omega)
    have h2 := hseg_u (m + 1) (by omega)
    have hum : u (m + 1) = v (m + i + 1) := by simp [hu, show m + 1 + i = m + i + 1 by omega]
    rw [show m + 1 + i = m + i + 1 by omega, show m + i + 1 + 1 = m + i + 2 by omega] at h2
    refine (inter_subset_inter h1 h2).trans ?_
    rw [hum]
    exact hc _ (by omega)
  · intro m m' hmm' hm'
    exact (hnc (m + i) (m' + i) (by omega) (by omega)).mono (hseg_u m (by omega))
      (hseg_u m' (by omega))

/-- **Splitting a simple arc at a point** other than its ends: the part before and the part
after are simple arcs whose union is the arc and which meet only at the point. -/
theorem IsSArc.split {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {x : Pt} (hx : x ∈ vpath v n)
    (hx0 : x ≠ v 0) (hx1 : x ≠ v (n - 1)) :
    ∃ (u₁ : ℕ → Pt) (k₁ : ℕ) (u₂ : ℕ → Pt) (k₂ : ℕ), IsSArc u₁ k₁ ∧ u₁ 0 = v 0 ∧
      u₁ (k₁ - 1) = x ∧ IsSArc u₂ k₂ ∧ u₂ 0 = x ∧ u₂ (k₂ - 1) = v (n - 1) ∧
      vpath u₁ k₁ ∪ vpath u₂ k₂ = vpath v n ∧ vpath u₁ k₁ ∩ vpath u₂ k₂ = {x} := by
  classical
  have hex : ∃ i, i + 1 < n ∧ x ∈ segment ℝ (v i) (v (i + 1)) := mem_vpath.1 hx
  obtain ⟨hi, hxi⟩ := Nat.find_spec hex
  set i := Nat.find hex with hidef
  have hmin : ∀ m < i, x ∉ segment ℝ (v m) (v (m + 1)) := fun m hm h' =>
    Nat.find_min hex hm ⟨by omega, h'⟩
  have hxvi : x ≠ v i := by
    intro hxv
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact hx0 (by rw [hxv, h0])
    · exact hmin (i - 1) (by omega)
        (by rw [hxv, show i - 1 + 1 = i by omega]; exact right_mem_segment _ _ _)
  have hn := h.1
  by_cases hxv : x = v (i + 1)
  · -- the point is the vertex `v (i+1)`
    have hi2 : i + 2 < n := by
      by_contra hc; apply hx1; rw [hxv]; congr 1; omega
    refine ⟨v, i + 2, fun m => v (m + (i + 1)), n - (i + 1), h.take (by omega) (by omega), rfl,
      by rw [hxv]; congr 1, h.drop (by omega), by simp [hxv], by simp only; congr 1; omega, ?_, ?_⟩
    · ext y
      simp only [mem_union, mem_vpath]
      constructor
      · rintro (⟨m, hm, hy⟩ | ⟨m, hm, hy⟩)
        · exact ⟨m, by omega, hy⟩
        · exact ⟨m + (i + 1), by omega, by rwa [vpath_drop_seg] at hy⟩
      · rintro ⟨m, hm, hy⟩
        by_cases hmi : m ≤ i
        · exact Or.inl ⟨m, by omega, hy⟩
        · refine Or.inr ⟨m - (i + 1), by omega, ?_⟩
          rw [vpath_drop_seg, show m - (i + 1) + (i + 1) = m by omega]; exact hy
    · apply subset_antisymm
      · rintro y ⟨hy1, hy2⟩
        obtain ⟨m, hm, hym⟩ := mem_vpath.1 hy1
        obtain ⟨m', hm', hym'⟩ := mem_vpath.1 hy2
        rw [vpath_drop_seg] at hym'
        by_cases hmm : m = i ∧ m' = 0
        · obtain ⟨hm1, hm2⟩ := hmm
          subst hm2
          rw [hm1] at hym
          have hym'' : y ∈ segment ℝ (v (i + 1)) (v (i + 2)) := by
            simpa [show i + 1 + 1 = i + 2 by omega] using hym'
          rw [hxv]
          exact h.2.2.1 i (by omega) ⟨hym, hym''⟩
        · exact absurd hym' ((h.2.2.2 m (m' + (i + 1)) (by omega) (by omega)).notMem_of_mem_left
            hym)
      · rintro y rfl
        refine ⟨?_, ?_⟩
        · rw [hxv]; exact vertex_mem_vpath (by omega) (by omega)
        · have := vertex_mem_vpath (v := fun m => v (m + (i + 1))) (n := n - (i + 1)) (k := 0)
            (by omega) (by omega)
          simpa [hxv] using this
  · -- the point is inside the segment `i`
    have hxv1 : ∀ m, m ≤ i → x ≠ v m := by
      intro m hm hxm
      rcases hm.lt_or_eq with hm | hm
      · rcases h.vertex_mem_seg (k := m) (by omega) hi (hxm ▸ hxi) with h' | h' <;> omega
      · exact hxvi (hm ▸ hxm)
    have hxv2 : ∀ m, i + 1 ≤ m → m < n → x ≠ v m := by
      intro m hm hmn hxm
      rcases hm.lt_or_eq with hm | hm
      · rcases h.vertex_mem_seg (k := m) hmn hi (hxm ▸ hxi) with h' | h' <;> omega
      · exact hxv (hm ▸ hxm)
    set u₁ : ℕ → Pt := fun m => if m ≤ i then v m else x with hu₁
    set u₂ : ℕ → Pt := fun m => if m = 0 then x else v (m + i) with hu₂
    have hS1 : ∀ m, m < i → segment ℝ (u₁ m) (u₁ (m + 1)) = segment ℝ (v m) (v (m + 1)) := by
      intro m hm; simp [hu₁, show m ≤ i by omega, show m + 1 ≤ i by omega]
    have hS1i : segment ℝ (u₁ i) (u₁ (i + 1)) = segment ℝ (v i) x := by simp [hu₁]
    have hS20 : segment ℝ (u₂ 0) (u₂ (0 + 1)) = segment ℝ x (v (i + 1)) := by
      simp [hu₂, add_comm]
    have hS2 : ∀ m, 1 ≤ m → segment ℝ (u₂ m) (u₂ (m + 1)) =
        segment ℝ (v (m + i)) (v (m + i + 1)) := by
      intro m hm; simp [hu₂, show m ≠ 0 by omega, show m + 1 + i = m + i + 1 by omega]
    have hsub1 : segment ℝ (v i) x ⊆ segment ℝ (v i) (v (i + 1)) :=
      (convex_segment _ _).segment_subset (left_mem_segment _ _ _) hxi
    have hsub2 : segment ℝ x (v (i + 1)) ⊆ segment ℝ (v i) (v (i + 1)) :=
      (convex_segment _ _).segment_subset hxi (right_mem_segment _ _ _)
    refine ⟨u₁, i + 2, u₂, n - i, h.cut_left hi hxi hxv1, by simp [hu₁], by simp [hu₁],
      h.cut_right hi hxi hxv2, by simp [hu₂], ?_, ?_, ?_⟩
    · simp only [hu₂, show n - i - 1 ≠ 0 by omega, if_false]
      congr 1; omega
    · ext y
      simp only [mem_union, mem_vpath]
      constructor
      · rintro (⟨m, hm, hy⟩ | ⟨m, hm, hy⟩)
        · rcases Nat.lt_or_ge m i with hmi | hmi
          · exact ⟨m, by omega, by rwa [hS1 m hmi] at hy⟩
          · have : m = i := by omega
            subst this
            exact ⟨i, hi, hsub1 (by rwa [hS1i] at hy)⟩
        · rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0; exact ⟨i, hi, hsub2 (by rwa [hS20] at hy)⟩
          · exact ⟨m + i, by omega, by rwa [hS2 m h0] at hy⟩
      · rintro ⟨m, hm, hy⟩
        rcases lt_trichotomy m i with hmi | hmi | hmi
        · exact Or.inl ⟨m, by omega, by rwa [hS1 m hmi]⟩
        · subst hmi
          rw [segment_eq_union_of_mem hxi] at hy
          rcases hy with hy | hy
          · exact Or.inl ⟨i, by omega, by rwa [hS1i]⟩
          · exact Or.inr ⟨0, by omega, by rwa [hS20]⟩
        · refine Or.inr ⟨m - i, by omega, ?_⟩
          rw [hS2 _ (by omega), show m - i + i = m by omega]; exact hy
    · apply subset_antisymm
      · rintro y ⟨hy1, hy2⟩
        obtain ⟨m, hm, hym⟩ := mem_vpath.1 hy1
        obtain ⟨m', hm', hym'⟩ := mem_vpath.1 hy2
        rcases Nat.lt_or_ge m i with hmi | hmi
        · rw [hS1 m hmi] at hym
          rcases Nat.eq_zero_or_pos m' with h0 | h0
          · subst h0
            rw [hS20] at hym'
            rcases Nat.lt_or_ge (m + 1) i with hmi' | hmi'
            · exact absurd (hsub2 hym') ((h.2.2.2 m i hmi' hi).notMem_of_mem_left hym)
            · have hm' : m = i - 1 := by omega
              subst hm'
              have h3 := h.2.2.1 (i - 1) (by omega)
              rw [show i - 1 + 1 = i by omega, show i - 1 + 2 = i + 1 by omega] at h3
              rw [show i - 1 + 1 = i by omega] at hym
              have hyv : y = v i := h3 ⟨hym, hsub2 hym'⟩
              exact absurd (hyv ▸ hym') (left_not_mem_segment_part hxi hxvi)
          · rw [hS2 m' h0] at hym'
            exact absurd hym' ((h.2.2.2 m (m' + i) (by omega) (by omega)).notMem_of_mem_left hym)
        · have : m = i := by omega
          subst this
          rw [hS1i] at hym
          rcases Nat.lt_or_ge m' 2 with h2 | h2
          · rcases Nat.eq_zero_or_pos m' with h0 | h0
            · subst h0
              rw [hS20] at hym'
              have := segment_inter_of_mem hxi
              exact this.subset ⟨hym, hym'⟩
            · have h1 : m' = 1 := by omega
              subst h1
              rw [hS2 1 le_rfl, show 1 + i = i + 1 by omega] at hym'
              have h3 := h.2.2.1 i (by omega)
              have hyv : y = v (i + 1) := h3 ⟨hsub1 hym, hym'⟩
              exact absurd (hyv ▸ hym) (right_not_mem_segment_part hxi hxv)
          · rw [hS2 m' (by omega)] at hym'
            exact absurd hym' ((h.2.2.2 i (m' + i) (by omega) (by omega)).notMem_of_mem_left
              (hsub1 hym))
      · rintro y rfl
        refine ⟨segment_subset_vpath (i := i) (by omega) ?_,
          segment_subset_vpath (i := 0) (by omega) ?_⟩
        · rw [hS1i]; exact right_mem_segment _ _ _
        · rw [hS20]; exact left_mem_segment _ _ _

end HPC.Plane
