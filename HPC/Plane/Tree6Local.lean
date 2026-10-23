import HPC.Plane.Tree67

/-!
# Batch 118, auxiliary: the local geometry of a simple closed polygon

A small square about a point `w` of a simple closed polygon meets the polygon in two rays from `w`
(one straight chord when `w` is not a vertex), and the square minus two such rays is the union of
two convex-or-connected pieces. Used for `PlaneFacts.local_side` in `HPC/Plane/Tree6.lean`.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-- The closed ray from `w` in direction `a`. -/
def rayFrom (w a : Pt) : Set Pt := (fun t : ℝ => w + t • a) '' Ici 0

theorem mem_rayFrom {w a x : Pt} :
    x ∈ rayFrom w a ↔ ∃ t : ℝ, 0 ≤ t ∧ x.1 = w.1 + t * a.1 ∧ x.2 = w.2 + t * a.2 := by
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl, rfl⟩
  · rintro ⟨t, ht, h1, h2⟩; exact ⟨t, ht, Prod.ext h1.symm h2.symm⟩

theorem convex_inter_halfplane (O : Set Pt) (hO : Convex ℝ O) (w : Pt) (c₁ c₂ : ℝ) :
    Convex ℝ (O ∩ {x : Pt | 0 < c₁ * (x.1 - w.1) + c₂ * (x.2 - w.2)}) := by
  refine hO.inter ?_
  intro x hx y hy s t hs ht hst
  simp only [mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  have : c₁ * (s * x.1 + t * y.1 - w.1) + c₂ * (s * x.2 + t * y.2 - w.2) =
      s * (c₁ * (x.1 - w.1) + c₂ * (x.2 - w.2)) + t * (c₁ * (y.1 - w.1) + c₂ * (y.2 - w.2)) := by
    linear_combination (c₁ * w.1 + c₂ * w.2) * hst
  rw [this]
  rcases hs.lt_or_eq with hs | hs
  · nlinarith [mul_nonneg ht hy.le]
  · subst hs; simp at hst; subst hst; simpa using hy

/-- **Two rays cut a square into (at most) two connected pieces.** For `w`, nonzero `a`, `b` not
positively parallel, and `r > 0`, the ball (an open square) about `w` minus the two rays from `w`
in directions `a`, `b` is the union of two preconnected sets. -/
theorem ball_diff_rays (w a b : Pt) (ha : a ≠ 0) (hb : b ≠ 0) (hab : ∀ c : ℝ, 0 < c → b ≠ c • a)
    {r : ℝ} (hr : 0 < r) :
    ∃ P₁ P₂ : Set Pt, IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      ball w r \ (rayFrom w a ∪ rayFrom w b) = P₁ ∪ P₂ := by
  have ha' : a.1 ^ 2 + a.2 ^ 2 ≠ 0 := by
    intro h; apply ha
    have h1 : a.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    have h2 : a.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    exact Prod.ext h1 h2
  set D := a.1 * b.2 - a.2 * b.1 with hD
  by_cases hD0 : D = 0
  · -- parallel (necessarily opposite) directions: one line through `w`
    refine ⟨ball w r ∩ {x : Pt | 0 < (-a.2) * (x.1 - w.1) + a.1 * (x.2 - w.2)},
      ball w r ∩ {x : Pt | 0 < a.2 * (x.1 - w.1) + (-a.1) * (x.2 - w.2)},
      (convex_inter_halfplane _ (convex_ball w r) w _ _).isPreconnected,
      (convex_inter_halfplane _ (convex_ball w r) w _ _).isPreconnected, ?_⟩
    ext x
    simp only [mem_diff, mem_union, mem_inter_iff, mem_setOf_eq, mem_rayFrom]
    constructor
    · rintro ⟨hx, hn⟩
      by_contra hc
      push_neg at hc
      have hg : a.1 * (x.2 - w.2) = a.2 * (x.1 - w.1) := by
        have := hc.1 hx; have := hc.2 hx; linarith
      set s := ((x.1 - w.1) * a.1 + (x.2 - w.2) * a.2) / (a.1 ^ 2 + a.2 ^ 2)
      have hs1 : x.1 = w.1 + s * a.1 := by
        simp only [s]; field_simp; linear_combination (-a.2) * hg
      have hs2 : x.2 = w.2 + s * a.2 := by
        simp only [s]; field_simp; linear_combination a.1 * hg
      set c := (b.1 * a.1 + b.2 * a.2) / (a.1 ^ 2 + a.2 ^ 2)
      have hc1 : b.1 = c * a.1 := by
        simp only [c]; field_simp; linear_combination (-a.2) * hD0
      have hc2 : b.2 = c * a.2 := by
        simp only [c]; field_simp; linear_combination a.1 * hD0
      have hcne : c ≠ 0 := by
        intro h0; apply hb; exact Prod.ext (by simp [hc1, h0]) (by simp [hc2, h0])
      have hcneg : c < 0 := by
        rcases lt_or_gt_of_ne hcne with h | h
        · exact h
        · exact absurd (Prod.ext (by simp [hc1]) (by simp [hc2])) (hab c h)
      rcases le_or_gt 0 s with hs | hs
      · exact hn (Or.inl ⟨s, hs, hs1, hs2⟩)
      · refine hn (Or.inr ⟨s / c, (div_pos_of_neg_of_neg hs hcneg).le, ?_, ?_⟩)
        · rw [hs1, hc1]; field_simp
        · rw [hs2, hc2]; field_simp
    · rintro (⟨hx, hp⟩ | ⟨hx, hp⟩) <;> refine ⟨hx, ?_⟩ <;>
        rintro (⟨t, -, h1, h2⟩ | ⟨t, -, h1, h2⟩) <;> rw [h1, h2] at hp <;>
        (have h0 : (a.1 * b.2 - a.2 * b.1) * t = 0 := by rw [← hD, hD0, zero_mul]
         nlinarith)
  · -- independent directions
    set f : Pt → ℝ := fun x => (b.2 / D) * (x.1 - w.1) + (-b.1 / D) * (x.2 - w.2) with hf
    set g : Pt → ℝ := fun x => (-a.2 / D) * (x.1 - w.1) + (a.1 / D) * (x.2 - w.2) with hg
    have hdec1 : ∀ x : Pt, x.1 = w.1 + f x * a.1 + g x * b.1 := by
      intro x; simp only [hf, hg]; field_simp; ring
    have hdec2 : ∀ x : Pt, x.2 = w.2 + f x * a.2 + g x * b.2 := by
      intro x; simp only [hf, hg]; field_simp; ring
    have hfa : ∀ t : ℝ, ∀ x : Pt, x.1 = w.1 + t * a.1 → x.2 = w.2 + t * a.2 →
        f x = t ∧ g x = 0 := by
      intro t x h1 h2; simp only [hf, hg, h1, h2]; constructor <;> field_simp <;> ring
    have hfb : ∀ t : ℝ, ∀ x : Pt, x.1 = w.1 + t * b.1 → x.2 = w.2 + t * b.2 →
        f x = 0 ∧ g x = t := by
      intro t x h1 h2; simp only [hf, hg, h1, h2]; constructor <;> field_simp <;> ring
    obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * ‖a + b‖ < r := by
      refine ⟨r / (2 * (‖a + b‖ + 1)), by positivity, ?_⟩
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (a + b)]
    set z : Pt := w - ε • (a + b) with hz
    have hzb : z ∈ ball w r := by
      rw [mem_ball, dist_eq_norm, hz, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos hε]
      exact hεr
    have hzf : f z = -ε ∧ g z = -ε := by
      simp only [hf, hg, hz, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add, smul_eq_mul]
      constructor <;> field_simp <;> ring
    refine ⟨(ball w r ∩ {x : Pt | 0 < (b.2 / D) * (x.1 - w.1) + (-b.1 / D) * (x.2 - w.2)}) ∩
        {x : Pt | 0 < (-a.2 / D) * (x.1 - w.1) + (a.1 / D) * (x.2 - w.2)},
      (ball w r ∩ {x : Pt | 0 < (-(b.2 / D)) * (x.1 - w.1) + (-(-b.1 / D)) * (x.2 - w.2)}) ∪
        (ball w r ∩ {x : Pt | 0 < (-(-a.2 / D)) * (x.1 - w.1) + (-(a.1 / D)) * (x.2 - w.2)}),
      (convex_inter_halfplane _ (convex_inter_halfplane _ (convex_ball w r) w _ _) w _ _
        ).isPreconnected, ?_, ?_⟩
    · refine (convex_inter_halfplane _ (convex_ball w r) w _ _).isPreconnected.union z ?_ ?_
        (convex_inter_halfplane _ (convex_ball w r) w _ _).isPreconnected
      · refine ⟨hzb, ?_⟩
        have := hzf.1; simp only [hf] at this; simp only [mem_setOf_eq]; linarith
      · refine ⟨hzb, ?_⟩
        have := hzf.2; simp only [hg] at this; simp only [mem_setOf_eq]; linarith
    ext x
    have e1 : (b.2 / D) * (x.1 - w.1) + (-b.1 / D) * (x.2 - w.2) = f x := rfl
    have e2 : (-a.2 / D) * (x.1 - w.1) + (a.1 / D) * (x.2 - w.2) = g x := rfl
    have e3 : (-(b.2 / D)) * (x.1 - w.1) + (-(-b.1 / D)) * (x.2 - w.2) = - f x := by
      simp only [hf]; ring
    have e4 : (-(-a.2 / D)) * (x.1 - w.1) + (-(a.1 / D)) * (x.2 - w.2) = - g x := by
      simp only [hg]; ring
    simp only [mem_diff, mem_union, mem_inter_iff, mem_setOf_eq, mem_rayFrom, e1, e2, e3, e4]
    constructor
    · rintro ⟨hx, hn⟩
      rcases lt_or_ge (f x) 0 with h1 | h1
      · exact Or.inr (Or.inl ⟨hx, by linarith⟩)
      rcases lt_or_ge (g x) 0 with h2 | h2
      · exact Or.inr (Or.inr ⟨hx, by linarith⟩)
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inl ⟨⟨hx, h1⟩, h2⟩
        · refine absurd (Or.inl ⟨f x, h1.le, ?_, ?_⟩) hn
          · have := hdec1 x; rw [← h2] at this; linarith
          · have := hdec2 x; rw [← h2] at this; linarith
      · refine absurd (Or.inr ⟨g x, h2, ?_, ?_⟩) hn
        · have := hdec1 x; rw [← h1] at this; linarith
        · have := hdec2 x; rw [← h1] at this; linarith
    · rintro (⟨⟨hx, hp⟩, hq⟩ | ⟨hx, hp⟩ | ⟨hx, hp⟩) <;> refine ⟨hx, ?_⟩ <;>
        rintro (⟨t, ht, h1, h2⟩ | ⟨t, ht, h1, h2⟩)
      · have := (hfa t x h1 h2).2; linarith
      · have := (hfb t x h1 h2).1; linarith
      · have := (hfa t x h1 h2).1; linarith
      · have := (hfb t x h1 h2).1; linarith
      · have := (hfa t x h1 h2).2; linarith
      · have := (hfb t x h1 h2).2; linarith

/-! ### Segments and rays -/

theorem isCompact_segment' (x y : Pt) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

theorem segment_subset_rayFrom (w u : Pt) : segment ℝ w u ⊆ rayFrom w (u - w) := by
  rw [segment_eq_image']
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ht.1, rfl⟩

theorem rayFrom_inter_ball_subset {w u : Pt} {ρ : ℝ} (hρ : ρ ≤ dist w u) :
    rayFrom w (u - w) ∩ ball w ρ ⊆ segment ℝ w u := by
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  rw [segment_eq_image']
  refine ⟨t, ⟨ht, ?_⟩, rfl⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht, ← dist_eq_norm, dist_comm] at hx
  by_contra h
  push_neg at h
  have : dist w u ≤ t * dist w u := le_mul_of_one_le_left dist_nonneg h.le
  linarith

theorem segment_subset_rays {v u w : Pt} (hw : w ∈ segment ℝ v u) (hv : w ≠ v) (hu : w ≠ u) :
    segment ℝ v u ⊆ rayFrom w (u - w) ∪ rayFrom w (v - w) := by
  rw [segment_eq_image'] at hw ⊢
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  have ht0' : t ≠ 0 := by rintro rfl; simp at hv
  have ht1' : t ≠ 1 := by rintro rfl; simp at hu
  have h1t : (0 : ℝ) < 1 - t := by have := lt_of_le_of_ne ht1 ht1'; linarith
  have h0t : (0 : ℝ) < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
  rintro x ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩
  rw [mem_union, mem_rayFrom, mem_rayFrom]
  rcases le_or_gt t τ with h | h
  · left
    refine ⟨(τ - t) / (1 - t), div_nonneg (by linarith) h1t.le, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring
  · right
    refine ⟨(t - τ) / t, div_nonneg (by linarith) h0t.le, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring

theorem succ_mod_cases {i n : ℕ} (h : i < n) :
    ((i + 1) % n = i + 1 ∧ i + 1 < n) ∨ ((i + 1) % n = 0 ∧ i + 1 = n) := by
  rcases Nat.lt_or_ge (i + 1) n with h' | h'
  · exact Or.inl ⟨Nat.mod_eq_of_lt h', h'⟩
  · have : i + 1 = n := by omega
    exact Or.inr ⟨by rw [this, Nat.mod_self], this⟩

/-! ### The local structure of a simple closed polygon -/

/-- Near any of its points `w`, a simple closed polygon is the union of two rays from `w` (in
directions that are nonzero and not positively parallel). -/
theorem polygon_local_rays {Γ : Set Pt} (hΓ : IsSimpleClosedPolygon Γ) {w : Pt} (hw : w ∈ Γ) :
    ∃ ρ > 0, ∃ a b : Pt, a ≠ 0 ∧ b ≠ 0 ∧ (∀ c : ℝ, 0 < c → b ≠ c • a) ∧
      Γ ∩ ball w ρ = (rayFrom w a ∪ rayFrom w b) ∩ ball w ρ := by
  obtain ⟨n, hn, v, rfl, hinj, hpoly⟩ := hΓ
  set nx : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ with hnx
  set e : Fin n → Set Pt := fun i => segment ℝ (v i) (v (nx i)) with he
  have hΓe : polygonOf v = ⋃ i, e i := rfl
  have hadj : ∀ i j, i ≠ j → ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
      e i ∩ e j ⊆ {v i, v j, v (nx i)} := fun i j hij h => (hpoly i j hij).1 h
  have hdis : ∀ i j, i ≠ j → ¬ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
      Disjoint (e i) (e j) := fun i j hij h => (hpoly i j hij).2 h
  have hnxne : ∀ i, nx i ≠ i := by
    intro i h
    have := congrArg Fin.val h
    simp only [hnx] at this
    rcases succ_mod_cases i.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega
  have hnxinj : ∀ i j, nx i = nx j → i = j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [hnx] at this
    apply Fin.ext
    rcases succ_mod_cases i.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;>
      rcases succ_mod_cases j.isLt with ⟨h3, -⟩ | ⟨h3, h4⟩ <;> omega
  have hseg : ∀ i, v i ≠ v (nx i) := fun i h => hnxne i (hinj h).symm
  -- the neighbourhood avoiding the far edges and the other vertices
  set O : Set Pt := (⋂ j ∈ Finset.univ.filter (fun j => w ∉ e j), (e j)ᶜ) ∩
    ⋂ j ∈ Finset.univ.filter (fun j => v j ≠ w), ({v j} : Set Pt)ᶜ with hO
  have hOo : IsOpen O := by
    refine (isOpen_biInter_finset fun j _ => (isCompact_segment' _ _).isClosed.isOpen_compl).inter
      (isOpen_biInter_finset fun j _ => isClosed_singleton.isOpen_compl)
  have hwO : w ∈ O := by
    refine ⟨mem_iInter₂.2 fun j hj => (Finset.mem_filter.1 hj).2,
      mem_iInter₂.2 fun j hj => fun h => (Finset.mem_filter.1 hj).2 h.symm⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hOo w hwO
  have hnear : ∀ j, ∀ x ∈ ball w ρ, x ∈ e j → w ∈ e j := by
    intro j x hx hxe
    by_contra h
    exact (mem_iInter₂.1 (hball hx).1 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) hxe
  have hfar : ∀ j, v j ≠ w → ρ ≤ dist w (v j) := by
    intro j hj
    by_contra h
    push_neg at h
    exact (mem_iInter₂.1 (hball (mem_ball.2 (by rwa [dist_comm]))).2 j
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)) rfl
  suffices key : ∃ a b : Pt, a ≠ 0 ∧ b ≠ 0 ∧ (∀ c : ℝ, 0 < c → b ≠ c • a) ∧
      (∀ j, w ∈ e j → e j ⊆ rayFrom w a ∪ rayFrom w b) ∧
      rayFrom w a ∩ ball w ρ ⊆ polygonOf v ∧ rayFrom w b ∩ ball w ρ ⊆ polygonOf v by
    obtain ⟨a, b, ha, hb, hab, hsub, hra, hrb⟩ := key
    refine ⟨ρ, hρ, a, b, ha, hb, hab, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      rw [hΓe] at hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact ⟨hsub j (hnear j x hxb hj) hj, hxb⟩
    · rintro ⟨hx | hx, hxb⟩
      · exact ⟨hra ⟨hx, hxb⟩, hxb⟩
      · exact ⟨hrb ⟨hx, hxb⟩, hxb⟩
  have heΓ : ∀ j, e j ⊆ polygonOf v := fun j => subset_iUnion e j
  by_cases hvert : ∃ k, v k = w
  · obtain ⟨k, rfl⟩ := hvert
    set pk : Fin n := ⟨(k.val + n - 1) % n, Nat.mod_lt _ (Fin.pos k)⟩ with hpk
    have hnxpk : nx pk = k := by
      apply Fin.ext
      simp only [hnx, hpk]
      rcases Nat.eq_zero_or_pos k.val with h0 | h0
      · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n), Nat.sub_add_cancel
          (by omega), Nat.mod_self]
      · rw [show k.val + n - 1 = (k.val - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : k.val - 1 < n), Nat.sub_add_cancel h0,
          Nat.mod_eq_of_lt k.isLt]
    have hpkne : pk ≠ k := by
      intro h; apply hnxne k; conv_lhs => rw [← h]; exact hnxpk
    have hepk : e pk = segment ℝ (v pk) (v k) := by simp only [he, hnxpk]
    have ha : v (nx k) - v k ≠ 0 := sub_ne_zero.2 (hseg k).symm
    have hb : v pk - v k ≠ 0 := sub_ne_zero.2 fun h => hpkne (hinj h)
    refine ⟨v (nx k) - v k, v pk - v k, ha, hb, ?_, ?_, ?_, ?_⟩
    · intro c hc hbc
      set μ := min 1 c / 2 with hμ
      have hμ0 : 0 < μ := by positivity
      have hμ1 : μ ≤ 1 := by have := min_le_left 1 c; linarith
      have hμc : μ < c := by have := min_le_right 1 c; linarith
      set p := v k + μ • (v (nx k) - v k) with hp
      have hp1 : p ∈ e k := by
        show p ∈ segment ℝ (v k) (v (nx k))
        rw [segment_eq_image']; exact ⟨μ, ⟨hμ0.le, hμ1⟩, rfl⟩
      have hp2 : p ∈ e pk := by
        rw [hepk, segment_symm, segment_eq_image']
        refine ⟨μ / c, ⟨by positivity, (div_le_one hc).2 hμc.le⟩, ?_⟩
        simp only [hp, hbc, smul_smul]
        rw [div_mul_cancel₀ _ hc.ne']
      have hsub := hadj pk k hpkne (Or.inl (congrArg Fin.val hnxpk)) ⟨hp2, hp1⟩
      rw [hnxpk] at hsub
      rcases hsub with h | h | h
      · -- `p = v pk = v k + c • a`
        have : (μ - c) • (v (nx k) - v k) = 0 := by
          rw [sub_smul, ← hbc, sub_eq_zero]
          have := congrArg (· - v k) h
          simpa [hp] using this
        rcases smul_eq_zero.1 this with h' | h'
        · linarith [sub_eq_zero.1 h']
        · exact ha h'
      · have : μ • (v (nx k) - v k) = 0 := by simpa [hp] using h
        rcases smul_eq_zero.1 this with h' | h'
        · linarith
        · exact ha h'
      · have : μ • (v (nx k) - v k) = 0 := by simpa [hp] using h
        rcases smul_eq_zero.1 this with h' | h'
        · linarith
        · exact ha h'
    · intro j hj
      by_cases hjk : j = k
      · subst hjk; exact (segment_subset_rayFrom _ _).trans subset_union_left
      by_cases hjp : j = pk
      · subst hjp
        rw [hepk, segment_symm]
        exact (segment_subset_rayFrom _ _).trans subset_union_right
      exfalso
      by_cases hjad : (j.val + 1) % n = k.val ∨ (k.val + 1) % n = j.val
      · rcases hjad with h | h
        · exact hjp (hnxinj j pk (by rw [hnxpk]; exact Fin.ext h))
        · have hj' : j = nx k := Fin.ext h.symm
          subst hj'
          have hsub : e k ⊆ e k ∩ e (nx k) :=
            fun x hx => ⟨hx, (convex_segment _ _).segment_subset hj (left_mem_segment _ _ _) hx⟩
          have hm := hadj k (nx k) (hnxne k).symm (Or.inl rfl)
            (hsub (midpoint_mem_segment (v k) (v (nx k))))
          rcases hm with h' | h' | h'
          · exact hseg k ((midpoint_eq_left_iff ℝ).1 h')
          · exact hseg k ((midpoint_eq_right_iff ℝ).1 h')
          · exact hseg k ((midpoint_eq_right_iff ℝ).1 h')
      · exact (hdis j k hjk hjad).notMem_of_mem_right (left_mem_segment _ _ _) hj
    · exact fun x hx => heΓ k (rayFrom_inter_ball_subset (hfar _ (hseg k).symm) hx)
    · intro x hx
      refine heΓ pk ?_
      rw [hepk, segment_symm]
      exact rayFrom_inter_ball_subset (hfar _ fun h => hpkne (hinj h)) hx
  · push_neg at hvert
    rw [hΓe] at hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    have ha : v (nx i) - w ≠ 0 := sub_ne_zero.2 (hvert (nx i))
    have hb : v i - w ≠ 0 := sub_ne_zero.2 (hvert i)
    refine ⟨v (nx i) - w, v i - w, ha, hb, ?_, ?_, ?_, ?_⟩
    · intro c hc hbc
      have hi' := hi
      simp only [he] at hi'
      rw [segment_eq_image'] at hi'
      obtain ⟨t, ⟨ht0, ht1⟩, hwt⟩ := hi'
      have ht0' : t ≠ 0 := by rintro rfl; exact hvert i (by simp [← hwt])
      have ht1' : t ≠ 1 := by rintro rfl; exact hvert (nx i) (by simp [← hwt])
      have hpos : 0 < t + c * (1 - t) := by
        have := lt_of_le_of_ne ht0 (Ne.symm ht0'); have := lt_of_le_of_ne ht1 ht1'
        nlinarith
      apply hseg i
      have h1 := congrArg Prod.fst hbc
      have h2 := congrArg Prod.snd hbc
      rw [← hwt] at h1 h2
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at h1 h2
      refine Prod.ext ?_ ?_
      · have : (t + c * (1 - t)) * ((v (nx i)).1 - (v i).1) = 0 := by linear_combination -h1
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      · have : (t + c * (1 - t)) * ((v (nx i)).2 - (v i).2) = 0 := by linear_combination -h2
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exact segment_subset_rays hi (hvert j).symm (hvert (nx j)).symm
      exfalso
      by_cases had : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
      · rcases hadj i j (Ne.symm hji) had ⟨hi, hj⟩ with h | h | h
        · exact hvert i h.symm
        · exact hvert j h.symm
        · exact hvert (nx i) h.symm
      · exact (hdis i j (Ne.symm hji) had).notMem_of_mem_left hi hj
    · intro x hx
      refine heΓ i ((convex_segment _ _).segment_subset hi (right_mem_segment _ _ _) ?_)
      exact rayFrom_inter_ball_subset (hfar _ (hvert (nx i))) hx
    · intro x hx
      refine heΓ i ((convex_segment _ _).segment_subset hi (left_mem_segment _ _ _) ?_)
      exact rayFrom_inter_ball_subset (hfar _ (hvert i)) hx

/-- **Local two-sidedness, from a split of the complement.** If `Γᶜ = U ∪ V` with `U`, `V` open
and disjoint and `w ∈ Γ` lies in the closure of both, then for small `r` the set `U ∩ ball w r` is
nonempty and connected: it is one of the two pieces of `ball_diff_rays`. -/
theorem local_side_of_split {Γ U V : Set Pt} (hΓ : IsSimpleClosedPolygon Γ) (hU : IsOpen U)
    (hV : IsOpen V) (hJ : Γᶜ = U ∪ V) (hd : Disjoint U V) {w : Pt} (hw : w ∈ Γ)
    (hwU : w ∈ closure U) (hwV : w ∈ closure V) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → (U ∩ ball w r).Nonempty ∧ IsConnected (U ∩ ball w r) := by
  obtain ⟨ρ, hρ, a, b, ha, hb, hab, hloc⟩ := polygon_local_rays hΓ hw
  refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
  have hne : ∀ W : Set Pt, w ∈ closure W → (W ∩ ball w r).Nonempty := by
    intro W hW
    obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.1 hW r hr
    exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hdy⟩
  have hUne := hne U hwU
  have hVne := hne V hwV
  obtain ⟨P₁, P₂, h1, h2, hP⟩ := ball_diff_rays w a b ha hb hab hr
  have hrb : ball w r ⊆ ball w ρ := ball_subset_ball hrρ
  have hdiff : ball w r \ Γ = P₁ ∪ P₂ := by
    rw [← hP]
    ext x
    simp only [mem_diff]
    constructor
    · rintro ⟨hx, hxΓ⟩
      refine ⟨hx, fun hray => hxΓ ?_⟩
      have : x ∈ (rayFrom w a ∪ rayFrom w b) ∩ ball w ρ := ⟨hray, hrb hx⟩
      rw [← hloc] at this
      exact this.1
    · rintro ⟨hx, hxr⟩
      refine ⟨hx, fun hxΓ => hxr ?_⟩
      have : x ∈ Γ ∩ ball w ρ := ⟨hxΓ, hrb hx⟩
      rw [hloc] at this
      exact this.1
  have hside : ∀ P : Set Pt, IsPreconnected P → P ⊆ ball w r \ Γ → P ⊆ U ∨ P ⊆ V := by
    intro P hP hsub
    refine isPreconnected_iff_subset_of_disjoint.1 hP U V hU hV ?_
      (by rw [hd.inter_eq, inter_empty])
    intro x hx
    have : x ∈ Γᶜ := (hsub hx).2
    rwa [hJ] at this
  have hUΓ : U ∩ ball w r ⊆ P₁ ∪ P₂ := by
    rw [← hdiff]
    rintro x ⟨hxU, hx⟩
    refine ⟨hx, fun hxΓ => ?_⟩
    have : x ∈ U ∪ V := Or.inl hxU
    rw [← hJ] at this
    exact this hxΓ
  have hVΓ : V ∩ ball w r ⊆ P₁ ∪ P₂ := by
    rw [← hdiff]
    rintro x ⟨hxV, hx⟩
    refine ⟨hx, fun hxΓ => ?_⟩
    have : x ∈ U ∪ V := Or.inr hxV
    rw [← hJ] at this
    exact this hxΓ
  have hP1 : P₁ ⊆ ball w r \ Γ := hdiff ▸ subset_union_left
  have hP2 : P₂ ⊆ ball w r \ Γ := hdiff ▸ subset_union_right
  -- the piece in `U` is all of `U ∩ ball w r`
  have key : ∀ P Q : Set Pt, IsPreconnected P → P ⊆ ball w r \ Γ → P ⊆ U → Q ⊆ V →
      U ∩ ball w r ⊆ P ∪ Q → (U ∩ ball w r).Nonempty ∧ IsConnected (U ∩ ball w r) := by
    intro P Q hP hPs hPU hQV hcov
    have heq : U ∩ ball w r = P := by
      apply subset_antisymm
      · intro x hx
        rcases hcov hx with h | h
        · exact h
        · exact absurd (hQV h) (hd.notMem_of_mem_left hx.1)
      · exact fun x hx => ⟨hPU hx, (hPs hx).1⟩
    exact ⟨hUne, hUne, heq ▸ hP⟩
  rcases hside P₁ h1 hP1 with hA | hA <;> rcases hside P₂ h2 hP2 with hB | hB
  · exfalso
    obtain ⟨x, hxV, hx⟩ := hVne
    rcases hVΓ ⟨hxV, hx⟩ with h | h
    · exact hd.notMem_of_mem_left (hA h) hxV
    · exact hd.notMem_of_mem_left (hB h) hxV
  · exact key P₁ P₂ h1 hP1 hA hB hUΓ
  · exact key P₂ P₁ h2 hP2 hB hA (by rw [union_comm]; exact hUΓ)
  · exfalso
    obtain ⟨x, hxU, hx⟩ := hUne
    rcases hUΓ ⟨hxU, hx⟩ with h | h
    · exact hd.notMem_of_mem_left hxU (hA h)
    · exact hd.notMem_of_mem_left hxU (hB h)

/-- A union of preconnected pieces `P w`, indexed by a preconnected set `α`, is preconnected if
the piece at `w` meets the piece at every point of `α` near `w`. -/
theorem isPreconnected_biUnion_of_local_meet {α : Set Pt} (hα : IsPreconnected α)
    (P : Pt → Set Pt) (ρ : Pt → ℝ) (hρ : ∀ w ∈ α, 0 < ρ w) (hP : ∀ w ∈ α, IsPreconnected (P w))
    (hmeet : ∀ w ∈ α, ∀ w' ∈ α, w' ∈ ball w (ρ w) → (P w ∩ P w').Nonempty) :
    IsPreconnected (⋃ w ∈ α, P w) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hS hdisj
  have hsub : ∀ w ∈ α, P w ⊆ ⋃ w ∈ α, P w := fun w hw => subset_biUnion_of_mem (u := P) hw
  have hside : ∀ w ∈ α, P w ⊆ u ∨ P w ⊆ v := fun w hw =>
    isPreconnected_iff_subset_of_disjoint.1 (hP w hw) u v hu hv ((hsub w hw).trans hS)
      (eq_empty_of_subset_empty (hdisj ▸ inter_subset_inter_left _ (hsub w hw)))
  have hbad : ∀ w ∈ α, ∀ x ∈ P w, x ∈ u → x ∈ v → False := by
    intro w hw x hx h1 h2
    have : x ∈ (⋃ w ∈ α, P w) ∩ (u ∩ v) := ⟨hsub w hw hx, h1, h2⟩
    rw [hdisj] at this
    exact this
  have hpropu : ∀ w ∈ α, ∀ w' ∈ α, w' ∈ ball w (ρ w) → P w ⊆ u → P w' ⊆ u := by
    intro w hw w' hw' hb hwu
    rcases hside w' hw' with h | h
    · exact h
    · obtain ⟨x, hx, hx'⟩ := hmeet w hw w' hw' hb
      exact (hbad w hw x hx (hwu hx) (h hx')).elim
  have hpropv : ∀ w ∈ α, ∀ w' ∈ α, w' ∈ ball w (ρ w) → P w ⊆ v → P w' ⊆ v := by
    intro w hw w' hw' hb hwv
    rcases hside w' hw' with h | h
    · obtain ⟨x, hx, hx'⟩ := hmeet w hw w' hw' hb
      exact (hbad w hw x hx (h hx') (hwv hx)).elim
    · exact h
  set T := {w | w ∈ α ∧ P w ⊆ u} with hT
  set T' := {w | w ∈ α ∧ P w ⊆ v} with hT'
  have hcov : α ⊆ (⋃ w ∈ T, ball w (ρ w)) ∪ ⋃ w ∈ T', ball w (ρ w) := by
    intro w hw
    rcases hside w hw with h | h
    · exact Or.inl (mem_biUnion ⟨hw, h⟩ (mem_ball_self (hρ w hw)))
    · exact Or.inr (mem_biUnion ⟨hw, h⟩ (mem_ball_self (hρ w hw)))
  have hdis' : α ∩ ((⋃ w ∈ T, ball w (ρ w)) ∩ ⋃ w ∈ T', ball w (ρ w)) = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro w ⟨hw, h1, h2⟩
    obtain ⟨w₁, ⟨hw₁, hu₁⟩, hb₁⟩ := mem_iUnion₂.1 h1
    obtain ⟨w₂, ⟨hw₂, hv₂⟩, hb₂⟩ := mem_iUnion₂.1 h2
    have hu' := hpropu w₁ hw₁ w hw hb₁ hu₁
    have hv' := hpropv w₂ hw₂ w hw hb₂ hv₂
    obtain ⟨x, hx, -⟩ := hmeet w hw w hw (mem_ball_self (hρ w hw))
    exact hbad w hw x hx (hu' hx) (hv' hx)
  rcases isPreconnected_iff_subset_of_disjoint.1 hα _ _
      (isOpen_biUnion fun _ _ => isOpen_ball) (isOpen_biUnion fun _ _ => isOpen_ball) hcov hdis'
    with h | h
  · left
    refine iUnion₂_subset fun w hw => ?_
    obtain ⟨w₁, ⟨hw₁, hu₁⟩, hb₁⟩ := mem_iUnion₂.1 (h hw)
    exact hpropu w₁ hw₁ w hw hb₁ hu₁
  · right
    refine iUnion₂_subset fun w hw => ?_
    obtain ⟨w₁, ⟨hw₁, hv₁⟩, hb₁⟩ := mem_iUnion₂.1 (h hw)
    exact hpropv w₁ hw₁ w hw hb₁ hv₁

/-- **Two-sidedness along a connected part of the polygon, from a split of the complement.** If
`α ⊆ Γ` is preconnected and lies in an open `h`, there is a preconnected `S ⊆ U ∩ h` containing,
at every point `w` of `α`, the whole local piece `U ∩ ball w r` for some `r > 0`. -/
theorem sides_of_split {Γ U V : Set Pt} (hΓ : IsSimpleClosedPolygon Γ) (hU : IsOpen U)
    (hV : IsOpen V) (hJ : Γᶜ = U ∪ V) (hd : Disjoint U V) (hfU : ∀ w ∈ Γ, w ∈ closure U)
    (hfV : ∀ w ∈ Γ, w ∈ closure V) {α h : Set Pt} (hα : α ⊆ Γ) (hαc : IsPreconnected α)
    (ho : IsOpen h) (hαh : α ⊆ h) :
    ∃ S : Set Pt, IsPreconnected S ∧ S ⊆ U ∩ h ∧ ∀ w ∈ α, ∃ r > 0, U ∩ ball w r ⊆ S := by
  have hloc : ∀ w, w ∈ α → ∃ ρ : ℝ, 0 < ρ ∧ IsPreconnected (U ∩ ball w ρ) ∧ ball w ρ ⊆ h := by
    intro w hw
    obtain ⟨r₀, hr₀, hr⟩ := local_side_of_split hΓ hU hV hJ hd (hα hw) (hfU w (hα hw))
      (hfV w (hα hw))
    obtain ⟨ε, hε, hεh⟩ := Metric.isOpen_iff.1 ho w (hαh hw)
    refine ⟨min r₀ ε, lt_min hr₀ hε, (hr _ (lt_min hr₀ hε) (min_le_left _ _)).2.isPreconnected,
      (ball_subset_ball (min_le_right _ _)).trans hεh⟩
  choose! ρ hρ hρc hρh using hloc
  refine ⟨⋃ w ∈ α, U ∩ ball w (ρ w), ?_, ?_, fun w hw => ⟨ρ w, hρ w hw,
    subset_biUnion_of_mem (u := fun w => U ∩ ball w (ρ w)) hw⟩⟩
  · refine isPreconnected_biUnion_of_local_meet hαc _ ρ hρ hρc ?_
    intro w hw w' hw' hb
    have hs : 0 < min (ρ w') (ρ w - dist w' w) :=
      lt_min (hρ w' hw') (by rw [mem_ball] at hb; linarith)
    obtain ⟨y, hyU, hy⟩ := Metric.mem_closure_iff.1 (hfU w' (hα hw')) _ hs
    have hy1 : dist y w' < ρ w' := by rw [dist_comm]; exact hy.trans_le (min_le_left _ _)
    have hy2 : dist y w < ρ w := by
      have := dist_triangle y w' w
      have : dist w' y < ρ w - dist w' w := hy.trans_le (min_le_right _ _)
      rw [dist_comm] at this
      linarith
    exact ⟨y, ⟨hyU, hy2⟩, hyU, hy1⟩
  · exact iUnion₂_subset fun w hw => fun y hy => ⟨hy.1, hρh w hw hy.2⟩

end HPC.Plane
