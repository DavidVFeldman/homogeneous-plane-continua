import HPC.Plane.StdChain
import HPC.Plane.Joints
import HPC.Plane.Shear

/-!
# The planar step in standard coordinates

Batch 84. For a slow pattern `x : Fin n → Fin m` with unit steps, the folding homeomorphism of
`Shear.lean` built on the joint positions of `Joints.lean` carries the fine standard chain (with
`n` links) into the coarse standard chain (with `m` links) following `x`, tightly, with small
pieces, and with the end boxes nested.
-/

namespace HPC.Plane

open Set

theorem dist_le_of_abs_le {p q : Pt} {η : ℝ} (h1 : |p.1 - q.1| ≤ η) (h2 : |p.2 - q.2| ≤ η) :
    dist p q ≤ η := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_le h1 h2

theorem abs_sub_le_of_mem {a b lo hi : ℝ} (ha1 : lo ≤ a) (ha2 : a ≤ hi) (hb1 : lo ≤ b)
    (hb2 : b ≤ hi) : |a - b| ≤ hi - lo := by
  rw [abs_le]; constructor <;> linarith

namespace StdStep

variable {m n : ℕ} {x : Fin n → Fin m} {N : ℕ} {β C : ℝ}

/-- Heights of the image of fine link `t` lie in `[1/4, 1/2]`. -/
theorem heights (hC0 : 0 < C) (hCn : C * (8 * ((n : ℝ) + 1)) ≤ 1) {t : ℕ} (ht : t < n) {y : ℝ}
    (h1 : 1 / 4 + 2 * C * t ≤ y) (h2 : y ≤ 1 / 4 + C * (2 * t + 3) + C / 8) :
    1 / 4 ≤ y ∧ y ≤ 1 / 2 := by
  have ht' : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have e1 : 0 ≤ C * t := by positivity
  have e2 : C * ((t : ℝ) + 1) ≤ C * n := mul_le_mul_of_nonneg_left ht' hC0.le
  constructor <;> nlinarith

variable (hx : Joints.UnitSteps x) (hs : Joints.Slow x N) (hN : 12 ≤ N)
  (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 100) (hC0 : 0 < C) (hCn : C * (8 * ((n : ℝ) + 1)) ≤ 1)
include hx hs hN hβ0 hβ1 hC0 hCn

theorem follow (t : Fin n) :
    Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' closure (stdRect t) ⊆ stdRect (x t) := by
  rintro _ ⟨⟨u, v⟩, hp, rfl⟩
  rw [closure_stdRect] at hp
  obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp
  try dsimp only at hu1 hu2 hv1 hv2
  obtain ⟨i1, i2, i3, i4⟩ := Shear.link_image n (Joints.P x N) hC0 t.isLt hβ0 hu1 hu2 hv1 hv2
  obtain ⟨⟨f1, f2⟩, -, -⟩ := Joints.link_facts hx hs hN t.isLt
  have ex : (Joints.xe x t : ℝ) = ((x t : ℕ) : ℝ) := by
    rw [Joints.xe_of_lt t.isLt]; simp
  rw [ex] at f1 f2
  have hy := heights hC0 hCn t.isLt i3 i4
  have l1 := min_le_max (a := Joints.P x N t) (b := Joints.P x N (t + 1))
  rw [Shear.Ψ_apply]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith

omit hCn in
theorem tight (t : Fin n) (l : Fin m)
    (h : (Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' stdRect t ∩ stdRect l).Nonempty) :
    ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t' := by
  obtain ⟨_, ⟨⟨u, v⟩, hp, rfl⟩, hl⟩ := h
  have hp' : (u, v) ∈ closure (stdRect t) := subset_closure hp
  rw [closure_stdRect] at hp'
  obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp'
  try dsimp only at hu1 hu2 hv1 hv2
  obtain ⟨i1, i2, -, -⟩ := Shear.link_image n (Joints.P x N) hC0 t.isLt hβ0 hu1 hu2 hv1 hv2
  obtain ⟨-, f, -⟩ := Joints.link_facts hx hs hN t.isLt
  rw [Shear.Ψ_apply] at hl
  obtain ⟨⟨l1, l2⟩, -⟩ := hl
  simp only at l1 l2
  obtain ⟨t', ht', e⟩ := f l (by linarith) (by linarith)
  exact ⟨t', ht', Fin.ext (by exact_mod_cast e)⟩

theorem small {η : ℝ} (hβ2 : β ≤ η / 10) (hC2 : C ≤ η / 8) (hNη : 1 / (2 * (N : ℝ)) ≤ η / 2)
    (t : Fin n) :
    (∀ p ∈ Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' closure (stdRect t),
      ∀ q ∈ Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' closure (stdRect t), dist p q ≤ η) ∨
    ∃ k : ℕ, k < m ∧ Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' closure (stdRect t) ⊆ zone k := by
  obtain ⟨⟨f1, f2⟩, -, f⟩ := Joints.link_facts hx hs hN t.isLt
  rcases f with f | ⟨k, k1, k2⟩
  · left
    rintro _ ⟨⟨u, v⟩, hp, rfl⟩ _ ⟨⟨u', v'⟩, hp', rfl⟩
    rw [closure_stdRect] at hp hp'
    obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp
    try dsimp only at hu1 hu2 hv1 hv2
    obtain ⟨⟨hu1', hu2'⟩, hv1', hv2'⟩ := hp'
    try dsimp only at hu1' hu2' hv1' hv2'
    obtain ⟨i1, i2, i3, i4⟩ := Shear.link_image n (Joints.P x N) hC0 t.isLt hβ0 hu1 hu2 hv1 hv2
    obtain ⟨j1, j2, j3, j4⟩ := Shear.link_image n (Joints.P x N) hC0 t.isLt hβ0 hu1' hu2' hv1' hv2'
    rw [Shear.Ψ_apply, Shear.Ψ_apply]
    apply dist_le_of_abs_le
    · refine (abs_sub_le_of_mem i1 i2 j1 j2).trans ?_; linarith
    · refine (abs_sub_le_of_mem i3 i4 j3 j4).trans ?_; linarith
  · right
    refine ⟨k, ?_, ?_⟩
    · have ex : (Joints.xe x t : ℝ) = ((x t : ℕ) : ℝ) := by
        rw [Joints.xe_of_lt t.isLt]; simp
      have : (k : ℝ) < ((x t : ℕ) : ℝ) + 1 := by
        have := min_le_max (a := Joints.P x N t) (b := Joints.P x N (t + 1))
        rw [ex] at f2; linarith
      have : k < (x t : ℕ) + 1 := by exact_mod_cast this
      omega
    · rintro _ ⟨⟨u, v⟩, hp, rfl⟩
      rw [closure_stdRect] at hp
      obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp
      try dsimp only at hu1 hu2 hv1 hv2
      obtain ⟨i1, i2, i3, i4⟩ := Shear.link_image n (Joints.P x N) hC0 t.isLt hβ0 hu1 hu2 hv1 hv2
      have hy := heights hC0 hCn t.isLt i3 i4
      rw [Shear.Ψ_apply]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith

omit hx in
theorem fine_zone (hm : 0 < m) {η : ℝ} (hβ2 : β ≤ η / 10) (hC2 : C ≤ η / 8) (t : ℕ) (ht : t < n) :
    Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' zone t ⊆ region m ∧
      ∀ p ∈ Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' zone t,
        ∀ q ∈ Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' zone t, dist p q ≤ η := by
  have ht' : (t : ℝ) + 1 ≤ n := by exact_mod_cast ht
  have e1 : 0 ≤ C * t := by positivity
  have e2 : C * ((t : ℝ) + 1) ≤ C * n := mul_le_mul_of_nonneg_left ht' hC0.le
  have hr := Joints.P_range hs hN hm (x := x) (t + 1)
  -- the horizontal offset `β (u - 2t - 2)` is at most `7β/5` in absolute value
  have off : ∀ u : ℝ, 2 * (t : ℝ) + 8 / 5 ≤ u → u ≤ 2 * t + 17 / 5 →
      -(2 / 5) * β ≤ β * (u - 2 * t - 2) ∧ β * (u - 2 * t - 2) ≤ 7 / 5 * β := by
    intro u h1 h2
    constructor <;> nlinarith
  constructor
  · rintro _ ⟨⟨u, v⟩, hp, rfl⟩
    obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp
    try dsimp only at hu1 hu2 hv1 hv2
    obtain ⟨i1, i2, i3⟩ := Shear.zone_image n (Joints.P x N) hC0 ht hu1 hu2 hv1 hv2
    have o := off u hu1 hu2
    rw [Shear.Ψ_apply]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only
    · rw [i1]; linarith
    · rw [i1]; linarith
    · linarith
    · linarith
  · rintro _ ⟨⟨u, v⟩, hp, rfl⟩ _ ⟨⟨u', v'⟩, hp', rfl⟩
    obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := hp
    try dsimp only at hu1 hu2 hv1 hv2
    obtain ⟨⟨hu1', hu2'⟩, hv1', hv2'⟩ := hp'
    try dsimp only at hu1' hu2' hv1' hv2'
    obtain ⟨i1, i2, i3⟩ := Shear.zone_image n (Joints.P x N) hC0 ht hu1 hu2 hv1 hv2
    obtain ⟨j1, j2, j3⟩ := Shear.zone_image n (Joints.P x N) hC0 ht hu1' hu2' hv1' hv2'
    have o := off u hu1 hu2
    have o' := off u' hu1' hu2'
    rw [Shear.Ψ_apply, Shear.Ψ_apply]
    apply dist_le_of_abs_le
    · simp only; rw [i1, j1, abs_le]; constructor <;> linarith
    · refine (abs_sub_le_of_mem i2 i3 j2 j3).trans ?_; linarith

omit hx in
theorem first_box (hn : 2 ≤ n) (h0 : (x ⟨0, by omega⟩ : ℕ) = 0) (h1 : (x ⟨1, by omega⟩ : ℕ) = 0) :
    Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' boxA ⊆ boxA := by
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := Joints.P_first hs hN hn h0 h1
  rintro _ ⟨⟨u, v⟩, ⟨⟨hu1, hu2⟩, hv1, hv2⟩, rfl⟩
  try dsimp only at hu1 hu2 hv1 hv2
  obtain ⟨i1, i2, i3, i4⟩ := Shear.link_image n (Joints.P x N) hC0 (t := 0) (u := u) (v := v)
    (by omega) hβ0 (by push_cast; linarith) (by push_cast; linarith) (by linarith) (by linarith)
  have hy := heights hC0 hCn (t := 0) (by omega) i3 i4
  have m1 : 3 / 2 ≤ min (Joints.P x N 0) (Joints.P x N (0 + 1)) := le_min a1 b1
  have m2 : max (Joints.P x N 0) (Joints.P x N (0 + 1)) ≤ 7 / 4 := max_le a2 b2
  rw [Shear.Ψ_apply]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith

omit hx in
theorem last_box (hm : 0 < m) (hn : 2 ≤ n) (h0 : (x ⟨n - 1, by omega⟩ : ℕ) = m - 1)
    (h1 : (x ⟨n - 2, by omega⟩ : ℕ) = m - 1) :
    Shear.Ψ n (Joints.P x N) hβ0.ne' hC0.ne' '' boxB n ⊆ boxB m := by
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := Joints.P_last hs hN hm hn h0 h1
  rintro _ ⟨⟨u, v⟩, ⟨⟨hu1, hu2⟩, hv1, hv2⟩, rfl⟩
  try dsimp only at hu1 hu2 hv1 hv2
  have e : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  obtain ⟨i1, i2, i3, i4⟩ := Shear.link_image n (Joints.P x N) hC0 (t := n - 1) (u := u) (v := v)
    (by omega) hβ0 (by rw [e]; linarith) (by rw [e]; linarith) (by linarith) (by linarith)
  have hy := heights hC0 hCn (t := n - 1) (by omega) i3 i4
  rw [show n - 1 + 1 = n by omega] at i1 i2
  have m1 : 2 * (m : ℝ) - 3 / 4 ≤ min (Joints.P x N (n - 1)) (Joints.P x N n) := le_min a1 b1
  have m2 : max (Joints.P x N (n - 1)) (Joints.P x N n) ≤ 2 * (m : ℝ) - 1 / 2 := max_le a2 b2
  rw [Shear.Ψ_apply]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith

end StdStep

/-- **The planar step, standard coordinates.** -/
theorem std_step {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 12 ≤ N ∧ ∀ (n : ℕ) (x : Fin n → Fin m), 0 < n → Joints.UnitSteps x →
      Joints.Slow x N → ∃ Ψ : Pt ≃ₜ Pt,
        (∀ t : Fin n, Ψ '' closure (stdRect t) ⊆ stdRect (x t)) ∧
        (∀ (t : Fin n) (l : Fin m), (Ψ '' stdRect t ∩ stdRect l).Nonempty →
          ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t') ∧
        (∀ t : Fin n, (∀ p ∈ Ψ '' closure (stdRect t), ∀ q ∈ Ψ '' closure (stdRect t),
            dist p q ≤ η) ∨ ∃ k : ℕ, k < m ∧ Ψ '' closure (stdRect t) ⊆ zone k) ∧
        (∀ t : ℕ, t < n → Ψ '' zone t ⊆ region m ∧
          ∀ p ∈ Ψ '' zone t, ∀ q ∈ Ψ '' zone t, dist p q ≤ η) ∧
        (∀ (h2 : 2 ≤ n), (x ⟨0, by omega⟩ : ℕ) = 0 → (x ⟨1, by omega⟩ : ℕ) = 0 →
          Ψ '' boxA ⊆ boxA) ∧
        (∀ (h2 : 2 ≤ n), (x ⟨n - 1, by omega⟩ : ℕ) = m - 1 → (x ⟨n - 2, by omega⟩ : ℕ) = m - 1 →
          Ψ '' boxB n ⊆ boxB m) := by
  refine ⟨max 12 ⌈1 / η⌉₊, le_max_left _ _, ?_⟩
  intro n x hn hx hs
  have hN : 12 ≤ max 12 ⌈1 / η⌉₊ := le_max_left _ _
  have hNη : 1 / (2 * ((max 12 ⌈1 / η⌉₊ : ℕ) : ℝ)) ≤ η / 2 := by
    have h1 : 1 / η ≤ ((max 12 ⌈1 / η⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hNpos : (0 : ℝ) < ((max 12 ⌈1 / η⌉₊ : ℕ) : ℝ) := by
      have : (12 : ℝ) ≤ ((max 12 ⌈1 / η⌉₊ : ℕ) : ℝ) := by exact_mod_cast hN
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hη] at h1
    nlinarith
  have hβ0 : 0 < min (1 / 100 : ℝ) (η / 10) := lt_min (by norm_num) (by positivity)
  have hC0 : 0 < min (1 / (8 * ((n : ℝ) + 1))) (η / 8) := lt_min (by positivity) (by positivity)
  have hCn : min (1 / (8 * ((n : ℝ) + 1))) (η / 8) * (8 * ((n : ℝ) + 1)) ≤ 1 := by
    have h := min_le_left (1 / (8 * ((n : ℝ) + 1))) (η / 8)
    rw [le_div_iff₀ (by positivity)] at h; linarith
  exact ⟨Shear.Ψ n (Joints.P x _) hβ0.ne' hC0.ne',
    StdStep.follow hx hs hN hβ0 (min_le_left _ _) hC0 hCn,
    StdStep.tight hx hs hN hβ0 (min_le_left _ _) hC0,
    StdStep.small hx hs hN hβ0 (min_le_left _ _) hC0 hCn (min_le_right _ _) (min_le_right _ _) hNη,
    StdStep.fine_zone hs hN hβ0 (min_le_left _ _) hC0 hCn hm (min_le_right _ _)
      (min_le_right _ _),
    StdStep.first_box hs hN hβ0 (min_le_left _ _) hC0 hCn,
    StdStep.last_box hs hN hβ0 (min_le_left _ _) hC0 hCn hm⟩

end HPC.Plane
