import HPC.Fold.T7Assemble
import HPC.Plane.Joints

/-!
# Stuttered Bing patterns, and crookedness from tightness

Batch 84. The planar step needs patterns that are *slow*; Bing's crooked pattern `bingF d` is not.
Repeating every value `K` times (`u ↦ bingF d (u / K)`) keeps it crooked and makes it `K`-slow.
`crooked_of_tight_pat` is `crooked_of_tight` (batch 82) for an arbitrary crooked pattern with unit
steps.
-/

namespace HPC.Plane

open HPC.Fold

variable {X : Type*} [MetricSpace X]

/-- `crooked_of_tight` for an arbitrary crooked level sequence `g` with unit steps. -/
theorem crooked_of_tight_pat {n m : ℕ} {F : Chain X n} {D : Chain X m} (g : ℕ → ℤ)
    (hlip : ∀ u, |g (u + 1) - g u| ≤ 1) (hcr : PatCrookedOn g 0 (n - 1))
    (h1 : ∀ u : Fin n, ∃ i : Fin m, (i : ℤ) = g u ∧ F.link u ⊆ D.link i)
    (h2 : ∀ (u : Fin n) (l : Fin m), (F.link u ∩ D.link l).Nonempty →
      ∃ u' : ℕ, u' < n ∧ u' ≤ u.val + 1 ∧ u.val ≤ u' + 1 ∧ (l : ℤ) = g u') :
    F.IsCrookedIn' D := by
  have hsub : ∀ (u : Fin n) (i : Fin m), (i : ℤ) = g u → F.link u ⊆ D.link i := by
    intro u i hi
    obtain ⟨i', hi', hsub'⟩ := h1 u
    have : i' = i := Fin.ext (by omega)
    rw [← this]; exact hsub'
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := h1 u
    exact ⟨i, hi⟩
  intro h k hk i j hi hj
  obtain ⟨u', hu1, hu2, hu3, hu4⟩ := h2 i h hi
  obtain ⟨v', hv1, hv2, hv3, hv4⟩ := h2 j k hj
  obtain ⟨r, s, hb, hr, hs⟩ := hcr u' v' (Nat.zero_le _) (by omega)
    (Nat.zero_le _) (by omega) h k (by rw [hu4]) (by rw [hv4]) (by omega)
  have near : ∀ (a b : ℕ), a ≤ b + 1 → b ≤ a + 1 → |g a - g b| ≤ 1 := by
    intro a b hab hba
    rcases (show a = b ∨ a = b + 1 ∨ b = a + 1 by omega) with e | e | e
    · subst e; simp
    · subst e; exact hlip b
    · subst e; rw [abs_sub_comm]; exact hlip a
  have ni := near u' i hu2 hu3
  have nj := near v' j hv2 hv3
  rw [abs_le] at ni nj
  have hbr : r < n := by unfold NBetween at hb; omega
  have hbs : s < n := by unfold NBetween at hb; omega
  have hri : r ≠ i.val := fun e => by rw [e] at hr; omega
  have hsj : s ≠ j.val := fun e => by rw [e] at hs; omega
  refine ⟨⟨r, hbr⟩, ⟨s, hbs⟩, ?_, hsub _ _ (by simp only; rw [hr]; omega),
    hsub _ _ (by simp only; rw [hs]; omega)⟩
  unfold NBetween at hb
  unfold Chain.Between
  simp only [Fin.lt_def, gt_iff_lt]
  omega

/-- The stuttered Bing pattern. -/
def stut (d K : ℕ) (u : ℕ) : ℤ := bingF d (u / K)

theorem stut_lip (d K : ℕ) (u : ℕ) : |stut d K (u + 1) - stut d K u| ≤ 1 := by
  unfold stut
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  have : (u + 1) / K = u / K ∨ (u + 1) / K = u / K + 1 := by
    rcases Nat.lt_or_ge ((u + 1) % K) 1 with h | h
    · right
      have h1 := Nat.div_add_mod (u + 1) K
      have h2 := Nat.div_add_mod u K
      have h3 := Nat.mod_lt u hK
      have h4 : (u + 1) % K = 0 := by omega
      have : (u + 1) / K * K = u + 1 := by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h4); linarith
      have h5 : u / K * K ≤ u := Nat.div_mul_le_self u K
      have h6 : u < (u / K + 1) * K := by
        have := Nat.lt_div_mul_add (a := u) hK; linarith
      have h7 : u / K < (u + 1) / K := by
        by_contra hc; push_neg at hc
        have := Nat.mul_le_mul_right K hc; linarith
      have h8 : (u + 1) / K ≤ u / K + 1 := by
        by_contra hc; push_neg at hc
        have := Nat.mul_le_mul_right K (show u / K + 2 ≤ (u + 1) / K by omega)
        nlinarith
      omega
    · left
      have h1 := Nat.div_add_mod (u + 1) K
      have h2 := Nat.div_add_mod u K
      have h3 := Nat.mod_lt u hK
      have h3' := Nat.mod_lt (u + 1) hK
      have hmod : (u + 1) % K = u % K + 1 := by
        rw [Nat.add_mod]
        rcases Nat.lt_or_ge (u % K + 1) K with c | c
        · rw [Nat.one_mod_eq_one.mpr (by omega), Nat.mod_eq_of_lt c]
        · exfalso
          have : u % K + 1 = K := by omega
          have : (u + 1) % K = 0 := by
            rw [Nat.add_mod, Nat.one_mod_eq_one.mpr (by omega), this, Nat.mod_self]
          omega
      have : (u + 1) / K * K = u / K * K := by
        have e1 : K * ((u + 1) / K) = K * (u / K) := by omega
        linarith [mul_comm K ((u + 1) / K), mul_comm K (u / K)]
      exact Nat.eq_of_mul_eq_mul_right hK this
  rcases this with e | e
  · rw [e]; simp
  · rw [e]; exact bingF_lip d _

theorem stut_crooked (d K : ℕ) (hK : 0 < K) : PatCrookedOn (stut d K) 0 (K * z d - 1) := by
  intro i j _ hi _ hj h k hgi hgj hhk
  have hz := z_pos d
  have hKz : 1 ≤ K * z d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hi' : i / K ≤ z d - 1 := by
    have : i / K < z d := (Nat.div_lt_iff_lt_mul hK).mpr (by rw [mul_comm]; omega)
    omega
  have hj' : j / K ≤ z d - 1 := by
    have : j / K < z d := (Nat.div_lt_iff_lt_mul hK).mpr (by rw [mul_comm]; omega)
    omega
  obtain ⟨r, s, hb, hr, hs⟩ := bingF_crooked d (i / K) (j / K) (Nat.zero_le _) hi'
    (Nat.zero_le _) hj' h k hgi hgj hhk
  refine ⟨r * K, s * K, ?_, ?_, ?_⟩
  · unfold NBetween at hb ⊢
    rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      refine ⟨?_, Nat.mul_lt_mul_of_pos_right h2 hK, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hK).mp h1
      · have : (s + 1) * K ≤ j := (Nat.le_div_iff_mul_le hK).mp h3
        nlinarith
    · right
      refine ⟨(Nat.div_lt_iff_lt_mul hK).mp h1, Nat.mul_lt_mul_of_pos_right h2 hK, ?_⟩
      have : (r + 1) * K ≤ i := (Nat.le_div_iff_mul_le hK).mp h3
      nlinarith
  · unfold stut; rw [Nat.mul_div_cancel _ hK]; exact hr
  · unfold stut; rw [Nat.mul_div_cancel _ hK]; exact hs

theorem stut_range (d K u : ℕ) : 0 ≤ stut d K u ∧ stut d K u ≤ d := bingF_range d _

/-- The stuttered pattern as a map of indices. -/
def stutPat (m K : ℕ) (hm : 0 < m) : Fin (K * z (m - 1)) → Fin m := fun u =>
  ⟨(stut (m - 1) K u).toNat, by
    have := stut_range (m - 1) K u
    have : ((m - 1 : ℕ) : ℤ) = m - 1 := by push_cast [Nat.cast_sub hm]; ring
    omega⟩

theorem stutPat_val (m K : ℕ) (hm : 0 < m) (u : Fin (K * z (m - 1))) :
    ((stutPat m K hm u : ℕ) : ℤ) = stut (m - 1) K u := by
  simp only [stutPat]
  exact Int.toNat_of_nonneg (stut_range (m - 1) K u).1

theorem stutPat_unitSteps (m K : ℕ) (hm : 0 < m) : Joints.UnitSteps (stutPat m K hm) := by
  intro t t' h
  have := stut_lip (m - 1) K t
  rw [stutPat_val, stutPat_val, show (t' : ℕ) = t + 1 from h]
  rw [abs_le] at this; omega

theorem stutPat_slow (m K : ℕ) (hm : 0 < m) (hK : 0 < K) : Joints.Slow (stutPat m K hm) K := by
  intro s s' h
  rw [stutPat_val, stutPat_val] at h
  by_contra hc
  push_neg at hc
  -- indices less than `K` apart have block numbers at most one apart
  have hb : (s : ℕ) / K ≤ (s' : ℕ) / K + 1 ∧ (s' : ℕ) / K ≤ (s : ℕ) / K + 1 := by
    have e1 := Nat.div_mul_le_self (s : ℕ) K
    have e2 := Nat.div_mul_le_self (s' : ℕ) K
    have f1 := Nat.lt_div_mul_add (a := (s : ℕ)) hK
    have f2 := Nat.lt_div_mul_add (a := (s' : ℕ)) hK
    constructor
    · by_contra c; push_neg at c
      have h3 : ((s' : ℕ) / K + 2) * K ≤ (s : ℕ) / K * K := Nat.mul_le_mul_right K c
      have h4 : ((s' : ℕ) / K + 2) * K = (s' : ℕ) / K * K + 2 * K := by ring
      omega
    · by_contra c; push_neg at c
      have h3 : ((s : ℕ) / K + 2) * K ≤ (s' : ℕ) / K * K := Nat.mul_le_mul_right K c
      have h4 : ((s : ℕ) / K + 2) * K = (s : ℕ) / K * K + 2 * K := by ring
      omega
  unfold stut at h
  rcases (show (s : ℕ) / K = (s' : ℕ) / K ∨ (s : ℕ) / K + 1 = (s' : ℕ) / K ∨
      (s' : ℕ) / K + 1 = (s : ℕ) / K by omega) with e | e | e
  · rw [e] at h; omega
  · have := bingF_lip (m - 1) ((s : ℕ) / K); rw [e, abs_le] at this; omega
  · have := bingF_lip (m - 1) ((s' : ℕ) / K); rw [e, abs_le] at this; omega

end HPC.Plane
