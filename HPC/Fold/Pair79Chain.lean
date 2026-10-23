import HPC.Fold.Pair79Excl

/-!
# Batch 79: the prefix fold for a two-link basepoint

`pair_prefix_fold`: for adjacent links `r`, `r' = r + 1` and a link `a ≥ r` meeting the first
coarse link, a fold of the chain on `[0, a]`, read either on the least or on the greatest coarse
indices, sending both `r` and `r'` to time `0` (or, when `a = r`, with `U = 0`).
-/

namespace HPC.Fold.B79

open HPC.Chain Z77

variable {X : Type*} [MetricSpace X]

/-- The data of a prefix fold for the basepoint pair `(r, r')` on `[0, a]`. -/
def PrefixFold {n : ℕ} (ρ σ : Fin n → ℤ) (r r' a : Fin n) : Prop :=
  ∃ (lP : Fin n → ℤ) (cP : ℕ → ℤ) (βP : Fin n → ℕ) (U : ℕ),
    (∀ t, ρ t ≤ lP t ∧ lP t ≤ σ t) ∧ βP r = 0 ∧
    ((r' ≤ a ∧ βP r' = 0) ∨ (a = r ∧ U = 0)) ∧
    (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(βP t' : ℤ) - βP t| ≤ 1) ∧
    (∀ t, t ≤ a → |lP t - cP (βP t)| ≤ 1) ∧ |(U : ℤ) - βP a| ≤ 1 ∧ cP U ≤ 1

/-- **The crookedness clause at a link meeting the first coarse link**, with the level of the
earlier link any coarse index containing it. -/
theorem meet_low_gen {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 2 ≤ N) (a t : Fin n) (ha : (E.link a ∩ D.link ⟨0, by omega⟩).Nonempty) (hta : t < a)
    (k : Fin N) (hk : 3 ≤ k.val) (htk : E.link t ⊆ D.link k) :
    ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧ E.link y ⊆ D.link ⟨1, by omega⟩ ∧
      E.link y' ⊆ D.link ⟨k.val - 1, by omega⟩ := by
  obtain ⟨z, hz⟩ := E.link_nonempty t
  obtain ⟨r, s, hbtw, hr, hs⟩ := hcr.2 ⟨0, by omega⟩ k (by simp only; omega) a t ha
    ⟨z, hz, htk hz⟩
  have hta' : t.val < a.val := hta
  rcases hbtw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso
    have : a.val < t.val := lt_trans (lt_trans h1 h2) h3
    omega
  · exact ⟨s, r, h3, h2, h1, hs, hr⟩

/-- The greatest coarse index of a link meeting the first coarse link is at most `1`. -/
theorem maxIdx_near_zero {n N : ℕ} {E : Chain X n} {D : Chain X N} (h : E.Refines D)
    (hN : 0 < N) (a : Fin n) (ha : (E.link a ∩ D.link ⟨0, hN⟩).Nonempty) :
    (h.maxIdx a).val ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := ha
  have := (D.adjacent _ _).mp ⟨z, maxIdx_subset h a hz1, hz2⟩
  simp only at this; omega

theorem minIdx_reverse {n N : ℕ} {E : Chain X n} {D : Chain X N} (h : E.Refines D) (t : Fin n) :
    ((h.reverse_right.minIdx t : ℕ) : ℤ) = (N : ℤ) - 1 - ((h.maxIdx t : ℕ) : ℤ) := by
  unfold Chain.Refines.maxIdx
  rw [Fin.val_rev]
  have := (h.reverse_right.minIdx t).isLt
  omega

/-- The two sequences of a crooked refinement. -/
theorem seq_facts {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D) :
    let ρ : Fin n → ℤ := fun t => ((hcr.1.minIdx t : ℕ) : ℤ)
    let σ : Fin n → ℤ := fun t => ((hcr.1.maxIdx t : ℕ) : ℤ)
    IsCrookedIvF ρ σ ∧ IsCrookedIvF (fun t => (N : ℤ) - 1 - σ t) (fun t => (N : ℤ) - 1 - ρ t) ∧
      (∀ t, 0 ≤ ρ t) ∧ (∀ t, σ t ≤ (N : ℤ) - 1) ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → |ρ t' - ρ t| ≤ 1) ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → |σ t' - σ t| ≤ 1) := by
  intro ρ σ
  have hI := isCrookedIvF_minIdx_maxIdx hcr
  have hIr := isCrookedIvF_minIdx_maxIdx hcr.reverse_right
  have e1 : (fun t => ((hcr.reverse_right.1.minIdx t : ℕ) : ℤ)) = fun t => (N : ℤ) - 1 - σ t := by
    funext t; exact minIdx_reverse hcr.1 t
  have e2 : (fun t => ((hcr.reverse_right.1.maxIdx t : ℕ) : ℤ)) = fun t => (N : ℤ) - 1 - ρ t := by
    funext t
    have h1 := minIdx_le hcr.reverse_right.1 t (j := Fin.rev (hcr.1.minIdx t))
      (by rw [reverse_link, Fin.rev_rev]; exact minIdx_subset hcr.1 t)
    have h2 := le_maxIdx hcr.reverse_right.1 t (j := Fin.rev (hcr.1.minIdx t))
      (by rw [reverse_link, Fin.rev_rev]; exact minIdx_subset hcr.1 t)
    have h3 := maxIdx_subset hcr.reverse_right.1 t
    rw [reverse_link] at h3
    have h4 := minIdx_le hcr.1 t h3
    rw [Fin.le_def] at h2 h4
    rw [Fin.val_rev] at h2 h4
    have := (hcr.1.minIdx t).isLt
    have := (hcr.reverse_right.1.maxIdx t).isLt
    simp only [ρ]; omega
  refine ⟨hI, ?_, fun t => by positivity, fun t => ?_, fun t t' h => ?_, fun t t' h => ?_⟩
  · have := hIr; rw [e1, e2] at this; exact this
  · have := (hcr.1.maxIdx t).isLt; simp only [σ]; omega
  · have := minIdx_lip hcr.1 t t' h; simp only [ρ]; rw [abs_le]; omega
  · have := maxIdx_lip hcr.1 t t' h; simp only [σ]; rw [abs_le]; omega

/-- **The prefix fold for two-link basepoints.** -/
theorem pair_prefix_fold {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 4 ≤ N) (r r' a : Fin n) (hr : r'.val = r.val + 1) (hra : r ≤ a)
    (ha : (E.link a ∩ D.link ⟨0, by omega⟩).Nonempty) :
    PrefixFold (fun t => ((hcr.1.minIdx t : ℕ) : ℤ)) (fun t => ((hcr.1.maxIdx t : ℕ) : ℤ))
      r r' a := by
  classical
  obtain ⟨hI, hIr, hnn, hσN, hlipρ, hlipσ⟩ := seq_facts hcr
  set ρ : Fin n → ℤ := fun t => ((hcr.1.minIdx t : ℕ) : ℤ) with hρdef
  set σ : Fin n → ℤ := fun t => ((hcr.1.maxIdx t : ℕ) : ℤ) with hσdef
  set f : Fin n → ℤ := fun t => (N : ℤ) - 1 - σ t with hfdef
  have hρσ : ∀ t, ρ t ≤ σ t := hI.le
  have hwid : ∀ t, σ t ≤ ρ t + 1 := hI.width
  have hρN : ∀ t, ρ t ≤ (N : ℤ) := fun t => by have := hρσ t; have := hσN t; omega
  have hρa : ρ a ≤ 1 := by
    have := minIdx_near_of_inter hcr.1 a ⟨0, by omega⟩ ha
    simp only [hρdef] at this ⊢; omega
  have hσa : σ a ≤ 1 := by
    have := maxIdx_near_zero hcr.1 (by omega) a ha
    simp only [hσdef]; omega
  have hmeetρ : ∀ t : Fin n, t < a → 3 ≤ ρ t → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      ρ y ≤ 1 ∧ ρ t - 2 ≤ ρ y' ∧ ρ y' ≤ ρ t - 1 := by
    intro t hta h3
    have h3u : (3 : ℤ) ≤ ((hcr.1.minIdx t : ℕ) : ℤ) := h3
    obtain ⟨y, y', h1, h2, h3', hy, hy'⟩ := meet_low_gen hcr (by omega) a t ha hta
      (hcr.1.minIdx t) (by simp only [hρdef] at h3; omega) (minIdx_subset hcr.1 t)
    refine ⟨y, y', h1, h2, h3', ?_, ?_, ?_⟩
    · have := minIdx_le hcr.1 y hy
      rw [Fin.le_def] at this; simp only [hρdef]; simp only at this; omega
    · have := subset_adjacent_of_subset hcr.1 y' (minIdx_subset hcr.1 y') hy'
      simp only [hρdef]; simp only at this; omega
    · have := minIdx_le hcr.1 y' hy'
      rw [Fin.le_def] at this; simp only [hρdef]; simp only at this; omega
  have hmeetA : ∀ t : Fin n, t < a → 3 ≤ ρ t → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      ρ y ≤ 1 ∧ ρ t - 1 ≤ σ y' := by
    intro t hta h3
    have h3u : (3 : ℤ) ≤ ((hcr.1.minIdx t : ℕ) : ℤ) := h3
    obtain ⟨y, y', h1, h2, h3', hy, hy'⟩ := meet_low_gen hcr (by omega) a t ha hta
      (hcr.1.minIdx t) (by simp only [hρdef] at h3; omega) (minIdx_subset hcr.1 t)
    refine ⟨y, y', h1, h2, h3', ?_, ?_⟩
    · have := minIdx_le hcr.1 y hy
      rw [Fin.le_def] at this; simp only [hρdef]; simp only at this; omega
    · have := le_maxIdx hcr.1 y' hy'
      rw [Fin.le_def] at this; simp only [hσdef, hρdef]; simp only at this; omega
  have hmeetσ : ∀ t : Fin n, t < a → f t + 3 ≤ (N : ℤ) - 1 → ∃ y y' : Fin n, t < y ∧ y < y' ∧
      y' < a ∧ (N : ℤ) - 1 - 2 ≤ f y ∧ f y ≤ (N : ℤ) - 1 - 1 ∧ f t ≤ f y' ∧ f y' ≤ f t + 1 := by
    intro t hta h3
    have h3u : (3 : ℤ) ≤ ((hcr.1.maxIdx t : ℕ) : ℤ) := by
      simp only [hfdef, hσdef] at h3; omega
    obtain ⟨y, y', h1, h2, h3', hy, hy'⟩ := meet_low_gen hcr (by omega) a t ha hta
      (hcr.1.maxIdx t) (by simp only [hfdef, hσdef] at h3; omega) (maxIdx_subset hcr.1 t)
    refine ⟨y, y', h1, h2, h3', ?_, ?_, ?_, ?_⟩
    · have := subset_adjacent_of_subset hcr.1 y (maxIdx_subset hcr.1 y) hy
      simp only [hfdef, hσdef]; simp only at this; omega
    · have := le_maxIdx hcr.1 y hy
      rw [Fin.le_def] at this; simp only [hfdef, hσdef]; simp only at this; omega
    · have := subset_adjacent_of_subset hcr.1 y' (maxIdx_subset hcr.1 y') hy'
      simp only [hfdef, hσdef]; simp only at this; omega
    · have := le_maxIdx hcr.1 y' hy'
      rw [Fin.le_def] at this; simp only [hfdef, hσdef]; simp only at this; omega
  have hcrρ : ∀ i : Fin n, CrkOn (reindex ρ i) (-(i.val : ℤ)) ((n : ℤ) - 1 - i.val) :=
    fun i => crkOn_of_isCrookedIvF hI i
  have hcrf : ∀ i : Fin n, CrkOn (reindex f i) (-(i.val : ℤ)) ((n : ℤ) - 1 - i.val) :=
    fun i => crkOn_of_isCrookedIvF hIr i
  have hlipf : ∀ t t' : Fin n, t'.val = t.val + 1 → |f t' - f t| ≤ 1 := by
    intro t t' h; have := hlipσ t t' h; simp only [hfdef]; rw [abs_le] at this ⊢; omega
  have hnnf : ∀ t, 0 ≤ f t := fun t => by have := hσN t; simp only [hfdef]; omega
  have hHf : ∀ t, f t ≤ (N : ℤ) - 1 := fun t => by
    have := hnn t; have := hρσ t; simp only [hfdef]; omega
  have hendf : (N : ℤ) - 1 - 1 ≤ f a := by simp only [hfdef]; omega
  rcases eq_or_lt_of_le hra with hra' | hra'
  · -- the low link is `r` itself
    subst hra'
    obtain ⟨c, β, U, b0, blip, bw, bU, bcU, bc0, -, bU0⟩ :=
      finfold_low ρ r r le_rfl N (hcrρ r) hlipρ hnn hρN hρa hmeetρ false (by
        simp only [Bool.false_eq_true, if_false]
        rintro (⟨t, -, ht, -⟩ | ⟨h0, -⟩)
        · have := hnn t; omega
        · omega)
    have hU0 : U = 0 := bU0 rfl (by
      rw [bc0]; simp only [Bool.false_eq_true, if_false]; have := hnn r
      rw [abs_le]; constructor <;> omega)
    exact ⟨ρ, c, β, U, fun t => ⟨le_rfl, hρσ t⟩, b0, Or.inr ⟨rfl, hU0⟩, blip, bw, bU, bcU⟩
  have hr'a : r' ≤ a := by rw [Fin.le_def]; rw [Fin.lt_def] at hra'; omega
  have key : ∀ lo hi : Fin n, (lo.val = hi.val + 1 ∨ hi.val = lo.val + 1) → lo ≤ a → hi ≤ a →
      ρ hi = ρ lo + 1 → σ hi = ρ lo + 1 →
      ∃ (lP : Fin n → ℤ) (cP : ℕ → ℤ) (βP : Fin n → ℕ) (U : ℕ),
        (∀ t, ρ t ≤ lP t ∧ lP t ≤ σ t) ∧ βP lo = 0 ∧ βP hi = 0 ∧
        (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(βP t' : ℤ) - βP t| ≤ 1) ∧
        (∀ t, t ≤ a → |lP t - cP (βP t)| ≤ 1) ∧ |(U : ℤ) - βP a| ≤ 1 ∧ cP U ≤ 1 := by
    intro lo hi hadj hlo hhi hρ' hσ'
    by_cases hup : EvUp ρ lo a 0
    · have hdn : ¬ EvDown σ hi a 0 := fun h =>
        pair_exclusion ρ σ hI lo hi a hadj hlo hρ' hσ' hnn hmeetA hup h
      have hok : ¬ EvUp f hi a ((N : ℤ) - 1) := by
        have := (evUp_reflect σ ((N : ℤ) - 1) hi a 0).not.mpr hdn
        rwa [sub_zero] at this
      obtain ⟨c, β, U, b0, blip, bw, bU, bcU, bc0, bz⟩ :=
        finfold_high f hi a hhi ((N : ℤ) - 1) (hcrf hi) hlipf hnnf hHf hendf hmeetσ true
          (by simpa using hok)
      simp only [if_true] at bc0
      refine ⟨σ, fun u => (N : ℤ) - 1 - c u, β, U, fun t => ⟨hρσ t, le_rfl⟩, ?_, b0, blip,
        fun t ht => ?_, bU, by beta_reduce; omega⟩
      · refine bz lo hlo (by omega) ?_
        rw [bc0]; simp only [hfdef]
        have := hρσ lo; have := hwid lo
        rw [abs_le]; constructor <;> omega
      · have := bw t ht; simp only [hfdef] at this; beta_reduce; rw [abs_le] at this ⊢; omega
    · obtain ⟨c, β, U, b0, blip, bw, bU, bcU, bc0, bz, -⟩ :=
        finfold_low ρ lo a hlo N (hcrρ lo) hlipρ hnn hρN hρa hmeetρ true (by simpa using hup)
      simp only [if_true] at bc0
      refine ⟨ρ, c, β, U, fun t => ⟨le_rfl, hρσ t⟩, b0, ?_, blip, bw, bU, bcU⟩
      refine bz hi hhi (by omega) ?_
      rw [bc0, abs_le]; constructor <;> omega
  by_cases heq : ρ r' = ρ r
  · obtain ⟨above, c, β, U, b0, blip, bw, bU, bcU, bc0, bz, -⟩ :=
      finfold_low_any ρ r a hra N (hcrρ r) hlipρ hnn hρN hρa hmeetρ
    refine ⟨ρ, c, β, U, fun t => ⟨le_rfl, hρσ t⟩, b0, Or.inl ⟨hr'a, ?_⟩, blip, bw, bU, bcU⟩
    refine bz r' hr'a (Or.inr hr) ?_
    rw [bc0, heq]; cases above <;> simp
  · have hadjI := hI.adj r r' hr
    simp only [max_le_iff] at hadjI
    have hm1 := min_le_left (ρ r) (ρ r')
    have hm2 := min_le_right (ρ r) (ρ r')
    have hm3 : min (ρ r) (ρ r') = ρ r ∨ min (ρ r) (ρ r') = ρ r' := min_choice _ _
    have hl := hlipρ r r' hr
    rw [abs_le] at hl
    have hlo := hρσ r; have hhi := hρσ r'
    rcases (show ρ r' = ρ r + 1 ∨ ρ r = ρ r' + 1 by omega) with h | h
    · obtain ⟨lP, cP, βP, U, k1, k2, k3, k4, k5, k6, k7⟩ :=
        key r r' (Or.inr hr) hra hr'a h (by omega)
      exact ⟨lP, cP, βP, U, k1, k2, Or.inl ⟨hr'a, k3⟩, k4, k5, k6, k7⟩
    · obtain ⟨lP, cP, βP, U, k1, k2, k3, k4, k5, k6, k7⟩ :=
        key r' r (Or.inl hr) hr'a hra h (by omega)
      exact ⟨lP, cP, βP, U, k1, k3, Or.inl ⟨hr'a, k2⟩, k4, k5, k6, k7⟩

end HPC.Fold.B79
