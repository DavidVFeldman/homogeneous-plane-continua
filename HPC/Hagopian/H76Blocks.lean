import HPC.Hagopian.Hagopian76V

/-!
# Batch 178, §6: the blocks (C′)

`blocks_of_finset`: for a finite family `I` of nondegenerate closed intervals `[r₁, r₂]` of `[0, 1]`
lying beyond `e > 0`, the components of `St J = [0, e] ∪ ⋃ I` are blocks `[x₂ᵢ₋₁, x₂ᵢ]`,
`1 ≤ i ≤ n`, with `x₁ = 0 < x₂ = e < x₃ < ⋯ < x₂ₙ`: every member of `I` lies in a block, every point
of a block lies in `[0, e]` or in a member of `I` (each block is a union of members of `J`), no member
of `I` meets a gap `(x₂ᵢ, x₂ᵢ₊₁)`, and `x₂ₙ` is the largest right end. Induction on `I`, adding the
member with the largest left end.

`exists_blocks_aux`: the Hagopian form, with `x₂ₙ = 1` from `LastIntervalReachesOne`.

*Shape change (recorded in the report):* the members of `I` are assumed **nondegenerate**
(`r₁ < r₂`). A crossing component inside a single layer `d⁻¹(u)` would give a member `[u, u]`, and a
block `[u, u]` isolated from the others would violate the strict monotonicity of `x` required by
`hagopian76_T15_T17_cond_fix`. That no crossing component lies in a single layer is not proved.
-/

namespace HPC.Hagopian

open Set HPC.Plane

/-- **The blocks of `St J`, combinatorial core.** -/
theorem blocks_of_finset {e : unitInterval} (he : 0 < e) (Is : Finset (unitInterval × unitInterval))
    (hnd : ∀ r ∈ Is, r.1 < r.2) (hle : ∀ r ∈ Is, e < r.1) :
    ∃ n, 1 ≤ n ∧ ∃ x : ℕ → unitInterval, StrictMonoOn x (Icc 1 (2 * n)) ∧ x 1 = 0 ∧ x 2 = e ∧
      (∀ r ∈ Is, ∃ i, 1 ≤ i ∧ i ≤ n ∧ x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
      (∀ r ∈ Is, r.2 ≤ x (2 * n)) ∧
      (x (2 * n - 1) = 0 ∨ ∃ r ∈ Is, r.1 = x (2 * n - 1)) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
        t ≤ e ∨ ∃ r ∈ Is, t ∈ Icc r.1 r.2) ∧
      (∀ i, 1 ≤ i → i < n → ∀ r ∈ Is, r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) := by
  induction Is using Finset.induction_on_max_value (fun r : unitInterval × unitInterval => r.1)
    with
  | h0 =>
    refine ⟨1, le_rfl, fun i => if i ≤ 1 then 0 else e, ?_, by simp, by simp, by simp, by simp,
      Or.inl (by simp), ?_, fun i hi hin => by omega⟩
    · intro i hi j hj hij
      simp only [mem_Icc] at hi hj
      have hi1 : i = 1 := by omega
      have hj2 : j = 2 := by omega
      subst hi1 hj2
      simpa using he
    · intro i hi hin t ht
      have : i = 1 := by omega
      subst this
      left
      simpa using ht.2
  | step a s has hmax ih =>
    obtain ⟨n, hn, x, hmono, hx1, hx2, hmem, hbound, hlast, hunion, hgap⟩ :=
      ih (fun r hr => hnd r (Finset.mem_insert_of_mem hr))
        (fun r hr => hle r (Finset.mem_insert_of_mem hr))
    have hna := hnd a (Finset.mem_insert_self a s)
    have hea := hle a (Finset.mem_insert_self a s)
    have hxle : ∀ i j, 1 ≤ i → i ≤ j → j ≤ 2 * n → x i ≤ x j := fun i j hi hij hj =>
      hmono.monotoneOn ⟨hi, by omega⟩ ⟨by omega, hj⟩ hij
    by_cases hc : x (2 * n) < a.1
    · -- a new block `[a₁, a₂]`
      set x' : ℕ → unitInterval := fun i => if i ≤ 2 * n then x i else
        if i = 2 * n + 1 then a.1 else a.2 with hx'
      have hx'le : ∀ i, i ≤ 2 * n → x' i = x i := fun i hi => by simp [hx', hi]
      have hx'1 : x' (2 * n + 1) = a.1 := by simp [hx']
      have hx'2 : x' (2 * n + 2) = a.2 := by simp [hx']
      refine ⟨n + 1, by omega, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi j hj hij
        simp only [mem_Icc] at hi hj
        by_cases hj' : j ≤ 2 * n
        · rw [hx'le i (by omega), hx'le j hj']
          exact hmono ⟨hi.1, by omega⟩ ⟨by omega, hj'⟩ hij
        · have hjv : a.1 ≤ x' j := by
            rcases (show j = 2 * n + 1 ∨ j = 2 * n + 2 by omega) with h | h
            · rw [h, hx'1]
            · rw [h, hx'2]; exact hna.le
          by_cases hi' : i ≤ 2 * n
          · rw [hx'le i hi']
            exact lt_of_le_of_lt (hxle i (2 * n) hi.1 hi' le_rfl) (lt_of_lt_of_le hc hjv)
          · have hi2 : i = 2 * n + 1 := by omega
            have hj2 : j = 2 * n + 2 := by omega
            rw [hi2, hj2, hx'1, hx'2]; exact hna
      · rw [hx'le 1 (by omega)]; exact hx1
      · rw [hx'le 2 (by omega)]; exact hx2
      · intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr
        · refine ⟨n + 1, by omega, le_rfl, ?_, ?_⟩
          · rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, hx'1]
          · rw [show 2 * (n + 1) = 2 * n + 2 by omega, hx'2]
        · obtain ⟨i, hi1, hin, h1, h2⟩ := hmem r hr
          refine ⟨i, hi1, by omega, ?_, ?_⟩
          · rw [hx'le _ (by omega)]; exact h1
          · rw [hx'le _ (by omega)]; exact h2
      · intro r hr
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, hx'2]
        rcases Finset.mem_insert.1 hr with rfl | hr
        · exact le_rfl
        · exact ((hbound r hr).trans hc.le).trans hna.le
      · right
        exact ⟨a, Finset.mem_insert_self a s, by
          rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, hx'1]⟩
      · intro i hi1 hin t ht
        by_cases hi' : i ≤ n
        · rw [hx'le _ (by omega), hx'le _ (by omega)] at ht
          rcases hunion i hi1 hi' t ht with h | ⟨r, hr, hrt⟩
          · exact Or.inl h
          · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hrt⟩
        · have : i = n + 1 := by omega
          subst this
          rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, hx'1,
            show 2 * (n + 1) = 2 * n + 2 by omega, hx'2] at ht
          exact Or.inr ⟨a, Finset.mem_insert_self a s, ht⟩
      · intro i hi1 hin r hr
        by_cases hi' : i < n
        · rw [hx'le _ (by omega), hx'le _ (by omega)]
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact Or.inr ((hxle _ _ (by omega) (by omega) le_rfl).trans hc.le)
          · exact hgap i hi1 hi' r hr
        · have : i = n := by omega
          subst this
          rcases Finset.mem_insert.1 hr with rfl | hr
          · right; rw [hx'1]
          · left; rw [hx'le _ le_rfl]; exact hbound r hr
    · -- `a` joins the last block
      push_neg at hc
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        subst this
        rw [hx2] at hc
        exact absurd hc (not_le.2 hea)
      set x' : ℕ → unitInterval := fun i => if i = 2 * n then max (x (2 * n)) a.2 else x i
        with hx'
      have hx'ne : ∀ i, i ≠ 2 * n → x' i = x i := fun i hi => by simp [hx', hi]
      have hx'n : x' (2 * n) = max (x (2 * n)) a.2 := by simp [hx']
      have hlast' : x (2 * n - 1) ≤ a.1 := by
        rcases hlast with h | ⟨r, hr, h⟩
        · rw [h]; exact unitInterval.nonneg'
        · rw [← h]; exact hmax r hr
      refine ⟨n, hn, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi j hj hij
        simp only [mem_Icc] at hi hj
        rw [hx'ne i (by omega)]
        by_cases hj' : j = 2 * n
        · rw [hj', hx'n]
          exact lt_of_lt_of_le (hmono ⟨hi.1, by omega⟩ ⟨by omega, le_rfl⟩ (by omega))
            (le_max_left _ _)
        · rw [hx'ne j hj']
          exact hmono ⟨hi.1, by omega⟩ ⟨by omega, hj.2⟩ hij
      · rw [hx'ne 1 (by omega)]; exact hx1
      · rw [hx'ne 2 (by omega)]; exact hx2
      · intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr
        · refine ⟨n, hn, le_rfl, ?_, ?_⟩
          · rw [hx'ne _ (by omega)]; exact hlast'
          · rw [hx'n]; exact le_max_right _ _
        · obtain ⟨i, hi1, hin, h1, h2⟩ := hmem r hr
          refine ⟨i, hi1, hin, ?_, ?_⟩
          · rw [hx'ne _ (by omega)]; exact h1
          · by_cases hi : 2 * i = 2 * n
            · rw [hi, hx'n]; rw [hi] at h2; exact h2.trans (le_max_left _ _)
            · rw [hx'ne _ hi]; exact h2
      · intro r hr
        rw [hx'n]
        rcases Finset.mem_insert.1 hr with rfl | hr
        · exact le_max_right _ _
        · exact (hbound r hr).trans (le_max_left _ _)
      · rw [hx'ne _ (by omega)]
        rcases hlast with h | ⟨r, hr, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, h⟩
      · intro i hi1 hin t ht
        rw [hx'ne _ (by omega)] at ht
        by_cases hi : i = n
        · subst hi
          rw [hx'n] at ht
          by_cases htm : t ≤ x (2 * i)
          · rcases hunion i hi1 le_rfl t ⟨ht.1, htm⟩ with h | ⟨r, hr, hrt⟩
            · exact Or.inl h
            · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hrt⟩
          · push_neg at htm
            refine Or.inr ⟨a, Finset.mem_insert_self a s, hc.trans htm.le, ?_⟩
            rcases le_max_iff.1 ht.2 with h | h
            · exact absurd h (not_le.2 htm)
            · exact h
        · rw [hx'ne _ (by omega)] at ht
          rcases hunion i hi1 hin t ht with h | ⟨r, hr, hrt⟩
          · exact Or.inl h
          · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hrt⟩
      · intro i hi1 hin r hr
        rw [hx'ne _ (by omega), hx'ne _ (by omega)]
        rcases Finset.mem_insert.1 hr with rfl | hr
        · exact Or.inr ((hxle _ _ (by omega) (by omega) (by omega)).trans hlast')
        · exact hgap i hi1 hin r hr

/-- **C′, the blocks** (commission 178 §6), combinatorial form for a finite set of intervals with
some member ending at `1`: `n ≥ 2`, `x₂ₙ = 1`. -/
theorem blocks_of_finite {e : unitInterval} (he : 0 < e) {Is : Set (unitInterval × unitInterval)}
    (hfin : Is.Finite) (hnd : ∀ r ∈ Is, r.1 < r.2) (hle : ∀ r ∈ Is, e < r.1)
    (hone : ∃ r ∈ Is, r.2 = 1) :
    ∃ n, 2 ≤ n ∧ ∃ x : ℕ → unitInterval, StrictMonoOn x (Icc 1 (2 * n)) ∧ x 1 = 0 ∧ x 2 = e ∧
      x (2 * n) = 1 ∧
      (∀ r ∈ Is, ∃ i, 1 ≤ i ∧ i ≤ n ∧ x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
        t ≤ e ∨ ∃ r ∈ Is, t ∈ Icc r.1 r.2) ∧
      (∀ i, 1 ≤ i → i < n → ∀ r ∈ Is, r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) := by
  obtain ⟨n, hn, x, hmono, hx1, hx2, hmem, hbound, -, hunion, hgap⟩ :=
    blocks_of_finset he hfin.toFinset (fun r hr => hnd r (hfin.mem_toFinset.1 hr))
      (fun r hr => hle r (hfin.mem_toFinset.1 hr))
  obtain ⟨r₀, hr₀, hr₀1⟩ := hone
  have hxn : x (2 * n) = 1 :=
    le_antisymm unitInterval.le_one' (hr₀1 ▸ hbound r₀ (hfin.mem_toFinset.2 hr₀))
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    subst this
    rw [hx2] at hxn
    have := (hle r₀ hr₀).trans (hnd r₀ hr₀)
    rw [hr₀1, ← hxn] at this
    exact lt_irrefl _ this
  refine ⟨n, hn2, x, hmono, hx1, hx2, hxn, fun r hr => hmem r (hfin.mem_toFinset.2 hr), ?_, ?_⟩
  · intro i hi hin t ht
    rcases hunion i hi hin t ht with h | ⟨r, hr, hrt⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hfin.mem_toFinset.1 hr, hrt⟩
  · intro i hi hin r hr
    exact hgap i hi hin r (hfin.mem_toFinset.2 hr)

section Hag

variable {M : Set Pt}

/-- **C′, the blocks of `St J`** (commission 178 §6) for Hagopian's `I`: given `e` with
`d⁻¹[[0, e]] = E` and `e` below every member of `I` (`hagopian76_J_xs`), `I` finite
(`hagopian76_I_finite`), some member ending at `1` (`x₂ₙ = 1`, `LastIntervalReachesOne`), and the
members nondegenerate, the block data required by `hagopian76_T15_T17_cond2` exist, with each block
a union of members of `J = I ∪ {[0, e]}` and no member of `J` meeting a gap. -/
theorem exists_blocks_aux {G : Set M} {d : G → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {E : Set M} {e : unitInterval} (he0 : 0 < e)
    (hE : layerSet d (Icc 0 e) = E) (he : ∀ p ∈ crossingIntervals d π F c₁ D', e < p.1)
    (hfin : (crossingIntervals d π F c₁ D').Finite)
    (hnd : ∀ p ∈ crossingIntervals d π F c₁ D', p.1 < p.2)
    (hlast : LastIntervalReachesOne d π F c₁ D') :
    ∃ (x : ℕ → unitInterval) (n : ℕ), 2 ≤ n ∧ StrictMonoOn x (Icc 1 (2 * n)) ∧ x 1 = 0 ∧
      layerSet d (Icc 0 (x 2)) = E ∧
      (∀ r ∈ crossingIntervals d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
        x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
      x (2 * n) = 1 ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
        t ≤ e ∨ ∃ r ∈ crossingIntervals d π F c₁ D', t ∈ Icc r.1 r.2) ∧
      (∀ i, 1 ≤ i → i < n → ∀ r ∈ crossingIntervals d π F c₁ D',
        r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) := by
  obtain ⟨n, hn, x, hmono, hx1, hx2, hxn, hmem, hunion, hgap⟩ :=
    blocks_of_finite he0 hfin hnd he hlast
  exact ⟨x, n, hn, hmono, hx1, by rw [hx2]; exact hE, hmem, hxn, hunion, hgap⟩

end Hag

end HPC.Hagopian
