import HPC.Fold.T9Ends
import HPC.Fold.Pair79Chain

/-!
# Theorem 9: the folded chain `H + D(s+1, n)` is crooked

Batch 82. On the fine indices `0, …, s` a block function `γ` follows Bing's pattern and is tight
(it is the overlay of the consolidations `G₁` of `E(0, r)` and `G₂` of `E(r, s)` read backwards);
the index `s` is in block `0` and `E.link s` lies in the first link of `D`. The chain
`H' = H + E(s+1, n)` puts position `p` of the pattern at index `Z − 1 − p` and the fine link `u > s`
at index `Z − 1 + (u − s)`. It is crooked in `D`.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- The block function of `H + E(s+1, n)`. -/
def foldMap (m s : ℕ) (γ : ℕ → ℕ) (u : ℕ) : ℕ :=
  if u ≤ s then z (m - 1) - 1 - γ u else z (m - 1) - 1 + (u - s)

/-- A level of Bing's pattern as a link index. -/
def lvF (m p : ℕ) (hm : 1 ≤ m) : Fin m :=
  ⟨(bingF (m - 1) p).toNat, by have := bingF_le (m - 1) p; have := bingF_nonneg (m - 1) p; omega⟩

theorem lvF_val (m p : ℕ) (hm : 1 ≤ m) : (((lvF m p hm : Fin m) : ℕ) : ℤ) = bingF (m - 1) p := by
  have := bingF_nonneg (m - 1) p
  simp only [lvF]; omega

theorem crooked_foldChain {n m s : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (hs : s < n) (γ : ℕ → ℕ)
    (hγlt : ∀ u, u ≤ s → γ u < z (m - 1))
    (hγ1 : ∀ u (hu : u ≤ s), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (γ u) ∧
      E.link ⟨u, by omega⟩ ⊆ D.link i)
    (hγ2 : ∀ u (hu : u ≤ s) (i : Fin m), (E.link ⟨u, by omega⟩ ∩ D.link i).Nonempty →
      ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ γ u + 1 ∧ γ u ≤ u' + 1 ∧ (i : ℤ) = bingF (m - 1) u')
    (hEs : E.link ⟨s, hs⟩ ⊆ D.link ⟨0, by omega⟩)
    (hlt : ∀ t, t < n → foldMap m s γ t < z (m - 1) + (n - 1 - s))
    (hb : IsBlockMap (natBlock (foldMap m s γ) hlt)) :
    (E.ofBlocks _ hb).IsCrookedIn' D := by
  have hZ3 : 3 ≤ z (m - 1) := z_three_le (m - 1) (by omega)
  have hlink := natBlock_link E (foldMap m s γ) hlt hb
  -- the two parts of the folded chain
  have fA : ∀ (j : Fin (z (m - 1) + (n - 1 - s))) (hj : j.val < z (m - 1)), ∀ x ∈ (E.ofBlocks _ hb).link j,
      ∃ t, ∃ ht : t ≤ s, γ t = z (m - 1) - 1 - j.val ∧ x ∈ E.link ⟨t, by omega⟩ := by
    intro j hj x hx
    rw [hlink] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    unfold foldMap at ht
    split_ifs at ht with h
    · have := hγlt t h
      exact ⟨t, h, by omega, hxt⟩
    · omega
  have fT : ∀ (j : Fin (z (m - 1) + (n - 1 - s))) (hj : z (m - 1) ≤ j.val),
      (E.ofBlocks _ hb).link j = E.link ⟨s + 1 + (j.val - z (m - 1)), by have := j.isLt; omega⟩ := by
    intro j hj
    rw [hlink]
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht, hxt⟩
      unfold foldMap at ht
      split_ifs at ht with h
      · have := hγlt t h; omega
      · rw [show t = (⟨s + 1 + (j.val - z (m - 1)), by have := j.isLt; omega⟩ : Fin n) from
          Fin.ext (by simp only; omega)] at hxt
        exact hxt
    · intro hx
      refine ⟨⟨s + 1 + (j.val - z (m - 1)), by have := j.isLt; omega⟩, ?_, hx⟩
      show foldMap m s γ (s + 1 + (j.val - z (m - 1))) = j.val
      unfold foldMap
      rw [if_neg (by omega)]
      omega
  have fT' : ∀ (u : ℕ) (hu : u < n) (hsu : s < u),
      (E.ofBlocks _ hb).link ⟨z (m - 1) - 1 + (u - s), by omega⟩ = E.link ⟨u, hu⟩ := by
    intro u hu hsu
    rw [fT _ (by simp only; omega)]
    congr 1; apply Fin.ext; simp only; omega
  -- levels and tightness of the pattern part
  have lvA : ∀ (j : Fin (z (m - 1) + (n - 1 - s))) (hj : j.val < z (m - 1)),
      (E.ofBlocks _ hb).link j ⊆ D.link (lvF m (z (m - 1) - 1 - j.val) (by omega)) := by
    intro j hj x hx
    obtain ⟨t, ht, hγt, hxt⟩ := fA j hj x hx
    obtain ⟨i, hi, hsub⟩ := hγ1 t ht
    have : i = lvF m (z (m - 1) - 1 - j.val) (by omega) := Fin.ext (by
      rw [← hγt]; have := lvF_val m (γ t) (by omega); omega)
    rw [← this]; exact hsub hxt
  have tA : ∀ (j : Fin (z (m - 1) + (n - 1 - s))) (hj : j.val < z (m - 1)) (l : Fin m),
      ((E.ofBlocks _ hb).link j ∩ D.link l).Nonempty →
      ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ (z (m - 1) - 1 - j.val) + 1 ∧ (z (m - 1) - 1 - j.val) ≤ u' + 1 ∧
        (l : ℤ) = bingF (m - 1) u' := by
    intro j hj l ⟨x, hx1, hx2⟩
    obtain ⟨t, ht, hγt, hxt⟩ := fA j hj x hx1
    rw [← hγt]
    exact hγ2 t ht l ⟨x, hxt, hx2⟩
  have lvEq : ∀ (p : ℕ) (l : Fin m), bingF (m - 1) p = (l : ℤ) → lvF m p (by omega) = l :=
    fun p l h => Fin.ext (by have := lvF_val m p (by omega); omega)
  -- the fine levels
  obtain ⟨-, -, hnn, -, hlipρ, -⟩ := B79.seq_facts hcr
  let ρn : ℕ → ℕ := fun t => if h : t < n then (hcr.1.minIdx ⟨t, h⟩).val else 0
  have hρn : ∀ t (h : t < n), ρn t = (hcr.1.minIdx ⟨t, h⟩).val := fun t h => by simp [ρn, h]
  refine ⟨fun j => ?_, ?_⟩
  · -- refinement
    by_cases hj : j.val < z (m - 1)
    · exact ⟨_, lvA j hj⟩
    · rw [fT j (by omega)]; exact hcr.1 _
  intro h k hk i j hi hj
  have hhk : (h : ℤ) + 3 ≤ k := by omega
  by_cases hiA : i.val < z (m - 1) <;> by_cases hjA : j.val < z (m - 1)
  · -- both in the pattern part
    obtain ⟨r0, s0, hb', hr0, hs0, hr, hs⟩ := pat_pair (m - 1) (z (m - 1) - 1 - i.val) (z (m - 1) - 1 - j.val) h k
      (by obtain ⟨u', a, b, c, d⟩ := tA i hiA h hi; exact ⟨u', a, b, c, d.symm⟩)
      (by obtain ⟨u', a, b, c, d⟩ := tA j hjA k hj; exact ⟨u', a, b, c, d.symm⟩) hhk
    refine ⟨⟨z (m - 1) - 1 - r0, by omega⟩, ⟨z (m - 1) - 1 - s0, by omega⟩, ?_, ?_, ?_⟩
    · unfold NBetween at hb'
      unfold Between
      simp only [Fin.lt_def, gt_iff_lt]
      omega
    · refine (lvA _ (by simp only; omega)).trans (le_of_eq (congrArg D.link (lvEq _ _ ?_)))
      simp only
      rw [show z (m - 1) - 1 - (z (m - 1) - 1 - r0) = r0 by omega]
      omega
    · refine (lvA _ (by simp only; omega)).trans (le_of_eq (congrArg D.link (lvEq _ _ ?_)))
      simp only
      rw [show z (m - 1) - 1 - (z (m - 1) - 1 - s0) = s0 by omega]
      omega
  · -- the low link in the pattern part, the high one in the tail
    have hjl := j.isLt
    set w := s + 1 + (j.val - z (m - 1)) with hw
    have hwn : w < n := by omega
    rw [fT j (by omega)] at hj
    have hρs : ρn s = 0 := by
      rw [hρn s hs]
      have := minIdx_le hcr.1 ⟨s, hs⟩ hEs
      rw [Fin.le_def] at this; simp only at this; omega
    have hρw : (k : ℤ) - 1 ≤ ρn w := by
      rw [hρn w hwn]
      have := minIdx_near_of_inter hcr.1 ⟨w, hwn⟩ k hj
      omega
    obtain ⟨u1, hu1, hu1', hρu1⟩ := nat_ivt ρn s (w - s) (fun t h1 h2 => by
      have := hlipρ ⟨t, by omega⟩ ⟨t + 1, by omega⟩ rfl
      simp only at this
      rw [hρn t (by omega), hρn (t + 1) (by omega)]
      rw [abs_le] at this; omega) h (by
        rw [show s + (w - s) = w by omega]; left; constructor <;> omega)
    rw [show s + (w - s) = w by omega] at hu1'
    have hu1w : u1 < w := by
      rcases eq_or_lt_of_le hu1' with e | e
      · rw [e] at hρu1; omega
      · exact e
    have hmeet : (E.link ⟨u1, by omega⟩ ∩ D.link h).Nonempty := by
      obtain ⟨x, hx⟩ := E.link_nonempty ⟨u1, by omega⟩
      refine ⟨x, hx, ?_⟩
      have := minIdx_subset hcr.1 ⟨u1, by omega⟩ hx
      rw [show hcr.1.minIdx ⟨u1, by omega⟩ = h from Fin.ext (by rw [← hρn u1 (by omega)]; exact hρu1)]
        at this
      exact this
    obtain ⟨r0, s0, hbt, hr, hs'⟩ := hcr.2 h k hk ⟨u1, by omega⟩ ⟨w, hwn⟩ hmeet hj
    unfold Between at hbt
    simp only [Fin.lt_def, gt_iff_lt] at hbt
    have hbt' : u1 < r0.val ∧ r0.val < s0.val ∧ s0.val < w := by omega
    refine ⟨⟨z (m - 1) - 1 + (r0.val - s), by omega⟩, ⟨z (m - 1) - 1 + (s0.val - s), by omega⟩, ?_, ?_, ?_⟩
    · unfold Between
      simp only [Fin.lt_def, gt_iff_lt]
      omega
    · rw [fT' r0.val r0.isLt (by omega)]; exact hr
    · rw [fT' s0.val s0.isLt (by omega)]; exact hs'
  · -- the low link in the tail, the high one in the pattern part
    obtain ⟨q', hq', hq1, hq2, hqk⟩ := tA j hjA k hj
    obtain ⟨r0, s0, hb', hr, hs'⟩ := bingF_crooked (m - 1) 0 q' le_rfl (Nat.zero_le _)
      (Nat.zero_le _) (by omega) h k (by rw [bingF_zero]; exact_mod_cast Nat.zero_le _)
      (by rw [hqk]) hhk
    unfold NBetween at hb'
    have hb'' : 0 < r0 ∧ r0 < s0 ∧ s0 < q' := by omega
    -- `s0` is not `j`'s own position
    have hsj : s0 ≠ z (m - 1) - 1 - j.val := by
      intro e
      obtain ⟨x, hx1, hx2⟩ := hj
      have := (D.adjacent_iff _ _).1 ⟨x, lvA j hjA hx1, hx2⟩
      have h2 := lvF_val m (z (m - 1) - 1 - j.val) (by omega)
      have h3 : bingF (m - 1) (z (m - 1) - 1 - j.val) = h + 1 := by rw [← e]; exact hs'
      omega
    refine ⟨⟨z (m - 1) - 1 - r0, by omega⟩, ⟨z (m - 1) - 1 - s0, by omega⟩, ?_, ?_, ?_⟩
    · unfold Between
      simp only [Fin.lt_def, gt_iff_lt]
      omega
    · refine (lvA _ (by simp only; omega)).trans (le_of_eq (congrArg D.link (lvEq _ _ ?_)))
      simp only
      rw [show z (m - 1) - 1 - (z (m - 1) - 1 - r0) = r0 by omega]
      omega
    · refine (lvA _ (by simp only; omega)).trans (le_of_eq (congrArg D.link (lvEq _ _ ?_)))
      simp only
      rw [show z (m - 1) - 1 - (z (m - 1) - 1 - s0) = s0 by omega]
      omega
  · -- both in the tail
    have hil := i.isLt
    have hjl := j.isLt
    rw [fT i (by omega)] at hi
    rw [fT j (by omega)] at hj
    obtain ⟨r0, s0, hbt, hr, hs'⟩ := hcr.2 h k hk _ _ hi hj
    unfold Between at hbt
    simp only [Fin.lt_def, gt_iff_lt] at hbt
    refine ⟨⟨z (m - 1) - 1 + (r0.val - s), by omega⟩, ⟨z (m - 1) - 1 + (s0.val - s), by omega⟩, ?_, ?_, ?_⟩
    · unfold Between
      simp only [Fin.lt_def, gt_iff_lt]
      omega
    · rw [fT' r0.val r0.isLt (by omega)]; exact hr
    · rw [fT' s0.val s0.isLt (by omega)]; exact hs'

end HPC.Fold
