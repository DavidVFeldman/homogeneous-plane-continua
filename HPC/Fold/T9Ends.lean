import HPC.Fold.T8Tight

/-!
# Theorem 9: tools

Batch 82. Block maps given by functions on `ℕ`; a discrete intermediate value theorem for them;
the block map of Theorem 7 with its end links in the end blocks (`exists_nat_blocks_ends`); and the
crooked-pair step of Bing's pattern with tolerance one (`pat_pair`).
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- A discrete intermediate value theorem for functions `ℕ → ℕ`. -/
theorem nat_ivt (b : ℕ → ℕ) (a : ℕ) : ∀ len : ℕ,
    (∀ t, a ≤ t → t < a + len → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1) →
    ∀ j, (b a ≤ j ∧ j ≤ b (a + len)) ∨ (b (a + len) ≤ j ∧ j ≤ b a) →
      ∃ t, a ≤ t ∧ t ≤ a + len ∧ b t = j
  | 0, _, j, h => ⟨a, le_rfl, le_rfl, by simp at h; omega⟩
  | len + 1, hl, j, h => by
      by_cases hv : b a = j
      · exact ⟨a, le_rfl, by omega, hv⟩
      · have h1 := hl a le_rfl (by omega)
        obtain ⟨t, ht1, ht2, ht3⟩ := nat_ivt b (a + 1) len
          (fun t h1 h2 => hl t (by omega) (by omega)) j (by
            rw [show a + 1 + len = a + (len + 1) by ring]; omega)
        exact ⟨t, by omega, by omega, ht3⟩

/-- The block map on `Fin n` given by a function on `ℕ`. -/
def natBlock {n q : ℕ} (b : ℕ → ℕ) (hlt : ∀ t, t < n → b t < q) : Fin n → Fin q :=
  fun t => ⟨b t, hlt t t.isLt⟩

theorem isBlockMap_natBlock {n q : ℕ} (b : ℕ → ℕ) (hlt : ∀ t, t < n → b t < q)
    (hlip : ∀ t, t + 1 < n → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1)
    (hsurj : ∀ j, j < q → ∃ t, t < n ∧ b t = j) : IsBlockMap (natBlock b hlt) := by
  refine ⟨fun j => ?_, fun t t' h => ?_⟩
  · obtain ⟨t, ht, hb⟩ := hsurj j j.isLt
    exact ⟨⟨t, ht⟩, Fin.ext hb⟩
  · have := hlip t.val (by omega)
    simp only [natBlock, h]
    omega

theorem natBlock_link {n q : ℕ} (E : Chain X n) (b : ℕ → ℕ) (hlt : ∀ t, t < n → b t < q)
    (hb : IsBlockMap (natBlock b hlt)) (j : Fin q) :
    (E.ofBlocks _ hb).link j = ⋃ t ∈ {t : Fin n | b t = j}, E.link t := by
  rw [ofBlocks_link]
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, natBlock, Fin.ext_iff]

/-- Level `0` of Bing's pattern within one step of a position forces the position to be `≤ 1`. -/
theorem le_one_of_bingF_zero {d b u' : ℕ} (hu' : u' < z d) (h1 : b ≤ u' + 1)
    (h : (0 : ℤ) = bingF d u') : b ≤ 1 := by
  have := bingF_eq_zero d u' hu' h.symm
  omega

/-- The block map of Theorem 7 for a chain whose first link lies in the first link of `D` and
whose last link lies in the last: the first block holds the first link and the last block the
last one. -/
theorem exists_nat_blocks_ends {n m : ℕ} (hm : 3 ≤ m) {E : Chain X n} {D : Chain X m}
    (hcr : E.IsCrookedIn' D) (hn : 0 < n) (h0 : E.link ⟨0, hn⟩ ⊆ D.link ⟨0, by omega⟩)
    (hl : E.link ⟨n - 1, by omega⟩ ⊆ D.link ⟨m - 1, by omega⟩) :
    ∃ b : ℕ → ℕ, (∀ t, t < n → b t < z (m - 1)) ∧
      (∀ t, t + 1 < n → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1) ∧
      b 0 = 0 ∧ b (n - 1) = z (m - 1) - 1 ∧
      (∀ t (ht : t < n), ∃ i : Fin m, (i : ℤ) = bingF (m - 1) (b t) ∧ E.link ⟨t, ht⟩ ⊆ D.link i) ∧
      (∀ t (ht : t < n) (i : Fin m), (E.link ⟨t, ht⟩ ∩ D.link i).Nonempty →
        ∃ u' : ℕ, u' < z (m - 1) ∧ u' ≤ b t + 1 ∧ b t ≤ u' + 1 ∧
          (i : ℤ) = bingF (m - 1) u') := by
  obtain ⟨β, hβ, h1, h2⟩ := exists_blocks_bingF hm hcr ⟨⟨0, hn⟩, h0⟩ ⟨⟨n - 1, by omega⟩, hl⟩
  have hZ3 : 3 ≤ z (m - 1) := z_three_le (m - 1) (by omega)
  let bb : ℕ → ℕ := fun t => if h : t < n then (β ⟨t, h⟩).val else 0
  have hbb : ∀ t (h : t < n), bb t = (β ⟨t, h⟩).val := fun t h => by simp [bb, h]
  -- meeting the first link forces the block to be `≤ 1`
  have lo : ∀ t (h : t < n), (E.link ⟨t, h⟩ ∩ D.link ⟨0, by omega⟩).Nonempty → bb t ≤ 1 := by
    intro t h hne
    obtain ⟨u', hu', hu1, hu2, hu3⟩ := h2 ⟨t, h⟩ ⟨0, by omega⟩ hne
    rw [hbb t h]
    exact le_one_of_bingF_zero hu' hu2 (by simpa using hu3)
  have hi : ∀ t (h : t < n), (E.link ⟨t, h⟩ ∩ D.link ⟨m - 1, by omega⟩).Nonempty →
      z (m - 1) - 2 ≤ bb t := by
    intro t h hne
    obtain ⟨u', hu', hu1, hu2, hu3⟩ := h2 ⟨t, h⟩ ⟨m - 1, by omega⟩ hne
    have := bingF_eq_top (m - 1) u' (by rw [← hu3])
    rw [hbb t h]
    omega
  have hbblt : ∀ t, t < n → bb t < z (m - 1) := fun t h => by rw [hbb t h]; exact (β _).isLt
  have hDsep : ¬ (D.link ⟨0, by omega⟩ ∩ D.link ⟨m - 1, by omega⟩).Nonempty := by
    intro h
    have := (D.adjacent_iff _ _).1 h
    simp only at this
    omega
  have hn2 : 2 ≤ n := by
    by_contra hc
    obtain ⟨x, hx⟩ := E.link_nonempty ⟨0, hn⟩
    apply hDsep
    refine ⟨x, h0 hx, hl ?_⟩
    rw [show (⟨n - 1, _⟩ : Fin n) = ⟨0, hn⟩ from Fin.ext (by simp only; omega)]
    exact hx
  -- neighbours of the end links
  have hE01 : (E.link ⟨1, by omega⟩ ∩ D.link ⟨0, by omega⟩).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := (E.adjacent_iff ⟨1, by omega⟩ ⟨0, hn⟩).2 (by simp)
    exact ⟨x, hx1, h0 hx2⟩
  have hEl : (E.link ⟨n - 2, by omega⟩ ∩ D.link ⟨m - 1, by omega⟩).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := (E.adjacent_iff ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩).2
      (by simp only; omega)
    exact ⟨x, hx1, hl hx2⟩
  have hn3 : 3 ≤ n := by
    by_contra hc
    have e : (⟨n - 2, by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
    rw [e] at hEl
    obtain ⟨x, hx1, hx2⟩ := hEl
    exact hDsep ⟨x, h0 hx1, hx2⟩
  let b : ℕ → ℕ := fun t => if t = 0 then 0 else if t = n - 1 then z (m - 1) - 1 else bb t
  have hb0 : b 0 = 0 := by simp [b]
  have hbl : b (n - 1) = z (m - 1) - 1 := by simp [b, show n - 1 ≠ 0 by omega]
  have hbm : ∀ t, t ≠ 0 → t ≠ n - 1 → b t = bb t := fun t h h' => by simp [b, h, h']
  have hlo1 := lo 1 (by omega) hE01
  have hhi1 := hi (n - 2) (by omega) hEl
  refine ⟨b, fun t ht => ?_, fun t ht => ?_, hb0, hbl, fun t ht => ?_, fun t ht i hne => ?_⟩
  · by_cases e0 : t = 0
    · subst e0; rw [hb0]; omega
    by_cases el : t = n - 1
    · subst el; rw [hbl]; omega
    rw [hbm t e0 el]; exact hbblt t ht
  · by_cases e0 : t = 0
    · subst e0
      rw [hb0, hbm 1 (by omega) (by omega)]
      omega
    by_cases el : t + 1 = n - 1
    · rw [el, hbl, hbm t e0 (by omega), show t = n - 2 by omega]
      have := hbblt (n - 2) (by omega)
      omega
    rw [hbm t e0 (by omega), hbm (t + 1) (by omega) el, hbb t (by omega), hbb (t + 1) ht]
    have := hβ.lip ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl
    omega
  · by_cases e0 : t = 0
    · subst e0
      refine ⟨⟨0, by omega⟩, by rw [hb0, bingF_zero]; rfl, h0⟩
    by_cases el : t = n - 1
    · subst el
      refine ⟨⟨m - 1, by omega⟩, ?_, hl⟩
      rw [hbl, bingF_top _ _ le_rfl]
    rw [hbm t e0 el]
    obtain ⟨i, hi', hs⟩ := h1 ⟨t, ht⟩
    exact ⟨i, by rw [hbb t ht]; exact hi', hs⟩
  · by_cases e0 : t = 0
    · subst e0
      have hi1 : (i : ℕ) ≤ 1 := by
        obtain ⟨x, hx1, hx2⟩ := hne
        have := (D.adjacent_iff ⟨0, by omega⟩ i).1 ⟨x, h0 hx1, hx2⟩
        simp only at this; omega
      rw [hb0]
      rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with e | e
      · exact ⟨0, by omega, by omega, by omega, by rw [bingF_zero]; exact_mod_cast e⟩
      · exact ⟨1, by omega, by omega, by omega, by rw [bingF_one _ (by omega)]; exact_mod_cast e⟩
    by_cases el : t = n - 1
    · subst el
      have hi1 : m - 2 ≤ (i : ℕ) := by
        obtain ⟨x, hx1, hx2⟩ := hne
        have := (D.adjacent_iff ⟨m - 1, by omega⟩ i).1 ⟨x, hl hx1, hx2⟩
        simp only at this; omega
      have hil := i.isLt
      rw [hbl]
      rcases (show (i : ℕ) = m - 1 ∨ (i : ℕ) = m - 2 by omega) with e | e
      · refine ⟨z (m - 1) - 1, by omega, by omega, by omega, ?_⟩
        rw [bingF_top _ _ le_rfl]; push_cast [e]; omega
      · refine ⟨z (m - 1) - 1 - 1, by omega, by omega, by omega, ?_⟩
        rw [bingF_rev (m - 1) 1 (by omega), bingF_one _ (by omega)]
        push_cast [e]; omega
    rw [hbm t e0 el, hbb t ht]
    exact h2 ⟨t, ht⟩ i hne

/-- **The crooked-pair step of Bing's pattern, with tolerance one.** If positions `p`, `q` have
neighbours at levels `h` and `k ≥ h + 3`, there are positions `r`, `s` strictly between `p` and
`q`, `r` nearer `p`, at levels `k − 1` and `h + 1`. -/
theorem pat_pair (d p q : ℕ) (h k : ℤ)
    (hh : ∃ p', p' < z d ∧ p' ≤ p + 1 ∧ p ≤ p' + 1 ∧ bingF d p' = h)
    (hk : ∃ q', q' < z d ∧ q' ≤ q + 1 ∧ q ≤ q' + 1 ∧ bingF d q' = k) (hhk : h + 3 ≤ k) :
    ∃ r s, NBetween p r s q ∧ r < z d ∧ s < z d ∧ bingF d r = k - 1 ∧ bingF d s = h + 1 := by
  obtain ⟨u', hu1, hu2, hu3, hu4⟩ := hh
  obtain ⟨v', hv1, hv2, hv3, hv4⟩ := hk
  obtain ⟨r, s, hb, hr, hs⟩ := bingF_crooked d u' v' (Nat.zero_le _) (by omega)
    (Nat.zero_le _) (by omega) h k (by rw [hu4]) (by rw [hv4]) hhk
  have hlip := bingF_lip d
  have near : ∀ (a b : ℕ), a ≤ b + 1 → b ≤ a + 1 → |bingF d a - bingF d b| ≤ 1 := by
    intro a b hab hba
    rcases (show a = b ∨ a = b + 1 ∨ b = a + 1 by omega) with e | e | e
    · subst e; simp
    · subst e; exact hlip b
    · subst e; rw [abs_sub_comm]; exact hlip a
  have ni := near u' p hu2 hu3
  have nj := near v' q hv2 hv3
  rw [abs_le] at ni nj
  have hbr : r < z d := by unfold NBetween at hb; omega
  have hbs : s < z d := by unfold NBetween at hb; omega
  have hri : r ≠ p := fun e => by rw [e] at hr; omega
  have hsj : s ≠ q := fun e => by rw [e] at hs; omega
  refine ⟨r, s, ?_, hbr, hbs, hr, hs⟩
  unfold NBetween at hb ⊢
  omega

end HPC.Fold
