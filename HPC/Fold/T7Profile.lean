import HPC.Fold.Lift82Main

/-!
# From chains to profiles, and the remaining lift manipulations

Batch 82. The profile of a fine chain `E` crooked in a coarse chain `D`; time reversal of profiles
and lifts; moving a position to the end of the pattern in the middle of a lift.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- The levels of the coarse links containing fine link `t`. -/
def chainK {n m : ℕ} (E : Chain X n) (D : Chain X m) (t : ℕ) : Set ℤ :=
  {j | ∃ (ht : t < n) (i : Fin m), (i : ℤ) = j ∧ E.link ⟨t, ht⟩ ⊆ D.link i}

/-- The levels of the coarse links met by fine link `t`. -/
def chainM {n m : ℕ} (E : Chain X n) (D : Chain X m) (t : ℕ) : Set ℤ :=
  {j | ∃ (ht : t < n) (i : Fin m), (i : ℤ) = j ∧ (E.link ⟨t, ht⟩ ∩ D.link i).Nonempty}

theorem chainM_bound {n m : ℕ} {E : Chain X n} {D : Chain X m} {t : ℕ} {h : ℤ}
    (hh : h ∈ chainM E D t) : 0 ≤ h ∧ h ≤ ((m - 1 : ℕ) : ℤ) := by
  obtain ⟨_, i, rfl, -⟩ := hh
  have := i.isLt
  constructor <;> omega

theorem isProfile_chain {n m : ℕ} {E : Chain X n} {D : Chain X m} (hcr : E.IsCrookedIn' D) :
    IsProfile n (chainK E D) (chainM E D) where
  ne t ht := by
    obtain ⟨i, hi⟩ := hcr.1 ⟨t, ht⟩
    exact ⟨i, ht, i, rfl, hi⟩
  sub t ht := by
    rintro _ ⟨ht', i, rfl, hsub⟩
    obtain ⟨x, hx⟩ := E.link_nonempty ⟨t, ht'⟩
    exact ⟨ht', i, rfl, x, hx, hsub hx⟩
  near t ht := by
    rintro _ ⟨ht1, i, rfl, hsub⟩ _ ⟨ht2, i', rfl, x, hx1, hx2⟩
    have := (D.adjacent_iff i i').1 ⟨x, hsub hx1, hx2⟩
    omega
  adj t ht := by
    rintro _ ⟨ht1, i, rfl, hsub⟩ _ ⟨ht2, i', rfl, hsub'⟩
    obtain ⟨x, hx1, hx2⟩ := (E.adjacent_iff ⟨t, ht1⟩ ⟨t + 1, ht2⟩).2 (show t ≤ t + 1 + 1 ∧ t + 1 ≤ t + 1 by omega)
    have := (D.adjacent_iff i i').1 ⟨x, hsub hx1, hsub' hx2⟩
    omega
  adjM t ht := by
    constructor
    · rintro _ ⟨ht2, i', rfl, hsub'⟩
      obtain ⟨x, hx1, hx2⟩ := (E.adjacent_iff ⟨t, by omega⟩ ⟨t + 1, ht2⟩).2 (show t ≤ t + 1 + 1 ∧ t + 1 ≤ t + 1 by omega)
      exact ⟨by omega, i', rfl, x, hx1, hsub' hx2⟩
    · rintro _ ⟨ht1, i, rfl, hsub⟩
      obtain ⟨x, hx1, hx2⟩ := (E.adjacent_iff ⟨t, ht1⟩ ⟨t + 1, ht⟩).2 (show t ≤ t + 1 + 1 ∧ t + 1 ≤ t + 1 by omega)
      exact ⟨ht, i, rfl, x, hx2, hsub hx1⟩
  crook i hi j hj h k := by
    rintro ⟨hi', a, rfl, hia⟩ ⟨hj', b, rfl, hjb⟩ hab
    obtain ⟨r, s, hbet, hr, hs⟩ := hcr.2 a b (by omega) ⟨i, hi'⟩ ⟨j, hj'⟩ hia hjb
    refine ⟨r, s, ?_, ⟨r.isLt, ⟨b.val - 1, by omega⟩, by simp; omega, hr⟩,
      ⟨s.isLt, ⟨a.val + 1, by omega⟩, by simp, hs⟩⟩
    unfold Between at hbet; unfold NBetween
    simp only [Fin.lt_def] at hbet
    omega

/-! ## Time reversal -/

theorem IsProfile.rev {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) :
    IsProfile n (fun t => K (n - 1 - t)) (fun t => M (n - 1 - t)) where
  ne t ht := hP.ne _ (by omega)
  sub t ht := hP.sub _ (by omega)
  near t ht := hP.near _ (by omega)
  adj t ht a ha b hb := by
    have := hP.adj (n - 1 - (t + 1)) (by omega) b hb a
      (by rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega]; exact ha)
    exact ⟨this.2, this.1⟩
  adjM t ht := by
    have := hP.adjM (n - 1 - (t + 1)) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩
  crook i hi j hj h k hh hk hhk := by
    obtain ⟨r, s, hb, hr, hs⟩ := hP.crook (n - 1 - i) (by omega) (n - 1 - j) (by omega) h k hh hk
      hhk
    have hb' := hb
    unfold NBetween at hb'
    refine ⟨n - 1 - r, n - 1 - s, by unfold NBetween; omega, ?_, ?_⟩
    · show k - 1 ∈ K (n - 1 - (n - 1 - r)); rw [show n - 1 - (n - 1 - r) = r by omega]; exact hr
    · show h + 1 ∈ K (n - 1 - (n - 1 - s)); rw [show n - 1 - (n - 1 - s) = s by omega]; exact hs

theorem compat_comp {K M : ℕ → Set ℤ} {f : ℕ → ℕ} {g : ℕ → ℤ} {L t u : ℕ} :
    Compat (fun t => K (f t)) (fun t => M (f t)) g L t u ↔ Compat K M g L (f t) u := Iff.rfl

theorem IsLift.timeRev {n : ℕ} {K M : ℕ → Set ℤ} {g : ℕ → ℤ} {L s0 s1 : ℕ} {β : ℕ → ℕ}
    (hl : IsLift (fun t => K (n - 1 - t)) (fun t => M (n - 1 - t)) g L s0 s1 β) (hs1 : s1 < n)
    (h01 : s0 ≤ s1) :
    IsLift K M g L (n - 1 - s1) (n - 1 - s0) (fun t => β (n - 1 - t)) := by
  refine ⟨fun t ht0 ht1 => ?_, fun t ht0 ht1 => ?_⟩
  · have := compat_comp.1 (hl.1 (n - 1 - t) (by omega) (by omega))
    rwa [show n - 1 - (n - 1 - t) = t by omega] at this
  · have := hl.2 (n - 1 - (t + 1)) (by omega) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩

/-- Moving a position to the end of the pattern at a time where the link lies in the top level. -/
theorem IsLift.adjust_top {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) {a : ℤ}
    {d t0 t1 : ℕ} {β : ℕ → ℕ} (hl : IsLift K M (fun u => a + bingF d u) (z d) t0 t1 β)
    {ts : ℕ} (hts0 : t0 ≤ ts) (hts1 : ts ≤ t1) (hK : a + d ∈ K ts)
    (hband : ∀ h ∈ M ts, h ≤ a + d) (ht1 : t1 < n) :
    IsLift K M (fun u => a + bingF d u) (z d) t0 t1
      (fun t => if t = ts then z d - 1 else β t) := by
  have hzp := z_pos d
  have hhigh : z d - 2 ≤ β ts := compat_high (hl.1 ts hts0 hts1) (hP.sub ts (by omega) hK)
  -- a neighbour of `ts` is not at position `z d - 3`
  have hnb : ∀ t, t0 ≤ t → t ≤ t1 → (t + 1 = ts ∨ t = ts + 1) → z d - 2 ≤ β t := by
    intro t ht0 ht1' hts
    have hlt := (hl.1 t ht0 ht1').1
    have hlip : β t + 1 ≥ β ts := by
      rcases hts with e | e
      · have := hl.2 t ht0 (by omega); rw [e] at this; omega
      · have := hl.2 ts hts0 (by omega); rw [← e] at this; omega
    by_contra hc
    have he : β t = z d - 3 := by omega
    have hc1 := hl.1 t ht0 ht1'
    rw [he] at hc1
    obtain ⟨hz, hk2, -⟩ := hc1
    have hd : 2 ≤ d := by
      by_contra hd; push_neg at hd
      interval_cases d <;> simp only [z] at hc hhigh <;> omega
    dsimp only at hk2
    rw [bingF_sub_two d hd] at hk2
    rcases hts with e | e
    · have := hP.adj t (by omega) _ hk2 _ (by rw [e]; exact hK)
      push_cast at this; omega
    · have := hP.adj ts (by omega) _ hK _ (by rw [← e]; exact hk2)
      push_cast at this; omega
  refine ⟨fun t ht0 ht1' => ?_, fun t ht0 ht1' => ?_⟩
  · by_cases ht : t = ts
    · subst ht
      simp only [if_true]
      refine ⟨by omega, by simpa [bingF_top d _ le_rfl] using hK, fun h hh => ?_⟩
      have hn := hP.near t (by omega) (a + d) hK h hh
      have hb := hband h hh
      rcases (show h = a + d ∨ h = a + d - 1 by omega) with e | e
      · left; simp [e, bingF_top d _ le_rfl]
      · right; left
        have hd : 1 ≤ d := by
          by_contra hd; push_neg at hd
          have : d = 0 := by omega
          subst this
          have hmem := hl.1 t ht0 ht1'
          obtain ⟨_, _, hm⟩ := hmem
          rcases hm h hh with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
            simp [bingF] at h1 <;> omega
        refine ⟨by have := z_two_le d hd; omega, ?_⟩
        dsimp only
        rw [show z d - 1 - 1 = z d - 2 by omega, bingF_sub_one d hd, e]; ring
    · simp only [ht, if_false]; exact hl.1 t ht0 ht1'
  · have hlt := (hl.1 t ht0 (by omega)).1
    have hlt' := (hl.1 (t + 1) (by omega) (by omega)).1
    by_cases h1 : t + 1 = ts
    · have := hnb t ht0 (by omega) (Or.inl h1)
      simp only [h1, if_true, show t ≠ ts by omega, if_false]
      constructor <;> omega
    · by_cases h2 : t = ts
      · have := hnb (t + 1) (by omega) (by omega) (Or.inr (by rw [h2]))
        simp only [h2, if_true, show ts + 1 ≠ ts by omega, if_false]
        subst h2
        constructor <;> omega
      · simp only [h1, h2, if_false]; exact hl.2 t ht0 ht1'

end HPC.Fold
