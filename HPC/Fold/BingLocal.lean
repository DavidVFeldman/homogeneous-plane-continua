import HPC.Fold.BingCrook

/-!
# Local shape of Bing's pattern

Batch 82. Bing's pattern `bingF d` never stays at a level, and at each interior local minimum
(valley) at level `v` it reaches `v + 2` two steps away on one side; at each interior local
maximum (peak) at level `v` it reaches `v − 2` two steps away on one side. These are the facts
behind the tightness of a crooked chain following the pattern (Theorem 8).
-/

namespace HPC.Fold

/-- A valley at `u` is followed or preceded, two steps away and inside `[lo, hi]`, by `v + 2`. -/
def ValleyOK (g : ℕ → ℤ) (lo hi u : ℕ) : Prop :=
  g (u - 1) = g u + 1 → g (u + 1) = g u + 1 →
    (lo + 2 ≤ u ∧ g (u - 2) = g u + 2) ∨ (u + 2 ≤ hi ∧ g (u + 2) = g u + 2)

/-- A peak at `u` is followed or preceded, two steps away and inside `[lo, hi]`, by `v − 2`. -/
def PeakOK (g : ℕ → ℤ) (lo hi u : ℕ) : Prop :=
  g (u - 1) = g u - 1 → g (u + 1) = g u - 1 →
    (lo + 2 ≤ u ∧ g (u - 2) = g u - 2) ∨ (u + 2 ≤ hi ∧ g (u + 2) = g u - 2)

/-- No flat steps, and every interior valley and peak is good, on the window `[lo, hi]`. -/
def PatLocal (g : ℕ → ℤ) (lo hi : ℕ) : Prop :=
  (∀ u, lo ≤ u → u < hi → g (u + 1) ≠ g u) ∧
  ∀ u, lo < u → u < hi → ValleyOK g lo hi u ∧ PeakOK g lo hi u

theorem ValleyOK.mono {g : ℕ → ℤ} {lo hi lo' hi' u : ℕ} (h : ValleyOK g lo hi u)
    (hl : lo' ≤ lo) (hh : hi ≤ hi') : ValleyOK g lo' hi' u := by
  intro h1 h2
  rcases h h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨by omega, b⟩
  · exact Or.inr ⟨by omega, b⟩

theorem PeakOK.mono {g : ℕ → ℤ} {lo hi lo' hi' u : ℕ} (h : PeakOK g lo hi u)
    (hl : lo' ≤ lo) (hh : hi ≤ hi') : PeakOK g lo' hi' u := by
  intro h1 h2
  rcases h h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨by omega, b⟩
  · exact Or.inr ⟨by omega, b⟩

theorem PatLocal.congr {g g' : ℕ → ℤ} {lo hi : ℕ} (hc : PatLocal g lo hi)
    (he : ∀ u, lo ≤ u → u ≤ hi → g' u = g u) : PatLocal g' lo hi := by
  refine ⟨fun u h1 h2 => ?_, fun u h1 h2 => ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · rw [he u h1 h2.le, he (u + 1) (by omega) h2]; exact hc.1 u h1 h2
  · rw [he u h1.le h2.le, he (u - 1) (by omega) (by omega)] at a
    rw [he u h1.le h2.le, he (u + 1) (by omega) (by omega)] at b
    rcases (hc.2 u h1 h2).1 a b with ⟨c, e⟩ | ⟨c, e⟩
    · left; refine ⟨c, ?_⟩
      rw [he u h1.le h2.le, he (u - 2) (by omega) (by omega)]; exact e
    · right; refine ⟨c, ?_⟩
      rw [he u h1.le h2.le, he (u + 2) (by omega) (by omega)]; exact e
  · rw [he u h1.le h2.le, he (u - 1) (by omega) (by omega)] at a
    rw [he u h1.le h2.le, he (u + 1) (by omega) (by omega)] at b
    rcases (hc.2 u h1 h2).2 a b with ⟨c, e⟩ | ⟨c, e⟩
    · left; refine ⟨c, ?_⟩
      rw [he u h1.le h2.le, he (u - 2) (by omega) (by omega)]; exact e
    · right; refine ⟨c, ?_⟩
      rw [he u h1.le h2.le, he (u + 2) (by omega) (by omega)]; exact e

theorem PatLocal.shift {g : ℕ → ℤ} {lo hi : ℕ} (hc : PatLocal g lo hi) (o : ℕ) (c : ℤ) :
    PatLocal (fun u => c + g (u - o)) (lo + o) (hi + o) := by
  refine ⟨fun u h1 h2 => ?_, fun u h1 h2 => ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · have := hc.1 (u - o) (by omega) (by omega)
    simp only
    rw [show u + 1 - o = u - o + 1 by omega]; intro h; exact this (by linarith)
  · simp only at a b ⊢
    rw [show u - 1 - o = u - o - 1 by omega] at a
    rw [show u + 1 - o = u - o + 1 by omega] at b
    rcases (hc.2 (u - o) (by omega) (by omega)).1 (by linarith) (by linarith) with
      ⟨c', e⟩ | ⟨c', e⟩
    · left; refine ⟨by omega, ?_⟩
      rw [show u - 2 - o = u - o - 2 by omega]; linarith
    · right; refine ⟨by omega, ?_⟩
      rw [show u + 2 - o = u - o + 2 by omega]; linarith
  · simp only at a b ⊢
    rw [show u - 1 - o = u - o - 1 by omega] at a
    rw [show u + 1 - o = u - o + 1 by omega] at b
    rcases (hc.2 (u - o) (by omega) (by omega)).2 (by linarith) (by linarith) with
      ⟨c', e⟩ | ⟨c', e⟩
    · left; refine ⟨by omega, ?_⟩
      rw [show u - 2 - o = u - o - 2 by omega]; linarith
    · right; refine ⟨by omega, ?_⟩
      rw [show u + 2 - o = u - o + 2 by omega]; linarith

theorem PatLocal.neg {g : ℕ → ℤ} {lo hi : ℕ} (hc : PatLocal g lo hi) (c : ℤ) :
    PatLocal (fun u => c - g u) lo hi := by
  refine ⟨fun u h1 h2 => ?_, fun u h1 h2 => ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · have := hc.1 u h1 h2
    simp only; intro h; exact this (by linarith)
  · simp only at a b ⊢
    rcases (hc.2 u h1 h2).2 (by linarith) (by linarith) with ⟨c', e⟩ | ⟨c', e⟩
    · exact Or.inl ⟨c', by linarith⟩
    · exact Or.inr ⟨c', by linarith⟩
  · simp only at a b ⊢
    rcases (hc.2 u h1 h2).1 (by linarith) (by linarith) with ⟨c', e⟩ | ⟨c', e⟩
    · exact Or.inl ⟨c', by linarith⟩
    · exact Or.inr ⟨c', by linarith⟩

/-- **The local shape of Bing's pattern.** -/
theorem bingF_local : ∀ d : ℕ, PatLocal (bingF d) 0 (z d - 1)
  | 0 => by
      have hz : z 0 = 1 := rfl
      refine ⟨fun u _ h => ?_, fun u h1 h2 => ?_⟩ <;> omega
  | 1 => by
      have hz : z 1 = 2 := rfl
      refine ⟨fun u _ h => ?_, fun u h1 h2 => ?_⟩
      · have hu : u = 0 := by omega
        subst hu; simp [bingF]
      · omega
  | 2 => by
      have hz : z 2 = 3 := rfl
      refine ⟨fun u _ h => ?_, fun u h1 h2 => ?_⟩
      · rw [bingF_small 2 u le_rfl (by omega), bingF_small 2 (u + 1) le_rfl (by omega)]; omega
      · have hu : u = 1 := by omega
        subst hu
        refine ⟨fun a _ => ?_, fun _ b => ?_⟩
        · rw [bingF_small 2 _ le_rfl (by omega), bingF_small 2 1 le_rfl (by omega)] at a
          norm_num at a
        · rw [bingF_small 2 _ le_rfl (by omega), bingF_small 2 1 le_rfl (by omega)] at b
          norm_num at b
  | d + 3 => by
      have hA3 := z_three_le (d + 2) (by omega)
      have hB2 := z_two_le (d + 1) (by omega)
      have hz := z_succ3 d
      set zA := z (d + 2) with hzA
      set zB := z (d + 1) with hzB
      have cA : PatLocal (bingF (d + 3)) 0 (zA - 1) :=
        (bingF_local (d + 2)).congr (fun u _ hu => bingF_A d u (by omega))
      have cB : PatLocal (bingF (d + 3)) (zA - 1) (zA + zB - 2) := by
        have := (((bingF_local (d + 1)).neg ((d : ℤ) + 2)).shift (zA - 1) 0)
        rw [show 0 + (zA - 1) = zA - 1 by omega,
          show z (d + 1) - 1 + (zA - 1) = zA + zB - 2 by omega] at this
        refine this.congr (fun u hu1 hu2 => ?_)
        rw [bingF_B d u hu1 (by omega)]; ring
      have cC : PatLocal (bingF (d + 3)) (zA + zB - 2) (z (d + 3) - 1) := by
        have := ((bingF_local (d + 2)).shift (zA + zB - 2) 1)
        rw [show 0 + (zA + zB - 2) = zA + zB - 2 by omega,
          show z (d + 2) - 1 + (zA + zB - 2) = z (d + 3) - 1 by omega] at this
        refine this.congr (fun u hu1 _ => ?_)
        rw [bingF_C d u hu1]
      -- values around the two junctions
      have j1 : bingF (d + 3) (zA - 1) = (d : ℤ) + 2 := by
        rw [bingF_A d _ (by omega), bingF_top (d + 2) _ le_rfl]; push_cast; ring
      have j1m : bingF (d + 3) (zA - 1 - 1) = (d : ℤ) + 1 := by
        rw [bingF_A d _ (by omega)]
        have := bingF_rev (d + 2) 1 (by omega)
        rw [bingF_one _ (by omega)] at this
        rw [show zA - 1 - 1 = z (d + 2) - 1 - 1 by rfl, this]; push_cast; ring
      have j1mm : bingF (d + 3) (zA - 1 - 2) = (d : ℤ) := by
        rw [bingF_A d _ (by omega)]
        have := bingF_rev (d + 2) 2 (by omega)
        rw [bingF_two _ (by omega)] at this
        rw [show zA - 1 - 2 = z (d + 2) - 1 - 2 by rfl, this]; push_cast; ring
      have j1p : bingF (d + 3) (zA - 1 + 1) = (d : ℤ) + 1 := by
        rw [bingF_B d _ (by omega) (by omega), show zA - 1 + 1 - (zA - 1) = 1 by omega,
          bingF_one _ (by omega)]; ring
      have j2 : bingF (d + 3) (zA + zB - 2) = 1 := by
        rw [bingF_C d _ le_rfl, Nat.sub_self, bingF_zero]; ring
      have j2m : bingF (d + 3) (zA + zB - 2 - 1) = 2 := by
        rw [bingF_B d _ (by omega) (by omega)]
        have := bingF_rev (d + 1) 1 (by omega)
        rw [bingF_one _ (by omega)] at this
        rw [show zA + zB - 2 - 1 - (zA - 1) = z (d + 1) - 1 - 1 by omega, this]; push_cast; ring
      have j2p : bingF (d + 3) (zA + zB - 2 + 1) = 2 := by
        rw [bingF_C d _ (by omega), show zA + zB - 2 + 1 - (zA + zB - 2) = 1 by omega,
          bingF_one _ (by omega)]; ring
      have j2pp : bingF (d + 3) (zA + zB - 2 + 2) = 3 := by
        rw [bingF_C d _ (by omega), show zA + zB - 2 + 2 - (zA + zB - 2) = 2 by omega,
          bingF_two _ (by omega)]; ring
      refine ⟨fun u _ hu => ?_, fun u h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge u (zA - 1) with h | h
        · exact cA.1 u (by omega) h
        rcases Nat.lt_or_ge u (zA + zB - 2) with h' | h'
        · exact cB.1 u h h'
        · exact cC.1 u h' hu
      · rcases Nat.lt_or_ge u (zA - 1) with h | h
        · have := cA.2 u h1 h
          exact ⟨this.1.mono le_rfl (by omega), this.2.mono le_rfl (by omega)⟩
        rcases Nat.lt_or_ge (zA - 1) u with h' | h'
        · rcases Nat.lt_or_ge u (zA + zB - 2) with h'' | h''
          · have := cB.2 u h' h''
            exact ⟨this.1.mono (by omega) (by omega), this.2.mono (by omega) (by omega)⟩
          rcases Nat.lt_or_ge (zA + zB - 2) u with h3 | h3
          · have := cC.2 u h3 h2
            exact ⟨this.1.mono (by omega) le_rfl, this.2.mono (by omega) le_rfl⟩
          · have hu : u = zA + zB - 2 := by omega
            subst hu
            refine ⟨fun _ _ => Or.inr ⟨by omega, by rw [j2pp, j2]; norm_num⟩, fun a _ => ?_⟩
            rw [j2m, j2] at a; norm_num at a
        · have hu : u = zA - 1 := by omega
          subst hu
          refine ⟨fun a _ => ?_, fun _ _ => Or.inl ⟨by omega, by rw [j1mm, j1]; ring⟩⟩
          rw [j1m, j1] at a; linarith

end HPC.Fold
