import HPC.Fold.Faithful

/-!
# Crookedness across the basepoint, in the form the jump-zigzag argument reads it

`CrkOn S lo hi` is the crookedness clause of the faithful model read on the level sequence alone,
re-indexed so that the basepoint sits at `0`: between two indices whose levels differ by three or
more the sequence first comes within one of the later level and then within one of the earlier
one. `crkOn_of_isCrookedIvF` derives it from `IsCrookedIvF`; `CrkOn.reverse` reads it backwards.

The two lemmas `up_core` and `down_core` are the whole of the crookedness used by the proof of
`S3` in `HPC/Fold/Zig77Main.lean`. The *left* arm is `j ↦ S (-j)`, the *right* arm `j ↦ S j`.
-/

namespace HPC.Fold.Z77

/-- Crookedness read on the levels, indices in `[lo, hi]`. -/
def CrkOn (S : ℤ → ℤ) (lo hi : ℤ) : Prop :=
  ∀ s t : ℤ, lo ≤ s → s < t → t ≤ hi →
    (S s + 3 ≤ S t → ∃ r r', s < r ∧ r < r' ∧ r' < t ∧
        S t - 2 ≤ S r ∧ S r ≤ S t - 1 ∧ S s ≤ S r' ∧ S r' ≤ S s + 1) ∧
    (S t + 3 ≤ S s → ∃ r r', s < r ∧ r < r' ∧ r' < t ∧
        S t ≤ S r ∧ S r ≤ S t + 1 ∧ S s - 2 ≤ S r' ∧ S r' ≤ S s - 1)

/-- **Crookedness read backwards.** -/
theorem CrkOn.reverse {S : ℤ → ℤ} {lo hi : ℤ} (h : CrkOn S lo hi) :
    CrkOn (fun x => S (-x)) (-hi) (-lo) := by
  intro s t hs hst ht
  obtain ⟨h1, h2⟩ := h (-t) (-s) (by omega) (by omega) (by omega)
  constructor
  · intro hlt
    obtain ⟨r, r', hr, hrr', hr', a1, a2, a3, a4⟩ := h2 hlt
    exact ⟨-r', -r, by omega, by omega, by omega, by simpa using a3, by simpa using a4,
      by simpa using a1, by simpa using a2⟩
  · intro hlt
    obtain ⟨r, r', hr, hrr', hr', a1, a2, a3, a4⟩ := h1 hlt
    exact ⟨-r', -r, by omega, by omega, by omega, by simpa using a3, by simpa using a4,
      by simpa using a1, by simpa using a2⟩

/-- The level sequence re-indexed at the basepoint `i`, extended by `0` outside `[0, n)`. -/
def reindex {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (x : ℤ) : ℤ :=
  if h : 0 ≤ (i : ℤ) + x ∧ (i : ℤ) + x < n then ρ ⟨((i : ℤ) + x).toNat, by omega⟩ else 0

theorem reindex_nat_right {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : ℕ) (hj : j < n - i.val) :
    reindex ρ i j = ρ ⟨i.val + j, by omega⟩ := by
  unfold reindex
  rw [dif_pos (by omega)]
  exact congrArg ρ (Fin.ext (by simp only; omega))

theorem reindex_nat_left {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : ℕ) (hj : j < i.val + 1) :
    reindex ρ i (-(j : ℤ)) = ρ ⟨i.val - j, by omega⟩ := by
  unfold reindex
  rw [dif_pos (by omega)]
  exact congrArg ρ (Fin.ext (by simp only; omega))

theorem reindex_fin {n : ℕ} (ρ : Fin n → ℤ) (i k : Fin n) :
    reindex ρ i ((k : ℤ) - i) = ρ k := by
  unfold reindex
  rw [dif_pos (by omega)]
  exact congrArg ρ (Fin.ext (by simp only; omega))

/-- **Crookedness of the faithful model, read on the levels.** -/
theorem crkOn_of_isCrookedIvF {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) :
    CrkOn (reindex ρ i) (-(i : ℤ)) ((n : ℤ) - 1 - i) := by
  intro s t hs hst ht
  set S := reindex ρ i
  have hS : ∀ k : Fin n, S ((k : ℤ) - i) = ρ k := reindex_fin ρ i
  set sf : Fin n := ⟨((i : ℤ) + s).toNat, by omega⟩
  set tf : Fin n := ⟨((i : ℤ) + t).toNat, by omega⟩
  have hsv : (sf : ℤ) = i + s := by simp only [sf]; omega
  have htv : (tf : ℤ) = i + t := by simp only [tf]; omega
  have hsf : S s = ρ sf := by rw [← hS sf, hsv]; ring_nf
  have htf : S t = ρ tf := by rw [← hS tf, htv]; ring_nf
  have hlt : sf < tf := by rw [Fin.lt_def]; omega
  have key : 3 ≤ |ρ sf - ρ tf| → ∃ r r' : Fin n, sf < r ∧ r < r' ∧ r' < tf ∧
      (ρ sf < ρ tf → (ρ r ≤ ρ tf - 1 ∧ ρ tf - 1 ≤ σ r) ∧ (ρ r' ≤ ρ sf + 1 ∧ ρ sf + 1 ≤ σ r')) ∧
      (ρ tf < ρ sf → (ρ r ≤ ρ tf + 1 ∧ ρ tf + 1 ≤ σ r) ∧ (ρ r' ≤ ρ sf - 1 ∧ ρ sf - 1 ≤ σ r')) :=
    fun h3 => hcr.crooked sf tf hlt (ρ sf) (ρ tf) ⟨sf, by simp, le_rfl, hcr.le sf⟩
      ⟨tf, by simp, le_rfl, hcr.le tf⟩ h3
  constructor
  · intro hup
    obtain ⟨r, r', h1, h2, h3, hc, -⟩ := key (by rw [le_abs]; omega)
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hc (by omega)
    have w1 := hcr.width r
    have w2 := hcr.width r'
    rw [Fin.lt_def] at h1 h2 h3
    refine ⟨(r : ℤ) - i, (r' : ℤ) - i, by omega, by omega, by omega, ?_⟩
    rw [hS, hS]
    omega
  · intro hdn
    obtain ⟨r, r', h1, h2, h3, -, hc⟩ := key (by rw [le_abs]; omega)
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hc (by omega)
    have w1 := hcr.width r
    have w2 := hcr.width r'
    rw [Fin.lt_def] at h1 h2 h3
    refine ⟨(r : ℤ) - i, (r' : ℤ) - i, by omega, by omega, by omega, ?_⟩
    rw [hS, hS]
    omega

/-- **The up core.** The left arm, from its time `τ` on, stays at `a - 1` or below until it
drops to `b - 2` at time `dr`, having been at `b` or above before `τ`; the right arm is at `b` or
above until it rises to `a + 2` at time `d`. Crookedness forbids it. -/
theorem up_core {S : ℤ → ℤ} {lo hi : ℤ} (hS : CrkOn S lo hi) (τ dr d : ℕ) (a b : ℤ)
    (hab : b ≤ a) (hlo : lo ≤ -(dr : ℤ)) (hhi : (d : ℤ) ≤ hi)
    (hF1 : ∀ j : ℕ, j < τ → b ≤ S (-(j : ℤ)))
    (hF2 : ∀ j : ℕ, τ ≤ j → j < dr → S (-(j : ℤ)) ≤ a - 1)
    (hF3 : S (-(dr : ℤ)) = b - 2)
    (hD1 : ∀ j : ℕ, j < d → b ≤ S j) (hD2 : S d = a + 2) : False := by
  have hst : -(dr : ℤ) < d := by
    rcases Nat.eq_zero_or_pos dr with h0 | h0
    · rcases Nat.eq_zero_or_pos d with h1 | h1
      · subst h0; subst h1; simp at hF3 hD2; omega
      · omega
    · omega
  obtain ⟨r, r', h1, h2, h3, a1, a2, a3, a4⟩ :=
    (hS (-(dr : ℤ)) d hlo hst hhi).1 (by rw [hF3, hD2]; omega)
  rw [hD2] at a1 a2
  rw [hF3] at a3 a4
  rcases le_or_gt 0 r' with hr' | hr'
  · have := hD1 r'.toNat (by omega)
    rw [Int.toNat_of_nonneg hr'] at this
    omega
  · have hj := hF1 (-r').toNat
    rw [show -(((-r').toNat : ℕ) : ℤ) = r' by rw [Int.toNat_of_nonneg (by omega)]; ring] at hj
    have hτ : τ ≤ (-r').toNat := by
      by_contra hc
      have := hj (by omega)
      omega
    have := hF2 (-r).toNat (by omega) (by omega)
    rw [show -(((-r).toNat : ℕ) : ℤ) = r by rw [Int.toNat_of_nonneg (by omega)]; ring] at this
    omega

/-- **The down core.** The left arm is at `b` or above before `τb`, at `a - 2` or below on
`[τb, σ)`, at `b + 1` or above on `[σ, rise)` and at `a + 2` at `rise`; the right arm is at `b` or
above before `τbD`, at `a - 1` or below on `[τbD, d)` and at `b - 2` at `d`. Crookedness forbids it:
once across the basepoint, and once more inside the left arm. -/
theorem down_core {S : ℤ → ℤ} {lo hi : ℤ} (hS : CrkOn S lo hi) (τb σ rise τbD d : ℕ) (a b : ℤ)
    (hab : b ≤ a) (hlo : lo ≤ -(rise : ℤ)) (hhi : (d : ℤ) ≤ hi)
    (hF1 : ∀ j : ℕ, j < τb → b ≤ S (-(j : ℤ)))
    (hF2 : ∀ j : ℕ, τb ≤ j → j < σ → S (-(j : ℤ)) ≤ a - 2)
    (hF3 : ∀ j : ℕ, σ ≤ j → j < rise → b + 1 ≤ S (-(j : ℤ)))
    (hF4 : S (-(rise : ℤ)) = a + 2)
    (hD1 : ∀ j : ℕ, j < τbD → b ≤ S j)
    (hD2 : ∀ j : ℕ, τbD ≤ j → j < d → S j ≤ a - 1)
    (hD3 : S d = b - 2) : False := by
  have hst : -(rise : ℤ) < d := by
    rcases Nat.eq_zero_or_pos rise with h0 | h0
    · rcases Nat.eq_zero_or_pos d with h1 | h1
      · subst h0; subst h1; simp at hF4 hD3; omega
      · omega
    · omega
  obtain ⟨r, r', h1, h2, h3, a1, a2, a3, a4⟩ :=
    (hS (-(rise : ℤ)) d hlo hst hhi).2 (by rw [hF4, hD3]; omega)
  rw [hD3] at a1 a2
  rw [hF4] at a3 a4
  rcases le_or_gt 0 r with hr | hr
  · -- on the right arm
    rcases lt_or_ge r.toNat τbD with hc | hc
    · have := hD1 r.toNat hc
      rw [Int.toNat_of_nonneg hr] at this
      omega
    · have := hD2 r'.toNat (by omega) (by omega)
      rw [Int.toNat_of_nonneg (by omega)] at this
      omega
  · -- on the left arm, strictly inside it
    set u := (-r).toNat with hu
    have hur : -(u : ℤ) = r := by rw [hu, Int.toNat_of_nonneg (by omega)]; ring
    have hu1 : τb ≤ u := by
      by_contra hc
      have := hF1 u (by omega)
      rw [hur] at this; omega
    have hu2 : u < σ := by
      by_contra hc
      have := hF3 u (by omega) (by omega)
      rw [hur] at this; omega
    -- the second reading, between the rise and `r`
    obtain ⟨q, q', g1, g2, g3, c1, c2, c3, c4⟩ :=
      (hS (-(rise : ℤ)) r hlo (by omega) (by omega)).2 (by rw [hF4]; omega)
    rw [hF4] at c3 c4
    have hq' : σ ≤ (-q').toNat := by
      by_contra hc
      have := hF2 (-q').toNat (by omega) (by omega)
      rw [show -(((-q').toNat : ℕ) : ℤ) = q' by rw [Int.toNat_of_nonneg (by omega)]; ring] at this
      omega
    have := hF3 (-q).toNat (by omega) (by omega)
    rw [show -(((-q).toNat : ℕ) : ℤ) = q by rw [Int.toNat_of_nonneg (by omega)]; ring] at this
    omega

end HPC.Fold.Z77
