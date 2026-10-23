import HPC.BJ59.BJ59E

/-!
# Batch 202, §8: non-vacuity

* `CircDescr`: `planeDescr` is the witness (`exists_circDescr_plane`); in every circular
  description the sizes tend to infinity (`CircDescr.N_tendsto`), so constant `N` is impossible.
* The sweep lemma, in the shape of `Sweep.lean` (at most two events): on the sweep pattern it
  applies to a single sweep and to a window with exactly two events.
* `circExp`, `stdCircLink`: for `N = 0` the meeting criterion fails; for `N = 1, 2, 3` both sides
  hold for all `s`, `t`.
* `circ_step`: its hypotheses hold for the stuttered identity `x t = ⌊t / Q⌋`, `Q ≥ S`.
* The omission of batch 201: the halves of the plane example are continuous snake-like arcs of
  pseudo-arcs, and they are non-degenerate inputs for `BJThm10`, `BJStep`, `bj_theorem8_cor_sub`,
  `bj_theorem5_window` and `exists_window_set`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Fold

/-! ### Circular descriptions -/

/-- In every circular description the number of links tends to infinity (`five_le_lam` with
`lam → 0`): a description with constant `N` does not exist. -/
theorem CircDescr.N_tendsto {X : Type*} [MetricSpace X] (Δ : CircDescr X) :
    Tendsto (fun k => (Δ.N k : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hb : (0 : ℝ) < 5 / (|b| + 1) := by positivity
  have hev := (Δ.lam_tendsto.eventually (Iio_mem_nhds hb))
  filter_upwards [hev] with k hk
  have h5 := Δ.five_le_lam k
  have hN : (0 : ℝ) ≤ Δ.N k := Nat.cast_nonneg _
  have hl : 0 < Δ.lam k := by
    by_contra h; push_neg at h; nlinarith
  have : 5 < 5 / (|b| + 1) * Δ.N k := lt_of_le_of_lt h5 (by
    by_cases hN0 : (Δ.N k : ℝ) = 0
    · rw [hN0] at h5; linarith
    · exact mul_lt_mul_of_pos_right hk (lt_of_le_of_ne hN (Ne.symm hN0)))
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at this
  have := le_abs_self b
  nlinarith

/-! ### The sweep lemma on the sweep pattern -/

section Sweep

variable {m S : ℕ}

/-- The sweep lemma applied to the sweep pattern on any window with at most two junctions
`p L` with `3 ∣ p` (the only possible events). -/
theorem sweepX_crookedZ (hm : 5 ≤ m) (hS : 1 ≤ S) {lo hi : ℤ}
    (hev : ∀ p₁ p₂ p₃ : ℤ, p₁ < p₂ → p₂ < p₃ → p₁ % 3 = 0 → p₂ % 3 = 0 → p₃ % 3 = 0 →
      lo ≤ p₁ * sweepL m S → p₃ * sweepL m S ≤ hi → False) :
    PatCrookedOnZ (sweepX m S) lo hi := by
  have hL := sweepL_pos hm hS
  have hLz : (0 : ℤ) < sweepL m S := by exact_mod_cast hL
  refine sweep_lemma (sweepX m S) (sweepL m S) hLz (fun n => swB m (n / 3))
    (fun n => swT m (n / 3)) (fun n => (n + m) % 2 = 0) (sweepX_step hm hS) ?_ ?_
    (sweepX_block_crooked hm hS) (fun n => by omega) (fun n h => sw_win_up h)
    (fun n h => sw_win_down h) ?_
  · intro n u h1 h2
    rcases lt_or_eq_of_le h2 with h2 | h2
    · have e : u = n * sweepL m S + ((u - n * sweepL m S).toNat : ℕ) := by omega
      rw [e, sweepX_block hL _ _ (by
        have : u - n * sweepL m S < sweepL m S := by
          have : (n + 1) * (sweepL m S : ℤ) = n * sweepL m S + sweepL m S := by ring
          omega
        omega)]
      exact swVal_range hm n _
    · rw [h2, sweepX_junction hm hS]
      exact swVal_range hm n _
  · intro n
    rw [sweepX_junction hm hS, swVal_last hm hS]
  · intro p₁ p₂ p₃ h12 h23 hlo hhi e1 e2 e3
    have ev : ∀ p : ℤ, (swB m (p / 3) ≠ swB m ((p - 1) / 3) ∨
        swT m (p / 3) ≠ swT m ((p - 1) / 3)) → p % 3 = 0 := by
      intro p hp
      by_contra hc
      have : p / 3 = (p - 1) / 3 := by omega
      rcases hp with h | h <;> exact h (by rw [this])
    exact hev p₁ p₂ p₃ h12 h23 (ev p₁ e1) (ev p₂ e2) (ev p₃ e3) hlo hhi

/-- The junctions `p L` with `3 ∣ p` are events: the window changes there. -/
theorem sweep_event (p : ℤ) (hp : p % 3 = 0) :
    swB m (p / 3) ≠ swB m ((p - 1) / 3) ∨ swT m (p / 3) ≠ swT m ((p - 1) / 3) := by
  have e : (p - 1) / 3 = p / 3 - 1 := by omega
  rw [e]
  unfold swB swT
  omega

end Sweep

/-- **The sweep lemma on a single sweep** (no junction inside): block 1 of the sweep pattern
`m = 5`, `S = 1`. -/
theorem nonvac_sweep_single :
    PatCrookedOnZ (sweepX 5 1) (sweepL 5 1) (2 * sweepL 5 1) := by
  have hL : (0 : ℤ) < sweepL 5 1 := by exact_mod_cast sweepL_pos (m := 5) (S := 1) le_rfl le_rfl
  refine sweepX_crookedZ le_rfl le_rfl fun p₁ p₂ p₃ h12 h23 _ _ _ hlo hhi => ?_
  have a : 1 ≤ p₁ := by
    by_contra h; push_neg at h
    have : p₁ * (sweepL 5 1 : ℤ) ≤ 0 * sweepL 5 1 := by nlinarith
    linarith
  have b : p₃ ≤ 2 := by
    by_contra h; push_neg at h
    have : 3 * (sweepL 5 1 : ℤ) ≤ p₃ * sweepL 5 1 := by nlinarith
    linarith
  omega

/-- **The sweep lemma on a window with exactly two events**: junctions `3 L` and `6 L` of the
sweep pattern `m = 5`, `S = 1`, both events (`sweep_event`). -/
theorem nonvac_sweep_two_events :
    PatCrookedOnZ (sweepX 5 1) (3 * sweepL 5 1) (6 * sweepL 5 1) ∧
      (swB 5 (3 / 3) ≠ swB 5 ((3 - 1) / 3) ∨ swT 5 (3 / 3) ≠ swT 5 ((3 - 1) / 3)) ∧
      (swB 5 (6 / 3) ≠ swB 5 ((6 - 1) / 3) ∨ swT 5 (6 / 3) ≠ swT 5 ((6 - 1) / 3)) := by
  refine ⟨?_, sweep_event 3 rfl, sweep_event 6 rfl⟩
  have hL : (0 : ℤ) < sweepL 5 1 := by exact_mod_cast sweepL_pos (m := 5) (S := 1) le_rfl le_rfl
  refine sweepX_crookedZ le_rfl le_rfl fun p₁ p₂ p₃ h12 h23 e1 e2 e3 hlo hhi => ?_
  have a : 3 ≤ p₁ := by
    by_contra h; push_neg at h
    have : p₁ * (sweepL 5 1 : ℤ) ≤ 2 * sweepL 5 1 := by nlinarith
    linarith
  have b : p₃ ≤ 6 := by
    by_contra h; push_neg at h
    have : 7 * (sweepL 5 1 : ℤ) ≤ p₃ * sweepL 5 1 := by nlinarith
    linarith
  omega

/-! ### The standard circular chains on degenerate inputs -/

/-- For `N = 0`, `circExp 0` maps everything onto the ray `{(e^v, 0)}`. -/
theorem circExp_zero (p : Pt) : circExp 0 p = (Real.exp p.2, 0) := by
  simp [circExp]

/-- For `N = 0` the meeting criterion of `stdCircLink_meet_iff` fails: links `0` and `5` meet,
but `|0 − 5 − n · 0| ≤ 1` has no solution. -/
theorem not_stdCircLink_meet_iff_zero :
    ¬ ∀ s t : ℤ, (stdCircLink 0 s ∩ stdCircLink 0 t).Nonempty ↔
      ∃ n : ℤ, |s - t - n * ((0 : ℕ) : ℤ)| ≤ 1 := by
  intro h
  have hmeet : (stdCircLink 0 0 ∩ stdCircLink 0 5).Nonempty := by
    refine ⟨circExp 0 (1, 1 / 2), ⟨(1, 1 / 2), ?_, rfl⟩, ⟨(11, 1 / 2), ?_, ?_⟩⟩
    · simp only [stdRectZ, mem_prod, mem_Ioo]; norm_num
    · simp only [stdRectZ, mem_prod, mem_Ioo]; norm_num
    · rw [circExp_zero, circExp_zero]
  obtain ⟨n, hn⟩ := (h 0 5).1 hmeet
  simp at hn

/-- For `N = 1, 2, 3` both sides of the meeting criterion hold for all `s`, `t`. -/
theorem stdCircLink_meet_small {N : ℕ} (hN1 : 1 ≤ N) (hN3 : N ≤ 3) (s t : ℤ) :
    (stdCircLink N s ∩ stdCircLink N t).Nonempty ∧ ∃ n : ℤ, |s - t - n * (N : ℤ)| ≤ 1 := by
  have hr : ∃ n : ℤ, |s - t - n * (N : ℤ)| ≤ 1 := by
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN1
    refine ⟨(s - t + 1) / N, ?_⟩
    have h1 := Int.emod_nonneg (s - t + 1) hNz.ne'
    have h2 := Int.emod_lt_of_pos (s - t + 1) hNz
    have h3 := Int.mul_ediv_add_emod (s - t + 1) N
    have hN3' : (N : ℤ) ≤ 3 := by exact_mod_cast hN3
    rw [abs_le]; constructor <;> nlinarith
  exact ⟨(CircStd.stdCircLink_meet_iff' (by omega) s t).2 hr, hr⟩

/-! ### `circ_step` on the stuttered identity -/

/-- The hypotheses of `circ_step` hold for the stuttered identity `x t = ⌊t / Q⌋` with `Q ≥ S`
(`y₀ = 0`, `B = 1`). -/
theorem nonvac_circ_step_hyps (Q S : ℕ) (hQ : 2 ≤ Q) (hSQ : S ≤ Q) :
    (∀ t : ℤ, (t + Q) / (Q : ℤ) = t / Q + 1) ∧
      (∀ t : ℤ, |(t + 1) / (Q : ℤ) - t / Q| ≤ 1) ∧
      (∀ s t : ℤ, s / (Q : ℤ) + 2 ≤ t / Q → (S : ℤ) ≤ |s - t|) ∧
      (∀ t : ℤ, |((t / (Q : ℤ) : ℤ) : ℝ) - (0 + (t : ℝ) / Q)| ≤ 1) := by
  have hQz : (0 : ℤ) < Q := by omega
  refine ⟨fun t => ?_, fun t => ?_, fun s t h => ?_, fun t => ?_⟩
  · rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hQz.ne']
  · have a1 := Int.mul_ediv_add_emod t Q
    have a2 := Int.mul_ediv_add_emod (t + 1) Q
    have b1 := Int.emod_nonneg t hQz.ne'
    have b2 := Int.emod_lt_of_pos t hQz
    have c1 := Int.emod_nonneg (t + 1) hQz.ne'
    have c2 := Int.emod_lt_of_pos (t + 1) hQz
    have d1 : t / (Q : ℤ) ≤ (t + 1) / Q := Int.ediv_le_ediv hQz (by omega)
    have d2 : (t + 1) / (Q : ℤ) ≤ t / Q + 1 := by
      have := Int.ediv_le_ediv hQz (show t + 1 ≤ t + Q by omega)
      rwa [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hQz.ne'] at this
    rw [abs_le]; constructor <;> omega
  · have a1 := Int.mul_ediv_add_emod s Q
    have a2 := Int.mul_ediv_add_emod t Q
    have b1 := Int.emod_nonneg s hQz.ne'
    have b2 := Int.emod_lt_of_pos s hQz
    have c1 := Int.emod_nonneg t hQz.ne'
    have c2 := Int.emod_lt_of_pos t hQz
    have : (Q : ℤ) * (s / Q) + 2 * Q ≤ Q * (t / Q) := by nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
    have : (S : ℤ) ≤ Q := by exact_mod_cast hSQ
    nlinarith
  · have hQr : (0 : ℝ) < Q := by exact_mod_cast hQz
    have a1 := Int.mul_ediv_add_emod t Q
    have b1 := Int.emod_nonneg t hQz.ne'
    have b2 := Int.emod_lt_of_pos t hQz
    have e : (t : ℝ) = Q * ((t / (Q : ℤ) : ℤ) : ℝ) + ((t % (Q : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast a1.symm
    have b1' : (0 : ℝ) ≤ ((t % (Q : ℤ) : ℤ) : ℝ) := by exact_mod_cast b1
    have b2' : ((t % (Q : ℤ) : ℤ) : ℝ) < Q := by exact_mod_cast b2
    rw [e, zero_add, show ((Q : ℝ) * ((t / (Q : ℤ) : ℤ) : ℝ) + ((t % (Q : ℤ) : ℤ) : ℝ)) / Q =
      ((t / (Q : ℤ) : ℤ) : ℝ) + ((t % (Q : ℤ) : ℤ) : ℝ) / Q by field_simp]
    rw [abs_le]; constructor
    · have : ((t % (Q : ℤ) : ℤ) : ℝ) / Q ≤ 1 := by rw [div_le_one hQr]; linarith
      linarith
    · have : 0 ≤ ((t % (Q : ℤ) : ℤ) : ℝ) / Q := div_nonneg b1' hQr.le
      linarith

end HPC.BJ59
