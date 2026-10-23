import HPC.BJ59.Sweep3

/-!
# Batch 202, §8: a sweep walk with four events that is not crooked

Commission 202 §8 asks for a sweep walk with four events that is not crooked, as a certificate
that the sweep lemma needs a bound on the number of events. The walk `cert4G` below has blocks of
length `2` (the block structure of `sweep_lemma`), windows of width `1` or `2` (so every block is
trivially crooked), alternating directions, and windows that change by one end at a time, as
`sweep_lemma` requires. Exactly four junctions in `[0, 10]` are events, and on `[0, 10]` the walk
climbs from `0` to `4` without returning from `3` to `1`.

The values on `[0, 10]` are `0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4`.

The same walk tests `sweep_lemma3` (at most three events, `HPC/BJ59/Sweep3.lean`) on a window with
exactly three events: on `[0, 7]` the events are the junctions `1, 2, 3`, and the walk is crooked
there (`nonvac_sweep_three_events`). On `[0, 7]` the walk takes the values `0, …, 3`, so the
crookedness is not vacuous.
-/

namespace HPC.BJ59

namespace Cert4

/-- The walk: period-4 sweeps across `[0, 2]` up to index `2`, across `[2, 4]` from index `8`,
and four sweeps with moving windows in between. -/
def cert4G (u : ℤ) : ℤ :=
  if u ≤ 2 then (if u % 4 = 3 then 1 else u % 4)
  else if 8 ≤ u then 2 + (if u % 4 = 3 then 1 else u % 4)
  else if u = 3 then 2 else if u = 4 then 1 else if u = 5 then 2 else if u = 6 then 3 else 3

/-- Bottoms of the windows. -/
def cert4B (n : ℤ) : ℤ := if n ≤ 0 then 0 else if n ≤ 2 then 1 else 2

/-- Tops of the windows. -/
def cert4T (n : ℤ) : ℤ := if n ≤ 1 then 2 else if n ≤ 3 then 3 else 4

/-- Directions: even blocks go up. -/
def cert4Up (n : ℤ) : Prop := n % 2 = 0

instance : DecidablePred cert4Up := fun n => inferInstanceAs (Decidable (n % 2 = 0))

theorem cert4_step (u : ℤ) : |cert4G (u + 1) - cert4G u| ≤ 1 := by
  rw [abs_le]; unfold cert4G; constructor <;> split_ifs <;> omega

theorem cert4_range (n u : ℤ) (h1 : n * 2 ≤ u) (h2 : u ≤ (n + 1) * 2) :
    cert4B n ≤ cert4G u ∧ cert4G u ≤ cert4T n := by
  unfold cert4B cert4T cert4G; constructor <;> split_ifs <;> omega

theorem cert4_end (n : ℤ) :
    cert4G ((n + 1) * 2) = if cert4Up n then cert4T n else cert4B n := by
  unfold cert4Up cert4B cert4T cert4G; split_ifs <;> omega

theorem cert4_crook (n : ℤ) : PatCrookedOnZ cert4G (n * 2) ((n + 1) * 2) := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  have a := cert4_range n i hi1 hi2
  have b := cert4_range n j hj1 hj2
  have : cert4T n ≤ cert4B n + 2 := by unfold cert4T cert4B; split_ifs <;> omega
  omega

theorem cert4_alt (n : ℤ) : cert4Up (n + 1) ↔ ¬ cert4Up n := by
  unfold cert4Up; omega

theorem cert4_win_up (n : ℤ) (hn : cert4Up n) :
    cert4T (n + 1) = cert4T n ∧ (cert4B (n + 1) = cert4B n ∨ cert4B (n + 1) = cert4B n + 1) := by
  unfold cert4Up at hn; unfold cert4T cert4B; split_ifs <;> omega

theorem cert4_win_down (n : ℤ) (hn : ¬ cert4Up n) :
    cert4B (n + 1) = cert4B n ∧ (cert4T (n + 1) = cert4T n ∨ cert4T (n + 1) = cert4T n + 1) := by
  unfold cert4Up at hn; unfold cert4T cert4B; split_ifs <;> omega

/-- The junctions `m` with `0 ≤ 2 m ≤ 10` that are events are exactly `m = 1, 2, 3, 4`. -/
theorem cert4_events (m : ℤ) (h1 : 0 ≤ m * 2) (h2 : m * 2 ≤ 10) :
    (cert4B m ≠ cert4B (m - 1) ∨ cert4T m ≠ cert4T (m - 1)) ↔ (1 ≤ m ∧ m ≤ 4) := by
  unfold cert4B cert4T; split_ifs <;> omega

/-- The walk is not crooked on `[0, 10]`. -/
theorem cert4_not_crooked : ¬ PatCrookedOnZ cert4G 0 10 := by
  intro hc
  obtain ⟨r, s, hb, hr, hs⟩ := hc 0 10 le_rfl (by norm_num) (by norm_num) le_rfl 0 4
    (by decide) (by decide) (by norm_num)
  unfold NBetweenZ at hb
  unfold cert4G at hr hs
  split_ifs at hr hs <;> omega

end Cert4

open Cert4 in
/-- **A sweep walk with four events that is not crooked** (commission 202 §8): every structural
hypothesis of `sweep_lemma` holds for `cert4G` (blocks of length `2`), the interval `[0, 10]`
contains exactly four event junctions, and `cert4G` is not crooked on `[0, 10]`. So the bound on
the number of events in the sweep lemma cannot be dropped, and cannot be raised to four. -/
theorem nonvac_sweep_four_events :
    (∀ u, |cert4G (u + 1) - cert4G u| ≤ 1) ∧
    (∀ n u, n * 2 ≤ u → u ≤ (n + 1) * 2 → cert4B n ≤ cert4G u ∧ cert4G u ≤ cert4T n) ∧
    (∀ n, cert4G ((n + 1) * 2) = if cert4Up n then cert4T n else cert4B n) ∧
    (∀ n, PatCrookedOnZ cert4G (n * 2) ((n + 1) * 2)) ∧
    (∀ n, cert4Up (n + 1) ↔ ¬ cert4Up n) ∧
    (∀ n, cert4Up n → cert4T (n + 1) = cert4T n ∧
      (cert4B (n + 1) = cert4B n ∨ cert4B (n + 1) = cert4B n + 1)) ∧
    (∀ n, ¬ cert4Up n → cert4B (n + 1) = cert4B n ∧
      (cert4T (n + 1) = cert4T n ∨ cert4T (n + 1) = cert4T n + 1)) ∧
    (∀ m : ℤ, 0 ≤ m * 2 → m * 2 ≤ 10 →
      ((cert4B m ≠ cert4B (m - 1) ∨ cert4T m ≠ cert4T (m - 1)) ↔ (1 ≤ m ∧ m ≤ 4))) ∧
    ¬ PatCrookedOnZ cert4G 0 10 :=
  ⟨cert4_step, cert4_range, cert4_end, cert4_crook, cert4_alt, cert4_win_up, cert4_win_down,
    cert4_events, cert4_not_crooked⟩

open Cert4 in
/-- **The sweep lemma with at most three events on a window with exactly three events**
(commission 202 §8): on `[0, 7]` exactly the junctions `1, 2, 3` are events, and `cert4G` is
crooked there, by `sweep_lemma3`. The window contains indices with values `0` and `3`. -/
theorem nonvac_sweep_three_events :
    (∀ m : ℤ, 0 ≤ m * 2 → m * 2 ≤ 7 →
      ((cert4B m ≠ cert4B (m - 1) ∨ cert4T m ≠ cert4T (m - 1)) ↔ (1 ≤ m ∧ m ≤ 3))) ∧
    cert4G 0 = 0 ∧ cert4G 6 = 3 ∧ PatCrookedOnZ cert4G 0 7 := by
  refine ⟨fun m h1 h2 => ?_, by decide, by decide, ?_⟩
  · rw [cert4_events m h1 (by omega)]; omega
  · refine sweep_lemma3 cert4G 2 (by norm_num) cert4B cert4T cert4Up cert4_step cert4_range
      cert4_end cert4_crook cert4_alt cert4_win_up cert4_win_down ?_
    intro m₁ m₂ m₃ m₄ h12 h23 h34 hlo hhi e1 e2 e3 e4
    have := (cert4_events m₁ (by omega) (by omega)).1 e1
    have := (cert4_events m₄ (by omega) (by omega)).1 e4
    omega

end HPC.BJ59
