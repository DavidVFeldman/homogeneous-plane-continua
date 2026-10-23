import HPC.Plane.Stutter

/-!
# Batch 202, §4.1: the sweep lemma

Crookedness for `ℤ`-indexed level sequences (`PatCrookedOnZ`), and the **sweep lemma**
(commission 202 §4.1) in the following shape. The walk `g : ℤ → ℤ` is cut into blocks
`[n L, (n + 1) L]` of a fixed length `L > 0` (closed: consecutive blocks share their junction).
Block `n` has a window `[b n, t n]` and a direction `up n`; on the block `g` stays in the window,
is crooked, starts at the extreme where it starts and ends at the opposite extreme. Directions
alternate, and the window changes only by one end: after an up block the bottom may grow by one,
after a down block the top may grow by one. A junction `m` is an *event* if the windows of
blocks `m - 1` and `m` differ.

**Shape change** (recorded in the report). Blocks have a fixed length, and the bound on events is
*at most two* events at junctions inside the interval (commission: at most three). The sweep
pattern of §4.2 has at most two events in every window it needs, and with at most two events
Case 2b of the commission's proof cannot occur. The commission's bound, at most three events, is
proved in the same block shape as `sweep_lemma3` (`HPC/BJ59/Sweep3.lean`).
-/

namespace HPC.BJ59

open HPC.Fold

/-- `r` and `s` lie strictly between `i` and `j`, `r` nearer to `i` (integer indices). -/
def NBetweenZ (i r s j : ℤ) : Prop := (i < r ∧ r < s ∧ s < j) ∨ (j < s ∧ s < r ∧ r < i)

/-- Crookedness of an integer-indexed level sequence on the window `[lo, hi]`. -/
def PatCrookedOnZ (g : ℤ → ℤ) (lo hi : ℤ) : Prop :=
  ∀ i j, lo ≤ i → i ≤ hi → lo ≤ j → j ≤ hi → ∀ h k : ℤ, g i ≤ h → k ≤ g j → h + 3 ≤ k →
    ∃ r s, NBetweenZ i r s j ∧ g r = k - 1 ∧ g s = h + 1

/-- From integer indices to natural ones. -/
theorem PatCrookedOnZ.toNat {g : ℤ → ℤ} {a : ℤ} {n : ℕ} (hc : PatCrookedOnZ g a (a + n)) :
    PatCrookedOn (fun u : ℕ => g (a + u)) 0 n := by
  intro i j _ hi _ hj h k hgi hgj hhk
  obtain ⟨r, s, hb, hr, hs⟩ := hc (a + i) (a + j) (by omega) (by omega) (by omega) (by omega)
    h k hgi hgj hhk
  have hr0 : 0 ≤ r - a := by unfold NBetweenZ at hb; omega
  have hs0 : 0 ≤ s - a := by unfold NBetweenZ at hb; omega
  refine ⟨(r - a).toNat, (s - a).toNat, ?_, ?_, ?_⟩
  · unfold NBetweenZ at hb; unfold NBetween; omega
  · simp only; rw [Int.toNat_of_nonneg hr0]; simpa using hr
  · simp only; rw [Int.toNat_of_nonneg hs0]; simpa using hs

/-- From natural indices to integer ones. -/
theorem PatCrookedOn.toZ {g : ℕ → ℤ} {lo hi : ℕ} (hc : PatCrookedOn g lo hi) (a : ℤ)
    (g' : ℤ → ℤ) (he : ∀ u : ℕ, lo ≤ u → u ≤ hi → g' (a + u) = g u) :
    PatCrookedOnZ g' (a + lo) (a + hi) := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  have ei : i = a + ((i - a).toNat : ℕ) := by omega
  have ej : j = a + ((j - a).toNat : ℕ) := by omega
  rw [ei, he _ (by omega) (by omega)] at hgi
  rw [ej, he _ (by omega) (by omega)] at hgj
  obtain ⟨r, s, hb, hr, hs⟩ := hc (i - a).toNat (j - a).toNat (by omega) (by omega) (by omega)
    (by omega) h k hgi hgj hhk
  refine ⟨a + r, a + s, ?_, ?_, ?_⟩
  · unfold NBetween at hb; unfold NBetweenZ; omega
  · rw [he r (by unfold NBetween at hb; omega) (by unfold NBetween at hb; omega)]; exact hr
  · rw [he s (by unfold NBetween at hb; omega) (by unfold NBetween at hb; omega)]; exact hs

/-- Extending a crooked window by one index carrying the same value as the last one. -/
theorem PatCrookedOnZ.extend {g : ℤ → ℤ} {lo hi : ℤ} (hc : PatCrookedOnZ g lo hi)
    (he : g (hi + 1) = g hi) : PatCrookedOnZ g lo (hi + 1) := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  by_cases ci : i = hi + 1
  · by_cases cj : j = hi + 1
    · subst ci cj; omega
    · subst ci
      rw [he] at hgi
      obtain ⟨r, s, hb, hr, hs⟩ := hc hi j (by omega) le_rfl hj1 (by omega) h k hgi hgj hhk
      exact ⟨r, s, by unfold NBetweenZ at *; omega, hr, hs⟩
  · by_cases cj : j = hi + 1
    · subst cj
      rw [he] at hgj
      obtain ⟨r, s, hb, hr, hs⟩ := hc i hi hi1 (by omega) (by omega) le_rfl h k hgi hgj hhk
      exact ⟨r, s, by unfold NBetweenZ at *; omega, hr, hs⟩
    · exact hc i j hi1 (by omega) hj1 (by omega) h k hgi hgj hhk

section Walk

variable (g : ℤ → ℤ)

/-- A discrete intermediate value theorem on integer indices. -/
theorem exists_eq_of_lipZ (hg : ∀ u, |g (u + 1) - g u| ≤ 1) {a c : ℤ} (hac : a ≤ c) {v : ℤ}
    (h : (g a ≤ v ∧ v ≤ g c) ∨ (g c ≤ v ∧ v ≤ g a)) : ∃ r, a ≤ r ∧ r ≤ c ∧ g r = v := by
  induction c, hac using Int.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, by omega⟩
  | succ c hac ih =>
      by_cases hv : (g a ≤ v ∧ v ≤ g c) ∨ (g c ≤ v ∧ v ≤ g a)
      · obtain ⟨r, h1, h2, h3⟩ := ih hv
        exact ⟨r, h1, by omega, h3⟩
      · have := hg c
        rw [abs_le] at this
        exact ⟨c + 1, by omega, le_rfl, by omega⟩

/-- The last index of `[i, j]` at level `≤ h`. -/
theorem exists_last_le {i j h : ℤ} (hij : i ≤ j) (hi : g i ≤ h) :
    ∃ t₀, i ≤ t₀ ∧ t₀ ≤ j ∧ g t₀ ≤ h ∧ ∀ u, t₀ < u → u ≤ j → h < g u := by
  induction j, hij using Int.le_induction with
  | base => exact ⟨i, le_rfl, le_rfl, hi, fun u h1 h2 => by omega⟩
  | succ j hij ih =>
      by_cases hj : g (j + 1) ≤ h
      · exact ⟨j + 1, by omega, le_rfl, hj, fun u h1 h2 => by omega⟩
      · obtain ⟨t₀, h1, h2, h3, h4⟩ := ih
        refine ⟨t₀, h1, by omega, h3, fun u hu1 hu2 => ?_⟩
        rcases (show u ≤ j ∨ u = j + 1 by omega) with e | e
        · exact h4 u hu1 e
        · subst e; omega

/-- The first index of `[t₀, j]` at level `≥ k`. -/
theorem exists_first_ge {t₀ j k : ℤ} (htj : t₀ ≤ j) (hj : k ≤ g j) :
    ∃ s₀, t₀ ≤ s₀ ∧ s₀ ≤ j ∧ k ≤ g s₀ ∧ ∀ u, t₀ ≤ u → u < s₀ → g u < k := by
  have key : ∀ j, t₀ ≤ j → (∃ u, t₀ ≤ u ∧ u ≤ j ∧ k ≤ g u) →
      ∃ s₀, t₀ ≤ s₀ ∧ s₀ ≤ j ∧ k ≤ g s₀ ∧ ∀ u, t₀ ≤ u → u < s₀ → g u < k := by
    intro j htj
    induction j, htj using Int.le_induction with
    | base =>
        rintro ⟨u, h1, h2, h3⟩
        exact ⟨t₀, le_rfl, le_rfl, by rwa [show u = t₀ by omega] at h3,
          fun u h1 h2 => by omega⟩
    | succ j hj ih =>
        rintro ⟨u, h1, h2, h3⟩
        by_cases hex : ∃ u, t₀ ≤ u ∧ u ≤ j ∧ k ≤ g u
        · obtain ⟨s₀, a1, a2, a3, a4⟩ := ih hex
          exact ⟨s₀, a1, by omega, a3, a4⟩
        · push_neg at hex
          have hu : u = j + 1 := by
            by_contra hne
            exact absurd h3 (not_le.mpr (hex u h1 (by omega)))
          subst hu
          exact ⟨j + 1, by omega, le_rfl, h3, fun v hv1 hv2 => hex v hv1 (by omega)⟩
  exact key j htj ⟨j, htj, le_rfl, hj⟩

/-- First growth of a monotone sequence with steps `0` or `1`. -/
theorem exists_first_growth (f : ℤ → ℤ) (hf : ∀ n, f n ≤ f (n + 1)) {n₁ n₂ : ℤ}
    (h12 : n₁ ≤ n₂) (hlt : f n₁ < f n₂) :
    ∃ m, n₁ < m ∧ m ≤ n₂ ∧ f (m - 1) = f n₁ ∧ f n₁ < f m := by
  have mono : ∀ a c, a ≤ c → f a ≤ f c := by
    intro a c hac
    induction c, hac using Int.le_induction with
    | base => exact le_rfl
    | succ c _ ih => exact ih.trans (hf c)
  induction n₂, h12 using Int.le_induction with
  | base => omega
  | succ n₂ h12 ih =>
      by_cases hlt' : f n₁ < f n₂
      · obtain ⟨m, a1, a2, a3, a4⟩ := ih hlt'
        exact ⟨m, a1, by omega, a3, a4⟩
      · have := mono n₁ n₂ h12
        exact ⟨n₂ + 1, by omega, le_rfl, by simp; omega, hlt⟩

end Walk

/-- **The sweep lemma** (commission 202 §4.1, shape adjusted: fixed block length `L`, at most two
events). `g` has unit steps; block `n` is `[n L, (n + 1) L]`, with window `[b n, t n]` and direction
`up n`. On a block `g` stays in the window and is crooked; it starts at the bottom and ends at the
top if `up n`, and the reverse otherwise. Directions alternate. After an up block the top is kept
and the bottom grows by `0` or `1`; after a down block the bottom is kept and the top grows by `0`
or `1`. If no three junctions in `[lo, hi]` are events, `g` is crooked on `[lo, hi]`. -/
theorem sweep_lemma (g : ℤ → ℤ) (L : ℤ) (hL : 0 < L) (b t : ℤ → ℤ) (up : ℤ → Prop)
    [DecidablePred up]
    (hstep : ∀ u, |g (u + 1) - g u| ≤ 1)
    (hrange : ∀ n u, n * L ≤ u → u ≤ (n + 1) * L → b n ≤ g u ∧ g u ≤ t n)
    (hend : ∀ n, g ((n + 1) * L) = if up n then t n else b n)
    (hcrook : ∀ n, PatCrookedOnZ g (n * L) ((n + 1) * L))
    (halt : ∀ n, up (n + 1) ↔ ¬ up n)
    (hwin_up : ∀ n, up n → t (n + 1) = t n ∧ (b (n + 1) = b n ∨ b (n + 1) = b n + 1))
    (hwin_down : ∀ n, ¬ up n → b (n + 1) = b n ∧ (t (n + 1) = t n ∨ t (n + 1) = t n + 1))
    {lo hi : ℤ}
    (hev : ∀ m₁ m₂ m₃ : ℤ, m₁ < m₂ → m₂ < m₃ → lo ≤ m₁ * L → m₃ * L ≤ hi →
      (b m₁ ≠ b (m₁ - 1) ∨ t m₁ ≠ t (m₁ - 1)) → (b m₂ ≠ b (m₂ - 1) ∨ t m₂ ≠ t (m₂ - 1)) →
      (b m₃ ≠ b (m₃ - 1) ∨ t m₃ ≠ t (m₃ - 1)) → False) :
    PatCrookedOnZ g lo hi := by
  -- monotonicity of the windows
  have tmono1 : ∀ n, t n ≤ t (n + 1) := by
    intro n
    by_cases hu : up n
    · have := (hwin_up n hu).1; omega
    · have := (hwin_down n hu).2; omega
  have tmono : ∀ a c, a ≤ c → t a ≤ t c := by
    intro a c hac
    induction c, hac using Int.le_induction with
    | base => exact le_rfl
    | succ c _ ih => exact ih.trans (tmono1 c)
  have tstep : ∀ n, t n ≤ t (n - 1) + 1 := by
    intro n
    have e : n = n - 1 + 1 := by ring
    by_cases hu : up (n - 1)
    · have := (hwin_up (n - 1) hu).1; rw [← e] at this; omega
    · have := (hwin_down (n - 1) hu).2; rw [← e] at this; omega
  -- the block of an index
  have blk : ∀ u, (u / L) * L ≤ u ∧ u < (u / L + 1) * L := by
    intro u
    refine ⟨Int.ediv_mul_le u hL.ne', ?_⟩
    have := Int.lt_ediv_add_one_mul_self u hL
    linarith
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  rcases le_total i j with hij | hji
  · -- ascending case
    obtain ⟨t₀, a1, a2, a3, a4⟩ := exists_last_le g hij hgi
    obtain ⟨s₀, b1, b2, b3, b4⟩ := exists_first_ge g a2 hgj
    have hts : t₀ < s₀ := by
      rcases eq_or_lt_of_le b1 with e | e
      · subst e; omega
      · exact e
    suffices ∃ r s, t₀ < r ∧ r < s ∧ s < s₀ ∧ g r = k - 1 ∧ g s = h + 1 by
      obtain ⟨r, s, c1, c2, c3, c4, c5⟩ := this
      exact ⟨r, s, Or.inl ⟨by omega, c2, by omega⟩, c4, c5⟩
    set n := t₀ / L with hn
    obtain ⟨n1, n2⟩ := blk t₀
    rw [← hn] at n1 n2
    by_cases c1 : s₀ ≤ (n + 1) * L
    · obtain ⟨r, s, hb, hr, hs⟩ := hcrook n t₀ s₀ n1 n2.le (by omega) c1 h k a3 b3 hhk
      refine ⟨r, s, ?_, ?_, ?_, hr, hs⟩ <;> · unfold NBetweenZ at hb; omega
    · push_neg at c1
      set e := (n + 1) * L with he
      have ge1 : h < g e := a4 e n2 (by omega)
      have ge2 : g e < k := b4 e (by omega) c1
      have hupn : up n := by
        by_contra hnu
        have h1 := hend n
        rw [if_neg hnu, ← he] at h1
        have := (hrange n t₀ n1 n2.le).1
        omega
      have hge : g e = t n := by rw [he, hend n, if_pos hupn]
      have hnu1 : ¬ up (n + 1) := by rw [halt]; simpa using hupn
      obtain ⟨wt, wb⟩ := hwin_up n hupn
      have hL1 : e < (n + 1 + 1) * L := by rw [he]; nlinarith
      have c2 : (n + 1 + 1) * L < s₀ := by
        by_contra hc
        push_neg at hc
        have := (hrange (n + 1) s₀ (by omega) hc).2
        omega
      set e2 := (n + 1 + 1) * L with he2
      have ge3 : h < g e2 := a4 e2 (by omega) (by omega)
      have ge4 : g e2 = b (n + 1) := by rw [he2, hend (n + 1), if_neg hnu1]
      have hbn : b n ≤ h := le_trans (hrange n t₀ n1 n2.le).1 a3
      have hb1 : b (n + 1) = b n + 1 := by rcases wb with w | w <;> omega
      have hbh : b n = h := by omega
      by_cases c3 : k - 1 ≤ t n
      · obtain ⟨r, r1, r2, r3⟩ := exists_eq_of_lipZ g hstep (show t₀ ≤ e by omega)
          (v := k - 1) (Or.inl ⟨by omega, by omega⟩)
        have : r ≠ t₀ := fun hr => by rw [hr] at r3; omega
        exact ⟨r, e2, by omega, by omega, c2, r3, by omega⟩
      · exfalso
        push_neg at c3
        set n₂ := s₀ / L with hn₂
        obtain ⟨m1, m2⟩ := blk s₀
        rw [← hn₂] at m1 m2
        have htn2 : k ≤ t n₂ := le_trans b3 (hrange n₂ s₀ m1 m2.le).2
        have hn12 : n + 1 + 1 ≤ n₂ := by
          by_contra hc; push_neg at hc
          have : (n₂ + 1) * L ≤ (n + 1 + 1) * L := by nlinarith
          omega
        obtain ⟨p1, q1, q2, q3, q4⟩ := exists_first_growth t tmono1
          (show n + 1 ≤ n₂ by omega) (by omega)
        have tst := tstep p1
        obtain ⟨p2, r1, r2, r3, r4⟩ := exists_first_growth t tmono1
          (show p1 ≤ n₂ by omega) (by omega)
        refine hev (n + 1) p1 p2 q1 r1 (by omega) ?_ ?_ ?_ ?_
        · have : p2 * L ≤ n₂ * L := by nlinarith
          omega
        · left; simp; omega
        · right; omega
        · right
          have := tmono p1 (p2 - 1) (by omega)
          omega
  · -- descending case
    have hjlt : j < i := by
      rcases eq_or_lt_of_le hji with e | e
      · subst e; omega
      · exact e
    obtain ⟨s₀, a1, a2, a3, a4⟩ := exists_last_le (fun u => -g u) hji (h := -k) (by simp; omega)
    obtain ⟨t₀, b1, b2, b3, b4⟩ := exists_first_ge (fun u => -g u) a2 (k := -h) (by simp; omega)
    have hst : s₀ < t₀ := by
      rcases eq_or_lt_of_le b1 with e | e
      · subst e; omega
      · exact e
    suffices ∃ r s, s₀ < s ∧ s < r ∧ r < t₀ ∧ g r = k - 1 ∧ g s = h + 1 by
      obtain ⟨r, s, c1, c2, c3, c4, c5⟩ := this
      exact ⟨r, s, Or.inr ⟨by omega, c2, by omega⟩, c4, c5⟩
    set n := s₀ / L with hn
    obtain ⟨n1, n2⟩ := blk s₀
    rw [← hn] at n1 n2
    by_cases c1 : t₀ ≤ (n + 1) * L
    · obtain ⟨r, s, hb, hr, hs⟩ := hcrook n t₀ s₀ (by omega) c1 n1 n2.le h k (by omega)
        (by omega) hhk
      refine ⟨r, s, ?_, ?_, ?_, hr, hs⟩ <;> · unfold NBetweenZ at hb; omega
    · exfalso
      push_neg at c1
      set e := (n + 1) * L with he
      have ge1 : g e < k := by have := a4 e n2 (by omega); omega
      have ge2 : h < g e := by have := b4 e (by omega) c1; omega
      have hnu : ¬ up n := by
        intro hu
        have h1 := hend n
        rw [if_pos hu, ← he] at h1
        have := (hrange n s₀ n1 n2.le).2
        omega
      have hge : g e = b n := by rw [he, hend n, if_neg hnu]
      have hu1 : up (n + 1) := by rw [halt]; exact hnu
      obtain ⟨wb, wt⟩ := hwin_down n hnu
      have c2 : (n + 1 + 1) * L < t₀ := by
        by_contra hc
        push_neg at hc
        have := (hrange (n + 1) t₀ (by omega) hc).1
        omega
      set e2 := (n + 1 + 1) * L with he2
      have hL1 : e < e2 := by rw [he, he2]; nlinarith
      have ge3 : g e2 < k := by have := a4 e2 (by omega) (by omega); omega
      have ge4 : g e2 = t (n + 1) := by rw [he2, hend (n + 1), if_pos hu1]
      have := (hrange n s₀ n1 n2.le).2
      have := tmono1 n
      omega

end HPC.BJ59
