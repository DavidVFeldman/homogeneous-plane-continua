import HPC.BJ59.Sweep

/-!
# Batch 202, §4.1: the sweep lemma with at most three events

The sweep lemma in the commission's strength (commission 202 §4.1: at most three events), in the
block shape of `sweep_lemma` (`HPC/BJ59/Sweep.lean`): blocks of a fixed length `L`, windows `b n`,
`t n`, alternating directions. The hypothesis on events now says that no *four* junctions in
`[lo, hi]` are events. Case 2b of the commission's proof is carried out: after the event at the end
of the down block following `t₀`, the top grows exactly once more before reaching `k − 1` (a further
growth would be a fourth event), the up block after that growth ends at `k − 1`, and the down
block after it ends at the bottom `h + 1` (a growth of the bottom in between would be a fourth
event).
-/

namespace HPC.BJ59

open HPC.Fold

/-- Case 2b of the sweep lemma, on the windows alone (commission 202 §4.1). After an up block `n`
whose junction with block `n + 1` raises the bottom from `h` to `h + 1`, if the top must reach
`k ≥ t n + 2` by block `n₂` and no four junctions in `[n + 1, n₂]` are events, then there is an up
block `p > n + 1`, with `p + 2 ≤ n₂`, ending at the top `k − 1`, followed by a down block with
bottom `h + 1`. -/
theorem sweep_window_case2b (b t : ℤ → ℤ) (up : ℤ → Prop)
    (halt : ∀ n, up (n + 1) ↔ ¬ up n)
    (hwin_up : ∀ n, up n → t (n + 1) = t n ∧ (b (n + 1) = b n ∨ b (n + 1) = b n + 1))
    (hwin_down : ∀ n, ¬ up n → b (n + 1) = b n ∧ (t (n + 1) = t n ∨ t (n + 1) = t n + 1))
    {n n₂ h k : ℤ} (hupn : up n) (hbn : b n = h) (hb1 : b (n + 1) = b n + 1)
    (hk : t n + 2 ≤ k) (htn2 : k ≤ t n₂) (hn12 : n + 2 ≤ n₂)
    (hev : ∀ m₁ m₂ m₃ m₄ : ℤ, m₁ < m₂ → m₂ < m₃ → m₃ < m₄ → n + 1 ≤ m₁ → m₄ ≤ n₂ →
      (b m₁ ≠ b (m₁ - 1) ∨ t m₁ ≠ t (m₁ - 1)) → (b m₂ ≠ b (m₂ - 1) ∨ t m₂ ≠ t (m₂ - 1)) →
      (b m₃ ≠ b (m₃ - 1) ∨ t m₃ ≠ t (m₃ - 1)) → (b m₄ ≠ b (m₄ - 1) ∨ t m₄ ≠ t (m₄ - 1)) →
      False) :
    ∃ p, n + 1 < p ∧ p + 2 ≤ n₂ ∧ up p ∧ t p = k - 1 ∧ b (p + 1) = h + 1 := by
  have tmono1 : ∀ m, t m ≤ t (m + 1) := by
    intro m
    by_cases hu : up m
    · have := (hwin_up m hu).1; omega
    · have := (hwin_down m hu).2; omega
  have bmono1 : ∀ m, b m ≤ b (m + 1) := by
    intro m
    by_cases hu : up m
    · have := (hwin_up m hu).2; omega
    · have := (hwin_down m hu).1; omega
  have mono : ∀ f : ℤ → ℤ, (∀ m, f m ≤ f (m + 1)) → ∀ a c, a ≤ c → f a ≤ f c := by
    intro f hf a c hac
    induction c, hac using Int.le_induction with
    | base => exact le_rfl
    | succ c _ ih => exact ih.trans (hf c)
  have tstep : ∀ m, t m ≤ t (m - 1) + 1 := by
    intro m
    have e : m = m - 1 + 1 := by ring
    by_cases hu : up (m - 1)
    · have := (hwin_up (m - 1) hu).1; rw [← e] at this; omega
    · have := (hwin_down (m - 1) hu).2; rw [← e] at this; omega
  have ht1 : t (n + 1) = t n := (hwin_up n hupn).1
  obtain ⟨p1, q1, q2, q3, q4⟩ := exists_first_growth t tmono1
    (show n + 1 ≤ n₂ by omega) (by omega)
  have tst := tstep p1
  have htp1 : t p1 = t n + 1 := by omega
  obtain ⟨p2, r1, r2, r3, r4⟩ := exists_first_growth t tmono1
    (show p1 ≤ n₂ by omega) (by omega)
  have ev1 : b (n + 1) ≠ b (n + 1 - 1) ∨ t (n + 1) ≠ t (n + 1 - 1) := by
    left; simp; omega
  have ev2 : b p1 ≠ b (p1 - 1) ∨ t p1 ≠ t (p1 - 1) := by right; omega
  have tp2 := mono t tmono1 p1 (p2 - 1) (by omega)
  have ev3 : b p2 ≠ b (p2 - 1) ∨ t p2 ≠ t (p2 - 1) := by right; omega
  have hk' : k - 1 = t n + 1 := by
    by_contra hne
    have tst2 := tstep p2
    obtain ⟨p3, s1, s2, s3, s4⟩ := exists_first_growth t tmono1
      (show p2 ≤ n₂ by omega) (by omega)
    have tp3 := mono t tmono1 p2 (p3 - 1) (by omega)
    exact hev (n + 1) p1 p2 p3 q1 r1 s1 le_rfl s2 ev1 ev2 ev3 (by right; omega)
  have hdp : ¬ up (p1 - 1) := by
    intro hu
    have := (hwin_up (p1 - 1) hu).1
    rw [show p1 - 1 + 1 = p1 by ring] at this
    omega
  have hup1 : up p1 := by
    have := halt (p1 - 1); rw [show p1 - 1 + 1 = p1 by ring] at this; exact this.mpr hdp
  have hbp1 : b p1 = b (p1 - 1) := by
    have := (hwin_down (p1 - 1) hdp).1
    rwa [show p1 - 1 + 1 = p1 by ring] at this
  have hp12 : p1 + 2 ≤ p2 := by
    by_contra hc
    have e : p2 = p1 + 1 := by omega
    have := (hwin_up p1 hup1).1
    rw [← e] at this
    omega
  have hle := mono b bmono1 (n + 1) (p1 + 1) (by omega)
  have hbq : b (p1 + 1) = h + 1 := by
    by_contra hne
    obtain ⟨m, w1, w2, w3, w4⟩ := exists_first_growth b bmono1
      (show n + 1 ≤ p1 + 1 by omega) (by omega)
    have evm : b m ≠ b (m - 1) ∨ t m ≠ t (m - 1) := by left; omega
    have hmp : m ≠ p1 := by
      intro e; subst e; omega
    rcases lt_or_gt_of_ne hmp with hm | hm
    · exact hev (n + 1) m p1 p2 w1 hm r1 le_rfl r2 ev1 evm ev2 ev3
    · exact hev (n + 1) p1 m p2 q1 hm (by omega) le_rfl r2 ev1 ev2 evm ev3
  exact ⟨p1, q1, by omega, hup1, by omega, hbq⟩

/-- **The sweep lemma, at most three events** (commission 202 §4.1). As `sweep_lemma`, with the
hypothesis on events weakened: no four junctions in `[lo, hi]` are events. -/
theorem sweep_lemma3 (g : ℤ → ℤ) (L : ℤ) (hL : 0 < L) (b t : ℤ → ℤ) (up : ℤ → Prop)
    [DecidablePred up]
    (hstep : ∀ u, |g (u + 1) - g u| ≤ 1)
    (hrange : ∀ n u, n * L ≤ u → u ≤ (n + 1) * L → b n ≤ g u ∧ g u ≤ t n)
    (hend : ∀ n, g ((n + 1) * L) = if up n then t n else b n)
    (hcrook : ∀ n, PatCrookedOnZ g (n * L) ((n + 1) * L))
    (halt : ∀ n, up (n + 1) ↔ ¬ up n)
    (hwin_up : ∀ n, up n → t (n + 1) = t n ∧ (b (n + 1) = b n ∨ b (n + 1) = b n + 1))
    (hwin_down : ∀ n, ¬ up n → b (n + 1) = b n ∧ (t (n + 1) = t n ∨ t (n + 1) = t n + 1))
    {lo hi : ℤ}
    (hev : ∀ m₁ m₂ m₃ m₄ : ℤ, m₁ < m₂ → m₂ < m₃ → m₃ < m₄ → lo ≤ m₁ * L → m₄ * L ≤ hi →
      (b m₁ ≠ b (m₁ - 1) ∨ t m₁ ≠ t (m₁ - 1)) → (b m₂ ≠ b (m₂ - 1) ∨ t m₂ ≠ t (m₂ - 1)) →
      (b m₃ ≠ b (m₃ - 1) ∨ t m₃ ≠ t (m₃ - 1)) → (b m₄ ≠ b (m₄ - 1) ∨ t m₄ ≠ t (m₄ - 1)) →
      False) :
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
      · push_neg at c3
        set n₂ := s₀ / L with hn₂
        obtain ⟨m1, m2⟩ := blk s₀
        rw [← hn₂] at m1 m2
        have htn2 : k ≤ t n₂ := le_trans b3 (hrange n₂ s₀ m1 m2.le).2
        have hn12 : n + 1 + 1 ≤ n₂ := by
          by_contra hc; push_neg at hc
          have : (n₂ + 1) * L ≤ (n + 1 + 1) * L := by nlinarith
          omega
        have hmulL : ∀ a c : ℤ, a ≤ c → a * L ≤ c * L := fun a c hac =>
          mul_le_mul_of_nonneg_right hac hL.le
        obtain ⟨p, hp1, hp2, hupp, htp, hbp⟩ := sweep_window_case2b b t up halt hwin_up hwin_down
          hupn hbh hb1 (by omega) htn2 (by omega) (fun m₁ m₂ m₃ m₄ h12 h23 h34 hm1 hm4 =>
            hev m₁ m₂ m₃ m₄ h12 h23 h34 (by have := hmulL _ _ hm1; omega)
              (by have := hmulL _ _ hm4; omega))
        have hdp1 : ¬ up (p + 1) := by rw [halt]; simpa using hupp
        have hr : g ((p + 1) * L) = k - 1 := by rw [hend p, if_pos hupp]; omega
        have hs : g ((p + 1 + 1) * L) = h + 1 := by rw [hend (p + 1), if_neg hdp1]; omega
        refine ⟨(p + 1) * L, (p + 1 + 1) * L, ?_, ?_, ?_, hr, hs⟩
        · have := hmulL (n + 1) p hp1.le
          have : p * L < (p + 1) * L := by linarith
          omega
        · linarith
        · have := hmulL (p + 1 + 1) n₂ (by omega)
          rcases eq_or_lt_of_le (show (p + 1 + 1) * L ≤ s₀ by omega) with e | e
          · rw [e] at hs; omega
          · exact e
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
