import HPC.Fold.Lift82

/-!
# Lifting a crooked chain onto Bing's pattern: the induction

Batch 82. `lift_exists` (see `HPC.Fold.Lift82` for the vocabulary).
-/

namespace HPC.Fold

open Classical

/-- The statement proved by induction on `d`. -/
def LiftStmt (d : ℕ) : Prop :=
  ∀ (n : ℕ) (K M : ℕ → Set ℤ), IsProfile n K M → ∀ (a : ℤ) (t0 t1 : ℕ), t0 ≤ t1 → t1 < n →
    a ∈ M t0 → Band M a d t0 t1 →
    ∃ β, IsLift K M (fun u => a + bingF d u) (z d) t0 t1 β ∧ β t0 ≤ 1

/-- A link in the band has a containing level in the band. -/
theorem exists_K_band {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) {a : ℤ} {d t0 t1 : ℕ}
    (hb : Band M a d t0 t1) {t : ℕ} (ht0 : t0 ≤ t) (ht1 : t ≤ t1) (htn : t < n) :
    ∃ x ∈ K t, a ≤ x ∧ x ≤ a + d := by
  obtain ⟨x, hx⟩ := hP.ne t htn
  exact ⟨x, hx, hb t ht0 ht1 x (hP.sub t htn hx)⟩

theorem liftStmt_zero : LiftStmt 0 := by
  intro n K M hP a t0 t1 h01 ht1 ha hb
  refine ⟨fun _ => 0, ⟨fun t ht0 ht1' => ?_, fun t _ _ => by dsimp only; omega⟩, by dsimp only; omega⟩
  obtain ⟨x, hx, hx1, hx2⟩ := exists_K_band hP hb ht0 ht1' (by omega)
  refine ⟨z_pos 0, ?_, fun h hh => ?_⟩
  · have : x = a := by push_cast at hx2; omega
    simpa [bingF, this] using hx
  · have := hb t ht0 ht1' h hh
    left; simp only [bingF]; push_cast at this; omega

theorem liftStmt_one : LiftStmt 1 := by
  intro n K M hP a t0 t1 h01 ht1 ha hb
  have hz : z 1 = 2 := rfl
  refine ⟨fun t => if a ∈ K t then 0 else 1, ⟨fun t ht0 ht1' => ?_, fun t _ _ => by
    dsimp only; constructor <;> split_ifs <;> omega⟩, by dsimp only; split_ifs <;> omega⟩
  obtain ⟨x, hx, hx1, hx2⟩ := exists_K_band hP hb ht0 ht1' (by omega)
  have hband := hb t ht0 ht1'
  by_cases hK : a ∈ K t
  · simp only [hK, if_true]
    refine ⟨by omega, by simpa [bingF] using hK, fun h hh => ?_⟩
    have := hband h hh
    push_cast at this
    rcases (show h = a ∨ h = a + 1 by omega) with e | e
    · left; simp [bingF, e]
    · right; right; exact ⟨by omega, by simp [bingF, e]⟩
  · simp only [hK, if_false]
    have hx' : x = a + 1 := by
      push_cast at hx2
      rcases (show x = a ∨ x = a + 1 by omega) with e | e
      · exact absurd (e ▸ hx) hK
      · exact e
    refine ⟨by omega, by simpa [bingF, hx'] using hx, fun h hh => ?_⟩
    have := hband h hh
    push_cast at this
    rcases (show h = a ∨ h = a + 1 by omega) with e | e
    · right; left; exact ⟨by omega, by simp [bingF, e]⟩
    · left; simp [bingF, e]

theorem liftStmt_two : LiftStmt 2 := by
  intro n K M hP a t0 t1 h01 ht1 ha hb
  have hz : z 2 = 3 := rfl
  -- the position of a link
  let β : ℕ → ℕ := fun t => if a + 1 ∈ K t then 1 else if a ∈ K t then 0 else 2
  have hβ2 : ∀ t, t0 ≤ t → t ≤ t1 → β t = 2 → a + 2 ∈ K t := by
    intro t ht0 ht1' he
    obtain ⟨x, hx, hx1, hx2⟩ := exists_K_band hP hb ht0 ht1' (by omega)
    by_cases h1 : a + 1 ∈ K t
    · simp [β, h1] at he
    by_cases h2 : a ∈ K t
    · simp [β, h1, h2] at he
    push_cast at hx2
    rcases (show x = a ∨ x = a + 1 ∨ x = a + 2 by omega) with e | e | e
    · exact absurd (e ▸ hx) h2
    · exact absurd (e ▸ hx) h1
    · exact e ▸ hx
  have hβ0 : ∀ t, β t = 0 → a ∈ K t := by
    intro t he
    by_cases h1 : a + 1 ∈ K t
    · simp [β, h1] at he
    by_cases h2 : a ∈ K t
    · exact h2
    · simp [β, h1, h2] at he
  have hβle : ∀ t, β t ≤ 2 := fun t => by simp only [β]; split_ifs <;> omega
  refine ⟨β, ⟨fun t ht0 ht1' => ?_, fun t ht0 ht1' => ?_⟩, ?_⟩
  · have hband := hb t ht0 ht1'
    have htn : t < n := by omega
    by_cases h1 : a + 1 ∈ K t
    · have : β t = 1 := by simp [β, h1]
      rw [this]
      refine ⟨by omega, by simpa [bingF] using h1, fun h hh => ?_⟩
      have := hband h hh
      push_cast at this
      rcases (show h = a ∨ h = a + 1 ∨ h = a + 2 by omega) with e | e | e
      · right; left; exact ⟨by omega, by simp [bingF, e]⟩
      · left; simp [bingF, e]
      · right; right; exact ⟨by omega, by simp [bingF, e]⟩
    by_cases h0 : a ∈ K t
    · have : β t = 0 := by simp [β, h1, h0]
      rw [this]
      refine ⟨by omega, by simpa [bingF] using h0, fun h hh => ?_⟩
      have := hband h hh
      have hn := hP.near t htn a h0 h hh
      push_cast at this
      rcases (show h = a ∨ h = a + 1 by omega) with e | e
      · left; simp [bingF, e]
      · right; right; exact ⟨by omega, by simp [bingF, e]⟩
    · have hb2 : β t = 2 := by simp [β, h1, h0]
      have hK2 := hβ2 t ht0 ht1' hb2
      rw [hb2]
      refine ⟨by omega, by simpa [bingF] using hK2, fun h hh => ?_⟩
      have := hband h hh
      have hn := hP.near t htn _ hK2 h hh
      push_cast at this
      rcases (show h = a + 1 ∨ h = a + 2 by omega) with e | e
      · right; left; exact ⟨by omega, by simp [bingF, e]⟩
      · left; simp [bingF, e]
  · have hs := hβle t
    have hs' := hβle (t + 1)
    constructor
    · by_contra hc
      have e1 : β t = 0 := by omega
      have e2 : β (t + 1) = 2 := by omega
      have := hP.adj t (by omega) _ (hβ0 t e1) _ (hβ2 (t + 1) (by omega) (by omega) e2)
      omega
    · by_contra hc
      have e1 : β (t + 1) = 0 := by omega
      have e2 : β t = 2 := by omega
      have := hP.adj t (by omega) _ (hβ2 t ht0 (by omega) e2) _ (hβ0 (t + 1) e1)
      omega
  · by_contra hc
    have hb2 : β t0 = 2 := by have := hβle t0; omega
    have hK2 := hβ2 t0 le_rfl h01 hb2
    have := hP.near t0 (by omega) _ hK2 a ha
    omega

/-- The inductive step. -/
theorem liftStmt_step (d : ℕ) (hA : LiftStmt (d + 2)) (hB : LiftStmt (d + 1))
    (n : ℕ) (K M : ℕ → Set ℤ) (hP : IsProfile n K M) (a : ℤ) (t0 t1 : ℕ) (h01 : t0 ≤ t1)
    (ht1 : t1 < n) (ha : a ∈ M t0) (hband : Band M a (d + 3) t0 t1)
    (IH : ∀ (K M : ℕ → Set ℤ), IsProfile n K M → ∀ (a : ℤ) (s0 : ℕ), t0 < s0 → s0 ≤ t1 →
      a ∈ M s0 → Band M a (d + 3) s0 t1 →
      ∃ β, IsLift K M (fun u => a + bingF (d + 3) u) (z (d + 3)) s0 t1 β ∧ β s0 ≤ 1) :
    ∃ β, IsLift K M (fun u => a + bingF (d + 3) u) (z (d + 3)) t0 t1 β ∧ β t0 ≤ 1 := by
  have hA3 := z_three_le (d + 2) (by omega)
  have hB2 := z_two_le (d + 1) (by omega)
  have hz := z_succ3 d
  set b : ℤ := a + ((d + 3 : ℕ) : ℤ) with hb_def
  have hbA : a + ((d + 2 : ℕ) : ℤ) = b - 1 := by rw [hb_def]; push_cast; ring
  -- the pieces of the pattern
  have eA : ∀ v < z (d + 2), a + bingF (d + 2) v = a + bingF (d + 3) (0 + v) := fun v hv => by
    rw [zero_add, bingF_A d v hv]
  have eB : ∀ v < z (d + 1), (b - 1) - bingF (d + 1) v = a + bingF (d + 3) (z (d + 2) - 1 + v) := fun v hv => by
    rw [bingF_B d (z (d + 2) - 1 + v) (by omega) (by omega), show z (d + 2) - 1 + v - (z (d + 2) - 1) = v by omega,
      hb_def]; push_cast; ring
  have eC : ∀ v < z (d + 2), (a + 1) + bingF (d + 2) v = a + bingF (d + 3) (z (d + 2) + z (d + 1) - 2 + v) :=
    fun v hv => by
      rw [bingF_C d (z (d + 2) + z (d + 1) - 2 + v) (by omega), show z (d + 2) + z (d + 1) - 2 + v - (z (d + 2) + z (d + 1) - 2) = v by
        omega]; ring
  have eT : ∀ v < z (d + 3), b - bingF (d + 3) v = a + bingF (d + 3) (z (d + 3) - 1 - v) :=
    fun v hv => by rw [bingF_rev (d + 3) v hv, hb_def]; ring
  by_cases hτ : ∃ t, t0 ≤ t ∧ t ≤ t1 ∧ b ∈ M t
  swap
  · -- the top level is never met: the first piece suffices
    push_neg at hτ
    have hbandA : Band M a (d + 2) t0 t1 := fun t ht0 ht1' h hh => by
      have h1 := hband t ht0 ht1' h hh
      have h2 : h ≠ b := fun e => hτ t ht0 ht1' (e ▸ hh)
      rw [hb_def] at h2; push_cast at h1 h2 ⊢; omega
    obtain ⟨β, hl, h0⟩ := hA n K M hP a t0 t1 h01 ht1 ha hbandA
    exact ⟨fun t => 0 + β t, hl.embed eA (by omega), by dsimp only; omega⟩
  -- the first time the top level is met
  set τ := Nat.find hτ with hτ_def
  obtain ⟨hτ0, hτ1, hτb⟩ := Nat.find_spec hτ
  have noTop : ∀ t, t0 ≤ t → t < τ → b ∉ M t := fun t ht0 htτ hbt =>
    Nat.find_min hτ htτ ⟨ht0, by omega, hbt⟩
  have hτn : τ < n := by omega
  have far : ∀ t < n, a ∈ M t → b ∈ M t → False := fun t ht h1 h2 => by
    obtain ⟨x, hx⟩ := hP.ne t ht
    have := hP.near t ht x hx a h1
    have := hP.near t ht x hx b h2
    rw [hb_def] at *; push_cast at *; omega
  have hτ0' : t0 < τ := by
    rcases Nat.lt_or_ge t0 τ with h | h
    · exact h
    · exfalso; exact far t0 (by omega) ha (by rw [show t0 = τ by omega]; exact hτb)
  -- Bing's decomposition `D(r, s)`
  obtain ⟨r0, s0, hrs0, hr0, hs0⟩ := hP.crook t0 (by omega) τ hτn a b ha hτb
    (by rw [hb_def]; push_cast; omega)
  have hrs0' : t0 < r0 ∧ r0 < s0 ∧ s0 < τ := by unfold NBetween at hrs0; omega
  let Ps : ℕ → Prop := fun s => a + 1 ∈ K s ∧ ∃ r, t0 < r ∧ r < s ∧ b - 1 ∈ K r
  set ss := Nat.findGreatest Ps (τ - 1) with hss_def
  have hssP : Ps ss := Nat.findGreatest_spec (m := s0) (by omega) ⟨hs0, r0, hrs0'.1, hrs0'.2.1, hr0⟩
  have hss_le : ss ≤ τ - 1 := Nat.findGreatest_le _
  have hss_max : ∀ s', ss < s' → s' ≤ τ - 1 → ¬ Ps s' := fun s' h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  obtain ⟨hssK, r1, hr1a, hr1b, hr1K⟩ := hssP
  let Pr : ℕ → Prop := fun r => t0 < r ∧ b - 1 ∈ K r
  set rr := Nat.findGreatest Pr (ss - 1) with hrr_def
  have hrrP : Pr rr := Nat.findGreatest_spec (m := r1) (by omega) ⟨hr1a, hr1K⟩
  have hrr_le : rr ≤ ss - 1 := Nat.findGreatest_le _
  have hrr_max : ∀ r', rr < r' → r' ≤ ss - 1 → ¬ Pr r' := fun r' h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  obtain ⟨hrr0, hrrK⟩ := hrrP
  -- the bottom level is not met on `[rr, τ]`
  have noLow : ∀ t, rr ≤ t → t ≤ τ → a ∉ M t := by
    intro t ht1' ht2 hat
    rcases Nat.lt_or_ge t τ with htτ | htτ
    · rcases Nat.lt_or_ge rr t with hrt | hrt
      · obtain ⟨r', s', hb', hr', hs'⟩ := hP.crook t (by omega) τ hτn a b hat hτb
          (by rw [hb_def]; push_cast; omega)
        have hb'' : t < r' ∧ r' < s' ∧ s' < τ := by unfold NBetween at hb'; omega
        rcases Nat.lt_or_ge r' ss with h | h
        · exact hrr_max r' (by omega) (by omega) ⟨by omega, hr'⟩
        · exact hss_max s' (by omega) (by omega) ⟨hs', rr, by omega, by omega, hrrK⟩
      · have e : t = rr := by omega
        rw [e] at hat
        have := hP.near rr (by omega) _ hrrK a hat
        rw [hb_def] at this; push_cast at this; omega
    · exact far t (by omega) hat (by rw [show t = τ by omega]; exact hτb)
  -- segment A: `[t0, rr]`, the first piece
  have bandA : Band M a (d + 2) t0 rr := fun t ht0 ht1' h hh => by
    have h1 := hband t ht0 (by omega) h hh
    have h2 : h ≠ b := fun e => noTop t ht0 (by omega) (e ▸ hh)
    rw [hb_def] at h2; push_cast at h1 h2 ⊢; omega
  obtain ⟨βA, hlA, hA0⟩ := hA n K M hP a t0 rr (by omega) (by omega) ha bandA
  have hlA' := hlA.adjust_end hP (by rw [hbA]; exact hrrK) bandA (by omega) (by omega)
  have L1 := hlA'.embed (g := fun u => a + bingF (d + 3) u) (L := z (d + 3)) (o := 0) eA (by omega)
  -- segment B: `[rr, ss]`, the reflected middle piece
  have bandB : Band (fun t => negSet (M t)) (-(b - 1)) (d + 1) rr ss := fun t ht0 ht1' h hh => by
    have hh' : -h ∈ M t := hh
    have h1 := hband t (by omega) (by omega) _ hh'
    have h2 : -h ≠ b := fun e => noTop t (by omega) (by omega) (e ▸ hh')
    have h3 : -h ≠ a := fun e => noLow t ht0 (by omega) (e ▸ hh')
    rw [hb_def] at h2 ⊢; push_cast at h1 h2 ⊢; omega
  have hPn := hP.neg
  obtain ⟨βB, hlB, hB0⟩ := hB n _ _ hPn (-(b - 1)) rr ss (by omega) (by omega)
    (show -(-(b - 1)) ∈ M rr by rw [neg_neg]; exact hP.sub rr (by omega) hrrK) bandB
  have hlB1 := hlB.adjust_start hPn hB0 (show -(-(b - 1)) ∈ K rr by rw [neg_neg]; exact hrrK)
    bandB (by omega) (by omega)
  have hlB2 := hlB1.adjust_end hPn
    (show -(-(b - 1) + ((d + 1 : ℕ) : ℤ)) ∈ K ss by
      rw [hb_def]; push_cast
      rw [show -(-(a + ((d : ℤ) + 3) - 1) + ((d : ℤ) + 1)) = a + 1 by ring]; exact hssK)
    bandB (by omega) (by omega)
  have L2 := (hlB2.of_neg (c := b - 1)).embed (g := fun u => a + bingF (d + 3) u) (L := z (d + 3)) (o := z (d + 2) - 1) eB (by omega)
  -- segment C: `[ss, τ]`, the last piece
  have bandC : Band M (a + 1) (d + 2) ss τ := fun t ht0 ht1' h hh => by
    have h1 := hband t (by omega) (by omega) h hh
    have h3 : h ≠ a := fun e => noLow t (by omega) ht1' (e ▸ hh)
    push_cast at h1 ⊢; omega
  obtain ⟨βC, hlC, hC0⟩ := hA n K M hP (a + 1) ss τ (by omega) hτn (hP.sub ss (by omega) hssK)
    bandC
  have hlC1 := hlC.adjust_start hP hC0 hssK bandC hτn (by omega)
  have L3 := hlC1.embed (g := fun u => a + bingF (d + 3) u) (L := z (d + 3)) (o := z (d + 2) + z (d + 1) - 2) eC (by omega)
  -- segment T: `[τ, t1]`, the rest, read from the top
  have bandT : Band (fun t => negSet (M t)) (-b) (d + 3) τ t1 := fun t ht0 ht1' h hh => by
    have hh' : -h ∈ M t := hh
    have h1 := hband t (by omega) ht1' _ hh'
    rw [hb_def]; push_cast at h1 ⊢; omega
  obtain ⟨βT, hlT, hT0⟩ := IH _ _ hPn (-b) τ hτ0' hτ1 (show -(-b) ∈ M τ by rw [neg_neg]; exact hτb)
    bandT
  have L4 := (hlT.of_neg (c := b)).rev (g := fun u => a + bingF (d + 3) u) eT
  -- gluing
  have G1 := L1.glue L2 (by omega) (fun h => by
    have := L2.2 rr le_rfl h
    simp only [show rr ≠ ss by omega, if_false, if_true] at this ⊢
    constructor <;> omega)
  have G2 := G1.glue L3 (by omega) (fun h => by
    have := L3.2 ss le_rfl h
    simp only [show ¬ ss ≤ rr by omega, if_false, if_true] at this ⊢
    constructor <;> omega)
  refine ⟨_, G2.glue L4 (by omega) (fun h => ?_), ?_⟩
  · have hc3 := L3.1 τ (by omega) le_rfl
    have hhigh := compat_high hc3 hτb
    have hlt3 := hc3.1
    have hl4 := L4.2 τ le_rfl h
    have hc4 := L4.1 (τ + 1) (by omega) h
    have hlt4 := hc4.1
    simp only [show ¬ τ ≤ ss by omega, show ¬ τ ≤ rr by omega, if_false]
      at hl4 hhigh hlt3 hlt4 ⊢
    refine ⟨by omega, ?_⟩
    by_contra hcon
    have e3 : z (d + 2) + z (d + 1) - 2 + (if τ = ss then 0 else βC τ) = z (d + 3) - 1 := by
      omega
    have e4 : z (d + 3) - 1 - βT (τ + 1) = z (d + 3) - 3 := by omega
    have k3 := hc3.2.1
    have k4 := hc4.2.1
    dsimp only at k3 k4
    rw [e3, bingF_top (d + 3) _ le_rfl] at k3
    rw [e4, bingF_sub_two (d + 3) (by omega)] at k4
    have := hP.adj τ (by omega) _ k3 _ k4
    push_cast at this; omega
  · simp only [show t0 ≤ τ by omega, show t0 ≤ ss by omega, show t0 ≤ rr by omega, if_true,
      show t0 ≠ rr by omega, if_false]
    omega

/-- **The lifting theorem.** A crooked profile meeting level `a` at time `t0` and staying in the
band `[a, a + d]` over `[t0, t1]` lifts onto the pattern `a + bingF d` over `[t0, t1]`, starting at
position `0` or `1`. -/
theorem liftStmt : ∀ d, LiftStmt d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    match d with
    | 0 => exact liftStmt_zero
    | 1 => exact liftStmt_one
    | 2 => exact liftStmt_two
    | d + 3 =>
      intro n K M hP a t0 t1 h01 ht1 ha hband
      -- inner induction on the length of the interval
      suffices H : ∀ N, ∀ (K M : ℕ → Set ℤ), IsProfile n K M → ∀ (a : ℤ) (s0 : ℕ), s0 ≤ t1 →
          t1 - s0 ≤ N → a ∈ M s0 → Band M a (d + 3) s0 t1 →
          ∃ β, IsLift K M (fun u => a + bingF (d + 3) u) (z (d + 3)) s0 t1 β ∧ β s0 ≤ 1 from
        H (t1 - t0) K M hP a t0 h01 le_rfl ha hband
      intro N
      induction N with
      | zero =>
        intro K M hP a s0 hs0 hN ha hband
        exact liftStmt_step d (ihd _ (by omega)) (ihd _ (by omega)) n K M hP a s0 t1 hs0 ht1 ha
          hband (fun K' M' hP' a' s' hs' hs'' _ _ => by omega)
      | succ N ihN =>
        intro K M hP a s0 hs0 hN ha hband
        exact liftStmt_step d (ihd _ (by omega)) (ihd _ (by omega)) n K M hP a s0 t1 hs0 ht1 ha
          hband (fun K' M' hP' a' s' hs' hs'' ha' hb' =>
            ihN K' M' hP' a' s' hs'' (by omega) ha' hb')

end HPC.Fold
