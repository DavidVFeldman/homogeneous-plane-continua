import HPC.Fold.BingCrook

/-!
# Lifting a crooked chain onto Bing's pattern

Batch 82. The combinatorial core of Theorem 7. A fine chain crooked in a coarse chain is recorded
by two sequences of level sets: `K t`, the coarse links containing fine link `t`, and `M t`, the
coarse links it meets (`IsProfile`). A *lift* onto a pattern `g` of length `L` assigns to each fine
link a position `β t < L` such that consecutive positions differ by at most one, fine link `t`
lies in the coarse link `g (β t)`, and every coarse link it meets is the level of `β t` or of a
neighbouring position (`Compat`). The last clause is what makes the resulting consolidation
crooked.

`lift_exists`: a crooked profile which meets level `a` at time `t0` and stays in the band
`[a, a + d]` on `[t0, t1]` lifts onto `a + bingF d` over `[t0, t1]`, starting at position `0` or `1`.
The proof is Bing's induction on `d` (the three pieces of the pattern), with an inner induction on
the length of the time interval for the phases after the top level is first met.
-/

namespace HPC.Fold

/-- The abstract record of a fine chain crooked in a coarse one, over times `t < n`. -/
structure IsProfile (n : ℕ) (K M : ℕ → Set ℤ) : Prop where
  ne : ∀ t < n, (K t).Nonempty
  sub : ∀ t < n, K t ⊆ M t
  near : ∀ t < n, ∀ a ∈ K t, ∀ h ∈ M t, a ≤ h + 1 ∧ h ≤ a + 1
  adj : ∀ t, t + 1 < n → ∀ a ∈ K t, ∀ b ∈ K (t + 1), a ≤ b + 1 ∧ b ≤ a + 1
  adjM : ∀ t, t + 1 < n → K (t + 1) ⊆ M t ∧ K t ⊆ M (t + 1)
  crook : ∀ i < n, ∀ j < n, ∀ h k : ℤ, h ∈ M i → k ∈ M j → h + 3 ≤ k →
    ∃ r s, NBetween i r s j ∧ k - 1 ∈ K r ∧ h + 1 ∈ K s

/-- Negating all levels. -/
def negSet (S : Set ℤ) : Set ℤ := {x | -x ∈ S}

@[simp] theorem mem_negSet {S : Set ℤ} {x : ℤ} : x ∈ negSet S ↔ -x ∈ S := Iff.rfl

theorem IsProfile.neg {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) :
    IsProfile n (fun t => negSet (K t)) (fun t => negSet (M t)) where
  ne t ht := by
    obtain ⟨x, hx⟩ := hP.ne t ht
    exact ⟨-x, by simpa using hx⟩
  sub t ht x hx := hP.sub t ht hx
  near t ht a ha h hh := by
    have := hP.near t ht (-a) ha (-h) hh
    constructor <;> linarith [this.1, this.2]
  adj t ht a ha b hb := by
    have := hP.adj t ht (-a) ha (-b) hb
    constructor <;> linarith [this.1, this.2]
  adjM t ht := ⟨fun x hx => (hP.adjM t ht).1 hx, fun x hx => (hP.adjM t ht).2 hx⟩
  crook i hi j hj h k hh hk hhk := by
    obtain ⟨r, s, hb, hr, hs⟩ := hP.crook j hj i hi (-k) (-h) hk hh (by linarith)
    refine ⟨s, r, hb.symm, ?_, ?_⟩
    · show -(k - 1) ∈ K s; rw [show -(k - 1) = -k + 1 by ring]; exact hs
    · show -(h + 1) ∈ K r; rw [show -(h + 1) = -h - 1 by ring]; exact hr

/-- Position `u` of the pattern `g` (of length `L`) can carry fine link `t`. -/
def Compat (K M : ℕ → Set ℤ) (g : ℕ → ℤ) (L t u : ℕ) : Prop :=
  u < L ∧ g u ∈ K t ∧ ∀ h ∈ M t, h = g u ∨ (0 < u ∧ h = g (u - 1)) ∨ (u + 1 < L ∧ h = g (u + 1))

/-- A lift over the time interval `[t0, t1]`. -/
def IsLift (K M : ℕ → Set ℤ) (g : ℕ → ℤ) (L t0 t1 : ℕ) (β : ℕ → ℕ) : Prop :=
  (∀ t, t0 ≤ t → t ≤ t1 → Compat K M g L t (β t)) ∧
  (∀ t, t0 ≤ t → t < t1 → β (t + 1) ≤ β t + 1 ∧ β t ≤ β (t + 1) + 1)

/-- Embedding a lift onto a piece `g' = g (o + ·)` of a pattern. -/
theorem Compat.embed {K M : ℕ → Set ℤ} {g g' : ℕ → ℤ} {L L' o t u : ℕ}
    (hc : Compat K M g' L' t u) (he : ∀ v < L', g' v = g (o + v)) (hL : o + L' ≤ L) :
    Compat K M g L t (o + u) := by
  obtain ⟨hu, hk, hm⟩ := hc
  refine ⟨by omega, by rw [← he u hu]; exact hk, fun h hh => ?_⟩
  rcases hm h hh with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; rw [h1, he u hu]
  · right; left; refine ⟨by omega, ?_⟩
    rw [h1, he (u - 1) (by omega)]; congr 1; omega
  · right; right; refine ⟨by omega, ?_⟩
    rw [h1, he (u + 1) h0]; congr 1

theorem IsLift.embed {K M : ℕ → Set ℤ} {g g' : ℕ → ℤ} {L L' o t0 t1 : ℕ} {β : ℕ → ℕ}
    (hl : IsLift K M g' L' t0 t1 β) (he : ∀ v < L', g' v = g (o + v)) (hL : o + L' ≤ L) :
    IsLift K M g L t0 t1 (fun t => o + β t) :=
  ⟨fun t h1 h2 => (hl.1 t h1 h2).embed he hL, fun t h1 h2 => by
    have := hl.2 t h1 h2; dsimp only; constructor <;> omega⟩

/-- Transfer across negation of levels. -/
theorem Compat.of_neg {K M : ℕ → Set ℤ} {f : ℕ → ℤ} {c : ℤ} {L t u : ℕ}
    (hc : Compat (fun t => negSet (K t)) (fun t => negSet (M t)) (fun u => -c + f u) L t u) :
    Compat K M (fun u => c - f u) L t u := by
  obtain ⟨hu, hk, hm⟩ := hc
  refine ⟨hu, ?_, fun h hh => ?_⟩
  · have : -(-c + f u) ∈ K t := hk
    simpa [show -(-c + f u) = c - f u by ring] using this
  · have := hm (-h) (by simpa using hh)
    simp only at this
    rcases this with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left; simp only; linarith
    · right; left; exact ⟨h0, by simp only; linarith⟩
    · right; right; exact ⟨h0, by simp only; linarith⟩

theorem IsLift.of_neg {K M : ℕ → Set ℤ} {f : ℕ → ℤ} {c : ℤ} {L t0 t1 : ℕ} {β : ℕ → ℕ}
    (hl : IsLift (fun t => negSet (K t)) (fun t => negSet (M t)) (fun u => -c + f u) L t0 t1 β) :
    IsLift K M (fun u => c - f u) L t0 t1 β :=
  ⟨fun t h1 h2 => (hl.1 t h1 h2).of_neg, hl.2⟩

/-- Transfer across reading the pattern backwards. -/
theorem Compat.rev {K M : ℕ → Set ℤ} {g g' : ℕ → ℤ} {L t u : ℕ}
    (hc : Compat K M g' L t u) (he : ∀ v < L, g' v = g (L - 1 - v)) :
    Compat K M g L t (L - 1 - u) := by
  obtain ⟨hu, hk, hm⟩ := hc
  refine ⟨by omega, by rw [← he u hu]; exact hk, fun h hh => ?_⟩
  rcases hm h hh with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; rw [h1, he u hu]
  · right; right; refine ⟨by omega, ?_⟩
    rw [h1, he (u - 1) (by omega)]; congr 1; omega
  · right; left; refine ⟨by omega, ?_⟩
    rw [h1, he (u + 1) h0, show L - 1 - (u + 1) = L - 1 - u - 1 by omega]

theorem IsLift.rev {K M : ℕ → Set ℤ} {g g' : ℕ → ℤ} {L t0 t1 : ℕ} {β : ℕ → ℕ}
    (hl : IsLift K M g' L t0 t1 β) (he : ∀ v < L, g' v = g (L - 1 - v)) :
    IsLift K M g L t0 t1 (fun t => L - 1 - β t) :=
  ⟨fun t h1 h2 => (hl.1 t h1 h2).rev he, fun t h1 h2 => by
    have := hl.2 t h1 h2
    have := (hl.1 t h1 (by omega)).1
    have := (hl.1 (t + 1) (by omega) (by omega)).1
    dsimp only; constructor <;> omega⟩

/-- Gluing two lifts at a common time where the second may be overridden by the first. -/
theorem IsLift.glue {K M : ℕ → Set ℤ} {g : ℕ → ℤ} {L t0 t1 t2 : ℕ} {β β' : ℕ → ℕ}
    (h1 : IsLift K M g L t0 t1 β) (h2 : IsLift K M g L t1 t2 β') (h01 : t0 ≤ t1)
    (hj : t1 < t2 → β' (t1 + 1) ≤ β t1 + 1 ∧ β t1 ≤ β' (t1 + 1) + 1) :
    IsLift K M g L t0 t2 (fun t => if t ≤ t1 then β t else β' t) := by
  refine ⟨fun t ht1 ht2 => ?_, fun t ht1 ht2 => ?_⟩
  · by_cases h : t ≤ t1
    · simp only [h, if_true]; exact h1.1 t ht1 h
    · simp only [h, if_false]; exact h2.1 t (by omega) ht2
  · by_cases h : t + 1 ≤ t1
    · simp only [h, show t ≤ t1 by omega, if_true]; exact h1.2 t ht1 (by omega)
    · by_cases h' : t = t1
      · subst h'; simp only [le_refl, if_true, show ¬ t + 1 ≤ t by omega, if_false]
        exact hj ht2
      · simp only [show ¬ t ≤ t1 by omega, h, if_false]; exact h2.2 t (by omega) ht2

/-- The profile stays in the band `[a, a + d]` over `[t0, t1]`. -/
def Band (M : ℕ → Set ℤ) (a : ℤ) (d t0 t1 : ℕ) : Prop :=
  ∀ t, t0 ≤ t → t ≤ t1 → ∀ h ∈ M t, a ≤ h ∧ h ≤ a + d

theorem Band.mono {M : ℕ → Set ℤ} {a : ℤ} {d t0 t1 s0 s1 : ℕ} (hb : Band M a d t0 t1)
    (h0 : t0 ≤ s0) (h1 : s1 ≤ t1) : Band M a d s0 s1 :=
  fun t ht0 ht1 => hb t (by omega) (by omega)

theorem bingF_sub_one (d : ℕ) (hd : 1 ≤ d) : bingF d (z d - 2) = d - 1 := by
  have := bingF_rev d 1 (by have := z_two_le d hd; omega)
  rw [bingF_one d hd, show z d - 1 - 1 = z d - 2 by omega] at this
  exact this

theorem bingF_sub_two (d : ℕ) (hd : 2 ≤ d) : bingF d (z d - 3) = d - 2 := by
  have := bingF_rev d 2 (by have := z_three_le d hd; omega)
  rw [bingF_two d hd, show z d - 1 - 2 = z d - 3 by omega] at this
  exact this

/-- A position carrying a link that meets the bottom level is `0` or `1`. -/
theorem compat_low {K M : ℕ → Set ℤ} {a : ℤ} {d t u : ℕ}
    (hc : Compat K M (fun u => a + bingF d u) (z d) t u) (ha : a ∈ M t) : u ≤ 1 := by
  obtain ⟨hu, -, hm⟩ := hc
  rcases hm a ha with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have := bingF_eq_zero d u hu (by simp only at h1; linarith); omega
  · have := bingF_eq_zero d (u - 1) (by omega) (by simp only at h1; linarith); omega
  · have := bingF_eq_zero d (u + 1) h0 (by simp only at h1; linarith); omega

/-- A position carrying a link that meets the top level is one of the last two. -/
theorem compat_high {K M : ℕ → Set ℤ} {a : ℤ} {d t u : ℕ}
    (hc : Compat K M (fun u => a + bingF d u) (z d) t u) (hb : a + d ∈ M t) : z d - 2 ≤ u := by
  obtain ⟨hu, -, hm⟩ := hc
  rcases hm (a + d) hb with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have := bingF_eq_top d u (by simp only at h1; linarith); omega
  · have := bingF_eq_top d (u - 1) (by simp only at h1; linarith); omega
  · have := bingF_eq_top d (u + 1) (by simp only at h1; linarith); omega

/-- Moving the first position of a lift to `0` when the first link lies in the bottom level. -/
theorem IsLift.adjust_start {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) {a : ℤ}
    {d t0 t1 : ℕ} {β : ℕ → ℕ} (hl : IsLift K M (fun u => a + bingF d u) (z d) t0 t1 β)
    (h0 : β t0 ≤ 1) (hK : a ∈ K t0) (hband : Band M a d t0 t1) (ht1 : t1 < n) (h01 : t0 ≤ t1) :
    IsLift K M (fun u => a + bingF d u) (z d) t0 t1 (fun t => if t = t0 then 0 else β t) := by
  refine ⟨fun t ht0 ht1' => ?_, fun t ht0 ht1' => ?_⟩
  · by_cases ht : t = t0
    · subst ht
      simp only [if_true]
      refine ⟨z_pos d, by simpa [bingF_zero] using hK, fun h hh => ?_⟩
      have hn := hP.near t (by omega) a hK h hh
      have hb := hband t le_rfl h01 h hh
      rcases (show h = a ∨ h = a + 1 by omega) with e | e
      · left; simp [e, bingF_zero]
      · right; right
        have hd : 1 ≤ d := by
          by_contra hd; push_neg at hd
          have : d = 0 := by omega
          subst this; push_cast at hb; omega
        exact ⟨by have := z_two_le d hd; omega, by simp [e, bingF_one d hd]⟩
    · simp only [ht, if_false]; exact hl.1 t ht0 ht1'
  · by_cases ht : t = t0
    · subst ht
      simp only [if_true, show t + 1 ≠ t by omega, if_false]
      refine ⟨?_, by omega⟩
      have h2 := hl.2 t le_rfl ht1'
      by_contra hc
      have he : β (t + 1) = 2 := by omega
      have hc1 := hl.1 (t + 1) (by omega) ht1'
      rw [he] at hc1
      obtain ⟨hz, hk2, -⟩ := hc1
      have hd : 2 ≤ d := by
        by_contra hd; push_neg at hd
        interval_cases d <;> simp [z] at hz
      dsimp only at hk2
      rw [bingF_two d hd] at hk2
      have := hP.adj t (by omega) a hK _ hk2
      omega
    · simp only [ht, if_false, show t + 1 ≠ t0 by omega]; exact hl.2 t ht0 ht1'

/-- Moving the last position of a lift to the end when the last link lies in the top level. -/
theorem IsLift.adjust_end {n : ℕ} {K M : ℕ → Set ℤ} (hP : IsProfile n K M) {a : ℤ}
    {d t0 t1 : ℕ} {β : ℕ → ℕ} (hl : IsLift K M (fun u => a + bingF d u) (z d) t0 t1 β)
    (hK : a + d ∈ K t1) (hband : Band M a d t0 t1) (ht1 : t1 < n) (h01 : t0 ≤ t1) :
    IsLift K M (fun u => a + bingF d u) (z d) t0 t1
      (fun t => if t = t1 then z d - 1 else β t) := by
  have hzp := z_pos d
  have hhigh : z d - 2 ≤ β t1 := compat_high (hl.1 t1 h01 le_rfl) (hP.sub t1 ht1 hK)
  have hlt : β t1 < z d := (hl.1 t1 h01 le_rfl).1
  refine ⟨fun t ht0 ht1' => ?_, fun t ht0 ht1' => ?_⟩
  · by_cases ht : t = t1
    · subst ht
      simp only [if_true]
      refine ⟨by omega, by simpa [bingF_top d _ le_rfl] using hK, fun h hh => ?_⟩
      have hn := hP.near t ht1 (a + d) hK h hh
      have hb := hband t h01 le_rfl h hh
      rcases (show h = a + d ∨ h = a + d - 1 by omega) with e | e
      · left; simp [e, bingF_top d _ le_rfl]
      · right; left
        have hd : 1 ≤ d := by
          by_contra hd; push_neg at hd
          have : d = 0 := by omega
          subst this; push_cast at hb; omega
        refine ⟨by have := z_two_le d hd; omega, ?_⟩
        dsimp only
        rw [show z d - 1 - 1 = z d - 2 by omega, bingF_sub_one d hd, e]; ring
    · simp only [ht, if_false]; exact hl.1 t ht0 ht1'
  · by_cases ht : t + 1 = t1
    · subst ht
      simp only [if_true, show t ≠ t + 1 by omega, if_false]
      have h2 := hl.2 t ht0 (by omega)
      have hlt' : β t < z d := (hl.1 t ht0 (by omega)).1
      refine ⟨?_, by omega⟩
      by_contra hc
      have he : β t = z d - 3 := by omega
      have hc1 := hl.1 t ht0 (by omega)
      rw [he] at hc1
      obtain ⟨hz, hk2, -⟩ := hc1
      have hd : 2 ≤ d := by
        by_contra hd; push_neg at hd
        interval_cases d <;> simp only [z] at hc <;> omega
      dsimp only at hk2
      rw [bingF_sub_two d hd] at hk2
      have := hP.adj t ht1 _ hk2 _ hK
      push_cast at this; omega
    · simp only [ht, if_false, show t ≠ t1 by omega]; exact hl.2 t ht0 (by omega)

end HPC.Fold
