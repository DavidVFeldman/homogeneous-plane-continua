import HPC.Fold.Mid2FoldG66

/-!
# The second route to a walk: `wb`, where a descent to `L + 1` comes first

`Mid2Fold66` and its mirror give both arms the reflected walk `w3` when the branch hypothesis is
met by its **first** disjunct — a time at `L + 8` before every descent to `L + 1`. This file takes
the other reflected walk, `wb`, and the opposite condition: a descent to `L + 1` before every
ascent to `L + 9`.

`wb`'s ceiling clause at a descent to `L + 1` accepts a landmark at `L + 6`, which is what the
*second* disjunct of `LowAt (L + 1) (L + 8)` offers, so on `wb` the branch hypothesis needs no case
distinction at all: either disjunct supplies that clause. What `wb` asks for instead is its deep
clause at the ascents to `L + 9` — a time at `L + 4` or below, then one at `L + 6` or above, then
one at `L + 2` or below — and a descent to `L + 1` before the ascent supplies its last link, the
branch hypothesis at that descent its middle one, and the landmark of the partner's failure its
first.

So, with the landmark that a failure of `Mid2Floor2` on either arm supplies on both
(`land_ascent_of_mid2fail2`, `land_ascent_armT_of_mid2fail2` and their mirrors):

* `leg4Land_wb_of_land_of_deepFirst` — an arm of the band with the branch hypothesis, with a time
  at `L + 4` or below before each of its own times at `L + 8`, and with a descent to `L + 1` before
  each of its own times at `L + 9`, is served by `wb`;
* `s3_span_nine_mid5_of_mid2fail2_deepFirst` and its mirror — hence at a basepoint of the branch
  where one arm fails `Mid2Floor2` and both arms descend to `L + 1` before they rise to `L + 9`,
  the pair folds onto `wb`;
* `crossMid2_relaxed_of_deepFirst` — equivalently, at such a crossing both arms satisfy
  `Mid2Floor2`.

An arm that never reaches `L + 9` satisfies the hypothesis vacuously. Together with
`crossMid2_relaxed_of_highFirst` this leaves, of the residue and for the relaxed clause, the
*mixed* basepoints: one arm high first and the other low first.

The index gaps are all paid by the timing law, which is packaged here as `ArmSep`: read on an arm,
`k` levels cost `z k - 1` steps, in whichever order the two times come (`armG_armSep`,
`armT_armSep`).
-/
namespace HPC.Fold

/-! ## The timing law read on an arm -/

/-- **The timing law on an arm.** Two times of the arm whose levels differ by `k` are `z k - 1`
steps apart, on whichever side. -/
def ArmSep {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ (k : ℕ) (p q : Fin m), (k : ℤ) ≤ f q - f p → p.val ≠ q.val →
    p.val + z k ≤ q.val + 1 ∨ q.val + z k ≤ p.val + 1

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

theorem armG_armSep (hcr : IsCrookedIvF ρ σ) (i : Fin n) : ArmSep (armG ρ i) := by
  intro k p q hk hne
  have hi := i.isLt
  have hpn := p.isLt
  have hqn := q.isLt
  have hpv : armG ρ i p = ρ ⟨i.val + p.val, by omega⟩ := rfl
  have hqv : armG ρ i q = ρ ⟨i.val + q.val, by omega⟩ := rfl
  have hne' : (⟨i.val + p.val, by omega⟩ : Fin n).val ≠ (⟨i.val + q.val, by omega⟩ : Fin n).val := by
    simp only []
    omega
  rcases ivSep hcr ⟨i.val + p.val, by omega⟩ ⟨i.val + q.val, by omega⟩ hne' k
    (armG ρ i p) (armG ρ i q) (by omega) (le_of_eq hpv) (by rw [hpv]; exact hcr.le _)
    (le_of_eq hqv) (by rw [hqv]; exact hcr.le _) with h | h
  · simp only [] at h; exact Or.inl (by omega)
  · simp only [] at h; exact Or.inr (by omega)

theorem armT_armSep (hcr : IsCrookedIvF ρ σ) (i : Fin n) : ArmSep (armT ρ i) := by
  intro k p q hk hne
  have hi := i.isLt
  have hpn := p.isLt
  have hqn := q.isLt
  have hpv : armT ρ i p = ρ ⟨i.val - p.val, by omega⟩ := rfl
  have hqv : armT ρ i q = ρ ⟨i.val - q.val, by omega⟩ := rfl
  have hne' : (⟨i.val - p.val, by omega⟩ : Fin n).val ≠ (⟨i.val - q.val, by omega⟩ : Fin n).val := by
    simp only []
    omega
  rcases ivSep hcr ⟨i.val - p.val, by omega⟩ ⟨i.val - q.val, by omega⟩ hne' k
    (armT ρ i p) (armT ρ i q) (by omega) (le_of_eq hpv) (by rw [hpv]; exact hcr.le _)
    (le_of_eq hqv) (by rw [hqv]; exact hcr.le _) with h | h
  · simp only [] at h; exact Or.inr (by omega)
  · simp only [] at h; exact Or.inl (by omega)

end Pair

/-! ## `wb` on an arm that descends before it rises to the top -/

/-- **`wb` from the landmark and a descent before each ascent to `L + 9`.** An arm of the band
`[L, L + 9]` based at `L + 5` with the branch hypothesis, with a time at `L + 4` or below before
each of its own times at `L + 8` or above, and with a descent to `L + 1` before each of its own
times at `L + 9`, is served by `wb = L+6 → L+3 → L+7 → L+1 → L+8`. Its ceiling clause accepts
either disjunct of the branch hypothesis, and its deep clause is the descent with the branch
hypothesis read at that descent. An arm that never reaches `L + 9` satisfies the last hypothesis
vacuously. -/
theorem leg4Land_wb_of_land_of_deepFirst {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (hm : 0 < m)
    (hsep : ArmSep f) (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 8))
    (hland : ∀ q : Fin m, L + 8 ≤ f q → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧
      f j ≤ L + 4)
    (hD : ∀ e : Fin m, L + 9 ≤ f e → ∃ d : Fin m, d.val < e.val ∧ f d ≤ L + 1) :
    Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hz3 : z 3 = 6 := by decide
  have hz4 : z 4 = 13 := by decide
  have hz5 : z 5 = 30 := by decide
  have hz7 : z 7 = 170 := by decide
  -- an arm time at `L + 2` or below is at index five or more
  have hlowIdx : ∀ j : Fin m, f j ≤ L + 2 → 5 ≤ j.val := by
    intro j hj
    have hne : j.val ≠ (⟨0, hm⟩ : Fin m).val := by
      intro hc
      have : j = ⟨0, hm⟩ := Fin.ext hc
      rw [this, h0] at hj
      omega
    rcases hsep 3 j ⟨0, hm⟩ (by rw [h0]; push_cast; omega) hne with h | h
    · simp only [] at h; omega
    · simp only [] at h; omega
  -- the chain the ceiling and the deep clause share, at a descent to `L + 1`
  have hchain : ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ k.val ∧
      k.val + 6 ≤ d.val ∧ f j ≤ L + 4 ∧ L + 6 ≤ f k := by
    intro d hd
    rcases hlow d hd with ⟨p, hpd, hp8⟩ | ⟨j, j', hjj', hj'd, hj2, hj'6⟩
    · obtain ⟨j, h1, h2, h3⟩ := hland p hp8
      have hsep7 : p.val + 7 ≤ d.val := by
        have hne : d.val ≠ p.val := by omega
        rcases hsep 7 d p (by omega) hne with h | h
        · omega
        · omega
      exact ⟨j, p, by omega, by omega, by omega, by omega, by omega⟩
    · have h3j : 5 ≤ j.val := hlowIdx j (by omega)
      have hsep4 : j.val + 12 ≤ j'.val := by
        have hne : j.val ≠ j'.val := by omega
        rcases hsep 4 j j' (by omega) hne with h | h
        · omega
        · omega
      have hsep5 : j'.val + 29 ≤ d.val := by
        have hne : d.val ≠ j'.val := by omega
        rcases hsep 5 d j' (by omega) hne with h | h
        · omega
        · omega
      exact ⟨j, j', by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the floor clause: the landmark, with its gap
    intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ f d := by omega
    obtain ⟨j, h1, h2, h3⟩ := hland d hd8
    have := hH d
    exact ⟨j, by omega, by omega, by omega⟩
  · -- the deep clause at the ascents to `L + 9`
    intro e he
    simp only [armRefl_apply] at he ⊢
    have he9 : L + 9 ≤ f e := by omega
    obtain ⟨d, hde, hd1⟩ := hD e he9
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hchain d hd1
    have hsepde : d.val + 169 ≤ e.val := by
      have hne : d.val ≠ e.val := by omega
      rcases hsep 7 d e (by omega) hne with h | h
      · omega
      · omega
    have := hH e
    exact ⟨j, k, d, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- the ceiling clause at the descents to `L + 1`
    intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hdl : f d ≤ L + 1 := by omega
    have hdL : L ≤ f d := hL d
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hchain d hdl
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The fold where both arms descend first -/

section PairFold

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The pair folds onto `wb`.** At a basepoint of the branch whose backward arm fails the relaxed
clause and both of whose arms descend to `L + 1` before they rise to `L + 9`. -/
theorem s3_span_nine_mid5_of_mid2fail2_deepFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hDG : ∀ e : Fin (n - i.val), L + 9 ≤ armG ρ i e →
      ∃ d : Fin (n - i.val), d.val < e.val ∧ armG ρ i d ≤ L + 1)
    (hDT : ∀ e : Fin (i.val + 1), L + 9 ≤ armT ρ i e →
      ∃ d : Fin (i.val + 1), d.val < e.val ∧ armT ρ i d ≤ L + 1)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  refine s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
    (leg4Window_wb L) (by omega) (by omega) ?_ ?_
  · exact leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
      (fun j => hHb _) hG (land_ascent_of_mid2fail2 hcr hlip i L hp hmid) hDG
  · exact leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
      (fun j => hHb _) hT (land_ascent_armT_of_mid2fail2 hcr hlip i L hp hmid) hDT

/-- **The mirror**, with the forward arm as the failing one. -/
theorem s3_span_nine_mid5_of_mid2fail2G_deepFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hDG : ∀ e : Fin (n - i.val), L + 9 ≤ armG ρ i e →
      ∃ d : Fin (n - i.val), d.val < e.val ∧ armG ρ i d ≤ L + 1)
    (hDT : ∀ e : Fin (i.val + 1), L + 9 ≤ armT ρ i e →
      ∃ d : Fin (i.val + 1), d.val < e.val ∧ armT ρ i d ≤ L + 1)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  refine s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
    (leg4Window_wb L) (by omega) (by omega) ?_ ?_
  · exact leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
      (fun j => hHb _) hG (land_ascent_armG_of_mid2fail2G hcr hlip i L hp hmid) hDG
  · exact leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
      (fun j => hHb _) hT (land_ascent_armT_of_mid2fail2G hcr hlip i L hp hmid) hDT

/-- **The residue, on the basepoints that descend before they rise.** At a crossing of the
trichotomy both of whose arms have a descent to `L + 1` before every time at `L + 9`, both arms
satisfy the relaxed clause `Mid2Floor2`. Here no disjunct of the branch hypothesis is preferred:
`wb` accepts both. -/
theorem crossMid2_relaxed_of_deepFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hDG : ∀ e : Fin (n - i.val), L + 9 ≤ armG ρ i e →
      ∃ d : Fin (n - i.val), d.val < e.val ∧ armG ρ i d ≤ L + 1)
    (hDT : ∀ e : Fin (i.val + 1), L + 9 ≤ armT ρ i e →
      ∃ d : Fin (i.val + 1), d.val < e.val ∧ armT ρ i d ≤ L + 1)
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armT ρ i) L ∧ Mid2Floor2 (armG ρ i) L := by
  classical
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  constructor
  · by_contra hmid
    exact hcross.2.2
      ⟨leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
          (fun j => hHb _) hGlow (land_ascent_of_mid2fail2 hcr hlip i L hp hmid) hDG,
        leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
          (fun j => hHb _) hTlow (land_ascent_armT_of_mid2fail2 hcr hlip i L hp hmid) hDT⟩
  · by_contra hmid
    exact hcross.2.2
      ⟨leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
          (fun j => hHb _) hGlow (land_ascent_armG_of_mid2fail2G hcr hlip i L hp hmid) hDG,
        leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
          (fun j => hHb _) hTlow (land_ascent_armT_of_mid2fail2G hcr hlip i L hp hmid) hDT⟩

end PairFold

end HPC.Fold
