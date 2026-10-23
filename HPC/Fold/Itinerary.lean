import HPC.Chains.Schedule

/-!
# Folding an arm onto the Λ-itinerary (Lemma F1), assembly, and the bridge to chains

Everything here is about 1-Lipschitz integer sequences; chains enter only in the last theorem.

An *arm* is a 1-Lipschitz `f : Fin m → ℤ` with `f 0 = p`. The *Λ-itinerary* for `p, H, L`
is the walk of centers `p, p+1, …, κ, κ−1, …, L+1` with `κ = max (H−1) p`. An arm *folds* onto
a walk if there is a 1-Lipschitz time-assignment from `0` with every level within one of its
time's center. **Lemma F1** characterizes folding onto Λ by the *peak-window criterion*: before
the arm's first drop to `p−2` it reaches level `≥ κ`, or reaches `≥ κ−1` twice, or reaches
`≥ κ−1` once after some non-ascending step. The V-itinerary is Λ for `−f`.

English proofs: COMMISSION-batch6.md §3. Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

/-- 1-Lipschitz integer sequences. -/
def IsLip {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ j j' : Fin m, j'.val = j.val + 1 → |f j' - f j| ≤ 1

/-! ## The Λ-itinerary -/

/-- The peak level. -/
def κ (p H : ℤ) : ℤ := max (H - 1) p

/-- Number of times: `κ − p + 1` ascending (times `0..κ−p`), then `κ − L − 1` descending
(centers `κ−1, …, L+1`), clamped at zero when there is nothing to descend to. -/
def lamLen (p H L : ℤ) : ℕ := ((κ p H - p) + max (κ p H - L - 1) 0 + 1).toNat

/-- The center at time `u`: `p + u` on the ascending leg, `κ − (u − (κ − p))` after. -/
def lamCenter (p H L : ℤ) (u : ℕ) : ℤ :=
  if (u : ℤ) ≤ κ p H - p then p + u else κ p H - ((u : ℤ) - (κ p H - p))

/-- The peak is at least the starting level. -/
theorem le_κ (p H : ℤ) : p ≤ κ p H := le_max_right _ _

/-- Membership in the walk, as an inequality over `ℤ`. -/
theorem lt_lamLen_iff {p H L : ℤ} {u : ℕ} :
    u < lamLen p H L ↔ (u : ℤ) ≤ (κ p H - p) + max (κ p H - L - 1) 0 := by
  rw [lamLen, Int.lt_toNat]; omega

/-- The center on the ascending leg. -/
theorem lamCenter_asc (p H L : ℤ) (u : ℕ) (hu : (u : ℤ) ≤ κ p H - p) :
    lamCenter p H L u = p + u := if_pos hu

/-- The center on the descending leg. -/
theorem lamCenter_desc (p H L : ℤ) (u : ℕ) (hu : ¬ ((u : ℤ) ≤ κ p H - p)) :
    lamCenter p H L u = κ p H - ((u : ℤ) - (κ p H - p)) := if_neg hu

theorem lamCenter_zero (p H L : ℤ) (_hp : p ≤ H) : lamCenter p H L 0 = p := by
  have h := le_κ p H
  rw [lamCenter_asc _ _ _ 0 (by simpa using by omega)]
  simp

/-- Consecutive centers differ by one (or the walk has stopped). -/
theorem lamCenter_lip (p H L : ℤ) (u : ℕ) (_hu : u + 1 < lamLen p H L) :
    |lamCenter p H L (u + 1) - lamCenter p H L u| ≤ 1 := by
  have h := le_κ p H
  rcases le_or_gt ((u : ℤ) + 1) (κ p H - p) with hc | hc
  · rw [lamCenter_asc _ _ _ (u + 1) (by push_cast; omega),
      lamCenter_asc _ _ _ u (by omega)]
    push_cast; rw [abs_le]; omega
  · rw [lamCenter_desc _ _ _ (u + 1) (by push_cast; omega)]
    rcases le_or_gt (u : ℤ) (κ p H - p) with hc2 | hc2
    · rw [lamCenter_asc _ _ _ u hc2]
      push_cast; rw [abs_le]; omega
    · rw [lamCenter_desc _ _ _ u (by omega)]
      push_cast; rw [abs_le]; omega

/-- The last center is `L + 1` when there is a descending leg, and the walk's centers cover
`[L+1, κ]`; with slack one every level of `[L, H]` is within one of some center. -/
theorem lamCenter_covers (p H L : ℤ) (hLp : L ≤ p) (hpH : p ≤ H) (ℓ : ℤ) (hℓL : L ≤ ℓ)
    (hℓH : ℓ ≤ H) : ∃ u, u < lamLen p H L ∧ |ℓ - lamCenter p H L u| ≤ 1 := by
  have hK := le_κ p H
  have hH1 : H - 1 ≤ κ p H := le_max_left _ _
  rcases le_or_gt p ℓ with h1 | h1
  · rcases le_or_gt ℓ (κ p H) with h2 | h2
    · -- ascending leg, exact hit
      refine ⟨(ℓ - p).toNat, by rw [lt_lamLen_iff]; omega, ?_⟩
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le]; omega
    · -- `ℓ = κ + 1`, use the peak
      refine ⟨(κ p H - p).toNat, by rw [lt_lamLen_iff]; omega, ?_⟩
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le]; omega
  · rcases lt_or_ge ((κ p H) - L - 1) 1 with h2 | h2
    · -- no room on the descending leg: then `ℓ ≥ p - 1` and time `0` serves
      refine ⟨0, by rw [lt_lamLen_iff]; omega, ?_⟩
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le]; omega
    · rcases le_or_gt (L + 1) ℓ with h3 | h3
      · -- descending leg, exact hit
        refine ⟨((κ p H - p) + (κ p H - ℓ)).toNat, by rw [lt_lamLen_iff]; omega, ?_⟩
        rw [lamCenter_desc _ _ _ _ (by omega), abs_le]; omega
      · -- `ℓ = L`, use the last center `L + 1`
        refine ⟨((κ p H - p) + (κ p H - L - 1)).toNat, by rw [lt_lamLen_iff]; omega, ?_⟩
        rw [lamCenter_desc _ _ _ _ (by omega), abs_le]; omega

/-! ## Folding -/

/-- `f` folds onto the walk `c` of length `len`: a Lipschitz time-assignment from `0`, every
level within one of its time's center. -/
def FoldsOnto {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) : Prop :=
  ∃ β : Fin m → ℕ, (∀ j, β j < len) ∧
    (∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
    (∀ j : Fin m, j.val = 0 → β j = 0) ∧
    ∀ j, |f j - c (β j)| ≤ 1

/-! ## The peak-window criterion -/

/-- A non-ascending step at index `t ≥ 1`: `f t ≤ f (t−1)`. -/
def NonAscAt {m : ℕ} (f : Fin m → ℤ) (t : Fin m) : Prop :=
  0 < t.val ∧ ∀ t' : Fin m, t'.val + 1 = t.val → f t ≤ f t'

/-- **The criterion.** Either the arm starts at the peak (`p ≥ κ`), or for every index `d` at
which the arm is at level `≤ p − 2` (in particular the first such index), the prefix before
`d` contains a link at level `≥ κ`, or two links at level `≥ κ − 1`, or one link at level
`≥ κ − 1` preceded by a non-ascending step. -/
def CritLam {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) : Prop :=
  p ≥ κ p H ∨
  ∀ d : Fin m, f d ≤ p - 2 →
    (∃ j : Fin m, j < d ∧ κ p H ≤ f j) ∨
    (∃ j j' : Fin m, j < j' ∧ j' < d ∧ κ p H - 1 ≤ f j ∧ κ p H - 1 ≤ f j') ∨
    (∃ j : Fin m, j < d ∧ κ p H - 1 ≤ f j ∧ ∃ t : Fin m, t < j ∧ NonAscAt f t)

/-! ### Auxiliary facts about sequences on `Fin m` -/

/-- A nonempty predicate on `Fin m` has a least index satisfying it. -/
theorem exists_least_index {m : ℕ} (P : Fin m → Prop) (h : ∃ j, P j) :
    ∃ j, P j ∧ ∀ j' : Fin m, j'.val < j.val → ¬ P j' := by
  classical
  obtain ⟨j0, hj0⟩ := h
  have hne : (Finset.univ.filter P).Nonempty := ⟨j0, by simp [hj0]⟩
  obtain ⟨j, hj, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter P) (fun j => j.val) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  refine ⟨j, hj, fun j' hj' hP => ?_⟩
  have := hmin j' (by simp [hP])
  omega

/-- A Lipschitz `ℕ`-valued sequence starting at `0` is bounded by its index. -/
theorem le_index_of_lip {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1)
    (hm : 0 < m) (h0 : β ⟨0, hm⟩ = 0) : ∀ (k : ℕ) (j : Fin m), j.val = k → β j ≤ k := by
  intro k
  induction k with
  | zero => intro j hj; rw [show j = ⟨0, hm⟩ from Fin.ext hj, h0]
  | succ k ih =>
      intro j hj
      have hk : k < m := by have := j.isLt; omega
      have h1 := ih ⟨k, hk⟩ rfl
      have h2 := hlip ⟨k, hk⟩ j hj
      rw [abs_le] at h2
      omega

/-- A bounded discrete intermediate value theorem: a Lipschitz `ℕ`-valued sequence passing
from `≤ v` at `a` to `> v` at `b` takes the value `v` somewhere in `[a, b)`. -/
theorem exists_lt_eq_of_lip {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) (v : ℕ) :
    ∀ (k : ℕ) (a b : Fin m), b.val = a.val + k → β a ≤ v → v < β b →
      ∃ t : Fin m, a.val ≤ t.val ∧ t.val < b.val ∧ β t = v := by
  intro k
  induction k with
  | zero =>
      intro a b hb h1 h2
      rw [show b = a from Fin.ext (by omega)] at h2
      omega
  | succ k ih =>
      intro a b hb h1 h2
      have hk : a.val + k < m := by have := b.isLt; omega
      have hstep := hlip ⟨a.val + k, hk⟩ b (by show b.val = a.val + k + 1; omega)
      rw [abs_le] at hstep
      by_cases hc : v < β ⟨a.val + k, hk⟩
      · obtain ⟨t, ht1, ht2, ht3⟩ := ih a ⟨a.val + k, hk⟩ rfl h1 hc
        refine ⟨t, ht1, ?_, ht3⟩
        have : t.val < a.val + k := ht2
        omega
      · refine ⟨⟨a.val + k, hk⟩, ?_, ?_, ?_⟩
        · show a.val ≤ a.val + k
          omega
        · show a.val + k < b.val
          omega
        · have hc' : β ⟨a.val + k, hk⟩ ≤ v := by omega
          omega

/-- If every step of `(j₁, j₂]` is strictly ascending, the arm climbs by at least the number
of steps. -/
theorem le_add_of_all_asc {m : ℕ} {f : Fin m → ℤ} :
    ∀ (k : ℕ) (j₁ j₂ : Fin m), j₂.val = j₁.val + k →
      (∀ t : Fin m, j₁.val < t.val → t.val ≤ j₂.val → ¬ NonAscAt f t) → f j₁ + k ≤ f j₂ := by
  intro k
  induction k with
  | zero =>
      intro j₁ j₂ h _
      rw [show j₂ = j₁ from Fin.ext (by omega)]
      simp
  | succ k ih =>
      intro j₁ j₂ h hno
      have hk : j₁.val + k < m := by have := j₂.isLt; omega
      have h1 : f j₁ + k ≤ f ⟨j₁.val + k, hk⟩ :=
        ih j₁ ⟨j₁.val + k, hk⟩ rfl
          (fun t ht1 ht2 => hno t ht1 (by have : t.val ≤ j₁.val + k := ht2; omega))
      have h2 := hno j₂ (by omega) le_rfl
      have h3 : ¬ (∀ t' : Fin m, t'.val + 1 = j₂.val → f j₂ ≤ f t') := fun hall =>
        h2 ⟨by omega, hall⟩
      push_neg at h3
      obtain ⟨t', ht'1, ht'2⟩ := h3
      rw [show t' = (⟨j₁.val + k, hk⟩ : Fin m) from
        Fin.ext (by show t'.val = j₁.val + k; omega)] at ht'2
      push_cast
      omega

/-! ### The two directions of Lemma F1 -/

/-- **Lemma F1, (⇐).** The criterion gives a fold. -/
theorem foldsOnto_lam_of_crit {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (hcrit : CritLam f p H) :
    FoldsOnto f (lamLen p H L) (lamCenter p H L) := by
  classical
  have hpH : p ≤ H := h0 ▸ hH ⟨0, hm⟩
  by_cases hpk : κ p H ≤ p
  · -- **Case `p ≥ κ`.** The walk is `p` then `p−1, …, L+1`; assign `max (0, p−1−f j)`.
    have hKp : κ p H = p := le_antisymm hpk (le_κ p H)
    have hHp : H ≤ p + 1 := by have h1 : H - 1 ≤ κ p H := le_max_left _ _; omega
    refine ⟨fun j => (p - 1 - f j).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro j
      rw [lt_lamLen_iff, hKp]
      have := hL j
      omega
    · intro j j' hjj'
      have := hf j j' hjj'
      rw [abs_le] at this ⊢
      omega
    · intro j hj
      rw [show j = ⟨0, hm⟩ from Fin.ext hj, h0]
      omega
    · intro j
      by_cases hc : p - 1 ≤ f j
      · have e : (p - 1 - f j).toNat = 0 := by omega
        rw [e, lamCenter_zero p H L hpH, abs_le]
        have := hH j
        omega
      · rw [lamCenter_desc _ _ _ _ (by rw [hKp]; omega), hKp, abs_le]
        omega
  · -- **Case `p < κ`.** Then `κ = H − 1`.
    have hκH : κ p H = H - 1 := by simp only [κ] at hpk ⊢; omega
    have hpK : p < κ p H := by omega
    have hcrit2 : ∀ d : Fin m, f d ≤ p - 2 →
        (∃ j : Fin m, j < d ∧ κ p H ≤ f j) ∨
        (∃ j j' : Fin m, j < j' ∧ j' < d ∧ κ p H - 1 ≤ f j ∧ κ p H - 1 ≤ f j') ∨
        (∃ j : Fin m, j < d ∧ κ p H - 1 ≤ f j ∧ ∃ t : Fin m, t < j ∧ NonAscAt f t) := by
      rcases hcrit with h | h
      · exact absurd h hpk
      · exact h
    -- *The phase.*
    set φ : Fin m → ℤ := fun j => if ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t then 1 else 0
      with hφdef
    have hφ1 : ∀ j : Fin m, (∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t) → φ j = 1 := by
      intro j hj; rw [hφdef]; exact if_pos hj
    have hφ0 : ∀ j : Fin m, ¬ (∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t) → φ j = 0 := by
      intro j hj; rw [hφdef]; exact if_neg hj
    have hφ01 : ∀ j, φ j = 0 ∨ φ j = 1 := by
      intro j
      by_cases hj : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t
      · exact Or.inr (hφ1 j hj)
      · exact Or.inl (hφ0 j hj)
    have hφz : φ ⟨0, hm⟩ = 0 := by
      refine hφ0 _ ?_
      rintro ⟨t, ht, hNA⟩
      have h1 : t.val ≤ 0 := ht
      have h2 := hNA.1
      omega
    -- *The phased arm.*
    set g : Fin m → ℤ := fun j => f j + φ j with hgdef
    have hgval : ∀ j, g j = f j + φ j := by intro j; rw [hgdef]
    have hgz : g ⟨0, hm⟩ = p := by rw [hgval, hφz, h0]; ring
    have hstepNA : ∀ j j' : Fin m, j'.val = j.val + 1 → φ j = 0 → φ j' = 1 → f j' ≤ f j := by
      intro j j' hjj' hj hj'
      have hex : ∃ t : Fin m, t.val ≤ j'.val ∧ NonAscAt f t := by
        by_contra hno
        have := hφ0 j' hno
        omega
      obtain ⟨t, ht, hNA⟩ := hex
      by_cases htj : t.val ≤ j.val
      · have := hφ1 j ⟨t, htj, hNA⟩
        omega
      · rw [show t = j' from Fin.ext (by omega)] at hNA
        exact hNA.2 j (by omega)
    have hglip : ∀ j j' : Fin m, j'.val = j.val + 1 → |g j' - g j| ≤ 1 := by
      intro j j' hjj'
      have hfs := hf j j' hjj'
      have e1 := hgval j
      have e2 := hgval j'
      rw [abs_le] at hfs ⊢
      rcases hφ01 j with hj | hj <;> rcases hφ01 j' with hj' | hj'
      · omega
      · have := hstepNA j j' hjj' hj hj'; omega
      · exfalso
        have hex : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t := by
          by_contra hno
          have := hφ0 j hno
          omega
        obtain ⟨t, ht, hNA⟩ := hex
        have := hφ1 j' ⟨t, by omega, hNA⟩
        omega
      · omega
    -- *Phase-one assignment: bound and window.*
    have hbound1 : ∀ j : Fin m, g j ≤ κ p H - 1 → (g j - p).toNat < lamLen p H L := by
      intro j hj
      rw [lt_lamLen_iff]
      omega
    have hwin1 : ∀ j : Fin m, p - 1 ≤ f j → g j ≤ κ p H - 1 →
        |f j - lamCenter p H L ((g j - p).toNat)| ≤ 1 := by
      intro j hf1 hj
      have e1 := hgval j
      have e2 := hφ01 j
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le]
      omega
    by_cases hQ : ∃ js : Fin m, κ p H ≤ g js ∧ ∀ j : Fin m, j.val ≤ js.val → p - 1 ≤ f j
    · -- *The switch index exists.*
      obtain ⟨js, ⟨hgjs, hbefore⟩, hjsmin⟩ := exists_least_index _ hQ
      have hlow : ∀ j : Fin m, j.val < js.val → g j ≤ κ p H - 1 := by
        intro j hj
        by_contra hcon
        exact hjsmin j hj ⟨by omega, fun j' hj' => hbefore j' (by omega)⟩
      have hjspos : 0 < js.val := by
        by_contra hcon
        rw [show js = ⟨0, hm⟩ from Fin.ext (by show js.val = 0; omega), hgz] at hgjs
        omega
      have hfjs : κ p H - 1 ≤ f js := by
        have := hgval js
        have := hφ01 js
        omega
      have hjs1 : js.val - 1 < m := by have := js.isLt; omega
      have hglast : g ⟨js.val - 1, hjs1⟩ = κ p H - 1 := by
        have h1 := hlow ⟨js.val - 1, hjs1⟩ (by show js.val - 1 < js.val; omega)
        have h2 := hglip ⟨js.val - 1, hjs1⟩ js (by show js.val = js.val - 1 + 1; omega)
        rw [abs_le] at h2
        omega
      refine ⟨fun j => if j.val < js.val then (g j - p).toNat
          else ((κ p H - p) + max (κ p H - 1 - f j) 0).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro j
        by_cases hc : j.val < js.val
        · rw [if_pos hc]
          exact hbound1 j (hlow j hc)
        · rw [if_neg hc, lt_lamLen_iff]
          have := hL j
          omega
      · intro j j' hjj'
        by_cases hc : j.val < js.val <;> by_cases hc' : j'.val < js.val
        · rw [if_pos hc, if_pos hc']
          have := hglip j j' hjj'
          rw [abs_le] at this ⊢
          omega
        · rw [if_pos hc, if_neg hc',
            show j = (⟨js.val - 1, hjs1⟩ : Fin m) from
              Fin.ext (by show j.val = js.val - 1; omega),
            show j' = js from Fin.ext (by omega), hglast]
          have e : max (κ p H - 1 - f js) 0 = 0 := by omega
          rw [e, abs_le]
          omega
        · exfalso; omega
        · rw [if_neg hc, if_neg hc']
          have := hf j j' hjj'
          rw [abs_le] at this ⊢
          omega
      · intro j hj
        rw [if_pos (show j.val < js.val by omega),
          show j = ⟨0, hm⟩ from Fin.ext hj, hgz]
        simp
      · intro j
        by_cases hc : j.val < js.val
        · rw [if_pos hc]
          exact hwin1 j (hbefore j (by omega)) (hlow j hc)
        · rw [if_neg hc]
          by_cases hd : κ p H - 1 ≤ f j
          · have e : max (κ p H - 1 - f j) 0 = 0 := by omega
            rw [e, lamCenter_asc _ _ _ _ (by omega), abs_le]
            have := hH j
            omega
          · have e : max (κ p H - 1 - f j) 0 = κ p H - 1 - f j := by omega
            rw [e, lamCenter_desc _ _ _ _ (by omega), abs_le]
            have := hL j
            omega
    · -- *No switch index: then the arm never drops, and phase one alone is a fold.*
      push_neg at hQ
      have hpeak : ∀ d : Fin m, f d ≤ p - 2 → ∃ j : Fin m, j.val < d.val ∧ κ p H ≤ g j := by
        intro d hd
        rcases hcrit2 d hd with ⟨j, hjd, hj⟩ | ⟨j1, j2, h12, h2d, hj1, hj2⟩ |
          ⟨j, hjd, hj, t, htj, hNA⟩
        · refine ⟨j, hjd, ?_⟩
          have := hgval j
          have := hφ01 j
          omega
        · by_cases hna : ∃ t : Fin m, j1.val < t.val ∧ t.val ≤ j2.val ∧ NonAscAt f t
          · obtain ⟨t, ht1, ht2, ht3⟩ := hna
            refine ⟨j2, h2d, ?_⟩
            have := hφ1 j2 ⟨t, ht2, ht3⟩
            have := hgval j2
            omega
          · push_neg at hna
            have h12' : j1.val < j2.val := h12
            have h4 := le_add_of_all_asc (f := f) (j2.val - j1.val) j1 j2 (by omega)
              (fun t ht1 ht2 => hna t ht1 ht2)
            refine ⟨j2, h2d, ?_⟩
            have := hgval j2
            have := hφ01 j2
            omega
        · refine ⟨j, hjd, ?_⟩
          have htj' : t.val < j.val := htj
          have := hφ1 j ⟨t, by omega, hNA⟩
          have := hgval j
          omega
      have hnodrop : ∀ j : Fin m, p - 1 ≤ f j := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨d, hd, hdmin⟩ := exists_least_index (fun j => f j ≤ p - 2)
          (by obtain ⟨j, hj⟩ := hcon; exact ⟨j, by omega⟩)
        obtain ⟨j, hjd, hjg⟩ := hpeak d hd
        obtain ⟨j', hj', hj'2⟩ := hQ j hjg
        exact hdmin j' (by omega) (by omega)
      have hglow : ∀ j, g j ≤ κ p H - 1 := by
        intro j
        by_contra hcon
        obtain ⟨j', hj', hj'2⟩ := hQ j (by omega)
        have := hnodrop j'
        omega
      refine ⟨fun j => (g j - p).toNat, fun j => hbound1 j (hglow j), ?_, ?_,
        fun j => hwin1 j (hnodrop j) (hglow j)⟩ <;> dsimp only
      · intro j j' hjj'
        have := hglip j j' hjj'
        rw [abs_le] at this ⊢
        omega
      · intro j hj
        rw [show j = ⟨0, hm⟩ from Fin.ext hj, hgz]
        simp

/-- **Lemma F1, (⇒).** A fold satisfies the criterion. -/
theorem crit_of_foldsOnto_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (p H L : ℤ)
    (h0 : f ⟨0, hm⟩ = p)
    (hfold : FoldsOnto f (lamLen p H L) (lamCenter p H L)) : CritLam f p H := by
  classical
  by_cases hpk : κ p H ≤ p
  · exact Or.inl hpk
  · right
    intro d hd
    obtain ⟨β, hlt, hlip, hz, hw⟩ := hfold
    have hκH : κ p H = H - 1 := by simp only [κ] at hpk ⊢; omega
    have hpK : p < κ p H := by omega
    -- `A` is the peak time
    set A : ℕ := (κ p H - p).toNat with hAdef
    have hA : (A : ℤ) = κ p H - p := by rw [hAdef]; omega
    have hApos : 0 < A := by omega
    have hβ0 : β ⟨0, hm⟩ = 0 := hz _ rfl
    -- the arm is at a level `≤ p − 1` at `d`, so its time there is past the peak
    have hβd : A < β d := by
      by_contra hcon
      have hwd := hw d
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le] at hwd
      omega
    obtain ⟨t0, -, ht02, ht03⟩ := exists_lt_eq_of_lip hlip A d.val ⟨0, hm⟩ d
      (by show d.val = 0 + d.val; omega) (by omega) hβd
    have ht02' : t0.val < d.val := ht02
    obtain ⟨j0, hj0, hj0min⟩ := exists_least_index (fun j => β j = A) ⟨t0, ht03⟩
    have hj0d : j0.val < d.val := by
      by_contra hcon
      exact hj0min t0 (by omega) ht03
    have hj0pos : 0 < j0.val := by
      by_contra hcon
      rw [show j0 = ⟨0, hm⟩ from Fin.ext (by show j0.val = 0; omega), hβ0] at hj0
      omega
    have hj01 : j0.val - 1 < m := by have := j0.isLt; omega
    have hstep := hlip ⟨j0.val - 1, hj01⟩ j0 (by show j0.val = j0.val - 1 + 1; omega)
    rw [abs_le] at hstep
    -- the peak time is reached from `A − 1`
    have hprev : β ⟨j0.val - 1, hj01⟩ = A - 1 := by
      have hne : β ⟨j0.val - 1, hj01⟩ ≠ A := hj0min _ (by show j0.val - 1 < j0.val; omega)
      by_contra hcon
      have hgt : A < β ⟨j0.val - 1, hj01⟩ := by omega
      obtain ⟨t, -, ht2, ht3⟩ := exists_lt_eq_of_lip hlip A (j0.val - 1) ⟨0, hm⟩
        ⟨j0.val - 1, hj01⟩ (by show j0.val - 1 = 0 + (j0.val - 1); omega) (by omega) hgt
      have ht2' : t.val < j0.val - 1 := ht2
      exact hj0min t (by omega) ht3
    -- the windows at the peak and just before it
    have hwj0 : κ p H - 1 ≤ f j0 ∧ f j0 ≤ κ p H + 1 := by
      have h1 := hw j0
      rw [hj0, lamCenter_asc _ _ _ _ (by omega), abs_le] at h1
      omega
    have hwj1 : f ⟨j0.val - 1, hj01⟩ ≤ κ p H := by
      have h1 := hw ⟨j0.val - 1, hj01⟩
      rw [hprev, lamCenter_asc _ _ _ _ (by omega), abs_le] at h1
      omega
    by_cases hc1 : κ p H ≤ f j0
    · exact Or.inl ⟨j0, hj0d, hc1⟩
    · by_cases hc2 : κ p H - 1 ≤ f ⟨j0.val - 1, hj01⟩
      · exact Or.inr (Or.inl ⟨⟨j0.val - 1, hj01⟩, j0,
          by show j0.val - 1 < j0.val; omega, hj0d, hc2, hwj0.1⟩)
      · -- `f j0 = κ − 1` and `f (j0 − 1) = κ − 2`: there is a non-ascending step before `j0`
        refine Or.inr (Or.inr ⟨j0, hj0d, hwj0.1, ?_⟩)
        by_contra hno
        push_neg at hno
        have hasc : ∀ t : Fin m, 0 < t.val → t.val ≤ j0.val → ¬ NonAscAt f t := by
          intro t ht1 ht2 hNA
          rcases Nat.lt_or_ge t.val j0.val with hlt | hge
          · exact hno t hlt hNA
          · have htj : t = j0 := Fin.ext (by omega)
            subst htj
            have := hNA.2 ⟨t.val - 1, hj01⟩ (by show t.val - 1 + 1 = t.val; omega)
            omega
        have hclimb := le_add_of_all_asc (f := f) j0.val ⟨0, hm⟩ j0
          (by show j0.val = 0 + j0.val; omega) (fun t ht1 ht2 => hasc t ht1 ht2)
        have hβle := le_index_of_lip hlip hm hβ0 j0.val j0 rfl
        rw [h0] at hclimb
        omega

/-- **Lemma F1.** For an arm with values in `[L, H]` starting at `p`, folding onto the
Λ-itinerary is equivalent to the peak-window criterion. -/
theorem foldsOnto_lam_iff {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) :
    FoldsOnto f (lamLen p H L) (lamCenter p H L) ↔ CritLam f p H :=
  ⟨crit_of_foldsOnto_lam hm f p H L h0, foldsOnto_lam_of_crit hm f hf p H L h0 hL hH⟩

/-! ## The V-itinerary by reflection -/

/-- The V-itinerary is the Λ-itinerary of the negated arm. -/
def veeLen (p H L : ℤ) : ℕ := lamLen (-p) (-L) (-H)
def veeCenter (p H L : ℤ) (u : ℕ) : ℤ := - lamCenter (-p) (-L) (-H) u
def CritVee {m : ℕ} (f : Fin m → ℤ) (p L : ℤ) : Prop := CritLam (fun j => - f j) (-p) (-L)

/-- Folding onto a reflected walk is folding of the reflected arm. -/
theorem foldsOnto_neg {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    FoldsOnto f len (fun u => - c u) ↔ FoldsOnto (fun j => - f j) len c := by
  constructor <;> rintro ⟨β, h1, h2, h3, h4⟩ <;> refine ⟨β, h1, h2, h3, fun j => ?_⟩ <;>
    · have := h4 j
      simp only [abs_le] at this ⊢
      omega

theorem foldsOnto_vee_iff {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) :
    FoldsOnto f (veeLen p H L) (veeCenter p H L) ↔ CritVee f p L := by
  have hneg : IsLip (fun j => - f j) := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [abs_le] at this ⊢
    omega
  have key := foldsOnto_lam_iff hm (fun j => - f j) hneg (-p) (-L) (-H)
    (by simp only; rw [h0]) (fun j => by simp only; have := hH j; omega)
    (fun j => by simp only; have := hL j; omega)
  show FoldsOnto f (lamLen (-p) (-L) (-H)) (fun u => - lamCenter (-p) (-L) (-H) u) ↔
    CritLam (fun j => - f j) (-p) (-L)
  rw [foldsOnto_neg]
  exact key

/-! ## Assembly: two arms folding onto one walk give a schedule of the whole sequence -/

/-- The forward arm from `i`: `j ↦ ρ (i + j)`. -/
def armG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) : Fin (n - i.val) → ℤ :=
  fun j => ρ ⟨i.val + j.val, by omega⟩

/-- The backward arm from `i`: `j ↦ ρ (i − j)`. -/
def armT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) : Fin (i.val + 1) → ℤ :=
  fun j => ρ ⟨i.val - j.val, by omega⟩

theorem armG_isLip {n : ℕ} {ρ : Fin n → ℤ} (h : IsLip ρ) (i : Fin n) : IsLip (armG ρ i) := by
  intro j j' hjj'
  have hj := j.isLt
  have hj' := j'.isLt
  exact h ⟨i.val + j.val, by omega⟩ ⟨i.val + j'.val, by omega⟩ (by simp; omega)

theorem armT_isLip {n : ℕ} {ρ : Fin n → ℤ} (h : IsLip ρ) (i : Fin n) : IsLip (armT ρ i) := by
  intro j j' hjj'
  have hj := j.isLt
  have hj' := j'.isLt
  have hi := i.isLt
  have := h ⟨i.val - j'.val, by omega⟩ ⟨i.val - j.val, by omega⟩ (by simp; omega)
  rw [abs_sub_comm] at this
  exact this

/-- If both arms fold onto the same walk, the whole sequence has a Lipschitz time-assignment
from `i` with every level within one of its time's center. -/
theorem exists_schedule_of_folds {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (len : ℕ) (c : ℕ → ℤ)
    (hG : FoldsOnto (armG ρ i) len c) (hT : FoldsOnto (armT ρ i) len c) :
    ∃ β : Fin n → ℕ, (∀ t, β t < len) ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → |(β t' : ℤ) - (β t : ℤ)| ≤ 1) ∧
      β i = 0 ∧ ∀ t, |ρ t - c (β t)| ≤ 1 := by
  classical
  obtain ⟨βG, hGlt, hGlip, hG0, hGw⟩ := hG
  obtain ⟨βT, hTlt, hTlip, hT0, hTw⟩ := hT
  set β : Fin n → ℕ := fun t => if h : i.val ≤ t.val
    then βG ⟨t.val - i.val, by have := t.isLt; omega⟩
    else βT ⟨i.val - t.val, by omega⟩ with hβ
  -- the two branches, valid also at the overlap `t = i`
  have hGval : ∀ (t : Fin n) (h : i.val ≤ t.val),
      β t = βG ⟨t.val - i.val, by have := t.isLt; omega⟩ := by
    intro t h; simp only [hβ]; rw [dif_pos h]
  have hTval : ∀ (t : Fin n) (h : t.val ≤ i.val),
      β t = βT ⟨i.val - t.val, by omega⟩ := by
    intro t h
    by_cases hc : i.val ≤ t.val
    · have e1 : βG ⟨t.val - i.val, by have := t.isLt; omega⟩ = 0 :=
        hG0 _ (by show t.val - i.val = 0; omega)
      have e2 : βT ⟨i.val - t.val, by omega⟩ = 0 :=
        hT0 _ (by show i.val - t.val = 0; omega)
      rw [hGval t hc, e1, e2]
    · simp only [hβ]; rw [dif_neg hc]
  -- the two arms recover `ρ`
  have hGrho : ∀ (t : Fin n) (h : i.val ≤ t.val),
      armG ρ i ⟨t.val - i.val, by have := t.isLt; omega⟩ = ρ t := by
    intro t h
    simp only [armG]
    congr 1
    exact Fin.ext (by show i.val + (t.val - i.val) = t.val; omega)
  have hTrho : ∀ (t : Fin n) (h : t.val ≤ i.val),
      armT ρ i ⟨i.val - t.val, by omega⟩ = ρ t := by
    intro t h
    simp only [armT]
    congr 1
    exact Fin.ext (by show i.val - (i.val - t.val) = t.val; omega)
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases hc : i.val ≤ t.val
    · rw [hGval t hc]; exact hGlt _
    · rw [hTval t (by omega)]; exact hTlt _
  · intro t t' htt'
    by_cases hc : i.val ≤ t.val
    · rw [hGval t hc, hGval t' (by omega)]
      exact hGlip _ _ (by show t'.val - i.val = (t.val - i.val) + 1; omega)
    · rw [hTval t (by omega), hTval t' (by omega)]
      rw [abs_sub_comm]
      exact hTlip _ _ (by show i.val - t.val = (i.val - t'.val) + 1; omega)
  · rw [hGval i le_rfl]
    exact hG0 _ (by show i.val - i.val = 0; omega)
  · intro t
    by_cases hc : i.val ≤ t.val
    · rw [hGval t hc, ← hGrho t hc]; exact hGw _
    · rw [hTval t (by omega), ← hTrho t (by omega)]; exact hTw _

/-! ## Bridge to chains (batch 5) -/

open HPC.Chain in
/-- If the minimal-index sequence of a refinement `E ≤ D`, read from link `i`, has both arms
folding onto a common walk, then `E` has a block consolidation with every block inside three
consecutive links of `D` and `d_i` in the first block. This is Bing 1948 Theorem 3 in the block
reading and three-link form, conditional on the folding. -/
theorem exists_blocks_first_of_folds {X : Type*} [MetricSpace X] {n m : ℕ}
    {E : Chain X m} {D : Chain X n} (h : E.Refines D) (i : Fin m) (len : ℕ) (c : ℕ → ℤ)
    (hG : FoldsOnto (armG (fun t => (h.minIdx t : ℤ)) i) len c)
    (hT : FoldsOnto (armT (fun t => (h.minIdx t : ℤ)) i) len c) :
    ∃ (p : ℕ) (β' : Fin m → Fin p) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  obtain ⟨β, hβlt, hβlip, hβi, hβw⟩ :=
    exists_schedule_of_folds (fun t => (h.minIdx t : ℤ)) i len c hG hT
  have hsched : IsSchedule β :=
    ⟨fun t t' htt' => by have := hβlip t t' htt'; rw [abs_le] at this; omega, ⟨i, hβi⟩⟩
  obtain ⟨p, β', hβ', hval, hblk⟩ :=
    Chain.exists_blocks_of_walk h hsched c (fun t => by
      have := hβw t; rw [abs_le] at this; omega)
  exact ⟨p, β', hβ', by rw [hval i, hβi], hblk⟩

end HPC.Fold
