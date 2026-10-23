import HPC.Fold.Span7

/-!
# The crookedness clause, read on one arm, at arbitrary levels

Batch 38 isolated one instance of the crookedness clause on an arm, `Zig f L H`: between a time
at `L + 1` or below and a later time at `H` or above the arm has been at `H - 2` or above and,
after that, at `L + 2` or below.  That instance is what the span-seven leaf walk needed.

This file proves the clause in full.  On a single arm of a faithful crooked sequence the
crookedness condition says, for *any* two times whose levels differ by at least three:

* `CrookUp`   — between an earlier low time and a later high time the arm has been just below the
  high level and, after that, just above the low level;
* `CrookDown` — between an earlier high time and a later low time the arm has been just above the
  low level and, after that, just below the high level.

Both hold on the forward arm (`crookUp_armG`, `crookDown_armG`) and on the backward arm
(`crookUp_armT`, `crookDown_armT`): reversing the index order exchanges the two branches of the
crookedness clause, and the two branches are mirror images, so the same shape comes out.

The level forms `CrookUp.levels` and `CrookDown.levels` are the shape in which the clause is used:
for levels `a + 3 ≤ b`,

```
f s ≤ a, b ≤ f t, s < t  →  ∃ s < u < u' < t,  b - 2 ≤ f u  ∧  f u' ≤ a + 1
f s ≥ b, f t ≤ a, s < t  →  ∃ s < u < u' < t,  f u ≤ a + 1  ∧  b - 2 ≤ f u'
```

`Zig` is the single instance `a = L + 1`, `b = H` of the first (`zig_of_crookUp`), so `zig_armG`
and `zig_armT` of batch 38 are corollaries.

Two consequences worth recording, both immediate: a crooked arm cannot descend three levels
monotonically (`no_monotone_drop`), nor ascend three levels monotonically (`no_monotone_climb`).
-/

namespace HPC.Fold

/-! ## The two clauses -/

/-- **`CrookUp f`**: between a time and a later time three or more levels above it, the arm has
been within one of the upper level and, after that, within one of the lower level. -/
def CrookUp {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ s t : Fin m, s.val < t.val → f s + 3 ≤ f t →
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      f t - 2 ≤ f u ∧ f u ≤ f t - 1 ∧ f s ≤ f u' ∧ f u' ≤ f s + 1

/-- **`CrookDown f`**: between a time and a later time three or more levels below it, the arm has
been within one of the lower level and, after that, within one of the upper level. -/
def CrookDown {m : ℕ} (f : Fin m → ℤ) : Prop :=
  ∀ s t : Fin m, s.val < t.val → f t + 3 ≤ f s →
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      f t ≤ f u ∧ f u ≤ f t + 1 ∧ f s - 2 ≤ f u' ∧ f u' ≤ f s - 1

/-! ## The level forms -/

/-- The level form of `CrookUp`: the trigger times may be at any levels `a` and `b` three
apart. -/
theorem CrookUp.levels {m : ℕ} {f : Fin m → ℤ} (h : CrookUp f) (a b : ℤ) (hab : a + 3 ≤ b)
    (s t : Fin m) (hst : s.val < t.val) (hs : f s ≤ a) (ht : b ≤ f t) :
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      b - 2 ≤ f u ∧ f u' ≤ a + 1 := by
  obtain ⟨u, u', h1, h2, h3, h4, -, -, h7⟩ := h s t hst (by omega)
  exact ⟨u, u', h1, h2, h3, by omega, by omega⟩

/-- The level form of `CrookDown`. -/
theorem CrookDown.levels {m : ℕ} {f : Fin m → ℤ} (h : CrookDown f) (a b : ℤ) (hab : a + 3 ≤ b)
    (s t : Fin m) (hst : s.val < t.val) (hs : b ≤ f s) (ht : f t ≤ a) :
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      f u ≤ a + 1 ∧ b - 2 ≤ f u' := by
  obtain ⟨u, u', h1, h2, h3, -, h5, h6, -⟩ := h s t hst (by omega)
  exact ⟨u, u', h1, h2, h3, by omega, by omega⟩

/-! ## The clauses on the forward arm -/

/-- **`CrookUp` on the forward arm.** -/
theorem crookUp_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) :
    CrookUp (armG ρ i) := by
  intro s t hst hlev
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : armG ρ i s = ρ ⟨i.val + s.val, by omega⟩ := rfl
  have hT : armG ρ i t = ρ ⟨i.val + t.val, by omega⟩ := rfl
  have hST : (⟨i.val + s.val, by omega⟩ : Fin n) < ⟨i.val + t.val, by omega⟩ := by
    rw [Fin.lt_def]; exact Nat.add_lt_add_left hst _
  obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
    hcr.crooked ⟨i.val + s.val, by omega⟩ ⟨i.val + t.val, by omega⟩ hST
      (ρ ⟨i.val + s.val, by omega⟩) (ρ ⟨i.val + t.val, by omega⟩)
      ⟨⟨i.val + s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val + t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have hrlt : i.val + s.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val + t.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hb1 : r.val - i.val < n - i.val := by omega
  have hb2 : r'.val - i.val < n - i.val := by omega
  have e1 : armG ρ i ⟨r.val - i.val, hb1⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    exact congrArg ρ (Fin.ext (by show i.val + (r.val - i.val) = r.val; omega))
  have e2 : armG ρ i ⟨r'.val - i.val, hb2⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    exact congrArg ρ (Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega))
  refine ⟨⟨r.val - i.val, hb1⟩, ⟨r'.val - i.val, hb2⟩,
    show s.val < r.val - i.val by omega, show r.val - i.val < r'.val - i.val by omega,
    show r'.val - i.val < t.val by omega, by omega, by omega, by omega, by omega⟩

/-- **`CrookDown` on the forward arm.** -/
theorem crookDown_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) :
    CrookDown (armG ρ i) := by
  intro s t hst hlev
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : armG ρ i s = ρ ⟨i.val + s.val, by omega⟩ := rfl
  have hT : armG ρ i t = ρ ⟨i.val + t.val, by omega⟩ := rfl
  have hST : (⟨i.val + s.val, by omega⟩ : Fin n) < ⟨i.val + t.val, by omega⟩ := by
    rw [Fin.lt_def]; exact Nat.add_lt_add_left hst _
  obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
    hcr.crooked ⟨i.val + s.val, by omega⟩ ⟨i.val + t.val, by omega⟩ hST
      (ρ ⟨i.val + s.val, by omega⟩) (ρ ⟨i.val + t.val, by omega⟩)
      ⟨⟨i.val + s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val + t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have hrlt : i.val + s.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val + t.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hb1 : r.val - i.val < n - i.val := by omega
  have hb2 : r'.val - i.val < n - i.val := by omega
  have e1 : armG ρ i ⟨r.val - i.val, hb1⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    exact congrArg ρ (Fin.ext (by show i.val + (r.val - i.val) = r.val; omega))
  have e2 : armG ρ i ⟨r'.val - i.val, hb2⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    exact congrArg ρ (Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega))
  refine ⟨⟨r.val - i.val, hb1⟩, ⟨r'.val - i.val, hb2⟩,
    show s.val < r.val - i.val by omega, show r.val - i.val < r'.val - i.val by omega,
    show r'.val - i.val < t.val by omega, by omega, by omega, by omega, by omega⟩

/-! ## The clauses on the backward arm -/

/-- **`CrookUp` on the backward arm.**  Reading the clause through the reversed index order
exchanges its two branches, and the two branches are mirror images. -/
theorem crookUp_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) :
    CrookUp (armT ρ i) := by
  intro s t hst hlev
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : armT ρ i s = ρ ⟨i.val - s.val, by omega⟩ := rfl
  have hT : armT ρ i t = ρ ⟨i.val - t.val, by omega⟩ := rfl
  have hST : (⟨i.val - t.val, by omega⟩ : Fin n) < ⟨i.val - s.val, by omega⟩ := by
    rw [Fin.lt_def]; show i.val - t.val < i.val - s.val; omega
  obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
    hcr.crooked ⟨i.val - t.val, by omega⟩ ⟨i.val - s.val, by omega⟩ hST
      (ρ ⟨i.val - t.val, by omega⟩) (ρ ⟨i.val - s.val, by omega⟩)
      ⟨⟨i.val - t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val - s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have hrlt : i.val - t.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val - s.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hb1 : i.val - r'.val < i.val + 1 := by omega
  have hb2 : i.val - r.val < i.val + 1 := by omega
  have e1 : armT ρ i ⟨i.val - r'.val, hb1⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega))
  have e2 : armT ρ i ⟨i.val - r.val, hb2⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - r.val) = r.val; omega))
  refine ⟨⟨i.val - r'.val, hb1⟩, ⟨i.val - r.val, hb2⟩,
    show s.val < i.val - r'.val by omega, show i.val - r'.val < i.val - r.val by omega,
    show i.val - r.val < t.val by omega, by omega, by omega, by omega, by omega⟩

/-- **`CrookDown` on the backward arm.** -/
theorem crookDown_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) :
    CrookDown (armT ρ i) := by
  intro s t hst hlev
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : armT ρ i s = ρ ⟨i.val - s.val, by omega⟩ := rfl
  have hT : armT ρ i t = ρ ⟨i.val - t.val, by omega⟩ := rfl
  have hST : (⟨i.val - t.val, by omega⟩ : Fin n) < ⟨i.val - s.val, by omega⟩ := by
    rw [Fin.lt_def]; show i.val - t.val < i.val - s.val; omega
  obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
    hcr.crooked ⟨i.val - t.val, by omega⟩ ⟨i.val - s.val, by omega⟩ hST
      (ρ ⟨i.val - t.val, by omega⟩) (ρ ⟨i.val - s.val, by omega⟩)
      ⟨⟨i.val - t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val - s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have hrlt : i.val - t.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val - s.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hb1 : i.val - r'.val < i.val + 1 := by omega
  have hb2 : i.val - r.val < i.val + 1 := by omega
  have e1 : armT ρ i ⟨i.val - r'.val, hb1⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega))
  have e2 : armT ρ i ⟨i.val - r.val, hb2⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - r.val) = r.val; omega))
  refine ⟨⟨i.val - r'.val, hb1⟩, ⟨i.val - r.val, hb2⟩,
    show s.val < i.val - r'.val by omega, show i.val - r'.val < i.val - r.val by omega,
    show i.val - r.val < t.val by omega, by omega, by omega, by omega, by omega⟩

/-! ## `Zig` is one instance -/

/-- Batch 38's `Zig` is the instance `a = L + 1`, `b = H` of `CrookUp.levels`. -/
theorem zig_of_crookUp {m : ℕ} {f : Fin m → ℤ} (h : CrookUp f) (L H : ℤ) (hLH : L + 4 ≤ H) :
    Zig f L H := by
  intro s t hst hs ht
  obtain ⟨u, u', h1, h2, h3, h4, h5⟩ := h.levels (L + 1) H (by omega) s t hst hs ht
  exact ⟨u, u', h1, h2, h3, h4, by omega⟩

/-! ## Two immediate consequences -/

/-- **No monotone drop of three.**  A crooked arm cannot descend three levels without rising in
between: between a time and a later time three levels below it there is a time within two of the
higher level, preceded by one within one of the lower. -/
theorem no_monotone_drop {m : ℕ} {f : Fin m → ℤ} (h : CrookDown f) (s t : Fin m)
    (hst : s.val < t.val) (hlev : f t + 3 ≤ f s) :
    ∃ u' : Fin m, s.val < u'.val ∧ u'.val < t.val ∧ f s - 2 ≤ f u' ∧
      ∃ u : Fin m, s.val < u.val ∧ u.val < u'.val ∧ f u ≤ f t + 1 := by
  obtain ⟨u, u', h1, h2, h3, -, h5, h6, -⟩ := h s t hst hlev
  exact ⟨u', by omega, h3, h6, u, h1, h2, h5⟩

/-- **No monotone climb of three.** -/
theorem no_monotone_climb {m : ℕ} {f : Fin m → ℤ} (h : CrookUp f) (s t : Fin m)
    (hst : s.val < t.val) (hlev : f s + 3 ≤ f t) :
    ∃ u : Fin m, s.val < u.val ∧ u.val < t.val ∧ f t - 2 ≤ f u ∧
      ∃ u' : Fin m, u.val < u'.val ∧ u'.val < t.val ∧ f u' ≤ f s + 1 := by
  obtain ⟨u, u', h1, h2, h3, h4, -, -, h7⟩ := h s t hst hlev
  exact ⟨u, h1, by omega, h4, u', h2, h3, h7⟩

end HPC.Fold
