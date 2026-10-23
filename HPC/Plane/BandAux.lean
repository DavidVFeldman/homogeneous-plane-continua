import Mathlib

/-!
# Batch 109, auxiliary: elementary facts about unit lattice steps and the chamfered band

Pure real/integer lemmas used by `HPC/Plane/Band.lean`.

* `unit_cases`: the four unit vectors of `ℤ²`.
* `edge_of_sum`: two unit lattice steps with the same endpoint sum (the same midpoint) have the
  same pair of endpoints.
* `locF`: the band over one stretch in lattice coordinates relative to the stretch's lattice
  point `c`: with `a = c_prev - c`, `b = c_next - c` (two distinct unit vectors),
  `locF a b s t = (1 - s) • (a/2 + t • J(-a)) + s • (b/2 + t • J b)`, `J (x, y) = (-y, x)`.
  It lies in the closed square `[-1/2, 1/2]²` (`locF_bound`), in the open square for
  `0 < s < 1` (`locF_strict`), and is injective in `(s, t)` (`locF_inj`), for `|t| < 1/8`.
* `hat`, `sum_hat_two`: piecewise-linear interpolation as a finite sum of hat functions.
-/

namespace HPC.Plane.BandAux

/-- The four unit vectors of the integer lattice. -/
lemma unit_cases {a : ℤ × ℤ} (h : |a.1| + |a.2| = 1) :
    (a.1 = 1 ∧ a.2 = 0) ∨ (a.1 = -1 ∧ a.2 = 0) ∨ (a.1 = 0 ∧ a.2 = 1) ∨ (a.1 = 0 ∧ a.2 = -1) := by
  rcases abs_cases a.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases a.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    omega

/-- Two unit lattice steps `p → q`, `p' → q'` with `p + q = p' + q'` have the same endpoints. -/
lemma edge_of_sum {p q p' q' : ℤ × ℤ} (h : |q.1 - p.1| + |q.2 - p.2| = 1)
    (h' : |q'.1 - p'.1| + |q'.2 - p'.2| = 1) (h1 : p.1 + q.1 = p'.1 + q'.1)
    (h2 : p.2 + q.2 = p'.2 + q'.2) : (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  have u := unit_cases (a := (q.1 - p.1, q.2 - p.2)) h
  have u' := unit_cases (a := (q'.1 - p'.1, q'.2 - p'.2)) h'
  simp only at u u'
  rcases u with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases u' with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
  first
  | (left; exact ⟨Prod.ext (by omega) (by omega), Prod.ext (by omega) (by omega)⟩)
  | (right; exact ⟨Prod.ext (by omega) (by omega), Prod.ext (by omega) (by omega)⟩)

/-- Distinct unit lattice vectors have nonpositive dot product. -/
lemma dot_nonpos_of_ne {a e : ℤ × ℤ} (ha : |a.1| + |a.2| = 1) (he : |e.1| + |e.2| = 1)
    (hne : a ≠ e) : a.1 * e.1 + a.2 * e.2 ≤ 0 := by
  rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases unit_cases he with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  first
  | (exfalso; exact hne (Prod.ext (by omega) (by omega)))
  | (rw [h1, h2, h3, h4]; norm_num)

/-- The band over one stretch, in lattice coordinates relative to the stretch's lattice point. -/
noncomputable def locF (a b : ℤ × ℤ) (s t : ℝ) : ℝ × ℝ :=
  ((1 - s) * ((a.1 : ℝ) / 2 + t * a.2) + s * ((b.1 : ℝ) / 2 - t * b.2),
   (1 - s) * ((a.2 : ℝ) / 2 - t * a.1) + s * ((b.2 : ℝ) / 2 + t * b.1))

lemma locF_bound {a b : ℤ × ℤ} (ha : |a.1| + |a.2| = 1) (hb : |b.1| + |b.2| = 1) (hab : a ≠ b)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : |t| < 1 / 8) :
    |(locF a b s t).1| ≤ 1 / 2 ∧ |(locF a b s t).2| ≤ 1 / 2 := by
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  have p1 := mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1/8 - t)
  have p2 := mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1/8 + t)
  have p3 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) ≤ 1/8 - t)
  have p4 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) ≤ 1/8 + t)
  rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases unit_cases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  first
  | (exfalso; exact hab (Prod.ext (by omega) (by omega)))
  | (simp only [locF, h1, h2, h3, h4, Int.cast_one, Int.cast_zero, Int.cast_neg]
     constructor <;> rw [abs_le] <;> constructor <;> linarith)

lemma locF_strict {a b : ℤ × ℤ} (ha : |a.1| + |a.2| = 1) (hb : |b.1| + |b.2| = 1) (hab : a ≠ b)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| < 1 / 8) :
    |(locF a b s t).1| < 1 / 2 ∧ |(locF a b s t).2| < 1 / 2 := by
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  have p1 := mul_pos hs0 (by linarith : (0:ℝ) < 1/8 - t)
  have p2 := mul_pos hs0 (by linarith : (0:ℝ) < 1/8 + t)
  have p3 := mul_pos (by linarith : (0:ℝ) < 1 - s) (by linarith : (0:ℝ) < 1/8 - t)
  have p4 := mul_pos (by linarith : (0:ℝ) < 1 - s) (by linarith : (0:ℝ) < 1/8 + t)
  rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases unit_cases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  first
  | (exfalso; exact hab (Prod.ext (by omega) (by omega)))
  | (simp only [locF, h1, h2, h3, h4, Int.cast_one, Int.cast_zero, Int.cast_neg]
     constructor <;> rw [abs_lt] <;> constructor <;> linarith)

lemma cancel_aux {s s' c : ℝ} (hc : c ≠ 0) (h : s * c = s' * c) : s = s' :=
  mul_right_cancel₀ hc h

lemma locF_inj {a b : ℤ × ℤ} (ha : |a.1| + |a.2| = 1) (hb : |b.1| + |b.2| = 1) (hab : a ≠ b)
    {s t s' t' : ℝ} (ht : |t| < 1 / 8) (ht' : |t'| < 1 / 8)
    (h : locF a b s t = locF a b s' t') : s = s' ∧ t = t' := by
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  obtain ⟨ht1', ht2'⟩ := abs_lt.mp ht'
  have e1 : (1 - s) * ((a.1 : ℝ) / 2 + t * a.2) + s * ((b.1 : ℝ) / 2 - t * b.2) =
      (1 - s') * ((a.1 : ℝ) / 2 + t' * a.2) + s' * ((b.1 : ℝ) / 2 - t' * b.2) :=
    congrArg Prod.fst h
  have e2 : (1 - s) * ((a.2 : ℝ) / 2 - t * a.1) + s * ((b.2 : ℝ) / 2 + t * b.1) =
      (1 - s') * ((a.2 : ℝ) / 2 - t' * a.1) + s' * ((b.2 : ℝ) / 2 + t' * b.1) :=
    congrArg Prod.snd h
  clear h
  have c1 : (1/2 + t) ≠ 0 := by intro h; linarith
  have c2 : (1/2 - t) ≠ 0 := by intro h; linarith
  rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases unit_cases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  first
  | (exfalso; exact hab (Prod.ext (by omega) (by omega)))
  | (rw [h1, h2, h3, h4] at e1 e2
     simp only [Int.cast_one, Int.cast_zero, Int.cast_neg] at e1 e2
     have htt : t = t' := by linarith
     subst htt
     refine ⟨?_, rfl⟩
     first
     | linarith
     | exact cancel_aux c1 (by linarith)
     | exact cancel_aux c2 (by linarith))

/-- The hat function `max 0 (1 - |x|)`. -/
noncomputable def hat (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma continuous_hat : Continuous hat :=
  continuous_const.max (continuous_const.sub continuous_abs)

lemma hat_eq_zero {x : ℝ} (h : 1 ≤ |x|) : hat x = 0 := by
  unfold hat; exact max_eq_left (by linarith)

/-- On `τ = k - 1/2 + s`, `s ∈ [0, 1]`, `1 ≤ k < n`, the hat-function interpolation of the values
`X j` at the nodes `j + 1/2` is `(1 - s) • X (k - 1) + s • X k`. -/
lemma sum_hat_two {V : Type*} [AddCommGroup V] [Module ℝ V] (n : ℕ) (X : ℕ → V) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k < n) {s τ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : τ = k - 1 / 2 + s) :
    ∑ j ∈ Finset.range n, hat (τ - 1 / 2 - j) • X j = (1 - s) • X (k - 1) + s • X k := by
  rw [Finset.sum_eq_add (k - 1) k (by omega)]
  · congr 1
    · congr 1
      unfold hat
      rw [Nat.cast_sub hk1, abs_of_nonneg (by subst hτ; push_cast; linarith)]
      push_cast; subst hτ
      rw [max_eq_right (by linarith)]; ring
    · congr 1
      unfold hat
      rw [abs_of_nonpos (by subst hτ; linarith)]
      subst hτ
      rw [max_eq_right (by linarith)]; ring
  · intro j _ hj
    rw [hat_eq_zero, zero_smul]
    rcases lt_or_gt_of_ne hj.1 with h | h
    · have h' : (j : ℝ) + 2 ≤ k := by exact_mod_cast (by omega : j + 2 ≤ k)
      rw [abs_of_nonneg (by subst hτ; linarith)]; subst hτ; linarith
    · have h' : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : k + 1 ≤ j)
      rw [abs_of_nonpos (by subst hτ; linarith)]; subst hτ; linarith
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr hkn) h

/-- Two integers that agree up to perturbations of size `< 1/2` are equal. -/
lemma int_eq_of_close {A B : ℤ} {x y : ℝ} (h : (A : ℝ) + x = B + y) (hx : |x| < 1 / 2)
    (hy : |y| < 1 / 2) : A = B := by
  have h1 : ((A - B : ℤ) : ℝ) < 1 := by
    push_cast; linarith [abs_lt.mp hx, abs_lt.mp hy]
  have h2 : (-1 : ℝ) < ((A - B : ℤ) : ℝ) := by
    push_cast; linarith [abs_lt.mp hx, abs_lt.mp hy]
  have h1' : A - B < 1 := by exact_mod_cast h1
  have h2' : -1 < A - B := by exact_mod_cast h2
  omega

lemma one_le_abs_sub_of_ne {A B : ℤ} (h : A ≠ B) : 1 ≤ |(A : ℝ) - B| := by
  have : (1 : ℤ) ≤ |A - B| := Int.one_le_abs (sub_ne_zero.mpr h)
  have : ((1 : ℤ) : ℝ) ≤ ((|A - B| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at this; exact this

/-- Every point of `[1/2, n - 1/2]` (`n ≥ 2`) lies in some stretch `[k - 1/2, k + 1/2]` with
`1 ≤ k ≤ n - 1`. -/
lemma exists_stretch {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (h1 : 1 / 2 ≤ τ) (h2 : τ ≤ n - 1 / 2) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ τ = k - 1 / 2 + s := by
  set k := min (max 1 ⌊τ + 1 / 2⌋₊) (n - 1) with hk
  have hfl := Nat.floor_le (show (0 : ℝ) ≤ τ + 1 / 2 by linarith)
  have hlt := Nat.lt_floor_add_one (τ + 1 / 2)
  have hn' : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  refine ⟨k, by omega, by omega, τ - k + 1 / 2, ?_, ?_, by ring⟩
  · -- k ≤ τ + 1/2
    have : (k : ℝ) ≤ τ + 1 / 2 := by
      rcases le_total 1 ⌊τ + 1 / 2⌋₊ with h | h
      · have : k ≤ ⌊τ + 1 / 2⌋₊ := by omega
        exact le_trans (by exact_mod_cast this) hfl
      · have : k ≤ 1 := by omega
        have : (k : ℝ) ≤ 1 := by exact_mod_cast this
        linarith
    linarith
  · have : τ - 1 / 2 ≤ k := by
      rcases le_total (max 1 ⌊τ + 1 / 2⌋₊) (n - 1) with h | h
      · have : max 1 ⌊τ + 1 / 2⌋₊ ≤ k := by omega
        have : ⌊τ + 1 / 2⌋₊ ≤ k := by omega
        have : ((⌊τ + 1 / 2⌋₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast this
        linarith
      · have : k = n - 1 := by omega
        rw [this, hn']; linarith
    linarith

end HPC.Plane.BandAux
