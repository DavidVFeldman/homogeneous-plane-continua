import Mathlib

/-!
# Batch 112, auxiliary: unit steps of `ℤ^d` and coordinates along an orthonormal family

Elementary lemmas used by `HPC/Plane/BandNPath.lean` and `HPC/Plane/BandN.lean`.

* `unitN_cases`: a unit step of `ℤ^d` is `± (basis vector)`.
* `dotZ`: the integer dot product; `dotZ_nonpos_of_ne` (distinct unit steps have nonpositive dot
  product), `dotZ_self_unit`, `abs_dotZ_le` (against a vector with entries in `[-1, 1]`).
* `diag_not_mem_span`: the arithmetic of `diagDir_not_mem_span`.
* `vecL e : (Fin d → ℝ) →ₗ[ℝ] E`, `x ↦ Σ x i • e i`, for an orthonormal family `e`: inner products,
  norms, injectivity.
-/

namespace HPC.Plane.BandNAux

open Set

/-! ### Unit steps of `ℤ^d` -/

/-- A unit step of `ℤ^d` is `± (basis vector)`. -/
theorem unitN_cases {d : ℕ} {u : Fin d → ℤ} (h : ∑ i, |u i| = 1) :
    ∃ a, (u a = 1 ∨ u a = -1) ∧ ∀ i, i ≠ a → u i = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h
  have hs : |u a| + ∑ i ∈ Finset.univ.erase a, |u i| = 1 := by
    rw [Finset.add_sum_erase _ (fun i => |u i|) (Finset.mem_univ a)]; exact h
  have hnn : 0 ≤ ∑ i ∈ Finset.univ.erase a, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : 1 ≤ |u a| := Int.one_le_abs ha
  have hz : ∑ i ∈ Finset.univ.erase a, |u i| = 0 := by omega
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _] at hz
  refine ⟨a, ?_, fun i hi => abs_eq_zero.mp (hz i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩))⟩
  have : |u a| = 1 := by omega
  rcases abs_cases (u a) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem unitN_neg {d : ℕ} {u : Fin d → ℤ} (h : ∑ i, |u i| = 1) : ∑ i, |(-u) i| = 1 := by
  simpa using h

/-- The integer dot product. -/
def dotZ {d : ℕ} (u v : Fin d → ℤ) : ℤ := ∑ i, u i * v i

theorem dotZ_eq_single {d : ℕ} {u : Fin d → ℤ} {a : Fin d} (hu : ∀ i, i ≠ a → u i = 0)
    (v : Fin d → ℤ) : dotZ u v = u a * v a := by
  rw [dotZ, Finset.sum_eq_single a (fun i _ hi => by rw [hu i hi, zero_mul]) (by simp)]

theorem dotZ_neg_right {d : ℕ} (u v : Fin d → ℤ) : dotZ u (-v) = -dotZ u v := by
  simp [dotZ, Finset.sum_neg_distrib]

theorem dotZ_comm {d : ℕ} (u v : Fin d → ℤ) : dotZ u v = dotZ v u := by
  simp [dotZ, mul_comm]

/-- Distinct unit steps have nonpositive dot product. -/
theorem dotZ_nonpos_of_ne {d : ℕ} {u v : Fin d → ℤ} (hu : ∑ i, |u i| = 1) (hv : ∑ i, |v i| = 1)
    (hne : u ≠ v) : dotZ u v ≤ 0 := by
  obtain ⟨a, ha, ha'⟩ := unitN_cases hu
  obtain ⟨b, hb, hb'⟩ := unitN_cases hv
  rw [dotZ_eq_single ha']
  by_cases hab : a = b
  · subst hab
    have hne' : u a ≠ v a := by
      intro e; apply hne; funext i
      by_cases hi : i = a
      · rw [hi, e]
      · rw [ha' i hi, hb' i hi]
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2] at hne' ⊢ <;> simp at hne' ⊢
  · rw [hb' a hab, mul_zero]

/-- A unit step and a step other than its opposite have nonnegative dot product. -/
theorem dotZ_nonneg_of_ne_neg {d : ℕ} {u v : Fin d → ℤ} (hu : ∑ i, |u i| = 1)
    (hv : ∑ i, |v i| = 1) (hne : u ≠ -v) : 0 ≤ dotZ u v := by
  have := dotZ_nonpos_of_ne hu (unitN_neg hv) hne
  rw [dotZ_neg_right] at this
  omega

theorem dotZ_self_unit {d : ℕ} {u : Fin d → ℤ} (hu : ∑ i, |u i| = 1) : dotZ u u = 1 := by
  obtain ⟨a, ha, ha'⟩ := unitN_cases hu
  rw [dotZ_eq_single ha']
  rcases ha with h1 | h1 <;> rw [h1] <;> norm_num

theorem abs_dotZ_le {d : ℕ} {u : Fin d → ℤ} (hu : ∑ i, |u i| = 1) {s : Fin d → ℤ}
    (hs : ∀ i, |s i| ≤ 1) : |dotZ u s| ≤ 1 := by
  obtain ⟨a, ha, ha'⟩ := unitN_cases hu
  rw [dotZ_eq_single ha', abs_mul]
  rcases ha with h1 | h1 <;> rw [h1] <;> simpa using hs a

/-- The sign vector of `v`. -/
def signZ {d : ℕ} (v : Fin d → ℤ) : Fin d → ℤ := fun i => Int.sign (v i)

theorem abs_signZ_le {d : ℕ} (v : Fin d → ℤ) (i : Fin d) : |signZ v i| ≤ 1 := by
  simp only [signZ]
  rcases Int.sign_trichotomy (v i) with h | h | h <;> rw [h] <;> norm_num

theorem abs_neg_signZ_le {d : ℕ} (v : Fin d → ℤ) (i : Fin d) : |(-signZ v) i| ≤ 1 := by
  simpa using abs_signZ_le v i

theorem dotZ_signZ {d : ℕ} (v : Fin d → ℤ) : dotZ v (signZ v) = ∑ i, |v i| := by
  simp only [dotZ, signZ, Int.mul_sign_self, Int.natCast_natAbs]

theorem dotZ_signZ_self_le {d : ℕ} (v : Fin d → ℤ) :
    dotZ (signZ v) (signZ v) ≤ dotZ v (signZ v) := by
  simp only [dotZ, signZ]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases lt_trichotomy (v i) 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; omega
  · rw [h]; simp
  · rw [Int.sign_eq_one_of_pos h]; omega

/-- A nonzero integer vector which is not a unit step has `ℓ¹`-norm at least `2`. -/
theorem two_le_l1 {d : ℕ} {v : Fin d → ℤ} (h0 : v ≠ 0) (h1 : ¬ ∑ i, |v i| = 1) :
    2 ≤ ∑ i, |v i| := by
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  have : 1 ≤ ∑ i, |v i| :=
    (Int.one_le_abs ha).trans (Finset.single_le_sum (f := fun i => |v i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
  omega

/-- **The arithmetic of `diagDir_not_mem_span`.** For unit steps `u, u', u''` of `ℤ^d`, `3 ≤ d`:
if `α (u + u') + β (u' + u'')` has all coordinates equal to `lam`, then `lam = 0`. If some axis
is missed by all three steps, that coordinate is `0`; otherwise `d = 3` and the three steps use
three distinct axes, where `(α ε₁, (α + β) ε₂, β ε₃) = (lam, lam, lam)` forces `lam = 0`. -/
theorem diag_not_mem_span {d : ℕ} (hd : 3 ≤ d) {u u' u'' : Fin d → ℤ}
    (hu : ∑ i, |u i| = 1) (hu' : ∑ i, |u' i| = 1) (hu'' : ∑ i, |u'' i| = 1) {α β lam : ℝ}
    (h : ∀ i, α * (u i + u' i) + β * (u' i + u'' i) = lam) : lam = 0 := by
  obtain ⟨a, ha, ha'⟩ := unitN_cases hu
  obtain ⟨b, hb, hb'⟩ := unitN_cases hu'
  obtain ⟨c, hc, hc'⟩ := unitN_cases hu''
  by_cases hex : ∃ i, i ≠ a ∧ i ≠ b ∧ i ≠ c
  · obtain ⟨i, hia, hib, hic⟩ := hex
    have := h i
    rw [ha' i hia, hb' i hib, hc' i hic] at this
    simpa using this.symm
  push_neg at hex
  have hcard : ∀ x y : Fin d, (∀ i, i = x ∨ i = y) → False := by
    intro x y hxy
    have : (Finset.univ : Finset (Fin d)) ⊆ {x, y} := fun i _ => by
      rcases hxy i with h | h <;> simp [h]
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_le_two (a := x) (b := y)
    simp at h1
    omega
  have hab : a ≠ b := fun e => hcard a c fun i => by
    by_cases h1 : i = a
    · exact Or.inl h1
    · exact Or.inr (hex i h1 (e ▸ h1))
  have hbc : b ≠ c := fun e => hcard a b fun i => by
    by_cases h1 : i = a
    · exact Or.inl h1
    · by_cases h2 : i = b
      · exact Or.inr h2
      · exact absurd (hex i h1 h2) (e ▸ h2)
  have hac : a ≠ c := fun e => hcard a b fun i => by
    by_cases h1 : i = a
    · exact Or.inl h1
    · by_cases h2 : i = b
      · exact Or.inr h2
      · exact absurd (hex i h1 h2) (e ▸ h1)
  have e1 := h a
  have e2 := h b
  have e3 := h c
  rw [hb' a hab, hc' a hac] at e1
  rw [ha' b (Ne.symm hab), hc' b hbc] at e2
  rw [ha' c (Ne.symm hac), hb' c (Ne.symm hbc)] at e3
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rcases hc with h3 | h3 <;>
    rw [h1] at e1 <;> rw [h2] at e2 <;> rw [h3] at e3 <;> push_cast at e1 e2 e3 <;> linarith

/-! ### Coordinates along an orthonormal family -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `x ↦ Σ x i • e i`. -/
noncomputable def vecL {d : ℕ} (e : Fin d → E) : (Fin d → ℝ) →ₗ[ℝ] E :=
  Fintype.linearCombination ℝ e

theorem vecL_apply {d : ℕ} (e : Fin d → E) (x : Fin d → ℝ) : vecL e x = ∑ i, x i • e i :=
  Fintype.linearCombination_apply ℝ e x

theorem inner_vecL {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (x y : Fin d → ℝ) :
    inner ℝ (vecL e x) (vecL e y) = ∑ i, x i * y i := by
  rw [vecL_apply, vecL_apply, hon.inner_sum x y Finset.univ]
  simp

theorem norm_vecL_sq {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (x : Fin d → ℝ) :
    ‖vecL e x‖ ^ 2 = ∑ i, x i * x i := by
  rw [← real_inner_self_eq_norm_sq, inner_vecL hon]

theorem vecL_injective {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) :
    Function.Injective (vecL e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := norm_vecL_sq hon x
  rw [hx, norm_zero] at h
  have h0 : ∀ i ∈ Finset.univ, x i * x i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp
      (by rw [← h]; norm_num)
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ i))

/-- Integer vectors as real vectors. -/
def toRN {d : ℕ} (p : Fin d → ℤ) : Fin d → ℝ := fun i => (p i : ℝ)

@[simp] theorem toRN_apply {d : ℕ} (p : Fin d → ℤ) (i : Fin d) : toRN p i = (p i : ℝ) := rfl

theorem toRN_sub {d : ℕ} (p q : Fin d → ℤ) : toRN (p - q) = toRN p - toRN q := by
  funext i; simp

theorem toRN_add {d : ℕ} (p q : Fin d → ℤ) : toRN (p + q) = toRN p + toRN q := by
  funext i; simp

theorem toRN_neg {d : ℕ} (p : Fin d → ℤ) : toRN (-p) = -toRN p := by
  funext i; simp

theorem toRN_injective {d : ℕ} : Function.Injective (toRN (d := d)) := by
  intro p q h
  funext i
  simpa using congrFun h i

theorem inner_vecL_toRN {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (a b : Fin d → ℤ) :
    inner ℝ (vecL e (toRN a)) (vecL e (toRN b)) = ((dotZ a b : ℤ) : ℝ) := by
  rw [inner_vecL hon, dotZ]; push_cast; rfl

theorem norm_vecL_unit {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {u : Fin d → ℤ}
    (hu : ∑ i, |u i| = 1) : ‖vecL e (toRN u)‖ = 1 := by
  have h : ‖vecL e (toRN u)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_vecL_toRN hon, dotZ_self_unit hu]; norm_num
  have h0 := norm_nonneg (vecL e (toRN u))
  nlinarith

theorem norm_vecL_toRN_sq {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (a : Fin d → ℤ) :
    ‖vecL e (toRN a)‖ ^ 2 = ((dotZ a a : ℤ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_vecL_toRN hon]

/-- The inequality behind the `ℓ¹` case of the separation lemma: if `(L - 1) δ ≤ N W` with
`W² ≤ L` and `L ≥ 2`, then `N ≥ (√2/2) δ`. -/
theorem sep_ineq {N W L δ : ℝ} (hN : 0 ≤ N) (hWL : W ^ 2 ≤ L) (hL : 2 ≤ L)
    (hδ : 0 < δ) (h : (L - 1) * δ ≤ N * W) : Real.sqrt 2 / 2 * δ ≤ N := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  by_contra hc
  push_neg at hc
  have hN2 : N ^ 2 < δ ^ 2 / 2 := by nlinarith
  have h1 : ((L - 1) * δ) ^ 2 ≤ (N * W) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) h 2
  have h2 : (N * W) ^ 2 ≤ N ^ 2 * L := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hWL (sq_nonneg N)
  have h3 : N ^ 2 * L < δ ^ 2 / 2 * L := mul_lt_mul_of_pos_right hN2 (by linarith)
  have h4 : (L - 1) ^ 2 * δ ^ 2 < L / 2 * δ ^ 2 := by nlinarith
  have h5 : (L - 1) ^ 2 < L / 2 := lt_of_mul_lt_mul_right h4 (by positivity)
  nlinarith

end HPC.Plane.BandNAux
