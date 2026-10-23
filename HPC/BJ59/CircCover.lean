import Mathlib

/-!
# Batch 202, §5: the shear on the universal cover

* `Ramp.phat P`: the interpolation of joint positions `P : ℤ → ℝ` (commission §5,
  "Interpolation"): constant, equal to `P t`, on `[2t − 2/5, 2t + 7/5]`, and linear from `P t` to
  `P (t+1)` on `[2t + 7/5, 2t + 8/5]`. It is continuous, and equivariant when `P` is.
* `cover g ε₀ C Q c`: the homeomorphism `(u, v) ↦ (g u + ε₀ v, 1/2 + C (g u − u/Q − c) + C ε₀ v)`
  of `ℝ × ℝ`, for every continuous `g`.
-/

namespace HPC.BJ59

open Set Topology Filter

namespace Ramp

/-- The ramp from `7/5` to `8/5`. -/
noncomputable def θ0 (w : ℝ) : ℝ := max 0 (min 1 (5 * (w - 7 / 5)))

theorem continuous_θ0 : Continuous θ0 := by unfold θ0; fun_prop

theorem θ0_mem (w : ℝ) : 0 ≤ θ0 w ∧ θ0 w ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem θ0_of_le {w : ℝ} (h : w ≤ 7 / 5) : θ0 w = 0 := by
  unfold θ0; rw [max_eq_left]; exact (min_le_right _ _).trans (by linarith)

theorem θ0_of_ge {w : ℝ} (h : 8 / 5 ≤ w) : θ0 w = 1 := by
  unfold θ0; rw [min_eq_left (by linarith), max_eq_right zero_le_one]

variable (P : ℤ → ℝ)

/-- The interpolation on piece `t`. -/
noncomputable def F (u : ℝ) (t : ℤ) : ℝ := P t + (P (t + 1) - P t) * θ0 (u - 2 * t)

/-- The piece of `u`: `u ∈ [2t − 2/5, 2t + 8/5)`. -/
noncomputable def piece (u : ℝ) : ℤ := ⌊(u + 2 / 5) / 2⌋

/-- **The interpolated joint positions** `P̂`. -/
noncomputable def phat (u : ℝ) : ℝ := F P u (piece u)

theorem piece_spec (u : ℝ) : 2 * (piece u : ℝ) - 2 / 5 ≤ u ∧ u < 2 * (piece u : ℝ) + 8 / 5 := by
  have h1 := Int.floor_le ((u + 2 / 5) / 2)
  have h2 := Int.lt_floor_add_one ((u + 2 / 5) / 2)
  unfold piece; constructor <;> linarith

theorem piece_eq {u : ℝ} {t : ℤ} (h1 : 2 * (t : ℝ) - 2 / 5 ≤ u) (h2 : u < 2 * (t : ℝ) + 8 / 5) :
    piece u = t := by
  unfold piece
  rw [Int.floor_eq_iff]; constructor <;> linarith

theorem F_succ {u : ℝ} {t : ℤ} (h1 : 2 * (t : ℝ) + 8 / 5 ≤ u) (h2 : u ≤ 2 * (t : ℝ) + 17 / 5) :
    F P u (t + 1) = F P u t := by
  unfold F
  rw [θ0_of_le (w := u - 2 * ((t + 1 : ℤ) : ℝ)) (by push_cast; linarith),
    θ0_of_ge (w := u - 2 * (t : ℝ)) (by linarith)]; ring

/-- On `[2t − 2/5, 2t + 17/5]`, `P̂` is the interpolation of piece `t`. -/
theorem phat_eq {u : ℝ} {t : ℤ} (h1 : 2 * (t : ℝ) - 2 / 5 ≤ u) (h2 : u ≤ 2 * (t : ℝ) + 17 / 5) :
    phat P u = F P u t := by
  unfold phat
  by_cases h : u < 2 * (t : ℝ) + 8 / 5
  · rw [piece_eq h1 h]
  · push_neg at h
    rw [piece_eq (t := t + 1) (by push_cast; linarith) (by push_cast; linarith), F_succ P h h2]

theorem continuous_F (t : ℤ) : Continuous fun u => F P u t := by
  unfold F; have := continuous_θ0; fun_prop

theorem continuous_phat : Continuous (phat P) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  set t : ℤ := ⌈(u₀ + 2 / 5) / 2⌉ - 1
  have h1 := Int.le_ceil ((u₀ + 2 / 5) / 2)
  have h2 := Int.ceil_lt_add_one ((u₀ + 2 / 5) / 2)
  have ht1 : 2 * (t : ℝ) - 2 / 5 < u₀ := by simp only [t]; push_cast; linarith
  have ht2 : u₀ < 2 * (t : ℝ) + 17 / 5 := by simp only [t]; push_cast; linarith
  refine ((continuous_F P t).continuousAt).congr ?_
  filter_upwards [Ioo_mem_nhds ht1 ht2] with u hu
  exact (phat_eq P hu.1.le hu.2.le).symm

/-- Values of `F` lie between the two joint positions. -/
theorem F_mem (u : ℝ) (t : ℤ) : min (P t) (P (t + 1)) ≤ F P u t ∧ F P u t ≤ max (P t) (P (t + 1)) := by
  unfold F
  have h := θ0_mem (u - 2 * t)
  set θ := θ0 (u - 2 * t)
  rcases le_total (P t) (P (t + 1)) with c | c
  · rw [min_eq_left c, max_eq_right c]; constructor <;> nlinarith
  · rw [min_eq_right c, max_eq_left c]; constructor <;> nlinarith

/-- Over the closure of fine link `t`, `P̂` lies between the joint positions `t` and `t + 1`. -/
theorem phat_mem_link {u : ℝ} {t : ℤ} (h1 : 2 * (t : ℝ) ≤ u) (h2 : u ≤ 2 * (t : ℝ) + 3) :
    min (P t) (P (t + 1)) ≤ phat P u ∧ phat P u ≤ max (P t) (P (t + 1)) := by
  rw [phat_eq P (t := t) (by linarith) (by linarith)]; exact F_mem P u t

/-- Over zone `t`, `P̂` is constant, equal to `P (t + 1)`. -/
theorem phat_zone {u : ℝ} {t : ℤ} (h1 : 2 * (t : ℝ) + 8 / 5 ≤ u) (h2 : u ≤ 2 * (t : ℝ) + 17 / 5) :
    phat P u = P (t + 1) := by
  rw [phat_eq P (by linarith) h2]; unfold F; rw [θ0_of_ge (by linarith)]; ring

/-- `P̂` is a value of `F` on the piece of `u`. -/
theorem phat_mem (u : ℝ) :
    min (P (piece u)) (P (piece u + 1)) ≤ phat P u ∧ phat P u ≤ max (P (piece u)) (P (piece u + 1)) :=
  F_mem P u _

/-- Equivariance. -/
theorem phat_add {D : ℤ} {c : ℝ} (hP : ∀ t, P (t + D) = P t + c) (u : ℝ) :
    phat P (u + 2 * D) = phat P u + c := by
  have hp : piece (u + 2 * D) = piece u + D := by
    have := piece_spec u
    exact piece_eq (by push_cast; linarith) (by push_cast; linarith)
  unfold phat
  rw [hp]; unfold F
  rw [show piece u + D + 1 = (piece u + 1) + D by ring, hP, hP]
  push_cast
  rw [show u + 2 * (D : ℝ) - 2 * ((piece u : ℝ) + D) = u - 2 * piece u by ring]; ring

end Ramp

/-! ### The shear on the cover -/

section Cover

variable (g : ℝ → ℝ) (hg : Continuous g) {ε₀ C Q : ℝ} (c : ℝ)

/-- **The shear on the universal cover** (commission §5): a homeomorphism of `ℝ × ℝ` for every
continuous `g`. -/
noncomputable def cover (hg : Continuous g) (hε₀ : ε₀ ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0) :
    ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (g p.1 + ε₀ * p.2, 1 / 2 + C * (g p.1 - p.1 / Q - c) + C * ε₀ * p.2)
  invFun q := (Q * (q.1 - (q.2 - 1 / 2) / C - c),
    (q.1 - g (Q * (q.1 - (q.2 - 1 / 2) / C - c))) / ε₀)
  left_inv p := by
    obtain ⟨u, v⟩ := p
    have e : Q * (g u + ε₀ * v - (1 / 2 + C * (g u - u / Q - c) + C * ε₀ * v - 1 / 2) / C - c) = u := by
      field_simp; ring
    simp only [e]
    ext <;> simp only
    field_simp; ring
  right_inv q := by
    obtain ⟨U, V⟩ := q
    ext <;> simp only
    · field_simp; ring
    · field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem cover_apply (hε₀ : ε₀ ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0) (p : ℝ × ℝ) :
    cover g c hg hε₀ hC hQ p =
      (g p.1 + ε₀ * p.2, 1 / 2 + C * (g p.1 - p.1 / Q - c) + C * ε₀ * p.2) := rfl

theorem cover_symm_apply (hε₀ : ε₀ ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0) (q : ℝ × ℝ) :
    (cover g c hg hε₀ hC hQ).symm q = (Q * (q.1 - (q.2 - 1 / 2) / C - c),
      (q.1 - g (Q * (q.1 - (q.2 - 1 / 2) / C - c))) / ε₀) := rfl

/-- Equivariance of the shear. -/
theorem cover_add {D A : ℝ} (hgD : ∀ u, g (u + D) = g u + A) (hDA : D / Q = A)
    (hε₀ : ε₀ ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0) (p : ℝ × ℝ) :
    cover g c hg hε₀ hC hQ (p.1 + D, p.2) = cover g c hg hε₀ hC hQ p + (A, 0) := by
  rw [cover_apply, cover_apply, hgD]
  ext <;> simp only [Prod.fst_add, Prod.snd_add]
  · ring
  · rw [show (p.1 + D) / Q = p.1 / Q + D / Q by ring, hDA]; ring

theorem cover_symm_add {D A : ℝ} (hgD : ∀ u, g (u + D) = g u + A) (hDA : D / Q = A)
    (hε₀ : ε₀ ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0) (q : ℝ × ℝ) :
    (cover g c hg hε₀ hC hQ).symm (q.1 + A, q.2) = (cover g c hg hε₀ hC hQ).symm q + (D, 0) := by
  apply (cover g c hg hε₀ hC hQ).injective
  rw [Homeomorph.apply_symm_apply]
  have := cover_add g hg c hgD hDA hε₀ hC hQ ((cover g c hg hε₀ hC hQ).symm q)
  rw [Homeomorph.apply_symm_apply] at this
  rw [show (cover g c hg hε₀ hC hQ).symm q + (D, 0) =
    (((cover g c hg hε₀ hC hQ).symm q).1 + D, ((cover g c hg hε₀ hC hQ).symm q).2) by
      ext <;> simp, this]
  ext <;> simp

end Cover

end HPC.BJ59
