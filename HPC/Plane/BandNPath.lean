import HPC.Plane.BandChain
import HPC.Plane.BandNAux

/-!
# Batch 112, items 1–3: lattice paths in `ℤ^d`, the piecewise-linear path, the band

Part (A) of the skeleton `BandN.lean` (split off for length; imported by `HPC/Plane/BandN.lean`).
Definitions and statements are the skeleton's, in the skeleton's order; the shape changes are
listed in the module doc of `HPC/Plane/BandN.lean`.

Coordinates: `vecL e x = Σ x i • e i` (`BandNAux`), so `latticePtN e δ p = δ • vecL e (toRN p)`.
-/

namespace HPC.Plane

open Set Metric BandAux BandNAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### (A) Lattice paths in `ℤ^d` -/

/-- A unit step of `ℤ^d`. -/
def IsUnitStepN {d : ℕ} (p q : Fin d → ℤ) : Prop := ∑ i, |q i - p i| = 1

/-- **A self-avoiding lattice path** in `ℤ^d` with `n` steps. -/
structure LatticePathN (d n : ℕ) where
  c : ℕ → (Fin d → ℤ)
  injOn : InjOn c (Iic n)
  step : ∀ i, i < n → IsUnitStepN (c i) (c (i + 1))

/-- The lattice point `p` placed in `E` along an orthonormal family `e`, at mesh `δ`. -/
def latticePtN {d : ℕ} (e : Fin d → E) (δ : ℝ) (p : Fin d → ℤ) : E :=
  δ • ∑ i, (p i : ℝ) • e i

noncomputable def stepMidN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (i : ℕ) : E :=
  midpoint ℝ (latticePtN e δ (P.c i)) (latticePtN e δ (P.c (i + 1)))

/-- The stretch triangle, as in `Band.lean`. -/
def stretchTriN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) (k : ℕ) :
    Set E :=
  convexHull ℝ ({latticePtN e δ (P.c k)} ∪
    (if 0 < k then {stepMidN e δ P (k - 1)} else ∅) ∪
    (if k < n then {stepMidN e δ P k} else ∅))

def polyPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) : Set E :=
  ⋃ i ∈ Iio n, segment ℝ (latticePtN e δ (P.c i)) (latticePtN e δ (P.c (i + 1)))

namespace BandN

theorem latticePtN_eq {d : ℕ} (e : Fin d → E) (δ : ℝ) (p : Fin d → ℤ) :
    latticePtN e δ p = δ • vecL e (toRN p) := by
  rw [latticePtN, vecL_apply]; rfl

theorem latticePtN_sub {d : ℕ} (e : Fin d → E) (δ : ℝ) (p q : Fin d → ℤ) :
    latticePtN e δ p - latticePtN e δ q = δ • vecL e (toRN (p - q)) := by
  rw [latticePtN_eq, latticePtN_eq, toRN_sub, map_sub, smul_sub]

/-- The step vector `c (i+1) - c i` is a unit step (for `i < n`). -/
theorem stepN_unit {d n : ℕ} (P : LatticePathN d n) {i : ℕ} (hi : i < n) :
    ∑ j, |(P.c (i + 1) - P.c i) j| = 1 := by
  simpa using P.step i hi

/-- The step vector `c (k-1) - c k` into a stretch from behind is a unit step. -/
theorem armN_left_unit {d n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∑ j, |(P.c (k - 1) - P.c k) j| = 1 := by
  have h := unitN_neg (stepN_unit P (i := k - 1) (by omega))
  rw [Nat.sub_add_cancel hk, neg_sub] at h
  exact h

theorem cN_ne {d n : ℕ} (P : LatticePathN d n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (h : i ≠ j) :
    P.c i ≠ P.c j := fun e => h (P.injOn (mem_Iic.mpr hi) (mem_Iic.mpr hj) e)

theorem stepMidN_sub_left {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (k : ℕ) :
    stepMidN e δ P k - latticePtN e δ (P.c k) = (δ / 2) • vecL e (toRN (P.c (k + 1) - P.c k)) := by
  rw [stepMidN, midpoint_eq_smul_add, invOf_eq_inv, latticePtN_eq, latticePtN_eq, toRN_sub,
    map_sub]
  module

theorem stepMidN_sub_right {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    {k : ℕ} (hk : 0 < k) :
    stepMidN e δ P (k - 1) - latticePtN e δ (P.c k) =
      (δ / 2) • vecL e (toRN (P.c (k - 1) - P.c k)) := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [stepMidN, hk', midpoint_eq_smul_add, invOf_eq_inv, latticePtN_eq, latticePtN_eq, toRN_sub,
    map_sub]
  module

/-- The stretch triangle lies in a half-space `⟪· - c k, v⟫ ≤ (δ/2) α` as soon as both step
vectors at `c k` do. -/
theorem stretchTriN_inner_le {d : ℕ} (e : Fin d → E) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (P : LatticePathN d n) (k : ℕ) (v : E) {α : ℝ} (hα : 0 ≤ α)
    (h1 : 0 < k → inner ℝ (vecL e (toRN (P.c (k - 1) - P.c k))) v ≤ α)
    (h2 : k < n → inner ℝ (vecL e (toRN (P.c (k + 1) - P.c k))) v ≤ α) :
    ∀ p ∈ stretchTriN e δ P k, inner ℝ (p - latticePtN e δ (P.c k)) v ≤ δ / 2 * α := by
  set c := latticePtN e δ (P.c k)
  have hconv : Convex ℝ {p : E | inner ℝ (p - c) v ≤ δ / 2 * α} := by
    have : {p : E | inner ℝ (p - c) v ≤ δ / 2 * α} =
        {p : E | inner ℝ p v ≤ δ / 2 * α + inner ℝ c v} := by
      ext p; simp only [mem_setOf_eq, inner_sub_left]; constructor <;> intro h <;> linarith
    rw [this]
    exact convex_halfSpace_le
      ⟨fun x y => inner_add_left x y v, fun r x => real_inner_smul_left x v r⟩ _
  refine convexHull_min ?_ hconv
  intro x hx
  rcases hx with (hx | hx) | hx
  · rw [mem_singleton_iff] at hx; subst hx
    show inner ℝ (c - c) v ≤ δ / 2 * α
    rw [sub_self, inner_zero_left]; positivity
  · split_ifs at hx with hk
    · rw [mem_singleton_iff] at hx; subst hx
      show inner ℝ (stepMidN e δ P (k - 1) - c) v ≤ δ / 2 * α
      rw [stepMidN_sub_right e δ P hk, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left (h1 hk) (by positivity)
    · exact absurd hx (notMem_empty _)
  · split_ifs at hx with hk
    · rw [mem_singleton_iff] at hx; subst hx
      show inner ℝ (stepMidN e δ P k - c) v ≤ δ / 2 * α
      rw [stepMidN_sub_left, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left (h2 hk) (by positivity)
    · exact absurd hx (notMem_empty _)

theorem latticePtN_mem_polyPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    {k : ℕ} (hk : k < n) : latticePtN e δ (P.c k) ∈ polyPathN e δ P :=
  mem_biUnion (x := k) (mem_Iio.mpr hk) (left_mem_segment ℝ _ _)

theorem latticePtN_mem_polyPathN' {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) : latticePtN e δ (P.c k) ∈ polyPathN e δ P := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact mem_biUnion (x := j) (mem_Iio.mpr (by omega)) (right_mem_segment ℝ _ _)

end BandN

open BandN

theorem stretchTriN_subset_ball {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk : k ≤ n) :
    stretchTriN e δ P k ⊆ closedBall (latticePtN e δ (P.c k)) (δ / 2) := by
  refine convexHull_min ?_ (convex_closedBall _ _)
  intro x hx
  rcases hx with (hx | hx) | hx
  · rw [mem_singleton_iff] at hx; subst hx; exact mem_closedBall_self (by positivity)
  · split_ifs at hx with hk'
    · rw [mem_singleton_iff] at hx; subst hx
      rw [mem_closedBall, dist_eq_norm, stepMidN_sub_right e δ P hk', norm_smul,
        norm_vecL_unit hon (armN_left_unit P hk' hk), Real.norm_of_nonneg (by positivity)]
      linarith
    · exact absurd hx (notMem_empty _)
  · split_ifs at hx with hk'
    · rw [mem_singleton_iff] at hx; subst hx
      rw [mem_closedBall, dist_eq_norm, stepMidN_sub_left, norm_smul,
        norm_vecL_unit hon (stepN_unit P hk'), Real.norm_of_nonneg (by positivity)]
      linarith
    · exact absurd hx (notMem_empty _)

theorem stretchTriN_subset_thickening {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (P : LatticePathN d n) {k : ℕ} (hk : k ≤ n) :
    stretchTriN e δ P k ⊆ cthickening (δ / 2) (polyPathN e δ P) := by
  intro p hp
  have hc : latticePtN e δ (P.c k) ∈ polyPathN e δ P := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact latticePtN_mem_polyPathN e δ P hn
    · exact latticePtN_mem_polyPathN' e δ P h hk
  exact mem_cthickening_of_dist_le p _ _ _ hc (stretchTriN_subset_ball hon hδ P hk hp)

/-- **Separation of nonadjacent stretches** in `ℤ^d` (the proof of `stretchTri_separated`: a
single separating direction, `w = Σ sign • e i` in the `ℓ¹` case, `w = c k' - c k` in the
lattice-adjacent case). -/
theorem stretchTriN_separated {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk' : k' ≤ n) (h : k + 2 ≤ k') :
    ∀ p ∈ stretchTriN e δ P k, ∀ q ∈ stretchTriN e δ P k',
      Real.sqrt 2 / 2 * δ ≤ dist p q := by
  intro p hp q hq
  set ck := latticePtN e δ (P.c k)
  set ck' := latticePtN e δ (P.c k')
  set dv := P.c k' - P.c k with hdv
  have hkk' : P.c k ≠ P.c k' := cN_ne P (by omega) hk' (by omega)
  have hdiff : ck' - ck = δ • vecL e (toRN dv) := latticePtN_sub e δ _ _
  have hsplit : ∀ v : E, inner ℝ (q - p) v =
      inner ℝ (q - ck') v + inner ℝ (ck' - ck) v - inner ℝ (p - ck) v := by
    intro v
    have : q - p = (q - ck') + (ck' - ck) - (p - ck) := by abel
    rw [this, inner_sub_left, inner_add_left]
  have hdist : dist p q = ‖q - p‖ := by rw [dist_comm, dist_eq_norm]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have armk1 : 0 < k → ∑ j, |(P.c (k - 1) - P.c k) j| = 1 :=
    fun hk => armN_left_unit P hk (by omega)
  have armk2 : ∑ j, |(P.c (k + 1) - P.c k) j| = 1 := stepN_unit P (by omega)
  have armk'1 : ∑ j, |(P.c (k' - 1) - P.c k') j| = 1 := armN_left_unit P (by omega) hk'
  have armk'2 : k' < n → ∑ j, |(P.c (k' + 1) - P.c k') j| = 1 := fun h => stepN_unit P h
  by_cases hu : ∑ j, |dv j| = 1
  · -- lattice-adjacent
    set v := vecL e (toRN dv)
    have hv : ‖v‖ = 1 := norm_vecL_unit hon hu
    have hnd := unitN_neg hu
    have hp' := stretchTriN_inner_le e hδ P k v le_rfl
      (fun hk => by
        rw [inner_vecL_toRN hon]
        have := dotZ_nonpos_of_ne (armk1 hk) hu (fun e => cN_ne P (by omega) hk' (by omega)
          (sub_left_inj.mp e))
        exact_mod_cast this)
      (fun _ => by
        rw [inner_vecL_toRN hon]
        have := dotZ_nonpos_of_ne armk2 hu (fun e => cN_ne P (by omega) hk' (by omega)
          (sub_left_inj.mp e))
        exact_mod_cast this) p hp
    have hq' := stretchTriN_inner_le e hδ P k' (vecL e (toRN (-dv))) le_rfl
      (fun _ => by
        rw [inner_vecL_toRN hon]
        have := dotZ_nonpos_of_ne armk'1 hnd (fun e => cN_ne P (by omega) (by omega)
          (show k' - 1 ≠ k by omega) (by
            have : P.c (k' - 1) - P.c k' = P.c k - P.c k' := by rw [e, hdv]; abel
            exact sub_left_inj.mp this))
        exact_mod_cast this)
      (fun hkn => by
        rw [inner_vecL_toRN hon]
        have := dotZ_nonpos_of_ne (armk'2 hkn) hnd (fun e => cN_ne P (by omega) (by omega)
          (show k' + 1 ≠ k by omega) (by
            have : P.c (k' + 1) - P.c k' = P.c k - P.c k' := by rw [e, hdv]; abel
            exact sub_left_inj.mp this))
        exact_mod_cast this) q hq
    rw [toRN_neg, map_neg, inner_neg_right] at hq'
    have hc : inner ℝ (ck' - ck) v = δ := by
      rw [hdiff, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]; ring
    have h1 := hsplit v
    have h2 : inner ℝ (q - p) v ≤ ‖q - p‖ := by
      have := real_inner_le_norm (q - p) v
      rwa [hv, mul_one] at this
    rw [hdist]
    nlinarith
  · -- `ℓ¹`-distance at least `2`
    have hd0 : dv ≠ 0 := fun h0 => hkk' (sub_eq_zero.mp h0).symm
    have hd2 := two_le_l1 hd0 hu
    set s := signZ dv
    set w := vecL e (toRN s)
    have hp' := stretchTriN_inner_le e hδ P k w zero_le_one
      (fun hk => by
        rw [inner_vecL_toRN hon]
        exact_mod_cast (abs_le.mp (abs_dotZ_le (armk1 hk) (abs_signZ_le dv))).2)
      (fun _ => by
        rw [inner_vecL_toRN hon]
        exact_mod_cast (abs_le.mp (abs_dotZ_le armk2 (abs_signZ_le dv))).2) p hp
    have hq' := stretchTriN_inner_le e hδ P k' (vecL e (toRN (-s))) zero_le_one
      (fun _ => by
        rw [inner_vecL_toRN hon]
        exact_mod_cast (abs_le.mp (abs_dotZ_le armk'1 (abs_neg_signZ_le dv))).2)
      (fun hkn => by
        rw [inner_vecL_toRN hon]
        exact_mod_cast (abs_le.mp (abs_dotZ_le (armk'2 hkn) (abs_neg_signZ_le dv))).2) q hq
    rw [toRN_neg, map_neg, inner_neg_right] at hq'
    have hc : inner ℝ (ck' - ck) w = δ * ((∑ j, |dv j| : ℤ) : ℝ) := by
      rw [hdiff, real_inner_smul_left, inner_vecL_toRN hon, dotZ_signZ]
    have hw2 : ‖w‖ ^ 2 ≤ ((∑ j, |dv j| : ℤ) : ℝ) := by
      rw [norm_vecL_toRN_sq hon, ← dotZ_signZ]
      exact_mod_cast dotZ_signZ_self_le dv
    have h1 := hsplit w
    have h2 : inner ℝ (q - p) w ≤ ‖q - p‖ * ‖w‖ := real_inner_le_norm (q - p) w
    have hL : (2 : ℝ) ≤ ((∑ j, |dv j| : ℤ) : ℝ) := by exact_mod_cast hd2
    rw [hdist]
    refine sep_ineq (norm_nonneg _) hw2 hL hδ ?_
    nlinarith

/-- **The piecewise-linear path through the midpoints** (the `roundedPath` of `Band.lean`, same
hat-function formula): `Γ (i + 1/2) = m_i`, linear in between; defined and continuous on `ℝ`;
stretch `k` (`1 ≤ k < n`) on `[k - 1/2, k + 1/2]`. -/
noncomputable def plPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    ℝ → E :=
  fun τ => ∑ j ∈ Finset.range n, hat (τ - 1 / 2 - j) • stepMidN e δ P j

theorem continuous_plPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    Continuous (plPathN e δ P) :=
  continuous_finset_sum _ fun _ _ =>
    (continuous_hat.comp ((continuous_id.sub continuous_const).sub continuous_const)).smul
      continuous_const

namespace BandN

theorem plPathN_stretch {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k < n) {s τ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : τ = k - 1 / 2 + s) :
    plPathN e δ P τ = (1 - s) • stepMidN e δ P (k - 1) + s • stepMidN e δ P k :=
  sum_hat_two n _ hk1 hkn hs0 hs1 hτ

theorem plPathN_half {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) {j : ℕ}
    (hj : j < n) : plPathN e δ P (j + 1 / 2) = stepMidN e δ P j :=
  Band.sum_hat_half n _ hj

/-- Midpoints in coordinates: `stepMidN = δ • vecL (midCN j)`. -/
noncomputable def midCN {d n : ℕ} (P : LatticePathN d n) (j : ℕ) : Fin d → ℝ :=
  (1 / 2 : ℝ) • (toRN (P.c j) + toRN (P.c (j + 1)))

theorem stepMidN_eq {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) (j : ℕ) :
    stepMidN e δ P j = δ • vecL e (midCN P j) := by
  rw [stepMidN, midpoint_eq_smul_add, invOf_eq_inv, latticePtN_eq, latticePtN_eq, midCN,
    map_smul, map_add]
  module

/-- On stretch `k`, `Γ = δ • vecL ((1 - s) • midCN (k-1) + s • midCN k)`. -/
theorem plPathN_stretch' {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k < n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    plPathN e δ P (k - 1 / 2 + s) =
      δ • vecL e ((1 - s) • midCN P (k - 1) + s • midCN P k) := by
  rw [plPathN_stretch e δ P hk1 hkn hs0 hs1 rfl, stepMidN_eq, stepMidN_eq, map_add, map_smul,
    map_smul]
  module

end BandN

theorem plPathN_mem_stretchTriN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {τ : ℝ}
    (hτ : τ ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    plPathN e δ P τ ∈ stretchTriN e δ P k := by
  have hs0 : 0 ≤ τ - k + 1 / 2 := by linarith [hτ.1]
  have hs1 : τ - k + 1 / 2 ≤ 1 := by linarith [hτ.2]
  rw [plPathN_stretch e δ P hk1 hkn hs0 hs1 (by ring)]
  refine segment_subset_convexHull ?_ ?_ ⟨1 - (τ - k + 1 / 2), τ - k + 1 / 2, by linarith, hs0,
    by ring, rfl⟩
  · exact Or.inl (Or.inr (by rw [if_pos (by omega)]; rfl))
  · exact Or.inr (by rw [if_pos hkn]; rfl)

namespace BandN

/-- Two parameters of `Γ` that are in stretches `k ≤ k'`, with `Γ τ - Γ τ'` a vector of length
`< (√2/2) δ`, have `k' ≤ k + 1`. -/
theorem stretch_close {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hk1' : 1 ≤ k')
    (hkn' : k' < n) {s s' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs0' : 0 ≤ s') (hs1' : s' ≤ 1)
    (h : dist (plPathN e δ P (k - 1 / 2 + s)) (plPathN e δ P (k' - 1 / 2 + s')) <
      Real.sqrt 2 / 2 * δ) : k' ≤ k + 1 := by
  by_contra hc
  exact absurd (stretchTriN_separated hon hδ P hkn'.le (by omega) _
    (plPathN_mem_stretchTriN e δ P hk1 hkn ⟨by linarith, by linarith⟩) _
    (plPathN_mem_stretchTriN e δ P hk1' hkn' ⟨by linarith, by linarith⟩)) (not_le.mpr h)

/-- The coordinates of the difference of `Γ` at stretch `k` and stretch `k` or `k + 1`. -/
theorem midCN_sub_same {d n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (s s' : ℝ)
    (i : Fin d) :
    ((1 - s) • midCN P (k - 1) + s • midCN P k - ((1 - s') • midCN P (k - 1) + s' • midCN P k)) i
      = (s - s') / 2 * (((P.c k - P.c (k - 1)) i : ℤ) + ((P.c (k + 1) - P.c k) i : ℤ)) := by
  have hk : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  simp only [midCN, hk, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, toRN_apply, smul_eq_mul]
  push_cast; ring

theorem midCN_sub_next {d n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (s s' : ℝ)
    (i : Fin d) :
    ((1 - s) • midCN P (k - 1) + s • midCN P k -
        ((1 - s') • midCN P (k + 1 - 1) + s' • midCN P (k + 1))) i
      = -(1 - s) / 2 * (((P.c k - P.c (k - 1)) i : ℤ) + ((P.c (k + 1) - P.c k) i : ℤ)) +
        -s' / 2 * (((P.c (k + 1) - P.c k) i : ℤ) + ((P.c (k + 2) - P.c (k + 1)) i : ℤ)) := by
  have hk : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  simp only [midCN, hk, Nat.add_sub_cancel, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, toRN_apply,
    smul_eq_mul]
  push_cast; ring

/-- Consecutive steps are not opposite (the path is self-avoiding). -/
theorem step_ne_neg {d n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    P.c k - P.c (k - 1) ≠ -(P.c (k + 1) - P.c k) := by
  intro h
  apply cN_ne P (by omega) (by omega) (show k - 1 ≠ k + 1 by omega)
  have : P.c (k + 1) = P.c k - (P.c k - P.c (k - 1)) := by rw [h]; abel
  rw [this]; abel

theorem stepN_unit' {d n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∑ j, |(P.c k - P.c (k - 1)) j| = 1 := by
  have h := stepN_unit P (i := k - 1) (by omega)
  rwa [Nat.sub_add_cancel hk1] at h

/-- `Γ` restricted to two stretches `k ≤ k'`: equal values force equal parameters. -/
theorem plPathN_eq_aux {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hk1' : 1 ≤ k')
    (hkn' : k' < n) {s s' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs0' : 0 ≤ s') (hs1' : s' ≤ 1)
    (hkk : k ≤ k') (h : plPathN e δ P (k - 1 / 2 + s) = plPathN e δ P (k' - 1 / 2 + s')) :
    (k : ℝ) - 1 / 2 + s = k' - 1 / 2 + s' := by
  have hk2 := stretch_close hon hδ P hk1 hkn hk1' hkn' hs0 hs1 hs0' hs1'
    (by rw [h, dist_self]; positivity)
  rw [plPathN_stretch' e δ P hk1 hkn hs0 hs1, plPathN_stretch' e δ P hk1' hkn' hs0' hs1'] at h
  have hc := congrFun (vecL_injective hon (smul_right_injective E hδ.ne' h))
  rcases (by omega : k = k' ∨ k' = k + 1) with rfl | rfl
  · -- the same stretch: the chord `m_k - m_{k-1}` is nonzero
    have hne : P.c (k + 1) - P.c k + (P.c k - P.c (k - 1)) ≠ 0 := by
      intro h0
      apply step_ne_neg P hk1 hkn
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
    obtain ⟨i, hi⟩ : ∃ i, (P.c (k + 1) - P.c k + (P.c k - P.c (k - 1))) i ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hne (funext hcon)
    have h1 := midCN_sub_same P hk1 s s' i
    rw [sub_eq_zero.mpr (funext hc)] at h1
    have hi' : (((P.c k - P.c (k - 1)) i : ℤ) : ℝ) + ((P.c (k + 1) - P.c k) i : ℤ) ≠ 0 := by
      have : ((P.c k - P.c (k - 1)) i + (P.c (k + 1) - P.c k) i : ℤ) ≠ 0 := by
        rw [add_comm]; simpa using hi
      exact_mod_cast this
    have : (s - s') / 2 = 0 := by
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact h2
      · exact absurd h2 hi'
    linarith
  · -- adjacent stretches: inner product with the common step `u_k`
    set u := P.c (k + 1) - P.c k
    have hu := stepN_unit P hkn
    have hu0 := stepN_unit' P hk1 hkn.le
    have hu2 : ∑ j, |(P.c (k + 2) - P.c (k + 1)) j| = 1 := stepN_unit P hkn'
    have hd1 : 0 ≤ dotZ (P.c k - P.c (k - 1)) u :=
      dotZ_nonneg_of_ne_neg hu0 hu (step_ne_neg P hk1 hkn)
    have hd2 : 0 ≤ dotZ (P.c (k + 2) - P.c (k + 1)) u := by
      have := step_ne_neg P (k := k + 1) (by omega) hkn'
      have h' : P.c (k + 1 + 1) - P.c (k + 1) ≠ -u := by
        intro e; apply this
        rw [Nat.add_sub_cancel, show k + 1 + 1 = k + 2 by ring] at *
        rw [e]; simp [u]
      rw [show k + 1 + 1 = k + 2 by ring] at h'
      exact dotZ_nonneg_of_ne_neg hu2 hu h'
    have hsum : ∑ i, (-(1 - s) / 2 * (((P.c k - P.c (k - 1)) i : ℤ) + ((P.c (k + 1) - P.c k) i : ℤ))
        + -s' / 2 * (((P.c (k + 1) - P.c k) i : ℤ) + ((P.c (k + 2) - P.c (k + 1)) i : ℤ))) *
          (u i : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← midCN_sub_next P hk1 s s' i, sub_eq_zero.mpr (funext hc)]
      simp
    have hexp : ∑ i, (-(1 - s) / 2 * (((P.c k - P.c (k - 1)) i : ℤ) + ((P.c (k + 1) - P.c k) i : ℤ))
        + -s' / 2 * (((P.c (k + 1) - P.c k) i : ℤ) + ((P.c (k + 2) - P.c (k + 1)) i : ℤ))) *
          (u i : ℝ) = -(1 - s) / 2 * (((dotZ (P.c k - P.c (k - 1)) u : ℤ) : ℝ) + dotZ u u) +
            -s' / 2 * (((dotZ u u : ℤ) : ℝ) + dotZ (P.c (k + 2) - P.c (k + 1)) u) := by
      simp only [dotZ]
      push_cast
      simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [u]
      ring
    rw [hexp, dotZ_self_unit hu] at hsum
    have hd1' : (0 : ℝ) ≤ ((dotZ (P.c k - P.c (k - 1)) u : ℤ) : ℝ) := by exact_mod_cast hd1
    have hd2' : (0 : ℝ) ≤ ((dotZ (P.c (k + 2) - P.c (k + 1)) u : ℤ) : ℝ) := by exact_mod_cast hd2
    push_cast at hsum
    have h1 : 0 ≤ (1 - s) * ((dotZ (P.c k - P.c (k - 1)) u : ℝ) + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ s' * (1 + (dotZ (P.c (k + 2) - P.c (k + 1)) u : ℝ)) :=
      mul_nonneg hs0' (by linarith)
    have h3 : (1 - s) * ((dotZ (P.c k - P.c (k - 1)) u : ℝ) + 1) = 0 := by linarith
    have h4 : s' * (1 + (dotZ (P.c (k + 2) - P.c (k + 1)) u : ℝ)) = 0 := by linarith
    have h5 : 1 - s = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · linarith
    have h6 : s' = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · linarith
    push_cast
    linarith

end BandN

/-- `Γ` is injective on `[1/2, n - 1/2]` (each stretch is a segment; adjacent stretches meet only
at the common midpoint, lying in opposite half-spaces of `⟪· - m_k, u_k⟫`; nonadjacent ones are
separated). -/
theorem plPathN_injOn {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) :
    InjOn (plPathN e δ P) (Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2)) := by
  intro τ hτ τ' hτ' h
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  obtain ⟨k', hk1', hkn', s', hs0', hs1', rfl⟩ := exists_stretch hn hτ'.1 hτ'.2
  rcases le_total k k' with hkk | hkk
  · exact plPathN_eq_aux hon hδ P hk1 hkn hk1' hkn' hs0 hs1 hs0' hs1' hkk h
  · exact (plPathN_eq_aux hon hδ P hk1' hkn' hk1 hkn hs0' hs1' hs0 hs1 hkk h.symm).symm

/-- The transverse direction `w = (Σ e i) / √d`. -/
noncomputable def diagDir {d : ℕ} (e : Fin d → E) : E := (Real.sqrt d)⁻¹ • ∑ i, e i

theorem diagDir_eq {d : ℕ} (e : Fin d → E) :
    diagDir e = (Real.sqrt d)⁻¹ • vecL e (fun _ => 1) := by
  rw [diagDir, vecL_apply]; simp

theorem norm_diagDir {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (hd : 0 < d) :
    ‖diagDir e‖ = 1 := by
  have h2 : ‖vecL e (fun _ => (1 : ℝ))‖ ^ 2 = d := by
    rw [norm_vecL_sq hon]; simp
  have h3 : ‖vecL e (fun _ => (1 : ℝ))‖ = Real.sqrt d := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rw [diagDir_eq, norm_smul, h3, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_cancel₀ hs.ne']

/-- **No nonzero multiple of `w` lies in the span of two consecutive chords.** For unit steps
`u, u', u''` of `ℤ^d` and `3 ≤ d`: if `α • (u + u') + β • (u' + u'') = λ • Σ e i` then `λ = 0`.
(The header's case analysis. Shape change: the hypotheses `u' ≠ -u`, `u'' ≠ -u'` of the skeleton
are not needed and are dropped.) -/
theorem diagDir_not_mem_span {d : ℕ} (hd : 3 ≤ d) {u u' u'' : Fin d → ℤ}
    (hu : ∑ i, |u i| = 1) (hu' : ∑ i, |u' i| = 1) (hu'' : ∑ i, |u'' i| = 1) {α β lam : ℝ}
    (h : ∀ i, α * (u i + u' i) + β * (u' i + u'' i) = lam) : lam = 0 :=
  diag_not_mem_span hd hu hu' hu'' h

/-- **The band with constant transverse direction**: `(τ, t) ↦ Γ τ + (t δ) • w`. -/
noncomputable def bandN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (q : ℝ × ℝ) : E :=
  plPathN e δ P q.1 + (q.2 * δ) • diagDir e

theorem continuous_bandN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    Continuous (bandN e δ P) :=
  ((continuous_plPathN e δ P).comp continuous_fst).add
    ((continuous_snd.mul continuous_const).smul continuous_const)

namespace BandN

/-- The band step of `bandN_injOn` for stretches `k ≤ k'`: if `Γ τ - Γ τ' = r • w` with
`|r| < δ/4`, then `r = 0`. -/
theorem bandN_aux {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k < n)
    (hk1' : 1 ≤ k') (hkn' : k' < n) {s s' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs0' : 0 ≤ s')
    (hs1' : s' ≤ 1) (hkk : k ≤ k') {r : ℝ} (hr : |r| < δ / 4)
    (h : plPathN e δ P (k - 1 / 2 + s) - plPathN e δ P (k' - 1 / 2 + s') = r • diagDir e) :
    r = 0 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hk2 := stretch_close hon hδ P hk1 hkn hk1' hkn' hs0 hs1 hs0' hs1' (by
    rw [dist_eq_norm, h, norm_smul, norm_diagDir hon (by omega), mul_one, Real.norm_eq_abs]
    nlinarith)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))
  rw [plPathN_stretch' e δ P hk1 hkn hs0 hs1, plPathN_stretch' e δ P hk1' hkn' hs0' hs1',
    ← smul_sub, ← map_sub, diagDir_eq, smul_smul, ← map_smul, ← map_smul] at h
  have hc := congrFun (vecL_injective hon h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at hc
  have hlam : r * (Real.sqrt d)⁻¹ = 0 := by
    rcases (by omega : k = k' ∨ k' = k + 1) with rfl | rfl
    · refine diagDir_not_mem_span hd (stepN_unit' P hk1 hkn.le) (stepN_unit P hkn)
        (stepN_unit P hkn) (α := δ * ((s - s') / 2)) (β := 0) fun i => ?_
      have := hc i
      rw [midCN_sub_same P hk1 s s' i] at this
      have h' : δ * ((s - s') / 2 * (((P.c k - P.c (k - 1)) i : ℤ) + ((P.c (k + 1) - P.c k) i : ℤ)))
          = r * (Real.sqrt d)⁻¹ := this
      linear_combination h'
    · refine diagDir_not_mem_span hd (stepN_unit' P hk1 hkn.le) (stepN_unit P hkn)
        (stepN_unit P hkn') (α := δ * (-(1 - s) / 2)) (β := δ * (-s' / 2)) fun i => ?_
      have := hc i
      rw [midCN_sub_next P hk1 s s' i] at this
      linear_combination this
  rcases mul_eq_zero.mp hlam with h0 | h0
  · exact h0
  · exact absurd h0 (inv_ne_zero hsd.ne')

end BandN

/-- **Injectivity of the band** on `[1/2, n - 1/2] × (-1/8, 1/8)` for `3 ≤ d`: if
`Γ τ - Γ τ' = (t' - t) δ • w` then either `t = t'` and `τ = τ'` by `plPathN_injOn`, or the
stretches of `τ, τ'` are nonadjacent (contradiction with `stretchTriN_separated`, since
`‖(t' - t) δ • w‖ < δ/4 < (√2/2) δ`), or they are equal or adjacent, and then the difference is
in the span of at most two chords, contradicting `diagDir_not_mem_span`. -/
theorem bandN_injOn {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) :
    InjOn (bandN e δ P) (Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2) ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  rintro ⟨τ, t⟩ ⟨hτ, ht⟩ ⟨τ', t'⟩ ⟨hτ', ht'⟩ heq
  simp only [bandN] at heq hτ hτ' ht ht'
  have htt : t = t' := by
    obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
    obtain ⟨k', hk1', hkn', s', hs0', hs1', rfl⟩ := exists_stretch hn hτ'.1 hτ'.2
    rcases le_total k k' with hkk | hkk
    · have h0 := bandN_aux hd hon hδ P hk1 hkn hk1' hkn' hs0 hs1 hs0' hs1' hkk
        (r := (t' - t) * δ) (by
          rw [abs_mul, abs_of_pos hδ]
          have : |t' - t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.2, ht'.1], by linarith [ht.1, ht'.2]⟩
          nlinarith)
        (by rw [sub_mul, sub_smul]; rw [← sub_eq_zero] at heq ⊢; rw [← heq]; abel)
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · linarith
    · have h0 := bandN_aux hd hon hδ P hk1' hkn' hk1 hkn hs0' hs1' hs0 hs1 hkk
        (r := (t - t') * δ) (by
          rw [abs_mul, abs_of_pos hδ]
          have : |t - t'| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1, ht'.2], by linarith [ht.2, ht'.1]⟩
          nlinarith)
        (by rw [sub_mul, sub_smul]; rw [← sub_eq_zero] at heq ⊢; rw [← neg_eq_zero, ← heq]; abel)
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · linarith
  subst htt
  have := plPathN_injOn hon hδ hn P hτ hτ' (add_right_cancel heq)
  rw [this]

end HPC.Plane
