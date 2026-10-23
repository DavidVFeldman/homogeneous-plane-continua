import HPC.Plane.Band

/-!
# Batch 109, item 4: the chain of a self-avoiding lattice path

Continuation of `HPC/Plane/Band.lean` (split off for length; imported by `HPC.lean`).

The strip `(0, 2m+1) × (0, 1)` is threaded through the band by
`(x, y) ↦ band (1/2 + λ x) ((y - 1/2)/4)`, `λ = (n - 1)/(2m+1)`. Shape change (recorded): the
parameter range of the rounded path is `[1/2, n - 1/2]` (length `n - 1`), so `λ = (n-1)/(2m+1)`
instead of `n/(2m+1)`, and `λ ∈ [3, 4)` becomes `6m + 4 ≤ n < 8m + 5`; the band theorem then
needs `n ≥ 22` instead of `21` (with `m = (n - 4)/6`).
-/

namespace HPC.Plane

open Set Metric BandAux Band

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The stretching factor `λ = (n - 1)/(2m + 1)`. -/
noncomputable def chainLam (n m : ℕ) : ℝ := ((n : ℝ) - 1) / (2 * m + 1)

theorem chainLam_mul (n m : ℕ) : chainLam n m * (2 * m + 1) = n - 1 := by
  rw [chainLam]; field_simp

theorem three_le_chainLam {n m : ℕ} (h₁ : 6 * m + 4 ≤ n) : 3 ≤ chainLam n m := by
  rw [chainLam, le_div_iff₀ (by positivity)]
  have : (6 * m + 4 : ℝ) ≤ n := by exact_mod_cast h₁
  linarith

theorem chainLam_lt_four {n m : ℕ} (h₂ : n < 8 * m + 5) : chainLam n m < 4 := by
  rw [chainLam, div_lt_iff₀ (by positivity)]
  have : (n : ℝ) < 8 * m + 5 := by exact_mod_cast h₂
  linarith

/-- The threading map of the strip: `(x, y) ↦ band (1/2 + λ x) ((y - 1/2)/4)`. -/
noncomputable def threadMap (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (m : ℕ) (p : Pt) :
    E :=
  band e₁ e₂ δ P (1 / 2 + chainLam n m * p.1, (p.2 - 1 / 2) / 4)

/-- The link `j`: the open `δ/8`-neighbourhood of the rounded path over
`τ ∈ [1/2 + 2λj, 1/2 + λ(2j+3)]`. -/
noncomputable def latticeLink (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (m : ℕ) (j : ℕ) :
    Set E :=
  thickening (δ / 8) (roundedPath e₁ e₂ δ P ''
    Icc (1 / 2 + chainLam n m * (2 * j)) (1 / 2 + chainLam n m * (2 * j + 3)))

/-- Points of the rounded path whose parameters are `≥ 3` apart lie in nonadjacent stretches, hence
are `≥ (√2/2) δ` apart. -/
theorem roundedPath_far {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : 2 ≤ n) (P : LatticePath n) {τ τ' : ℝ} (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2))
    (hτ' : τ' ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) (h : τ + 3 ≤ τ') :
    Real.sqrt 2 / 2 * δ ≤ dist (roundedPath e₁ e₂ δ P τ) (roundedPath e₁ e₂ δ P τ') := by
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  obtain ⟨k', hk1', hkn', s', hs0', hs1', rfl⟩ := exists_stretch hn hτ'.1 hτ'.2
  have hkk : k + 2 ≤ k' := by
    have : (k : ℝ) + 2 ≤ k' := by linarith
    exact_mod_cast this
  exact stretchTri_separated hon hδ P hkn'.le hkk _
    (roundedPath_mem_stretchTri e₁ e₂ δ P hk1 hkn ⟨by linarith, by linarith⟩) _
    (roundedPath_mem_stretchTri e₁ e₂ δ P hk1' hkn' ⟨by linarith, by linarith⟩)

/-- Every point of the rounded path is within `δ/2` of the lattice point of its stretch. -/
theorem roundedPath_near {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : 2 ≤ n) (P : LatticePath n) {τ : ℝ} (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) :
    ∃ k : ℕ, k < n ∧ τ - 1 / 2 ≤ k ∧ (k : ℝ) ≤ τ + 1 / 2 ∧
      dist (roundedPath e₁ e₂ δ P τ) (latticePt e₁ e₂ δ (P.c k)) ≤ δ / 2 := by
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  refine ⟨k, hkn, by linarith, by linarith, ?_⟩
  exact stretchTri_subset_ball hon hδ P hkn.le
    (roundedPath_mem_stretchTri e₁ e₂ δ P hk1 hkn ⟨by linarith, by linarith⟩)

theorem latticePt_sub (e₁ e₂ : E) (δ : ℝ) (a b : ℤ × ℤ) :
    latticePt e₁ e₂ δ a - latticePt e₁ e₂ δ b = δ • planeL e₁ e₂ (toR (a - b)) := by
  rw [latticePt_eq, latticePt_eq, toR_sub, map_sub, smul_sub]

/-- Lattice points `d` steps apart along the path are within `d δ`. -/
theorem dist_latticePt_le {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) (i : ℕ) :
    ∀ d : ℕ, i + d ≤ n →
      dist (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + d))) ≤ δ * d := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : dist (latticePt e₁ e₂ δ (P.c (i + d))) (latticePt e₁ e₂ δ (P.c (i + d + 1))) = δ := by
      rw [dist_comm, dist_eq_norm, latticePt_sub, norm_smul,
        norm_planeL_unit hon (step_unit P (by omega)), Real.norm_of_nonneg hδ.le, mul_one]
    calc dist (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + (d + 1))))
        ≤ dist (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + d))) +
          dist (latticePt e₁ e₂ δ (P.c (i + d))) (latticePt e₁ e₂ δ (P.c (i + d + 1))) :=
          dist_triangle _ _ _
      _ ≤ δ * (d + 1 : ℕ) := by rw [h2]; push_cast; linarith

theorem dist_latticePt_le' {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {k k' : ℕ} (hk : k ≤ n) (hk' : k' ≤ n) {D : ℕ}
    (h1 : k ≤ k' + D) (h2 : k' ≤ k + D) :
    dist (latticePt e₁ e₂ δ (P.c k)) (latticePt e₁ e₂ δ (P.c k')) ≤ δ * D := by
  rcases le_total k k' with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    refine (dist_latticePt_le hon hδ P k d hk').trans ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : d ≤ D)) hδ.le
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [dist_comm]
    refine (dist_latticePt_le hon hδ P k' d hk).trans ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : d ≤ D)) hδ.le

/-- Links two or more apart are disjoint. -/
theorem latticeLink_disjoint {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) {i j : ℕ} (hij : i + 2 ≤ j)
    (hj : j < m) {x : E} (hxi : x ∈ latticeLink e₁ e₂ δ P m i)
    (hxj : x ∈ latticeLink e₁ e₂ δ P m j) : False := by
  have hlam := three_le_chainLam h₁
  have hlm := chainLam_mul n m
  obtain ⟨_, ⟨τ, hτ, rfl⟩, hx⟩ := mem_thickening_iff.mp hxi
  obtain ⟨_, ⟨τ', hτ', rfl⟩, hx'⟩ := mem_thickening_iff.mp hxj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hij' : (i : ℝ) + 2 ≤ j := by exact_mod_cast hij
  have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1 : chainLam n m * (2 * i + 3) + 3 ≤ chainLam n m * (2 * j) := by nlinarith
  have e2 : chainLam n m * (2 * j + 3) ≤ chainLam n m * (2 * m + 1) := by nlinarith
  have hfar := roundedPath_far hon hδ (by omega) P (τ := τ) (τ' := τ')
    ⟨by nlinarith [hτ.1], by linarith [hτ.2]⟩ ⟨by nlinarith [hτ'.1], by linarith [hτ'.2]⟩
    (by linarith [hτ.2, hτ'.1])
  have htri := dist_triangle_left (roundedPath e₁ e₂ δ P τ) (roundedPath e₁ e₂ δ P τ') x
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  nlinarith

/-- **The chain of a lattice path** with `n` steps, `6m + 4 ≤ n < 8m + 5` (so `λ ∈ [3, 4)`):
links `latticeLink`; adjacent links share `Γ (1/2 + λ (2j + 2))`; nonadjacent links have
`τ`-ranges `≥ λ ≥ 3` apart, hence meet only nonadjacent stretches, at distance
`≥ (√2/2) δ > δ/4`. (Shape change: hypotheses `6m + 4 ≤ n < 8m + 5`, see the module doc.) -/
noncomputable def latticeChain {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) (_h₂ : n < 8 * m + 5) :
    Chain E m where
  link j := latticeLink e₁ e₂ δ P m j
  isOpen _ := isOpen_thickening
  adjacent i j := by
    have hlam := three_le_chainLam h₁
    have hδ8 : 0 < δ / 8 := by positivity
    constructor
    · rintro ⟨x, hxi, hxj⟩
      by_contra hfar
      rcases (by omega : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) with h | h
      · exact latticeLink_disjoint hon hδ P h₁ h j.2 hxi hxj
      · exact latticeLink_disjoint hon hδ P h₁ h i.2 hxj hxi
    · intro h
      -- a common point of the parameter ranges
      have key : ∀ a b : ℕ, a ≤ b → b ≤ a + 1 →
          (latticeLink e₁ e₂ δ P m a ∩ latticeLink e₁ e₂ δ P m b).Nonempty := by
        intro a b hab hba
        refine ⟨roundedPath e₁ e₂ δ P (1 / 2 + chainLam n m * (2 * b)),
          self_subset_thickening hδ8 _ ⟨_, ⟨?_, ?_⟩, rfl⟩,
          self_subset_thickening hδ8 _ ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
        · have : (a : ℝ) ≤ b := by exact_mod_cast hab
          nlinarith
        · have : (b : ℝ) ≤ a + 1 := by exact_mod_cast hba
          nlinarith
        · exact le_rfl
        · nlinarith
      rcases le_total i.val j.val with hle | hle
      · exact key i j hle (by omega)
      · rw [inter_comm]; exact key j i hle (by omega)

theorem latticeChain_link {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) (h₂ : n < 8 * m + 5) (j : Fin m) :
    (latticeChain hon hδ P h₁ h₂).link j = latticeLink e₁ e₂ δ P m j := rfl

/-- The threading map carries the strip into the band domain. -/
theorem threadMap_param {n m : ℕ} (h₁ : 6 * m + 4 ≤ n) {p : Pt}
    (hp : p ∈ Ioo (0 : ℝ) (2 * m + 1) ×ˢ Ioo (0 : ℝ) 1) :
    (1 / 2 + chainLam n m * p.1, (p.2 - 1 / 2) / 4) ∈
      Icc (1 / 2 : ℝ) (n - 1 / 2) ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8) := by
  have hlam := three_le_chainLam h₁
  have hlm := chainLam_mul n m
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
  refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith, by linarith⟩

theorem isThreadedChain_latticeChain {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) (h₂ : n < 8 * m + 5) :
    IsThreadedChain (latticeChain hon hδ P h₁ h₂) := by
  have hlam := three_le_chainLam h₁
  have hn : 2 ≤ n := by omega
  refine ⟨threadMap e₁ e₂ δ P m, ?_, ?_, ?_⟩
  · exact ((continuous_band e₁ e₂ δ P).comp (Continuous.prodMk
      (continuous_const.add (continuous_const.mul continuous_fst))
      ((continuous_snd.sub continuous_const).div_const _))).continuousOn
  · intro p hp p' hp' h
    have h' := band_injOn hon hδ hn P (threadMap_param h₁ (stripSet_subset m hp))
      (threadMap_param h₁ (stripSet_subset m hp')) h
    simp only [Prod.mk.injEq] at h'
    have hl : chainLam n m ≠ 0 := by linarith
    exact Prod.ext (mul_left_cancel₀ hl (by linarith [h'.1])) (by linarith [h'.2])
  · rintro j _ ⟨p, hp, rfl⟩
    have hp' : p ∈ stripSet m := mem_iUnion.mpr ⟨j, hp⟩
    have hdom := threadMap_param (n := n) h₁ (stripSet_subset m hp')
    obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
    show threadMap e₁ e₂ δ P m p ∈ latticeLink e₁ e₂ δ P m j
    refine mem_thickening_iff.mpr ⟨_, ⟨1 / 2 + chainLam n m * p.1, ⟨by nlinarith, by nlinarith⟩,
      rfl⟩, ?_⟩
    rw [threadMap, band, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hν := norm_roundedNormal hon (δ := δ) hn P hdom.1
    have ht : ‖(p.2 - 1 / 2) / 4 * δ‖ < δ / 8 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
      have : |(p.2 - 1 / 2) / 4| < 1 / 8 := abs_lt.mpr ⟨by linarith, by linarith⟩
      nlinarith
    calc ‖(p.2 - 1 / 2) / 4 * δ‖ * ‖roundedNormal e₁ e₂ δ P (1 / 2 + chainLam n m * p.1)‖
        ≤ ‖(p.2 - 1 / 2) / 4 * δ‖ * 1 := mul_le_mul_of_nonneg_left hν (norm_nonneg _)
      _ < δ / 8 := by rw [mul_one]; exact ht

/-- Every parameter in `[1/2, n - 1/2]` lies in the parameter range of some link. -/
theorem exists_link_param {n m : ℕ} (hm : 0 < m) (h₁ : 6 * m + 4 ≤ n) {τ : ℝ}
    (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) :
    ∃ j : ℕ, j < m ∧ τ ∈ Icc (1 / 2 + chainLam n m * (2 * j)) (1 / 2 + chainLam n m * (2 * j + 3)) := by
  have hlam := three_le_chainLam h₁
  have hlm := chainLam_mul n m
  set u := (τ - 1 / 2) / (2 * chainLam n m) with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hτ.1]) (by positivity)
  have hτu : τ - 1 / 2 = 2 * chainLam n m * u := by rw [hu]; field_simp
  have hfl := Nat.floor_le hu0
  have hlt := Nat.lt_floor_add_one u
  set J := min ⌊u⌋₊ (m - 1) with hJ
  refine ⟨J, by omega, ?_, ?_⟩
  · have : (J : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast (min_le_left _ _)
    nlinarith
  · rcases le_total ⌊u⌋₊ (m - 1) with h | h
    · have hJ' : J = ⌊u⌋₊ := by omega
      rw [hJ']
      nlinarith
    · have hJ' : (J : ℝ) + 1 = m := by
        have : J + 1 = m := by omega
        exact_mod_cast this
      have : chainLam n m * (2 * J + 3) = n - 1 := by rw [← hlm]; linear_combination chainLam n m * 2 * hJ'
      linarith [hτ.2]

/-- **The band theorem.** A self-avoiding lattice path with `n ≥ 22` steps at mesh `δ` carries a
threaded chain of at least three links, each of diameter `≤ 16 δ`, whose union lies within `δ` of
the polygonal path and comes within `δ` of every lattice point of the path. (Shape change: `22`
instead of `21`, see the module doc.) -/
theorem exists_threadedChain_of_latticePath {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 22 ≤ n) (P : LatticePath n) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧
      (∀ j, diam (D.link j) ≤ 16 * δ) ∧
      D.union ⊆ thickening δ (polyPath e₁ e₂ δ P) ∧
      ∀ i, i ≤ n → ∃ x ∈ D.union, dist x (latticePt e₁ e₂ δ (P.c i)) ≤ δ := by
  set m := (n - 4) / 6 with hm
  have h₁ : 6 * m + 4 ≤ n := by omega
  have h₂ : n < 8 * m + 5 := by omega
  have hm3 : 3 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hlam := three_le_chainLam h₁
  have hlam4 := chainLam_lt_four h₂
  have hlm := chainLam_mul n m
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  -- parameters of a link lie in `[1/2, n - 1/2]`
  have hrange : ∀ j : Fin m, ∀ τ ∈ Icc (1 / 2 + chainLam n m * (2 * (j : ℕ)))
      (1 / 2 + chainLam n m * (2 * (j : ℕ) + 3)), τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2) := by
    intro j τ hτ
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    have hjm : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast j.2
    exact ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  refine ⟨m, latticeChain hon hδ P h₁ h₂, hm3, isThreadedChain_latticeChain hon hδ P h₁ h₂,
    ?_, ?_, ?_⟩
  · -- diameters
    intro j
    refine diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hx⟩ := mem_thickening_iff.mp hx
    obtain ⟨_, ⟨τ', hτ', rfl⟩, hy⟩ := mem_thickening_iff.mp hy
    obtain ⟨k, hkn, hk1, hk2, hdk⟩ := roundedPath_near hon hδ hn2 P (hrange j τ hτ)
    obtain ⟨k', hkn', hk1', hk2', hdk'⟩ := roundedPath_near hon hδ hn2 P (hrange j τ' hτ')
    have hττ : |τ - τ'| ≤ 3 * chainLam n m := by
      rw [abs_le]; constructor <;> nlinarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
    have hkk1 : k ≤ k' + 12 := by
      have : (k : ℝ) < k' + 13 := by linarith [(abs_le.mp hττ).2]
      have : k < k' + 13 := by exact_mod_cast this
      omega
    have hkk2 : k' ≤ k + 12 := by
      have : (k' : ℝ) < k + 13 := by linarith [(abs_le.mp hττ).1]
      have : k' < k + 13 := by exact_mod_cast this
      omega
    have hcc := dist_latticePt_le' hon hδ P hkn.le hkn'.le hkk1 hkk2
    have t1 := dist_triangle x (roundedPath e₁ e₂ δ P τ) y
    have t2 := dist_triangle (roundedPath e₁ e₂ δ P τ) (latticePt e₁ e₂ δ (P.c k)) y
    have t3 := dist_triangle (latticePt e₁ e₂ δ (P.c k)) (latticePt e₁ e₂ δ (P.c k')) y
    have t4 := dist_triangle (latticePt e₁ e₂ δ (P.c k')) (roundedPath e₁ e₂ δ P τ') y
    rw [dist_comm] at hdk' hy
    push_cast at hcc
    linarith
  · -- the union lies within `δ` of the polygonal path
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hxτ⟩ := mem_thickening_iff.mp hj
    obtain ⟨k, hkn, _, _, hdk⟩ := roundedPath_near hon hδ hn2 P (hrange j τ hτ)
    refine mem_thickening_iff.mpr ⟨_, latticePt_mem_polyPath e₁ e₂ δ P hkn, ?_⟩
    linarith [dist_triangle x (roundedPath e₁ e₂ δ P τ) (latticePt e₁ e₂ δ (P.c k))]
  · -- every lattice point of the path is within `δ` of the union
    intro i hi
    obtain ⟨i₀, hi₀n, hτ₀, hdist⟩ : ∃ i₀ : ℕ, i₀ < n ∧
        ((i₀ : ℝ) + 1 / 2 ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) ∧
        dist (stepMid e₁ e₂ δ P i₀) (latticePt e₁ e₂ δ (P.c i)) = δ / 2 := by
      rcases lt_or_eq_of_le hi with hlt | rfl
      · refine ⟨i, hlt, ⟨by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩, ?_⟩
        · have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hlt
          linarith
        · rw [dist_eq_norm, stepMid_sub_left, norm_smul, norm_planeL_unit hon (step_unit P hlt),
            Real.norm_of_nonneg (by positivity), mul_one]
      · refine ⟨i - 1, by omega, ⟨by linarith [(Nat.cast_nonneg (i - 1) : (0 : ℝ) ≤ (i - 1 : ℕ))],
          ?_⟩, ?_⟩
        · rw [Nat.cast_sub (by omega)]; push_cast; linarith
        · rw [dist_eq_norm, stepMid_sub_right e₁ e₂ δ P (by omega : 0 < i), norm_smul,
            norm_planeL_unit hon (arm_left_unit P (by omega) le_rfl),
            Real.norm_of_nonneg (by positivity), mul_one]
    obtain ⟨J, hJm, hJ⟩ := exists_link_param (by omega) h₁ hτ₀
    refine ⟨roundedPath e₁ e₂ δ P (i₀ + 1 / 2), mem_iUnion.mpr ⟨⟨J, hJm⟩,
      self_subset_thickening (by positivity) _ ⟨_, hJ, rfl⟩⟩, ?_⟩
    rw [roundedPath_half e₁ e₂ δ P hi₀n, hdist]
    linarith

end HPC.Plane
