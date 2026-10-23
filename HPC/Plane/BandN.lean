import HPC.Plane.LatticeCycle
import HPC.Plane.BandNPath

/-!
# Batch 112: the band in dimension `≥ 3`, and the reduction of Hilbert space to finite dimension

Saved from the uploaded skeleton as `HPC/Plane/BandN.lean`; `import HPC.Plane.BandN` is added at
the end of `HPC.lean`. Split for length (the commission allows it): items 1–3 (lattice paths in
`ℤ^d`, the piecewise-linear path, the band) are in `HPC/Plane/BandNPath.lean`, the elementary
integer and coordinate lemmas in `HPC/Plane/BandNAux.lean`; this file has item 4 (the chain) and
item 5 (Hilbert space).

Towards `geomLemma'_of_two_le_rank` (then open). *Batch 116 note:* that lemma is now proved in every
dimension `≥ 2` (batch 113, `HPC/Plane/CubeCycle.lean`), and both halves below are used there.
Two independent halves:

**(A) Lattice paths in `ℤ^d` and the band with a fixed transverse direction (`3 ≤ d`).** The
plane needed a normal field turning at the corners (`Band.lean`); in dimension `d ≥ 3` the band
`(τ, t) ↦ Γ τ + (t δ) • w` with the *constant* unit vector `w = (e 0 + ⋯ + e (d-1)) / √d` is
already injective, because every coordinate of `w` is nonzero: for `τ, τ'` in the same or in
adjacent stretches the difference `Γ τ - Γ τ'` lies in the span of at most two vectors of the form
`(u + u')/2` (`u, u'` consecutive unit steps), and no nonzero multiple of `w` does; for
nonadjacent stretches the separation lemma (`(√2/2) δ`) beats `‖(t - t') δ w‖ < δ/4`. The chain
is then as in `BandChain.lean`.

**(B) Hilbert space.** `GeomLemma' E` follows from `GeomLemma' F` for the finite-dimensional
subspaces `F` of `E` of dimension `≥ 2`: a compact `g` has a finite `ε/4`-net; `F` is the span of
the net and of two independent vectors; the orthogonal projection `P_F` moves each point of `g` by
less than `ε/4`; `P_F '' g` is a continuum of `F`; the chain `D'` of `F` for `P_F '' g` and `ε/2`
is pulled back to `E` as `link j := P_F ⁻¹' (D'.link j) ∩ thickening η F`.

**Shape changes from the skeleton** (all recorded in `doc/batches/REPORT-batch112.md`):
* `diagDir_not_mem_span`: the hypotheses `u' ≠ -u` and `u'' ≠ -u'` are dropped (not needed: if
  the three unit steps miss an axis that coordinate vanishes, and otherwise `d = 3` and the three
  steps use three distinct axes, where the arithmetic of the header applies).
* `exists_threadedChain_pullback` and `geomLemma'_of_subspaces`: the instance argument
  `[CompleteSpace E]` is dropped (not needed: the orthogonal projection onto a finite-dimensional
  subspace exists in any inner product space).
* `plPathN_mem_stretchTriN`: the hypotheses `hon` and `hδ` are dropped and `e`, `δ` become
  explicit (not needed: on stretch `k` the path is a convex combination of the two midpoints).
* `plPathN` (a `sorry` definition in the skeleton) is the hat-function sum of `roundedPath`,
  `τ ↦ Σ_{j < n} hat (τ - 1/2 - j) • m_j`.
-/

namespace HPC.Plane

open Set Metric BandAux BandNAux BandN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Item 4: the chain of a lattice path in `ℤ^d` -/

/-- The threading map of the strip: `(x, y) ↦ bandN (1/2 + λ x) ((y - 1/2)/4)`. -/
noncomputable def threadMapN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (m : ℕ) (p : Pt) : E :=
  bandN e δ P (1 / 2 + chainLam n m * p.1, (p.2 - 1 / 2) / 4)

/-- The link `j`: the open `δ/8`-neighbourhood of `Γ` over
`τ ∈ [1/2 + 2λj, 1/2 + λ(2j+3)]`. -/
noncomputable def latticeLinkN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (m : ℕ) (j : ℕ) : Set E :=
  thickening (δ / 8) (plPathN e δ P ''
    Icc (1 / 2 + chainLam n m * (2 * j)) (1 / 2 + chainLam n m * (2 * j + 3)))

/-- Points of `Γ` whose parameters are `≥ 3` apart are `≥ (√2/2) δ` apart. -/
theorem plPathN_far {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) {τ τ' : ℝ}
    (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) (hτ' : τ' ∈ Icc (1 / 2 : ℝ) (n - 1 / 2))
    (h : τ + 3 ≤ τ') :
    Real.sqrt 2 / 2 * δ ≤ dist (plPathN e δ P τ) (plPathN e δ P τ') := by
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  obtain ⟨k', hk1', hkn', s', hs0', hs1', rfl⟩ := exists_stretch hn hτ'.1 hτ'.2
  have hkk : k + 2 ≤ k' := by
    have : (k : ℝ) + 2 ≤ k' := by linarith
    exact_mod_cast this
  exact stretchTriN_separated hon hδ P hkn'.le hkk _
    (plPathN_mem_stretchTriN e δ P hk1 hkn ⟨by linarith, by linarith⟩) _
    (plPathN_mem_stretchTriN e δ P hk1' hkn' ⟨by linarith, by linarith⟩)

/-- Every point of `Γ` is within `δ/2` of the lattice point of its stretch. -/
theorem plPathN_near {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) {τ : ℝ} (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) :
    ∃ k : ℕ, k < n ∧ τ - 1 / 2 ≤ k ∧ (k : ℝ) ≤ τ + 1 / 2 ∧
      dist (plPathN e δ P τ) (latticePtN e δ (P.c k)) ≤ δ / 2 := by
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  refine ⟨k, hkn, by linarith, by linarith, ?_⟩
  exact stretchTriN_subset_ball hon hδ P hkn.le
    (plPathN_mem_stretchTriN e δ P hk1 hkn ⟨by linarith, by linarith⟩)

/-- Lattice points `D` steps apart along the path are within `D δ`. -/
theorem dist_latticePtN_le {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePathN d n) (i : ℕ) :
    ∀ D : ℕ, i + D ≤ n →
      dist (latticePtN e δ (P.c i)) (latticePtN e δ (P.c (i + D))) ≤ δ * D := by
  intro D
  induction D with
  | zero => intro _; simp
  | succ D ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : dist (latticePtN e δ (P.c (i + D))) (latticePtN e δ (P.c (i + D + 1))) = δ := by
      rw [dist_comm, dist_eq_norm, latticePtN_sub, norm_smul,
        norm_vecL_unit hon (stepN_unit P (by omega)), Real.norm_of_nonneg hδ.le, mul_one]
    calc dist (latticePtN e δ (P.c i)) (latticePtN e δ (P.c (i + (D + 1))))
        ≤ dist (latticePtN e δ (P.c i)) (latticePtN e δ (P.c (i + D))) +
          dist (latticePtN e δ (P.c (i + D))) (latticePtN e δ (P.c (i + D + 1))) :=
          dist_triangle _ _ _
      _ ≤ δ * (D + 1 : ℕ) := by rw [h2]; push_cast; linarith

theorem dist_latticePtN_le' {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk : k ≤ n) (hk' : k' ≤ n) {D : ℕ}
    (h1 : k ≤ k' + D) (h2 : k' ≤ k + D) :
    dist (latticePtN e δ (P.c k)) (latticePtN e δ (P.c k')) ≤ δ * D := by
  rcases le_total k k' with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    refine (dist_latticePtN_le hon hδ P k j hk').trans ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : j ≤ D)) hδ.le
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [dist_comm]
    refine (dist_latticePtN_le hon hδ P k' j hk).trans ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : j ≤ D)) hδ.le

/-- Links two or more apart are disjoint. -/
theorem latticeLinkN_disjoint {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j < m) {x : E} (hxi : x ∈ latticeLinkN e δ P m i)
    (hxj : x ∈ latticeLinkN e δ P m j) : False := by
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
  have hfar := plPathN_far hon hδ (by omega) P (τ := τ) (τ' := τ')
    ⟨by nlinarith [hτ.1], by linarith [hτ.2]⟩ ⟨by nlinarith [hτ'.1], by linarith [hτ'.2]⟩
    (by linarith [hτ.2, hτ'.1])
  have htri := dist_triangle_left (plPathN e δ P τ) (plPathN e δ P τ') x
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  nlinarith

/-- **The chain of a lattice path** in `ℤ^d` with `n` steps, `6m + 4 ≤ n < 8m + 5`. -/
noncomputable def latticeChainN {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {m : ℕ} (h₁ : 6 * m + 4 ≤ n) :
    Chain E m where
  link j := latticeLinkN e δ P m j
  isOpen _ := isOpen_thickening
  adjacent i j := by
    have hlam := three_le_chainLam h₁
    have hδ8 : 0 < δ / 8 := by positivity
    constructor
    · rintro ⟨x, hxi, hxj⟩
      by_contra hfar
      rcases (by omega : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) with h | h
      · exact latticeLinkN_disjoint hon hδ P h₁ h j.2 hxi hxj
      · exact latticeLinkN_disjoint hon hδ P h₁ h i.2 hxj hxi
    · intro h
      have key : ∀ a b : ℕ, a ≤ b → b ≤ a + 1 →
          (latticeLinkN e δ P m a ∩ latticeLinkN e δ P m b).Nonempty := by
        intro a b hab hba
        refine ⟨plPathN e δ P (1 / 2 + chainLam n m * (2 * b)),
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

theorem isThreadedChain_latticeChainN {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E}
    (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {m : ℕ}
    (h₁ : 6 * m + 4 ≤ n) : IsThreadedChain (latticeChainN hon hδ P h₁) := by
  have hlam := three_le_chainLam h₁
  have hn : 2 ≤ n := by omega
  refine ⟨threadMapN e δ P m, ?_, ?_, ?_⟩
  · exact ((continuous_bandN e δ P).comp (Continuous.prodMk
      (continuous_const.add (continuous_const.mul continuous_fst))
      ((continuous_snd.sub continuous_const).div_const _))).continuousOn
  · intro p hp p' hp' h
    have h' := bandN_injOn hd hon hδ hn P (threadMap_param h₁ (stripSet_subset m hp))
      (threadMap_param h₁ (stripSet_subset m hp')) h
    simp only [Prod.mk.injEq] at h'
    have hl : chainLam n m ≠ 0 := by linarith
    exact Prod.ext (mul_left_cancel₀ hl (by linarith [h'.1])) (by linarith [h'.2])
  · rintro j _ ⟨p, hp, rfl⟩
    obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
    show threadMapN e δ P m p ∈ latticeLinkN e δ P m j
    refine mem_thickening_iff.mpr ⟨_, ⟨1 / 2 + chainLam n m * p.1, ⟨by nlinarith, by nlinarith⟩,
      rfl⟩, ?_⟩
    rw [threadMapN, bandN, dist_eq_norm, add_sub_cancel_left, norm_smul,
      norm_diagDir hon (by omega), mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    have : |(p.2 - 1 / 2) / 4| < 1 / 8 := abs_lt.mpr ⟨by linarith, by linarith⟩
    nlinarith

/-- **The band theorem in dimension `≥ 3`** (the statement of
`exists_threadedChain_of_latticePath`, with `bandN` in place of `band`; the chain of
`BandChain.lean` with `λ = (n - 1)/(2m + 1)`, `m = (n - 4)/6`). -/
theorem exists_threadedChain_of_latticePathN {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E}
    (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 22 ≤ n) (P : LatticePathN d n) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧
      (∀ j, diam (D.link j) ≤ 16 * δ) ∧
      D.union ⊆ thickening δ (polyPathN e δ P) ∧
      ∀ i, i ≤ n → ∃ x ∈ D.union, dist x (latticePtN e δ (P.c i)) ≤ δ := by
  set m := (n - 4) / 6 with hm
  have h₁ : 6 * m + 4 ≤ n := by omega
  have h₂ : n < 8 * m + 5 := by omega
  have hm3 : 3 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hlam := three_le_chainLam h₁
  have hlam4 := chainLam_lt_four h₂
  have hlm := chainLam_mul n m
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hrange : ∀ j : Fin m, ∀ τ ∈ Icc (1 / 2 + chainLam n m * (2 * (j : ℕ)))
      (1 / 2 + chainLam n m * (2 * (j : ℕ) + 3)), τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2) := by
    intro j τ hτ
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    have hjm : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast j.2
    exact ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  refine ⟨m, latticeChainN hon hδ P h₁, hm3, isThreadedChain_latticeChainN hd hon hδ P h₁,
    ?_, ?_, ?_⟩
  · -- diameters
    intro j
    refine diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hx⟩ := mem_thickening_iff.mp hx
    obtain ⟨_, ⟨τ', hτ', rfl⟩, hy⟩ := mem_thickening_iff.mp hy
    obtain ⟨k, hkn, hk1, hk2, hdk⟩ := plPathN_near hon hδ hn2 P (hrange j τ hτ)
    obtain ⟨k', hkn', hk1', hk2', hdk'⟩ := plPathN_near hon hδ hn2 P (hrange j τ' hτ')
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
    have hcc := dist_latticePtN_le' hon hδ P hkn.le hkn'.le hkk1 hkk2
    have t1 := dist_triangle x (plPathN e δ P τ) y
    have t2 := dist_triangle (plPathN e δ P τ) (latticePtN e δ (P.c k)) y
    have t3 := dist_triangle (latticePtN e δ (P.c k)) (latticePtN e δ (P.c k')) y
    have t4 := dist_triangle (latticePtN e δ (P.c k')) (plPathN e δ P τ') y
    rw [dist_comm] at hdk' hy
    push_cast at hcc
    linarith
  · -- the union lies within `δ` of the polygonal path
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hxτ⟩ := mem_thickening_iff.mp hj
    obtain ⟨k, hkn, _, _, hdk⟩ := plPathN_near hon hδ hn2 P (hrange j τ hτ)
    refine mem_thickening_iff.mpr ⟨_, latticePtN_mem_polyPathN e δ P hkn, ?_⟩
    linarith [dist_triangle x (plPathN e δ P τ) (latticePtN e δ (P.c k))]
  · -- every lattice point of the path is within `δ` of the union
    intro i hi
    obtain ⟨i₀, hi₀n, hτ₀, hdist⟩ : ∃ i₀ : ℕ, i₀ < n ∧
        ((i₀ : ℝ) + 1 / 2 ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) ∧
        dist (stepMidN e δ P i₀) (latticePtN e δ (P.c i)) = δ / 2 := by
      rcases lt_or_eq_of_le hi with hlt | rfl
      · refine ⟨i, hlt, ⟨by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩, ?_⟩
        · have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hlt
          linarith
        · rw [dist_eq_norm, stepMidN_sub_left, norm_smul, norm_vecL_unit hon (stepN_unit P hlt),
            Real.norm_of_nonneg (by positivity), mul_one]
      · refine ⟨i - 1, by omega, ⟨by linarith [(Nat.cast_nonneg (i - 1) : (0 : ℝ) ≤ (i - 1 : ℕ))],
          ?_⟩, ?_⟩
        · rw [Nat.cast_sub (by omega)]; push_cast; linarith
        · rw [dist_eq_norm, stepMidN_sub_right e δ P (by omega : 0 < i), norm_smul,
            norm_vecL_unit hon (armN_left_unit P (by omega) le_rfl),
            Real.norm_of_nonneg (by positivity), mul_one]
    obtain ⟨J, hJm, hJ⟩ := exists_link_param (by omega) h₁ hτ₀
    refine ⟨plPathN e δ P (i₀ + 1 / 2), mem_iUnion.mpr ⟨⟨J, hJm⟩,
      self_subset_thickening (by positivity) _ ⟨_, hJ, rfl⟩⟩, ?_⟩
    rw [plPathN_half e δ P hi₀n, hdist]
    linarith

/-! ### Item 5: reduction of `E` to its finite-dimensional subspaces -/

/-- A compact set is within `η` of a finite-dimensional subspace of dimension `≥ 2`
(span of a finite `η`-net, enlarged if necessary; needs `2 ≤ Module.rank ℝ E`). -/
theorem exists_finiteDimensional_subspace_near (hdim : 2 ≤ Module.rank ℝ E) {g : Set E}
    (hg : IsCompact g) {η : ℝ} (hη : 0 < η) :
    ∃ F : Submodule ℝ E, FiniteDimensional ℝ F ∧ 2 ≤ Module.finrank ℝ F ∧
      ∀ x ∈ g, ∃ y ∈ F, dist x y < η := by
  obtain ⟨t, -, htf, hcover⟩ := hg.finite_cover_balls hη
  obtain ⟨s, hs, hli⟩ := le_rank_iff_exists_linearIndependent.mp hdim
  have hsf : s.Finite :=
    Cardinal.mk_lt_aleph0_iff.mp (by rw [hs]; exact Cardinal.natCast_lt_aleph0)
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (t ∪ s)) :=
    FiniteDimensional.span_of_finite ℝ (htf.union hsf)
  refine ⟨Submodule.span ℝ (t ∪ s), inferInstance, ?_, ?_⟩
  · haveI := hsf.fintype
    have h1 : Module.finrank ℝ (Submodule.span ℝ s) = 2 := by
      rw [finrank_span_set_eq_card hli]
      have := Cardinal.mk_fintype s
      rw [hs] at this
      rw [Set.toFinset_card]
      exact_mod_cast this.symm
    rw [← h1]
    exact Submodule.finrank_mono (Submodule.span_mono subset_union_right)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨y, Submodule.subset_span (Or.inl hy), hxy⟩

namespace BandN

/-- A point within `η` of a finite-dimensional subspace is within `η` of its orthogonal
projection. -/
theorem dist_orthogonalProjection_lt (F : Submodule ℝ E) [FiniteDimensional ℝ F] {x : E} {η : ℝ}
    (hx : x ∈ thickening η (F : Set E)) : dist x (F.orthogonalProjection x : E) < η := by
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  rw [dist_eq_norm, ← Submodule.starProjection_apply, Submodule.starProjection_minimal]
  refine lt_of_le_of_lt (ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨y, hy⟩) ?_
  rw [← dist_eq_norm]; exact hxy

/-- The pulled-back links. -/
noncomputable def pullLink (F : Submodule ℝ E) [FiniteDimensional ℝ F] {m : ℕ} (D' : Chain F m)
    (η : ℝ) (j : Fin m) : Set E :=
  F.orthogonalProjection ⁻¹' D'.link j ∩ thickening η (F : Set E)

theorem coe_mem_pullLink (F : Submodule ℝ E) [FiniteDimensional ℝ F] {m : ℕ} (D' : Chain F m)
    {η : ℝ} (hη : 0 < η) {j : Fin m} {y : F} (hy : y ∈ D'.link j) :
    (y : E) ∈ pullLink F D' η j :=
  ⟨by simpa [mem_preimage] using hy, self_subset_thickening hη _ y.2⟩

/-- The pulled-back chain. -/
noncomputable def pullChain (F : Submodule ℝ E) [FiniteDimensional ℝ F] {m : ℕ} (D' : Chain F m)
    {η : ℝ} (hη : 0 < η) : Chain E m where
  link := pullLink F D' η
  isOpen j := ((D'.isOpen j).preimage F.orthogonalProjection.continuous).inter isOpen_thickening
  adjacent i j := by
    rw [← D'.adjacent i j]
    constructor
    · rintro ⟨x, hxi, hxj⟩
      exact ⟨F.orthogonalProjection x, hxi.1, hxj.1⟩
    · rintro ⟨y, hyi, hyj⟩
      exact ⟨y, coe_mem_pullLink F D' hη hyi, coe_mem_pullLink F D' hη hyj⟩

end BandN

/-- **Pulling a threaded chain of a closed subspace back to `E`**: `link j := P_F ⁻¹' (D'.link j)
∩ thickening η F` is a chain of `E` with the same adjacency, threaded by the same map followed by
the inclusion, with `diam ≤ diam (D'.link j) + 2η`, `D.union ⊆ thickening η (D'.union)` and
`D'.union ⊆ D.union`. (Shape change: `[CompleteSpace E]` dropped, not needed.) -/
theorem exists_threadedChain_pullback (F : Submodule ℝ E)
    [FiniteDimensional ℝ F] {m : ℕ} (D' : Chain F m) (hD' : IsThreadedChain D') {η : ℝ}
    (hη : 0 < η) :
    ∃ D : Chain E m, IsThreadedChain D ∧
      (∀ j, Bornology.IsBounded (D'.link j) → diam (D.link j) ≤ diam (D'.link j) + 2 * η) ∧
      D.union ⊆ thickening η ((↑) '' D'.union : Set E) ∧
      ((↑) '' D'.union : Set E) ⊆ D.union := by
  obtain ⟨f, hfc, hfi, himg⟩ := hD'
  refine ⟨pullChain F D' hη, ⟨fun p => (f p : E), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp_continuousOn hfc
  · exact Subtype.val_injective.comp_injOn hfi
  · rintro j _ ⟨p, hp, rfl⟩
    exact coe_mem_pullLink F D' hη (himg j ⟨p, hp, rfl⟩)
  · intro j hb
    refine diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have h1 := dist_orthogonalProjection_lt F hx.2
    have h2 := dist_orthogonalProjection_lt F hy.2
    have h3 : dist (F.orthogonalProjection x : E) (F.orthogonalProjection y : E) ≤
        diam (D'.link j) := dist_le_diam_of_mem hb hx.1 hy.1
    have t1 := dist_triangle x (F.orthogonalProjection x : E) y
    have t2 := dist_triangle (F.orthogonalProjection x : E) (F.orthogonalProjection y : E) y
    rw [dist_comm] at h2
    linarith
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact mem_thickening_iff.mpr ⟨_, ⟨F.orthogonalProjection x, mem_iUnion.mpr ⟨j, hj.1⟩, rfl⟩,
      dist_orthogonalProjection_lt F hj.2⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨j, coe_mem_pullLink F D' hη hj⟩

/-- **The reduction.** If `GeomLemma'` holds in every finite-dimensional subspace of `E` of
dimension `≥ 2`, it holds in `E`. (Shape change: `[CompleteSpace E]` dropped, not needed.) -/
theorem geomLemma'_of_subspaces (hdim : 2 ≤ Module.rank ℝ E)
    (hF : ∀ F : Submodule ℝ E, FiniteDimensional ℝ F → 2 ≤ Module.finrank ℝ F → GeomLemma' F) :
    GeomLemma' E := by
  intro g hg ε hε
  obtain ⟨F, hFd, hF2, hnear⟩ := exists_finiteDimensional_subspace_near hdim hg.1
    (show 0 < ε / 4 by positivity)
  haveI := hFd
  set P := F.orthogonalProjection
  have hgF : ∀ z ∈ g, dist z (P z : E) < ε / 4 := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := hnear z hz
    exact dist_orthogonalProjection_lt F (mem_thickening_iff.mpr ⟨y, hy, hzy⟩)
  have hg' : Fold.Q78.IsContinuum (P '' g) :=
    ⟨hg.1.image P.continuous, hg.2.image _ P.continuous.continuousOn⟩
  obtain ⟨m, D', hm, hD', hdiam, hD'g, hgD'⟩ := hF F hFd hF2 _ hg' (ε / 2) (by positivity)
  obtain ⟨D, hD, hdiamD, hDD', hD'D⟩ := exists_threadedChain_pullback F D' hD'
    (show 0 < ε / 8 by positivity)
  have hbdd : Bornology.IsBounded D'.union :=
    (hg'.1.isBounded.thickening).subset hD'g
  refine ⟨m, D, hm, hD, fun j => ?_, ?_, ?_⟩
  · have := hdiamD j (hbdd.subset (subset_iUnion _ j))
    linarith [hdiam j]
  · intro x hx
    obtain ⟨_, ⟨y', hy', rfl⟩, hxy⟩ := mem_thickening_iff.mp (hDD' hx)
    obtain ⟨_, ⟨z, hz, rfl⟩, hyz⟩ := mem_thickening_iff.mp (hD'g hy')
    refine mem_thickening_iff.mpr ⟨z, hz, ?_⟩
    have h1 : dist (y' : E) (P z : E) < ε / 2 := hyz
    have h2 := hgF z hz
    rw [dist_comm] at h2
    linarith [dist_triangle x (y' : E) (P z : E), dist_triangle x (P z : E) z]
  · intro z hz
    obtain ⟨y', hy', hzy⟩ := mem_thickening_iff.mp (hgD' ⟨z, hz, rfl⟩)
    refine mem_thickening_iff.mpr ⟨y', hD'D ⟨y', hy', rfl⟩, ?_⟩
    have h1 : dist (P z : E) (y' : E) < ε / 2 := hzy
    linarith [hgF z hz, dist_triangle z (P z : E) (y' : E)]

end HPC.Plane
