import HPC.Plane.BandChain
import HPC.Plane.LatticeCycleAux

/-!
# Batch 110: a self-avoiding lattice cycle through the squares meeting a plane continuum, and the
# density lemma in the plane

Saved from the uploaded skeleton as `HPC/Plane/LatticeCycle.lean`; `import HPC.Plane.LatticeCycle` is
added at the end of `HPC.lean`. The combinatorics of the cycle (and the definitions `PolyConnected`,
`InSq`, `InSqInt` of the skeleton) are split off into `HPC/Plane/LatticeCycleAux.lean`.

Second half of the density lemma (first half: batch 109, `Band.lean`, `BandChain.lean`).

Conventions. Squares are indexed by `s : ℤ × ℤ`; square `s` is `[s.1, s.1 + 1] × [s.2, s.2 + 1]` in
units of the side `δ`. The fine lattice has mesh `δ/8`, so in fine coordinates square `s` is
`[8 s.1, 8 s.1 + 8] × [8 s.2, 8 s.2 + 8]` and its *depth-1 points* are those with both coordinates
strictly inside. Two squares are *adjacent* when their indices differ by a unit step (they share a
side). A finite set of squares is *connected* when it has no nonempty proper subset closed under
adjacency within the set.

**The cycle (item 2; construction changed from the skeleton, see the report).** Instead of
replacing the five interior points of a free row by a 21-point detour, one *edge* is replaced: the
invariant keeps, for every free side of every square, the two middle depth-1 points of its row
(offsets `3` and `4`) as consecutive points of the cycle. A new square `ℓ` across the free side
`σ` of `s` is spliced in at that edge `x → y`: `x`, the point of `σ` beyond `x`, the whole depth-1
loop of `ℓ` (24 points, traversed the long way from the point beyond to the point beyond `y`), the
point of `σ` beyond `y`, `y`. The cycle grows by `26` points per square: `L = 26 N - 2`
(`exists_latticeCycle'`). Details in the module doc of `LatticeCycleAux.lean`.

**Batch 111.** At the end of the file: the open density lemma for general `E`,
`geomLemma'_of_two_le_rank`, replacing the deleted batch-90 statement `exists_tame_chain_near`, and
its consequences `dense_pseudoArcs`, `theorem2_HIC` (Pacific Theorem 2; moved here from
`Most51.lean` with the same statements) and `theorem2_1951` (Duke Theorem 2, general `E`; new).
**Batch 113:** these four were moved to `HPC/Plane/CubeCycle.lean`, where they are proved.
-/

namespace HPC.Plane

open Set Metric Band

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Polyominoes and the cycle -/

/-- A connected finite set of squares has a connected enumeration: a bijection `Fin N → T` in which
every square after the first is adjacent to an earlier one. -/
theorem exists_connected_enumeration (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (hc : PolyConnected T) :
    ∃ (N : ℕ) (e : ℕ → ℤ × ℤ), N = T.card ∧ InjOn e (Iio N) ∧ (∀ i < N, e i ∈ T) ∧
      ∀ k, 0 < k → k < N → ∃ j < k, IsUnitStep (e j) (e k) := by
  have key : ∀ k, 1 ≤ k → k ≤ T.card → ∃ e : ℕ → ℤ × ℤ, InjOn e (Iio k) ∧ (∀ i < k, e i ∈ T) ∧
      ∀ k', 0 < k' → k' < k → ∃ j < k', IsUnitStep (e j) (e k') := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · obtain ⟨s₁, hs₁⟩ := hT
        refine ⟨fun _ => s₁, ?_, fun _ _ => hs₁, fun k' h1 h2 => by omega⟩
        intro a ha b hb _
        simp only [mem_Iio] at ha hb
        omega
      · obtain ⟨e, hinj, hmem, hadj⟩ := ih hk0 (by omega)
        set A := (Finset.range k).image e with hA
        have hAT : A ⊆ T := by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact hmem i (Finset.mem_range.mp hi)
        have hAc : A.card = k := by
          rw [Finset.card_image_of_injOn]
          · simp
          · intro a ha b hb hab
            exact hinj (mem_Iio.mpr (by simpa using ha)) (mem_Iio.mpr (by simpa using hb)) hab
        have hne : A ≠ T := by intro h; rw [h] at hAc; omega
        have hAne : A.Nonempty := ⟨e 0, Finset.mem_image.mpr ⟨0, by simp; omega, rfl⟩⟩
        have : ¬ ∀ s ∈ A, ∀ s' ∈ T, IsUnitStep s s' → s' ∈ A := fun h => hne (hc A hAT hAne h)
        push_neg at this
        obtain ⟨s, hs, s', hs'T, hst, hs'A⟩ := this
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
        have hjk : j < k := Finset.mem_range.mp hj
        refine ⟨Function.update e k s', ?_, ?_, ?_⟩
        · intro a ha b hb hab
          simp only [mem_Iio] at ha hb
          by_cases hak : a = k <;> by_cases hbk : b = k
          · rw [hak, hbk]
          · subst hak
            rw [Function.update_self, Function.update_of_ne hbk] at hab
            exact absurd (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr (by omega), hab.symm⟩) hs'A
          · subst hbk
            rw [Function.update_self, Function.update_of_ne hak] at hab
            exact absurd (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr (by omega), hab⟩) hs'A
          · rw [Function.update_of_ne hak, Function.update_of_ne hbk] at hab
            exact hinj (mem_Iio.mpr (by omega)) (mem_Iio.mpr (by omega)) hab
        · intro i hi
          by_cases hik : i = k
          · subst hik; rw [Function.update_self]; exact hs'T
          · rw [Function.update_of_ne hik]; exact hmem i (by omega)
        · intro k' hk'0 hk'
          by_cases hkk : k' = k
          · subst hkk
            refine ⟨j, hjk, ?_⟩
            rw [Function.update_self, Function.update_of_ne (by omega)]
            exact hst
          · obtain ⟨j', hj', h'⟩ := hadj k' hk'0 (by omega)
            refine ⟨j', hj', ?_⟩
            rw [Function.update_of_ne (by omega), Function.update_of_ne hkk]
            exact h'
  obtain ⟨e, h1, h2, h3⟩ := key T.card (Finset.card_pos.mpr hT) le_rfl
  exact ⟨T.card, e, rfl, h1, h2, h3⟩

/-- **The self-avoiding lattice cycle.** For a nonempty connected finite set `T` of squares there
is a self-avoiding closed lattice path on the fine lattice, of length `L ≥ 24`, inside the union of
the closed squares, with a depth-1 point in every square. (`c i` for `i ≥ L` is irrelevant.) -/
theorem exists_latticeCycle (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (hc : PolyConnected T) :
    ∃ (L : ℕ) (c : ℕ → ℤ × ℤ), 24 ≤ L ∧ InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStep (c i) (c (i + 1))) ∧ IsUnitStep (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InSq s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InSqInt s (c i) := by
  obtain ⟨L, c, -, h⟩ := exists_latticeCycle' T hT hc
  exact ⟨L, c, h⟩

/-- The cycle minus its closing step: a `LatticePath` with `n = L - 1 ≥ 23` steps. -/
theorem exists_latticePath_of_polyomino (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (hc : PolyConnected T) :
    ∃ (n : ℕ) (P : LatticePath n), 23 ≤ n ∧
      (∀ i ≤ n, ∃ s ∈ T, InSq s (P.c i)) ∧
      ∀ s ∈ T, ∃ i ≤ n, InSqInt s (P.c i) := by
  obtain ⟨L, c, h24, hinj, hstep, -, hsq, hint⟩ := exists_latticeCycle T hT hc
  refine ⟨L - 1, ⟨c, ?_, fun i hi => hstep i (by omega)⟩, by omega, fun i hi => hsq i (by omega),
    fun s hs => ?_⟩
  · intro a ha b hb hab
    exact hinj (mem_Iio.mpr (by simp only [mem_Iic] at ha; omega))
      (mem_Iio.mpr (by simp only [mem_Iic] at hb; omega)) hab
  · obtain ⟨i, hi, h⟩ := hint s hs
    exact ⟨i, by omega, h⟩

/-! ### The squares meeting a plane continuum -/

/-- The closed square `s` of side `δ` in the `(e₁, e₂)`-plane. -/
def sqSet (e₁ e₂ : E) (δ : ℝ) (s : ℤ × ℤ) : Set E :=
  {x | δ * s.1 ≤ inner ℝ x e₁ ∧ inner ℝ x e₁ ≤ δ * (s.1 + 1) ∧
    δ * s.2 ≤ inner ℝ x e₂ ∧ inner ℝ x e₂ ≤ δ * (s.2 + 1)}

/-- The squares meeting `g`. -/
def squaresMeeting (e₁ e₂ : E) (δ : ℝ) (g : Set E) : Set (ℤ × ℤ) :=
  {s | (sqSet e₁ e₂ δ s ∩ g).Nonempty}

/-- A two-dimensional real inner product space has an orthonormal pair spanning it. -/
theorem exists_orthonormal_pair_span [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    ∃ e₁ e₂ : E, Orthonormal ℝ ![e₁, e₂] ∧
      ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂ := by
  let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
  refine ⟨b 0, b 1, ?_, fun x => ?_⟩
  · have : ![b 0, b 1] = ⇑b := by ext i; fin_cases i <;> rfl
    rw [this]; exact b.orthonormal
  · have := b.sum_repr' x
    rw [Fin.sum_univ_two, real_inner_comm x (b 0), real_inner_comm x (b 1)] at this
    exact this.symm

/-- In the plane, a bounded set meets finitely many squares. -/
theorem squaresMeeting_finite {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : Bornology.IsBounded g) : (squaresMeeting e₁ e₂ δ g).Finite := by
  have h1 : ‖e₁‖ = 1 := by simpa using hon.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using hon.1 1
  obtain ⟨R, hR⟩ := hg.subset_closedBall 0
  set M : ℤ := ⌈R / δ⌉ + 1
  have hRd : R / δ ≤ ⌈R / δ⌉ := Int.le_ceil _
  have bound : ∀ (t : ℝ) (a : ℤ), |t| ≤ R → δ * a ≤ t → t ≤ δ * (a + 1) → -M ≤ a ∧ a ≤ M := by
    intro t a ht h1 h2
    have k1 : (a : ℝ) ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith [(abs_le.mp ht).2]
    have k2 : (-R) / δ ≤ a + 1 := by rw [div_le_iff₀ hδ]; linarith [(abs_le.mp ht).1]
    rw [neg_div] at k2
    have k3 : (a : ℝ) ≤ ⌈R / δ⌉ := k1.trans hRd
    have k4 : -((⌈R / δ⌉ : ℤ) : ℝ) - 1 ≤ a := by linarith
    constructor
    · have : ((-M : ℤ) : ℝ) ≤ a := by simp only [M]; push_cast; linarith
      exact_mod_cast this
    · have : (a : ℝ) ≤ ((M : ℤ) : ℝ) := by simp only [M]; push_cast; linarith
      exact_mod_cast this
  refine ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M)).subset ?_
  rintro s ⟨x, ⟨a1, a2, a3, a4⟩, hxg⟩
  have hx : ‖x‖ ≤ R := by simpa using hR hxg
  have hb1 : |inner ℝ x e₁| ≤ R := (abs_real_inner_le_norm x e₁).trans (by rw [h1, mul_one]; exact hx)
  have hb2 : |inner ℝ x e₂| ≤ R := (abs_real_inner_le_norm x e₂).trans (by rw [h2, mul_one]; exact hx)
  exact ⟨bound _ _ hb1 a1 a2, bound _ _ hb2 a3 a4⟩

/-- In the plane, every point lies in some square. -/
theorem exists_sq_mem {e₁ e₂ : E} {δ : ℝ} (hδ : 0 < δ)
    (x : E) : ∃ s, x ∈ sqSet e₁ e₂ δ s := by
  refine ⟨(⌊inner ℝ x e₁ / δ⌋, ⌊inner ℝ x e₂ / δ⌋), ?_⟩
  have f : ∀ t : ℝ, δ * ⌊t / δ⌋ ≤ t ∧ t ≤ δ * (⌊t / δ⌋ + 1) := by
    intro t
    have h1 := Int.floor_le (t / δ)
    have h2 := Int.lt_floor_add_one (t / δ)
    constructor
    · have := mul_le_mul_of_nonneg_left h1 hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
    · have := mul_le_mul_of_nonneg_left h2.le hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
  exact ⟨(f _).1, (f _).2, (f _).1, (f _).2⟩

/-- A square of side `δ` has diameter `δ √2` (in the plane; `≤ 2 δ` is enough). -/
theorem diam_sqSet_le {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂])
    (hspan : ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂) {δ : ℝ} (hδ : 0 < δ)
    (s : ℤ × ℤ) : ∀ x ∈ sqSet e₁ e₂ δ s, ∀ y ∈ sqSet e₁ e₂ δ s, dist x y ≤ 2 * δ := by
  intro x ⟨x1, x2, x3, x4⟩ y ⟨y1, y2, y3, y4⟩
  set a := inner ℝ (x - y) e₁ with ha
  set b := inner ℝ (x - y) e₂ with hb
  have ha' : a = inner ℝ x e₁ - inner ℝ y e₁ := inner_sub_left _ _ _
  have hb' : b = inner ℝ x e₂ - inner ℝ y e₂ := inner_sub_left _ _ _
  have hxy : x - y = Band.planeL e₁ e₂ (a, b) := hspan (x - y)
  have hn := Band.norm_planeL_sq hon (a, b)
  rw [← hxy] at hn
  simp only at hn
  have ka : a ^ 2 ≤ δ ^ 2 := by
    have : -δ ≤ a ∧ a ≤ δ := ⟨by linarith, by linarith⟩
    nlinarith
  have kb : b ^ 2 ≤ δ ^ 2 := by
    have : -δ ≤ b ∧ b ≤ δ := ⟨by linarith, by linarith⟩
    nlinarith
  rw [dist_eq_norm]
  by_contra hcon
  push_neg at hcon
  have : (2 * δ) ^ 2 < ‖x - y‖ ^ 2 := by
    have := norm_nonneg (x - y)
    nlinarith
  nlinarith

/-- A fine lattice point in the closed square `s` (fine coordinates) is in `sqSet s`, and a
depth-1 point is in it too. -/
theorem latticePt_mem_sqSet {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {s p : ℤ × ℤ} (h : InSq s p) : latticePt e₁ e₂ (δ / 8) p ∈ sqSet e₁ e₂ δ s := by
  have i1 : inner ℝ (latticePt e₁ e₂ (δ / 8) p) e₁ = δ / 8 * p.1 := by
    have := Band.inner_planeL hon (Band.toR p) (1, 0)
    simp only [Band.planeL_apply, Band.toR, one_smul, zero_smul, add_zero, mul_one,
      mul_zero] at this
    rw [latticePt, real_inner_smul_left, this]
  have i2 : inner ℝ (latticePt e₁ e₂ (δ / 8) p) e₂ = δ / 8 * p.2 := by
    have := Band.inner_planeL hon (Band.toR p) (0, 1)
    simp only [Band.planeL_apply, Band.toR, one_smul, zero_smul, zero_add, mul_one,
      mul_zero] at this
    rw [latticePt, real_inner_smul_left, this]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have r1 : (8 * s.1 : ℝ) ≤ p.1 := by exact_mod_cast h1
  have r2 : (p.1 : ℝ) ≤ 8 * s.1 + 8 := by exact_mod_cast h2
  have r3 : (8 * s.2 : ℝ) ≤ p.2 := by exact_mod_cast h3
  have r4 : (p.2 : ℝ) ≤ 8 * s.2 + 8 := by exact_mod_cast h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [i1, i2] <;> nlinarith

/-- **The squares meeting a connected set are connected.** If `T = A ⊔ B` with no adjacency
between `A` and `B`, then `g ∩ ⋃ A` and `g ∩ ⋃ B` are closed, cover `g`, and are nonempty, so
they share a point `x ∈ g` lying in some `s_A ∈ A` and `s_B ∈ B`; `s_A ∩ s_B` is a side (then they
are adjacent) or a single corner `x`; in the latter case the other two squares at that corner
contain `x ∈ g`, so lie in `T`, and each is adjacent to both `s_A` and `s_B`. -/
theorem squaresMeeting_connected {e₁ e₂ : E} {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : IsConnected g) (hfin : (squaresMeeting e₁ e₂ δ g).Finite) :
    PolyConnected hfin.toFinset := by
  intro A hAT hAne hcl
  by_contra hne
  obtain ⟨b₀, hb₀T, hb₀A⟩ : ∃ b ∈ hfin.toFinset, b ∉ A := by
    by_contra h
    push_neg at h
    exact hne (Finset.Subset.antisymm hAT h)
  have hclosed : ∀ s, IsClosed (sqSet e₁ e₂ δ s) := by
    intro s
    have c1 : Continuous fun x : E => inner ℝ x e₁ := continuous_id.inner continuous_const
    have c2 : Continuous fun x : E => inner ℝ x e₂ := continuous_id.inner continuous_const
    simp only [sqSet, setOf_and]
    exact (isClosed_le continuous_const c1).inter ((isClosed_le c1 continuous_const).inter
      ((isClosed_le continuous_const c2).inter (isClosed_le c2 continuous_const)))
  set B := hfin.toFinset \ A
  have hU : IsClosed (⋃ s ∈ A, sqSet e₁ e₂ δ s) := isClosed_biUnion_finset fun s _ => hclosed s
  have hV : IsClosed (⋃ s ∈ B, sqSet e₁ e₂ δ s) := isClosed_biUnion_finset fun s _ => hclosed s
  have hcover : g ⊆ (⋃ s ∈ A, sqSet e₁ e₂ δ s) ∪ ⋃ s ∈ B, sqSet e₁ e₂ δ s := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_sq_mem hδ x
    have hsT : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hs, hx⟩
    by_cases hsA : s ∈ A
    · exact Or.inl (mem_biUnion hsA hs)
    · exact Or.inr (mem_biUnion (Finset.mem_sdiff.mpr ⟨hsT, hsA⟩) hs)
  have hgU : (g ∩ ⋃ s ∈ A, sqSet e₁ e₂ δ s).Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨x, hxs, hxg⟩ := hfin.mem_toFinset.mp (hAT ha)
    exact ⟨x, hxg, mem_biUnion ha hxs⟩
  have hgV : (g ∩ ⋃ s ∈ B, sqSet e₁ e₂ δ s).Nonempty := by
    obtain ⟨x, hxs, hxg⟩ := hfin.mem_toFinset.mp hb₀T
    exact ⟨x, hxg, mem_biUnion (Finset.mem_sdiff.mpr ⟨hb₀T, hb₀A⟩) hxs⟩
  obtain ⟨x, hxg, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hg.isPreconnected _ _ hU hV hcover hgU hgV
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxU
  obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxV
  obtain ⟨hbT, hbA⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨a1, a2, a3, a4⟩ := hxa
  obtain ⟨b1, b2, b3, b4⟩ := hxb
  have lt : ∀ u v : ℤ, δ * u ≤ δ * (v + 1) → u ≤ v + 1 := by
    intro u v h
    have : (u : ℝ) ≤ v + 1 := le_of_mul_le_mul_left h hδ
    exact_mod_cast this
  have q1 := lt a.1 b.1 (by linarith)
  have q2 := lt b.1 a.1 (by linarith)
  have q3 := lt a.2 b.2 (by linarith)
  have q4 := lt b.2 a.2 (by linarith)
  have ustep : ∀ p q : ℤ × ℤ, (q.1 = p.1 ∧ (q.2 - p.2 = 1 ∨ q.2 - p.2 = -1)) ∨
      (q.2 = p.2 ∧ (q.1 - p.1 = 1 ∨ q.1 - p.1 = -1)) → IsUnitStep p q := by
    intro p q h
    unfold IsUnitStep
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp [h1, h2]
  by_cases e1 : a.1 = b.1
  · have e2 : a.2 ≠ b.2 := fun e2 => hbA (by rwa [show b = a from Prod.ext e1.symm e2.symm])
    exact hbA (hcl a ha b hbT (ustep a b (Or.inl ⟨e1.symm, by omega⟩)))
  by_cases e2 : a.2 = b.2
  · exact hbA (hcl a ha b hbT (ustep a b (Or.inr ⟨e2.symm, by omega⟩)))
  have hxc : x ∈ sqSet e₁ e₂ δ (a.1, b.2) := ⟨a1, a2, b3, b4⟩
  have hcT : (a.1, b.2) ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hxc, hxg⟩
  have hcA := hcl a ha _ hcT (ustep a (a.1, b.2) (Or.inl ⟨rfl, by simp only; omega⟩))
  exact hbA (hcl _ hcA b hbT (ustep (a.1, b.2) b (Or.inr ⟨rfl, by simp only; omega⟩)))

/-! ### Assembly -/

/-- **The density lemma in the plane** (threaded form). Take `δ = ε/4`; the squares of side `δ`
meeting `g`; the lattice path of `exists_latticePath_of_polyomino` at fine mesh `δ/8`; the chain
of `exists_threadedChain_of_latticePath`. Links have diameter `≤ 16 (δ/8) = ε/2`; the union is
within `δ/8` of the polygonal path, which lies in the union of the closed squares, each meeting `g`
and of diameter `≤ 2δ`; every `x ∈ g` lies in a square, which has a depth-1 point of the path,
within `δ/8` of the union. -/
theorem geomLemma'_of_finrank_two [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    GeomLemma' E := by
  intro g hg ε hε
  obtain ⟨e₁, e₂, hon, hspan⟩ := exists_orthonormal_pair_span h
  set δ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hfin := squaresMeeting_finite hon hδ hg.1.isBounded
  have hpc := squaresMeeting_connected hδ hg.2 hfin
  obtain ⟨x₀, hx₀⟩ := hg.2.nonempty
  obtain ⟨s₀, hs₀⟩ := exists_sq_mem hδ x₀
  have hTne : hfin.toFinset.Nonempty := ⟨s₀, hfin.mem_toFinset.mpr ⟨x₀, hs₀, hx₀⟩⟩
  obtain ⟨n, P, hn, hPsq, hPint⟩ := exists_latticePath_of_polyomino _ hTne hpc
  have hδ8 : 0 < δ / 8 := by positivity
  obtain ⟨m, D, hm, hD, hdiam, hunion, hnear⟩ :=
    exists_threadedChain_of_latticePath hon hδ8 (by omega : 22 ≤ n) P
  have hpt : ∀ i ≤ n, ∃ w ∈ g, dist (latticePt e₁ e₂ (δ / 8) (P.c i)) w ≤ 2 * δ := by
    intro i hi
    obtain ⟨s, hs, hsq⟩ := hPsq i hi
    obtain ⟨w, hws, hwg⟩ := hfin.mem_toFinset.mp hs
    exact ⟨w, hwg, diam_sqSet_le hon hspan hδ s _ (latticePt_mem_sqSet hon hδ hsq) w hws⟩
  refine ⟨m, D, hm, hD, fun j => (hdiam j).trans_lt (by linarith), ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hunion hy)
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    have hi' : i < n := hi
    have hstep : dist (latticePt e₁ e₂ (δ / 8) (P.c (i + 1))) (latticePt e₁ e₂ (δ / 8) (P.c i)) =
        δ / 8 := by
      rw [dist_eq_norm, latticePt_sub, norm_smul, Band.norm_planeL_unit hon (Band.step_unit P hi'),
        Real.norm_of_nonneg hδ8.le, mul_one]
    have hzd : dist z (latticePt e₁ e₂ (δ / 8) (P.c i)) ≤ δ / 8 :=
      (convex_closedBall (latticePt e₁ e₂ (δ / 8) (P.c i)) (δ / 8)).segment_subset
        (mem_closedBall_self hδ8.le) (by rw [mem_closedBall, hstep]) hzi
    obtain ⟨w, hwg, hw⟩ := hpt i hi'.le
    refine mem_thickening_iff.mpr ⟨w, hwg, ?_⟩
    linarith [dist_triangle y z (latticePt e₁ e₂ (δ / 8) (P.c i)),
      dist_triangle y (latticePt e₁ e₂ (δ / 8) (P.c i)) w]
  · intro x hx
    obtain ⟨s, hs⟩ := exists_sq_mem hδ x
    have hsT : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hs, hx⟩
    obtain ⟨i, hi, hint⟩ := hPint s hsT
    have h1 := diam_sqSet_le hon hspan hδ s x hs _
      (latticePt_mem_sqSet hon hδ (LCyc.inSq_of_inSqInt hint))
    obtain ⟨y, hy, hyd⟩ := hnear i hi
    refine mem_thickening_iff.mpr ⟨y, hy, ?_⟩
    linarith [dist_triangle x (latticePt e₁ e₂ (δ / 8) (P.c i)) y,
      dist_comm y (latticePt e₁ e₂ (δ / 8) (P.c i))]

/-- **Density of pseudo-arcs in the plane.** -/
theorem dense_pseudoArcs_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  dense_pseudoArcs_of' (geomLemma'_of_finrank_two h)

/-- **Bing 1951 (Pacific), Theorem 2, in the plane**: the pseudo-arcs form a dense `G_δ` in the
space of compact continua of a two-dimensional real inner product space. -/
theorem theorem2_HIC_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  theorem2_HIC_of' (geomLemma'_of_finrank_two h)

/-- The snake-like continua form a `G_δ` in `C(S)` (complement of the union of the closed sets
`isClosed_notCoverable i`, via `Most.isSnakeLike_iff`). -/
theorem isGδ_snakeLike {S : Type*} [MetricSpace S] :
    IsGδ {K : Cont S | IsSnakeLike (K.1 : Set S)} := by
  have e : {K : Cont S | IsSnakeLike (K.1 : Set S)} =
      ⋂ i : ℕ, {K : Cont S | ¬ ∃ (n : ℕ) (D : Chain S n), IsEpsChain D (1 / ((i : ℝ) + 1)) ∧
        (K.1 : Set S) ⊆ D.union}ᶜ := by
    ext K
    simp only [mem_setOf_eq, mem_iInter, mem_compl_iff, not_not]
    exact Most.isSnakeLike_iff K
  rw [e]
  exact IsGδ.iInter fun i => (isClosed_notCoverable i).isOpen_compl.isGδ

/-- Density of snake-like continua in the plane (pseudo-arcs are snake-like). -/
theorem dense_snakeLike_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} :=
  (dense_pseudoArcs_plane h).mono fun _ hK => hK.1

/-- **Bing 1951 (Duke), Theorem 2, in the plane**: "most" compact continua are snake-like — the
snake-like continua form a dense `G_δ` in the space of compact continua. -/
theorem theorem2_1951_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsSnakeLike (K.1 : Set E)} :=
  ⟨dense_snakeLike_plane h, isGδ_snakeLike⟩

/-! The general-`E` statements of batch 111 (`geomLemma'_of_two_le_rank`, `dense_pseudoArcs`,
`theorem2_HIC`, `theorem2_1951`) were moved to `HPC/Plane/CubeCycle.lean` in batch 113, where they
are proved. -/

end HPC.Plane
