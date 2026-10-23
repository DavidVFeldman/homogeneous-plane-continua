import HPC.Plane.CubeCycleAux

/-!
# Batch 113: the lattice cycle through the cubes of `ℤ^d` meeting a continuum; the density lemma
# in every dimension; Bing's Theorem 2 (Pacific) and Theorem 2 (Duke) as he states them

Saved from the uploaded skeleton as `HPC/Plane/CubeCycle.lean`; `import HPC.Plane.CubeCycle` is
added at the end of `HPC.lean`. Split for length (the commission allows it):
* `HPC/Plane/CubeLoop.lean`: the definitions `eZ`, `InCube`, `InCubeInt`, `CubeConnected`,
  `faceDir`, `CubeLoop` and item 1 (`exists_cubeLoop_two`, `exists_cubeLoop_succ`,
  `exists_cubeLoop`);
* `HPC/Plane/CubeCycleAux.lean`: the invariant and the splice of item 2;
* this file: item 2 (`exists_latticeCycleN`, `exists_latticePathN_of_cubes`), item 3 (the cubes of
  `E`), item 4 (assembly), and — moved here from `HPC/Plane/LatticeCycle.lean` —
  `geomLemma'_of_two_le_rank`, `dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951`, now proved.

Plan. The plane construction (`LatticeCycleAux.lean`) is: a 24-point loop in the square, with a
*designated pair* (`pA`, `pB`) on each of the four sides, and a splice that attaches a new square
across a free side by replacing the designated edge of that side with a detour through the new
square's loop. In `ℤ^d` the same induction runs with the loop replaced by an abstract **cube loop**
(`CubeLoop d`): a self-avoiding closed lattice path through depth-1 points of the cube `(0,8)^d`,
with a designated edge on each of the `2d` faces, the designated points pairwise distinct across
faces, and the two designated edges of opposite faces translates of each other by `6 e_i`. Cube
loops exist for every `d ≥ 2` by induction (the plane loop for `d = 2`; doubling, of length
`2 |l| + 10`). The cubes of a `d`-dimensional `E` meeting a continuum form a connected finite set;
with `bandN` the density lemma follows for `finrank = d ≥ 3`. Finally `geomLemma'_of_subspaces`
reduces every `E` of `rank ≥ 2` to its finite-dimensional subspaces, where `finrank = 2` is the
plane case and `finrank ≥ 3` is this one. That closes OPEN.md item 4.

**Lengths.** Loop: `24` for `d = 2`, `L_{d+1} = 2 L_d + 10` (so `L_d = 34 · 2^(d-2) - 10`).
Cycle through `N` cubes: `L₀ + (L₀ + 2)(N - 1)` for the loop length `L₀`
(`exists_latticeCycleN_of_loop`).

**Shape changes from the skeleton.**
* `exists_cubeLoop_succ`: the hypothesis `2 ≤ d` is dropped (unused: the field `big` provides the
  two edges of the doubling step).
* `geomLemma'_of_two_le_rank'` is not kept: its statement is `geomLemma'_of_two_le_rank`, moved
  here from `LatticeCycle.lean` with the same statement and proved (the commission's preferred
  option).
-/

namespace HPC.Plane

open Set Metric BandNAux BandN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The cycle through a connected set of cubes -/

/-- **The self-avoiding lattice cycle through the cubes** (the plane's `exists_latticeCycle` in
`ℤ^d`): the invariant and the splice of `LatticeCycleAux.lean`, with the cube loop's `A`, `B`,
`edge`, `distinct`, `A_opp`, `B_opp` in place of `pA`, `pB`, `D_pair`, `pair_eq`, `side_eq`,
`dvec_opp`. The detour across the face `(i, b)` of `s` into `ℓ = s + faceDir i b`:
`x + e, x + 2e, … (the loop of ℓ the long way from its designated edge of the face (i, ¬b)) …,
y + 2e, y + e`, where `x → y` is the designated edge of `(i, b)` in `s`. Length `L₀ + (L₀ + 2)
(N - 1)` for the loop length `L₀` (`exists_latticeCycleN_of_loop`). -/
theorem exists_latticeCycleN {d : ℕ} (hd : 2 ≤ d) (T : Finset (Fin d → ℤ)) (hT : T.Nonempty)
    (hc : CubeConnected T) :
    ∃ (L : ℕ) (c : ℕ → (Fin d → ℤ)), 24 ≤ L ∧ InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStepN (c i) (c (i + 1))) ∧ IsUnitStepN (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InCube s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InCubeInt s (c i) := by
  obtain ⟨l, hl⟩ := exists_cubeLoop_ge hd
  obtain ⟨L, c, -, hL, h⟩ := exists_latticeCycleN_of_loop l T hT hc
  exact ⟨L, c, hl.trans hL, h⟩

/-- The cycle minus its closing step: a `LatticePathN` with `n = L - 1 ≥ 23` steps. -/
theorem exists_latticePathN_of_cubes {d : ℕ} (hd : 2 ≤ d) (T : Finset (Fin d → ℤ))
    (hT : T.Nonempty) (hc : CubeConnected T) :
    ∃ (n : ℕ) (P : LatticePathN d n), 23 ≤ n ∧
      (∀ i ≤ n, ∃ s ∈ T, InCube s (P.c i)) ∧
      ∀ s ∈ T, ∃ i ≤ n, InCubeInt s (P.c i) := by
  obtain ⟨L, c, h24, hinj, hstep, -, hsq, hint⟩ := exists_latticeCycleN hd T hT hc
  refine ⟨L - 1, ⟨c, ?_, fun i hi => hstep i (by omega)⟩, by omega, fun i hi => hsq i (by omega),
    fun s hs => ?_⟩
  · intro a ha b hb hab
    exact hinj (mem_Iio.mpr (by simp only [mem_Iic] at ha; omega))
      (mem_Iio.mpr (by simp only [mem_Iic] at hb; omega)) hab
  · obtain ⟨i, hi, h⟩ := hint s hs
    exact ⟨i, by omega, h⟩

/-! ### The cubes of a `d`-dimensional `E` -/

/-- The closed cube `s` of side `δ` along the orthonormal family `e`. -/
def cubeSet {d : ℕ} (e : Fin d → E) (δ : ℝ) (s : Fin d → ℤ) : Set E :=
  {x | ∀ i, δ * s i ≤ inner ℝ x (e i) ∧ inner ℝ x (e i) ≤ δ * (s i + 1)}

/-- The cubes meeting `g`. -/
def cubesMeeting {d : ℕ} (e : Fin d → E) (δ : ℝ) (g : Set E) : Set (Fin d → ℤ) :=
  {s | (cubeSet e δ s ∩ g).Nonempty}

/-- A `d`-dimensional real inner product space has an orthonormal basis `Fin d → E`. -/
theorem exists_orthonormal_basis_fin [FiniteDimensional ℝ E] {d : ℕ}
    (h : Module.finrank ℝ E = d) :
    ∃ e : Fin d → E, Orthonormal ℝ e ∧ ∀ x : E, x = ∑ i, (inner ℝ x (e i)) • e i := by
  let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
  refine ⟨b, b.orthonormal, fun x => ?_⟩
  have := b.sum_repr' x
  simp only [real_inner_comm x] at this ⊢
  exact this.symm

theorem cubesMeeting_finite {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : Bornology.IsBounded g) : (cubesMeeting e δ g).Finite := by
  obtain ⟨R, hR⟩ := hg.subset_closedBall 0
  set M : ℤ := ⌈R / δ⌉ + 1
  have hRd : R / δ ≤ ⌈R / δ⌉ := Int.le_ceil _
  have bound : ∀ (t : ℝ) (a : ℤ), |t| ≤ R → δ * a ≤ t → t ≤ δ * (a + 1) → -M ≤ a ∧ a ≤ M := by
    intro t a ht h1 h2
    have k1 : (a : ℝ) ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith [(abs_le.mp ht).2]
    have k2 : (-R) / δ ≤ a + 1 := by rw [div_le_iff₀ hδ]; linarith [(abs_le.mp ht).1]
    rw [neg_div] at k2
    have k3 : (a : ℝ) ≤ ⌈R / δ⌉ := k1.trans hRd
    constructor
    · have : ((-M : ℤ) : ℝ) ≤ a := by simp only [M]; push_cast; linarith
      exact_mod_cast this
    · have : (a : ℝ) ≤ ((M : ℤ) : ℝ) := by simp only [M]; push_cast; linarith
      exact_mod_cast this
  refine (Set.Finite.pi (t := fun _ : Fin d => Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
  rintro s ⟨x, hxs, hxg⟩
  have hx : ‖x‖ ≤ R := by simpa using hR hxg
  intro i _
  have hb : |inner ℝ x (e i)| ≤ R :=
    (abs_real_inner_le_norm x (e i)).trans (by rw [hon.1 i, mul_one]; exact hx)
  exact bound _ _ hb (hxs i).1 (hxs i).2

theorem exists_cube_mem {d : ℕ} (e : Fin d → E) {δ : ℝ} (hδ : 0 < δ) (x : E) :
    ∃ s, x ∈ cubeSet e δ s := by
  refine ⟨fun i => ⌊inner ℝ x (e i) / δ⌋, fun i => ?_⟩
  have h1 := Int.floor_le (inner ℝ x (e i) / δ)
  have h2 := Int.lt_floor_add_one (inner ℝ x (e i) / δ)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  · have := mul_le_mul_of_nonneg_left h2.le hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this

/-- A cube of side `δ` has diameter `δ √d` (in `E` spanned by `e`); `≤ √d · δ` is stated. -/
theorem diam_cubeSet_le {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e)
    (hspan : ∀ x : E, x = ∑ i, (inner ℝ x (e i)) • e i) {δ : ℝ} (hδ : 0 < δ) (s : Fin d → ℤ) :
    ∀ x ∈ cubeSet e δ s, ∀ y ∈ cubeSet e δ s, dist x y ≤ Real.sqrt d * δ := by
  intro x hx y hy
  set a : Fin d → ℝ := fun i => inner ℝ (x - y) (e i) with ha
  have hxy : x - y = vecL e a := by rw [vecL_apply]; exact hspan (x - y)
  have hn := norm_vecL_sq hon a
  rw [← hxy] at hn
  have ka : ∀ i, a i * a i ≤ δ ^ 2 := by
    intro i
    have : a i = inner ℝ x (e i) - inner ℝ y (e i) := inner_sub_left _ _ _
    have h1 := hx i
    have h2 := hy i
    have : -δ ≤ a i ∧ a i ≤ δ := ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    nlinarith
  have hsum : ∑ i, a i * a i ≤ d * δ ^ 2 := by
    calc ∑ i, a i * a i ≤ ∑ _i : Fin d, δ ^ 2 := Finset.sum_le_sum fun i _ => ka i
      _ = d * δ ^ 2 := by simp
  rw [dist_eq_norm]
  have hsq : ‖x - y‖ ^ 2 ≤ (Real.sqrt d * δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem inner_latticePtN {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (δ : ℝ)
    (p : Fin d → ℤ) (i : Fin d) : inner ℝ (latticePtN e δ p) (e i) = δ * p i := by
  rw [latticePtN, real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left, orthonormal_iff_ite.mp hon, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem latticePtN_mem_cubeSet {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {s p : Fin d → ℤ} (h : InCube s p) : latticePtN e (δ / 8) p ∈ cubeSet e δ s := by
  intro i
  rw [inner_latticePtN hon]
  have r1 : (8 * s i : ℝ) ≤ p i := by exact_mod_cast (h i).1
  have r2 : (p i : ℝ) ≤ 8 * s i + 8 := by exact_mod_cast (h i).2
  constructor <;> nlinarith

theorem isClosed_cubeSet {d : ℕ} (e : Fin d → E) (δ : ℝ) (s : Fin d → ℤ) :
    IsClosed (cubeSet e δ s) := by
  have : cubeSet e δ s = ⋂ i, ({x : E | δ * s i ≤ inner ℝ x (e i)} ∩
      {x : E | inner ℝ x (e i) ≤ δ * (s i + 1)}) := by
    ext x; simp [cubeSet]
  rw [this]
  refine isClosed_iInter fun i => ?_
  have c1 : Continuous fun x : E => inner ℝ x (e i) := continuous_id.inner continuous_const
  exact (isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)

/-- **The cubes meeting a connected set are connected.** If `x ∈ g` lies in cubes `a` and `b`,
then `|a i - b i| ≤ 1` for every `i`, and changing the coordinates of `a` into those of `b` one
at a time passes through cubes all containing `x`, consecutive ones adjacent; so a split of the
cubes with no adjacency across it would split `g` into two closed sets that do not meet (the plane
argument of `squaresMeeting_connected`, by induction on the number of differing coordinates). -/
theorem cubesMeeting_connected {d : ℕ} (e : Fin d → E) {δ : ℝ} (hδ : 0 < δ) {g : Set E}
    (hg : IsConnected g) (hfin : (cubesMeeting e δ g).Finite) :
    CubeConnected hfin.toFinset := by
  classical
  intro A hAT hAne hcl
  by_contra hne
  obtain ⟨b₀, hb₀T, hb₀A⟩ : ∃ b ∈ hfin.toFinset, b ∉ A := by
    by_contra h
    push_neg at h
    exact hne (Finset.Subset.antisymm hAT h)
  set B := hfin.toFinset \ A
  have hU : IsClosed (⋃ s ∈ A, cubeSet e δ s) :=
    isClosed_biUnion_finset fun s _ => isClosed_cubeSet e δ s
  have hV : IsClosed (⋃ s ∈ B, cubeSet e δ s) :=
    isClosed_biUnion_finset fun s _ => isClosed_cubeSet e δ s
  have hcover : g ⊆ (⋃ s ∈ A, cubeSet e δ s) ∪ ⋃ s ∈ B, cubeSet e δ s := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_cube_mem e hδ x
    have hsT : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hs, hx⟩
    by_cases hsA : s ∈ A
    · exact Or.inl (mem_biUnion hsA hs)
    · exact Or.inr (mem_biUnion (Finset.mem_sdiff.mpr ⟨hsT, hsA⟩) hs)
  have hgU : (g ∩ ⋃ s ∈ A, cubeSet e δ s).Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨x, hxs, hxg⟩ := hfin.mem_toFinset.mp (hAT ha)
    exact ⟨x, hxg, mem_biUnion ha hxs⟩
  have hgV : (g ∩ ⋃ s ∈ B, cubeSet e δ s).Nonempty := by
    obtain ⟨x, hxs, hxg⟩ := hfin.mem_toFinset.mp hb₀T
    exact ⟨x, hxg, mem_biUnion (Finset.mem_sdiff.mpr ⟨hb₀T, hb₀A⟩) hxs⟩
  obtain ⟨x, hxg, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hg.isPreconnected _ _ hU hV hcover hgU hgV
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxU
  obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxV
  obtain ⟨hbT, hbA⟩ := Finset.mem_sdiff.mp hb
  have lt : ∀ u v : ℤ, δ * u ≤ δ * (v + 1) → u ≤ v + 1 := by
    intro u v h
    have : (u : ℝ) ≤ v + 1 := le_of_mul_le_mul_left h hδ
    exact_mod_cast this
  -- change the coordinates of a cube containing `x` into those of `b`, one at a time
  have key : ∀ n, ∀ a' ∈ A, x ∈ cubeSet e δ a' →
      (Finset.univ.filter fun i => a' i ≠ b i).card = n → b ∈ A := by
    intro n
    induction n with
    | zero =>
      intro a' ha' _ hn
      have : a' = b := by
        funext i
        by_contra hi
        have : i ∈ Finset.univ.filter fun i => a' i ≠ b i := by simp [hi]
        rw [Finset.card_eq_zero.mp hn] at this
        simp at this
      exact this ▸ ha'
    | succ n ih =>
      intro a' ha' hxa' hn
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < _ by rw [hn]; omega)
      have hi' : a' i ≠ b i := (Finset.mem_filter.mp hi).2
      set a'' := Function.update a' i (b i)
      have hxa'' : x ∈ cubeSet e δ a'' := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [a'', Function.update_self]; exact hxb j
        · simp only [a'', Function.update_of_ne hj]; exact hxa' j
      have hT'' : a'' ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hxa'', hxg⟩
      have q1 := lt (a' i) (b i) (by linarith [(hxa' i).1, (hxb i).2])
      have q2 := lt (b i) (a' i) (by linarith [(hxb i).1, (hxa' i).2])
      have hstep : IsUnitStepN a' a'' := by
        unfold IsUnitStepN
        rw [Finset.sum_eq_single i]
        · simp only [a'', Function.update_self]
          rcases lt_or_gt_of_ne hi' with h | h
          · rw [abs_of_pos (by omega)]; omega
          · rw [abs_of_neg (by omega)]; omega
        · intro j _ hj; simp [a'', Function.update_of_ne hj]
        · simp
      have hA'' := hcl a' ha' a'' hT'' hstep
      refine ih a'' hA'' hxa'' ?_
      have hsub : (Finset.univ.filter fun j => a'' j ≠ b j) =
          (Finset.univ.filter fun j => a' j ≠ b j).erase i := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [a'']
        · simp [a'', hj]
      rw [hsub, Finset.card_erase_of_mem hi, hn]; rfl
  exact hbA (key _ a ha hxa rfl)

/-! ### Assembly -/

/-- **The density lemma in dimension `d ≥ 3`**: `δ := ε / (4 √d)`, the cubes of side `δ` meeting
`g`, the lattice path at fine mesh `δ/8`, the chain of `exists_threadedChain_of_latticePathN`.
(Constants: links `≤ 16 (δ/8) = 2δ < ε`; union within `δ/8 + δ/8 + √d δ < ε` of `g`; `g` within
`√d δ + δ/8 < ε` of the union.) -/
theorem geomLemma'_of_finrank_ge_three [FiniteDimensional ℝ E] (h : 3 ≤ Module.finrank ℝ E) :
    GeomLemma' E := by
  intro g hg ε hε
  set d := Module.finrank ℝ E with hd
  obtain ⟨e, hon, hspan⟩ := exists_orthonormal_basis_fin (E := E) rfl
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ d by omega)
  set δ := ε / (4 * Real.sqrt d) with hδdef
  have hδ : 0 < δ := by positivity
  have hsdδ : Real.sqrt d * δ = ε / 4 := by
    rw [hδdef]; field_simp
  have hδε : δ ≤ ε / 4 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hfin := cubesMeeting_finite hon hδ hg.1.isBounded
  have hpc := cubesMeeting_connected e hδ hg.2 hfin
  obtain ⟨x₀, hx₀⟩ := hg.2.nonempty
  obtain ⟨s₀, hs₀⟩ := exists_cube_mem e hδ x₀
  have hTne : hfin.toFinset.Nonempty := ⟨s₀, hfin.mem_toFinset.mpr ⟨x₀, hs₀, hx₀⟩⟩
  obtain ⟨n, P, hn, hPsq, hPint⟩ := exists_latticePathN_of_cubes (by omega) _ hTne hpc
  have hδ8 : 0 < δ / 8 := by positivity
  obtain ⟨m, D, hm, hD, hdiam, hunion, hnear⟩ :=
    exists_threadedChain_of_latticePathN h hon hδ8 (by omega : 22 ≤ n) P
  have hpt : ∀ i ≤ n, ∃ w ∈ g, dist (latticePtN e (δ / 8) (P.c i)) w ≤ ε / 4 := by
    intro i hi
    obtain ⟨s, hs, hsq⟩ := hPsq i hi
    obtain ⟨w, hws, hwg⟩ := hfin.mem_toFinset.mp hs
    exact ⟨w, hwg, hsdδ ▸ diam_cubeSet_le hon hspan hδ s _ (latticePtN_mem_cubeSet hon hδ hsq) w
      hws⟩
  refine ⟨m, D, hm, hD, fun j => (hdiam j).trans_lt (by linarith), ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hunion hy)
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    have hi' : i < n := hi
    have hstep : dist (latticePtN e (δ / 8) (P.c (i + 1))) (latticePtN e (δ / 8) (P.c i)) =
        δ / 8 := by
      rw [dist_eq_norm, latticePtN_sub, norm_smul, norm_vecL_unit hon (stepN_unit P hi'),
        Real.norm_of_nonneg hδ8.le, mul_one]
    have hzd : dist z (latticePtN e (δ / 8) (P.c i)) ≤ δ / 8 :=
      (convex_closedBall (latticePtN e (δ / 8) (P.c i)) (δ / 8)).segment_subset
        (mem_closedBall_self hδ8.le) (by rw [mem_closedBall, hstep]) hzi
    obtain ⟨w, hwg, hw⟩ := hpt i hi'.le
    refine mem_thickening_iff.mpr ⟨w, hwg, ?_⟩
    linarith [dist_triangle y z (latticePtN e (δ / 8) (P.c i)),
      dist_triangle y (latticePtN e (δ / 8) (P.c i)) w]
  · intro x hx
    obtain ⟨s, hs⟩ := exists_cube_mem e hδ x
    have hsT : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hs, hx⟩
    obtain ⟨i, hi, hint⟩ := hPint s hsT
    have h1 := diam_cubeSet_le hon hspan hδ s x hs _
      (latticePtN_mem_cubeSet hon hδ (CubeLoopAux.inCube_of_inCubeInt hint))
    obtain ⟨y, hy, hyd⟩ := hnear i hi
    refine mem_thickening_iff.mpr ⟨y, hy, ?_⟩
    linarith [dist_triangle x (latticePtN e (δ / 8) (P.c i)) y,
      dist_comm y (latticePtN e (δ / 8) (P.c i))]

/-- **The density lemma in every finite dimension `≥ 2`**: the plane case
(`geomLemma'_of_finrank_two`) or the previous theorem. -/
theorem geomLemma'_of_finrank [FiniteDimensional ℝ E] (h : 2 ≤ Module.finrank ℝ E) :
    GeomLemma' E := by
  rcases h.eq_or_lt with h2 | h3
  · exact geomLemma'_of_finrank_two h2.symm
  · exact geomLemma'_of_finrank_ge_three h3

/-! ### General `E`: the density lemma and Bing's Theorem 2 (moved from `LatticeCycle.lean`) -/

/-- **The density lemma in dimension `≥ 2`** (Bing 1951 (Pacific), §3, for Euclidean `n`-space
and Hilbert space): `geomLemma'_of_subspaces` with `geomLemma'_of_finrank` for every
finite-dimensional subspace of dimension `≥ 2`. (Moved here from `LatticeCycle.lean` in batch 113
with the same statement; the instance `[CompleteSpace E]` of that statement is not used by the
proof.) -/
theorem geomLemma'_of_two_le_rank [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    GeomLemma' E :=
  geomLemma'_of_subspaces hdim fun _ _ h2 => geomLemma'_of_finrank h2

/-- **Density**: every compact continuum is a Hausdorff limit of pseudo-arcs. -/
theorem dense_pseudoArcs [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  dense_pseudoArcs_of' (geomLemma'_of_two_le_rank hdim)

/-- **Bing 1951 (Pacific), Theorem 2.** In a complete real inner product space of dimension at
least two (Euclidean `n`-space with `n > 1`, or Hilbert space), the pseudo-arcs form a dense `G_δ`
in the space of compact continua: most compact continua are pseudo-arcs. -/
theorem theorem2_HIC [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  theorem2_HIC_of' (geomLemma'_of_two_le_rank hdim)

/-- **Bing 1951 (Duke), Theorem 2**: in a complete real inner product space of dimension at least
two (Euclidean `n`-space with `n > 1`, or Hilbert space), the snake-like continua form a dense
`G_δ` in the space of compact continua. -/
theorem theorem2_1951 [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsSnakeLike (K.1 : Set E)} :=
  ⟨(dense_pseudoArcs hdim).mono fun _ hK => hK.1, isGδ_snakeLike⟩

end HPC.Plane
