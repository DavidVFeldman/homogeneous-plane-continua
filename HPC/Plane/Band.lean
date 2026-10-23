import HPC.Plane.Arcs48
import HPC.Plane.BandAux

/-!
# Batch 109: threaded chains, and the band around a self-avoiding lattice path

Saved from the uploaded skeleton as `HPC/Plane/Band.lean`; `import HPC.Plane.Band` is added at the
end of `HPC.lean`. Elementary integer/real lemmas are in `HPC/Plane/BandAux.lean`.

Purpose: the first half of a proof of the density lemma of Bing 1951 (Pacific) §3 in the plane,
replacing the open `exists_tame_chain_near` (a chain of links that are images of the standard boxes
under a *homeomorphism of `E`*) by what `exists_pseudoArc_in_tameChain` actually uses — a map of
the open standard strip into `E`, continuous and injective on the strip, carrying each standard
rectangle into the corresponding link (`IsThreadedChain`).

Conventions. `E` is a real inner product space; `e₁, e₂` an orthonormal pair; `δ > 0` the lattice
mesh; the lattice point `(a, b) : ℤ × ℤ` sits at `δ • (a • e₁ + b • e₂)`. A self-avoiding lattice
path with `n` steps is `c 0, …, c n`, pairwise distinct, consecutive ones a unit step apart.

**Parametrisation chosen (shape change, recorded in the report).** The corners are *chamfered*
rather than rounded by quarter circles. Write `m_i` for the midpoint of step `i` (`i < n`) and
`N_i` for the left unit normal of step `i`. The path `Γ = roundedPath` is the piecewise-linear
interpolation `Γ (i + 1/2) = m_i`, and the normal field `ν = roundedNormal` the piecewise-linear
interpolation `ν (i + 1/2) = N_i`, both on `τ ∈ [1/2, n - 1/2]`. So on stretch `k`
(`1 ≤ k ≤ n - 1`, `τ = k - 1/2 + s`, `s ∈ [0, 1]`), `Γ τ = (1 - s) m_{k-1} + s m_k` (the straight
half-steps on a straight stretch, the chord between the two midpoints at a corner) and
`ν τ = (1 - s) N_{k-1} + s N_k` (constant on a straight stretch). `‖ν‖ ≤ 1` (in fact
`≥ √2/2`), not `= 1`. The band `(τ, t) ↦ Γ τ + (t δ) • ν τ` is injective on
`[1/2, n - 1/2] × (-1/8, 1/8)`: over stretch `k` it lies in the closed lattice square of side `δ`
centred at `c k`, touching the boundary only at the two ends of the stretch, where it is
`m_i + (t δ) • N_i`; these points determine `i` and `t`.

The strip `(0, 2m+1) × (0, 1)` is threaded through the band by
`(x, y) ↦ band (1/2 + λ x) ((y - 1/2)/4)` with `λ = (n - 1)/(2m+1) ∈ [3, 4)`; that part (item 4)
is in `HPC/Plane/BandChain.lean`.

**Shape changes from the skeleton** (all recorded in `doc/batches/REPORT-batch109.md`):
* Refutations of three statements at degenerate parameters, each proved formally and the statement
  corrected: `stripSet_eq` is false for `m = 0` (`stripSet_zero_ne`; now assumes `0 < m`);
  `stretchTri_subset_ball` is false for `k > n` (`stretchTri_subset_ball_false`; now assumes
  `k ≤ n`); `stretchTri_subset_thickening` is false for `n = 0`
  (`stretchTri_subset_thickening_false`; now assumes `0 < n`).
* `stepMid` is marked `noncomputable` (the skeleton did not compile without it).
* Chamfered corners (above); `norm_roundedNormal` gives `‖ν τ‖ ≤ 1` on `[1/2, n - 1/2]` instead
  of `= 1` on `[0, n]`; `roundedPath_mem_stretchTri` is stated for `1 ≤ k < n` and
  `τ ∈ [k - 1/2, k + 1/2]`; `band_injOn` is on `[1/2, n - 1/2] × (-1/8, 1/8)` and assumes
  `2 ≤ n`. `roundedPath_continuousOn`, `roundedNormal_continuousOn`, `band_continuousOn` hold as
  stated (the maps are continuous everywhere); their unused hypotheses are dropped.
-/

namespace HPC.Plane

open Set Metric BandAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Threaded chains -/

/-- The open strip `(0, 2m+1) × (0, 1)`: the union of the first `m` standard rectangles. -/
def stripSet (m : ℕ) : Set Pt := ⋃ j : Fin m, stdRect j

theorem stripSet_subset (m : ℕ) : stripSet m ⊆ Ioo (0 : ℝ) (2 * m + 1) ×ˢ Ioo (0 : ℝ) 1 := by
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hj
  have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.2
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- **Refutation of the skeleton's `stripSet_eq` at `m = 0`**: `stripSet 0` is empty, the
rectangle `(0, 1) × (0, 1)` is not. The corrected statement `stripSet_eq` assumes `0 < m`. -/
theorem stripSet_zero_ne : stripSet 0 ≠ Ioo (0 : ℝ) (2 * (0 : ℕ) + 1) ×ˢ Ioo (0 : ℝ) 1 := by
  intro h
  have : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ stripSet 0 := by
    rw [h]; constructor <;> constructor <;> norm_num
  obtain ⟨j, _⟩ := mem_iUnion.mp this
  exact j.elim0

/-- The strip is the union of the standard rectangles (for `0 < m`; shape change: the skeleton's
statement is false for `m = 0`, see `stripSet_zero_ne`). -/
theorem stripSet_eq {m : ℕ} (hm : 0 < m) :
    stripSet m = Ioo (0 : ℝ) (2 * m + 1) ×ˢ Ioo (0 : ℝ) 1 := by
  refine (stripSet_subset m).antisymm ?_
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy⟩
  have hc1 : 0 < ⌈x / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hc2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x / 2 by positivity)
  have hc3 := Nat.le_ceil (x / 2)
  set j := min (⌈x / 2⌉₊ - 1) (m - 1) with hj
  have hjm : j < m := by omega
  have hjc : ((j : ℕ) : ℝ) + 1 ≤ ⌈x / 2⌉₊ := by exact_mod_cast (by omega : j + 1 ≤ ⌈x / 2⌉₊)
  refine mem_iUnion.mpr ⟨⟨j, hjm⟩, ⟨?_, ?_⟩, hy⟩
  · show 2 * (j : ℝ) < x
    linarith
  · show x < 2 * (j : ℝ) + 3
    rcases le_total (⌈x / 2⌉₊ - 1) (m - 1) with h | h
    · have : ((⌈x / 2⌉₊ : ℕ) : ℝ) ≤ j + 1 := by exact_mod_cast (by omega : ⌈x / 2⌉₊ ≤ j + 1)
      linarith
    · have : (m : ℝ) ≤ j + 1 := by exact_mod_cast (by omega : m ≤ j + 1)
      linarith

/-- **A threaded chain** in `E`: a map of the plane, continuous and injective on the open strip,
carrying each standard rectangle into the corresponding link. Weaker than `IsTameChain` (no
homeomorphism of `E`, no openness, links need not be images); it is exactly what
`exists_pseudoArc_in_tameChain` uses. -/
def IsThreadedChain {m : ℕ} (D : Chain E m) : Prop :=
  ∃ f : Pt → E, ContinuousOn f (stripSet m) ∧ InjOn f (stripSet m) ∧
    ∀ j : Fin m, f '' stdRect j ⊆ D.link j

theorem isThreadedChain_of_isTameChain {m : ℕ} {D : Chain E m} (hD : IsTameChain D) :
    IsThreadedChain D := by
  obtain ⟨e₁, e₂, hon, Φ, hΦ⟩ := hD
  refine ⟨fun p => Φ (Most.planeMap e₁ e₂ p),
    (Φ.continuous.comp (Most.continuous_planeMap e₁ e₂)).continuousOn,
    (Φ.injective.comp (Most.planeMap_injective hon)).injOn, ?_⟩
  rintro j _ ⟨p, hp, rfl⟩
  rw [hΦ j]
  exact ⟨_, Most.planeMap_stdRect hon j ⟨p, hp, rfl⟩, rfl⟩

omit [InnerProductSpace ℝ E] in
/-- **A pseudo-arc inside a threaded chain** (the proof of `exists_pseudoArc_in_tameChain`,
verbatim, with `f` in place of `Φ ∘ planeMap`: batch 84's planar pseudo-arc in the standard
rectangles, carried by `f`; Pacific Theorem 4 for the continuous injective image).
`IsMonotoneMap` needs only `ContinuousOn f M`, which follows from `M ⊆ stripSet m`. -/
theorem exists_pseudoArc_in_threadedChain {m : ℕ} (hm : 3 ≤ m) (D : Chain E m)
    (hD : IsThreadedChain D) :
    ∃ h : Set E, IsPseudoArc h ∧ h ⊆ D.union ∧ ∀ j, (h ∩ D.link j).Nonempty := by
  obtain ⟨f, hfc, hfi, himg⟩ := hD
  obtain ⟨M, hM, hMsub, hMmeet⟩ := exists_pseudoArc_stdRect hm
  have hMs : M ⊆ stripSet m := fun p hp => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hMsub hp)
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hfib : ∀ x ∈ M, M ∩ f ⁻¹' {f x} = {x} := by
    intro x hx
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => hfi (hMs h.1) (hMs hx) h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
  have hmono : IsMonotoneMap f M (f '' M) := by
    refine ⟨hfc.mono hMs, rfl, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hfib x hx]
    exact isConnected_singleton
  have hproper : ∀ y ∈ f '' M, M ∩ f ⁻¹' {y} ≠ M := by
    rintro _ ⟨x, hx, rfl⟩ e
    rw [hfib x hx] at e
    obtain ⟨a, ha, b, hb, hab⟩ := hM.2.2
    rw [← e] at ha hb
    exact hab (ha.trans hb.symm)
  refine ⟨f '' M, (theorem4_HIC hM hmono hproper).1, ?_, fun j => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hMsub hp)
    exact mem_iUnion.mpr ⟨j, himg j ⟨p, hj, rfl⟩⟩
  · obtain ⟨p, hpM, hpj⟩ := hMmeet j
    exact ⟨f p, ⟨p, hpM, rfl⟩, himg j ⟨p, hpj, rfl⟩⟩

/-- The geometric lemma with threaded chains in place of tame chains, as a hypothesis. -/
def GeomLemma' (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  ∀ g : Set E, Fold.Q78.IsContinuum g → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε g ∧ g ⊆ thickening ε D.union

theorem geomLemma'_of_geomLemma (h : GeomLemma E) : GeomLemma' E := by
  intro g hg ε hε
  obtain ⟨m, D, hm, hD, h1, h2, h3⟩ := h g hg ε hε
  exact ⟨m, D, hm, isThreadedChain_of_isTameChain hD, h1, h2, h3⟩

/-- Density from the threaded form (the proof of `dense_pseudoArcs_of`, verbatim). -/
theorem dense_pseudoArcs_of' (hgeo : GeomLemma' E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  rw [Metric.dense_iff]
  intro K r hr
  obtain ⟨m, D, hm, hD, hdiam, hDg, hgD⟩ :=
    hgeo _ ⟨K.1.isCompact, K.2⟩ (r / 3) (by positivity)
  obtain ⟨h, hpa, hhD, hmeet⟩ := exists_pseudoArc_in_threadedChain hm D hD
  have hbdd : Bornology.IsBounded D.union := K.1.isCompact.isBounded.thickening.subset hDg
  let H : Cont E := ⟨⟨⟨h, hpa.1.1.1⟩, hpa.1.1.2.nonempty⟩, hpa.1.1.2⟩
  refine ⟨H, ?_, hpa⟩
  rw [mem_ball]
  change hausdorffDist h (K.1 : Set E) < r
  have hle : hausdorffDist h (K.1 : Set E) ≤ 2 * (r / 3) := by
    refine hausdorffDist_le_of_mem_dist (by positivity) (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp (hDg (hhD hx))
      exact ⟨z, hz, by linarith⟩
    · obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hgD hy)
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      obtain ⟨w, hwh, hwj⟩ := hmeet j
      have hlb : Bornology.IsBounded (D.link j) := hbdd.subset (subset_iUnion _ j)
      have hzw : dist z w ≤ diam (D.link j) := dist_le_diam_of_mem hlb hj hwj
      refine ⟨w, hwh, ?_⟩
      calc dist y w ≤ dist y z + dist z w := dist_triangle _ _ _
        _ ≤ 2 * (r / 3) := by linarith [hdiam j]
  linarith

theorem theorem2_HIC_of' (hgeo : GeomLemma' E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  ⟨dense_pseudoArcs_of' hgeo, isGδ_pseudoArcs⟩

/-! ### Lattice paths -/

/-- A unit step of the integer lattice. -/
def IsUnitStep (p q : ℤ × ℤ) : Prop := |q.1 - p.1| + |q.2 - p.2| = 1

/-- **A self-avoiding lattice path** with `n` steps: `c 0, …, c n` pairwise distinct, consecutive
points a unit step apart. (Values of `c` beyond `n` are irrelevant.) -/
structure LatticePath (n : ℕ) where
  c : ℕ → ℤ × ℤ
  injOn : InjOn c (Iic n)
  step : ∀ i, i < n → IsUnitStep (c i) (c (i + 1))

/-- The lattice point `(a, b)` placed in `E` at mesh `δ`. -/
def latticePt (e₁ e₂ : E) (δ : ℝ) (p : ℤ × ℤ) : E := δ • ((p.1 : ℝ) • e₁ + (p.2 : ℝ) • e₂)

/-- The midpoint of step `i` of the path. -/
noncomputable def stepMid (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (i : ℕ) : E :=
  midpoint ℝ (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + 1)))

/-- **The stretch triangle** of index `k`: the convex hull of `c k` and the midpoints of steps
`k - 1` and `k` (only the one midpoint at `k = 0` and `k = n`). -/
def stretchTri (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (k : ℕ) : Set E :=
  convexHull ℝ ({latticePt e₁ e₂ δ (P.c k)} ∪
    (if 0 < k then {stepMid e₁ e₂ δ P (k - 1)} else ∅) ∪
    (if k < n then {stepMid e₁ e₂ δ P k} else ∅))

/-- The polygonal path: the union of the steps as segments of `E`. -/
def polyPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) : Set E :=
  ⋃ i ∈ Iio n, segment ℝ (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + 1)))

namespace Band

/-! #### Coordinates in the `(e₁, e₂)`-plane -/

/-- The `(e₁, e₂)`-plane as a linear map `ℝ² → E` (`Most.planeMap`). -/
noncomputable def planeL (e₁ e₂ : E) : (ℝ × ℝ) →ₗ[ℝ] E :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight e₁ + (LinearMap.snd ℝ ℝ ℝ).smulRight e₂

theorem planeL_apply (e₁ e₂ : E) (p : ℝ × ℝ) : planeL e₁ e₂ p = p.1 • e₁ + p.2 • e₂ := rfl

theorem inner_planeL {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (p q : ℝ × ℝ) :
    inner ℝ (planeL e₁ e₂ p) (planeL e₁ e₂ q) = p.1 * q.1 + p.2 * q.2 := by
  have h1 : ‖e₁‖ = 1 := by simpa using hon.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using hon.1 1
  have h12 : inner ℝ e₁ e₂ = 0 := by simpa using hon.2 (show (0 : Fin 2) ≠ 1 by decide)
  have h21 : inner ℝ e₂ e₁ = 0 := by rw [real_inner_comm]; exact h12
  have h11 : inner ℝ e₁ e₁ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : inner ℝ e₂ e₂ = 1 := by rw [real_inner_self_eq_norm_sq, h2]; norm_num
  simp only [planeL_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h11, h12, h21, h22]
  ring

theorem norm_planeL_sq {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (p : ℝ × ℝ) :
    ‖planeL e₁ e₂ p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_planeL hon]; ring

theorem planeL_injective {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) :
    Function.Injective (planeL e₁ e₂) :=
  Most.planeMap_injective hon

/-- Integer points as real points. -/
def toR (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

theorem latticePt_eq (e₁ e₂ : E) (δ : ℝ) (p : ℤ × ℤ) :
    latticePt e₁ e₂ δ p = δ • planeL e₁ e₂ (toR p) := rfl

theorem toR_sub (p q : ℤ × ℤ) : toR (p - q) = toR p - toR q := by
  simp [toR]

theorem norm_planeL_unit {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {a : ℤ × ℤ}
    (ha : |a.1| + |a.2| = 1) : ‖planeL e₁ e₂ (toR a)‖ = 1 := by
  have h := norm_planeL_sq hon (toR a)
  have : (toR a).1 ^ 2 + (toR a).2 ^ 2 = 1 := by
    simp only [toR]
    rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> norm_num
  rw [this] at h
  have h0 := norm_nonneg (planeL e₁ e₂ (toR a))
  nlinarith

/-- The step vector `c (i+1) - c i` is a unit vector (for `i < n`). -/
theorem step_unit {n : ℕ} (P : LatticePath n) {i : ℕ} (hi : i < n) :
    |(P.c (i + 1) - P.c i).1| + |(P.c (i + 1) - P.c i).2| = 1 := P.step i hi

theorem step_unit_neg {n : ℕ} (P : LatticePath n) {i : ℕ} (hi : i < n) :
    |(P.c i - P.c (i + 1)).1| + |(P.c i - P.c (i + 1)).2| = 1 := by
  have := P.step i hi
  simp only [IsUnitStep] at this
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [abs_sub_comm, abs_sub_comm (P.c i).2]; exact this

theorem c_ne {n : ℕ} (P : LatticePath n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (h : i ≠ j) :
    P.c i ≠ P.c j := fun e => h (P.injOn (mem_Iic.mpr hi) (mem_Iic.mpr hj) e)

/-- A stretch's offset vectors: the two midpoints relative to the lattice point. -/
theorem stepMid_sub_left (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (k : ℕ) :
    stepMid e₁ e₂ δ P k - latticePt e₁ e₂ δ (P.c k) =
      (δ / 2) • planeL e₁ e₂ (toR (P.c (k + 1) - P.c k)) := by
  rw [stepMid, midpoint_eq_smul_add, invOf_eq_inv, latticePt_eq, latticePt_eq, toR_sub, map_sub]
  module

theorem stepMid_sub_right (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) {k : ℕ} (hk : 0 < k) :
    stepMid e₁ e₂ δ P (k - 1) - latticePt e₁ e₂ δ (P.c k) =
      (δ / 2) • planeL e₁ e₂ (toR (P.c (k - 1) - P.c k)) := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [stepMid, hk', midpoint_eq_smul_add, invOf_eq_inv, latticePt_eq, latticePt_eq, toR_sub, map_sub]
  module

/-- The stretch triangle lies in a half-space `⟪· - c k, v⟫ ≤ (δ/2) α` as soon as both
step vectors at `c k` do (convexity). -/
theorem stretchTri_inner_le (e₁ e₂ : E) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) (k : ℕ)
    (v : E) {α : ℝ} (hα : 0 ≤ α)
    (h1 : 0 < k → inner ℝ (planeL e₁ e₂ (toR (P.c (k - 1) - P.c k))) v ≤ α)
    (h2 : k < n → inner ℝ (planeL e₁ e₂ (toR (P.c (k + 1) - P.c k))) v ≤ α) :
    ∀ p ∈ stretchTri e₁ e₂ δ P k,
      inner ℝ (p - latticePt e₁ e₂ δ (P.c k)) v ≤ δ / 2 * α := by
  set c := latticePt e₁ e₂ δ (P.c k)
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
      show inner ℝ (stepMid e₁ e₂ δ P (k - 1) - c) v ≤ δ / 2 * α
      rw [stepMid_sub_right e₁ e₂ δ P hk, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left (h1 hk) (by positivity)
    · exact absurd hx (notMem_empty _)
  · split_ifs at hx with hk
    · rw [mem_singleton_iff] at hx; subst hx
      show inner ℝ (stepMid e₁ e₂ δ P k - c) v ≤ δ / 2 * α
      rw [stepMid_sub_left, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left (h2 hk) (by positivity)
    · exact absurd hx (notMem_empty _)

/-- The step vector `c (k-1) - c k` into a stretch from behind is a unit vector. -/
theorem arm_left_unit {n : ℕ} (P : LatticePath n) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    |(P.c (k - 1) - P.c k).1| + |(P.c (k - 1) - P.c k).2| = 1 := by
  have h := step_unit_neg P (i := k - 1) (by omega)
  rwa [Nat.sub_add_cancel hk] at h

theorem inner_planeL_toR {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (a w : ℤ × ℤ) :
    inner ℝ (planeL e₁ e₂ (toR a)) (planeL e₁ e₂ (toR w)) = ((a.1 * w.1 + a.2 * w.2 : ℤ) : ℝ) := by
  rw [inner_planeL hon]; simp [toR]

theorem dot_le_one {a w : ℤ × ℤ} (ha : |a.1| + |a.2| = 1) (hw1 : w.1 = 1 ∨ w.1 = -1)
    (hw2 : w.2 = 1 ∨ w.2 = -1) : a.1 * w.1 + a.2 * w.2 ≤ 1 ∧ -1 ≤ a.1 * w.1 + a.2 * w.2 := by
  rcases unit_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases hw1 with h3 | h3 <;> rcases hw2 with h4 | h4 <;> rw [h1, h2, h3, h4] <;> norm_num

end Band

open Band

/-- Each stretch triangle lies in the closed ball of radius `δ/2` about its lattice point.
(Shape change: `k ≤ n` added; for `k > n` the values `c (k-1)`, `c k` are unconstrained and the
statement fails, e.g. `n = 0`, `c 1 = (10, 0)`, `k = 1`: see `stretchTri_subset_ball_false`.) -/
theorem stretchTri_subset_ball {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {k : ℕ} (hkn : k ≤ n) :
    stretchTri e₁ e₂ δ P k ⊆ closedBall (latticePt e₁ e₂ δ (P.c k)) (δ / 2) := by
  refine convexHull_min ?_ (convex_closedBall _ _)
  intro x hx
  rcases hx with (hx | hx) | hx
  · rw [mem_singleton_iff] at hx; subst hx; exact mem_closedBall_self (by positivity)
  · split_ifs at hx with hk
    · rw [mem_singleton_iff] at hx; subst hx
      rw [mem_closedBall, dist_eq_norm, stepMid_sub_right e₁ e₂ δ P hk, norm_smul,
        norm_planeL_unit hon (arm_left_unit P hk hkn), Real.norm_of_nonneg (by positivity)]
      linarith
    · exact absurd hx (notMem_empty _)
  · split_ifs at hx with hk
    · rw [mem_singleton_iff] at hx; subst hx
      rw [mem_closedBall, dist_eq_norm, stepMid_sub_left, norm_smul,
        norm_planeL_unit hon (step_unit P hk), Real.norm_of_nonneg (by positivity)]
      linarith
    · exact absurd hx (notMem_empty _)

/-- **Refutation of the skeleton's `stretchTri_subset_ball` for `k > n`**: with no steps and
`c i = (10 i, 0)`, the stretch triangle `1` contains the midpoint of `c 0` and `c 1`, at distance
`5 δ` from `c 1`. -/
theorem stretchTri_subset_ball_false {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) : ∃ P : LatticePath 0,
      ¬ stretchTri e₁ e₂ δ P 1 ⊆ closedBall (latticePt e₁ e₂ δ (P.c 1)) (δ / 2) := by
  refine ⟨⟨fun i => (10 * i, 0), fun a ha b hb _ => by
    rw [mem_Iic, Nat.le_zero] at ha hb; rw [ha, hb], fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
    fun h => ?_⟩
  set P : LatticePath 0 := ⟨fun i => (10 * i, 0), _, _⟩
  have hmem : stepMid e₁ e₂ δ P (1 - 1) ∈ stretchTri e₁ e₂ δ P 1 :=
    subset_convexHull ℝ _ (Or.inl (Or.inr (by rw [if_pos one_pos]; rfl)))
  have h1 := h hmem
  rw [mem_closedBall, dist_eq_norm, stepMid_sub_right e₁ e₂ δ P one_pos, norm_smul,
    Real.norm_of_nonneg (by positivity)] at h1
  have h2 : ‖planeL e₁ e₂ (toR (P.c (1 - 1) - P.c 1))‖ = 10 := by
    have := norm_planeL_sq hon (toR (P.c (1 - 1) - P.c 1))
    have e : (toR (P.c (1 - 1) - P.c 1)).1 ^ 2 + (toR (P.c (1 - 1) - P.c 1)).2 ^ 2 = 10 ^ 2 := by
      simp [P, toR]
    rw [e] at this
    nlinarith [norm_nonneg (planeL e₁ e₂ (toR (P.c (1 - 1) - P.c 1)))]
  rw [h2] at h1
  linarith

theorem latticePt_mem_polyPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) {k : ℕ}
    (hk : k < n) : latticePt e₁ e₂ δ (P.c k) ∈ polyPath e₁ e₂ δ P :=
  mem_biUnion (x := k) (mem_Iio.mpr hk) (left_mem_segment ℝ _ _)

theorem latticePt_mem_polyPath' (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) : latticePt e₁ e₂ δ (P.c k) ∈ polyPath e₁ e₂ δ P := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact mem_biUnion (x := j) (mem_Iio.mpr (by omega)) (right_mem_segment ℝ _ _)

/-- **Refutation of the skeleton's `stretchTri_subset_thickening` at `n = 0`**: the polygonal path
of a path with no steps is empty, the stretch triangle `0` is the point `c 0`. -/
theorem stretchTri_subset_thickening_false (e₁ e₂ : E) (δ : ℝ) (P : LatticePath 0) :
    ¬ stretchTri e₁ e₂ δ P 0 ⊆ cthickening (δ / 2) (polyPath e₁ e₂ δ P) := by
  intro h
  have hp : polyPath e₁ e₂ δ P = ∅ := by
    simp [polyPath]
  have hmem : latticePt e₁ e₂ δ (P.c 0) ∈ stretchTri e₁ e₂ δ P 0 :=
    subset_convexHull ℝ _ (Or.inl (Or.inl rfl))
  have := h hmem
  rw [hp, cthickening_empty] at this
  exact this

/-- Each stretch triangle lies within `δ/2` of the polygonal path. (Shape change: `0 < n` added;
false for `n = 0`, see `stretchTri_subset_thickening_false`.) -/
theorem stretchTri_subset_thickening {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (P : LatticePath n) {k : ℕ} (hk : k ≤ n) :
    stretchTri e₁ e₂ δ P k ⊆ cthickening (δ / 2) (polyPath e₁ e₂ δ P) := by
  intro p hp
  have hc : latticePt e₁ e₂ δ (P.c k) ∈ polyPath e₁ e₂ δ P := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact latticePt_mem_polyPath e₁ e₂ δ P hn
    · exact latticePt_mem_polyPath' e₁ e₂ δ P h hk
  exact mem_cthickening_of_dist_le p _ _ _ hc (stretchTri_subset_ball hon hδ P hk hp)

/-- **Separation of nonadjacent stretches.** For `k' ≥ k + 2` (both `≤ n`) the stretch triangles
are at distance at least `(√2/2) δ`. Two cases: the lattice points `c k`, `c k'` at `ℓ¹`-distance
`≥ 2` (then a diagonal direction `w = (±1, ±1)` separates: `⟪· - c k, w⟫ ≤ δ/2` on stretch `k`,
`⟪· - c k', w⟫ ≥ -δ/2` on stretch `k'`, `⟪c k' - c k, w⟫ ≥ 2δ`, `‖w‖ = √2`); or lattice-adjacent,
`c k' = c k + e` — then neither path-neighbour of `c k` is `c k'` (the path is self-avoiding and
`|k - k'| ≥ 2`), so stretch `k` lies in the half-plane `⟪· - c k, e⟫ ≤ 0`, and symmetrically
stretch `k'` in `⟪· - c k, e⟫ ≥ δ`: distance `≥ δ`. -/
theorem stretchTri_separated {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {k k' : ℕ} (hk' : k' ≤ n) (h : k + 2 ≤ k') :
    ∀ p ∈ stretchTri e₁ e₂ δ P k, ∀ q ∈ stretchTri e₁ e₂ δ P k',
      Real.sqrt 2 / 2 * δ ≤ dist p q := by
  intro p hp q hq
  set ck := latticePt e₁ e₂ δ (P.c k)
  set ck' := latticePt e₁ e₂ δ (P.c k')
  set d := P.c k' - P.c k with hd_def
  have hkk' : P.c k ≠ P.c k' := c_ne P (by omega) hk' (by omega)
  have hdiff : ck' - ck = δ • planeL e₁ e₂ (toR d) := by
    rw [hd_def, toR_sub, map_sub, smul_sub]; rfl
  have hsplit : ∀ v : E, inner ℝ (q - p) v =
      inner ℝ (q - ck') v + inner ℝ (ck' - ck) v - inner ℝ (p - ck) v := by
    intro v
    have : q - p = (q - ck') + (ck' - ck) - (p - ck) := by abel
    rw [this, inner_sub_left, inner_add_left]
  have hdist : dist p q = ‖q - p‖ := by rw [dist_comm, dist_eq_norm]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- the arms at `c k` and at `c k'`
  have armk1 : 0 < k → |(P.c (k - 1) - P.c k).1| + |(P.c (k - 1) - P.c k).2| = 1 :=
    fun hk => arm_left_unit P hk (by omega)
  have armk2 : |(P.c (k + 1) - P.c k).1| + |(P.c (k + 1) - P.c k).2| = 1 :=
    step_unit P (by omega)
  have armk'1 : |(P.c (k' - 1) - P.c k').1| + |(P.c (k' - 1) - P.c k').2| = 1 :=
    arm_left_unit P (by omega) hk'
  have armk'2 : k' < n → |(P.c (k' + 1) - P.c k').1| + |(P.c (k' + 1) - P.c k').2| = 1 :=
    fun h => step_unit P h
  by_cases hu : |d.1| + |d.2| = 1
  · -- lattice-adjacent
    set v := planeL e₁ e₂ (toR d)
    have hv : ‖v‖ = 1 := norm_planeL_unit hon hu
    have hnd : |(-d).1| + |(-d).2| = 1 := by simpa [abs_neg] using hu
    have hp' := stretchTri_inner_le e₁ e₂ hδ P k v le_rfl
      (fun hk => by
        rw [inner_planeL_toR hon]
        have := dot_nonpos_of_ne (armk1 hk) hu (fun e => c_ne P (by omega) hk' (by omega)
          (sub_left_inj.mp e))
        exact_mod_cast this)
      (fun _ => by
        rw [inner_planeL_toR hon]
        have := dot_nonpos_of_ne armk2 hu (fun e => c_ne P (by omega) hk' (by omega)
          (sub_left_inj.mp e))
        exact_mod_cast this) p hp
    have hq' := stretchTri_inner_le e₁ e₂ hδ P k' (-v) le_rfl
      (fun _ => by
        rw [inner_neg_right, inner_planeL_toR hon]
        have := dot_nonpos_of_ne armk'1 hnd (fun e => c_ne P (by omega) (by omega)
          (show k' - 1 ≠ k by omega) (by
            have : P.c (k' - 1) - P.c k' = P.c k - P.c k' := by rw [e, hd_def]; abel
            exact sub_left_inj.mp this))
        have h2 : ((P.c (k' - 1) - P.c k').1 * (-d).1 + (P.c (k' - 1) - P.c k').2 * (-d).2 : ℤ)
            = -((P.c (k' - 1) - P.c k').1 * d.1 + (P.c (k' - 1) - P.c k').2 * d.2) := by
          simp only [Prod.fst_neg, Prod.snd_neg]; ring
        rw [h2] at this
        have : (0 : ℝ) ≤ (((P.c (k' - 1) - P.c k').1 * d.1 +
            (P.c (k' - 1) - P.c k').2 * d.2 : ℤ) : ℝ) := by exact_mod_cast (by omega)
        linarith)
      (fun hkn => by
        rw [inner_neg_right, inner_planeL_toR hon]
        have := dot_nonpos_of_ne (armk'2 hkn) hnd (fun e => c_ne P (by omega) (by omega)
          (show k' + 1 ≠ k by omega) (by
            have : P.c (k' + 1) - P.c k' = P.c k - P.c k' := by rw [e, hd_def]; abel
            exact sub_left_inj.mp this))
        have h2 : ((P.c (k' + 1) - P.c k').1 * (-d).1 + (P.c (k' + 1) - P.c k').2 * (-d).2 : ℤ)
            = -((P.c (k' + 1) - P.c k').1 * d.1 + (P.c (k' + 1) - P.c k').2 * d.2) := by
          simp only [Prod.fst_neg, Prod.snd_neg]; ring
        rw [h2] at this
        have : (0 : ℝ) ≤ (((P.c (k' + 1) - P.c k').1 * d.1 +
            (P.c (k' + 1) - P.c k').2 * d.2 : ℤ) : ℝ) := by exact_mod_cast (by omega)
        linarith) q hq
    rw [inner_neg_right] at hq'
    have hc : inner ℝ (ck' - ck) v = δ := by
      rw [hdiff, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]; ring
    have h1 := hsplit v
    have h2 : inner ℝ (q - p) v ≤ ‖q - p‖ := by
      have := real_inner_le_norm (q - p) v
      rwa [hv, mul_one] at this
    rw [hdist]
    nlinarith
  · -- `ℓ¹`-distance at least `2`
    have hd0 : ¬ (d.1 = 0 ∧ d.2 = 0) := by
      rintro ⟨h1, h2⟩
      exact hkk' (by
        have : d = 0 := Prod.ext h1 h2
        exact (sub_eq_zero.mp this).symm)
    have hd2 : 2 ≤ |d.1| + |d.2| := by
      rcases abs_cases d.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases d.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    set w : ℤ × ℤ := (if 0 ≤ d.1 then 1 else -1, if 0 ≤ d.2 then 1 else -1) with hw
    have hw1 : w.1 = 1 ∨ w.1 = -1 := by simp only [hw]; split_ifs <;> simp
    have hw2 : w.2 = 1 ∨ w.2 = -1 := by simp only [hw]; split_ifs <;> simp
    have hdw : d.1 * w.1 + d.2 * w.2 = |d.1| + |d.2| := by
      simp only [hw]
      split_ifs with h1 h2 h2
      · rw [abs_of_nonneg h1, abs_of_nonneg h2]; ring
      · rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2)]; ring
      · rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2]; ring
      · rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2)]; ring
    set v := planeL e₁ e₂ (toR w)
    have hv2 : ‖v‖ ^ 2 = 2 := by
      rw [norm_planeL_sq hon]; simp only [toR]
      rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hv : ‖v‖ = Real.sqrt 2 := by
      rw [← hv2, Real.sqrt_sq (norm_nonneg _)]
    have hp' := stretchTri_inner_le e₁ e₂ hδ P k v zero_le_one
      (fun hk => by
        rw [inner_planeL_toR hon]; exact_mod_cast (dot_le_one (armk1 hk) hw1 hw2).1)
      (fun _ => by
        rw [inner_planeL_toR hon]; exact_mod_cast (dot_le_one armk2 hw1 hw2).1) p hp
    have hq' := stretchTri_inner_le e₁ e₂ hδ P k' (-v) zero_le_one
      (fun _ => by
        rw [inner_neg_right, inner_planeL_toR hon]
        have := (dot_le_one armk'1 hw1 hw2).2
        have : (-1 : ℝ) ≤ (((P.c (k' - 1) - P.c k').1 * w.1 +
            (P.c (k' - 1) - P.c k').2 * w.2 : ℤ) : ℝ) := by exact_mod_cast this
        linarith)
      (fun hkn => by
        rw [inner_neg_right, inner_planeL_toR hon]
        have := (dot_le_one (armk'2 hkn) hw1 hw2).2
        have : (-1 : ℝ) ≤ (((P.c (k' + 1) - P.c k').1 * w.1 +
            (P.c (k' + 1) - P.c k').2 * w.2 : ℤ) : ℝ) := by exact_mod_cast this
        linarith) q hq
    rw [inner_neg_right] at hq'
    have hc : 2 * δ ≤ inner ℝ (ck' - ck) v := by
      rw [hdiff, real_inner_smul_left, inner_planeL_toR hon, hdw]
      have : (2 : ℝ) ≤ ((|d.1| + |d.2| : ℤ) : ℝ) := by exact_mod_cast hd2
      nlinarith
    have h1 := hsplit v
    have h2 : inner ℝ (q - p) v ≤ ‖q - p‖ * Real.sqrt 2 := by
      have := real_inner_le_norm (q - p) v
      rwa [hv] at this
    rw [hdist]
    nlinarith [norm_nonneg (q - p)]

/-! ### The rounded (chamfered) path and its band -/

namespace Band

/-- Lattice coordinates of the midpoint of step `i`. -/
noncomputable def midC {n : ℕ} (P : LatticePath n) (i : ℕ) : ℝ × ℝ :=
  (1 / 2 : ℝ) • (toR (P.c i) + toR (P.c (i + 1)))

/-- The left normal `J u = (-u₂, u₁)` of the step vector `u = c (i+1) - c i`, an integer vector. -/
def nrmZ {n : ℕ} (P : LatticePath n) (i : ℕ) : ℤ × ℤ :=
  ((P.c i).2 - (P.c (i + 1)).2, (P.c (i + 1)).1 - (P.c i).1)

/-- The rounded path in lattice coordinates: piecewise-linear interpolation of the midpoints,
`pathC (j + 1/2) = midC j`. -/
noncomputable def pathC {n : ℕ} (P : LatticePath n) (τ : ℝ) : ℝ × ℝ :=
  ∑ j ∈ Finset.range n, hat (τ - 1 / 2 - j) • midC P j

/-- The normal field in lattice coordinates: piecewise-linear interpolation of the left normals. -/
noncomputable def normC {n : ℕ} (P : LatticePath n) (τ : ℝ) : ℝ × ℝ :=
  ∑ j ∈ Finset.range n, hat (τ - 1 / 2 - j) • toR (nrmZ P j)

theorem continuous_pathC {n : ℕ} (P : LatticePath n) : Continuous (pathC P) :=
  continuous_finset_sum _ fun _ _ =>
    (continuous_hat.comp ((continuous_id.sub continuous_const).sub continuous_const)).smul
      continuous_const

theorem continuous_normC {n : ℕ} (P : LatticePath n) : Continuous (normC P) :=
  continuous_finset_sum _ fun _ _ =>
    (continuous_hat.comp ((continuous_id.sub continuous_const).sub continuous_const)).smul
      continuous_const

theorem nrmZ_unit {n : ℕ} (P : LatticePath n) {i : ℕ} (hi : i < n) :
    |(nrmZ P i).1| + |(nrmZ P i).2| = 1 := by
  have h := P.step i hi
  simp only [IsUnitStep] at h
  simp only [nrmZ]
  rw [abs_sub_comm]; linarith

theorem pathC_stretch {n : ℕ} (P : LatticePath n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {s τ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : τ = k - 1 / 2 + s) :
    pathC P τ = (1 - s) • midC P (k - 1) + s • midC P k :=
  sum_hat_two n _ hk1 hkn hs0 hs1 hτ

theorem normC_stretch {n : ℕ} (P : LatticePath n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {s τ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : τ = k - 1 / 2 + s) :
    normC P τ = (1 - s) • toR (nrmZ P (k - 1)) + s • toR (nrmZ P k) :=
  sum_hat_two n _ hk1 hkn hs0 hs1 hτ

theorem sum_hat_half {V : Type*} [AddCommGroup V] [Module ℝ V] (n : ℕ) (X : ℕ → V) {j : ℕ}
    (hj : j < n) : ∑ i ∈ Finset.range n, hat ((j : ℝ) + 1 / 2 - 1 / 2 - i) • X i = X j := by
  rw [Finset.sum_eq_single j]
  · simp [hat]
  · intro i _ hij
    rw [hat_eq_zero, zero_smul]
    have : (j : ℝ) + 1 / 2 - 1 / 2 - i = ((j : ℤ) - i : ℤ) := by push_cast; ring
    rw [this]
    have h := one_le_abs_sub_of_ne (A := (j : ℤ)) (B := i) (by exact_mod_cast hij.symm)
    push_cast at h ⊢; exact h
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

theorem pathC_half {n : ℕ} (P : LatticePath n) {j : ℕ} (hj : j < n) :
    pathC P (j + 1 / 2) = midC P j := sum_hat_half n _ hj

theorem normC_half {n : ℕ} (P : LatticePath n) {j : ℕ} (hj : j < n) :
    normC P (j + 1 / 2) = toR (nrmZ P j) := sum_hat_half n _ hj

/-- On stretch `k`, the band in lattice coordinates is `c k + locF a b s t` with
`a = c (k-1) - c k`, `b = c (k+1) - c k`. -/
theorem bandC_stretch {n : ℕ} (P : LatticePath n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    pathC P (k - 1 / 2 + s) + t • normC P (k - 1 / 2 + s) =
      toR (P.c k) + locF (P.c (k - 1) - P.c k) (P.c (k + 1) - P.c k) s t := by
  rw [pathC_stretch P hk1 hkn hs0 hs1 rfl, normC_stretch P hk1 hkn hs0 hs1 rfl]
  have hk : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  simp only [midC, nrmZ, hk, toR, locF]
  ext <;> simp <;> ring

/-- Two endpoints of stretches (`m_j + t N_j`) coincide only for the same `j` and `t`. -/
theorem mid_inj {n : ℕ} (P : LatticePath n) {j j' : ℕ} (hj : j < n) (hj' : j' < n) {t t' : ℝ}
    (ht : |t| < 1 / 8) (ht' : |t'| < 1 / 8)
    (h : midC P j + t • toR (nrmZ P j) = midC P j' + t' • toR (nrmZ P j')) :
    j = j' ∧ t = t' := by
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [midC, nrmZ, toR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at e1 e2
  have hs := P.step j hj
  have hs' := P.step j' hj'
  simp only [IsUnitStep] at hs hs'
  have small : ∀ {u : ℤ} {r : ℝ}, |u| ≤ 1 → |r| < 1 / 8 → |2 * r * u| < 1 / 2 := by
    intro u r hu hr
    have hu' : |(u : ℝ)| ≤ 1 := by exact_mod_cast hu
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (u : ℝ), abs_nonneg r, mul_nonneg (abs_nonneg r) (sub_nonneg.mpr hu')]
  have b1 : |(P.c j).2 - (P.c (j + 1)).2| ≤ 1 := by
    rw [abs_sub_comm]; linarith [abs_nonneg ((P.c (j + 1)).1 - (P.c j).1)]
  have b2 : |(P.c (j + 1)).1 - (P.c j).1| ≤ 1 := by
    linarith [abs_nonneg ((P.c (j + 1)).2 - (P.c j).2)]
  have b1' : |(P.c j').2 - (P.c (j' + 1)).2| ≤ 1 := by
    rw [abs_sub_comm]; linarith [abs_nonneg ((P.c (j' + 1)).1 - (P.c j').1)]
  have b2' : |(P.c (j' + 1)).1 - (P.c j').1| ≤ 1 := by
    linarith [abs_nonneg ((P.c (j' + 1)).2 - (P.c j').2)]
  have hA1 : (P.c j).1 + (P.c (j + 1)).1 = (P.c j').1 + (P.c (j' + 1)).1 := by
    refine int_eq_of_close (x := 2 * t * ((P.c j).2 - (P.c (j + 1)).2 : ℤ))
      (y := 2 * t' * ((P.c j').2 - (P.c (j' + 1)).2 : ℤ)) ?_ (small b1 ht) (small b1' ht')
    push_cast at e1 ⊢; linarith
  have hA2 : (P.c j).2 + (P.c (j + 1)).2 = (P.c j').2 + (P.c (j' + 1)).2 := by
    refine int_eq_of_close (x := 2 * t * ((P.c (j + 1)).1 - (P.c j).1 : ℤ))
      (y := 2 * t' * ((P.c (j' + 1)).1 - (P.c j').1 : ℤ)) ?_ (small b2 ht) (small b2' ht')
    push_cast at e2 ⊢; linarith
  have hjj : j = j' := by
    rcases edge_of_sum hs hs' hA1 hA2 with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact P.injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h1
    · have := P.injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h1
      have := P.injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) h2
      omega
  subst hjj
  refine ⟨rfl, ?_⟩
  have hne : toR (nrmZ P j) ≠ 0 := by
    intro h0
    have u := nrmZ_unit P hj
    have h1 : ((nrmZ P j).1 : ℝ) = 0 := congrArg Prod.fst h0
    have h2 : ((nrmZ P j).2 : ℝ) = 0 := congrArg Prod.snd h0
    have h1' : (nrmZ P j).1 = 0 := by exact_mod_cast h1
    have h2' : (nrmZ P j).2 = 0 := by exact_mod_cast h2
    rw [h1', h2'] at u; norm_num at u
  exact smul_left_injective ℝ hne (add_left_cancel h)

/-- A lattice point and a point of an open square of side `1` around another lattice point
cannot be matched with a point of the closed square unless the lattice points agree. -/
theorem not_both_interior {A A' : ℤ × ℤ} (hne : A ≠ A') {F F' : ℝ × ℝ}
    (heq : toR A + F = toR A' + F') (hF : |F.1| < 1 / 2 ∧ |F.2| < 1 / 2)
    (hF' : |F'.1| ≤ 1 / 2 ∧ |F'.2| ≤ 1 / 2) : False := by
  have e1 : (A.1 : ℝ) + F.1 = A'.1 + F'.1 := congrArg Prod.fst heq
  have e2 : (A.2 : ℝ) + F.2 = A'.2 + F'.2 := congrArg Prod.snd heq
  have : A.1 ≠ A'.1 ∨ A.2 ≠ A'.2 := by
    by_contra h; push_neg at h; exact hne (Prod.ext h.1 h.2)
  obtain ⟨a1, a2⟩ := abs_lt.mp hF.1
  obtain ⟨a3, a4⟩ := abs_lt.mp hF.2
  obtain ⟨b1, b2⟩ := abs_le.mp hF'.1
  obtain ⟨b3, b4⟩ := abs_le.mp hF'.2
  rcases this with h | h
  · have h1 := one_le_abs_sub_of_ne h
    have : |(A.1 : ℝ) - A'.1| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · have h1 := one_le_abs_sub_of_ne h
    have : |(A.2 : ℝ) - A'.2| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith

end Band

open Band

/-- **The rounded path** `Γ : ℝ → E` (here: chamfered), parametrised by `τ ∈ [1/2, n - 1/2]`:
the piecewise-linear interpolation with `Γ (i + 1/2) = m_i`, the midpoint of step `i`. On stretch
`k` (`τ ∈ [k - 1/2, k + 1/2]`, `1 ≤ k ≤ n - 1`) it is the straight segment from `m_{k-1}` to `m_k`:
the two half-steps through `c k` on a straight stretch, the chord between the two midpoints at a
corner. (Shape change: chamfered corners instead of quarter circles; the end half-steps are not
used, `τ` runs over `[1/2, n - 1/2]`.) -/
noncomputable def roundedPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) : ℝ → E :=
  fun τ => δ • planeL e₁ e₂ (pathC P τ)

/-- **The normal field** `ν : ℝ → E`: the piecewise-linear interpolation with `ν (i + 1/2) = N_i`,
the left unit normal `(a, b) ↦ (-b, a)` of step `i`. Constant on a straight stretch; on a corner
it interpolates linearly between the two left normals, so `√2/2 ≤ ‖ν‖ ≤ 1` there. Continuous
everywhere. -/
noncomputable def roundedNormal (e₁ e₂ : E) (_δ : ℝ) {n : ℕ} (P : LatticePath n) : ℝ → E :=
  fun τ => planeL e₁ e₂ (normC P τ)

theorem continuous_roundedPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) :
    Continuous (roundedPath e₁ e₂ δ P) :=
  continuous_const.smul ((planeL e₁ e₂).continuous_of_finiteDimensional.comp (continuous_pathC P))

theorem continuous_roundedNormal (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) :
    Continuous (roundedNormal e₁ e₂ δ P) :=
  (planeL e₁ e₂).continuous_of_finiteDimensional.comp (continuous_normC P)

theorem roundedPath_continuousOn {e₁ e₂ : E} {δ : ℝ} {n : ℕ} (P : LatticePath n) :
    ContinuousOn (roundedPath e₁ e₂ δ P) (Icc 0 n) :=
  (continuous_roundedPath e₁ e₂ δ P).continuousOn

theorem roundedNormal_continuousOn {e₁ e₂ : E} {δ : ℝ} {n : ℕ} (P : LatticePath n) :
    ContinuousOn (roundedNormal e₁ e₂ δ P) (Icc 0 n) :=
  (continuous_roundedNormal e₁ e₂ δ P).continuousOn

theorem stepMid_eq (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (i : ℕ) :
    stepMid e₁ e₂ δ P i = δ • planeL e₁ e₂ (midC P i) := by
  rw [stepMid, midpoint_eq_smul_add, invOf_eq_inv, latticePt_eq, latticePt_eq, midC, map_smul,
    map_add]
  module

/-- The rounded path at the node `j + 1/2` is the midpoint of step `j`. -/
theorem roundedPath_half (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) {j : ℕ} (hj : j < n) :
    roundedPath e₁ e₂ δ P (j + 1 / 2) = stepMid e₁ e₂ δ P j := by
  rw [stepMid_eq, roundedPath, pathC_half P hj]

/-- **`‖ν‖ ≤ 1`** on `[1/2, n - 1/2]` (shape change: not `= 1`; the normal is a convex
combination of two unit normals). -/
theorem norm_roundedNormal {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (P : LatticePath n) {τ : ℝ} (hτ : τ ∈ Icc (1 / 2 : ℝ) (n - 1 / 2)) :
    ‖roundedNormal e₁ e₂ δ P τ‖ ≤ 1 := by
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  rw [roundedNormal, normC_stretch P hk1 hkn hs0 hs1 rfl, map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_planeL_unit hon (nrmZ_unit P (by omega)),
    norm_planeL_unit hon (nrmZ_unit P hkn), Real.norm_of_nonneg (by linarith),
    Real.norm_of_nonneg hs0]
  linarith

/-- Stretch `k` of the rounded path lies in the stretch triangle `k`. (Shape change: stated for
the full stretches `1 ≤ k ≤ n - 1`, which cover the parameter range `[1/2, n - 1/2]`.) -/
theorem roundedPath_mem_stretchTri (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k < n) {τ : ℝ} (hτ : τ ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    roundedPath e₁ e₂ δ P τ ∈ stretchTri e₁ e₂ δ P k := by
  have hs0 : 0 ≤ τ - k + 1 / 2 := by linarith [hτ.1]
  have hs1 : τ - k + 1 / 2 ≤ 1 := by linarith [hτ.2]
  have h : roundedPath e₁ e₂ δ P τ =
      (1 - (τ - k + 1 / 2)) • stepMid e₁ e₂ δ P (k - 1) + (τ - k + 1 / 2) • stepMid e₁ e₂ δ P k := by
    rw [roundedPath, pathC_stretch P hk1 hkn hs0 hs1 (by ring), stepMid_eq, stepMid_eq, map_add,
      map_smul, map_smul]
    module
  rw [h]
  refine segment_subset_convexHull ?_ ?_ ⟨1 - (τ - k + 1 / 2), τ - k + 1 / 2, by linarith, hs0,
    by ring, rfl⟩
  · exact Or.inl (Or.inr (by rw [if_pos (by omega)]; rfl))
  · exact Or.inr (by rw [if_pos hkn]; rfl)

/-- **The band**: `(τ, t) ↦ Γ τ + (t δ) • ν τ`. -/
noncomputable def band (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (q : ℝ × ℝ) : E :=
  roundedPath e₁ e₂ δ P q.1 + (q.2 * δ) • roundedNormal e₁ e₂ δ P q.1

theorem band_eq (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (q : ℝ × ℝ) :
    band e₁ e₂ δ P q = δ • planeL e₁ e₂ (pathC P q.1 + q.2 • normC P q.1) := by
  rw [band, roundedPath, roundedNormal, map_add, map_smul]
  module

theorem continuous_band (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) :
    Continuous (band e₁ e₂ δ P) :=
  ((continuous_roundedPath e₁ e₂ δ P).comp continuous_fst).add
    ((continuous_snd.mul continuous_const).smul
      ((continuous_roundedNormal e₁ e₂ δ P).comp continuous_fst))

theorem band_continuousOn {e₁ e₂ : E} {δ : ℝ} {n : ℕ} (P : LatticePath n) :
    ContinuousOn (band e₁ e₂ δ P) (Icc (0 : ℝ) n ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) :=
  (continuous_band e₁ e₂ δ P).continuousOn

/-- **Injectivity of the band, in lattice coordinates.** -/
theorem bandC_injOn {n : ℕ} (hn : 2 ≤ n) (P : LatticePath n) :
    InjOn (fun q : ℝ × ℝ => pathC P q.1 + q.2 • normC P q.1)
      (Icc (1 / 2 : ℝ) (n - 1 / 2) ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  rintro ⟨τ, t⟩ ⟨hτ, ht⟩ ⟨τ', t'⟩ ⟨hτ', ht'⟩ heq0
  simp only at heq0 hτ hτ' ht ht'
  have ht0 : |t| < 1 / 8 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht0' : |t'| < 1 / 8 := abs_lt.mpr ⟨by linarith [ht'.1], ht'.2⟩
  obtain ⟨k, hk1, hkn, s, hs0, hs1, rfl⟩ := exists_stretch hn hτ.1 hτ.2
  obtain ⟨k', hk1', hkn', s', hs0', hs1', rfl⟩ := exists_stretch hn hτ'.1 hτ'.2
  have heq := heq0
  rw [bandC_stretch P hk1 hkn hs0 hs1, bandC_stretch P hk1' hkn' hs0' hs1'] at heq
  -- the two arms at each stretch
  have ha := arm_left_unit P (by omega : 0 < k) hkn.le
  have hb := step_unit P hkn
  have hab : P.c (k - 1) - P.c k ≠ P.c (k + 1) - P.c k := fun e =>
    c_ne P (by omega) (by omega) (show k - 1 ≠ k + 1 by omega) (sub_left_inj.mp e)
  have ha' := arm_left_unit P (by omega : 0 < k') hkn'.le
  have hb' := step_unit P hkn'
  have hab' : P.c (k' - 1) - P.c k' ≠ P.c (k' + 1) - P.c k' := fun e =>
    c_ne P (by omega) (by omega) (show k' - 1 ≠ k' + 1 by omega) (sub_left_inj.mp e)
  by_cases hcc : P.c k = P.c k'
  · have hkk : k = k' := P.injOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) hcc
    subst hkk
    obtain ⟨rfl, rfl⟩ := locF_inj ha hb hab ht0 ht0' (add_left_cancel heq)
    rfl
  · -- both parameters are stretch ends
    have hend : s = 0 ∨ s = 1 := by
      by_contra hc
      push_neg at hc
      exact not_both_interior hcc heq
        (locF_strict ha hb hab (lt_of_le_of_ne hs0 (Ne.symm hc.1)) (lt_of_le_of_ne hs1 hc.2) ht0)
        (locF_bound ha' hb' hab' hs0' hs1' ht0')
    have hend' : s' = 0 ∨ s' = 1 := by
      by_contra hc
      push_neg at hc
      exact not_both_interior (Ne.symm hcc) heq.symm
        (locF_strict ha' hb' hab' (lt_of_le_of_ne hs0' (Ne.symm hc.1)) (lt_of_le_of_ne hs1' hc.2)
          ht0')
        (locF_bound ha hb hab hs0 hs1 ht0)
    have hj : ∃ j : ℕ, j < n ∧ (k : ℝ) - 1 / 2 + s = j + 1 / 2 := by
      rcases hend with rfl | rfl
      · exact ⟨k - 1, by omega, by rw [Nat.cast_sub hk1]; push_cast; ring⟩
      · exact ⟨k, hkn, by ring⟩
    have hj' : ∃ j : ℕ, j < n ∧ (k' : ℝ) - 1 / 2 + s' = j + 1 / 2 := by
      rcases hend' with rfl | rfl
      · exact ⟨k' - 1, by omega, by rw [Nat.cast_sub hk1']; push_cast; ring⟩
      · exact ⟨k', hkn', by ring⟩
    obtain ⟨j, hjn, hj⟩ := hj
    obtain ⟨j', hjn', hj'⟩ := hj'
    rw [hj, hj', pathC_half P hjn, normC_half P hjn, pathC_half P hjn', normC_half P hjn'] at heq0
    obtain ⟨rfl, rfl⟩ := mid_inj P hjn hjn' ht0 ht0' heq0
    rw [hj, hj']

/-- **Injectivity of the band** on `[1/2, n - 1/2] × (-1/8, 1/8)` (shape change: the parameter
range, and `2 ≤ n`). Over stretch `k` the band lies in the closed square of side `δ` centred at
`c k`, meeting its boundary only at the two ends of the stretch (`locF_bound`, `locF_strict`);
within one stretch the band is injective (`locF_inj`); two points over different stretches lie in
two different squares, so both are stretch ends `m_i + (t δ) • N_i`, and these determine `i` and
`t` (`mid_inj`). -/
theorem band_injOn {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : 2 ≤ n) (P : LatticePath n) :
    InjOn (band e₁ e₂ δ P) (Icc (1 / 2 : ℝ) (n - 1 / 2) ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  intro q hq q' hq' h
  rw [band_eq, band_eq] at h
  exact bandC_injOn hn P hq hq'
    (planeL_injective hon (smul_right_injective E hδ.ne' h))

end HPC.Plane
