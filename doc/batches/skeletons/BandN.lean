import HPC.Plane.LatticeCycle

/-!
# Batch 112: the band in dimension `≥ 3`, and the reduction of Hilbert space to finite dimension

Skeleton (save as `HPC/Plane/BandN.lean`; add `import HPC.Plane.BandN` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. No existing file is to be edited, except the audit.

Towards the open `geomLemma'_of_two_le_rank` (OPEN.md item 4). Two independent halves:

**(A) Lattice paths in `ℤ^d` and the band with a fixed transverse direction (`3 ≤ d`).** The
plane needed a normal field turning at the corners (`Band.lean`); in dimension `d ≥ 3` the band
`(τ, t) ↦ Γ τ + (t δ) • w` with the *constant* unit vector `w = (e 0 + ⋯ + e (d-1)) / √d` is
already injective, because every coordinate of `w` is nonzero: for `τ, τ'` in the same or in
adjacent stretches the difference `Γ τ - Γ τ'` lies in the span of at most two vectors of the form
`(u + u')/2` (`u, u'` consecutive unit steps, `u' ≠ -u`), and no nonzero multiple of `w` does
(three distinct axes: `(α ε₁, (α + β) ε₂, β ε₃) = (1, 1, 1)` forces `ε₁ + ε₃ = ε₂ = ±1`,
impossible; fewer axes: a coordinate of `w` would vanish; `d ≥ 4`: a fourth coordinate would
vanish); for nonadjacent stretches the separation lemma (`(√2/2) δ`, same proof as in the plane)
beats `‖(t - t') δ w‖ < δ/4`. So no normal field at all. The chain is then as in
`BandChain.lean`.

**(B) Hilbert space.** `GeomLemma' E` follows from `GeomLemma' F` for the finite-dimensional
subspaces `F` of `E` of dimension `≥ 2`: a compact `g` has a finite `ε/4`-net; `F` is the span of
the net, enlarged to dimension `≥ 2`; the orthogonal projection `P_F` moves each point of `g` by
less than `ε/4` (the nearest point of `F` is at least as close as the net point); `P_F '' g` is a
continuum of `F`; the chain `D'` of `F` for `P_F '' g` and `ε/2` is pulled back to `E` as
`link j := P_F ⁻¹' (D'.link j) ∩ thickening η F`, which is open, has the same intersection
pattern, is threaded by the same map followed by the inclusion `F → E`, and has diameter
`< diam (D'.link j) + 2η`.

Batch 113 (planned): the self-avoiding lattice cycle through the cubes meeting `g` in `ℤ^d`
(the splice of `LatticeCycleAux.lean` with a `d`-cube loop built by induction on `d`: two copies
of the `(d-1)`-loop on the bottom and top layers joined by two columns), the cubes of a
`d`-dimensional `E`, and the assembly of `geomLemma'_of_two_le_rank` from (A), (B), the plane case
and the cycle.
-/

namespace HPC.Plane

open Set Metric

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

theorem stretchTriN_subset_ball {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk : k ≤ n) :
    stretchTriN e δ P k ⊆ closedBall (latticePtN e δ (P.c k)) (δ / 2) := by
  sorry

theorem stretchTriN_subset_thickening {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (P : LatticePathN d n) {k : ℕ} (hk : k ≤ n) :
    stretchTriN e δ P k ⊆ cthickening (δ / 2) (polyPathN e δ P) := by
  sorry

/-- **Separation of nonadjacent stretches** in `ℤ^d` (the proof of `stretchTri_separated`: a
single separating direction, `w = Σ sign • e i` in the `ℓ¹` case, `w = c k' - c k` in the
lattice-adjacent case). -/
theorem stretchTriN_separated {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k k' : ℕ} (hk' : k' ≤ n) (h : k + 2 ≤ k') :
    ∀ p ∈ stretchTriN e δ P k, ∀ q ∈ stretchTriN e δ P k',
      Real.sqrt 2 / 2 * δ ≤ dist p q := by
  sorry

/-- **The piecewise-linear path through the midpoints** (the `roundedPath` of `Band.lean`, same
hat-function formula): `Γ (i + 1/2) = m_i`, linear in between; defined and continuous on `ℝ`;
stretch `k` (`1 ≤ k < n`) on `[k - 1/2, k + 1/2]`. -/
noncomputable def plPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    ℝ → E := sorry

theorem continuous_plPathN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    Continuous (plPathN e δ P) := by
  sorry

theorem plPathN_mem_stretchTriN {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePathN d n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {τ : ℝ}
    (hτ : τ ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    plPathN e δ P τ ∈ stretchTriN e δ P k := by
  sorry

/-- `Γ` is injective on `[1/2, n - 1/2]` (each stretch is a segment; adjacent stretches meet only
at the common midpoint, lying in opposite half-spaces of `⟪· - m_k, u_k⟫`; nonadjacent ones are
separated). -/
theorem plPathN_injOn {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) :
    InjOn (plPathN e δ P) (Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2)) := by
  sorry

/-- The transverse direction `w = (Σ e i) / √d`. -/
noncomputable def diagDir {d : ℕ} (e : Fin d → E) : E := (Real.sqrt d)⁻¹ • ∑ i, e i

theorem norm_diagDir {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) (hd : 0 < d) :
    ‖diagDir e‖ = 1 := by
  sorry

/-- **No nonzero multiple of `w` lies in the span of two consecutive chords.** For unit steps
`u, u', u''` of `ℤ^d` with `u' ≠ -u`, `u'' ≠ -u'` and `3 ≤ d`: if
`α • (u + u') + β • (u' + u'') = λ • Σ e i` then `λ = 0`. (The header's case analysis.) -/
theorem diagDir_not_mem_span {d : ℕ} (hd : 3 ≤ d) {u u' u'' : Fin d → ℤ}
    (hu : ∑ i, |u i| = 1) (hu' : ∑ i, |u' i| = 1) (hu'' : ∑ i, |u'' i| = 1)
    (h1 : u' ≠ -u) (h2 : u'' ≠ -u') {α β lam : ℝ}
    (h : ∀ i, α * (u i + u' i) + β * (u' i + u'' i) = lam) : lam = 0 := by
  sorry

/-- **The band with constant transverse direction**: `(τ, t) ↦ Γ τ + (t δ) • w`. -/
noncomputable def bandN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n)
    (q : ℝ × ℝ) : E :=
  plPathN e δ P q.1 + (q.2 * δ) • diagDir e

theorem continuous_bandN {d : ℕ} (e : Fin d → E) (δ : ℝ) {n : ℕ} (P : LatticePathN d n) :
    Continuous (bandN e δ P) := by
  sorry

/-- **Injectivity of the band** on `[1/2, n - 1/2] × (-1/8, 1/8)` for `3 ≤ d`: if
`Γ τ - Γ τ' = (t' - t) δ • w` then either `t = t'` and `τ = τ'` by `plPathN_injOn`, or the
stretches of `τ, τ'` are nonadjacent (contradiction with `stretchTriN_separated`, since
`‖(t' - t) δ • w‖ < δ/4 < (√2/2) δ`), or they are equal or adjacent, and then the difference is
in the span of at most two chords, contradicting `diagDir_not_mem_span`. -/
theorem bandN_injOn {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n) (P : LatticePathN d n) :
    InjOn (bandN e δ P) (Icc (1 / 2 : ℝ) ((n : ℝ) - 1 / 2) ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  sorry

/-- **The band theorem in dimension `≥ 3`** (the statement of
`exists_threadedChain_of_latticePath`, with `bandN` in place of `band`; the chain of
`BandChain.lean` with `λ = (n - 1)/(2m + 1)`, `m = (n - 4)/6`). -/
theorem exists_threadedChain_of_latticePathN {d : ℕ} (hd : 3 ≤ d) {e : Fin d → E}
    (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 22 ≤ n) (P : LatticePathN d n) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧
      (∀ j, diam (D.link j) ≤ 16 * δ) ∧
      D.union ⊆ thickening δ (polyPathN e δ P) ∧
      ∀ i, i ≤ n → ∃ x ∈ D.union, dist x (latticePtN e δ (P.c i)) ≤ δ := by
  sorry

/-! ### (B) Reduction of `E` to its finite-dimensional subspaces -/

/-- A compact set is within `η` of a finite-dimensional subspace of dimension `≥ 2`
(span of a finite `η`-net, enlarged if necessary; needs `2 ≤ Module.rank ℝ E`). -/
theorem exists_finiteDimensional_subspace_near (hdim : 2 ≤ Module.rank ℝ E) {g : Set E}
    (hg : IsCompact g) {η : ℝ} (hη : 0 < η) :
    ∃ F : Submodule ℝ E, FiniteDimensional ℝ F ∧ 2 ≤ Module.finrank ℝ F ∧
      ∀ x ∈ g, ∃ y ∈ F, dist x y < η := by
  sorry

/-- **Pulling a threaded chain of a closed subspace back to `E`**: `link j := P_F ⁻¹' (D'.link j)
∩ thickening η F` is a chain of `E` with the same adjacency, threaded by the same map followed by
the inclusion, with `diam ≤ diam (D'.link j) + 2η`, `D.union ⊆ thickening η (D'.union)` and
`D'.union ⊆ D.union`. -/
theorem exists_threadedChain_pullback [CompleteSpace E] (F : Submodule ℝ E)
    [FiniteDimensional ℝ F] {m : ℕ} (D' : Chain F m) (hD' : IsThreadedChain D') {η : ℝ}
    (hη : 0 < η) :
    ∃ D : Chain E m, IsThreadedChain D ∧
      (∀ j, Bornology.IsBounded (D'.link j) → diam (D.link j) ≤ diam (D'.link j) + 2 * η) ∧
      D.union ⊆ thickening η ((↑) '' D'.union : Set E) ∧
      ((↑) '' D'.union : Set E) ⊆ D.union := by
  sorry

/-- **The reduction.** If `GeomLemma'` holds in every finite-dimensional subspace of `E` of
dimension `≥ 2`, it holds in `E`. -/
theorem geomLemma'_of_subspaces [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E)
    (hF : ∀ F : Submodule ℝ E, FiniteDimensional ℝ F → 2 ≤ Module.finrank ℝ F → GeomLemma' F) :
    GeomLemma' E := by
  sorry

end HPC.Plane
