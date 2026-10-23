import HPC.Plane.BandN

/-!
# Batch 113: the lattice cycle through the cubes of `ℤ^d` meeting a continuum; the density lemma
# in every dimension; Bing's Theorem 2 (Pacific) and Theorem 2 (Duke) as he states them

Skeleton (save as `HPC/Plane/CubeCycle.lean`; add `import HPC.Plane.CubeCycle` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with
the change recorded. No existing file is to be edited, except the audit and — in the last item —
`HPC/Plane/LatticeCycle.lean`, where the open `geomLemma'_of_two_le_rank` receives its proof.

Plan. The plane construction (`LatticeCycleAux.lean`) is: a 24-point loop in the square, with a
*designated pair* (`pA`, `pB`) on each of the four sides, and a splice that attaches a new square
across a free side by replacing the designated edge of that side with a detour through the new
square's loop. The facts about the loop and the detour were checked by `decide`. In `ℤ^d` the
same induction runs with the loop replaced by an abstract **cube loop** (`CubeLoop d`): a
self-avoiding closed lattice path through depth-1 points of the cube `(0,8)^d`, with a designated
edge on each of the `2d` faces, the designated points pairwise distinct across faces, and the two
designated edges of opposite faces translates of each other by `6 e_i` (so that the detour
`x, x + e, x + 2e, …, y + 2e, y + e, y` enters the new cube at *its* designated edge for the
opposite face). Cube loops exist for every `d ≥ 2` by induction: the plane loop for `d = 2`; from
a loop `l` of the `(d-1)`-cube, open a non-designated edge `p q`, and form

    bottom copy of `l` from `q` to `p` at height 1, the column `p` from height 2 to 6,
    the top copy of `l` from `p` back to `q` at height 7, the column `q` from 6 down to 2,

of length `2 |l| + 10`; the designated edges of the old faces are inherited at height 1, those of
the two new faces are an edge `p' q'` of `l` with undesignated endpoints, at heights 1 and 7.
Then the invariant and the splice of `LatticeCycleAux.lean`, with the loop's properties in place
of `decide`, give a self-avoiding cycle through the cubes of any connected finite set; the cubes
of a `d`-dimensional `E` meeting a continuum form such a set; and with `bandN` the density lemma
follows for `finrank = d ≥ 3`. Finally `geomLemma'_of_subspaces` reduces every `E` of
`rank ≥ 2` to its finite-dimensional subspaces, where `finrank = 2` is the plane case and
`finrank ≥ 3` is this one. That closes OPEN.md item 4.
-/

namespace HPC.Plane

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Cubes of `ℤ^d` -/

/-- The unit vector `e i` of `ℤ^d`. -/
def eZ {d : ℕ} (i : Fin d) : Fin d → ℤ := Pi.single i 1

/-- The fine lattice point `p` lies in the closed cube `s` (fine coordinates, mesh `1/8`). -/
def InCube {d : ℕ} (s p : Fin d → ℤ) : Prop := ∀ i, 8 * s i ≤ p i ∧ p i ≤ 8 * s i + 8

/-- `p` is a depth-1 point of the cube `s` (strictly inside). -/
def InCubeInt {d : ℕ} (s p : Fin d → ℤ) : Prop := ∀ i, 8 * s i < p i ∧ p i < 8 * s i + 8

/-- Edge-connectedness of a finite set of cubes. -/
def CubeConnected {d : ℕ} (T : Finset (Fin d → ℤ)) : Prop :=
  ∀ A : Finset (Fin d → ℤ), A ⊆ T → A.Nonempty →
    (∀ s ∈ A, ∀ s' ∈ T, IsUnitStepN s s' → s' ∈ A) → A = T

/-- A face of the cube: an axis `i` and a side (`true` = the side `x i = 8`). The outward
direction is `± e i`. -/
def faceDir {d : ℕ} (i : Fin d) (b : Bool) : Fin d → ℤ := if b then eZ i else -eZ i

/-- **A cube loop** in dimension `d`: a self-avoiding closed lattice path `c 0, …, c (L-1)`
through depth-1 points of the cube `0`, with on each face `(i, b)` a designated edge `A i b → B i b`
(an edge of the cycle in one direction or the other) whose points have coordinate `i` equal to `7`
(`b = true`) or `1` (`b = false`); designated points of distinct faces are distinct; the designated
edges of opposite faces are translates by `6 e i`. -/
structure CubeLoop (d : ℕ) where
  L : ℕ
  two_le : 2 ≤ L
  /-- Enough edges to find, in the doubling step, a non-designated edge and an edge with
  undesignated endpoints: at most `4d` designated points touch at most `8d` edges. -/
  big : 8 * d + 2 ≤ L
  c : ℕ → (Fin d → ℤ)
  injOn : InjOn c (Iio L)
  step : ∀ k < L, IsUnitStepN (c k) (c ((k + 1) % L))
  mem : ∀ k < L, InCubeInt 0 (c k)
  A : Fin d → Bool → (Fin d → ℤ)
  B : Fin d → Bool → (Fin d → ℤ)
  A_mem : ∀ i b, ∃ k < L, c k = A i b
  B_mem : ∀ i b, ∃ k < L, c k = B i b
  edge : ∀ i b, (∃ k < L, c k = A i b ∧ c ((k + 1) % L) = B i b) ∨
    (∃ k < L, c k = B i b ∧ c ((k + 1) % L) = A i b)
  A_coord : ∀ i b, A i b i = if b then 7 else 1
  B_coord : ∀ i b, B i b i = if b then 7 else 1
  distinct : ∀ i b i' b', (i, b) ≠ (i', b') →
    A i b ≠ A i' b' ∧ A i b ≠ B i' b' ∧ B i b ≠ A i' b' ∧ B i b ≠ B i' b'
  AB_ne : ∀ i b, A i b ≠ B i b
  A_opp : ∀ i, A i true = A i false + 6 • eZ i
  B_opp : ∀ i, B i true = B i false + 6 • eZ i

/-- The plane loop of `LatticeCycleAux.lean` (`loop0`, `pA 0`, `pB 0`), as a cube loop in
dimension 2 (`ℤ × ℤ ≃ (Fin 2 → ℤ)`); its properties by `decide`. -/
theorem exists_cubeLoop_two : Nonempty (CubeLoop 2) := by
  sorry

/-- **Doubling.** From a cube loop in dimension `d` (with `d ≥ 2`, so that its length exceeds the
number of designated points enough to find the two edges needed), a cube loop in dimension
`d + 1` of length `2 L + 10`, as in the header. -/
theorem exists_cubeLoop_succ {d : ℕ} (hd : 2 ≤ d) (l : CubeLoop d) :
    ∃ l' : CubeLoop (d + 1), l'.L = 2 * l.L + 10 := by
  sorry

theorem exists_cubeLoop {d : ℕ} (hd : 2 ≤ d) : Nonempty (CubeLoop d) := by
  sorry

/-! ### The cycle through a connected set of cubes -/

/-- **The self-avoiding lattice cycle through the cubes** (the plane's `exists_latticeCycle` in
`ℤ^d`): the invariant and the splice of `LatticeCycleAux.lean`, with the cube loop's `A`, `B`,
`edge`, `distinct`, `A_opp`, `B_opp` in place of `pA`, `pB`, `D_pair`, `pair_eq`, `side_eq`,
`dvec_opp`. The detour across the face `(i, b)` of `s` into `ℓ = s + faceDir i b`:
`x + e, x + 2e, … (the loop of ℓ the long way from its designated edge of the face (i, ¬b)) …,
y + 2e, y + e`, where `x → y` is the designated edge of `(i, b)` in `s`. Length `L₀ + (L₀ + 2)
(N - 1)` for the loop length `L₀`. -/
theorem exists_latticeCycleN {d : ℕ} (hd : 2 ≤ d) (T : Finset (Fin d → ℤ)) (hT : T.Nonempty)
    (hc : CubeConnected T) :
    ∃ (L : ℕ) (c : ℕ → (Fin d → ℤ)), 24 ≤ L ∧ InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStepN (c i) (c (i + 1))) ∧ IsUnitStepN (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InCube s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InCubeInt s (c i) := by
  sorry

theorem exists_latticePathN_of_cubes {d : ℕ} (hd : 2 ≤ d) (T : Finset (Fin d → ℤ))
    (hT : T.Nonempty) (hc : CubeConnected T) :
    ∃ (n : ℕ) (P : LatticePathN d n), 23 ≤ n ∧
      (∀ i ≤ n, ∃ s ∈ T, InCube s (P.c i)) ∧
      ∀ s ∈ T, ∃ i ≤ n, InCubeInt s (P.c i) := by
  sorry

/-! ### The cubes of a `d`-dimensional `E` -/

/-- The closed cube `s` of side `δ` along the orthonormal family `e`. -/
def cubeSet {d : ℕ} (e : Fin d → E) (δ : ℝ) (s : Fin d → ℤ) : Set E :=
  {x | ∀ i, δ * s i ≤ inner ℝ x (e i) ∧ inner ℝ x (e i) ≤ δ * (s i + 1)}

def cubesMeeting {d : ℕ} (e : Fin d → E) (δ : ℝ) (g : Set E) : Set (Fin d → ℤ) :=
  {s | (cubeSet e δ s ∩ g).Nonempty}

/-- A `d`-dimensional real inner product space has an orthonormal basis `Fin d → E`. -/
theorem exists_orthonormal_basis_fin [FiniteDimensional ℝ E] {d : ℕ}
    (h : Module.finrank ℝ E = d) :
    ∃ e : Fin d → E, Orthonormal ℝ e ∧ ∀ x : E, x = ∑ i, (inner ℝ x (e i)) • e i := by
  sorry

theorem cubesMeeting_finite {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : Bornology.IsBounded g) : (cubesMeeting e δ g).Finite := by
  sorry

theorem exists_cube_mem {d : ℕ} (e : Fin d → E) {δ : ℝ} (hδ : 0 < δ) (x : E) :
    ∃ s, x ∈ cubeSet e δ s := by
  sorry

/-- A cube of side `δ` has diameter `δ √d` (in `E` spanned by `e`); `≤ √d · δ` is stated. -/
theorem diam_cubeSet_le {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e)
    (hspan : ∀ x : E, x = ∑ i, (inner ℝ x (e i)) • e i) {δ : ℝ} (hδ : 0 < δ) (s : Fin d → ℤ) :
    ∀ x ∈ cubeSet e δ s, ∀ y ∈ cubeSet e δ s, dist x y ≤ Real.sqrt d * δ := by
  sorry

theorem latticePtN_mem_cubeSet {d : ℕ} {e : Fin d → E} (hon : Orthonormal ℝ e) {δ : ℝ}
    (hδ : 0 < δ) {s p : Fin d → ℤ} (h : InCube s p) : latticePtN e (δ / 8) p ∈ cubeSet e δ s := by
  sorry

/-- **The cubes meeting a connected set are connected.** If `x ∈ g` lies in cubes `a` and `b`,
then `|a i - b i| ≤ 1` for every `i`, and changing the coordinates of `a` into those of `b` one
at a time passes through cubes all containing `x`, consecutive ones adjacent; so a split of the
cubes with no adjacency across it would split `g` into two closed sets that do not meet (the plane
argument of `squaresMeeting_connected`, by induction on the number of differing coordinates). -/
theorem cubesMeeting_connected {d : ℕ} (e : Fin d → E) {δ : ℝ} (hδ : 0 < δ) {g : Set E}
    (hg : IsConnected g) (hfin : (cubesMeeting e δ g).Finite) :
    CubeConnected hfin.toFinset := by
  sorry

/-! ### Assembly -/

/-- **The density lemma in dimension `d ≥ 3`**: `δ := ε / (4 √d)`, the cubes of side `δ` meeting
`g`, the lattice path at fine mesh `δ/8`, the chain of `exists_threadedChain_of_latticePathN`.
(Constants: links `≤ 16 (δ/8) = 2δ ≤ ε/2`; union within `δ/8 + δ/8 + √d δ ≤ ε`; `g` within
`√d δ + δ/8` of the union.) -/
theorem geomLemma'_of_finrank_ge_three [FiniteDimensional ℝ E] (h : 3 ≤ Module.finrank ℝ E) :
    GeomLemma' E := by
  sorry

/-- **The density lemma in every finite dimension `≥ 2`**: the plane case
(`geomLemma'_of_finrank_two`) or the previous theorem. -/
theorem geomLemma'_of_finrank [FiniteDimensional ℝ E] (h : 2 ≤ Module.finrank ℝ E) :
    GeomLemma' E := by
  sorry

/-- **The density lemma, as Bing states it** (Euclidean `n`-space, `n ≥ 2`, and Hilbert space):
`geomLemma'_of_subspaces` with `geomLemma'_of_finrank` for every finite-dimensional subspace of
dimension `≥ 2`. This is the proof to be placed into the open `geomLemma'_of_two_le_rank` in
`HPC/Plane/LatticeCycle.lean` (which imports neither this file nor `BandN.lean`): either move
that statement and its three consequences into this file (deleting them from `LatticeCycle.lean`
and updating `OPEN.md`, `Axioms.lean`), or restructure the imports. State what was done. -/
theorem geomLemma'_of_two_le_rank' [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    GeomLemma' E := by
  sorry

end HPC.Plane
