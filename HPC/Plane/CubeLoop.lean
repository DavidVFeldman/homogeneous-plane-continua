import HPC.Plane.BandN

/-!
# Batch 113, item 1: cube loops in `ℤ^d`

Split off from the skeleton `HPC/Plane/CubeCycle.lean` (for length): the definitions of the
skeleton (`eZ`, `InCube`, `InCubeInt`, `CubeConnected`, `faceDir`, `CubeLoop`) and item 1
(`exists_cubeLoop_two`, `exists_cubeLoop_succ`, `exists_cubeLoop`), with the statements of the
skeleton. The cycle (item 2) is in `HPC/Plane/CubeCycleAux.lean`; items 3–4 in
`HPC/Plane/CubeCycle.lean`.

* The base loop (`d = 2`) is the plane loop `LCyc.loop0` of `LatticeCycleAux.lean`, transported
  along `p ↦ ![p.1, p.2]`; the face `(i, b)` is the side `LCyc.dvec j` with `j = 0, 1, 2, 3` for
  `(0, true), (1, true), (0, false), (1, false)`.
* Doubling (`exists_cubeLoop_succ`): two edges `k₀ ≠ k₁` of the loop with no designated endpoint
  (they exist since at most `4d` designated points touch at most `8d` of the `L ≥ 8d + 2` edges);
  the loop opened at `k₀` (`CubeLoopAux.fwd`) at height `1`, the column of `c k₀` at heights
  `2, …, 6`, the opened loop backwards at height `7`, the column of `c (k₀ + 1)` at heights
  `6, …, 2`: length `2 L + 10`. Old designated edges at height `1`; the two new faces get the
  edge `k₁` at heights `1` and `7`.
-/

namespace HPC.Plane

open Set Metric

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

namespace CubeLoopAux

/-! ### Unit steps -/

theorem isUnitStepN_symm {d : ℕ} {p q : Fin d → ℤ} (h : IsUnitStepN p q) : IsUnitStepN q p := by
  unfold IsUnitStepN at *
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _

theorem eZ_apply {d : ℕ} (i j : Fin d) : eZ i j = if j = i then 1 else 0 := by
  simp [eZ, Pi.single_apply]

theorem faceDir_apply {d : ℕ} (i : Fin d) (b : Bool) (j : Fin d) :
    faceDir i b j = if j = i then (if b then 1 else -1) else 0 := by
  cases b <;> by_cases h : j = i <;> simp [faceDir, eZ_apply, h]

theorem faceDir_self {d : ℕ} (i : Fin d) (b : Bool) : faceDir i b i = if b then 1 else -1 := by
  simp [faceDir_apply]

theorem faceDir_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) (b : Bool) : faceDir i b j = 0 := by
  simp [faceDir_apply, h]

theorem isUnitStepN_faceDir {d : ℕ} (p : Fin d → ℤ) (i : Fin d) (b : Bool) :
    IsUnitStepN p (p + faceDir i b) := by
  unfold IsUnitStepN
  simp only [Pi.add_apply, add_sub_cancel_left, faceDir_apply]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj; simp [hj]
  · simp

theorem isUnitStepN_faceDir' {d : ℕ} (p : Fin d → ℤ) (i : Fin d) (b : Bool) :
    IsUnitStepN (p + faceDir i b) p := isUnitStepN_symm (isUnitStepN_faceDir p i b)

theorem isUnitStepN_iff {d : ℕ} {p q : Fin d → ℤ} (h : IsUnitStepN p q) :
    ∃ i b, q = p + faceDir i b := by
  obtain ⟨a, ha, h0⟩ := BandNAux.unitN_cases (u := q - p) (by simpa using h)
  rcases ha with ha | ha
  · refine ⟨a, true, funext fun j => ?_⟩
    by_cases hj : j = a
    · subst hj; simp only [Pi.sub_apply] at ha; simp [faceDir_self]; omega
    · have := h0 j hj; simp only [Pi.sub_apply] at this; simp [faceDir_ne hj]; omega
  · refine ⟨a, false, funext fun j => ?_⟩
    by_cases hj : j = a
    · subst hj; simp only [Pi.sub_apply] at ha; simp [faceDir_self]; omega
    · have := h0 j hj; simp only [Pi.sub_apply] at this; simp [faceDir_ne hj]; omega

theorem faceDir_opp {d : ℕ} (s : Fin d → ℤ) (i : Fin d) (b : Bool) :
    s + faceDir i b + faceDir i (!b) = s := by
  funext j; by_cases hj : j = i <;> cases b <;> simp [faceDir_apply, hj]

theorem inCube_of_inCubeInt {d : ℕ} {s p : Fin d → ℤ} (h : InCubeInt s p) : InCube s p :=
  fun i => ⟨(h i).1.le, (h i).2.le⟩

theorem inCubeInt_unique {d : ℕ} {s t p : Fin d → ℤ} (h1 : InCubeInt s p) (h2 : InCubeInt t p) :
    s = t := by
  funext i; have := h1 i; have := h2 i; omega

/-! ### Opening a closed path at an edge -/

/-- The closed path `c 0, …, c (L-1)` opened at its edge `c k₀ → c (k₀ + 1)`, read forward from
`c (k₀ + 1)` (so its last point, index `L - 1`, is `c k₀`). -/
def fwd {α : Type*} (c : ℕ → α) (L k₀ : ℕ) (j : ℕ) : α := c ((k₀ + 1 + j) % L)

theorem fwd_injOn {α : Type*} {c : ℕ → α} {L : ℕ} (hL : 0 < L) (k₀ : ℕ)
    (hinj : InjOn c (Iio L)) : InjOn (fwd c L k₀) (Iio L) := by
  intro j₁ hj₁ j₂ hj₂ heq
  simp only [mem_Iio] at hj₁ hj₂
  have h1 := hinj (mem_Iio.mpr (Nat.mod_lt (k₀ + 1 + j₁) hL))
    (mem_Iio.mpr (Nat.mod_lt (k₀ + 1 + j₂) hL)) heq
  have h2 : j₁ ≡ j₂ [MOD L] := Nat.ModEq.add_left_cancel' (k₀ + 1) h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at h2

theorem fwd_succ {α : Type*} (c : ℕ → α) (L k₀ j : ℕ) :
    fwd c L k₀ (j + 1) = c (((k₀ + 1 + j) % L + 1) % L) := by
  simp only [fwd, Nat.mod_add_mod, add_assoc]

theorem fwd_lt {L : ℕ} (hL : 0 < L) (k₀ j : ℕ) :
    (k₀ + 1 + j) % L < L := Nat.mod_lt _ hL

theorem fwd_zero {α : Type*} (c : ℕ → α) (L k₀ : ℕ) : fwd c L k₀ 0 = c ((k₀ + 1) % L) := rfl

theorem fwd_last {α : Type*} (c : ℕ → α) {L k₀ : ℕ} (hk : k₀ < L) :
    fwd c L k₀ (L - 1) = c k₀ := by
  simp only [fwd]
  rw [show k₀ + 1 + (L - 1) = k₀ + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

theorem fwd_mem {α : Type*} (c : ℕ → α) {L : ℕ} (hL : 0 < L) (k₀ : ℕ) {k : ℕ} (hk : k < L) :
    ∃ j < L, fwd c L k₀ j = c k := by
  obtain ⟨j, hj, hjk⟩ := LCyc.mod_surj hL (k₀ + 1) k hk
  exact ⟨j, hj, by simp only [fwd, add_comm (k₀ + 1) j, hjk]⟩

/-- Every edge of the closed path other than the opened one is an edge of the opened path. -/
theorem fwd_edge {α : Type*} (c : ℕ → α) {L k₀ k₁ : ℕ} (hk₀ : k₀ < L) (hk₁ : k₁ < L)
    (hne : k₁ ≠ k₀) :
    ∃ m, m + 1 < L ∧ fwd c L k₀ m = c k₁ ∧ fwd c L k₀ (m + 1) = c ((k₁ + 1) % L) := by
  have hL : 0 < L := by omega
  obtain ⟨m, hm, hmk⟩ := LCyc.mod_surj hL (k₀ + 1) k₁ hk₁
  rw [add_comm m] at hmk
  refine ⟨m, ?_, by simp only [fwd, hmk], by rw [fwd_succ, hmk]⟩
  by_contra hcon
  have : m = L - 1 := by omega
  subst this
  rw [show k₀ + 1 + (L - 1) = k₀ + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk₀] at hmk
  exact hne hmk.symm

/-! ### Opened cube loops -/

/-- `q` is the loop `l` opened at the designated edge of the face `(i, b)`, from `u` to `v`: the
points of `l`, self-avoiding, consecutive ones a unit step apart, and every other designated edge
an edge of `q`. -/
def IsOpenedLoop {d : ℕ} (l : CubeLoop d) (i : Fin d) (b : Bool) (q : ℕ → (Fin d → ℤ))
    (u v : Fin d → ℤ) : Prop :=
  q 0 = u ∧ q (l.L - 1) = v ∧ InjOn q (Iio l.L) ∧
    (∀ k, k + 1 < l.L → IsUnitStepN (q k) (q (k + 1))) ∧ (∀ k < l.L, InCubeInt 0 (q k)) ∧
    ∀ i' b', (i', b') ≠ (i, b) → ∃ k, k + 1 < l.L ∧
      ((q k = l.A i' b' ∧ q (k + 1) = l.B i' b') ∨ (q k = l.B i' b' ∧ q (k + 1) = l.A i' b'))

theorem isOpenedLoop_rev {d : ℕ} {l : CubeLoop d} {i : Fin d} {b : Bool} {q : ℕ → (Fin d → ℤ)}
    {u v : Fin d → ℤ} (h : IsOpenedLoop l i b q u v) :
    IsOpenedLoop l i b (fun k => q (l.L - 1 - k)) v u := by
  obtain ⟨h0, h1, hinj, hstep, hmem, hedge⟩ := h
  have hL := l.two_le
  refine ⟨by simpa using h1, by simpa [show l.L - 1 - (l.L - 1) = 0 by omega] using h0, ?_, ?_,
    ?_, ?_⟩
  · intro a ha b' hb heq
    simp only [mem_Iio] at ha hb
    have := hinj (mem_Iio.mpr (show l.L - 1 - a < l.L by omega))
      (mem_Iio.mpr (show l.L - 1 - b' < l.L by omega)) heq
    omega
  · intro k hk
    have := hstep (l.L - 1 - (k + 1)) (by omega)
    rw [show l.L - 1 - (k + 1) + 1 = l.L - 1 - k by omega] at this
    exact isUnitStepN_symm this
  · intro k hk; exact hmem _ (by omega)
  · intro i' b' hne
    obtain ⟨k, hk, h⟩ := hedge i' b' hne
    refine ⟨l.L - 1 - (k + 1), by omega, ?_⟩
    simp only [show l.L - 1 - (l.L - 1 - (k + 1)) = k + 1 by omega,
      show l.L - 1 - (l.L - 1 - (k + 1) + 1) = k by omega]
    tauto

theorem designated_ne {d : ℕ} (l : CubeLoop d) {i i' : Fin d} {b b' : Bool}
    (hne : (i', b') ≠ (i, b)) {x : Fin d → ℤ} (hx : x = l.A i' b' ∨ x = l.B i' b') :
    x ≠ l.A i b ∧ x ≠ l.B i b := by
  have := l.distinct i' b' i b hne
  rcases hx with rfl | rfl <;> tauto

/-- The loop opened at the designated edge of `(i, b)`, in both directions. -/
theorem exists_isOpenedLoop {d : ℕ} (l : CubeLoop d) (i : Fin d) (b : Bool) :
    (∃ q, IsOpenedLoop l i b q (l.A i b) (l.B i b)) ∧
      ∃ q, IsOpenedLoop l i b q (l.B i b) (l.A i b) := by
  have hL : 0 < l.L := by have := l.two_le; omega
  -- the loop opened at an edge `c k₀ = v → c (k₀+1) = u`, from `u` to `v`
  have key : ∀ k₀ < l.L, ∀ u v, l.c k₀ = v → l.c ((k₀ + 1) % l.L) = u →
      (u = l.A i b ∧ v = l.B i b ∨ u = l.B i b ∧ v = l.A i b) →
      IsOpenedLoop l i b (fwd l.c l.L k₀) u v := by
    intro k₀ hk₀ u v hv hu huv
    refine ⟨hu, by rw [fwd_last _ hk₀, hv], fwd_injOn hL k₀ l.injOn, ?_, ?_, ?_⟩
    · intro k _
      rw [fwd_succ]
      exact l.step _ (fwd_lt hL k₀ k)
    · intro k _
      exact l.mem _ (fwd_lt hL k₀ k)
    · intro i' b' hne
      have hk₀ne : ∀ k₁ < l.L, (l.c k₁ = l.A i' b' ∨ l.c k₁ = l.B i' b') → k₁ ≠ k₀ := by
        intro k₁ _ hx he
        subst he
        have := designated_ne l hne hx
        rcases huv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rw [hv] at this <;> tauto
      rcases l.edge i' b' with ⟨k₁, hk₁, hA, hB⟩ | ⟨k₁, hk₁, hB, hA⟩
      · obtain ⟨m, hm, h1, h2⟩ := fwd_edge l.c hk₀ hk₁ (hk₀ne k₁ hk₁ (Or.inl hA))
        exact ⟨m, hm, Or.inl ⟨h1.trans hA, h2.trans hB⟩⟩
      · obtain ⟨m, hm, h1, h2⟩ := fwd_edge l.c hk₀ hk₁ (hk₀ne k₁ hk₁ (Or.inr hB))
        exact ⟨m, hm, Or.inr ⟨h1.trans hB, h2.trans hA⟩⟩
  rcases l.edge i b with ⟨k₀, hk₀, hA, hB⟩ | ⟨k₀, hk₀, hB, hA⟩
  · have h := key k₀ hk₀ _ _ hA hB (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨_, isOpenedLoop_rev h⟩, ⟨_, h⟩⟩
  · have h := key k₀ hk₀ _ _ hB hA (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨_, h⟩, ⟨_, isOpenedLoop_rev h⟩⟩


/-! ### Extension by a last coordinate -/

/-- `x` placed at height `h` in `ℤ^(d+1)`. -/
def ext {d : ℕ} (x : Fin d → ℤ) (h : ℤ) : Fin (d + 1) → ℤ := Fin.snoc x h

@[simp] theorem ext_castSucc {d : ℕ} (x : Fin d → ℤ) (h : ℤ) (j : Fin d) :
    ext x h (Fin.castSucc j) = x j := by simp [ext]

@[simp] theorem ext_last {d : ℕ} (x : Fin d → ℤ) (h : ℤ) : ext x h (Fin.last d) = h := by
  simp [ext]

theorem ext_inj {d : ℕ} {x y : Fin d → ℤ} {h h' : ℤ} : ext x h = ext y h' ↔ x = y ∧ h = h' := by
  constructor
  · intro e
    exact ⟨funext fun j => by simpa using congrFun e (Fin.castSucc j),
      by simpa using congrFun e (Fin.last d)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem isUnitStepN_ext_iff {d : ℕ} (x y : Fin d → ℤ) (h : ℤ) :
    IsUnitStepN (ext x h) (ext y h) ↔ IsUnitStepN x y := by
  unfold IsUnitStepN; rw [Fin.sum_univ_castSucc]; simp

theorem isUnitStepN_ext_up {d : ℕ} (x : Fin d → ℤ) (h h' : ℤ) (hh : h' = h + 1) :
    IsUnitStepN (ext x h) (ext x h') := by
  unfold IsUnitStepN; rw [Fin.sum_univ_castSucc]; simp [hh]

theorem isUnitStepN_ext_down {d : ℕ} (x : Fin d → ℤ) (h h' : ℤ) (hh : h = h' + 1) :
    IsUnitStepN (ext x h) (ext x h') := isUnitStepN_symm (isUnitStepN_ext_up x h' h hh)

theorem inCubeInt_ext {d : ℕ} {x : Fin d → ℤ} {h : ℤ} (hx : InCubeInt 0 x) (h0 : 0 < h)
    (h8 : h < 8) : InCubeInt 0 (ext x h) := by
  intro j
  cases j using Fin.lastCases with
  | last => simp [h0, h8]
  | cast j => simpa using hx j

theorem ext_add_eZ_castSucc {d : ℕ} (x : Fin d → ℤ) (h : ℤ) (j : Fin d) (a : ℕ) :
    ext x h + a • eZ (Fin.castSucc j) = ext (x + a • eZ j) h := by
  funext k
  cases k using Fin.lastCases with
  | last => simp [eZ_apply, (Fin.castSucc_lt_last j).ne']
  | cast k => simp [eZ_apply]

theorem ext_add_eZ_last {d : ℕ} (x : Fin d → ℤ) (h : ℤ) (a : ℕ) :
    ext x h + a • eZ (Fin.last d) = ext x (h + a) := by
  funext k
  cases k using Fin.lastCases with
  | last => simp [eZ_apply]
  | cast k => simp [eZ_apply, (Fin.castSucc_lt_last k).ne]

/-! ### Two edges with undesignated endpoints -/

/-- `x` is not a designated point of `l`. -/
def Undes {d : ℕ} (l : CubeLoop d) (x : Fin d → ℤ) : Prop := ∀ i b, x ≠ l.A i b ∧ x ≠ l.B i b

theorem mod_succ_inj {L a b : ℕ} (ha : a < L) (hb : b < L) (h : (a + 1) % L = (b + 1) % L) :
    a = b := by
  have h2 : a ≡ b [MOD L] := Nat.ModEq.add_right_cancel' 1 h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

theorem exists_two_free_edges {d : ℕ} (l : CubeLoop d) :
    ∃ k₀ k₁, k₀ < l.L ∧ k₁ < l.L ∧ k₁ ≠ k₀ ∧ Undes l (l.c k₀) ∧ Undes l (l.c ((k₀ + 1) % l.L)) ∧
      Undes l (l.c k₁) ∧ Undes l (l.c ((k₁ + 1) % l.L)) := by
  classical
  have hL : 0 < l.L := by have := l.two_le; omega
  set Des : Finset (Fin d → ℤ) := Finset.univ.image (fun f : Fin d × Bool => l.A f.1 f.2) ∪
    Finset.univ.image (fun f : Fin d × Bool => l.B f.1 f.2) with hDes
  have hDc : Des.card ≤ 4 * d := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin d × Bool)))
      (f := fun f => l.A f.1 f.2)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin d × Bool)))
      (f := fun f => l.B f.1 f.2)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1 h2
    omega
  have hund : ∀ x, x ∉ Des → Undes l x := by
    intro x hx i b
    constructor
    · rintro rfl; exact hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, b), by simp, rfl⟩))
    · rintro rfl
      exact hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, b), by simp, rfl⟩))
  set S1 := (Finset.range l.L).filter (fun k => l.c k ∈ Des)
  set S2 := (Finset.range l.L).filter (fun k => l.c ((k + 1) % l.L) ∈ Des)
  have hS1 : S1.card ≤ Des.card := by
    refine Finset.card_le_card_of_injOn l.c
      (fun k hk => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2) ?_
    intro a ha b hb hab
    exact l.injOn (mem_Iio.mpr (Finset.mem_range.mp (Finset.mem_filter.mp ha).1))
      (mem_Iio.mpr (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)) hab
  have hS2 : S2.card ≤ Des.card := by
    refine Finset.card_le_card_of_injOn (fun k => l.c ((k + 1) % l.L))
      (fun k hk => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2) ?_
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    exact mod_succ_inj ha' hb' (l.injOn (mem_Iio.mpr (Nat.mod_lt _ hL))
      (mem_Iio.mpr (Nat.mod_lt _ hL)) hab)
  have hG : 1 < (Finset.range l.L \ (S1 ∪ S2)).card := by
    have h1 := Finset.le_card_sdiff (S1 ∪ S2) (Finset.range l.L)
    have h2 := Finset.card_union_le S1 S2
    rw [Finset.card_range] at h1
    have := l.big
    omega
  obtain ⟨k₀, hk₀, k₁, hk₁, hne⟩ := Finset.one_lt_card.mp hG
  have mem : ∀ k ∈ Finset.range l.L \ (S1 ∪ S2), k < l.L ∧ Undes l (l.c k) ∧ Undes l (l.c ((k + 1) % l.L)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
    have hkL := Finset.mem_range.mp hk1
    refine ⟨hkL, hund _ fun h => hk2 (Finset.mem_union_left _ ?_),
      hund _ fun h => hk2 (Finset.mem_union_right _ ?_)⟩
    · exact Finset.mem_filter.mpr ⟨hk1, h⟩
    · exact Finset.mem_filter.mpr ⟨hk1, h⟩
  obtain ⟨a1, a2, a3⟩ := mem k₀ hk₀
  obtain ⟨b1, b2, b3⟩ := mem k₁ hk₁
  exact ⟨k₀, k₁, a1, b1, Ne.symm hne, a2, a3, b2, b3⟩


/-! ### The doubled loop -/

section Doubling

variable {d : ℕ} (l : CubeLoop d) (k₀ k₁ : ℕ)

/-- The doubled loop (header of the file): bottom copy, column, top copy backwards, column. -/
def dblPt (n : ℕ) : Fin (d + 1) → ℤ :=
  if n < l.L then ext (fwd l.c l.L k₀ n) 1
  else if n < l.L + 5 then ext (fwd l.c l.L k₀ (l.L - 1)) (((n - l.L : ℕ) : ℤ) + 2)
  else if n < 2 * l.L + 5 then ext (fwd l.c l.L k₀ (2 * l.L + 4 - n)) 7
  else ext (fwd l.c l.L k₀ 0) (6 - ((n - (2 * l.L + 5) : ℕ) : ℤ))

/-- Designated points of the doubled loop: the old ones at height `1`; for the new axis, the
endpoints of the edge `k₁` at height `7` (`b = true`) or `1`. -/
def dblA (i : Fin (d + 1)) (b : Bool) : Fin (d + 1) → ℤ :=
  Fin.lastCases (motive := fun _ => Fin (d + 1) → ℤ) (ext (l.c k₁) (if b then 7 else 1))
    (fun j => ext (l.A j b) 1) i

def dblB (i : Fin (d + 1)) (b : Bool) : Fin (d + 1) → ℤ :=
  Fin.lastCases (motive := fun _ => Fin (d + 1) → ℤ) (ext (l.c ((k₁ + 1) % l.L)) (if b then 7 else 1))
    (fun j => ext (l.B j b) 1) i

variable {l k₀}

theorem dblPt_bot {n : ℕ} (h : n < l.L) : dblPt l k₀ n = ext (fwd l.c l.L k₀ n) 1 := by
  simp [dblPt, h]

theorem dblPt_colp {n : ℕ} (h1 : l.L ≤ n) (h2 : n < l.L + 5) :
    dblPt l k₀ n = ext (fwd l.c l.L k₀ (l.L - 1)) (((n - l.L : ℕ) : ℤ) + 2) := by
  simp [dblPt, h2, show ¬ n < l.L by omega]

theorem dblPt_top {n : ℕ} (h1 : l.L + 5 ≤ n) (h2 : n < 2 * l.L + 5) :
    dblPt l k₀ n = ext (fwd l.c l.L k₀ (2 * l.L + 4 - n)) 7 := by
  simp [dblPt, h2, show ¬ n < l.L by omega, show ¬ n < l.L + 5 by omega]

theorem dblPt_colq {n : ℕ} (h1 : 2 * l.L + 5 ≤ n) :
    dblPt l k₀ n = ext (fwd l.c l.L k₀ 0) (6 - ((n - (2 * l.L + 5) : ℕ) : ℤ)) := by
  simp [dblPt, show ¬ n < l.L by omega, show ¬ n < l.L + 5 by omega,
    show ¬ n < 2 * l.L + 5 by omega]

theorem fwd_step {n : ℕ} (hn : n + 1 < l.L) :
    IsUnitStepN (fwd l.c l.L k₀ n) (fwd l.c l.L k₀ (n + 1)) := by
  have hL : 0 < l.L := by omega
  rw [fwd_succ]
  exact l.step _ (fwd_lt hL k₀ n)

theorem dblPt_step {n : ℕ} (hn : n < 2 * l.L + 10) :
    IsUnitStepN (dblPt l k₀ n) (dblPt l k₀ ((n + 1) % (2 * l.L + 10))) := by
  have hL2 := l.two_le
  by_cases h9 : n + 1 = 2 * l.L + 10
  · rw [h9, Nat.mod_self, dblPt_colq (by omega), dblPt_bot (by omega)]
    exact isUnitStepN_ext_down _ _ _ (by push_cast; omega)
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases c1 : n + 1 < l.L
  · rw [dblPt_bot (by omega), dblPt_bot c1, isUnitStepN_ext_iff]
    exact fwd_step c1
  by_cases c2 : n + 1 = l.L
  · rw [dblPt_bot (by omega), dblPt_colp (by omega) (by omega), show n = l.L - 1 by omega]
    exact isUnitStepN_ext_up _ _ _ (by push_cast; omega)
  by_cases c3 : n + 1 < l.L + 5
  · rw [dblPt_colp (by omega) (by omega), dblPt_colp (by omega) (by omega)]
    exact isUnitStepN_ext_up _ _ _ (by omega)
  by_cases c4 : n + 1 = l.L + 5
  · rw [dblPt_colp (by omega) (by omega), dblPt_top (by omega) (by omega),
      show 2 * l.L + 4 - (n + 1) = l.L - 1 by omega]
    exact isUnitStepN_ext_up _ _ _ (by omega)
  by_cases c5 : n + 1 < 2 * l.L + 5
  · rw [dblPt_top (by omega) (by omega), dblPt_top (by omega) (by omega), isUnitStepN_ext_iff]
    have := fwd_step (l := l) (k₀ := k₀) (n := 2 * l.L + 4 - (n + 1)) (by omega)
    rw [show 2 * l.L + 4 - (n + 1) + 1 = 2 * l.L + 4 - n by omega] at this
    exact isUnitStepN_symm this
  by_cases c6 : n + 1 = 2 * l.L + 5
  · rw [dblPt_top (by omega) (by omega), dblPt_colq (by omega),
      show 2 * l.L + 4 - n = 0 by omega]
    exact isUnitStepN_ext_down _ _ _ (by push_cast; omega)
  · rw [dblPt_colq (by omega), dblPt_colq (by omega)]
    exact isUnitStepN_ext_down _ _ _ (by push_cast; omega)

theorem dblPt_injOn (hk₀ : k₀ < l.L) : InjOn (dblPt l k₀) (Iio (2 * l.L + 10)) := by
  have hL2 := l.two_le
  have hL : 0 < l.L := by omega
  have hr := fwd_injOn hL k₀ l.injOn
  have rinj : ∀ a b, a < l.L → b < l.L → fwd l.c l.L k₀ a = fwd l.c l.L k₀ b → a = b :=
    fun a b ha hb h => hr (mem_Iio.mpr ha) (mem_Iio.mpr hb) h
  have region : ∀ n, n < 2 * l.L + 10 →
      (n < l.L ∧ dblPt l k₀ n = ext (fwd l.c l.L k₀ n) 1) ∨
      (l.L ≤ n ∧ n < l.L + 5 ∧
        dblPt l k₀ n = ext (fwd l.c l.L k₀ (l.L - 1)) (((n - l.L : ℕ) : ℤ) + 2)) ∨
      (l.L + 5 ≤ n ∧ n < 2 * l.L + 5 ∧ dblPt l k₀ n = ext (fwd l.c l.L k₀ (2 * l.L + 4 - n)) 7) ∨
      (2 * l.L + 5 ≤ n ∧ dblPt l k₀ n =
        ext (fwd l.c l.L k₀ 0) (6 - ((n - (2 * l.L + 5) : ℕ) : ℤ))) := by
    intro n hn
    by_cases c1 : n < l.L
    · exact Or.inl ⟨c1, dblPt_bot c1⟩
    by_cases c2 : n < l.L + 5
    · exact Or.inr (Or.inl ⟨by omega, c2, dblPt_colp (by omega) c2⟩)
    by_cases c3 : n < 2 * l.L + 5
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, c3, dblPt_top (by omega) c3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, dblPt_colq (by omega)⟩))
  intro a ha b hb hab
  simp only [mem_Iio] at ha hb
  rcases region a ha with ⟨a1, ea⟩ | ⟨a1, a2, ea⟩ | ⟨a1, a2, ea⟩ | ⟨a1, ea⟩ <;>
  rcases region b hb with ⟨b1, eb⟩ | ⟨b1, b2, eb⟩ | ⟨b1, b2, eb⟩ | ⟨b1, eb⟩ <;>
  rw [ea, eb, ext_inj] at hab <;> obtain ⟨hx, hh⟩ := hab <;>
  first
  | omega
  | exact rinj _ _ a1 b1 hx
  | (have := rinj _ _ (by omega) (by omega) hx; omega)

theorem dbl_edge_bot (hk₀ : k₀ < l.L) (h0 : Undes l (l.c k₀)) {k : ℕ} (hk : k < l.L)
    (hx : ¬ Undes l (l.c k)) {x y : Fin d → ℤ} (hcx : l.c k = x) (hcy : l.c ((k + 1) % l.L) = y)
    (hh : ℤ) (hh1 : hh = 1) :
    ∃ m < 2 * l.L + 10, dblPt l k₀ m = ext x hh ∧
      dblPt l k₀ ((m + 1) % (2 * l.L + 10)) = ext y hh := by
  have hne : k ≠ k₀ := by rintro rfl; exact hx h0
  obtain ⟨m, hm, h1, h2⟩ := fwd_edge l.c hk₀ hk hne
  refine ⟨m, by omega, ?_, ?_⟩
  · rw [dblPt_bot (by omega), h1, hcx, hh1]
  · rw [Nat.mod_eq_of_lt (by omega), dblPt_bot hm, h2, hcy, hh1]

end Doubling


/-! ### The plane loop as a cube loop -/

/-- `ℤ × ℤ ≃ (Fin 2 → ℤ)`. -/
def toV (p : ℤ × ℤ) : Fin 2 → ℤ := ![p.1, p.2]

theorem toV_injective : Function.Injective toV := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [toV, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

theorem isUnitStepN_toV (p q : ℤ × ℤ) : IsUnitStepN (toV p) (toV q) ↔ IsUnitStep p q := by
  simp [IsUnitStepN, IsUnitStep, Fin.sum_univ_two, toV]

theorem inCubeInt_toV (p : ℤ × ℤ) : InCubeInt 0 (toV p) ↔ InSqInt 0 p := by
  simp [InCubeInt, InSqInt, Fin.forall_fin_two, toV, and_assoc]

/-- The face `(i, b)` of the square as a side `LCyc.dvec j`. -/
def faceIdx (i : Fin 2) (b : Bool) : Fin 4 :=
  if b then (if i = 0 then 0 else 1) else (if i = 0 then 2 else 3)

end CubeLoopAux

open CubeLoopAux

/-- The plane loop `LCyc.loop0` with the middle pairs `LCyc.pA 0`, `LCyc.pB 0`, as a cube loop. -/
def cubeLoopTwo : CubeLoop 2 where
  L := 24
  two_le := by norm_num
  big := by norm_num
  c k := toV (LCyc.Lfun k)
  injOn := by
    intro a ha b hb h
    simp only [mem_Iio] at ha hb
    have := LCyc.L_inj ⟨a, ha⟩ ⟨b, hb⟩ (toV_injective h)
    simpa using this
  step k hk := (isUnitStepN_toV _ _).mpr (by simpa using LCyc.L_step ⟨k, hk⟩)
  mem k hk := (inCubeInt_toV _).mpr (LCyc.L_mem ⟨k, hk⟩)
  A i b := toV (LCyc.pA 0 (faceIdx i b))
  B i b := toV (LCyc.pB 0 (faceIdx i b))
  A_mem i b := by
    obtain ⟨k, hk | hk⟩ := LCyc.L_pair (faceIdx i b)
    · exact ⟨k, k.2, by rw [← hk.1]⟩
    · exact ⟨(k + 1) % 24, Nat.mod_lt _ (by norm_num), by rw [← hk.2]⟩
  B_mem i b := by
    obtain ⟨k, hk | hk⟩ := LCyc.L_pair (faceIdx i b)
    · exact ⟨(k + 1) % 24, Nat.mod_lt _ (by norm_num), by rw [← hk.2]⟩
    · exact ⟨k, k.2, by rw [← hk.1]⟩
  edge i b := by
    obtain ⟨k, hk | hk⟩ := LCyc.L_pair (faceIdx i b)
    · exact Or.inl ⟨k, k.2, by rw [← hk.1], by rw [← hk.2]⟩
    · exact Or.inr ⟨k, k.2, by rw [← hk.1], by rw [← hk.2]⟩
  A_coord := by decide
  B_coord := by decide
  distinct := by
    simp only [ne_eq, toV_injective.eq_iff]
    decide
  AB_ne := by
    simp only [ne_eq, toV_injective.eq_iff]
    decide
  A_opp := by decide
  B_opp := by decide

/-- The plane loop (`LatticeCycleAux.lean`: `loop0`, `pA 0`, `pB 0`), as a cube loop in
dimension 2 (`ℤ × ℤ ≃ (Fin 2 → ℤ)`); its properties by `decide`. -/
theorem exists_cubeLoop_two : Nonempty (CubeLoop 2) := ⟨cubeLoopTwo⟩

/-- **Doubling.** From a cube loop in dimension `d`, a cube loop in dimension `d + 1` of length
`2 L + 10`, as in the header. (Shape change: the hypothesis `2 ≤ d` of the skeleton is dropped;
the field `big` of the loop already provides the two edges needed.) -/
theorem exists_cubeLoop_succ {d : ℕ} (l : CubeLoop d) :
    ∃ l' : CubeLoop (d + 1), l'.L = 2 * l.L + 10 := by
  obtain ⟨k₀, k₁, hk₀, hk₁, hne, u0, -, u1, u1'⟩ := exists_two_free_edges l
  have hL2 := l.two_le
  have hL : 0 < l.L := by omega
  have hedge : ∀ (i : Fin (d + 1)) (b : Bool),
      (∃ k < 2 * l.L + 10, dblPt l k₀ k = dblA l k₁ i b ∧
        dblPt l k₀ ((k + 1) % (2 * l.L + 10)) = dblB l k₁ i b) ∨
      (∃ k < 2 * l.L + 10, dblPt l k₀ k = dblB l k₁ i b ∧
        dblPt l k₀ ((k + 1) % (2 * l.L + 10)) = dblA l k₁ i b) := by
    intro i b
    cases i using Fin.lastCases with
    | last =>
      obtain ⟨m, hm, h1, h2⟩ := fwd_edge l.c hk₀ hk₁ hne
      cases b
      · left
        refine ⟨m, by omega, ?_, ?_⟩
        · simp [dblA, dblPt_bot (show m < l.L by omega), h1]
        · rw [Nat.mod_eq_of_lt (by omega)]
          simp [dblB, dblPt_bot hm, h2]
      · right
        refine ⟨2 * l.L + 3 - m, by omega, ?_, ?_⟩
        · rw [dblPt_top (by omega) (by omega), show 2 * l.L + 4 - (2 * l.L + 3 - m) = m + 1 by omega]
          simp [dblB, h2]
        · rw [Nat.mod_eq_of_lt (by omega), dblPt_top (by omega) (by omega),
            show 2 * l.L + 4 - (2 * l.L + 3 - m + 1) = m by omega]
          simp [dblA, h1]
    | cast j =>
      simp only [dblA, dblB, Fin.lastCases_castSucc]
      rcases l.edge j b with ⟨k, hk, hA, hB⟩ | ⟨k, hk, hB, hA⟩
      · exact Or.inl (dbl_edge_bot hk₀ u0 hk (fun h => (h j b).1 hA) hA hB 1 rfl)
      · exact Or.inr (dbl_edge_bot hk₀ u0 hk (fun h => (h j b).2 hB) hB hA 1 rfl)
  have hk₁ne : l.c k₁ ≠ l.c ((k₁ + 1) % l.L) := by
    intro h
    have := l.injOn (mem_Iio.mpr hk₁) (mem_Iio.mpr (Nat.mod_lt _ hL)) h
    by_cases hlt : k₁ + 1 < l.L
    · rw [Nat.mod_eq_of_lt hlt] at this; omega
    · rw [show k₁ + 1 = l.L by omega, Nat.mod_self] at this; omega
  refine ⟨{ L := 2 * l.L + 10
            two_le := by omega
            big := by have := l.big; omega
            c := dblPt l k₀
            injOn := dblPt_injOn hk₀
            step := fun k hk => dblPt_step hk
            mem := ?_
            A := dblA l k₁
            B := dblB l k₁
            A_mem := ?_
            B_mem := ?_
            edge := hedge
            A_coord := ?_
            B_coord := ?_
            distinct := ?_
            AB_ne := ?_
            A_opp := ?_
            B_opp := ?_ }, rfl⟩
  · intro n hn
    have hm : ∀ j, InCubeInt 0 (fwd l.c l.L k₀ j) := fun j => l.mem _ (fwd_lt hL k₀ j)
    by_cases c1 : n < l.L
    · rw [dblPt_bot c1]; exact inCubeInt_ext (hm _) (by norm_num) (by norm_num)
    by_cases c2 : n < l.L + 5
    · rw [dblPt_colp (by omega) c2]; exact inCubeInt_ext (hm _) (by omega) (by omega)
    by_cases c3 : n < 2 * l.L + 5
    · rw [dblPt_top (by omega) c3]; exact inCubeInt_ext (hm _) (by norm_num) (by norm_num)
    · rw [dblPt_colq (by omega)]; exact inCubeInt_ext (hm _) (by omega) (by omega)
  · intro i b
    rcases hedge i b with ⟨k, hk, h1, -⟩ | ⟨k, hk, -, h2⟩
    · exact ⟨k, hk, h1⟩
    · exact ⟨_, Nat.mod_lt _ (by omega), h2⟩
  · intro i b
    rcases hedge i b with ⟨k, hk, -, h2⟩ | ⟨k, hk, h1, -⟩
    · exact ⟨_, Nat.mod_lt _ (by omega), h2⟩
    · exact ⟨k, hk, h1⟩
  · intro i b
    cases i using Fin.lastCases with
    | last => simp [dblA]
    | cast j => simp [dblA, l.A_coord]
  · intro i b
    cases i using Fin.lastCases with
    | last => simp [dblB]
    | cast j => simp [dblB, l.B_coord]
  · intro i b i' b' hne'
    cases i using Fin.lastCases with
    | last =>
      cases i' using Fin.lastCases with
      | last =>
        have hb : b ≠ b' := fun h => hne' (by rw [h])
        simp only [dblA, dblB, Fin.lastCases_last, ne_eq, ext_inj]
        cases b <;> cases b' <;> simp_all
      | cast j' =>
        simp only [dblA, dblB, Fin.lastCases_last, Fin.lastCases_castSucc, ne_eq, ext_inj]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, and_true]
          exact ⟨(u1 j' b').1, (u1 j' b').2, (u1' j' b').1, (u1' j' b').2⟩
        · simp
    | cast j =>
      cases i' using Fin.lastCases with
      | last =>
        simp only [dblA, dblB, Fin.lastCases_last, Fin.lastCases_castSucc, ne_eq, ext_inj]
        cases b'
        · simp only [Bool.false_eq_true, ↓reduceIte, and_true]
          exact ⟨fun h => (u1 j b).1 h.symm, fun h => (u1' j b).1 h.symm,
            fun h => (u1 j b).2 h.symm, fun h => (u1' j b).2 h.symm⟩
        · simp
      | cast j' =>
        have hne2 : (j, b) ≠ (j', b') := fun h => hne' (by
          simp only [Prod.mk.injEq] at h ⊢; exact ⟨by rw [h.1], h.2⟩)
        have := l.distinct j b j' b' hne2
        simp only [dblA, dblB, Fin.lastCases_castSucc, ne_eq, ext_inj, and_true]
        exact this
  · intro i b
    cases i using Fin.lastCases with
    | last => simp only [dblA, dblB, Fin.lastCases_last, ne_eq, ext_inj, not_and]; exact fun h => absurd h hk₁ne
    | cast j => simp only [dblA, dblB, Fin.lastCases_castSucc, ne_eq, ext_inj, and_true]; exact l.AB_ne j b
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [dblA, Fin.lastCases_last, ext_add_eZ_last]
      norm_num
    | cast j => simp only [dblA, Fin.lastCases_castSucc, ext_add_eZ_castSucc, l.A_opp]
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [dblB, Fin.lastCases_last, ext_add_eZ_last]
      norm_num
    | cast j => simp only [dblB, Fin.lastCases_castSucc, ext_add_eZ_castSucc, l.B_opp]

/-- Cube loops of length at least `24` exist in every dimension `d ≥ 2`. -/
theorem exists_cubeLoop_ge {d : ℕ} (hd : 2 ≤ d) : ∃ l : CubeLoop d, 24 ≤ l.L := by
  induction d, hd using Nat.le_induction with
  | base => exact ⟨cubeLoopTwo, le_rfl⟩
  | succ d _ ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l', hl'⟩ := exists_cubeLoop_succ l
    exact ⟨l', by omega⟩

theorem exists_cubeLoop {d : ℕ} (hd : 2 ≤ d) : Nonempty (CubeLoop d) :=
  (exists_cubeLoop_ge hd).elim fun l _ => ⟨l⟩

end HPC.Plane
