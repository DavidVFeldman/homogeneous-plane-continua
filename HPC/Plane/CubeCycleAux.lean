import HPC.Plane.CubeLoop

/-!
# Batch 113, item 2: the self-avoiding lattice cycle through a connected set of cubes

Split off from the skeleton `HPC/Plane/CubeCycle.lean` (for length). The plane construction of
`LatticeCycleAux.lean` (`LCyc.Inv`, `inv_rot`, `inv_splice`, `inv_grow`, `exists_inv_sub`) with a
cube loop `l : CubeLoop d` in place of the 24-point square loop:

* cube `s` has fine coordinates `[8 s i, 8 s i + 8]`, and `tr s p = 8 • s + p` translates the
  loop of cube `0` to cube `s`;
* the faces `(i, b)` replace the four sides, `faceDir i b` replaces `dvec`;
* the *side points* `tr s (l.A i b) + faceDir i b`, `tr s (l.B i b) + faceDir i b` replace
  `pA s i + dvec i`, `pB s i + dvec i`.

Invariant (`CCyc.Inv l T L c`): `L = l.L + (l.L + 2) (|T| - 1)`; the points `c 0, …, c (L-1)` are
distinct, cyclically consecutive points a unit step apart; every point is a depth-1 point of a cube
of `T` or a side point of a face shared by two cubes of `T`; every cube of `T` has a depth-1 point
on the cycle; for every cube `s ∈ T` and every face `(i, b)` not shared within `T`, the designated
pair `tr s (l.A i b)`, `tr s (l.B i b)` is an edge of the cycle.

Step: for `ℓ = s + faceDir i b ∉ T` across the free face `(i, b)` of `s ∈ T`, rotate the cycle so
the designated edge `x → y` of `(i, b)` is the closing edge, and append `x + e`, the loop of `ℓ`
opened at its designated edge of the face `(i, ¬b)` from `x + 2e` to `y + 2e`
(`CubeLoopAux.IsOpenedLoop`), and `y + e` (with `e = faceDir i b`): `l.L + 2` new points.
-/

namespace HPC.Plane

open Set CubeLoopAux

namespace CCyc

variable {d : ℕ}

/-! ### Translation -/

/-- Translation of the loop of cube `0` to cube `s`: `tr s p = 8 • s + p`. -/
def tr (s p : Fin d → ℤ) : Fin d → ℤ := fun i => 8 * s i + p i

@[simp] theorem tr_apply (s p : Fin d → ℤ) (i : Fin d) : tr s p i = 8 * s i + p i := rfl

theorem tr_injective (s : Fin d → ℤ) : Function.Injective (tr s) := by
  intro p q h; funext i; have := congrFun h i; simp only [tr_apply] at this; omega

theorem isUnitStepN_tr (s p q : Fin d → ℤ) : IsUnitStepN (tr s p) (tr s q) ↔ IsUnitStepN p q := by
  unfold IsUnitStepN; simp only [tr_apply, add_sub_add_left_eq_sub]

theorem inCubeInt_tr (s p : Fin d → ℤ) : InCubeInt s (tr s p) ↔ InCubeInt 0 p := by
  unfold InCubeInt
  simp only [tr_apply, Pi.zero_apply, mul_zero, zero_add]
  constructor <;> intro h i <;> have := h i <;> omega

theorem A_int (l : CubeLoop d) (i : Fin d) (b : Bool) : InCubeInt 0 (l.A i b) := by
  obtain ⟨k, hk, h⟩ := l.A_mem i b; exact h ▸ l.mem k hk

theorem B_int (l : CubeLoop d) (i : Fin d) (b : Bool) : InCubeInt 0 (l.B i b) := by
  obtain ⟨k, hk, h⟩ := l.B_mem i b; exact h ▸ l.mem k hk

theorem int_coord {X : Fin d → ℤ} (h : InCubeInt 0 X) (k : Fin d) : 0 < X k ∧ X k < 8 := by
  have := h k; simp only [Pi.zero_apply, mul_zero, zero_add] at this; exact this

/-! ### Side points -/

theorem side_coord {s X : Fin d → ℤ} {i : Fin d} {b : Bool} (hX : X i = if b then 7 else 1) :
    (tr s X + faceDir i b) i = 8 * s i + (if b then 8 else 0) := by
  cases b <;> simp [faceDir_self, hX]; ring

theorem side_coord_ne {s X : Fin d → ℤ} {i j : Fin d} (hj : j ≠ i) (b : Bool) :
    (tr s X + faceDir i b) j = 8 * s j + X j := by
  simp [faceDir_ne hj]

theorem not_inCubeInt_side {s t X : Fin d → ℤ} {i : Fin d} {b : Bool}
    (hX : X i = if b then 7 else 1) : ¬ InCubeInt t (tr s X + faceDir i b) := by
  intro h
  have := h i
  rw [side_coord hX] at this
  cases b <;> simp at this <;> omega

theorem inCube_side {s X : Fin d → ℤ} {i : Fin d} {b : Bool} (hX0 : InCubeInt 0 X)
    (hX : X i = if b then 7 else 1) : InCube s (tr s X + faceDir i b) := by
  intro k
  by_cases hk : k = i
  · subst hk; rw [side_coord hX]; cases b <;> simp
  · rw [side_coord_ne hk]; have := int_coord hX0 k; omega

/-- A side point determines its face, up to the cube on either side. -/
theorem side_eq {s s' X X' : Fin d → ℤ} {i j : Fin d} {b b' : Bool} (hX0 : InCubeInt 0 X)
    (hX : X i = if b then 7 else 1) (hX0' : InCubeInt 0 X') (hX' : X' j = if b' then 7 else 1)
    (h : tr s' X' + faceDir j b' = tr s X + faceDir i b) :
    s' + faceDir j b' = s + faceDir i b ∨ s' = s + faceDir i b := by
  have hji : j = i := by
    by_contra hne
    have e := congrFun h j
    rw [side_coord hX', side_coord_ne hne] at e
    have := int_coord hX0 j
    cases b' <;> simp at e <;> omega
  subst hji
  have hk : ∀ k, k ≠ j → s' k = s k := by
    intro k hk
    have e := congrFun h k
    rw [side_coord_ne hk, side_coord_ne hk] at e
    have := int_coord hX0 k
    have := int_coord hX0' k
    omega
  have e := congrFun h j
  rw [side_coord hX', side_coord hX] at e
  cases b <;> cases b'
  · left; funext k; by_cases hkj : k = j
    · subst hkj; simp at e; simp; omega
    · simp [faceDir_ne hkj, hk k hkj]
  · right; funext k; by_cases hkj : k = j
    · subst hkj; simp at e; simp [faceDir_self]; omega
    · simp [faceDir_ne hkj, hk k hkj]
  · right; funext k; by_cases hkj : k = j
    · subst hkj; simp at e; simp [faceDir_self]; omega
    · simp [faceDir_ne hkj, hk k hkj]
  · left; funext k; by_cases hkj : k = j
    · subst hkj; simp at e; simp; omega
    · simp [faceDir_ne hkj, hk k hkj]

/-- The designated pair determines the cube and the face. -/
theorem pair_eq (l : CubeLoop d) {s s' : Fin d → ℤ} {i j : Fin d} {b b' : Bool}
    (h : (tr s' (l.A j b') = tr s (l.A i b) ∧ tr s' (l.B j b') = tr s (l.B i b)) ∨
      (tr s' (l.A j b') = tr s (l.B i b) ∧ tr s' (l.B j b') = tr s (l.A i b))) :
    s' = s ∧ (j, b') = (i, b) := by
  have hs : s' = s := by
    have h1 := (inCubeInt_tr s' _).mpr (A_int l j b')
    rcases h with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at h1
    · exact inCubeInt_unique h1 ((inCubeInt_tr s _).mpr (A_int l i b))
    · exact inCubeInt_unique h1 ((inCubeInt_tr s _).mpr (B_int l i b))
  subst hs
  refine ⟨rfl, ?_⟩
  by_contra hne
  have := l.distinct j b' i b hne
  rcases h with ⟨e, -⟩ | ⟨e, -⟩
  · exact this.1 (tr_injective _ e)
  · exact this.2.1 (tr_injective _ e)

/-- Across the face `(i, b)`, two steps out of the designated point of `(i, b)` of `s` is the
designated point of `(i, ¬b)` of the neighbour `s + faceDir i b`. -/
theorem tr_opp_aux {X Y : Fin d → ℤ} {i : Fin d} (hXY : X = Y + 6 • eZ i) (s : Fin d → ℤ) :
    (tr s Y + faceDir i false + faceDir i false = tr (s + faceDir i false) X) ∧
      (tr s X + faceDir i true + faceDir i true = tr (s + faceDir i true) Y) := by
  subst hXY
  constructor <;> funext k <;> by_cases hk : k = i <;>
    simp [faceDir_apply, eZ_apply, hk] <;> ring

theorem A_tr_opp (l : CubeLoop d) (s : Fin d → ℤ) (i : Fin d) (b : Bool) :
    tr s (l.A i b) + faceDir i b + faceDir i b = tr (s + faceDir i b) (l.A i (!b)) := by
  cases b
  · exact (tr_opp_aux (l.A_opp i) s).1
  · exact (tr_opp_aux (l.A_opp i) s).2

theorem B_tr_opp (l : CubeLoop d) (s : Fin d → ℤ) (i : Fin d) (b : Bool) :
    tr s (l.B i b) + faceDir i b + faceDir i b = tr (s + faceDir i b) (l.B i (!b)) := by
  cases b
  · exact (tr_opp_aux (l.B_opp i) s).1
  · exact (tr_opp_aux (l.B_opp i) s).2

/-! ### The invariant -/

/-- Admissible cycle points for the set `T`: depth-1 points of a cube of `T`, or the side points of
a face shared by two cubes of `T`. -/
def Good (l : CubeLoop d) (T : Finset (Fin d → ℤ)) (p : Fin d → ℤ) : Prop :=
  (∃ s ∈ T, InCubeInt s p) ∨
    ∃ s ∈ T, ∃ i b, s + faceDir i b ∈ T ∧
      (p = tr s (l.A i b) + faceDir i b ∨ p = tr s (l.B i b) + faceDir i b)

/-- `x → y` is an edge of the closed path `c 0, …, c (L-1)`. -/
def CAdj (c : ℕ → (Fin d → ℤ)) (L : ℕ) (x y : Fin d → ℤ) : Prop :=
  ∃ k < L, c k = x ∧ c ((k + 1) % L) = y

/-- The invariant of the construction. -/
def Inv (l : CubeLoop d) (T : Finset (Fin d → ℤ)) (L : ℕ) (c : ℕ → (Fin d → ℤ)) : Prop :=
  2 ≤ L ∧ L = l.L + (l.L + 2) * (T.card - 1) ∧ InjOn c (Iio L) ∧
    (∀ k < L, IsUnitStepN (c k) (c ((k + 1) % L))) ∧
    (∀ k < L, Good l T (c k)) ∧ (∀ s ∈ T, ∃ k < L, InCubeInt s (c k)) ∧
    ∀ s ∈ T, ∀ i b, s + faceDir i b ∉ T →
      CAdj c L (tr s (l.A i b)) (tr s (l.B i b)) ∨ CAdj c L (tr s (l.B i b)) (tr s (l.A i b))

variable {l : CubeLoop d}

theorem good_mono {T T' : Finset (Fin d → ℤ)} (h : T ⊆ T') {p : Fin d → ℤ} (hp : Good l T p) :
    Good l T' p := by
  rcases hp with ⟨s, hs, h1⟩ | ⟨s, hs, i, b, hi, h1⟩
  · exact Or.inl ⟨s, h hs, h1⟩
  · exact Or.inr ⟨s, h hs, i, b, h hi, h1⟩

theorem good_not_inCubeInt {T : Finset (Fin d → ℤ)} {ℓ p : Fin d → ℤ} (hℓ : ℓ ∉ T)
    (hp : Good l T p) : ¬ InCubeInt ℓ p := by
  rcases hp with ⟨s, hs, h1⟩ | ⟨s, hs, i, b, hi, h1 | h1⟩
  · intro h2; rw [inCubeInt_unique h1 h2] at hs; exact hℓ hs
  · rw [h1]; exact not_inCubeInt_side (l.A_coord i b)
  · rw [h1]; exact not_inCubeInt_side (l.B_coord i b)

theorem good_ne_side {T : Finset (Fin d → ℤ)} {s p X : Fin d → ℤ} {i : Fin d} {b : Bool}
    (hX0 : InCubeInt 0 X) (hX : X i = if b then 7 else 1) (hℓ : s + faceDir i b ∉ T)
    (hp : Good l T p) : p ≠ tr s X + faceDir i b := by
  rcases hp with ⟨s', _, h1⟩ | ⟨s', hs', j, b', hj, h1⟩
  · rintro rfl; exact not_inCubeInt_side hX h1
  · intro he
    have key : ∀ X', InCubeInt 0 X' → X' j = (if b' then 7 else 1) →
        p = tr s' X' + faceDir j b' → False := by
      intro X' hX0' hX' hp'
      rcases side_eq hX0 hX hX0' hX' (hp'.symm.trans he) with h | h
      · exact hℓ (h ▸ hj)
      · exact hℓ (h ▸ hs')
    rcases h1 with h1 | h1
    · exact key _ (A_int l j b') (l.A_coord j b') h1
    · exact key _ (B_int l j b') (l.B_coord j b') h1

theorem inCube_of_good {T : Finset (Fin d → ℤ)} {p : Fin d → ℤ} (h : Good l T p) :
    ∃ s ∈ T, InCube s p := by
  rcases h with ⟨s, hs, h1⟩ | ⟨s, hs, i, b, _, h1 | h1⟩
  · exact ⟨s, hs, inCube_of_inCubeInt h1⟩
  · exact ⟨s, hs, h1 ▸ inCube_side (A_int l i b) (l.A_coord i b)⟩
  · exact ⟨s, hs, h1 ▸ inCube_side (B_int l i b) (l.B_coord i b)⟩

/-! ### Rotation -/

theorem cadj_rot {c : ℕ → (Fin d → ℤ)} {L : ℕ} (hL : 0 < L) (r : ℕ) {x y : Fin d → ℤ}
    (h : CAdj c L x y) : CAdj (fun j => c ((j + r) % L)) L x y := by
  obtain ⟨k, hk, hx, hy⟩ := h
  obtain ⟨j, hj, hjk⟩ := LCyc.mod_surj hL r k hk
  refine ⟨j, hj, by simp only [hjk, hx], ?_⟩
  simp only [LCyc.mod_succ_add, hjk, hy]

theorem inv_rot {T : Finset (Fin d → ℤ)} {L : ℕ} {c : ℕ → (Fin d → ℤ)} (h : Inv l T L c)
    (r : ℕ) : Inv l T L (fun j => c ((j + r) % L)) := by
  obtain ⟨hL2, hLc, hinj, hstep, hgood, hint, hpair⟩ := h
  have hL : 0 < L := by omega
  refine ⟨hL2, hLc, ?_, ?_, ?_, ?_, ?_⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [mem_Iio] at hj₁ hj₂
    have h1 := hinj (mem_Iio.mpr (Nat.mod_lt (j₁ + r) hL)) (mem_Iio.mpr (Nat.mod_lt (j₂ + r) hL))
      heq
    have h2 : j₁ ≡ j₂ [MOD L] := Nat.ModEq.add_right_cancel' r h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at h2
  · intro k _
    simp only [LCyc.mod_succ_add]
    exact hstep _ (Nat.mod_lt _ hL)
  · intro k _
    exact hgood _ (Nat.mod_lt _ hL)
  · intro s hs
    obtain ⟨k, hk, hks⟩ := hint s hs
    obtain ⟨j, hj, hjk⟩ := LCyc.mod_surj hL r k hk
    exact ⟨j, hj, by simp only [hjk, hks]⟩
  · intro s hs i b hi
    rcases hpair s hs i b hi with h | h
    · exact Or.inl (cadj_rot hL r h)
    · exact Or.inr (cadj_rot hL r h)

/-! ### The splice -/

/-- The closed path with the detour through `ℓ` appended after its last point: `c (L-1) + e`, the
opened loop `q` translated to `ℓ`, `c 0 + e`. -/
def splice (c : ℕ → (Fin d → ℤ)) (L : ℕ) (ℓ e : Fin d → ℤ) (L₀ : ℕ) (q : ℕ → (Fin d → ℤ))
    (j : ℕ) : Fin d → ℤ :=
  if j < L then c j else if j = L then c (L - 1) + e
  else if j < L + L₀ + 1 then tr ℓ (q (j - L - 1)) else c 0 + e

theorem cadj_splice {c : ℕ → (Fin d → ℤ)} {L : ℕ} (hL : 0 < L) (ℓ e : Fin d → ℤ) (L₀ : ℕ)
    (q : ℕ → (Fin d → ℤ)) {u v : Fin d → ℤ} (h : CAdj c L u v)
    (hne : c (L - 1) = u → c 0 = v → False) :
    CAdj (splice c L ℓ e L₀ q) (L + L₀ + 2) u v := by
  obtain ⟨k, hk, hu, hv⟩ := h
  by_cases hk1 : k + 1 < L
  · refine ⟨k, by omega, by simp [splice, hk, hu], ?_⟩
    rw [Nat.mod_eq_of_lt hk1] at hv
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [splice, hk1, hv]
  · have : k = L - 1 := by omega
    subst this
    rw [show L - 1 + 1 = L by omega, Nat.mod_self] at hv
    exact (hne hu hv).elim

theorem inv_splice {T : Finset (Fin d → ℤ)} {L : ℕ} {c : ℕ → (Fin d → ℤ)} (h : Inv l T L c)
    {s : Fin d → ℤ} (hs : s ∈ T) {i : Fin d} {b : Bool} (hℓ : s + faceDir i b ∉ T)
    {X Y : Fin d → ℤ} (hXY : X = l.A i b ∧ Y = l.B i b ∨ X = l.B i b ∧ Y = l.A i b)
    (hx : c (L - 1) = tr s X) (hy : c 0 = tr s Y) {q : ℕ → (Fin d → ℤ)} {U V : Fin d → ℤ}
    (hq : IsOpenedLoop l i (!b) q U V)
    (hU : tr (s + faceDir i b) U = tr s X + faceDir i b + faceDir i b)
    (hV : tr (s + faceDir i b) V = tr s Y + faceDir i b + faceDir i b) :
    Inv l (insert (s + faceDir i b) T) (L + l.L + 2)
      (splice c L (s + faceDir i b) (faceDir i b) l.L q) := by
  obtain ⟨hL2, hLc, hinj, hstep, hgood, hint, hpair⟩ := h
  obtain ⟨hq0, hqL, hqinj, hqstep, hqmem, hqedge⟩ := hq
  set e := faceDir i b with he
  set ℓ := s + e with hℓdef
  set S := splice c L ℓ e l.L q with hS
  have hL : 0 < L := by omega
  have hL0 := l.two_le
  have hX0 : InCubeInt 0 X := by rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [A_int l i b, B_int l i b]
  have hY0 : InCubeInt 0 Y := by rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [B_int l i b, A_int l i b]
  have hXc : X i = if b then 7 else 1 := by
    rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [l.A_coord i b, l.B_coord i b]
  have hYc : Y i = if b then 7 else 1 := by
    rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [l.B_coord i b, l.A_coord i b]
  have hXYne : X ≠ Y := by
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [l.AB_ne i b, (l.AB_ne i b).symm]
  have hC : ∀ k < L, S k = c k := fun k hk => by simp [hS, splice, hk]
  have hD0 : S L = tr s X + e := by simp [hS, splice, hx]
  have hDq : ∀ k < l.L, S (L + 1 + k) = tr ℓ (q k) := fun k hk => by
    rw [hS, splice, if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show L + 1 + k - L - 1 = k by omega]
  have hDl : S (L + l.L + 1) = tr s Y + e := by
    rw [hS, splice, if_neg (by omega), if_neg (by omega), if_neg (by omega), hy]
  have hqint : ∀ k < l.L, InCubeInt ℓ (tr ℓ (q k)) := fun k hk => (inCubeInt_tr ℓ _).mpr (hqmem k hk)
  -- classification of the detour points
  have hdet : ∀ j, L ≤ j → j < L + l.L + 2 →
      (j = L ∧ S j = tr s X + e) ∨ (j = L + l.L + 1 ∧ S j = tr s Y + e) ∨
        ∃ k < l.L, j = L + 1 + k ∧ S j = tr ℓ (q k) := by
    intro j hj1 hj2
    by_cases c1 : j = L
    · exact Or.inl ⟨c1, c1 ▸ hD0⟩
    by_cases c2 : j = L + l.L + 1
    · exact Or.inr (Or.inl ⟨c2, c2 ▸ hDl⟩)
    · obtain ⟨k, rfl⟩ : ∃ k, j = L + 1 + k := ⟨j - L - 1, by omega⟩
      exact Or.inr (Or.inr ⟨k, by omega, rfl, hDq k (by omega)⟩)
  have hgoodS : ∀ j, L ≤ j → j < L + l.L + 2 → Good l (insert ℓ T) (S j) := by
    intro j hj1 hj2
    rcases hdet j hj1 hj2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨k, hk, -, h⟩ <;> rw [h]
    · rcases hXY with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, b, Finset.mem_insert_self _ _, Or.inl rfl⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, b, Finset.mem_insert_self _ _, Or.inr rfl⟩
    · rcases hXY with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, b, Finset.mem_insert_self _ _, Or.inr rfl⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, b, Finset.mem_insert_self _ _, Or.inl rfl⟩
    · exact Or.inl ⟨ℓ, Finset.mem_insert_self _ _, hqint k hk⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    rw [Finset.card_insert_of_notMem hℓ, hLc]
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by
      have := Finset.card_pos.mpr ⟨s, hs⟩; omega⟩
    rw [hm]; simp only [add_tsub_cancel_right]; ring
  · -- injectivity
    have hmix : ∀ a j, a < L → L ≤ j → j < L + l.L + 2 → S a ≠ S j := by
      intro a j ha hj1 hj2 heq
      rw [hC a ha] at heq
      have hg := hgood a ha
      rcases hdet j hj1 hj2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨k, hk, -, h⟩ <;> rw [h] at heq
      · exact good_ne_side hX0 hXc hℓ hg heq
      · exact good_ne_side hY0 hYc hℓ hg heq
      · exact good_not_inCubeInt hℓ hg (heq ▸ hqint k hk)
    intro j₁ hj₁ j₂ hj₂ heq
    simp only [mem_Iio] at hj₁ hj₂
    by_cases h1 : j₁ < L <;> by_cases h2 : j₂ < L
    · rw [hC _ h1, hC _ h2] at heq
      exact hinj (mem_Iio.mpr h1) (mem_Iio.mpr h2) heq
    · exact (hmix _ _ h1 (by omega) hj₂ heq).elim
    · exact (hmix _ _ h2 (by omega) hj₁ heq.symm).elim
    · have side_ne_q : ∀ (Z : Fin d → ℤ), Z i = (if b then 7 else 1) → ∀ k < l.L,
          tr s Z + e ≠ tr ℓ (q k) := by
        intro Z hZ k hk he'
        exact not_inCubeInt_side hZ (he' ▸ hqint k hk)
      rcases hdet j₁ (by omega) hj₁ with ⟨r1, e1⟩ | ⟨r1, e1⟩ | ⟨k1, hk1, r1, e1⟩ <;>
      rcases hdet j₂ (by omega) hj₂ with ⟨r2, e2⟩ | ⟨r2, e2⟩ | ⟨k2, hk2, r2, e2⟩ <;>
      rw [e1, e2] at heq
      · omega
      · exact absurd (tr_injective s (add_right_cancel heq)) hXYne
      · exact absurd heq (side_ne_q X hXc k2 hk2)
      · exact absurd (tr_injective s (add_right_cancel heq)).symm hXYne
      · omega
      · exact absurd heq (side_ne_q Y hYc k2 hk2)
      · exact absurd heq.symm (side_ne_q X hXc k1 hk1)
      · exact absurd heq.symm (side_ne_q Y hYc k1 hk1)
      · have := hqinj (mem_Iio.mpr hk1) (mem_Iio.mpr hk2) (tr_injective ℓ heq)
        omega
  · -- steps
    intro k hk
    by_cases hk1 : k + 1 < L
    · rw [Nat.mod_eq_of_lt (by omega), hC _ (by omega), hC _ hk1]
      have := hstep k (by omega)
      rwa [Nat.mod_eq_of_lt hk1] at this
    by_cases hk2 : k + 1 = L
    · rw [Nat.mod_eq_of_lt (by omega), hC _ (by omega), hk2, hD0, show k = L - 1 by omega, hx]
      exact isUnitStepN_faceDir _ _ _
    by_cases hk3 : k = L
    · subst hk3
      rw [Nat.mod_eq_of_lt (by omega), hD0, show k + 1 = k + 1 + 0 by rfl, hDq 0 (by omega), hq0,
        hU]
      exact isUnitStepN_faceDir _ _ _
    by_cases hk4 : k + 1 < L + l.L + 1
    · obtain ⟨a, rfl⟩ : ∃ a, k = L + 1 + a := ⟨k - L - 1, by omega⟩
      rw [Nat.mod_eq_of_lt (by omega), show L + 1 + a + 1 = L + 1 + (a + 1) by ring,
        hDq a (by omega), hDq (a + 1) (by omega), isUnitStepN_tr]
      exact hqstep a (by omega)
    by_cases hk5 : k = L + l.L
    · subst hk5
      rw [Nat.mod_eq_of_lt (by omega), hDl, show L + l.L = L + 1 + (l.L - 1) by omega,
        hDq _ (by omega), hqL, hV]
      exact isUnitStepN_faceDir' _ _ _
    · have hk6 : k = L + l.L + 1 := by omega
      subst hk6
      rw [show L + l.L + 1 + 1 = L + l.L + 2 by ring, Nat.mod_self, hC 0 hL, hDl, hy]
      exact isUnitStepN_faceDir' _ _ _
  · -- good points
    intro k hk
    by_cases hk1 : k < L
    · rw [hC _ hk1]; exact good_mono (Finset.subset_insert _ _) (hgood k hk1)
    · exact hgoodS k (by omega) hk
  · -- every cube has a depth-1 point
    intro s₂ hs₂
    rcases Finset.mem_insert.mp hs₂ with rfl | hs₂
    · exact ⟨L + 1 + 0, by omega, by rw [hDq 0 (by omega)]; exact hqint 0 (by omega)⟩
    · obtain ⟨k, hk, hks⟩ := hint s₂ hs₂
      exact ⟨k, by omega, by rw [hC k hk]; exact hks⟩
  · -- free faces
    intro s₂ hs₂ j b₂ hfree
    rcases Finset.mem_insert.mp hs₂ with rfl | hs₂
    · have hj : (j, b₂) ≠ (i, !b) := by
        intro hjb
        simp only [Prod.mk.injEq] at hjb
        obtain ⟨rfl, rfl⟩ := hjb
        apply hfree
        rw [hℓdef, he, faceDir_opp]
        exact Finset.mem_insert_of_mem hs
      obtain ⟨k, hk, hk'⟩ := hqedge j b₂ hj
      have hadj : ∀ u v, q k = u → q (k + 1) = v → CAdj S (L + l.L + 2) (tr ℓ u) (tr ℓ v) := by
        intro u v hu hv
        refine ⟨L + 1 + k, by omega, by rw [hDq k (by omega), hu], ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), show L + 1 + k + 1 = L + 1 + (k + 1) by ring,
          hDq _ hk, hv]
      rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hadj _ _ h1 h2)
      · exact Or.inr (hadj _ _ h1 h2)
    · have hfree' : s₂ + faceDir j b₂ ∉ T := fun h => hfree (Finset.mem_insert_of_mem h)
      have hne : s₂ + faceDir j b₂ ≠ ℓ := fun h => hfree (h ▸ Finset.mem_insert_self _ _)
      have key : ∀ u v, ((u = tr s₂ (l.A j b₂) ∧ v = tr s₂ (l.B j b₂)) ∨
          (u = tr s₂ (l.B j b₂) ∧ v = tr s₂ (l.A j b₂))) →
          CAdj c L u v → CAdj S (L + l.L + 2) u v := by
        intro u v huv h
        refine cadj_splice hL ℓ e l.L q h fun hu hv => ?_
        rw [hx] at hu
        rw [hy] at hv
        have := pair_eq l (s := s) (s' := s₂) (i := i) (j := j) (b := b) (b' := b₂) (by
          rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all)
        apply hne
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2.1, this.2.2]
      rcases hpair s₂ hs₂ j b₂ hfree' with h | h
      · exact Or.inl (key _ _ (Or.inl ⟨rfl, rfl⟩) h)
      · exact Or.inr (key _ _ (Or.inr ⟨rfl, rfl⟩) h)

/-! ### Base case and induction -/

theorem inv_base (l : CubeLoop d) (s₁ : Fin d → ℤ) :
    Inv l {s₁} l.L (fun k => tr s₁ (l.c k)) := by
  refine ⟨l.two_le, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    exact l.injOn hj₁ hj₂ (tr_injective s₁ heq)
  · intro k hk
    exact (isUnitStepN_tr _ _ _).mpr (l.step k hk)
  · intro k hk
    exact Or.inl ⟨s₁, Finset.mem_singleton_self _, (inCubeInt_tr _ _).mpr (l.mem k hk)⟩
  · intro s hs
    rw [Finset.mem_singleton.mp hs]
    exact ⟨0, by have := l.two_le; omega, (inCubeInt_tr _ _).mpr (l.mem 0 (by have := l.two_le; omega))⟩
  · intro s hs i b _
    rw [Finset.mem_singleton.mp hs]
    rcases l.edge i b with ⟨k, hk, h1, h2⟩ | ⟨k, hk, h1, h2⟩
    · exact Or.inl ⟨k, hk, by simp only [h1], by simp only [h2]⟩
    · exact Or.inr ⟨k, hk, by simp only [h1], by simp only [h2]⟩

/-- One growth step: splice in a cube adjacent across a free face. -/
theorem inv_grow {T : Finset (Fin d → ℤ)} {L : ℕ} {c : ℕ → (Fin d → ℤ)} (h : Inv l T L c)
    {s : Fin d → ℤ} (hs : s ∈ T) {i : Fin d} {b : Bool} (hℓ : s + faceDir i b ∉ T) :
    ∃ c', Inv l (insert (s + faceDir i b) T) (L + l.L + 2) c' := by
  have hL : 0 < L := by have := h.1; omega
  have hlast : ∀ k < L, (L - 1 + (k + 1)) % L = k := by
    intro k hk
    rw [show L - 1 + (k + 1) = k + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  obtain ⟨⟨qA, hqA⟩, ⟨qB, hqB⟩⟩ := exists_isOpenedLoop l i (!b)
  rcases h.2.2.2.2.2.2 s hs i b hℓ with ⟨k, hk, hx, hy⟩ | ⟨k, hk, hx, hy⟩
  · exact ⟨_, inv_splice (inv_rot h (k + 1)) hs hℓ (Or.inl ⟨rfl, rfl⟩)
      (by simp only [hlast k hk, hx]) (by simp only [zero_add, hy]) hqA
      (A_tr_opp l s i b).symm (B_tr_opp l s i b).symm⟩
  · exact ⟨_, inv_splice (inv_rot h (k + 1)) hs hℓ (Or.inr ⟨rfl, rfl⟩)
      (by simp only [hlast k hk, hx]) (by simp only [zero_add, hy]) hqB
      (B_tr_opp l s i b).symm (A_tr_opp l s i b).symm⟩

theorem exists_inv_sub (l : CubeLoop d) {T : Finset (Fin d → ℤ)} (hc : CubeConnected T) :
    ∀ n, 1 ≤ n → n ≤ T.card → ∃ A ⊆ T, A.card = n ∧ ∃ L c, Inv l A L c := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      exact ⟨{s₁}, by simpa using hs₁, by simp, _, _, inv_base l s₁⟩
    · obtain ⟨A, hAT, hAc, L, c, hinv⟩ := ih hn0 (by omega)
      have hne : A ≠ T := by rintro rfl; omega
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      have : ¬ ∀ s ∈ A, ∀ s' ∈ T, IsUnitStepN s s' → s' ∈ A := fun h => hne (hc A hAT hAne h)
      push_neg at this
      obtain ⟨s, hs, s', hs'T, hstep, hs'A⟩ := this
      obtain ⟨i, b, rfl⟩ := isUnitStepN_iff hstep
      obtain ⟨c', hc'⟩ := inv_grow hinv hs hs'A
      refine ⟨insert (s + faceDir i b) A, Finset.insert_subset hs'T hAT, ?_, _, c', hc'⟩
      rw [Finset.card_insert_of_notMem hs'A, hAc]

theorem exists_inv (l : CubeLoop d) {T : Finset (Fin d → ℤ)} (hT : T.Nonempty)
    (hc : CubeConnected T) : ∃ L c, Inv l T L c := by
  obtain ⟨A, hAT, hAc, L, c, h⟩ := exists_inv_sub l hc T.card (Finset.card_pos.mpr hT) le_rfl
  rw [Finset.eq_of_subset_of_card_le hAT hAc.ge] at h
  exact ⟨L, c, h⟩

end CCyc

/-- The cycle of `CCyc.exists_inv` for a cube loop `l`, with its exact length
`l.L + (l.L + 2) (N - 1)`. -/
theorem exists_latticeCycleN_of_loop {d : ℕ} (l : CubeLoop d) (T : Finset (Fin d → ℤ))
    (hT : T.Nonempty) (hc : CubeConnected T) :
    ∃ (L : ℕ) (c : ℕ → (Fin d → ℤ)), L = l.L + (l.L + 2) * (T.card - 1) ∧ l.L ≤ L ∧
      InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStepN (c i) (c (i + 1))) ∧ IsUnitStepN (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InCube s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InCubeInt s (c i) := by
  obtain ⟨L, c, hL2, hLc, hinj, hstep, hgood, hint, -⟩ := CCyc.exists_inv l hT hc
  refine ⟨L, c, hLc, by rw [hLc]; omega, hinj, fun i hi => ?_, ?_,
    fun i hi => CCyc.inCube_of_good (hgood i hi), hint⟩
  · have := hstep i (by omega)
    rwa [Nat.mod_eq_of_lt hi] at this
  · have := hstep (L - 1) (by omega)
    rwa [show L - 1 + 1 = L by omega, Nat.mod_self] at this

end HPC.Plane
