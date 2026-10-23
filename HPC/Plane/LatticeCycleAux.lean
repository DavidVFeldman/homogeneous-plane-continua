import HPC.Plane.Band

/-!
# Batch 110: the self-avoiding lattice cycle through a connected set of squares

Combinatorial half of `HPC/Plane/LatticeCycle.lean` (split off, see the report). The definitions
`PolyConnected`, `InSq`, `InSqInt` of the skeleton live here.

**Construction (invariant changed from the skeleton, recorded in the report).** Square `s` is
`[8 s.1, 8 s.1 + 8] × [8 s.2, 8 s.2 + 8]` in fine coordinates; its depth-1 points have both
coordinates strictly inside. For a side `i` of `s` (outward direction `dvec i`) the *middle pair*
`pA s i`, `pB s i` are the depth-1 points of the row along that side at offsets `4` and `3`.
Invariant (`LCyc.Inv`) for the current set `T` and closed path `c 0, …, c (L-1)`:
* `L = 26 |T| - 2`, the points are distinct and consecutive points (cyclically) a unit step apart;
* (b) every point is a depth-1 point of a square of `T`, or `pA s i + dvec i`, `pB s i + dvec i`
  (the two middle points of a side) for a side shared by two squares of `T`;
* (c') every square of `T` has a depth-1 point on the cycle;
* (a') for every square `s ∈ T` and every side `i` not shared within `T`, the middle pair
  `pA s i, pB s i` is an edge of the cycle (in one direction or the other).
Step: for a new square `ℓ = s + dvec i` across the free side `i` of `s`, rotate the cycle so the
edge `x → y` of the middle pair is the closing edge, and append the 26-point detour
`x + dvec i`, the depth-1 loop of `ℓ` traversed the long way from `x + 2 dvec i` to
`y + 2 dvec i`, `y + dvec i`. The local facts about the detour (eight cases: four sides, two
orientations) and the base loop are checked by `decide` in the coordinates of square `0`.
-/

namespace HPC.Plane

open Set

/-- A finite set of squares is **connected** (edge-adjacency: indices a unit step apart). -/
def PolyConnected (T : Finset (ℤ × ℤ)) : Prop :=
  ∀ A : Finset (ℤ × ℤ), A ⊆ T → A.Nonempty →
    (∀ s ∈ A, ∀ s' ∈ T, IsUnitStep s s' → s' ∈ A) → A = T

/-- The fine lattice point `p` lies in the closed square `s` (fine coordinates, mesh `1/8`). -/
def InSq (s p : ℤ × ℤ) : Prop :=
  8 * s.1 ≤ p.1 ∧ p.1 ≤ 8 * s.1 + 8 ∧ 8 * s.2 ≤ p.2 ∧ p.2 ≤ 8 * s.2 + 8

/-- The fine lattice point `p` is a depth-1 point of the square `s` (strictly inside). -/
def InSqInt (s p : ℤ × ℤ) : Prop :=
  8 * s.1 < p.1 ∧ p.1 < 8 * s.1 + 8 ∧ 8 * s.2 < p.2 ∧ p.2 < 8 * s.2 + 8

namespace LCyc

instance (p q : ℤ × ℤ) : Decidable (IsUnitStep p q) := by unfold IsUnitStep; infer_instance
instance (s p : ℤ × ℤ) : Decidable (InSqInt s p) := by unfold InSqInt; infer_instance

/-- The four unit directions. -/
def dvec : Fin 4 → ℤ × ℤ := ![(1, 0), (0, 1), (-1, 0), (0, -1)]

/-- The two middle depth-1 points (offsets `4` and `3`) of square `s` along its side `i`. -/
def pA (s : ℤ × ℤ) (i : Fin 4) : ℤ × ℤ := (8 * s.1 + 4 + 3 * (dvec i).1, 8 * s.2 + 4 + 3 * (dvec i).2)
def pB (s : ℤ × ℤ) (i : Fin 4) : ℤ × ℤ :=
  ((pA s i).1 - |(dvec i).2|, (pA s i).2 - |(dvec i).1|)

/-- The depth-1 loop of square `0`: the boundary of `[1,7]²`, counterclockwise. -/
def loop0 : List (ℤ × ℤ) :=
  ((List.range 7).map fun k => ((k : ℤ) + 1, 1)) ++ ((List.range 6).map fun k => (7, (k : ℤ) + 2)) ++
  ((List.range 6).map fun k => (6 - (k : ℤ), 7)) ++ ((List.range 5).map fun k => (1, 6 - (k : ℤ)))

/-- Translation by the square `s`. -/
def tr (s p : ℤ × ℤ) : ℤ × ℤ := (8 * s.1 + p.1, 8 * s.2 + p.2)

/-- The loop `l` traversed the long way from `a` to its neighbour `b`. -/
def longPath (l : List (ℤ × ℤ)) (a b : ℤ × ℤ) : List (ℤ × ℤ) :=
  let r := l.rotate (l.idxOf a)
  if r.getLast? = some b then r else a :: r.tail.reverse

/-- The orientation-dependent ends of the edge to be spliced. -/
def ex (i : Fin 4) (o : Bool) : ℤ × ℤ := if o then pB 0 i else pA 0 i
def ey (i : Fin 4) (o : Bool) : ℤ × ℤ := if o then pA 0 i else pB 0 i

/-- The local detour (square `0`, neighbour `dvec i`): 26 points. -/
def Dloc (i : Fin 4) (o : Bool) : List (ℤ × ℤ) :=
  [ex i o + dvec i] ++ longPath (loop0.map (tr (dvec i))) (ex i o + dvec i + dvec i)
    (ey i o + dvec i + dvec i) ++ [ey i o + dvec i]

def Dfun (i : Fin 4) (o : Bool) (k : ℕ) : ℤ × ℤ := (Dloc i o).getD k 0
def Lfun (k : ℕ) : ℤ × ℤ := loop0.getD k 0

set_option maxRecDepth 100000

theorem D_step : ∀ i : Fin 4, ∀ o : Bool, ∀ k : Fin 25,
    IsUnitStep (Dfun i o k) (Dfun i o (k + 1)) := by decide
theorem D_inj : ∀ i : Fin 4, ∀ o : Bool, ∀ k₁ k₂ : Fin 26,
    Dfun i o k₁ = Dfun i o k₂ → k₁ = k₂ := by decide
theorem D_mem : ∀ i : Fin 4, ∀ o : Bool, ∀ k : Fin 26,
    InSqInt (dvec i) (Dfun i o k) ∨ Dfun i o k = ex i o + dvec i ∨ Dfun i o k = ey i o + dvec i := by
  decide
theorem D_zero : ∀ i : Fin 4, ∀ o : Bool, Dfun i o 0 = ex i o + dvec i := by decide
theorem D_last : ∀ i : Fin 4, ∀ o : Bool, Dfun i o 25 = ey i o + dvec i := by decide
theorem D_one : ∀ i : Fin 4, ∀ o : Bool, InSqInt (dvec i) (Dfun i o 1) := by decide
theorem D_pair : ∀ i : Fin 4, ∀ o : Bool, ∀ j : Fin 4, j ≠ i + 2 → ∃ k : Fin 25,
    (Dfun i o k = pA (dvec i) j ∧ Dfun i o (k + 1) = pB (dvec i) j) ∨
    (Dfun i o k = pB (dvec i) j ∧ Dfun i o (k + 1) = pA (dvec i) j) := by decide
theorem L_step : ∀ k : Fin 24, IsUnitStep (Lfun k) (Lfun ((k + 1) % 24)) := by decide
theorem L_inj : ∀ k₁ k₂ : Fin 24, Lfun k₁ = Lfun k₂ → k₁ = k₂ := by decide
theorem L_mem : ∀ k : Fin 24, InSqInt 0 (Lfun k) := by decide
theorem L_pair : ∀ j : Fin 4, ∃ k : Fin 24,
    (Lfun k = pA 0 j ∧ Lfun ((k + 1) % 24) = pB 0 j) ∨
    (Lfun k = pB 0 j ∧ Lfun ((k + 1) % 24) = pA 0 j) := by decide
theorem dvec_opp : ∀ i : Fin 4, dvec (i + 2) = -dvec i := by decide


/-! ### Translation and arithmetic -/

theorem isUnitStep_tr (s p q : ℤ × ℤ) : IsUnitStep (tr s p) (tr s q) ↔ IsUnitStep p q := by
  unfold IsUnitStep tr; simp only [add_sub_add_left_eq_sub]

theorem inSqInt_tr (s t p : ℤ × ℤ) : InSqInt (s + t) (tr s p) ↔ InSqInt t p := by
  unfold InSqInt tr; simp only [Prod.fst_add, Prod.snd_add]; constructor <;> intro h <;> omega

theorem tr_injective (s : ℤ × ℤ) : Function.Injective (tr s) := by
  intro p q h; simp only [tr, Prod.mk.injEq] at h; ext <;> omega

theorem pA_tr (s t : ℤ × ℤ) (j : Fin 4) : pA (s + t) j = tr s (pA t j) := by
  simp only [pA, tr, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]; constructor <;> ring

theorem pB_tr (s t : ℤ × ℤ) (j : Fin 4) : pB (s + t) j = tr s (pB t j) := by
  simp only [pB, pA, tr, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]; constructor <;> ring

theorem tr_add (s p q : ℤ × ℤ) : tr s (p + q) = tr s p + q := by
  ext <;> simp [tr] <;> ring

theorem ex_tr (s : ℤ × ℤ) (i : Fin 4) (o : Bool) :
    tr s (ex i o) = if o then pB s i else pA s i := by
  have h1 := pA_tr s 0 i; have h2 := pB_tr s 0 i
  rw [add_zero] at h1 h2
  cases o <;> simp [ex, h1, h2]

theorem ey_tr (s : ℤ × ℤ) (i : Fin 4) (o : Bool) :
    tr s (ey i o) = if o then pA s i else pB s i := by
  have h1 := pA_tr s 0 i; have h2 := pB_tr s 0 i
  rw [add_zero] at h1 h2
  cases o <;> simp [ey, h1, h2]

theorem isUnitStep_dvec (p : ℤ × ℤ) (i : Fin 4) : IsUnitStep p (p + dvec i) := by
  unfold IsUnitStep; fin_cases i <;> simp [dvec]

theorem isUnitStep_dvec' (p : ℤ × ℤ) (i : Fin 4) : IsUnitStep (p + dvec i) p := by
  unfold IsUnitStep; fin_cases i <;> simp [dvec]

theorem isUnitStep_iff (p q : ℤ × ℤ) : IsUnitStep p q ↔ ∃ i, q = p + dvec i := by
  constructor
  · intro h
    unfold IsUnitStep at h
    rcases abs_cases (q.1 - p.1) with h1 | h1 <;> rcases abs_cases (q.2 - p.2) with h2 | h2
    · by_cases hq : q.1 - p.1 = 0
      · exact ⟨1, by ext <;> simp [dvec] <;> omega⟩
      · exact ⟨0, by ext <;> simp [dvec] <;> omega⟩
    · by_cases hq : q.1 - p.1 = 0
      · exact ⟨3, by ext <;> simp [dvec] <;> omega⟩
      · exact ⟨0, by ext <;> simp [dvec] <;> omega⟩
    · by_cases hq : q.2 - p.2 = 0
      · exact ⟨2, by ext <;> simp [dvec] <;> omega⟩
      · exact ⟨1, by ext <;> simp [dvec] <;> omega⟩
    · exfalso; omega
  · rintro ⟨i, rfl⟩; exact isUnitStep_dvec p i

theorem inSqInt_unique {s t p : ℤ × ℤ} (h1 : InSqInt s p) (h2 : InSqInt t p) : s = t := by
  unfold InSqInt at h1 h2; ext <;> omega

/-- Side points are not depth-1 points. -/
theorem not_inSqInt_side (s t : ℤ × ℤ) (j : Fin 4) :
    ¬ InSqInt t (pA s j + dvec j) ∧ ¬ InSqInt t (pB s j + dvec j) := by
  unfold InSqInt; fin_cases j <;> simp [pA, pB, dvec] <;> omega

/-- A side point determines its side. -/
theorem side_eq {s s' : ℤ × ℤ} {i j : Fin 4}
    (h : pA s' j + dvec j = pA s i + dvec i ∨ pA s' j + dvec j = pB s i + dvec i ∨
      pB s' j + dvec j = pA s i + dvec i ∨ pB s' j + dvec j = pB s i + dvec i) :
    s' + dvec j = s + dvec i ∨ s' = s + dvec i := by
  simp only [Prod.ext_iff] at h ⊢
  fin_cases i <;> fin_cases j <;> simp [pA, pB, dvec] at h ⊢ <;> omega

/-- The middle pair determines the square and side. -/
theorem pair_eq {s s' : ℤ × ℤ} {i j : Fin 4}
    (h : (pA s' j = pA s i ∧ pB s' j = pB s i) ∨ (pA s' j = pB s i ∧ pB s' j = pA s i)) :
    s' = s ∧ j = i := by
  simp only [Prod.ext_iff] at h ⊢
  fin_cases i <;> fin_cases j <;> simp [pA, pB, dvec] at h ⊢
  all_goals omega

theorem inSq_of_inSqInt {s p : ℤ × ℤ} (h : InSqInt s p) : InSq s p := by
  unfold InSqInt at h; unfold InSq; omega

theorem inSq_side (s : ℤ × ℤ) (j : Fin 4) : InSq s (pA s j + dvec j) ∧ InSq s (pB s j + dvec j) := by
  unfold InSq; fin_cases j <;> simp [pA, pB, dvec] <;> omega


/-! ### The cycle invariant -/

/-- Admissible cycle points for the set `T`: depth-1 points of a square of `T`, or the two middle
points of a side shared by two squares of `T`. -/
def Good (T : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : Prop :=
  (∃ s ∈ T, InSqInt s p) ∨
    ∃ s ∈ T, ∃ i : Fin 4, s + dvec i ∈ T ∧ (p = pA s i + dvec i ∨ p = pB s i + dvec i)

/-- `x → y` is an edge of the closed path `c 0, …, c (L-1)`. -/
def CAdj (c : ℕ → ℤ × ℤ) (L : ℕ) (x y : ℤ × ℤ) : Prop :=
  ∃ k < L, c k = x ∧ c ((k + 1) % L) = y

/-- The invariant of the construction. -/
def Inv (T : Finset (ℤ × ℤ)) (L : ℕ) (c : ℕ → ℤ × ℤ) : Prop :=
  2 ≤ L ∧ L = 26 * T.card - 2 ∧ InjOn c (Iio L) ∧
    (∀ k < L, IsUnitStep (c k) (c ((k + 1) % L))) ∧
    (∀ k < L, Good T (c k)) ∧ (∀ s ∈ T, ∃ k < L, InSqInt s (c k)) ∧
    ∀ s ∈ T, ∀ i : Fin 4, s + dvec i ∉ T →
      CAdj c L (pA s i) (pB s i) ∨ CAdj c L (pB s i) (pA s i)

theorem good_mono {T T' : Finset (ℤ × ℤ)} (h : T ⊆ T') {p : ℤ × ℤ} (hp : Good T p) :
    Good T' p := by
  rcases hp with ⟨s, hs, h1⟩ | ⟨s, hs, i, hi, h1⟩
  · exact Or.inl ⟨s, h hs, h1⟩
  · exact Or.inr ⟨s, h hs, i, h hi, h1⟩

theorem good_not_inSqInt {T : Finset (ℤ × ℤ)} {ℓ p : ℤ × ℤ} (hℓ : ℓ ∉ T) (hp : Good T p) :
    ¬ InSqInt ℓ p := by
  rcases hp with ⟨s, hs, h1⟩ | ⟨s, hs, i, hi, h1 | h1⟩
  · intro h2; rw [inSqInt_unique h1 h2] at hs; exact hℓ hs
  · rw [h1]; exact (not_inSqInt_side s ℓ i).1
  · rw [h1]; exact (not_inSqInt_side s ℓ i).2

theorem good_ne_side {T : Finset (ℤ × ℤ)} {s p : ℤ × ℤ} {i : Fin 4} (hℓ : s + dvec i ∉ T)
    (hp : Good T p) : p ≠ pA s i + dvec i ∧ p ≠ pB s i + dvec i := by
  rcases hp with ⟨s', _, h1⟩ | ⟨s', hs', j, hj, h1⟩
  · constructor <;> rintro rfl
    · exact (not_inSqInt_side s s' i).1 h1
    · exact (not_inSqInt_side s s' i).2 h1
  · have key : ∀ q, (q = pA s i + dvec i ∨ q = pB s i + dvec i) →
        (q = pA s' j + dvec j ∨ q = pB s' j + dvec j) → False := by
      intro q hq hq'
      have := side_eq (s := s) (s' := s') (i := i) (j := j) (by
        rcases hq with rfl | rfl <;> rcases hq' with h | h <;> simp [h])
      rcases this with h | h
      · exact hℓ (h ▸ hj)
      · exact hℓ (h ▸ hs')
    exact ⟨fun h => key p (Or.inl h) h1, fun h => key p (Or.inr h) h1⟩

/-! ### Rotation -/

/-- The closed path rotated by `r`. -/
def rot (c : ℕ → ℤ × ℤ) (L r : ℕ) (j : ℕ) : ℤ × ℤ := c ((j + r) % L)

theorem mod_surj {L : ℕ} (hL : 0 < L) (r k : ℕ) (hk : k < L) : ∃ j < L, (j + r) % L = k := by
  refine ⟨(k + (L - r % L)) % L, Nat.mod_lt _ hL, ?_⟩
  have h1 := Nat.mod_add_div r L
  have h2 := Nat.mod_lt r hL
  rw [Nat.mod_add_mod]
  have : k + (L - r % L) + r = k + L * (r / L + 1) := by
    rw [mul_add, mul_one]
    generalize r % L = m at h1 h2 ⊢
    generalize L * (r / L) = Q at h1 ⊢
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem mod_succ_add (L r j : ℕ) : ((j + 1) % L + r) % L = ((j + r) % L + 1) % L := by
  rw [Nat.mod_add_mod, Nat.mod_add_mod, show j + 1 + r = j + r + 1 by omega]

theorem cadj_rot {c : ℕ → ℤ × ℤ} {L : ℕ} (hL : 0 < L) (r : ℕ) {x y : ℤ × ℤ}
    (h : CAdj c L x y) : CAdj (rot c L r) L x y := by
  obtain ⟨k, hk, hx, hy⟩ := h
  obtain ⟨j, hj, hjk⟩ := mod_surj hL r k hk
  refine ⟨j, hj, by simp only [rot, hjk, hx], ?_⟩
  simp only [rot, mod_succ_add, hjk, hy]

theorem inv_rot {T : Finset (ℤ × ℤ)} {L : ℕ} {c : ℕ → ℤ × ℤ} (h : Inv T L c) (r : ℕ) :
    Inv T L (rot c L r) := by
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
    simp only [rot, mod_succ_add]
    exact hstep _ (Nat.mod_lt _ hL)
  · intro k _
    exact hgood _ (Nat.mod_lt _ hL)
  · intro s hs
    obtain ⟨k, hk, hks⟩ := hint s hs
    obtain ⟨j, hj, hjk⟩ := mod_surj hL r k hk
    exact ⟨j, hj, by simp only [rot, hjk, hks]⟩
  · intro s hs i hi
    rcases hpair s hs i hi with h | h
    · exact Or.inl (cadj_rot hL r h)
    · exact Or.inr (cadj_rot hL r h)


/-! ### The splice -/

/-- The closed path with the detour through `s + dvec i` appended after its last point. -/
def splice (c : ℕ → ℤ × ℤ) (L : ℕ) (s : ℤ × ℤ) (i : Fin 4) (o : Bool) (j : ℕ) : ℤ × ℤ :=
  if j < L then c j else tr s (Dfun i o (j - L))

theorem D_mem_tr (s : ℤ × ℤ) (i : Fin 4) (o : Bool) {k : ℕ} (hk : k < 26) :
    InSqInt (s + dvec i) (tr s (Dfun i o k)) ∨ tr s (Dfun i o k) = pA s i + dvec i ∨
      tr s (Dfun i o k) = pB s i + dvec i := by
  rcases D_mem i o ⟨k, hk⟩ with h | h | h
  · exact Or.inl ((inSqInt_tr s _ _).mpr h)
  · simp only at h
    rw [h, tr_add, ex_tr]
    cases o <;> simp
  · simp only at h
    rw [h, tr_add, ey_tr]
    cases o <;> simp

theorem cadj_splice {c : ℕ → ℤ × ℤ} {L : ℕ} (hL : 0 < L) (s : ℤ × ℤ) (i : Fin 4) (o : Bool)
    {u v : ℤ × ℤ} (h : CAdj c L u v) (hne : c (L - 1) = u → c 0 = v → False) :
    CAdj (splice c L s i o) (L + 26) u v := by
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

theorem inv_splice {T : Finset (ℤ × ℤ)} {L : ℕ} {c : ℕ → ℤ × ℤ} (h : Inv T L c) {s : ℤ × ℤ}
    (hs : s ∈ T) {i : Fin 4} (hℓ : s + dvec i ∉ T) (o : Bool)
    (hx : c (L - 1) = tr s (ex i o)) (hy : c 0 = tr s (ey i o)) :
    Inv (insert (s + dvec i) T) (L + 26) (splice c L s i o) := by
  obtain ⟨hL2, hLc, hinj, hstep, hgood, hint, hpair⟩ := h
  have hL : 0 < L := by omega
  have hC : ∀ k < L, splice c L s i o k = c k := fun k hk => by simp [splice, hk]
  have hD : ∀ k, splice c L s i o (L + k) = tr s (Dfun i o k) := fun k => by simp [splice]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hℓ]; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [mem_Iio] at hj₁ hj₂
    have hmix : ∀ a b, a < L → L ≤ b → b < L + 26 → splice c L s i o a ≠ splice c L s i o b := by
      intro a b ha hb hb' he
      obtain ⟨b', rfl⟩ : ∃ b', b = L + b' := ⟨b - L, by omega⟩
      rw [hC a ha, hD] at he
      have hg := hgood a ha
      rcases D_mem_tr s i o (show b' < 26 by omega) with h | h | h
      · exact good_not_inSqInt hℓ hg (he ▸ h)
      · exact (good_ne_side hℓ hg).1 (he.trans h)
      · exact (good_ne_side hℓ hg).2 (he.trans h)
    by_cases h1 : j₁ < L <;> by_cases h2 : j₂ < L
    · rw [hC _ h1, hC _ h2] at heq
      exact hinj (mem_Iio.mpr h1) (mem_Iio.mpr h2) heq
    · exact (hmix _ _ h1 (by omega) hj₂ heq).elim
    · exact (hmix _ _ h2 (by omega) hj₁ heq.symm).elim
    · obtain ⟨a, rfl⟩ : ∃ a, j₁ = L + a := ⟨j₁ - L, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, j₂ = L + b := ⟨j₂ - L, by omega⟩
      rw [hD, hD] at heq
      have := D_inj i o ⟨a, by omega⟩ ⟨b, by omega⟩ (tr_injective s heq)
      simp only [Fin.mk.injEq] at this
      omega
  · intro k hk
    by_cases hk1 : k + 1 < L
    · rw [Nat.mod_eq_of_lt (by omega), hC _ (by omega), hC _ hk1]
      have := hstep k (by omega)
      rwa [Nat.mod_eq_of_lt hk1] at this
    by_cases hk2 : k + 1 = L
    · have h0 := hD 0
      rw [add_zero] at h0
      rw [Nat.mod_eq_of_lt (by omega), hC _ (by omega), hk2, h0, show k = L - 1 by omega, hx]
      have := D_zero i o
      simp only at this
      rw [this, tr_add]
      exact isUnitStep_dvec _ _
    by_cases hk3 : k + 1 < L + 26
    · obtain ⟨a, rfl⟩ : ∃ a, k = L + a := ⟨k - L, by omega⟩
      rw [Nat.mod_eq_of_lt hk3, show L + a + 1 = L + (a + 1) by ring, hD, hD,
        isUnitStep_tr]
      exact D_step i o ⟨a, by omega⟩
    · have hk4 : k = L + 25 := by omega
      subst hk4
      rw [show L + 25 + 1 = L + 26 by ring, Nat.mod_self, hC 0 hL, hD, hy]
      have := D_last i o
      simp only at this
      rw [this, tr_add]
      exact isUnitStep_dvec' _ _
  · intro k hk
    by_cases hk1 : k < L
    · rw [hC _ hk1]; exact good_mono (Finset.subset_insert _ _) (hgood k hk1)
    · obtain ⟨a, rfl⟩ : ∃ a, k = L + a := ⟨k - L, by omega⟩
      rw [hD]
      rcases D_mem_tr s i o (show a < 26 by omega) with h | h | h
      · exact Or.inl ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, Finset.mem_insert_self _ _, Or.inl h⟩
      · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, i, Finset.mem_insert_self _ _, Or.inr h⟩
  · intro s₂ hs₂
    rcases Finset.mem_insert.mp hs₂ with rfl | hs₂
    · exact ⟨L + 1, by omega, by rw [hD]; exact (inSqInt_tr s _ _).mpr (D_one i o)⟩
    · obtain ⟨k, hk, hks⟩ := hint s₂ hs₂
      exact ⟨k, by omega, by rw [hC k hk]; exact hks⟩
  · intro s₂ hs₂ j hfree
    rcases Finset.mem_insert.mp hs₂ with rfl | hs₂
    · have hj : j ≠ i + 2 := by
        rintro rfl
        apply hfree
        rw [dvec_opp, add_neg_cancel_right]
        exact Finset.mem_insert_of_mem hs
      obtain ⟨k, hk⟩ := D_pair i o j hj
      have hadj : ∀ u v, Dfun i o k = u → Dfun i o (k + 1) = v →
          CAdj (splice c L s i o) (L + 26) (tr s u) (tr s v) := by
        intro u v hu hv
        refine ⟨L + k, by omega, by rw [hD, hu], ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), show L + k + 1 = L + (k + 1) by ring, hD, hv]
      rw [pA_tr, pB_tr]
      rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hadj _ _ h1 h2)
      · exact Or.inr (hadj _ _ h1 h2)
    · have hfree' : s₂ + dvec j ∉ T := fun h => hfree (Finset.mem_insert_of_mem h)
      have hne : s₂ + dvec j ≠ s + dvec i := fun h => hfree (h ▸ Finset.mem_insert_self _ _)
      have key : ∀ u v, ((u = pA s₂ j ∧ v = pB s₂ j) ∨ (u = pB s₂ j ∧ v = pA s₂ j)) →
          CAdj c L u v → CAdj (splice c L s i o) (L + 26) u v := by
        intro u v huv h
        refine cadj_splice hL s i o h fun hu hv => ?_
        rw [hx, ex_tr] at hu
        rw [hy, ey_tr] at hv
        have := pair_eq (s := s) (s' := s₂) (i := i) (j := j) (by
          cases o <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu hv <;>
            rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all)
        exact hne (by rw [this.1, this.2])
      rcases hpair s₂ hs₂ j hfree' with h | h
      · exact Or.inl (key _ _ (Or.inl ⟨rfl, rfl⟩) h)
      · exact Or.inr (key _ _ (Or.inr ⟨rfl, rfl⟩) h)


/-! ### Base case and induction -/

theorem inv_base (s₁ : ℤ × ℤ) : Inv {s₁} 24 (fun k => tr s₁ (Lfun k)) := by
  refine ⟨by norm_num, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [mem_Iio] at hj₁ hj₂
    have := L_inj ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (tr_injective s₁ heq)
    simpa using this
  · intro k hk
    simp only
    rw [isUnitStep_tr]
    exact L_step ⟨k, hk⟩
  · intro k hk
    refine Or.inl ⟨s₁, Finset.mem_singleton_self _, ?_⟩
    have := (inSqInt_tr s₁ 0 (Lfun k)).mpr (L_mem ⟨k, hk⟩)
    rwa [add_zero] at this
  · intro s hs
    rw [Finset.mem_singleton.mp hs]
    refine ⟨0, by norm_num, ?_⟩
    have := (inSqInt_tr s₁ 0 (Lfun 0)).mpr (L_mem ⟨0, by norm_num⟩)
    rwa [add_zero] at this
  · intro s hs j _
    rw [Finset.mem_singleton.mp hs]
    have hA := pA_tr s₁ 0 j
    have hB := pB_tr s₁ 0 j
    rw [add_zero] at hA hB
    obtain ⟨k, hk⟩ := L_pair j
    rw [hA, hB]
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨k, k.2, by simp only [h1], by simp only [h2]⟩
    · exact Or.inr ⟨k, k.2, by simp only [h1], by simp only [h2]⟩

/-- One growth step: splice in a square adjacent across a free side. -/
theorem inv_grow {T : Finset (ℤ × ℤ)} {L : ℕ} {c : ℕ → ℤ × ℤ} (h : Inv T L c) {s : ℤ × ℤ}
    (hs : s ∈ T) {i : Fin 4} (hℓ : s + dvec i ∉ T) :
    ∃ c', Inv (insert (s + dvec i) T) (L + 26) c' := by
  have hL : 0 < L := by have := h.1; omega
  have hlast : ∀ k < L, (L - 1 + (k + 1)) % L = k := by
    intro k hk
    rw [show L - 1 + (k + 1) = k + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  rcases h.2.2.2.2.2.2 s hs i hℓ with ⟨k, hk, hx, hy⟩ | ⟨k, hk, hx, hy⟩
  · refine ⟨_, inv_splice (inv_rot h (k + 1)) hs hℓ false ?_ ?_⟩
    · simp only [rot, hlast k hk, hx, ex_tr]; simp
    · simp only [rot, zero_add, hy, ey_tr]; simp
  · refine ⟨_, inv_splice (inv_rot h (k + 1)) hs hℓ true ?_ ?_⟩
    · simp only [rot, hlast k hk, hx, ex_tr]; simp
    · simp only [rot, zero_add, hy, ey_tr]; simp

theorem exists_inv_sub {T : Finset (ℤ × ℤ)} (hc : PolyConnected T) :
    ∀ n, 1 ≤ n → n ≤ T.card → ∃ A ⊆ T, A.card = n ∧ ∃ L c, Inv A L c := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      exact ⟨{s₁}, by simpa using hs₁, by simp, 24, _, inv_base s₁⟩
    · obtain ⟨A, hAT, hAc, L, c, hinv⟩ := ih hn0 (by omega)
      have hne : A ≠ T := by rintro rfl; omega
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      have : ¬ ∀ s ∈ A, ∀ s' ∈ T, IsUnitStep s s' → s' ∈ A := fun h => hne (hc A hAT hAne h)
      push_neg at this
      obtain ⟨s, hs, s', hs'T, hstep, hs'A⟩ := this
      obtain ⟨i, rfl⟩ := (isUnitStep_iff s s').mp hstep
      obtain ⟨c', hc'⟩ := inv_grow hinv hs hs'A
      refine ⟨insert (s + dvec i) A, Finset.insert_subset hs'T hAT, ?_, _, c', hc'⟩
      rw [Finset.card_insert_of_notMem hs'A, hAc]

theorem exists_inv {T : Finset (ℤ × ℤ)} (hT : T.Nonempty) (hc : PolyConnected T) :
    ∃ L c, Inv T L c := by
  obtain ⟨A, hAT, hAc, L, c, h⟩ :=
    exists_inv_sub hc T.card (Finset.card_pos.mpr hT) le_rfl
  rw [Finset.eq_of_subset_of_card_le hAT hAc.ge] at h
  exact ⟨L, c, h⟩

theorem inSq_of_good {T : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (h : Good T p) : ∃ s ∈ T, InSq s p := by
  rcases h with ⟨s, hs, h1⟩ | ⟨s, hs, i, _, h1 | h1⟩
  · exact ⟨s, hs, inSq_of_inSqInt h1⟩
  · exact ⟨s, hs, h1 ▸ (inSq_side s i).1⟩
  · exact ⟨s, hs, h1 ▸ (inSq_side s i).2⟩

end LCyc

/-- The cycle of `LCyc.exists_inv`, with its exact length `26 N - 2`. -/
theorem exists_latticeCycle' (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (hc : PolyConnected T) :
    ∃ (L : ℕ) (c : ℕ → ℤ × ℤ), L = 26 * T.card - 2 ∧ 24 ≤ L ∧ InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStep (c i) (c (i + 1))) ∧ IsUnitStep (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InSq s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InSqInt s (c i) := by
  obtain ⟨L, c, hL2, hLc, hinj, hstep, hgood, hint, -⟩ := LCyc.exists_inv hT hc
  have hcard : 1 ≤ T.card := Finset.card_pos.mpr hT
  refine ⟨L, c, hLc, by omega, hinj, fun i hi => ?_, ?_, fun i hi => LCyc.inSq_of_good (hgood i hi),
    hint⟩
  · have := hstep i (by omega)
    rwa [Nat.mod_eq_of_lt hi] at this
  · have := hstep (L - 1) (by omega)
    rwa [show L - 1 + 1 = L by omega, Nat.mod_self] at this

end HPC.Plane
