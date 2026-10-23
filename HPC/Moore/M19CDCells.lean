import HPC.Moore.M19CDTile

/-!
# Moore 1919: the subdivision lemma (batch 141, item B)

The arcs of a double ruling with `n` and `m` arcs cut the interior `I` of `ABCDA` into exactly
`(n + 1)(m + 1)` subdivisions, each the interior of a closed curve lying on `ABCDA` and the arcs.

Proof (by tilings, `HPC/Moore/M19CDTile.lean`): start from the single tile `I`; each arc `XᵢX′ᵢ`
meets `ABCDA` and the earlier arcs only in its two ends, so adds one tile; each arc `YⱼY′ⱼ` meets
`ABCDA`, the arcs `X` and the earlier arcs `Y` in its two ends and its `n` crossing points with the
arcs `X`, so adds `n + 1` tiles. Total: `1 + n + m(n + 1) = (n + 1)(m + 1)`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- Points listed in order on an arc are distinct and lie on the arc. -/
theorem Space.InOrder.nodup_subset {K : Set S} {K₀ K₁ : S} {pts : List S}
    (h : σ.InOrder K K₀ K₁ pts) : pts.Nodup ∧ ∀ x ∈ pts, x ∈ K := by
  letI := σ.topology
  obtain ⟨f, hf, hfr, -, -, ts, hts, rfl⟩ := h
  refine ⟨List.Nodup.map hf.injective (hts.imp ne_of_lt), ?_⟩
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact hfr ▸ mem_range_self t

/-- The inner points of an ordered list `a, …, b` on an arc are on the arc and differ from `a`,
`b`. -/
theorem Space.InOrder.mid {K : Set S} {K₀ K₁ a b : S} {L : List S}
    (h : σ.InOrder K K₀ K₁ ([a] ++ L ++ [b])) : ∀ x ∈ L, x ∈ K ∧ x ≠ a ∧ x ≠ b := by
  obtain ⟨hnd, hmem⟩ := h.nodup_subset
  intro x hx
  have h₁ : (a :: (L ++ [b])).Nodup := by simpa using hnd
  have h₂ : (b :: L).Nodup := by
    have := List.nodup_append_comm.mp h₁.of_cons
    simpa using this
  refine ⟨hmem x (by simp [hx]), ?_, ?_⟩
  · rintro rfl
    exact (List.nodup_cons.mp h₁).1 (List.mem_append_left _ hx)
  · rintro rfl
    exact (List.nodup_cons.mp h₂).1 hx

namespace Space.Quad

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

theorem sAB_sub (q : σ.Quad J I A B C D sAB sBC sCD sDA) : sAB ⊆ J := q.union ▸ fun _ h => Or.inl (Or.inl (Or.inl h))
theorem sBC_sub (q : σ.Quad J I A B C D sAB sBC sCD sDA) : sBC ⊆ J := q.union ▸ fun _ h => Or.inl (Or.inl (Or.inr h))
theorem sCD_sub (q : σ.Quad J I A B C D sAB sBC sCD sDA) : sCD ⊆ J := q.union ▸ fun _ h => Or.inl (Or.inr h)
theorem sDA_sub (q : σ.Quad J I A B C D sAB sBC sCD sDA) : sDA ⊆ J := q.union ▸ fun _ h => Or.inr h

end Space.Quad

namespace Space.DoubleRuling

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ} (R : σ.DoubleRuling q n m)

theorem X_inj : Function.Injective R.X := by
  obtain ⟨hnd, -⟩ := R.orderAB.nodup_subset
  exact List.nodup_ofFn.mp (hnd.sublist
    ((List.sublist_append_right [A] _).trans (List.sublist_append_left _ [B])))

theorem X_mem (i : Fin n) : R.X i ∈ sAB ∧ R.X i ≠ A ∧ R.X i ≠ B :=
  R.orderAB.mid _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem X'_mem (i : Fin n) : R.X' i ∈ sCD ∧ R.X' i ≠ D ∧ R.X' i ≠ C :=
  R.orderDC.mid _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem Y_mem (j : Fin m) : R.Y j ∈ sBC ∧ R.Y j ≠ B ∧ R.Y j ≠ C :=
  R.orderBC.mid _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem Y'_mem (j : Fin m) : R.Y' j ∈ sDA ∧ R.Y' j ≠ A ∧ R.Y' j ≠ D :=
  R.orderAD.mid _ (List.mem_ofFn.mpr ⟨j, rfl⟩)


/-- The arcs `X` meet `ABCDA` only in their ends. -/
theorem arcX_inter (hIJ : Disjoint I J) (i : Fin n) : R.arcX i ∩ J = {R.X i, R.X' i} := by
  apply subset_antisymm
  · rintro x ⟨hx, hxJ⟩
    by_contra hxe
    exact disjoint_left.mp hIJ (R.withinX i ⟨hx, hxe⟩) hxJ
  · rintro x (rfl | rfl)
    · exact ⟨(R.isArcX i).2.2.2.2.1, q.sAB_sub (R.X_mem i).1⟩
    · exact ⟨(R.isArcX i).2.2.2.2.2.1, q.sCD_sub (R.X'_mem i).1⟩

/-- The arcs `Y` meet `ABCDA` only in their ends. -/
theorem arcY_inter (hIJ : Disjoint I J) (j : Fin m) : R.arcY j ∩ J = {R.Y j, R.Y' j} := by
  apply subset_antisymm
  · rintro x ⟨hx, hxJ⟩
    by_contra hxe
    exact disjoint_left.mp hIJ (R.withinY j ⟨hx, hxe⟩) hxJ
  · rintro x (rfl | rfl)
    · exact ⟨(R.isArcY j).2.2.2.2.1, q.sBC_sub (R.Y_mem j).1⟩
    · exact ⟨(R.isArcY j).2.2.2.2.2.1, q.sDA_sub (R.Y'_mem j).1⟩

/-- The crossing point of `XᵢX′ᵢ` and `YⱼY′ⱼ`. -/
noncomputable def cross (i : Fin n) (j : Fin m) : S := (R.crossXY i j).exists.choose

theorem cross_mem (i : Fin n) (j : Fin m) : R.cross i j ∈ R.arcX i ∩ R.arcY j :=
  (R.crossXY i j).exists.choose_spec

theorem cross_unique {i : Fin n} {j : Fin m} {P : S} (hP : P ∈ R.arcX i ∩ R.arcY j) :
    P = R.cross i j :=
  (R.crossXY i j).unique hP (R.cross_mem i j)

/-- A crossing point is not an end of the arc `Y`. -/
theorem cross_ne (hIJ : Disjoint I J) (i : Fin n) (j : Fin m) :
    R.cross i j ≠ R.Y j ∧ R.cross i j ≠ R.Y' j := by
  have hX : R.cross i j ∈ R.arcX i := (R.cross_mem i j).1
  have key : ∀ {y : S}, y ∈ J → R.cross i j = y → y = R.X i ∨ y = R.X' i := by
    intro y hy e
    have : y ∈ R.arcX i ∩ J := ⟨e ▸ hX, hy⟩
    rw [R.arcX_inter hIJ] at this
    exact this
  obtain ⟨hYs, hYB, hYC⟩ := R.Y_mem j
  obtain ⟨hY's, hY'A, hY'D⟩ := R.Y'_mem j
  obtain ⟨hXs, -, -⟩ := R.X_mem i
  obtain ⟨hX's, -, -⟩ := R.X'_mem i
  constructor
  · intro e
    rcases key (q.sBC_sub hYs) e with h | h
    · have : R.Y j ∈ sAB ∩ sBC := ⟨h ▸ hXs, hYs⟩
      rw [q.ab_bc] at this; exact hYB this
    · have : R.Y j ∈ sBC ∩ sCD := ⟨hYs, h ▸ hX's⟩
      rw [q.bc_cd] at this; exact hYC this
  · intro e
    rcases key (q.sDA_sub hY's) e with h | h
    · have : R.Y' j ∈ sDA ∩ sAB := ⟨hY's, h ▸ hXs⟩
      rw [q.da_ab] at this; exact hY'A this
    · have : R.Y' j ∈ sCD ∩ sDA := ⟨h ▸ hX's, hY's⟩
      rw [q.cd_da] at this; exact hY'D this

/-- `J` together with the first `k` arcs `X`. -/
def GX (k : ℕ) : Set S := J ∪ ⋃ (i : Fin n) (_ : (i : ℕ) < k), R.arcX i

/-- `J`, all the arcs `X`, and the first `k` arcs `Y`. -/
def GY (k : ℕ) : Set S := R.GX n ∪ ⋃ (j : Fin m) (_ : (j : ℕ) < k), R.arcY j

theorem GX_succ {k : ℕ} (hk : k < n) : R.GX (k + 1) = R.GX k ∪ R.arcX ⟨k, hk⟩ := by
  ext x
  simp only [GX, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (h | ⟨i, hi, hx⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact Or.inl (Or.inr ⟨i, hi, hx⟩)
      · right; have : i = ⟨k, hk⟩ := Fin.ext hi
        exact this ▸ hx
  · rintro ((h | ⟨i, hi, hx⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact Or.inr ⟨⟨k, hk⟩, Nat.lt_succ_self k, h⟩

theorem GY_succ {k : ℕ} (hk : k < m) : R.GY (k + 1) = R.GY k ∪ R.arcY ⟨k, hk⟩ := by
  ext x
  simp only [GY, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (h | ⟨i, hi, hx⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact Or.inl (Or.inr ⟨i, hi, hx⟩)
      · right; have : i = ⟨k, hk⟩ := Fin.ext hi
        exact this ▸ hx
  · rintro ((h | ⟨i, hi, hx⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact Or.inr ⟨⟨k, hk⟩, Nat.lt_succ_self k, h⟩

theorem GY_m : R.GY m = J ∪ R.carrier := by
  ext x
  simp only [GY, GX, carrier, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro ((h | ⟨i, -, hx⟩) | ⟨j, -, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hx⟩)
    · exact Or.inr (Or.inr ⟨j, hx⟩)
  · rintro (h | ⟨i, hx⟩ | ⟨j, hx⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨i, i.2, hx⟩)
    · exact Or.inr ⟨j, j.2, hx⟩

section Sub

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **The tiling by the subdivisions**: `I − ⋃ arcs` is tiled by exactly `(n + 1)(m + 1)`
interiors of closed curves lying on `J + ⋃ arcs`. -/
theorem tiling : ∃ F : Finset (Set S), σ.Tiling I (J ∪ R.carrier) F ∧
    F.card = (n + 1) * (m + 1) := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have hT0 : σ.Tiling I J {I} := by
    refine ⟨by simp, ?_, ?_⟩
    · intro V hV
      rw [Finset.mem_singleton] at hV
      exact ⟨J, hV ▸ q.interior, subset_rfl⟩
    · simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
      exact hIJ.sdiff_eq_left.symm
  have hXt : ∀ i, TArc (R.X i) (R.X' i) (R.arcX i) := fun i =>
    (isArc_iff_tarc h1 h3 h4 h51).mp (R.isArcX i)
  have hYt : ∀ j, TArc (R.Y j) (R.Y' j) (R.arcY j) := fun j =>
    (isArc_iff_tarc h1 h3 h4 h51).mp (R.isArcY j)
  -- the arcs `X`
  have stepX : ∀ k ≤ n, ∃ F : Finset (Set S), σ.Tiling I (R.GX k) F ∧ F.card = k + 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨{I}, ?_, rfl⟩
      have : R.GX 0 = J := by simp [GX]
      rw [this]; exact hT0
    | succ k ih =>
      intro hk
      obtain ⟨F, hT, hc⟩ := ih (Nat.le_of_succ_le hk)
      have hJG : J ⊆ R.GX k := subset_union_left
      set i : Fin n := ⟨k, hk⟩
      obtain ⟨F', hT', hc'⟩ := hT.add_arc h1 h2 h3 h4 h5 h7 h8
        (hJG (q.sAB_sub (R.X_mem i).1)) (hJG (q.sCD_sub (R.X'_mem i).1)) (hXt i) (by
          intro x hx
          refine ⟨R.withinX i hx, ?_⟩
          rintro (hxJ | hxX)
          · exact disjoint_left.mp hIJ (R.withinX i hx) hxJ
          · simp only [mem_iUnion, exists_prop] at hxX
            obtain ⟨i', hi', hx'⟩ := hxX
            have hne : i ≠ i' := fun e => by
              rw [← e] at hi'; exact lt_irrefl _ hi'
            exact disjoint_left.mp (R.disjX i i' hne) hx.1 hx')
      exact ⟨F', by rw [R.GX_succ hk]; exact hT', by omega⟩
  obtain ⟨FX, hTX, hcX⟩ := stepX n le_rfl
  -- the arcs `Y`
  have stepY : ∀ k ≤ m, ∃ F : Finset (Set S), σ.Tiling I (R.GY k) F ∧
      F.card = (n + 1) * (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨FX, ?_, by rw [hcX]; ring⟩
      have : R.GY 0 = R.GX n := by simp [GY]
      rw [this]; exact hTX
    | succ k ih =>
      intro hk
      obtain ⟨F, hT, hc⟩ := ih (Nat.le_of_succ_le hk)
      have hJG : J ⊆ R.GY k := subset_union_left.trans subset_union_left
      set j : Fin m := ⟨k, hk⟩
      -- the meeting set
      have hmeet : R.arcY j ∩ R.GY k = {R.Y j, R.Y' j} ∪ range (fun i => R.cross i j) := by
        apply subset_antisymm
        · rintro x ⟨hxY, hxG⟩
          simp only [GY, GX, mem_union, mem_iUnion, exists_prop] at hxG
          rcases hxG with (hxJ | ⟨i, -, hxX⟩) | ⟨j', hj', hxY'⟩
          · left
            have : x ∈ R.arcY j ∩ J := ⟨hxY, hxJ⟩
            rwa [R.arcY_inter hIJ] at this
          · right
            exact ⟨i, (R.cross_unique ⟨hxX, hxY⟩).symm⟩
          · have hne : j ≠ j' := fun e => by
              rw [← e] at hj'; exact lt_irrefl _ hj'
            exact absurd hxY' (disjoint_left.mp (R.disjY j j' hne) hxY)
        · rintro x (hx | ⟨i, rfl⟩)
          · have : x ∈ R.arcY j ∩ J := by rw [R.arcY_inter hIJ]; exact hx
            exact ⟨this.1, hJG this.2⟩
          · refine ⟨(R.cross_mem i j).2, ?_⟩
            exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, i.2, (R.cross_mem i j).1⟩))
      have hinj : Function.Injective (fun i => R.cross i j) := by
        intro i i' e
        have e : R.cross i j = R.cross i' j := e
        by_contra hne
        exact disjoint_left.mp (R.disjX i i' hne) (R.cross_mem i j).1
          (e ▸ (R.cross_mem i' j).1)
      have hfin : (R.arcY j ∩ R.GY k).Finite := by
        rw [hmeet]; exact (toFinite _).union (finite_range _)
      have hcard : (R.arcY j ∩ R.GY k).ncard = n + 2 := by
        rw [hmeet, ncard_union_eq, ncard_pair (hYt j).ne, ncard_range_of_injective hinj,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        · ring
        · rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
          rintro x ⟨hx, ⟨i, rfl⟩⟩
          obtain ⟨h₁, h₂⟩ := R.cross_ne hIJ i j
          rcases hx with h | h
          · exact h₁ h
          · exact h₂ h
      obtain ⟨F', hT', hc'⟩ := hT.add_arc_finite h1 h2 h3 h4 h5 h7 h8 _
        (hJG (q.sBC_sub (R.Y_mem j).1)) (hJG (q.sDA_sub (R.Y'_mem j).1)) (hYt j)
        (R.withinY j) hfin hcard
      refine ⟨F', by rw [R.GY_succ hk]; exact hT', ?_⟩
      rw [hc] at hc'
      have : F'.card = (n + 1) * (k + 1) + (n + 1) := by omega
      rw [this]; ring
  obtain ⟨F, hT, hc⟩ := stepY m le_rfl
  exact ⟨F, by rw [← R.GY_m]; exact hT, hc⟩

omit h8 in
/-- The subdivisions are the tiles. -/
theorem cells_eq {F : Finset (Set S)} (hT : σ.Tiling I (J ∪ R.carrier) F) : R.cells = ↑F := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have heq : I \ (J ∪ R.carrier) = I \ R.carrier := by
    ext x
    simp only [mem_diff, mem_union, not_or]
    constructor
    · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, fun hJ => disjoint_left.mp hIJ h hJ, h'⟩
  rw [← hT.components h1 h2 h3 h4 h5 h7, heq]
  rfl

end Sub

end Space.DoubleRuling

section SubLemma

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Subdivision lemma** (used throughout 1919, never stated): every subdivision of a double
ruling is the interior of a closed curve lying in `J ∪ ⋃ arcs`. *Axioms used: 1, 2, 3, 4, 5, 7, 8.*
**Shape change:** the axioms are made explicit (Axiom 6 is not used). -/
theorem doubleRuling_cell {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) {U : Set S} (hU : U ∈ R.cells) :
    ∃ J' : Set S, σ.IsInteriorOf J' U ∧ J' ⊆ J ∪ R.carrier := by
  obtain ⟨F, hT, -⟩ := R.tiling h1 h2 h3 h4 h5 h7 h8
  rw [R.cells_eq h1 h2 h3 h4 h5 h7 hT] at hU
  exact hT.int U hU

/-- **Subdivision lemma**, the count: there are exactly `(n + 1)(m + 1)` subdivisions.
*Axioms used: 1, 2, 3, 4, 5, 7, 8.* **Shape change:** the axioms are made explicit. -/
theorem doubleRuling_cells_ncard {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : R.cells.ncard = (n + 1) * (m + 1) := by
  obtain ⟨F, hT, hc⟩ := R.tiling h1 h2 h3 h4 h5 h7 h8
  rw [R.cells_eq h1 h2 h3 h4 h5 h7 hT, ncard_coe_finset, hc]

end SubLemma

end HPC.Moore
