import HPC.Moore.M19CDOrder

/-!
# Moore 1919: refinement and padding of double rulings (batch 141, items A and E)

* `doubleRuling_refine` (item E): Moore's "the arcs of these rulings may be extended in such a way
  that there will result a new double ruling `τ₂` of `ABCDA` such that each arc of `τ₁` is also an
  arc of `τ₂`" (p. 175; again in Theorem E, p. 176), for the double rulings of the commission.
* `doubleRuling_pad` (item A): every double ruling with `n` and `m` arcs can be extended, by adding
  arcs, to a double ruling with `max n m` arcs in each ruling whose subdivisions lie in those of the
  given one. So the choice of different numbers `n`, `m` is a convenience, not a necessity: the
  printed definition (equal numbers) loses nothing.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- `ABCDA` has a double ruling all of whose subdivisions have property `Good`. -/
def Space.DoubleRulable (σ : Space S) (Good : Set S → Prop) {J I : Set S} {A B C D : S}
    {sAB sBC sCD sDA : Set S} (q : σ.Quad J I A B C D sAB sBC sCD sDA) : Prop :=
  ∃ n m : ℕ, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, Good U

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- A point of an open arc avoiding a given finite set. -/
theorem exists_mem_openArc_notMem (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {a b : S} {s : Set S} (hs : σ.IsArc a b s) {F : Set S}
    (hF : F.Finite) : ∃ P ∈ s \ {a, b}, P ∉ F := by
  letI := σ.topology
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hs
  obtain ⟨_, ⟨t, ht, rfl⟩, htF⟩ :=
    ((Ioo_infinite (zero_lt_one' unitInterval)).image hf.injective.injOn).exists_notMem_finite hF
  refine ⟨f t, ⟨hfr ▸ mem_range_self t, ?_⟩, htF⟩
  rintro (h | h)
  · exact ht.1.ne' (hf.injective (h.trans hf0.symm))
  · exact ht.2.ne (hf.injective (h.trans hf1.symm))

/-- The arcs of a ruling meet `ABCDA` in finitely many points. -/
theorem Space.ArcRuling.finite_inter_J (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) : (J ∩ ⋃₀ 𝒴).Finite := by
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  refine ((R.finY.image (· ∩ J)).sUnion ?_).subset ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨P, P', -, -, -, -, hJ⟩ := (R.arcY y hy).inter_J hIJ
    exact (toFinite {P, P'}).subset fun z hz => hJ z hz.1 hz.2
  · rintro z ⟨hzJ, y, hy, hzy⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hzy, hzJ⟩

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Padding the arcs `Y`**: `k` arcs can be added to the arcs `Y` of a ruling. -/
theorem Space.ArcRuling.padY (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 : Set (Set S)} (k : ℕ) :
    ∀ {𝒴 : Set (Set S)}, σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴 →
      ∃ 𝒴', 𝒴 ⊆ 𝒴' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴' ∧ 𝒴'.ncard = 𝒴.ncard + k := by
  have h51 := axiom5₁_of_axiom5 h5
  induction k with
  | zero => exact fun R => ⟨_, subset_rfl, R, rfl⟩
  | succ k ih =>
    intro 𝒴 R
    obtain ⟨𝒴', hsub, R', hc⟩ := ih R
    obtain ⟨P, hP, hPF⟩ := exists_mem_openArc_notMem h1 h3 h4 h51 q.bc
      (R'.finite_inter_J h1 h2 h3 h4 h51 h7 q)
    have hPY : P ∉ ⋃₀ 𝒴' := fun h => hPF ⟨q.sBC_sub hP.1, h⟩
    obtain ⟨y, hPy, R''⟩ := R'.extendY h1 h2 h3 h4 h5 h6 h7 h8 q hP hPY
    have hy : y ∉ 𝒴' := fun h => hPY ⟨y, h, hPy⟩
    refine ⟨insert y 𝒴', hsub.trans (subset_insert _ _), R'', ?_⟩
    rw [ncard_insert_of_notMem hy R'.finY, hc]; rfl

/-- **Padding the arcs `X`**: `k` arcs can be added to the arcs `X` of a ruling. -/
theorem Space.ArcRuling.padX (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) (k : ℕ) :
    ∃ 𝒳', 𝒳 ⊆ 𝒳' ∧ σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳' 𝒴 ∧ 𝒳'.ncard = 𝒳.ncard + k := by
  obtain ⟨𝒳', hsub, R', hc⟩ := Space.ArcRuling.padY h1 h2 h3 h4 h5 h6 h7 h8 q.rot k (R.rot h1)
  exact ⟨𝒳', hsub, ((R'.rot h1).rot h1).rot h1, hc⟩

omit h6 in
theorem Space.ArcRuling.toDoubleRuling' (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    {𝒳 𝒴 : Set (Set S)} (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {n m : ℕ}
    (hn : 𝒳.ncard = n) (hm : 𝒴.ncard = m) :
    ∃ R' : σ.DoubleRuling q n m, range R'.arcX = 𝒳 ∧ range R'.arcY = 𝒴 := by
  subst hn hm
  exact R.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q

omit h2 h6 h7 h8 in
theorem Space.DoubleRuling.arcX_injective {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : Function.Injective R.arcX := by
  letI := σ.topology
  intro i i' h
  by_contra hne
  have hX := ((isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcX i)).left_mem
  exact disjoint_left.mp (R.disjX i i' hne) hX (h ▸ hX)

omit h2 h6 h7 h8 in
theorem Space.DoubleRuling.arcY_injective {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : Function.Injective R.arcY := by
  letI := σ.topology
  intro j j' h
  by_contra hne
  have hY := ((isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcY j)).left_mem
  exact disjoint_left.mp (R.disjY j j' hne) hY (h ▸ hY)

/-- **Padding** (item A). Every double ruling with `n` arcs `X` and `m` arcs `Y` extends, by adding
arcs, to a double ruling with `max n m` arcs in each ruling, each of whose subdivisions lies in a
subdivision of the given one. -/
theorem doubleRuling_pad (q : σ.Quad J I A B C D sAB sBC sCD sDA) {n m : ℕ}
    (R : σ.DoubleRuling q n m) :
    ∃ R' : σ.DoubleRuling q (max n m) (max n m), (∀ i, ∃ i', R'.arcX i' = R.arcX i) ∧
      (∀ j, ∃ j', R'.arcY j' = R.arcY j) ∧ ∀ U ∈ R'.cells, ∃ V ∈ R.cells, U ⊆ V := by
  have RA := R.toArcRuling h1 h3 h4 h5
  have hn : (range R.arcX).ncard = n := by
    rw [ncard_range_of_injective (R.arcX_injective h1 h3 h4 h5), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hm : (range R.arcY).ncard = m := by
    rw [ncard_range_of_injective (R.arcY_injective h1 h3 h4 h5), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨𝒳', hX, R₁, hc₁⟩ := RA.padX h1 h2 h3 h4 h5 h6 h7 h8 q (max n m - n)
  obtain ⟨𝒴', hY, R₂, hc₂⟩ := R₁.padY h1 h2 h3 h4 h5 h6 h7 h8 q (max n m - m)
  obtain ⟨R', hr₁, hr₂⟩ := R₂.toDoubleRuling' h1 h2 h3 h4 h5 h7 h8 q (n := max n m) (m := max n m)
    (by rw [hc₁, hn]; omega) (by rw [hc₂, hm]; omega)
  refine ⟨R', fun i => ?_, fun j => ?_, fun U hU => ?_⟩
  · have : R.arcX i ∈ range R'.arcX := by rw [hr₁]; exact hX (mem_range_self i)
    exact this
  · have : R.arcY j ∈ range R'.arcY := by rw [hr₂]; exact hY (mem_range_self j)
    exact this
  · rw [R'.cells_eq_cellsOf, R'.carrier_eq, hr₁, hr₂] at hU
    rw [R.cells_eq_cellsOf, R.carrier_eq]
    exact Space.cellsOf_mono (union_subset_union (sUnion_mono hX) (sUnion_mono hY)) hU

/-- **Refinement of a double ruling** (item E; used without proof on pp. 175 and 176). Let `Good`
be a property of sets inherited by subsets (in Moore's uses: *lies within some curve, or region, of a
given set*; *lies wholly without `g₁, …, gₖ` or within some curve of `G`*). If every subdivision of
the double ruling `R` of `ABCDA`, taken as the interior of a quadrilateral in any way, has a double
ruling all of whose subdivisions are `Good`, then `ABCDA` has a double ruling `R′` such that each arc
of `R` is an arc of `R′`, and each subdivision of `R′` is `Good` and lies in a subdivision of `R`.
*Axioms used: 1–8.* -/
theorem doubleRuling_refine {Good : Set S → Prop} (hGood : ∀ U V, U ⊆ V → Good V → Good U)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {n m : ℕ} (R : σ.DoubleRuling q n m)
    (H : ∀ {J' I' : Set S} {A' B' C' D' : S} {s₁ s₂ s₃ s₄ : Set S}
      (q' : σ.Quad J' I' A' B' C' D' s₁ s₂ s₃ s₄), I' ∈ R.cells → σ.DoubleRulable Good q') :
    ∃ n' m' : ℕ, ∃ R' : σ.DoubleRuling q n' m', (∀ i, ∃ i', R'.arcX i' = R.arcX i) ∧
      (∀ j, ∃ j', R'.arcY j' = R.arcY j) ∧ ∀ U ∈ R'.cells, Good U ∧ ∃ V ∈ R.cells, U ⊆ V := by
  have RA := R.toArcRuling h1 h3 h4 h5
  have H' : σ.CellsRulable Good I (⋃₀ range R.arcX ∪ ⋃₀ range R.arcY) := by
    intro J' I' A' B' C' D' s₁ s₂ s₃ s₄ q' hI'
    rw [← R.carrier_eq, ← R.cells_eq_cellsOf] at hI'
    obtain ⟨n'', m'', R'', hG⟩ := H q' hI'
    refine ⟨_, _, R''.toArcRuling h1 h3 h4 h5, ?_⟩
    rw [← R''.carrier_eq, ← R''.cells_eq_cellsOf]
    exact hG
  obtain ⟨𝒳', 𝒴', hX, hY, R₁, hP⟩ := RA.refine h1 h2 h3 h4 h5 h6 h7 h8 hGood q H'
  obtain ⟨R', hr₁, hr₂⟩ := R₁.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  refine ⟨_, _, R', fun i => ?_, fun j => ?_, fun U hU => ?_⟩
  · have : R.arcX i ∈ range R'.arcX := by rw [hr₁]; exact hX (mem_range_self i)
    exact this
  · have : R.arcY j ∈ range R'.arcY := by rw [hr₂]; exact hY (mem_range_self j)
    exact this
  · rw [R'.cells_eq_cellsOf, R'.carrier_eq, hr₁, hr₂] at hU
    rw [R.cells_eq_cellsOf, R.carrier_eq]
    exact hP U hU

end Ax

end HPC.Moore
