import HPC.Moore.M19CDRefine

/-!
# Moore 1919: rulings as sets of arcs are the double rulings of the commission (batch 141, item E)

A double ruling `R` (indexed arcs, with the ends in order on the sides) gives the ruling
`(range R.arcX, range R.arcY)` (`Space.DoubleRuling.toArcRuling`). Conversely, a ruling `(𝒳, 𝒴)`
given by sets of arcs is, up to indexing, a double ruling with `#𝒳` and `#𝒴` arcs
(`Space.ArcRuling.toDoubleRuling`): index the arcs `X` by the order of their ends on `AB`; then their
ends on `DC` are in the same order (`Space.ArcRuling.param_mono`: the arc `x′` starting after `x` on
`AB` lies in the half `XBCX′X` cut off by `x`, so it ends after `x` on `DC`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- The ends of an arc from `AB` to `CD` in terms of parametrizations of the two sides. -/
theorem Space.XArc.param (q : σ.Quad J I A B C D sAB sBC sCD sDA) (hIJ : Disjoint I J)
    {f g : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB)
    (hf0 : f 0 = A) (hf1 : f 1 = B) (hg : @IsEmbedding _ _ _ σ.topology g) (hgr : range g = sCD)
    (hg0 : g 0 = D) (hg1 : g 1 = C) {x : Set S} (hx : σ.XArc I sAB sCD A B C D x) :
    ∃ t s : unitInterval, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧ @TArc S σ.topology (f t) (g s) x ∧
      x \ {f t, g s} ⊆ I ∧ (∀ u, f u ∈ x → u = t) ∧ (∀ u, g u ∈ x → u = s) := by
  letI := σ.topology
  obtain ⟨P, P', ⟨hP, hPAB⟩, ⟨hP', hP'CD⟩, hxa, hxI, hxJ⟩ := hx.inter_J hIJ
  obtain ⟨t, rfl⟩ : P ∈ range f := hfr ▸ hP
  obtain ⟨s, rfl⟩ : P' ∈ range g := hgr ▸ hP'
  have ht0 : 0 < t := lt_of_le_of_ne nonneg' fun e => hPAB (Or.inl (by rw [← e, hf0]))
  have ht1 : t < 1 := lt_of_le_of_ne le_one' fun e => hPAB (Or.inr (by rw [e, hf1]; exact mem_singleton _))
  have hs0 : 0 < s := lt_of_le_of_ne nonneg' fun e => hP'CD (Or.inr (by rw [← e, hg0]; exact mem_singleton _))
  have hs1 : s < 1 := lt_of_le_of_ne le_one' fun e => hP'CD (Or.inl (by rw [e, hg1]))
  refine ⟨t, s, ht0, ht1, hs0, hs1, hxa, hxI, fun u hu => ?_, fun u hu => ?_⟩
  · have hfu : f u ∈ sAB := hfr ▸ mem_range_self u
    rcases hxJ _ hu (q.sAB_sub hfu) with h | h
    · exact hf.injective h
    · exact absurd (h ▸ hfu) (disjoint_right.mp q.ab_cd hP')
  · have hgu : g u ∈ sCD := hgr ▸ mem_range_self u
    rcases hxJ _ hu (q.sCD_sub hgu) with h | h
    · exact absurd (h ▸ hgu) (disjoint_left.mp q.ab_cd hP)
    · exact hg.injective h

/-- A cut along an arc from `f t` to `g s`, with the four pieces of `AB` and `CD` named. -/
theorem Space.Quad.exists_cut_param (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    {f g : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB)
    (hf0 : f 0 = A) (hf1 : f 1 = B) (hg : @IsEmbedding _ _ _ σ.topology g) (hgr : range g = sCD)
    (hg0 : g 0 = D) (hg1 : g 1 = C) {t s : unitInterval} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s)
    (hs1 : s < 1) {x : Set S} (hx : @TArc S σ.topology (f t) (g s) x) (hxI : x \ {f t, g s} ⊆ I) :
    ∃ c : q.Cut x, c.s₁ = f '' Icc 0 t ∧ c.s₂ = f '' Icc t 1 ∧ c.t₁ = g '' Icc 0 s ∧
      c.t₂ = g '' Icc s 1 := by
  letI := σ.topology
  obtain ⟨IA, IB, qA, qB, hsplit, hdis⟩ :=
    q.splitX h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hg hgr hg0 hg1 ht0 ht1 hs0 hs1 hx hxI
  refine ⟨⟨f t, g s, _, _, _, _, IA, IB, qA, qB, ?_, ?_, ?_, ?_, hsplit, hdis⟩, rfl, rfl, rfl, rfl⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc ht0.le ht1.le, unitInterval_Icc_zero_one, image_univ,
      hfr]
  · rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton ht0.le ht1.le, image_singleton]
  · rw [← image_union, Icc_union_Icc_eq_Icc hs0.le hs1.le, unitInterval_Icc_zero_one, image_univ,
      hgr]
  · rw [← image_inter hg.injective, Icc_inter_Icc_eq_singleton hs0.le hs1.le, image_singleton]

/-- **Planarity of a ruling.** If the arc `x′` of a ruling starts after the arc `x` on `AB`, it ends
after `x` on `DC`. -/
theorem Space.ArcRuling.param_mono (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴)
    {f g : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB)
    (hf0 : f 0 = A) (hf1 : f 1 = B) (hg : @IsEmbedding _ _ _ σ.topology g) (hgr : range g = sCD)
    (hg0 : g 0 = D) (hg1 : g 1 = C) {x x' : Set S} (hx : x ∈ 𝒳) (hx' : x' ∈ 𝒳) (hne : x ≠ x')
    {t s t' s' : unitInterval} (hxt : f t ∈ x) (hxs : g s ∈ x) (hx't : f t' ∈ x')
    (hx's : g s' ∈ x') (htt : t < t') : s < s' := by
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨t₀, s₀, ht0, ht1, hs0, hs1, hxa, hxI, ut, us⟩ :=
    (R.arcX x hx).param q hIJ hf hfr hf0 hf1 hg hgr hg0 hg1
  obtain rfl := ut t hxt
  obtain rfl := us s hxs
  obtain ⟨c, -, hs₂, ht₁, -⟩ :=
    q.exists_cut_param h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hg hgr hg0 hg1 ht0 ht1 hs0 hs1 hxa hxI
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have hd := R.disjX hx hx' hne
  rcases (c.X_eq h1 h2 h3 h4 h51 h7 R hx).le hx' with h | h | h
  · exact absurd h hne.symm
  · exfalso
    have hB : f t' ∈ c.clB := Or.inr (Or.inl (Or.inl (Or.inl (hs₂ ▸ ⟨t', ⟨htt.le, le_one'⟩, rfl⟩))))
    exact disjoint_left.mp hd (icl ⟨h.2.2 hx't, hB⟩) hx't
  · by_contra hss
    have hA : g s' ∈ c.clA :=
      Or.inr (Or.inl (Or.inr (ht₁ ▸ ⟨s', ⟨nonneg', not_lt.mp hss⟩, rfl⟩)))
    exact disjoint_left.mp hd (icl ⟨hA, h.2.2 hx's⟩) hx's

theorem pairwise_ends {n : ℕ} {u : Fin n → unitInterval} (hu : StrictMono u) (h0 : ∀ i, 0 < u i)
    (h1 : ∀ i, u i < 1) : ([0] ++ List.ofFn u ++ [1]).Pairwise (· < ·) := by
  simp only [List.pairwise_append, List.pairwise_ofFn, List.mem_append, List.mem_ofFn,
    List.mem_singleton]
  refine ⟨⟨List.pairwise_singleton _ _, fun i j hij => hu hij, ?_⟩, List.pairwise_singleton _ _, ?_⟩
  · rintro a rfl b ⟨i, rfl⟩; exact h0 i
  · rintro a (rfl | ⟨i, rfl⟩) b rfl
    · exact zero_lt_one
    · exact h1 i

/-- **Indexing the arcs `X` of a ruling** by the order of their ends on `AB`: their ends on `DC` are
then in the same order. -/
theorem Space.ArcRuling.sortX (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) :
    ∃ (n : ℕ) (X X' : Fin n → S) (arc : Fin n → Set S), n = 𝒳.ncard ∧ range arc = 𝒳 ∧
      Function.Injective arc ∧ σ.InOrder sAB A B ([A] ++ List.ofFn X ++ [B]) ∧
      σ.InOrder sCD D C ([D] ++ List.ofFn X' ++ [C]) ∧ (∀ i, σ.IsArc (X i) (X' i) (arc i)) ∧
      (∀ i, openArc (X i) (X' i) (arc i) ⊆ I) := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp q.ab
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp q.cd).symm
  have par := fun x (hx : x ∈ 𝒳) => (R.arcX x hx).param q hIJ hf hfr hf0 hf1 hg hgr hg0 hg1
  choose! τ κ hτ0 hτ1 hκ0 hκ1 harc hI uτ uκ using par
  have τinj : InjOn τ 𝒳 := by
    intro x hx x' hx' h
    by_contra hne
    refine disjoint_left.mp (R.disjX hx hx' hne) (harc x hx).left_mem ?_
    rw [h]; exact (harc x' hx').left_mem
  set T := R.finX.toFinset.image τ with hT
  have hTc : T.card = 𝒳.ncard := by
    rw [hT, Finset.card_image_of_injOn (by simpa using τinj), ← ncard_eq_toFinset_card _ R.finX]
  set e := T.orderEmbOfFin rfl
  have he : ∀ i, ∃ x ∈ 𝒳, τ x = e i := fun i => by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (T.orderEmbOfFin_mem rfl i)
    exact ⟨x, R.finX.mem_toFinset.mp hx, hxe⟩
  choose arc harc𝒳 harcτ using he
  have hmono : StrictMono fun i => κ (arc i) := by
    intro i j hij
    refine R.param_mono h1 h2 h3 h4 h5 h7 h8 q hf hfr hf0 hf1 hg hgr hg0 hg1 (harc𝒳 i) (harc𝒳 j)
      (fun h => ?_) (harc _ (harc𝒳 i)).left_mem (harc _ (harc𝒳 i)).right_mem
      (harc _ (harc𝒳 j)).left_mem (harc _ (harc𝒳 j)).right_mem ?_
    · have : e i = e j := by rw [← harcτ i, ← harcτ j, h]
      exact (ne_of_lt hij) (e.injective this)
    · rw [harcτ i, harcτ j]; exact e.strictMono hij
  refine ⟨T.card, fun i => f (e i), fun i => g (κ (arc i)), arc, hTc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩; exact harc𝒳 i
    · intro hx
      have : τ x ∈ range e := by
        rw [Finset.range_orderEmbOfFin]; simp only [hT, Finset.coe_image, Finite.coe_toFinset]
        exact ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := this
      exact ⟨i, τinj (harc𝒳 i) hx (by rw [harcτ i, hi])⟩
  · intro i j h
    apply e.injective
    rw [← harcτ i, ← harcτ j, h]
  · refine ⟨f, hf, hfr, hf0, hf1, [0] ++ List.ofFn (fun i => e i) ++ [1],
      pairwise_ends e.strictMono (fun i => ?_) (fun i => ?_), ?_⟩
    · rw [← harcτ i]; exact hτ0 _ (harc𝒳 i)
    · rw [← harcτ i]; exact hτ1 _ (harc𝒳 i)
    · simp [List.map_ofFn, hf0, hf1, Function.comp_def]
  · refine ⟨g, hg, hgr, hg0, hg1, [0] ++ List.ofFn (fun i => κ (arc i)) ++ [1],
      pairwise_ends hmono (fun i => hκ0 _ (harc𝒳 i)) (fun i => hκ1 _ (harc𝒳 i)), ?_⟩
    simp [List.map_ofFn, hg0, hg1, Function.comp_def]
  · intro i
    refine (isArc_iff_tarc h1 h3 h4 h51).mpr ?_
    have := harc _ (harc𝒳 i)
    rwa [harcτ i] at this
  · intro i
    have := hI _ (harc𝒳 i)
    rwa [harcτ i] at this

/-- **A double ruling is a ruling by sets of arcs.** -/
theorem Space.DoubleRuling.toArcRuling (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ} (R : σ.DoubleRuling q n m) :
    σ.ArcRuling I sAB sBC sCD sDA A B C D (range R.arcX) (range R.arcY) where
  finX := finite_range _
  finY := finite_range _
  arcX := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨hX, hXA, hXB⟩ := R.X_mem i
    obtain ⟨hX', hX'D, hX'C⟩ := R.X'_mem i
    refine ⟨R.X i, R.X' i, ⟨hX, ?_⟩, ⟨hX', ?_⟩,
      (isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcX i), R.withinX i⟩
    · rintro (h | h)
      · exact hXA h
      · exact hXB h
    · rintro (h | h)
      · exact hX'C h
      · exact hX'D h
  arcY := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨hY, hYB, hYC⟩ := R.Y_mem j
    obtain ⟨hY', hY'A, hY'D⟩ := R.Y'_mem j
    refine ⟨R.Y j, R.Y' j, ⟨hY, ?_⟩, ⟨hY', ?_⟩,
      (isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcY j), R.withinY j⟩
    · rintro (h | h)
      · exact hYB h
      · exact hYC h
    · rintro (h | h)
      · exact hY'D h
      · exact hY'A h
  disjX := by
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hne
    exact R.disjX i i' fun h => hne (h ▸ rfl)
  disjY := by
    rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩ hne
    exact R.disjY j j' fun h => hne (h ▸ rfl)
  cross := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact R.crossXY i j

theorem Space.DoubleRuling.carrier_eq {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : R.carrier = ⋃₀ range R.arcX ∪ ⋃₀ range R.arcY := by
  simp only [Space.DoubleRuling.carrier, sUnion_range]

theorem Space.DoubleRuling.cells_eq_cellsOf {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : R.cells = σ.cellsOf I R.carrier := rfl

/-- **A ruling by sets of arcs is a double ruling**, with `#𝒳` and `#𝒴` arcs, indexed by the order
of their ends on `AB` and on `BC`. -/
theorem Space.ArcRuling.toDoubleRuling (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) :
    ∃ R' : σ.DoubleRuling q 𝒳.ncard 𝒴.ncard, range R'.arcX = 𝒳 ∧ range R'.arcY = 𝒴 := by
  obtain ⟨n, X, X', aX, rfl, hrX, hiX, oAB, oDC, isX, wX⟩ := R.sortX h1 h2 h3 h4 h5 h7 h8 q
  obtain ⟨m, Y, Y', aY, rfl, hrY, hiY, oBC, oAD, isY, wY⟩ :=
    (R.rot h1).sortX h1 h2 h3 h4 h5 h7 h8 q.rot
  have mX : ∀ i, aX i ∈ 𝒳 := fun i => hrX ▸ mem_range_self i
  have mY : ∀ j, aY j ∈ 𝒴 := fun j => hrY ▸ mem_range_self j
  exact ⟨⟨X, X', Y, Y', aX, aY, oAB, oBC, oDC, oAD, isX, isY, wX, wY,
    fun i j => R.cross _ (mX i) _ (mY j),
    fun i i' hne => R.disjX (mX i) (mX i') fun h => hne (hiX h),
    fun j j' hne => R.disjY (mY j) (mY j') fun h => hne (hiY h)⟩, hrX, hrY⟩

end HPC.Moore
