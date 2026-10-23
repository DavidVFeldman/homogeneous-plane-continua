import HPC.Moore.M19ESeq

/-!
# Moore 1919, Theorem E: the sides of a cross-cut as a "line" (batch 143, items A–B)

For a quadrilateral `ABCDA` with `AB` parametrized by `f` (from `A` to `B`), an arc `x` from `AB` to
`CD` is recorded by its *line record* `(t, L, R)`: `t` is the parameter of its end on `AB`, and `L`,
`R` are the closures of the two halves `AXX′DA`, `XBCX′X` of a cut along it. The sides `DA` and `BC`
are recorded as `(0, DA, J + I)` and `(1, J + I, BC)`.

These records satisfy the axioms of a family of lines (`HPC.Sq.Family`): the two sides are closed,
cover `J + I`, meet in the arc, the arc is in the closure of the complement of each side; along `AB`
a point `f s` is on the `L`-side iff `s ≤ t`; and two disjoint arcs are nested in the order of their
ends on `AB` (`lr_mono`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- A *line record* of the arc `x` (see the module docstring). -/
def Space.Quad.IsLineRec (q : σ.Quad J I A B C D sAB sBC sCD sDA) (f : unitInterval → S)
    (x : Set S) (r : ℝ × Set S × Set S) : Prop :=
  ∃ (t : unitInterval) (c : q.Cut x), 0 < t ∧ t < 1 ∧ f t ∈ x ∧ c.s₁ = f '' Icc 0 t ∧
    c.s₂ = f '' Icc t 1 ∧ r = ((t : ℝ), c.clA, c.clB)

section Lines

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

omit h1 h2 h3 h4 h5 h7 h8 in
/-- An arc from `AB` to `CD` lies on or within `ABCDA`. -/
theorem Space.XArc.sub_K (q : σ.Quad J I A B C D sAB sBC sCD sDA) {x : Set S}
    (hx : σ.XArc I sAB sCD A B C D x) : x ⊆ J ∪ I := by
  obtain ⟨P, P', hP, hP', -, hxI⟩ := hx
  intro z hz
  by_cases hzP : z = P ∨ z = P'
  · rcases hzP with rfl | rfl
    · exact Or.inl (q.sAB_sub hP.1)
    · exact Or.inl (q.sCD_sub hP'.1)
  · push_neg at hzP
    exact Or.inr (hxI ⟨hz, by simp [hzP.1, hzP.2]⟩)

variable (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f : unitInterval → S}
  (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)

include hf hfr hf0 hf1 in
/-- Every arc from `AB` to `CD` has a line record. -/
theorem exists_lineRec {x : Set S} (hx : σ.XArc I sAB sCD A B C D x) : ∃ r, q.IsLineRec f x r := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp q.cd).symm
  obtain ⟨t, s, ht0, ht1, hs0, hs1, hxa, hxI, -, -⟩ :=
    hx.param q hIJ hf hfr hf0 hf1 hg hgr hg0 hg1
  obtain ⟨c, hs₁, hs₂, -, -⟩ :=
    q.exists_cut_param h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hg hgr hg0 hg1 ht0 ht1 hs0 hs1 hxa hxI
  exact ⟨_, t, c, ht0, ht1, hxa.left_mem, hs₁, hs₂, rfl⟩

variable {q}
variable {x : Set S} {r : ℝ × Set S × Set S} (hx : σ.XArc I sAB sCD A B C D x)
  (hr : q.IsLineRec f x r)
include hx hr

omit hf hfr hf0 hf1 h8 hx in
theorem lr_closedL : @IsClosed S σ.topology r.2.1 := by
  letI := σ.topology
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  rw [← c.closure_IA h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7]; exact isClosed_closure

omit hf hfr hf0 hf1 h8 hx in
theorem lr_closedR : @IsClosed S σ.topology r.2.2 := by
  letI := σ.topology
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  rw [← c.closure_IB h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7]; exact isClosed_closure

omit hf hfr hf0 hf1 h1 h2 h3 h4 h5 h7 h8 in
theorem lr_union : r.2.1 ∪ r.2.2 = J ∪ I := by
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  apply subset_antisymm
  · have hxK := hx.sub_K q
    rintro z ((hz | ((hz | hz) | hz) | hz) | (hz | ((hz | hz) | hz) | hz))
    · exact Or.inr (c.IA_sub hz).1
    · exact Or.inl (q.sAB_sub (c.s₁_sub hz))
    · exact hxK hz
    · exact Or.inl (q.sCD_sub (c.t₁_sub hz))
    · exact Or.inl (q.sDA_sub hz)
    · exact Or.inr (c.IB_sub hz).1
    · exact Or.inl (q.sAB_sub (c.s₂_sub hz))
    · exact Or.inl (q.sBC_sub hz)
    · exact Or.inl (q.sCD_sub (c.t₂_sub hz))
    · exact hxK hz
  · rw [union_comm J]; exact c.sub_cl_union

omit hf hfr hf0 hf1 h8 hx in
theorem lr_line : r.2.1 ∩ r.2.2 = x := by
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  exact subset_antisymm (c.inter_cl h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7)
    (subset_inter c.x_sub_clA c.x_sub_clB)

omit hf hfr hf0 hf1 h8 hx in
theorem lr_frontL : x ⊆ @closure S σ.topology ((J ∪ I) \ r.2.1) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  refine c.x_sub_clB.trans ?_
  rw [← c.closure_IB h1 h2 h3 h4 h51 h7]
  refine closure_mono fun z hz => ⟨Or.inr (c.IB_sub hz).1, fun hzA => ?_⟩
  exact (c.IB_sub hz).2 (c.inter_cl h1 h2 h3 h4 h51 h7 ⟨hzA, Or.inl hz⟩)

omit hf hfr hf0 hf1 h8 hx in
theorem lr_frontR : x ⊆ @closure S σ.topology ((J ∪ I) \ r.2.2) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  refine c.x_sub_clA.trans ?_
  rw [← c.closure_IA h1 h2 h3 h4 h51 h7]
  refine closure_mono fun z hz => ⟨Or.inr (c.IA_sub hz).1, fun hzB => ?_⟩
  exact (c.IA_sub hz).2 (c.inter_cl h1 h2 h3 h4 h51 h7 ⟨Or.inl hz, hzB⟩)

omit h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hr in
theorem lr_conn : @IsPreconnected S σ.topology x := by
  letI := σ.topology
  obtain ⟨P, P', -, -, hxa, -⟩ := hx; exact hxa.isPreconnected

omit h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hx in
theorem lr_t : ∃ t : unitInterval, r.1 = t ∧ 0 < t ∧ t < 1 ∧ f t ∈ x := by
  obtain ⟨t, c, ht0, ht1, hft, -, -, rfl⟩ := hr
  exact ⟨t, rfl, ht0, ht1, hft⟩

include hf hfr hf0 hf1 in
omit h8 hf1 in
/-- Along `AB`, the `L`-side of the line is the part from `A` to its end. -/
theorem lr_fL (s : unitInterval) : f s ∈ r.2.1 ↔ (s : ℝ) ≤ r.1 := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨P, P', hP, hP', -, -, hxJ⟩ := hx.inter_J hIJ
  obtain ⟨t, c, -, -, hft, hs₁, -, rfl⟩ := hr
  have hfs : f s ∈ sAB := hfr ▸ mem_range_self s
  have hPt : f t = P := by
    rcases hxJ _ hft (q.sAB_sub (hfr ▸ mem_range_self t)) with h | h
    · exact h
    · exact absurd (h ▸ hfr ▸ mem_range_self t) (disjoint_right.mp q.ab_cd hP'.1)
  show f s ∈ c.clA ↔ (s : ℝ) ≤ t
  rw [Subtype.coe_le_coe]
  constructor
  · rintro (hz | ((hz | hz) | hz) | hz)
    · exact absurd (q.sAB_sub hfs) (disjoint_left.mp hIJ (c.IA_sub hz).1)
    · rw [hs₁] at hz
      obtain ⟨u, hu, hue⟩ := hz
      exact hf.injective hue ▸ hu.2
    · rcases hxJ _ hz (q.sAB_sub hfs) with h | h
      · exact le_of_eq (hf.injective (h.trans hPt.symm))
      · exact absurd (h ▸ hfs) (disjoint_right.mp q.ab_cd hP'.1)
    · exact absurd (c.t₁_sub hz) (disjoint_left.mp q.ab_cd hfs)
    · have : f s ∈ sDA ∩ sAB := ⟨hz, hfs⟩
      rw [q.da_ab, mem_singleton_iff, ← hf0] at this
      rw [hf.injective this]; exact unitInterval.nonneg'
  · intro hst
    exact Or.inr (Or.inl (Or.inl (Or.inl (hs₁ ▸ ⟨s, ⟨unitInterval.nonneg', hst⟩, rfl⟩))))

include hf hfr hf0 hf1 in
omit h8 hf0 in
/-- Along `AB`, the `R`-side of the line is the part from its end to `B`. -/
theorem lr_fR (s : unitInterval) : f s ∈ r.2.2 ↔ r.1 ≤ (s : ℝ) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨P, P', hP, hP', -, -, hxJ⟩ := hx.inter_J hIJ
  obtain ⟨t, c, -, -, hft, -, hs₂, rfl⟩ := hr
  have hfs : f s ∈ sAB := hfr ▸ mem_range_self s
  have hPt : f t = P := by
    rcases hxJ _ hft (q.sAB_sub (hfr ▸ mem_range_self t)) with h | h
    · exact h
    · exact absurd (h ▸ hfr ▸ mem_range_self t) (disjoint_right.mp q.ab_cd hP'.1)
  show f s ∈ c.clB ↔ (t : ℝ) ≤ s
  rw [Subtype.coe_le_coe]
  constructor
  · rintro (hz | ((hz | hz) | hz) | hz)
    · exact absurd (q.sAB_sub hfs) (disjoint_left.mp hIJ (c.IB_sub hz).1)
    · rw [hs₂] at hz
      obtain ⟨u, hu, hue⟩ := hz
      exact hf.injective hue ▸ hu.1
    · have : f s ∈ sAB ∩ sBC := ⟨hfs, hz⟩
      rw [q.ab_bc, mem_singleton_iff, ← hf1] at this
      rw [hf.injective this]; exact unitInterval.le_one'
    · exact absurd (c.t₂_sub hz) (disjoint_left.mp q.ab_cd hfs)
    · rcases hxJ _ hz (q.sAB_sub hfs) with h | h
      · exact le_of_eq (hf.injective (hPt.trans h.symm))
      · exact absurd (h ▸ hfs) (disjoint_right.mp q.ab_cd hP'.1)
  · intro hst
    exact Or.inr (Or.inl (Or.inl (Or.inl (hs₂ ▸ ⟨s, ⟨hst, unitInterval.le_one'⟩, rfl⟩))))

end Lines

section Mono

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {q : σ.Quad J I A B C D sAB sBC sCD sDA} {f : unitInterval → S}

/-- The two halves of a line record, as open connected sets. -/
theorem lr_halves {x : Set S} {r : ℝ × Set S × Set S} (hr : q.IsLineRec f x r) :
    ∃ U V : Set S, @IsOpen S σ.topology U ∧ @IsOpen S σ.topology V ∧
      @IsPreconnected S σ.topology U ∧ @IsPreconnected S σ.topology V ∧ Disjoint U V ∧
      I \ x = U ∪ V ∧ @closure S σ.topology U = r.2.1 ∧ @closure S σ.topology V = r.2.2 ∧
      sDA ⊆ r.2.1 ∧ sBC ⊆ r.2.2 ∧ Disjoint sDA r.2.2 ∧ Disjoint r.2.1 sBC := by
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨t, c, -, -, -, -, -, rfl⟩ := hr
  have jA := jordan h1 h2 h3 h4 h51 h7 c.qA.interior
  have jB := jordan h1 h2 h3 h4 h51 h7 c.qB.interior
  refine ⟨c.IA, c.IB, jA.1, jB.1, jA.2.1, jB.2.1, c.dis, c.split, c.closure_IA h1 h2 h3 h4 h51 h7,
    c.closure_IB h1 h2 h3 h4 h51 h7, fun z hz => Or.inr (Or.inr hz),
    fun z hz => Or.inr (Or.inl (Or.inl (Or.inr hz))), ?_, ?_⟩
  · have := c.closure_IB_disjoint_DA h1 h2 h3 h4 h51 h7
    rw [c.closure_IB h1 h2 h3 h4 h51 h7] at this; exact this.symm
  · have := c.closure_IA_disjoint_BC h1 h2 h3 h4 h51 h7
    rwa [c.closure_IA h1 h2 h3 h4 h51 h7] at this

variable (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A)
  (hf1 : f 1 = B)
include hf hfr hf0 hf1

omit hf1 in
/-- An arc disjoint from the line of `r` and starting after it on `AB` lies on its `R`-side and
misses its `L`-side. -/
theorem lr_side_of_disjoint {x x' : Set S} {r r' : ℝ × Set S × Set S}
    (hx : σ.XArc I sAB sCD A B C D x) (hx' : σ.XArc I sAB sCD A B C D x')
    (hr : q.IsLineRec f x r) (hr' : q.IsLineRec f x' r') (hd : Disjoint x x')
    (hlt : r.1 < r'.1) : x' ⊆ r.2.2 ∧ Disjoint r.2.1 x' := by
  letI := σ.topology
  have hu := lr_union hx hr
  have hl := lr_line h1 h2 h3 h4 h5 h7 hr
  obtain ⟨t', ht', -, -, hft'⟩ := lr_t hr'
  have hsub : x' ⊆ r.2.1 ∪ r.2.2 := hu ▸ hx'.sub_K q
  have hdis : r.2.1 ∩ r.2.2 ∩ x' = ∅ := by
    rw [hl]; exact disjoint_iff_inter_eq_empty.mp hd
  have hB : x' ⊆ r.2.2 := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (lr_conn hx') _ _
      (lr_closedL h1 h2 h3 h4 h5 h7 hr) (lr_closedR h1 h2 h3 h4 h5 h7 hr) hsub
      (by rw [inter_comm]; exact hdis) with h | h
    · have := (lr_fL h1 h2 h3 h4 h5 h7 hf hfr hf0 hx hr t').mp (h hft')
      linarith
    · exact h
  refine ⟨hB, disjoint_left.mpr fun z hzA hzx => ?_⟩
  have : z ∈ r.2.1 ∩ r.2.2 ∩ x' := ⟨⟨hzA, hB hzx⟩, hzx⟩
  rw [hdis] at this; exact this

omit hf0 in
/-- The symmetric statement: an arc starting before the line of `r'` lies on its `L`-side. -/
theorem lr_side_of_disjoint' {x x' : Set S} {r r' : ℝ × Set S × Set S}
    (hx : σ.XArc I sAB sCD A B C D x) (hx' : σ.XArc I sAB sCD A B C D x')
    (hr : q.IsLineRec f x r) (hr' : q.IsLineRec f x' r') (hd : Disjoint x x')
    (hlt : r.1 < r'.1) : x ⊆ r'.2.1 ∧ Disjoint x r'.2.2 := by
  letI := σ.topology
  have hu := lr_union hx' hr'
  have hl := lr_line h1 h2 h3 h4 h5 h7 hr'
  obtain ⟨t, ht, -, -, hft⟩ := lr_t hr
  have hsub : x ⊆ r'.2.1 ∪ r'.2.2 := hu ▸ hx.sub_K q
  have hdis : r'.2.1 ∩ r'.2.2 ∩ x = ∅ := by
    rw [hl]; exact disjoint_iff_inter_eq_empty.mp hd.symm
  have hA : x ⊆ r'.2.1 := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (lr_conn hx) _ _
      (lr_closedL h1 h2 h3 h4 h5 h7 hr') (lr_closedR h1 h2 h3 h4 h5 h7 hr') hsub
      (by rw [inter_comm]; exact hdis) with h | h
    · exact h
    · have := (lr_fR h1 h2 h3 h4 h5 h7 hf hfr hf1 hx' hr' t).mp (h hft)
      linarith
  refine ⟨hA, disjoint_left.mpr fun z hzx hzB => ?_⟩
  have : z ∈ r'.2.1 ∩ r'.2.2 ∩ x := ⟨⟨hA hzx, hzB⟩, hzx⟩
  rw [hdis] at this; exact this

/-- **Nesting of lines.** Of two disjoint arcs, the one starting first on `AB` has the smaller
`L`-side and the larger `R`-side, and its `L`-side misses the other's `R`-side. -/
theorem lr_mono {x x' : Set S} {r r' : ℝ × Set S × Set S}
    (hx : σ.XArc I sAB sCD A B C D x) (hx' : σ.XArc I sAB sCD A B C D x')
    (hr : q.IsLineRec f x r) (hr' : q.IsLineRec f x' r') (hd : Disjoint x x')
    (hlt : r.1 < r'.1) : r.2.1 ⊆ r'.2.1 ∧ r'.2.2 ⊆ r.2.2 ∧ Disjoint r.2.1 r'.2.2 := by
  letI := σ.topology
  obtain ⟨hx'B, hAx'⟩ := lr_side_of_disjoint h1 h2 h3 h4 h5 h7 hf hfr hf0 hx hx' hr hr' hd hlt
  obtain ⟨hxA', hxB'⟩ :=
    lr_side_of_disjoint' h1 h2 h3 h4 h5 h7 hf hfr hf1 hx hx' hr hr' hd hlt
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, hsplit, hUcl, hVcl, -⟩ :=
    lr_halves h1 h2 h3 h4 h5 h7 hr
  obtain ⟨U', V', hUo', hVo', hUc', hVc', hUV', hsplit', hUcl', hVcl', -⟩ :=
    lr_halves h1 h2 h3 h4 h5 h7 hr'
  obtain ⟨t, ht, ht0, ht1, -⟩ := lr_t hr
  obtain ⟨t', ht', ht0', ht1', -⟩ := lr_t hr'
  have fL := lr_fL h1 h2 h3 h4 h5 h7 hf hfr hf0 hx hr
  have fR' := lr_fR h1 h2 h3 h4 h5 h7 hf hfr hf1 hx' hr'
  have fL' := lr_fL h1 h2 h3 h4 h5 h7 hf hfr hf0 hx' hr'
  have fR := lr_fR h1 h2 h3 h4 h5 h7 hf hfr hf1 hx hr
  have hUI : U ⊆ I := fun z hz => ((hsplit.symm ▸ Or.inl hz : z ∈ I \ x)).1
  have hV'I : V' ⊆ I := fun z hz => ((hsplit'.symm ▸ Or.inr hz : z ∈ I \ x')).1
  have h1' : r.2.1 ⊆ r'.2.1 := by
    have hU : U ⊆ U' ∪ V' := fun z hz => by
      rw [← hsplit']
      exact ⟨hUI hz, fun h => disjoint_left.mp hAx' (hUcl ▸ subset_closure hz) h⟩
    rcases hUc.subset_or_subset hUo' hVo' hUV' hU with h | h
    · rw [← hUcl, ← hUcl']; exact closure_mono h
    · exfalso
      have h0 : f 0 ∈ r.2.1 := (fL 0).mpr (by rw [ht]; exact unitInterval.nonneg')
      rw [← hUcl] at h0
      have := (fR' 0).mp (hVcl' ▸ closure_mono h h0)
      rw [ht'] at this
      exact absurd (le_antisymm this unitInterval.nonneg') (ne_of_gt ht0')
  have h2' : r'.2.2 ⊆ r.2.2 := by
    have hV : V' ⊆ U ∪ V := fun z hz => by
      rw [← hsplit]
      exact ⟨hV'I hz, fun h => disjoint_left.mp hxB' h (hVcl' ▸ subset_closure hz)⟩
    rcases hVc'.subset_or_subset hUo hVo hUV hV with h | h
    · exfalso
      have h0 : f 1 ∈ r'.2.2 := (fR' 1).mpr (by rw [ht']; exact unitInterval.le_one')
      rw [← hVcl'] at h0
      have := (fL 1).mp (hUcl ▸ closure_mono h h0)
      rw [ht] at this
      exact absurd (le_antisymm unitInterval.le_one' this) (ne_of_lt ht1)
    · rw [← hVcl, ← hVcl']; exact closure_mono h
  refine ⟨h1', h2', disjoint_left.mpr fun z hzA hzB' => ?_⟩
  have : z ∈ r'.2.1 ∩ r'.2.2 := ⟨h1' hzA, hzB'⟩
  rw [lr_line h1 h2 h3 h4 h5 h7 hr'] at this
  exact disjoint_left.mp hAx' hzA this

end Mono

end HPC.Moore
