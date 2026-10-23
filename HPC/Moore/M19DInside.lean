import HPC.Moore.M19DChords

/-!
# Moore 1919, Theorem D: a closed curve within `ABCDA`

**Theorem** (`inside_rulable`). If the closed curve `h` lies within `ABCDA`, there is a ruling of
`ABCDA` none of whose subdivisions meets `h`.

An arc `x` from a point `P` of the open side `AB` to a point `H` of the open side `CD` is built
from an arc `Pa` meeting `h` only in `a`, an arc `ab` of `h`, and an arc `bH` meeting `h` only in
`b` and missing `Pa` (it is drawn in `I − Pa`, connected by Theorem 33). The other arc of `h` from
`a` to `b` is then a chord of one half of the cut along `x`; the other half meets `h` nowhere.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

include h1 h3 h4 h5 in
/-- An open side contains a point. -/
theorem Space.Quad.exists_side_point (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    (sAB \ {A, B}).Nonempty := by
  letI := σ.topology
  exact ((isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp q.ab).nonempty_diff

include h1 h2 h3 h4 h5 in
/-- **Access to the open side `AB`** from a connected open subset `R` of `I` whose boundary lies on
`J` and a closed set `Z`, `Z` missing some point of the open side `AB` on the boundary of `R`. -/
theorem Space.Quad.side_access (q : σ.Quad J I A B C D sAB sBC sCD sDA) {R Z : Set S}
    (hRo : @IsOpen S σ.topology R) (hRc : @IsPreconnected S σ.topology R)
    (hZ : @IsClosed S σ.topology Z) (hfr : @frontier S σ.topology R ⊆ J ∪ Z) {Q : S}
    (hQ : Q ∈ sAB \ {A, B}) (hQZ : Q ∉ Z) (hQR : Q ∈ @frontier S σ.topology R) {F : S}
    (hF : F ∈ R) : ∃ H ∈ sAB \ {A, B}, ∃ γ, @TArc S σ.topology F H γ ∧ γ \ {H} ⊆ R := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  have cl : ∀ {E F : S} {s : Set S}, σ.IsArc E F s → IsClosed s := fun hs =>
    ((isArc_iff_tarc h1 h3 h4 h51).mp hs).isClosed
  set N := (sBC ∪ sCD ∪ sDA ∪ Z)ᶜ
  have hNo : IsOpen N := ((((cl q.bc).union (cl q.cd)).union (cl q.da)).union hZ).isOpen_compl
  obtain ⟨hQAB, hQn⟩ := hQ
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hQn
  have hQN : Q ∈ N := by
    simp only [N, mem_compl_iff, mem_union, not_or]
    refine ⟨⟨⟨fun h => hQn.2 ?_, fun h => ?_⟩, fun h => hQn.1 ?_⟩, hQZ⟩
    · exact Space.Quad.Cut.single hQAB h q.ab_bc
    · exact disjoint_left.mp q.ab_cd hQAB h
    · exact Space.Quad.Cut.single h hQAB q.da_ab
  obtain ⟨H, ⟨hHfr, hHN⟩, γ, hγ, hγR⟩ := exists_access harc hRo hRc hF hQR (hNo.mem_nhds hQN)
  refine ⟨H, ?_, γ, hγ, hγR⟩
  simp only [N, mem_compl_iff, mem_union, not_or] at hHN
  obtain ⟨⟨⟨hHBC, hHCD⟩, hHDA⟩, hHZ⟩ := hHN
  rcases hfr hHfr with hHJ | hHZ'
  · rw [← q.union] at hHJ
    rcases hHJ with ((hH | hH) | hH) | hH
    · refine ⟨hH, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => hHDA (e ▸ q.da.right_mem), fun e => hHBC (e ▸ q.bc.left_mem)⟩
    · exact absurd hH hHBC
    · exact absurd hH hHCD
    · exact absurd hH hHDA
  · exact absurd hHZ' hHZ

end Ax

section Inside

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **A closed curve within `ABCDA`**: there is a ruling of `ABCDA` none of whose subdivisions
meets it. -/
theorem inside_rulable (q : σ.Quad J I A B C D sAB sBC sCD sDA) {h W : Set S}
    (hW : σ.IsInteriorOf h W) (hhI : h ⊆ I) :
    σ.Rulable (fun U => Disjoint U h) I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, hIc, -, hfrI, -, -, -, -, hclI, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hhcpt, hht⟩ := jordan h1 h2 h3 h4 h51 h7 hW
  have hhc : IsClosed h := hhcpt.isClosed
  obtain ⟨a₀, b₀, C₁, C₂, hC₁, -, -, hhe⟩ := hht
  have ha₀ : a₀ ∈ h := hhe ▸ Or.inl hC₁.left_mem
  have hb₀ : b₀ ∈ h := hhe ▸ Or.inl hC₁.right_mem
  have hJh : ∀ {z}, z ∈ J → z ∉ h := fun hz hzh => disjoint_left.mp hIJ (hhI hzh) hz
  have hAB : ∀ {z}, z ∈ sAB → z ∈ J := fun hz => q.union ▸ Or.inl (Or.inl (Or.inl hz))
  have hCD : ∀ {z}, z ∈ sCD → z ∈ J := fun hz => q.union ▸ Or.inl (Or.inr hz)
  -- the arc `Pa`
  obtain ⟨Q, hQ⟩ := q.exists_side_point h1 h3 h4 h5
  have hQJ : Q ∈ J := hAB hQ.1
  obtain ⟨P, hP, β, hβ, hβI⟩ := q.side_access h1 h2 h3 h4 h5 hIo hIc isClosed_empty
    (by rw [hfrI]; exact subset_union_left) hQ (notMem_empty Q) (hfrI ▸ hQJ)
    (hhI ha₀)
  have hPJ : P ∈ J := hAB hP.1
  obtain ⟨a, hah, K₁, hK₁β, hK₁, hK₁h⟩ := hβ.symm.first_point hhc
    ⟨a₀, hβ.left_mem, ha₀⟩ (hJh hPJ)
  have hK₁I : K₁ \ {P} ⊆ I := fun z hz => hβI ⟨hK₁β hz.1, hz.2⟩
  -- a second point of `h`
  obtain ⟨z₁, hz₁h, hz₁a⟩ : ∃ z ∈ h, z ≠ a := by
    by_cases e : a₀ = a
    · exact ⟨b₀, hb₀, fun e' => hC₁.ne (e.trans e'.symm)⟩
    · exact ⟨a₀, ha₀, e⟩
  have hz₁K : z₁ ∉ K₁ := fun hz => hz₁a (Space.Quad.Cut.single hz hz₁h hK₁h)
  -- the region `I − Pa`
  have hK₁c : IsClosed K₁ := hK₁.isClosed
  have hRo : IsOpen (I \ K₁) := hIo.sdiff hK₁c
  have hRc : IsPreconnected (I \ K₁) :=
    hair_isPreconnected h1 h2 h3 h4 h5 h6 h7 h8 hIo hIc (disjoint_right.mp hIJ hPJ) (hhI hah) hK₁ hK₁I
  have hK₁J : ∀ {z}, z ∈ K₁ → z ∈ J → z = P := by
    intro z hz hzJ
    by_contra hne
    exact disjoint_left.mp hIJ (hK₁I ⟨hz, hne⟩) hzJ
  have q2 := q.rot.rot
  obtain ⟨Q', hQ'⟩ := q2.exists_side_point h1 h3 h4 h5
  have hQ'J : Q' ∈ J := hCD hQ'.1
  have hQ'K : Q' ∉ K₁ := by
    intro hz
    have := hK₁J hz hQ'J
    subst this
    exact disjoint_left.mp q.ab_cd hP.1 hQ'.1
  have hfrR : frontier (I \ K₁) ⊆ J ∪ K₁ := by
    intro z hz
    rw [diff_eq] at hz
    rcases frontier_inter_subset _ _ hz with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact Or.inl (hfrI ▸ hz)
    · rw [frontier_compl] at hz; exact Or.inr (hK₁c.frontier_subset hz)
  have hQ'fr : Q' ∈ frontier (I \ K₁) := by
    refine ⟨?_, fun hi => disjoint_left.mp hIJ (interior_subset hi).1 hQ'J⟩
    have hQcl : Q' ∈ closure I := hclI ▸ Or.inr hQ'J
    rw [diff_eq, inter_comm]
    exact hK₁c.isOpen_compl.inter_closure ⟨hQ'K, hQcl⟩
  obtain ⟨H, hH, γ, hγ, hγR⟩ := q2.side_access h1 h2 h3 h4 h5 hRo hRc hK₁c hfrR hQ' hQ'K hQ'fr
    ⟨hhI hz₁h, hz₁K⟩
  have hHJ : H ∈ J := hCD hH.1
  obtain ⟨b, hbh, K₃, hK₃γ, hK₃, hK₃h⟩ := hγ.symm.first_point hhc ⟨z₁, hγ.left_mem, hz₁h⟩ (hJh hHJ)
  have hK₃R : K₃ \ {H} ⊆ I \ K₁ := fun z hz => hγR ⟨hK₃γ hz.1, hz.2⟩
  have hK₁K₃ : Disjoint K₁ K₃ := by
    refine disjoint_left.mpr fun z hz1 hz3 => ?_
    by_cases hzH : z = H
    · subst hzH
      have := hK₁J hz1 hHJ
      subst this
      exact disjoint_left.mp q.ab_cd hP.1 hH.1
    · exact (hK₃R ⟨hz3, hzH⟩).2 hz1
  have hab : a ≠ b := fun e => disjoint_left.mp hK₁K₃ (hK₁.right_mem) (e ▸ hK₃.right_mem)
  -- the two arcs of `h` from `a` to `b`
  obtain ⟨E₁, E₂, hE₁, hE₂, hEi, hEu, -⟩ := fa_scc_two_arcs h1 h3 h4 h51 hW.1 hah hbh hab
  rw [isArc_iff_tarc h1 h3 h4 h51] at hE₁ hE₂
  have hE₁h : E₁ ⊆ h := hEu ▸ subset_union_left
  have hE₂h : E₂ ⊆ h := hEu ▸ subset_union_right
  -- the arc `x`
  have hx₁ : TArc P b (K₁ ∪ E₁) := by
    refine hK₁.union hE₁ (subset_antisymm ?_ ?_)
    · rintro z ⟨hz1, hz2⟩; exact Space.Quad.Cut.single hz1 (hE₁h hz2) hK₁h ▸ rfl
    · rintro z rfl; exact ⟨hK₁.right_mem, hE₁.left_mem⟩
  have hx : TArc P H (K₁ ∪ E₁ ∪ K₃) := by
    refine hx₁.union hK₃.symm (subset_antisymm ?_ ?_)
    · rintro z ⟨hz1 | hz1, hz3⟩
      · exact absurd hz3 (disjoint_left.mp hK₁K₃ hz1)
      · exact Space.Quad.Cut.single hz3 (hE₁h hz1) hK₃h ▸ rfl
    · rintro z rfl; exact ⟨Or.inr hE₁.right_mem, hK₃.right_mem⟩
  set x := K₁ ∪ E₁ ∪ K₃
  have hxI : x \ {P, H} ⊆ I := by
    rintro z ⟨(hz | hz) | hz, hzn⟩
    · exact hK₁I ⟨hz, fun e => hzn (Or.inl e)⟩
    · exact hhI (hE₁h hz)
    · exact (hK₃R ⟨hz, fun e => hzn (Or.inr e)⟩).1
  have hxq : σ.XArc I sAB sCD A B C D x := ⟨P, H, hP, hH, hx, hxI⟩
  obtain ⟨c⟩ := q.exists_cut h1 h2 h3 h4 h5 h7 h8 hxq
  -- the other arc of `h` is a chord of one half
  have hE₂x : E₂ \ {a, b} ⊆ I \ x := by
    rintro z ⟨hz, hzn⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzn
    refine ⟨hhI (hE₂h hz), ?_⟩
    rintro ((hz' | hz') | hz')
    · exact hzn.1 (Space.Quad.Cut.single hz' (hE₂h hz) hK₁h)
    · have : z ∈ E₁ ∩ E₂ := ⟨hz', hz⟩
      rw [hEi] at this
      rcases this with e | e
      · exact hzn.1 e
      · exact hzn.2 e
    · exact hzn.2 (Space.Quad.Cut.single hz' (hE₂h hz) hK₃h)
  have hnc : ∀ {e}, e ∈ I → e ∉ ({A, B, C, D, c.X, c.X'} : Set S) := by
    intro e heI he
    have hJ' : e ∈ J := by
      simp only [mem_insert_iff, mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hAB q.ab.left_mem
      · exact hAB q.ab.right_mem
      · exact hCD q.cd.left_mem
      · exact hCD q.cd.right_mem
      · exact hAB (c.s₁_sub c.qA.ab.right_mem)
      · exact hCD (c.t₁_sub c.qA.cd.left_mem)
    exact disjoint_left.mp hIJ heI hJ'
  have hax : a ∈ x := Or.inl (Or.inr hE₁.left_mem)
  have hbx : b ∈ x := Or.inl (Or.inr hE₁.right_mem)
  have hEx : E₁ ⊆ x := fun z hz => Or.inl (Or.inr hz)
  have key := c.chord_half h1 h2 h3 h4 h5 h7 hE₂ hE₂x (Or.inr hax) (Or.inr hbx)
    (hnc (hhI hah)) (hnc (hhI hbh))
  suffices H' : σ.Rulable (fun U => Disjoint U (⋃₀ {h})) I sAB sBC sCD sDA A B C D by
    simpa using H'
  have hxIA : Disjoint x c.IA := disjoint_left.mpr fun z hz hzA => (c.IA_sub hzA).2 hz
  have hxIB : Disjoint x c.IB := disjoint_left.mpr fun z hz hzB => (c.IB_sub hzB).2 hz
  rcases key with ⟨hcl, hch⟩ | ⟨hcl, hch⟩
  · refine c.glue_chords h1 h2 h3 h4 h5 h6 h7 h8 hxq (TA := {E₂}) (TB := ∅)
      (chords_rulable h1 h2 h3 h4 h5 h6 h7 h8 c.qA (finite_singleton _) (by simpa using hch)
        (pairwise_singleton _ _))
      (c.qB.rulable_of_good h1 h2 h3 h4 h5 h7 (by simp)) ?_ ?_
    · rintro z ⟨hz, hzA⟩
      simp only [sUnion_singleton] at hz ⊢
      rw [← hEu] at hz
      rcases hz with hz | hz
      · exact absurd hzA (disjoint_left.mp hxIA (hEx hz))
      · exact hz
    · rintro z ⟨hz, hzB⟩
      simp only [sUnion_singleton] at hz
      rw [← hEu] at hz
      rcases hz with hz | hz
      · exact absurd hzB (disjoint_left.mp hxIB (hEx hz))
      · exact absurd hzB (disjoint_left.mp (c.clA_disj_IB h1 h2 h3 h4 h5 h7 hcl) hz)
  · refine c.glue_chords h1 h2 h3 h4 h5 h6 h7 h8 hxq (TA := ∅) (TB := {E₂})
      (c.qA.rulable_of_good h1 h2 h3 h4 h5 h7 (by simp))
      (chords_rulable h1 h2 h3 h4 h5 h6 h7 h8 c.qB (finite_singleton _) (by simpa using hch)
        (pairwise_singleton _ _)) ?_ ?_
    · rintro z ⟨hz, hzA⟩
      simp only [sUnion_singleton] at hz
      rw [← hEu] at hz
      rcases hz with hz | hz
      · exact absurd hzA (disjoint_left.mp hxIA (hEx hz))
      · exact absurd hzA (disjoint_left.mp (c.clB_disj_IA h1 h2 h3 h4 h5 h7 hcl) hz)
    · rintro z ⟨hz, hzB⟩
      simp only [sUnion_singleton] at hz ⊢
      rw [← hEu] at hz
      rcases hz with hz | hz
      · exact absurd hzB (disjoint_left.mp hxIB (hEx hz))
      · exact hz

end Inside

end HPC.Moore
