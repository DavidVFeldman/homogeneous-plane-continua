import HPC.Moore.M19CDSplit

/-!
# Moore 1919: rulings as sets of arcs; cutting a ruling along one of its arcs (batch 141, item E)

`Space.ArcRuling` is a double ruling given by its two *sets* of arcs, with no order and no indexing:
a finite set `𝒳` of mutually exclusive arcs from the open side `AB` to the open side `CD`, a finite
set `𝒴` of mutually exclusive arcs from the open side `BC` to the open side `DA`, all within
`ABCDA` except for their ends, each arc of `𝒳` having just one point in common with each arc of
`𝒴`. (`HPC/Moore/M19CDOrder.lean` shows that these are exactly the double rulings of the
commission, up to indexing.) Its subdivisions are the components of `I − ⋃ arcs`
(`Space.cellsOf`).

`Space.Quad.Cut` packages the two quadrilaterals into which an arc `x` from `AB` to `CD` cuts
`ABCDA` (`Space.Quad.splitX`, `Space.Quad.exists_cut`); `Space.ArcRuling.restrict_half` cuts a
ruling containing `x` into a ruling of a half (used for both halves in `HPC/Moore/M19CDCut.lean`;
`Space.Quad.Cut.cells_split`, in `HPC/Moore/M19CDRefine.lean`, shows that the subdivisions are
those of the two halves).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- An arc from a point of the open side `AB` to a point of the open side `CD`, lying within `I`
except for its ends. -/
def Space.XArc (σ : Space S) (I sAB sCD : Set S) (A B C D : S) (x : Set S) : Prop :=
  ∃ P P', P ∈ sAB \ {A, B} ∧ P' ∈ sCD \ {C, D} ∧ @TArc S σ.topology P P' x ∧ x \ {P, P'} ⊆ I

/-- A *double ruling* of `ABCDA` given by its two sets of arcs. -/
structure Space.ArcRuling (σ : Space S) (I sAB sBC sCD sDA : Set S) (A B C D : S)
    (𝒳 𝒴 : Set (Set S)) : Prop where
  finX : 𝒳.Finite
  finY : 𝒴.Finite
  arcX : ∀ x ∈ 𝒳, σ.XArc I sAB sCD A B C D x
  arcY : ∀ y ∈ 𝒴, σ.XArc I sBC sDA B C D A y
  disjX : 𝒳.Pairwise Disjoint
  disjY : 𝒴.Pairwise Disjoint
  cross : ∀ x ∈ 𝒳, ∀ y ∈ 𝒴, ∃! P, P ∈ x ∩ y

/-- The *subdivisions* of `U` by `G`: the components of `U − G`. -/
def Space.cellsOf (σ : Space S) (U G : Set S) : Set (Set S) :=
  letI := σ.topology
  {V | ∃ z ∈ U \ G, V = connectedComponentIn (U \ G) z}

theorem Space.XArc.symm (h1 : σ.Axiom1) {I sAB sCD : Set S} {A B C D : S} {x : Set S}
    (h : σ.XArc I sAB sCD A B C D x) : σ.XArc I sCD sAB C D A B x := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨P, P', hP, hP', hx, hxI⟩ := h
  exact ⟨P', P, hP', hP, hx.symm, by rwa [pair_comm]⟩

theorem Space.XArc.mono {I I' sAB sCD : Set S} {A B C D : S} {x : Set S}
    (h : σ.XArc I sAB sCD A B C D x) (hI : I ⊆ I') : σ.XArc I' sAB sCD A B C D x := by
  obtain ⟨P, P', hP, hP', hx, hxI⟩ := h
  exact ⟨P, P', hP, hP', hx, hxI.trans hI⟩

/-- **Rotation of a ruling**: a ruling of `ABCDA` is a ruling of `BCDAB`, the two sets of arcs
exchanging roles. -/
theorem Space.ArcRuling.rot (h1 : σ.Axiom1) {I sAB sBC sCD sDA : Set S} {A B C D : S} {𝒳 𝒴 : Set (Set S)}
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) :
    σ.ArcRuling I sBC sCD sDA sAB B C D A 𝒴 𝒳 where
  finX := R.finY
  finY := R.finX
  arcX := R.arcY
  arcY x hx := (R.arcX x hx).symm h1
  disjX := R.disjY
  disjY := R.disjX
  cross y hy x hx := by simpa only [inter_comm] using R.cross x hx y hy

theorem Space.cellsOf_mono {U G G' : Set S} (hG : G ⊆ G') {V : Set S} (hV : V ∈ σ.cellsOf U G') :
    ∃ W ∈ σ.cellsOf U G, V ⊆ W := by
  letI := σ.topology
  obtain ⟨z, hz, rfl⟩ := hV
  exact ⟨_, ⟨z, ⟨hz.1, fun h => hz.2 (hG h)⟩, rfl⟩,
    connectedComponentIn_mono _ (diff_subset_diff_right hG)⟩

/-- Components of a union of two mutually exclusive open sets. -/
theorem connectedComponentIn_union_left [TopologicalSpace S] {U₁ U₂ : Set S} (h₁ : IsOpen U₁)
    (h₂ : IsOpen U₂) (hd : Disjoint U₁ U₂) {z : S} (hz : z ∈ U₁) :
    connectedComponentIn (U₁ ∪ U₂) z = connectedComponentIn U₁ z := by
  apply subset_antisymm
  · have hsub : connectedComponentIn (U₁ ∪ U₂) z ⊆ U₁ :=
      (isPreconnected_connectedComponentIn).subset_left_of_subset_union h₁ h₂ hd
        (connectedComponentIn_subset _ _) ⟨z, mem_connectedComponentIn (Or.inl hz), hz⟩
    exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn (Or.inl hz)) hsub
  · exact connectedComponentIn_mono _ subset_union_left

theorem Space.cellsOf_union {U G U₁ G₁ U₂ G₂ : Set S}
    (hU : U \ G = (U₁ \ G₁) ∪ (U₂ \ G₂)) (ho₁ : @IsOpen S σ.topology (U₁ \ G₁))
    (ho₂ : @IsOpen S σ.topology (U₂ \ G₂)) (hd : Disjoint (U₁ \ G₁) (U₂ \ G₂)) :
    σ.cellsOf U G = σ.cellsOf U₁ G₁ ∪ σ.cellsOf U₂ G₂ := by
  letI := σ.topology
  ext V
  simp only [Space.cellsOf, mem_union, mem_setOf_eq]
  rw [hU]
  constructor
  · rintro ⟨z, hz | hz, rfl⟩
    · exact Or.inl ⟨z, hz, connectedComponentIn_union_left ho₁ ho₂ hd hz⟩
    · refine Or.inr ⟨z, hz, ?_⟩
      rw [union_comm]; exact connectedComponentIn_union_left ho₂ ho₁ hd.symm hz
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Or.inl hz, (connectedComponentIn_union_left ho₁ ho₂ hd hz).symm⟩
    · refine ⟨z, Or.inr hz, ?_⟩
      rw [union_comm]; exact (connectedComponentIn_union_left ho₂ ho₁ hd.symm hz).symm

namespace Space.Quad

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **The cut of `ABCDA` along an arc `x` from `AB` to `CD`**: `x` runs from `X ∈ AB` to
`X′ ∈ CD`, `AB = s₁ + s₂` and `CD = t₁ + t₂` with `s₁ = AX`, `t₁ = DX′`, and `AXX′DA` (interior
`IA`) and `XBCX′X` (interior `IB`) are quadrilaterals with `I − x = IA + IB`. -/
structure Cut (_q : σ.Quad J I A B C D sAB sBC sCD sDA) (x : Set S) where
  X : S
  X' : S
  s₁ : Set S
  s₂ : Set S
  t₁ : Set S
  t₂ : Set S
  IA : Set S
  IB : Set S
  qA : σ.Quad (s₁ ∪ x ∪ t₁ ∪ sDA) IA A X X' D s₁ x t₁ sDA
  qB : σ.Quad (s₂ ∪ sBC ∪ t₂ ∪ x) IB X B C X' s₂ sBC t₂ x
  hs : s₁ ∪ s₂ = sAB
  hsi : s₁ ∩ s₂ = {X}
  ht : t₁ ∪ t₂ = sCD
  hti : t₁ ∩ t₂ = {X'}
  split : I \ x = IA ∪ IB
  dis : Disjoint IA IB

theorem exists_cut (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    {x : Set S} (hx : σ.XArc I sAB sCD A B C D x) : Nonempty (q.Cut x) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨P, P', ⟨hP, hPAB⟩, ⟨hP', hP'CD⟩, hxa, hxI⟩ := hx
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp q.ab
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp q.cd).symm
  obtain ⟨t, rfl⟩ : P ∈ range f := hfr ▸ hP
  obtain ⟨s, rfl⟩ : P' ∈ range g := hgr ▸ hP'
  have ht0 : 0 < t := lt_of_le_of_ne nonneg' fun e => hPAB (Or.inl (by rw [← e, hf0]))
  have ht1 : t < 1 := lt_of_le_of_ne le_one' fun e => hPAB (Or.inr (by rw [e, hf1]; exact mem_singleton _))
  have hs0 : 0 < s := lt_of_le_of_ne nonneg' fun e => hP'CD (Or.inr (by rw [← e, hg0]; exact mem_singleton _))
  have hs1 : s < 1 := lt_of_le_of_ne le_one' fun e => hP'CD (Or.inl (by rw [e, hg1]))
  obtain ⟨IA, IB, qA, qB, hsplit, hdis⟩ :=
    q.splitX h1 h2 h3 h4 h5 h7 h8 hf hfr hf0 hf1 hg hgr hg0 hg1 ht0 ht1 hs0 hs1 hxa hxI
  refine ⟨⟨f t, g s, _, _, _, _, IA, IB, qA, qB, ?_, ?_, ?_, ?_, hsplit, hdis⟩⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc ht0.le ht1.le, unitInterval_Icc_zero_one, image_univ,
      hfr]
  · rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton ht0.le ht1.le, image_singleton]
  · rw [← image_union, Icc_union_Icc_eq_Icc hs0.le hs1.le, unitInterval_Icc_zero_one, image_univ,
      hgr]
  · rw [← image_inter hg.injective, Icc_inter_Icc_eq_singleton hs0.le hs1.le, image_singleton]

end Space.Quad

namespace Space.Quad

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Reflection**: `ABCDA` is also the quadrilateral `BADCB`. -/
theorem refl (q : σ.Quad J I A B C D sAB sBC sCD sDA) : σ.Quad J I B A D C sAB sDA sCD sBC where
  interior := q.interior
  ab := q.ab.symm
  bc := q.da.symm
  cd := q.cd.symm
  da := q.bc.symm
  union := by rw [← q.union]; ext; simp only [mem_union]; tauto
  ab_bc := by rw [inter_comm]; exact q.da_ab
  bc_cd := by rw [inter_comm]; exact q.cd_da
  cd_da := by rw [inter_comm]; exact q.bc_cd
  da_ab := by rw [inter_comm]; exact q.ab_bc
  ab_cd := q.ab_cd
  bc_da := q.bc_da.symm

/-- A point of the open side `AB` is on no other side. -/
theorem notMem_of_ab (q : σ.Quad J I A B C D sAB sBC sCD sDA) {z : S} (hz : z ∈ sAB \ {A, B}) :
    z ∉ sBC ∧ z ∉ sCD ∧ z ∉ sDA := by
  obtain ⟨hz, hzAB⟩ := hz
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzAB
  refine ⟨fun h => hzAB.2 ?_, fun h => disjoint_left.mp q.ab_cd hz h, fun h => hzAB.1 ?_⟩
  · have : z ∈ sAB ∩ sBC := ⟨hz, h⟩
    rw [q.ab_bc] at this; exact this
  · have : z ∈ sDA ∩ sAB := ⟨h, hz⟩
    rw [q.da_ab] at this; exact this

theorem notMem_of_bc (q : σ.Quad J I A B C D sAB sBC sCD sDA) {z : S} (hz : z ∈ sBC \ {B, C}) :
    z ∉ sCD ∧ z ∉ sDA ∧ z ∉ sAB := q.rot.notMem_of_ab hz

theorem notMem_of_cd (q : σ.Quad J I A B C D sAB sBC sCD sDA) {z : S} (hz : z ∈ sCD \ {C, D}) :
    z ∉ sDA ∧ z ∉ sAB ∧ z ∉ sBC := q.rot.rot.notMem_of_ab hz

theorem notMem_of_da (q : σ.Quad J I A B C D sAB sBC sCD sDA) {z : S} (hz : z ∈ sDA \ {D, A}) :
    z ∉ sAB ∧ z ∉ sBC ∧ z ∉ sCD := q.rot.rot.rot.notMem_of_ab hz

end Space.Quad

theorem Space.XArc.inter_J {J I sAB sCD : Set S} {A B C D : S} {x : Set S}
    (h : σ.XArc I sAB sCD A B C D x) (hIJ : Disjoint I J) :
    ∃ P P', P ∈ sAB \ {A, B} ∧ P' ∈ sCD \ {C, D} ∧ @TArc S σ.topology P P' x ∧
      x \ {P, P'} ⊆ I ∧ ∀ z ∈ x, z ∈ J → z = P ∨ z = P' := by
  obtain ⟨P, P', hP, hP', hx, hxI⟩ := h
  refine ⟨P, P', hP, hP', hx, hxI, fun z hz hzJ => ?_⟩
  by_contra hne
  simp only [not_or] at hne
  exact disjoint_left.mp hIJ (hxI ⟨hz, by simp [hne.1, hne.2]⟩) hzJ

theorem Space.ArcRuling.rule_refl (h1 : σ.Axiom1) {I sAB sBC sCD sDA : Set S} {A B C D : S}
    {𝒳 𝒴 : Set (Set S)} (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) :
    σ.ArcRuling I sAB sDA sCD sBC B A D C 𝒳 𝒴 where
  finX := R.finX
  finY := R.finY
  arcX x hx := by
    obtain ⟨P, P', hP, hP', hxa, hxI⟩ := R.arcX x hx
    exact ⟨P, P', by rwa [pair_comm], by rwa [pair_comm], hxa, hxI⟩
  arcY y hy := by
    obtain ⟨Q, Q', hQ, hQ', hya, hyI⟩ := (R.arcY y hy).symm h1
    exact ⟨Q, Q', by rwa [pair_comm], by rwa [pair_comm], hya, hyI⟩
  disjX := R.disjX
  disjY := R.disjY
  cross := R.cross

section Restrict

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
  (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7)
include h1 h2 h3 h4 h51 h7

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {𝒳 𝒴 : Set (Set S)}

/-- An arc of a ruling other than `x` lies, in a half `I′` of `I − x`, on `I′` and its boundary, or
does not meet `I′`. -/
theorem Space.ArcRuling.side_of_cut (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {x : Set S} (hx : x ∈ 𝒳)
    {X X' : S} {s₁ t₁ J' I' I'' : Set S} (q' : σ.Quad J' I' A X X' D s₁ x t₁ sDA)
    (hsplit : I \ x = I' ∪ I'') (hI'' : @IsOpen S σ.topology I'') (hdis : Disjoint I' I'')
    {w : Set S} (hw : w ∈ 𝒳) (hwx : w ≠ x) : w ⊆ I' ∪ J' ∨ w ∩ I' = ∅ := by
  letI := σ.topology
  obtain ⟨hI'o, -, -, -, -, -, -, -, hclI', -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q'.interior
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  obtain ⟨P, P', ⟨hP, -⟩, ⟨hP', -⟩, hwa, hwI⟩ := R.arcX w hw
  have hwx' : Disjoint w x := R.disjX hw hx hwx
  have hsub : w \ {P, P'} ⊆ I' ∪ I'' := by
    rw [← hsplit]
    exact fun z hz => ⟨hwI hz, fun hzx => disjoint_left.mp hwx' hz.1 hzx⟩
  rcases hwa.isPreconnected_diff.subset_or_subset hI'o hI'' hdis hsub with h | h
  · left
    rw [← hclI']
    exact hwa.subset_closure_diff.trans (closure_mono h)
  · right
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hzw, hzI'⟩
    by_cases hz : z = P ∨ z = P'
    · rcases hz with rfl | rfl
      · exact disjoint_left.mp hIJ ((hsplit.symm ▸ Or.inl hzI' : z ∈ I \ x).1) (q.sAB_sub hP)
      · exact disjoint_left.mp hIJ ((hsplit.symm ▸ Or.inl hzI' : z ∈ I \ x).1) (q.sCD_sub hP')
    · simp only [not_or] at hz
      exact disjoint_left.mp hdis hzI' (h ⟨hzw, by simp [hz.1, hz.2]⟩)

/-- **Restriction of a ruling to one half of a cut.** If `x` is an arc of the ruling `(𝒳, 𝒴)` of
`ABCDA`, cutting `I` into `I′`, the interior of `AXX′DA`, and `I″`, whose closure misses `DA`, then
the arcs of `𝒳` on `I′` and its boundary, and the parts of the arcs of `𝒴` on `I′` and its boundary,
form a ruling of `AXX′DA`. -/
theorem Space.ArcRuling.restrict_half (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (R : σ.ArcRuling I sAB sBC sCD sDA A B C D 𝒳 𝒴) {x : Set S} (hx : x ∈ 𝒳)
    {X X' : S} {s₁ t₁ J' I' I'' : Set S} (q' : σ.Quad J' I' A X X' D s₁ x t₁ sDA)
    (hs₁ : s₁ ⊆ sAB) (ht₁ : t₁ ⊆ sCD)
    (hsplit : I \ x = I' ∪ I'') (hI'' : @IsOpen S σ.topology I'') (hdis : Disjoint I' I'')
    (hcl : Disjoint (@closure S σ.topology I'') sDA) :
    σ.ArcRuling I' s₁ x t₁ sDA A X X' D {w ∈ 𝒳 | w ≠ x ∧ w ⊆ I' ∪ J'}
      ((· ∩ (I' ∪ J')) '' 𝒴) := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨hI'o, -, -, -, -, -, -, -, hclI', hI'J', -, -, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 q'.interior
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  have hJ' : J' = s₁ ∪ x ∪ t₁ ∪ sDA := q'.union.symm
  have hI'sub : I' ⊆ I \ x := hsplit ▸ subset_union_left
  have hI''sub : I'' ⊆ I \ x := hsplit ▸ subset_union_right
  have notI : ∀ {z : S}, z ∈ J → z ∉ I := fun hz hzI => disjoint_left.mp hIJ hzI hz
  have hXx : X ∈ x := q'.bc.left_mem
  have hX'x : X' ∈ x := q'.bc.right_mem
  have hXJ : X ∈ J := q.sAB_sub (hs₁ q'.ab.right_mem)
  have hX'J : X' ∈ J := q.sCD_sub (ht₁ q'.cd.left_mem)
  obtain ⟨P₀, P₀', hP₀, hP₀', -, -, hxJ⟩ := (R.arcX x hx).inter_J hIJ
  -- points of `J′`
  have J'_cases : ∀ {z : S}, z ∈ J' → z ∈ s₁ ∨ z ∈ x ∨ z ∈ t₁ ∨ z ∈ sDA := by
    intro z hz
    rw [hJ'] at hz
    rcases hz with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have J'_sub : ∀ {z : S}, z ∈ J' → z ∈ J ∨ z ∈ x := by
    intro z hz
    rcases J'_cases hz with h | h | h | h
    · exact Or.inl (q.sAB_sub (hs₁ h))
    · exact Or.inr h
    · exact Or.inl (q.sCD_sub (ht₁ h))
    · exact Or.inl (q.sDA_sub h)
  have I''_cl' : ∀ {z : S}, z ∈ I'' → z ∉ I' ∪ J' := by
    rintro z hz (h | h)
    · exact disjoint_left.mp hdis h hz
    · rcases J'_sub h with h' | h'
      · exact notI h' (hI''sub hz).1
      · exact (hI''sub hz).2 h'
  -- `x` meets `BC` and `DA` nowhere
  have hx_BC : ∀ {z : S}, z ∈ x → z ∉ sBC := by
    intro z hz hzBC
    rcases hxJ z hz (q.sBC_sub hzBC) with rfl | rfl
    · exact (q.notMem_of_ab hP₀).1 hzBC
    · exact (q.notMem_of_cd hP₀').2.2 hzBC
  have hx_DA : ∀ {z : S}, z ∈ x → z ∉ sDA := by
    intro z hz hzDA
    rcases hxJ z hz (q.sDA_sub hzDA) with rfl | rfl
    · exact (q.notMem_of_ab hP₀).2.2 hzDA
    · exact (q.notMem_of_cd hP₀').1 hzDA
  refine ⟨R.finX.subset (sep_subset _ _), R.finY.image _, ?_, ?_,
    R.disjX.mono (sep_subset _ _), ?_, ?_⟩
  · -- arcs `X`
    rintro w ⟨hw, hwx, hwcl⟩
    obtain ⟨P, P', ⟨hP, hPAB⟩, ⟨hP', hP'CD⟩, hwa, hwI⟩ := R.arcX w hw
    have hwx' : Disjoint w x := R.disjX hw hx hwx
    have hPJ' : P ∈ J' := (hwcl hwa.left_mem).resolve_left fun h => notI (q.sAB_sub hP) (hI'sub h).1
    have hP'J' : P' ∈ J' :=
      (hwcl hwa.right_mem).resolve_left fun h => notI (q.sCD_sub hP') (hI'sub h).1
    have hPns := q.notMem_of_ab ⟨hP, hPAB⟩
    have hP'ns := q.notMem_of_cd ⟨hP', hP'CD⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hPAB hP'CD
    have hPs₁ : P ∈ s₁ := by
      rcases J'_cases hPJ' with h | h | h | h
      · exact h
      · exact absurd h (disjoint_left.mp hwx' hwa.left_mem)
      · exact absurd (ht₁ h) hPns.2.1
      · exact absurd h hPns.2.2
    have hP't₁ : P' ∈ t₁ := by
      rcases J'_cases hP'J' with h | h | h | h
      · exact absurd (hs₁ h) hP'ns.2.1
      · exact absurd h (disjoint_left.mp hwx' hwa.right_mem)
      · exact h
      · exact absurd h hP'ns.1
    refine ⟨P, P', ⟨hPs₁, ?_⟩, ⟨hP't₁, ?_⟩, hwa, ?_⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hPAB.1, fun e => disjoint_left.mp hwx' hwa.left_mem (e ▸ hXx)⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => disjoint_left.mp hwx' hwa.right_mem (e ▸ hX'x), hP'CD.2⟩
    · intro z hz
      have hzI := hwI hz
      have hzx : z ∉ x := fun h => disjoint_left.mp hwx' hz.1 h
      rcases hwcl hz.1 with h | h
      · exact h
      · rcases J'_sub h with h' | h'
        · exact absurd hzI (notI h')
        · exact absurd h' hzx
  · -- arcs `Y`
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, ⟨hcx, hcy⟩, hcu⟩ := R.cross x hx y hy
    obtain ⟨Q, Q', hQ, hQ', hya, hyI, hyJ⟩ := (R.arcY y hy).inter_J hIJ
    have hQns := q.notMem_of_bc hQ
    have hQ'ns := q.notMem_of_da hQ'
    have hcJ : c ∉ J := by
      intro hcJ
      rcases hyJ c hcy hcJ with rfl | rfl
      · exact hx_BC hcx hQ.1
      · exact hx_DA hcx hQ'.1
    have hcQ : c ≠ Q := fun e => hcJ (e ▸ q.sBC_sub hQ.1)
    have hcQ' : c ≠ Q' := fun e => hcJ (e ▸ q.sDA_sub hQ'.1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hyu, hyi⟩ := hya.split hcy hcQ hcQ'
    have hy₁y : y₁ ⊆ y := hyu ▸ subset_union_left
    have hy₂y : y₂ ⊆ y := hyu ▸ subset_union_right
    have hyx : ∀ {z : S}, z ∈ y → z ∈ x → z = c := fun hzy hzx => hcu _ ⟨hzx, hzy⟩
    have mid : ∀ {z : S}, z ∈ y → z ≠ Q → z ≠ Q' → z ≠ c → z ∈ I' ∪ I'' := by
      intro z hz h₁ h₂ h₃
      rw [← hsplit]
      exact ⟨hyI ⟨hz, by simp [h₁, h₂]⟩, fun hzx => h₃ (hyx hz hzx)⟩
    have hQy₂ : Q ∉ y₂ := fun h => hcQ (by
      have : Q ∈ y₁ ∩ y₂ := ⟨hy₁.left_mem, h⟩
      rw [hyi] at this; exact this.symm)
    have hQ'y₁ : Q' ∉ y₁ := fun h => hcQ' (by
      have : Q' ∈ y₁ ∩ y₂ := ⟨h, hy₂.right_mem⟩
      rw [hyi] at this; exact this.symm)
    have hy₂sub : y₂ \ {c, Q'} ⊆ I' ∪ I'' := fun z hz => mid (hy₂y hz.1)
      (fun e => hQy₂ (e ▸ hz.1)) (fun e => hz.2 (by simp [e])) (fun e => hz.2 (by simp [e]))
    have hy₁sub : y₁ \ {Q, c} ⊆ I' ∪ I'' := fun z hz => mid (hy₁y hz.1)
      (fun e => hz.2 (by simp [e])) (fun e => hQ'y₁ (e ▸ hz.1)) (fun e => hz.2 (by simp [e]))
    have hy₂I' : y₂ \ {c, Q'} ⊆ I' := by
      rcases hy₂.isPreconnected_diff.subset_or_subset hI'o hI'' hdis hy₂sub with h | h
      · exact h
      · exact absurd hQ'.1 (disjoint_left.mp hcl
          (hy₂.subset_closure_diff.trans (closure_mono h) hy₂.right_mem))
    have hQcl : Q ∉ I' ∪ J' := by
      rintro (h | h)
      · exact notI (q.sBC_sub hQ.1) (hI'sub h).1
      · rcases J'_cases h with h | h | h | h
        · exact hQns.2.2 (hs₁ h)
        · exact hx_BC h hQ.1
        · exact hQns.1 (ht₁ h)
        · exact hQns.2.1 h
    have hy₁I'' : y₁ \ {Q, c} ⊆ I'' := by
      rcases hy₁.isPreconnected_diff.subset_or_subset hI'o hI'' hdis hy₁sub with h | h
      · refine absurd ?_ hQcl
        rw [← hclI']
        exact hy₁.subset_closure_diff.trans (closure_mono h) hy₁.left_mem
      · exact h
    have hy₂cl : y₂ ⊆ I' ∪ J' := by
      rw [← hclI']; exact hy₂.subset_closure_diff.trans (closure_mono hy₂I')
    have heq : y ∩ (I' ∪ J') = y₂ := by
      apply subset_antisymm
      · rintro z ⟨hzy, hzcl⟩
        rw [← hyu] at hzy
        rcases hzy with h | h
        · by_cases hzQ : z = Q
          · exact absurd (hzQ ▸ hzcl) hQcl
          by_cases hzc : z = c
          · exact hzc ▸ hy₂.left_mem
          exact absurd hzcl (I''_cl' (hy₁I'' ⟨h, by simp [hzQ, hzc]⟩))
        · exact h
      · exact subset_inter hy₂y hy₂cl
    show σ.XArc I' x sDA X X' D A (y ∩ (I' ∪ J'))
    rw [heq]
    refine ⟨c, Q', ⟨hcx, ?_⟩, ⟨hQ'.1, ?_⟩, hy₂, hy₂I'⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => hcJ (e ▸ hXJ), fun e => hcJ (e ▸ hX'J)⟩
    · have := hQ'.2
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at this ⊢
      exact this
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
    exact (R.disjY hy hy' fun e => hne (e ▸ rfl)).mono inter_subset_left inter_subset_left
  · rintro w ⟨hw, -, hwcl⟩ _ ⟨y, hy, rfl⟩
    have : w ∩ (y ∩ (I' ∪ J')) = w ∩ y := by
      rw [← inter_assoc, inter_right_comm, inter_eq_left.mpr hwcl]
    rw [this]
    exact R.cross w hw y hy

end Restrict

end HPC.Moore
