import HPC.Plane.Atriodic51Props

/-!
# Bing 1951 (*Snake-like continua*), §4, part one: Theorem 8

Batch-92 skeleton, part three (the definitions are in `HPC/Plane/Atriodic51Defs.lean`, properties
1–6 in `HPC/Plane/Atriodic51Props.lean`).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **The one-layer elements**: `g p` is the intersection of all continua containing
`p` interiorly. Bing's own elements (p. 658) are `bingElt` (`Atriodic51BElt.lean`). -/
def gElt (p : S) : Set S := ⋂₀ {H : Set S | Fold.Q78.IsContinuum H ∧ p ∈ interior H}

/-! ## The one-layer elements `g p` -/

/-- `S` is a continuum containing every point interiorly. -/
theorem BingS.univ_nbhd (hS : BingS S) (p : S) :
    Fold.Q78.IsContinuum (univ : Set S) ∧ p ∈ interior (univ : Set S) := by
  haveI := hS.connected
  exact ⟨⟨isCompact_univ, isConnected_univ⟩, by rw [interior_univ]; exact mem_univ p⟩

omit [CompactSpace S] in
theorem gElt_subset {p : S} {H : Set S} (hH : Fold.Q78.IsContinuum H) (hp : p ∈ interior H) :
    gElt p ⊆ H :=
  sInter_subset_of_mem ⟨hH, hp⟩

omit [CompactSpace S] in
theorem mem_gElt (p : S) : p ∈ gElt p :=
  mem_sInter.mpr fun _ hH => interior_subset hH.2

/-- **Theorem 8, the elements are continua** (property 1). -/
theorem gElt_isContinuum (hS : BingS S) (p : S) : Fold.Q78.IsContinuum (gElt p) :=
  prop1_inter_continuum hS ⟨univ, hS.univ_nbhd p⟩ (fun _ hH => hH.1) ⟨p, mem_gElt p⟩

/-- The continua containing `p` interiorly are closed under intersection. -/
theorem BingS.nbhd_inter (hS : BingS S) {p : S} {H H' : Set S} (hH : Fold.Q78.IsContinuum H)
    (hp : p ∈ interior H) (hH' : Fold.Q78.IsContinuum H') (hp' : p ∈ interior H') :
    Fold.Q78.IsContinuum (H ∩ H') ∧ p ∈ interior (H ∩ H') :=
  ⟨hS.inter_two hH hH' ⟨p, interior_subset hp, interior_subset hp'⟩,
    by rw [interior_inter]; exact ⟨hp, hp'⟩⟩

/-- Inside any open set containing `g p` there is a continuum containing `p` interiorly
(compactness). -/
theorem BingS.exists_nbhd_subset (hS : BingS S) {p : S} {U : Set S} (hU : IsOpen U)
    (hg : gElt p ⊆ U) : ∃ H, Fold.Q78.IsContinuum H ∧ p ∈ interior H ∧ H ⊆ U := by
  classical
  set T : Set (Set S) := {H : Set S | Fold.Q78.IsContinuum H ∧ p ∈ interior H} with hT
  have hfin : ∀ u : Finset T, Fold.Q78.IsContinuum (⋂ i ∈ u, (i : Set S)) ∧
      p ∈ interior (⋂ i ∈ u, (i : Set S)) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using hS.univ_nbhd p
    | insert a u _ ih =>
      rw [Finset.set_biInter_insert]
      exact hS.nbhd_inter a.2.1 a.2.2 ih.1 ih.2
  obtain ⟨u, hu⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun i : T => (i : Set S)) (fun i => i.2.1.1.isClosed) (by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_iInter, mem_empty_iff_false, iff_false,
        not_and]
      intro hxU hall
      exact hxU (hg (mem_sInter.mpr fun H hH => hall ⟨H, hH⟩)))
  refine ⟨_, (hfin u).1, (hfin u).2, fun x hx => ?_⟩
  by_contra hxU
  have : x ∈ Uᶜ ∩ ⋂ i ∈ u, (i : Set S) := ⟨hxU, hx⟩
  rw [hu] at this; exact this

/-- **The side of a separating continuum.** If `K` separates `A` from `B`, then `K` together
with the side of `S \ K` containing `A` is a continuum containing `A` interiorly and missing `B`. -/
theorem BingS.side_of_separates (hS : BingS S) {K A B : Set S} (hK : Fold.Q78.IsContinuum K)
    (h : Separates K A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ Z, Fold.Q78.IsContinuum Z ∧ K ⊆ Z ∧ A ⊆ interior Z ∧ Disjoint Z B := by
  haveI := hS.connected
  obtain ⟨dKA, dKB, U, V, hU, hV, hUV, hcov, hAU, hBV⟩ := h
  have hKo : IsOpen Kᶜ := hK.1.isClosed.isOpen_compl
  set W := Kᶜ ∩ U with hW_def
  have hWo : IsOpen W := hKo.inter hU
  have hAW : A ⊆ W := fun x hx => ⟨fun hxK => Set.disjoint_left.mp dKA hxK hx, hAU hx⟩
  have hBK : B ⊆ Kᶜ ∩ V := fun x hx => ⟨fun hxK => Set.disjoint_left.mp dKB hxK hx, hBV hx⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hcovK : Kᶜ ⊆ U ∪ V := fun x hx => hcov ⟨mem_univ x, hx⟩
  have dUVK : Disjoint (Kᶜ ∩ U) (Kᶜ ∩ V) := hUV.mono inter_subset_right inter_subset_right
  have hWpc : IsPreconnected W :=
    hS.split_piece_preconnected hK hU hV hcovK ⟨b, hBK hb⟩ dUVK
  have hZeq : K ∪ W = (Kᶜ ∩ V)ᶜ := by
    ext x
    simp only [hW_def, mem_union, mem_inter_iff, mem_compl_iff, not_and]
    constructor
    · rintro (h | ⟨_, hxU⟩) hxK
      · exact absurd h hxK
      · exact fun hxV => Set.disjoint_left.mp hUV hxU hxV
    · intro h
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hxK, (hcovK hxK).resolve_right (h hxK)⟩
  have hz : (closure W ∩ K).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hWcl : closure W ⊆ W := by
      intro x hx
      have hx' : x ∈ (Kᶜ ∩ V)ᶜ := closure_minimal (fun z hz => by
        rw [← hZeq]; exact Or.inr hz) (hKo.inter hV).isClosed_compl hx
      rw [← hZeq] at hx'
      rcases hx' with h | h
      · have : x ∈ closure W ∩ K := ⟨hx, h⟩
        rw [hno] at this; exact this.elim
      · exact h
    rcases isClopen_iff.mp ⟨closure_subset_iff_isClosed.mp hWcl, hWo⟩ with h | h
    · have : a ∈ W := hAW ha
      rw [h] at this; exact this
    · have hbW : b ∈ W := h ▸ mem_univ b
      exact Set.disjoint_left.mp dUVK hbW (hBK hb)
  obtain ⟨z, hzcl, hzK⟩ := hz
  have hpc : IsPreconnected (W ∪ ∅ ∪ K) :=
    preconnected_through hWpc (empty_subset _) hzcl hzK hK.2.2
  rw [union_empty, union_comm] at hpc
  refine ⟨K ∪ W, ⟨(hZeq ▸ (hKo.inter hV).isClosed_compl : IsClosed (K ∪ W)).isCompact,
    ⟨⟨a, Or.inr (hAW ha)⟩, hpc⟩⟩, subset_union_left,
    hAW.trans (interior_maximal subset_union_right hWo), ?_⟩
  rw [hZeq]
  exact Set.disjoint_left.mpr fun x hx hxB => hx (hBK hxB)

omit [CompactSpace S] in
theorem separates_mono {A B C B' C' : Set S} (h : Separates A B C) (hB : B' ⊆ B)
    (hC : C' ⊆ C) : Separates A B' C' := by
  obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hBU, hCV⟩ := h
  exact ⟨d1.mono_right hB, d2.mono_right hC, U, V, hU, hV, hUV, hcov, hB.trans hBU, hC.trans hCV⟩

omit [CompactSpace S] in
/-- A point of the open set `W ⊆ F ∪ G` outside the closed `F` is interior to `G`. -/
theorem exists_private {W F G : Set S} (hWo : IsOpen W) (hF : IsClosed F) (hWFG : W ⊆ F ∪ G)
    (hnot : ¬ W ⊆ F) : ∃ x ∈ W, x ∉ F ∧ x ∈ interior G := by
  obtain ⟨x, hxW, hxF⟩ := not_subset.mp hnot
  exact ⟨x, hxW, hxF, interior_maximal (fun y hy => (hWFG hy.1).resolve_left hy.2)
    (hWo.inter hF.isOpen_compl) ⟨hxW, hxF⟩⟩

/-- **Two disjoint continua with interior points** inside any continuum containing a nonempty
open set (Bing, Theorem 8 (b): "`g` is the sum of three continua such that each contains a point
interiorly that belongs to neither of the others", then property 3). The three continua come from a
minimal continuum `Z ⊇ W`, a decomposition `A ∪ B` of it, and a decomposition of a minimal
`B' ⊆ B` with `W ⊆ A ∪ B'`. -/
theorem BingS.two_disjoint_with_interior (hS : BingS S) {W Z₀ : Set S} (hWo : IsOpen W)
    (hWne : W.Nonempty) (hZ₀ : Fold.Q78.IsContinuum Z₀) (hWZ : W ⊆ Z₀) :
    ∃ K₁ K₂ : Set S, Fold.Q78.IsContinuum K₁ ∧ Fold.Q78.IsContinuum K₂ ∧ K₁ ⊆ Z₀ ∧ K₂ ⊆ Z₀ ∧
      Disjoint K₁ K₂ ∧ (interior K₁).Nonempty ∧ (interior K₂).Nonempty := by
  -- a minimal continuum containing `W`
  obtain ⟨Z, -, hZmin⟩ := zorn_superset_nonempty
    {Z : Set S | Fold.Q78.IsContinuum Z ∧ Z ⊆ Z₀ ∧ W ⊆ Z} (fun c hc _ hcne => by
      refine ⟨⋂₀ c, ⟨prop1_inter_continuum hS hcne (fun K hK => (hc hK).1)
        (hWne.mono fun x hx => mem_sInter.mpr fun K hK => (hc hK).2.2 hx), ?_, ?_⟩,
        fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨K, hK⟩ := hcne
        exact (sInter_subset_of_mem hK).trans (hc hK).2.1
      · exact fun x hx => mem_sInter.mpr fun K hK => (hc hK).2.2 hx) Z₀ ⟨hZ₀, subset_rfl, hWZ⟩
  obtain ⟨hZ, hZZ₀, hWZ'⟩ := hZmin.prop
  have hZnt : Z.Nontrivial := (hS.open_nontrivial hWo hWne).mono hWZ'
  obtain ⟨A, B, hA, hB, hAZ, hBZ, hABZ⟩ := hS.hd Z (subset_univ _) hZ hZnt
  have hAZ' : A ⊆ Z := hABZ ▸ subset_union_left
  have hBZ' : B ⊆ Z := hABZ ▸ subset_union_right
  have hWA : ¬ W ⊆ A := fun h =>
    hAZ (Subset.antisymm hAZ' (hZmin.le_of_le ⟨hA, hAZ'.trans hZZ₀, h⟩ hAZ'))
  have hWB : ¬ W ⊆ B := fun h =>
    hBZ (Subset.antisymm hBZ' (hZmin.le_of_le ⟨hB, hBZ'.trans hZZ₀, h⟩ hBZ'))
  have hWAB : W ⊆ A ∪ B := hABZ ▸ hWZ'
  -- a minimal `B' ⊆ B` with `W ⊆ A ∪ B'`
  obtain ⟨B', -, hB'min⟩ := zorn_superset_nonempty
    {B' : Set S | Fold.Q78.IsContinuum B' ∧ B' ⊆ B ∧ W ⊆ A ∪ B'} (fun c hc _ hcne => by
      obtain ⟨x, hxW, hxA⟩ := not_subset.mp hWA
      refine ⟨⋂₀ c, ⟨prop1_inter_continuum hS hcne (fun K hK => (hc hK).1)
        ⟨x, mem_sInter.mpr fun K hK => ((hc hK).2.2 hxW).resolve_left hxA⟩, ?_, ?_⟩,
        fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨K, hK⟩ := hcne
        exact (sInter_subset_of_mem hK).trans (hc hK).2.1
      · intro y hyW
        by_cases hyA : y ∈ A
        · exact Or.inl hyA
        · exact Or.inr (mem_sInter.mpr fun K hK => ((hc hK).2.2 hyW).resolve_left hyA))
    B ⟨hB, subset_rfl, hWAB⟩
  obtain ⟨hB', hB'B, hWAB'⟩ := hB'min.prop
  have hWB' : ¬ W ⊆ B' := fun h => hWB (h.trans hB'B)
  obtain ⟨q, hqW, hqA, hqi⟩ := exists_private hWo hA.1.isClosed hWAB' hWA
  have hB'nt : B'.Nontrivial :=
    (hS.open_nontrivial isOpen_interior ⟨q, hqi⟩).mono interior_subset
  obtain ⟨B₁, B₂, hB₁, hB₂, hB₁ne, hB₂ne, hB₁₂⟩ := hS.hd B' (subset_univ _) hB' hB'nt
  have hB₁B' : B₁ ⊆ B' := hB₁₂ ▸ subset_union_left
  have hB₂B' : B₂ ⊆ B' := hB₁₂ ▸ subset_union_right
  have notW : ∀ Bi : Set S, Fold.Q78.IsContinuum Bi → Bi ⊆ B' → Bi ≠ B' → ¬ W ⊆ A ∪ Bi :=
    fun Bi hBi hBiB' hne h =>
      hne (Subset.antisymm hBiB' (hB'min.le_of_le ⟨hBi, hBiB'.trans hB'B, h⟩ hBiB'))
  have hW3 : W ⊆ (A ∪ B₂) ∪ B₁ := fun x hx => by
    have := hWAB' hx; rw [← hB₁₂] at this
    simp only [mem_union] at this ⊢; tauto
  have hW3' : W ⊆ (A ∪ B₁) ∪ B₂ := fun x hx => by
    have := hWAB' hx; rw [← hB₁₂] at this
    simp only [mem_union] at this ⊢; tauto
  obtain ⟨pA, -, hpAB', hpAi⟩ := exists_private hWo hB'.1.isClosed
    (by rw [union_comm]; exact hWAB') hWB'
  obtain ⟨p₁, -, hp₁F, hp₁i⟩ := exists_private hWo (hA.1.isClosed.union hB₂.1.isClosed) hW3
    (notW B₂ hB₂ hB₂B' hB₂ne)
  obtain ⟨p₂, -, hp₂F, hp₂i⟩ := exists_private hWo (hA.1.isClosed.union hB₁.1.isClosed) hW3'
    (notW B₁ hB₁ hB₁B' hB₁ne)
  simp only [mem_union, not_or] at hp₁F hp₂F
  have sA : A ⊆ Z₀ := hAZ'.trans hZZ₀
  have s₁ : B₁ ⊆ Z₀ := hB₁B'.trans (hB'B.trans (hBZ'.trans hZZ₀))
  have s₂ : B₂ ⊆ Z₀ := hB₂B'.trans (hB'B.trans (hBZ'.trans hZZ₀))
  by_cases d1 : Disjoint A B₁
  · exact ⟨A, B₁, hA, hB₁, sA, s₁, d1, ⟨pA, hpAi⟩, ⟨p₁, hp₁i⟩⟩
  by_cases d2 : Disjoint A B₂
  · exact ⟨A, B₂, hA, hB₂, sA, s₂, d2, ⟨pA, hpAi⟩, ⟨p₂, hp₂i⟩⟩
  by_cases d3 : Disjoint B₁ B₂
  · exact ⟨B₁, B₂, hB₁, hB₂, s₁, s₂, d3, ⟨p₁, hp₁i⟩, ⟨p₂, hp₂i⟩⟩
  exfalso
  rw [not_disjoint_iff_nonempty_inter] at d1 d2 d3
  rcases prop3_one_in_union hS hA hB₁ hB₂ d1 d3 d2 with h | h | h
  · rcases h (interior_subset hpAi) with h' | h'
    · exact hpAB' (hB₁B' h')
    · exact hpAB' (hB₂B' h')
  · rcases h (interior_subset hp₁i) with h' | h'
    · exact hp₁F.1 h'
    · exact hp₁F.2 h'
  · rcases h (interior_subset hp₂i) with h' | h'
    · exact hp₂F.1 h'
    · exact hp₂F.2 h'

/-- **From neighbourhood continua to elements** (Theorem 8 (a)). If a continuum `H₁` containing
`p` interiorly separates two continua `H₂`, `H₃` with interior points, then so does every smaller
continuum containing `p` interiorly (property 4 and the side continua), and hence — taking the union
of the sides — so does `g p`. -/
theorem gElt_separates_of (hS : BingS S) {p : S} {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (hp : p ∈ interior H₁) (h₂ : Fold.Q78.IsContinuum H₂)
    (h₃ : Fold.Q78.IsContinuum H₃) (hi₂ : (interior H₂).Nonempty)
    (hi₃ : (interior H₃).Nonempty) (d₁₂ : Disjoint H₁ H₂) (d₂₃ : Disjoint H₂ H₃)
    (d₁₃ : Disjoint H₁ H₃) (hsep : Separates H₁ H₂ H₃) : Separates (gElt p) H₂ H₃ := by
  obtain ⟨x₂, hx₂⟩ := h₂.2.1
  obtain ⟨x₃, hx₃⟩ := h₃.2.1
  -- every smaller neighbourhood continuum separates
  have hstep : ∀ H', Fold.Q78.IsContinuum H' → p ∈ interior H' → H' ⊆ H₁ →
      Separates H' H₂ H₃ := by
    intro H' hH' hp' hsub
    obtain ⟨Z₃, hZ₃, hH₁Z₃, hH₃Z₃, dZ₃⟩ :=
      hS.side_of_separates h₁ (separates_comm hsep) ⟨x₃, hx₃⟩ ⟨x₂, hx₂⟩
    obtain ⟨Z₂, hZ₂, hH₁Z₂, hH₂Z₂, dZ₂⟩ := hS.side_of_separates h₁ hsep ⟨x₂, hx₂⟩ ⟨x₃, hx₃⟩
    rcases prop4_separates hS hH' h₂ h₃ ⟨p, hp'⟩ hi₂ hi₃ (d₁₂.mono_left hsub) d₂₃
      (d₁₃.mono_left hsub) with h | h | h
    · exact h
    · exact absurd h (not_separates_of_preconnected hZ₃.2.2 dZ₃
        ⟨p, hH₁Z₃ (hsub (interior_subset hp')), interior_subset hp'⟩
        ⟨x₃, interior_subset (hH₃Z₃ hx₃), hx₃⟩)
    · exact absurd h (not_separates_of_preconnected hZ₂.2.2 dZ₂
        ⟨p, hH₁Z₂ (hsub (interior_subset hp')), interior_subset hp'⟩
        ⟨x₂, interior_subset (hH₂Z₂ hx₂), hx₂⟩)
  -- the two sides of a good continuum
  have hside : ∀ H', Fold.Q78.IsContinuum H' → p ∈ interior H' → H' ⊆ H₁ →
      IsOpen (connectedComponentIn H'ᶜ x₂) ∧ IsOpen (connectedComponentIn H'ᶜ x₃) ∧
      H₂ ⊆ connectedComponentIn H'ᶜ x₂ ∧ H₃ ⊆ connectedComponentIn H'ᶜ x₃ ∧
      H'ᶜ ⊆ connectedComponentIn H'ᶜ x₂ ∪ connectedComponentIn H'ᶜ x₃ ∧
      Disjoint (connectedComponentIn H'ᶜ x₂) (connectedComponentIn H'ᶜ x₃) := by
    intro H' hH' hp' hsub
    have dH'2 : Disjoint H' H₂ := d₁₂.mono_left hsub
    have dH'3 : Disjoint H' H₃ := d₁₃.mono_left hsub
    have hx₂' : x₂ ∉ H' := fun h => Set.disjoint_left.mp dH'2 h hx₂
    have hx₃' : x₃ ∉ H' := fun h => Set.disjoint_left.mp dH'3 h hx₃
    obtain ⟨-, -, U, V, hU, hV, hUV, hcov, hH₂U, hH₃V⟩ := hstep H' hH' hp' hsub
    have hcovH : H'ᶜ ⊆ U ∪ V := fun x hx => hcov ⟨mem_univ x, hx⟩
    have dUVH : Disjoint (H'ᶜ ∩ U) (H'ᶜ ∩ V) := hUV.mono inter_subset_right inter_subset_right
    have hPU : connectedComponentIn H'ᶜ x₂ ⊆ U := by
      rcases isPreconnected_connectedComponentIn.subset_or_subset hU hV hUV
        ((connectedComponentIn_subset _ _).trans hcovH) with h | h
      · exact h
      · exact absurd (h (mem_connectedComponentIn hx₂'))
          (Set.disjoint_left.mp hUV (hH₂U hx₂))
    have hQV : connectedComponentIn H'ᶜ x₃ ⊆ V := by
      rcases isPreconnected_connectedComponentIn.subset_or_subset hU hV hUV
        ((connectedComponentIn_subset _ _).trans hcovH) with h | h
      · exact absurd (h (mem_connectedComponentIn hx₃'))
          (Set.disjoint_right.mp hUV (hH₃V hx₃))
      · exact h
    refine ⟨hS.isOpen_component_compl hH' hx₂', hS.isOpen_component_compl hH' hx₃',
      h₂.2.2.subset_connectedComponentIn hx₂ fun x hx hxH => Set.disjoint_left.mp dH'2 hxH hx,
      h₃.2.2.subset_connectedComponentIn hx₃ fun x hx hxH => Set.disjoint_left.mp dH'3 hxH hx,
      ?_, hUV.mono hPU hQV⟩
    intro x hx
    rcases hcovH hx with h | h
    · left
      exact (hS.split_piece_preconnected hH' hU hV hcovH ⟨x₃, hx₃', hH₃V hx₃⟩
        dUVH).subset_connectedComponentIn ⟨hx₂', hH₂U hx₂⟩ inter_subset_left ⟨hx, h⟩
    · right
      exact (hS.split_piece_preconnected hH' hV hU (by rw [union_comm]; exact hcovH)
        ⟨x₂, hx₂', hH₂U hx₂⟩ dUVH.symm).subset_connectedComponentIn ⟨hx₃', hH₃V hx₃⟩
        inter_subset_left ⟨hx, h⟩
  -- monotonicity of the sides
  have hmono : ∀ {H' H'' : Set S} {x : S}, H'' ⊆ H' → x ∉ H' →
      connectedComponentIn H'ᶜ x ⊆ connectedComponentIn H''ᶜ x := fun hsub hx =>
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr hsub))
  have hx₂H : ∀ {H'}, H' ⊆ H₁ → x₂ ∉ H' := fun hsub h =>
    Set.disjoint_left.mp d₁₂ (hsub h) hx₂
  have hx₃H : ∀ {H'}, H' ⊆ H₁ → x₃ ∉ H' := fun hsub h =>
    Set.disjoint_left.mp d₁₃ (hsub h) hx₃
  set Good : Set (Set S) := {H' | Fold.Q78.IsContinuum H' ∧ p ∈ interior H' ∧ H' ⊆ H₁}
    with hGood
  have hGoodInter : ∀ {H' H''}, H' ∈ Good → H'' ∈ Good → H' ∩ H'' ∈ Good := by
    intro H' H'' h' h''
    obtain ⟨hc, hi⟩ := hS.nbhd_inter h'.1 h'.2.1 h''.1 h''.2.1
    exact ⟨hc, hi, inter_subset_left.trans h'.2.2⟩
  have hgsub : gElt p ⊆ H₁ := gElt_subset h₁ hp
  refine ⟨d₁₂.mono_left hgsub, d₁₃.mono_left hgsub,
    ⋃ H' ∈ Good, connectedComponentIn H'ᶜ x₂, ⋃ H' ∈ Good, connectedComponentIn H'ᶜ x₃,
    isOpen_biUnion fun H' h' => (hside H' h'.1 h'.2.1 h'.2.2).1,
    isOpen_biUnion fun H' h' => (hside H' h'.1 h'.2.1 h'.2.2).2.1, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨H', h', hxH'⟩ := mem_iUnion₂.mp hx
    obtain ⟨H'', h'', hxH''⟩ := mem_iUnion₂.mp hx'
    have h3 := hGoodInter h' h''
    exact Set.disjoint_left.mp (hside _ h3.1 h3.2.1 h3.2.2).2.2.2.2.2
      (hmono inter_subset_left (hx₂H h'.2.2) hxH')
      (hmono inter_subset_right (hx₃H h''.2.2) hxH'')
  · rintro x ⟨-, hxg⟩
    obtain ⟨H, ⟨hH, hpH⟩, hxH⟩ : ∃ H ∈ {H : Set S | Fold.Q78.IsContinuum H ∧ p ∈ interior H},
        x ∉ H := by
      by_contra hno
      push_neg at hno
      exact hxg (mem_sInter.mpr hno)
    have hG : H ∩ H₁ ∈ Good := by
      obtain ⟨hc, hi⟩ := hS.nbhd_inter hH hpH h₁ hp
      exact ⟨hc, hi, inter_subset_right⟩
    rcases (hside _ hG.1 hG.2.1 hG.2.2).2.2.2.2.1 (fun h => hxH h.1) with h | h
    · exact Or.inl (mem_iUnion₂.mpr ⟨_, hG, h⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨_, hG, h⟩)
  · have hG : H₁ ∈ Good := ⟨h₁, hp, subset_rfl⟩
    exact fun x hx => mem_iUnion₂.mpr ⟨H₁, hG, (hside H₁ h₁ hp subset_rfl).2.2.1 hx⟩
  · have hG : H₁ ∈ Good := ⟨h₁, hp, subset_rfl⟩
    exact fun x hx => mem_iUnion₂.mpr ⟨H₁, hG, (hside H₁ h₁ hp subset_rfl).2.2.2.1 hx⟩

/-! ## Theorem 8 from the partition property

Bing's proof of Theorem 8 has two parts: (i) `q ∈ g p → g p = g q` (the `g p` partition `S`), and
(ii) everything else. Part (ii) is proved here from part (i). -/

section partition

variable (hT3 : ∀ p q : S, q ∈ gElt p → gElt p = gElt q)
include hT3

omit [CompactSpace S] in
theorem gElt_disjoint {p q : S} (h : gElt p ≠ gElt q) : Disjoint (gElt p) (gElt q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  exact h ((hT3 p x hxp).trans (hT3 q x hxq).symm)

/-- **Upper semicontinuity** (Theorem 8). -/
theorem gElt_usc (hS : BingS S) (U : Set S) (hU : IsOpen U) :
    IsOpen (⋃ q ∈ {q | gElt q ⊆ U}, gElt q) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨q, hqU, hxq⟩ := mem_iUnion₂.mp hx
  have hxU : gElt x ⊆ U := (hT3 q x hxq) ▸ hqU
  obtain ⟨H, hH, hxH, hHU⟩ := hS.exists_nbhd_subset hU hxU
  refine ⟨interior H, fun y hy => mem_iUnion₂.mpr ⟨y, (gElt_subset hH hy).trans hHU,
    mem_gElt y⟩, isOpen_interior, hxH⟩

/-- **Theorem 8 (b)**: no element has interior points. Otherwise the element contains two disjoint
continua with interior points; the separating continuum of property 5 and its side give a continuum
containing a point of the first interiorly and missing the second, so the two points lie in
different elements. -/
theorem gElt_interior_eq_empty (hS : BingS S) (p : S) : interior (gElt p) = ∅ := by
  by_contra hne
  obtain ⟨K₁, K₂, hK₁, hK₂, hK₁g, hK₂g, d, hi₁, hi₂⟩ :=
    hS.two_disjoint_with_interior isOpen_interior (nonempty_iff_ne_empty.mpr hne)
      (gElt_isContinuum hS p) interior_subset
  obtain ⟨K, hK, -, hsep⟩ := prop5_exists_separating hS hK₁ hK₂ hi₁ hi₂ d
  obtain ⟨Z, hZ, -, hK₁Z, dZ⟩ := hS.side_of_separates hK hsep hK₁.2.1 hK₂.2.1
  obtain ⟨x₁, hx₁⟩ := hi₁
  obtain ⟨x₂, hx₂⟩ := hi₂
  have h1 : gElt x₁ ⊆ Z := gElt_subset hZ (hK₁Z (interior_subset hx₁))
  have h2 : x₂ ∈ gElt x₁ := hT3 p x₁ (hK₁g (interior_subset hx₁)) ▸ hK₂g (interior_subset hx₂)
  exact Set.disjoint_left.mp dZ (h1 h2) (interior_subset hx₂)

/-- **Theorem 8 (a)**: of three distinct elements one separates the other two (properties 2 and
4: choose disjoint continua containing the elements interiorly, apply property 4, and pass to the
elements with `gElt_separates_of`). -/
theorem gElt_separates_triple (hS : BingS S) (p q r : S) (hpq : gElt p ≠ gElt q)
    (hqr : gElt q ≠ gElt r) (hpr : gElt p ≠ gElt r) :
    Separates (gElt p) (gElt q) (gElt r) ∨ Separates (gElt q) (gElt p) (gElt r) ∨
      Separates (gElt r) (gElt p) (gElt q) := by
  have cp := (gElt_isContinuum hS p).1
  have cq := (gElt_isContinuum hS q).1
  have cr := (gElt_isContinuum hS r).1
  obtain ⟨U₁₂, U₂₁, o₁₂, o₂₁, s₁₂, s₂₁, d₁₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact cp cq (gElt_disjoint hT3 hpq)
  obtain ⟨U₁₃, U₃₁, o₁₃, o₃₁, s₁₃, s₃₁, d₁₃⟩ :=
    SeparatedNhds.of_isCompact_isCompact cp cr (gElt_disjoint hT3 hpr)
  obtain ⟨U₂₃, U₃₂, o₂₃, o₃₂, s₂₃, s₃₂, d₂₃⟩ :=
    SeparatedNhds.of_isCompact_isCompact cq cr (gElt_disjoint hT3 hqr)
  obtain ⟨H₁, h₁, hp₁, hH₁⟩ := hS.exists_nbhd_subset (o₁₂.inter o₁₃) (subset_inter s₁₂ s₁₃)
  obtain ⟨H₂, h₂, hp₂, hH₂⟩ := hS.exists_nbhd_subset (o₂₁.inter o₂₃) (subset_inter s₂₁ s₂₃)
  obtain ⟨H₃, h₃, hp₃, hH₃⟩ := hS.exists_nbhd_subset (o₃₁.inter o₃₂) (subset_inter s₃₁ s₃₂)
  have e₁₂ : Disjoint H₁ H₂ :=
    d₁₂.mono (hH₁.trans inter_subset_left) (hH₂.trans inter_subset_left)
  have e₁₃ : Disjoint H₁ H₃ :=
    d₁₃.mono (hH₁.trans inter_subset_right) (hH₃.trans inter_subset_left)
  have e₂₃ : Disjoint H₂ H₃ :=
    d₂₃.mono (hH₂.trans inter_subset_right) (hH₃.trans inter_subset_right)
  have g₁ := gElt_subset h₁ hp₁
  have g₂ := gElt_subset h₂ hp₂
  have g₃ := gElt_subset h₃ hp₃
  rcases prop4_separates hS h₁ h₂ h₃ ⟨p, hp₁⟩ ⟨q, hp₂⟩ ⟨r, hp₃⟩ e₁₂ e₂₃ e₁₃ with h | h | h
  · exact Or.inl (separates_mono (gElt_separates_of hS h₁ hp₁ h₂ h₃ ⟨q, hp₂⟩ ⟨r, hp₃⟩ e₁₂ e₂₃
      e₁₃ h) g₂ g₃)
  · exact Or.inr (Or.inl (separates_mono (gElt_separates_of hS h₂ hp₂ h₁ h₃ ⟨p, hp₁⟩ ⟨r, hp₃⟩
      e₁₂.symm e₁₃ e₂₃ h) g₁ g₃))
  · exact Or.inr (Or.inr (separates_mono (gElt_separates_of hS h₃ hp₃ h₁ h₂ ⟨p, hp₁⟩ ⟨q, hp₂⟩
      e₁₃.symm e₁₂ e₂₃.symm h) g₁ g₂))

/-- **Theorem 8 (c)**: a subcontinuum meeting two different end elements is `S`. If not, its
complement meets three different elements (no element has interior points); an element missing it
contradicts (a) and the end property, and if all three meet it, it and the three elements form a
triod. -/
theorem gElt_irreducible (hS : BingS S) (r s : S)
    (hr : ∀ q q' : S, gElt q ≠ gElt r → gElt q' ≠ gElt r → gElt q ≠ gElt q' →
      ¬ Separates (gElt r) (gElt q) (gElt q'))
    (hs : ∀ q q' : S, gElt q ≠ gElt s → gElt q' ≠ gElt s → gElt q ≠ gElt q' →
      ¬ Separates (gElt s) (gElt q) (gElt q'))
    (hrs : gElt r ≠ gElt s) (M : Set S) (hM : Fold.Q78.IsContinuum M) (hrM : r ∈ M)
    (hsM : s ∈ M) : M = univ := by
  by_contra hMne
  obtain ⟨x₁, hx₁⟩ := (ne_univ_iff_exists_notMem M).mp hMne
  have hint := gElt_interior_eq_empty hT3 hS
  have hMo : IsOpen Mᶜ := hM.1.isClosed.isOpen_compl
  have hcl : ∀ q, IsClosed (gElt q) := fun q => (gElt_isContinuum hS q).1.isClosed
  have notsub : ∀ F : Set S, interior F = ∅ → (Mᶜ).Nonempty → ¬ Mᶜ ⊆ F := fun F hF hne h => by
    obtain ⟨y, hy⟩ := hne
    have := interior_maximal h hMo hy
    rw [hF] at this; exact this
  obtain ⟨x₂, hx₂M, hx₂g⟩ := not_subset.mp (notsub _ (hint x₁) ⟨x₁, hx₁⟩)
  obtain ⟨x₃, hx₃M, hx₃g⟩ := not_subset.mp (notsub _
    (by rw [interior_union_isClosed_of_interior_empty (hcl x₁) (hint x₂)]; exact hint x₁)
    ⟨x₁, hx₁⟩)
  simp only [mem_union, not_or] at hx₃g
  have ne : ∀ {a b : S}, a ∉ gElt b → gElt a ≠ gElt b := fun h e => h (e ▸ mem_gElt _)
  -- an element missing `M`
  have meets : ∀ x : S, (gElt x ∩ M).Nonempty := by
    intro x
    by_contra hno
    rw [not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hno
    have hxr : gElt x ≠ gElt r := fun e =>
      Set.disjoint_left.mp hno (e ▸ mem_gElt r : r ∈ gElt x) hrM
    have hxs : gElt x ≠ gElt s := fun e =>
      Set.disjoint_left.mp hno (e ▸ mem_gElt s : s ∈ gElt x) hsM
    rcases gElt_separates_triple hT3 hS x r s hxr hrs hxs with h | h | h
    · exact not_separates_of_preconnected hM.2.2 hno.symm ⟨r, hrM, mem_gElt r⟩
        ⟨s, hsM, mem_gElt s⟩ h
    · exact hr x s hxr hrs.symm hxs h
    · exact hs x r hxs hrs hxr h
  -- otherwise `M` and three elements form a triod
  set T := M ∪ gElt x₁ ∪ gElt x₂ ∪ gElt x₃ with hT_def
  have mono : ∀ {A B : Set S}, (A ∩ B).Nonempty → ∀ C, ((C ∪ A) ∩ B).Nonempty := fun h C =>
    h.mono (inter_subset_inter_left _ subset_union_right)
  have hT : Fold.Q78.IsContinuum T := by
    have c1 := isContinuum_union hM (gElt_isContinuum hS x₁) (by rw [inter_comm]; exact meets x₁)
    have c2 := isContinuum_union c1 (gElt_isContinuum hS x₂) (by
      obtain ⟨y, hy, hyM⟩ := meets x₂; exact ⟨y, Or.inl hyM, hy⟩)
    exact isContinuum_union c2 (gElt_isContinuum hS x₃) (by
      obtain ⟨y, hy, hyM⟩ := meets x₃; exact ⟨y, Or.inl (Or.inl hyM), hy⟩)
  have d12 := gElt_disjoint hT3 (ne hx₂g).symm
  have d13 := gElt_disjoint hT3 (ne hx₃g.1).symm
  have d23 := gElt_disjoint hT3 (ne hx₃g.2).symm
  have cl : ∀ q, closure (gElt q \ M) ⊆ gElt q := fun q => closure_minimal diff_subset (hcl q)
  refine hS.atriodic T (subset_univ _) ⟨hT, M, hM, subset_union_left.trans
    (subset_union_left.trans subset_union_left), gElt x₁ \ M, gElt x₂ \ M, gElt x₃ \ M,
    ⟨x₁, mem_gElt x₁, hx₁⟩, ⟨x₂, mem_gElt x₂, hx₂M⟩, ⟨x₃, mem_gElt x₃, hx₃M⟩, ?_,
    (d12.mono (cl x₁) diff_subset), (d12.mono diff_subset (cl x₂)),
    (d13.mono (cl x₁) diff_subset), (d13.mono diff_subset (cl x₃)),
    (d23.mono (cl x₂) diff_subset), (d23.mono diff_subset (cl x₃))⟩
  ext y
  simp only [hT_def, mem_diff, mem_union]
  tauto

/-- **Theorem 8 from the partition property.** If `q ∈ g p` always gives `g p = g q`, every other
clause of Theorem 8 holds. -/
theorem theorem8_1951_of_partition (hS : BingS S) :
    (∀ p : S, Fold.Q78.IsContinuum (gElt p)) ∧
    (∀ p : S, p ∈ gElt p) ∧ (∀ p q : S, q ∈ gElt p → gElt p = gElt q) ∧
    (∀ (p : S) (U : Set S), IsOpen U → gElt p ⊆ U → IsOpen (⋃ q ∈ {q | gElt q ⊆ U}, gElt q)) ∧
    (∀ p q r : S, gElt p ≠ gElt q → gElt q ≠ gElt r → gElt p ≠ gElt r →
      Separates (gElt p) (gElt q) (gElt r) ∨ Separates (gElt q) (gElt p) (gElt r) ∨
        Separates (gElt r) (gElt p) (gElt q)) ∧
    (∀ p : S, interior (gElt p) = ∅) ∧
    (∀ r s : S, (∀ q q' : S, gElt q ≠ gElt r → gElt q' ≠ gElt r → gElt q ≠ gElt q' →
        ¬ Separates (gElt r) (gElt q) (gElt q')) →
      (∀ q q' : S, gElt q ≠ gElt s → gElt q' ≠ gElt s → gElt q ≠ gElt q' →
        ¬ Separates (gElt s) (gElt q) (gElt q')) →
      gElt r ≠ gElt s →
      ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) :=
  ⟨gElt_isContinuum hS, mem_gElt, hT3, fun _ U hU _ => gElt_usc hT3 hS U hU,
    gElt_separates_triple hT3 hS, gElt_interior_eq_empty hT3 hS, gElt_irreducible hT3 hS⟩

end partition

-- Commented-out statement `theorem8_1951`, `isArc_of_separatesPairs` removed in batch 103; see `LEDGER.md`.

end HPC.Plane
