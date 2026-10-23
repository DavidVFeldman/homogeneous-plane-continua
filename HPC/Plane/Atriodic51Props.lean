import HPC.Plane.Atriodic51Defs

/-!
# Bing 1951, §4: the six properties of an atriodic, hereditarily unicoherent, hereditarily
# decomposable continuum

Properties 1–6 of Bing's §4 (pp. 657–658), all proved. The statements are those of the batch-92
skeleton. What Bing's text leaves to the reader is supplied as follows (REPORT-batch92.md):

* property 1: finite intersections by induction, then compactness;
* property 2: literally the definition of a triod with `M = S`, `N = H`;
* property 3: the pieces `H_i \ (H_j ∪ H_k)` are the three mutually separated sets;
* property 4: Bing's `K_i` is `H_i` together with two connectors, each a continuum avoiding the
  interiors of the other two continua (`connector_of_not_separates`: a component of
  `S \ (int H_j ∪ int H_k)`, or else a clopen splitting that makes `H_j` separate);
* property 5: Bing's `C` is `Xᶜ ∩ Yᶜ` for the "filled" continua `X ⊇ H₁`, `Y ⊇ H₂`
  (`BingS.fill`), connected by unicoherence (`BingS.compl_inter_preconnected`); the three
  continua with private interior points come from a decomposition `A ∪ B` of `C̄` and a decomposition
  of a *minimal* `B' ⊆ B` with `A ∪ B' = C̄` (Zorn);
* property 6: the components of `S \ H₁` are open (property 2), and Bing's `H(C)` is the
  separating continuum of property 5 together with the side containing `H₂`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- Two intersecting subcontinua have a continuum as intersection (hereditary unicoherence). -/
theorem BingS.inter_two (hS : BingS S) {H K : Set S} (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) (hne : (H ∩ K).Nonempty) : Fold.Q78.IsContinuum (H ∩ K) := by
  refine ⟨hH.1.inter_right hK.1.isClosed, ?_⟩
  by_cases hnt : (H ∪ K).Nontrivial
  · exact hS.hu (H ∪ K) (subset_univ _) (isContinuum_union hH hK hne) hnt H K hH hK rfl
  · rw [Set.not_nontrivial_iff] at hnt
    exact ⟨hne, (hnt.anti (inter_subset_left.trans subset_union_left)).isPreconnected⟩

/-- **Property 1.** The intersection of a nonempty family of subcontinua with nonempty
intersection is a continuum. -/
theorem prop1_inter_continuum (hS : BingS S) {𝒦 : Set (Set S)} (h𝒦 : 𝒦.Nonempty)
    (hc : ∀ K ∈ 𝒦, Fold.Q78.IsContinuum K) (hne : (⋂₀ 𝒦).Nonempty) :
    Fold.Q78.IsContinuum (⋂₀ 𝒦) := by
  classical
  obtain ⟨K0, hK0⟩ := h𝒦
  have hfin : ∀ u : Finset 𝒦, Fold.Q78.IsContinuum (K0 ∩ ⋂ i ∈ u, (i : Set S)) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using hc K0 hK0
    | insert K u hKu ih =>
      have e : K0 ∩ ⋂ i ∈ insert K u, (i : Set S) = (K0 ∩ ⋂ i ∈ u, (i : Set S)) ∩ K := by
        ext x
        simp only [mem_inter_iff, mem_iInter, Finset.mem_insert]
        constructor
        · rintro ⟨h0, h⟩
          exact ⟨⟨h0, fun i hi => h i (Or.inr hi)⟩, h K (Or.inl rfl)⟩
        · rintro ⟨⟨h0, h⟩, hK⟩
          refine ⟨h0, fun i hi => ?_⟩
          rcases hi with rfl | hi
          · exact hK
          · exact h i hi
      rw [e]
      refine hS.inter_two ih (hc K K.2) ?_
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, ⟨mem_sInter.mp hx K0 hK0, ?_⟩, mem_sInter.mp hx K K.2⟩
      simp only [mem_iInter]
      intro i _
      exact mem_sInter.mp hx i i.2
  have hcl : IsClosed (⋂₀ 𝒦) := isClosed_sInter fun K hK => (hc K hK).1.isClosed
  refine ⟨hcl.isCompact, hne, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro a b ha hb hab hdisj
  have hd : Disjoint (⋂₀ 𝒦 ∩ a) (⋂₀ 𝒦 ∩ b) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← hdisj]; ext x; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hcl.inter ha).isCompact (hcl.inter hb).isCompact hd
  have hTUV : ⋂₀ 𝒦 ⊆ U ∪ V := fun x hx => (hab hx).elim
    (fun h => Or.inl (haU ⟨hx, h⟩)) (fun h => Or.inr (hbV ⟨hx, h⟩))
  have hcomp : IsCompact (K0 \ (U ∪ V)) := ((hc K0 hK0).1.isClosed.sdiff (hU.union hV)).isCompact
  obtain ⟨u, hu⟩ := hcomp.elim_finite_subfamily_closed (fun i : 𝒦 => (i : Set S))
    (fun i => (hc i i.2).1.isClosed) (by
      ext x
      simp only [mem_inter_iff, mem_diff, mem_iInter, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨_, hxUV⟩ hall
      exact hxUV (hTUV (mem_sInter.mpr fun K hK => hall ⟨K, hK⟩)))
  have hFUV : K0 ∩ ⋂ i ∈ u, (i : Set S) ⊆ U ∪ V := by
    intro x hx
    by_contra hxUV
    have : x ∈ (K0 \ (U ∪ V)) ∩ ⋂ i ∈ u, (i : Set S) := ⟨⟨hx.1, hxUV⟩, hx.2⟩
    rw [hu] at this; exact this
  have hTF : ⋂₀ 𝒦 ⊆ K0 ∩ ⋂ i ∈ u, (i : Set S) := fun x hx =>
    ⟨mem_sInter.mp hx K0 hK0, mem_iInter₂.mpr fun i _ => mem_sInter.mp hx i i.2⟩
  rcases (hfin u).2.2.subset_or_subset hU hV hUV hFUV with h | h
  · left
    intro x hx
    rcases hab hx with h' | h'
    · exact h'
    · exact absurd (h (hTF hx)) (Set.disjoint_left.mp hUV.symm (hbV ⟨hx, h'⟩))
  · right
    intro x hx
    rcases hab hx with h' | h'
    · exact absurd (h (hTF hx)) (Set.disjoint_left.mp hUV (haU ⟨hx, h'⟩))
    · exact h'

/-- **Property 2.** The complement of a subcontinuum has at most two components (stated as: no
three nonempty mutually separated pieces); the complement of the union of two intersecting
subcontinua has at most three. -/
theorem prop2_components (hS : BingS S) {H : Set S} (hH : Fold.Q78.IsContinuum H) :
    ¬ ∃ A B C : Set S, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ (univ : Set S) \ H = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C) := by
  haveI := hS.connected
  rintro ⟨A, B, C, hA, hB, hC, hcov, h1, h2, h3, h4, h5, h6⟩
  exact hS.atriodic univ subset_rfl ⟨⟨isCompact_univ, isConnected_univ⟩, H, hH, subset_univ _,
    A, B, C, hA, hB, hC, hcov, h1, h2, h3, h4, h5, h6⟩

/-- **Property 3.** If three subcontinua pairwise intersect, one lies in the union of the other
two. -/
theorem prop3_one_in_union (hS : BingS S) {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂) (h₃ : Fold.Q78.IsContinuum H₃)
    (h₁₂ : (H₁ ∩ H₂).Nonempty) (h₂₃ : (H₂ ∩ H₃).Nonempty) (h₁₃ : (H₁ ∩ H₃).Nonempty) :
    H₁ ⊆ H₂ ∪ H₃ ∨ H₂ ⊆ H₁ ∪ H₃ ∨ H₃ ⊆ H₁ ∪ H₂ := by
  set T := H₁ ∪ H₂ ∪ H₃ with hT_def
  have hT : Fold.Q78.IsContinuum T :=
    isContinuum_union (isContinuum_union h₁ h₂ h₁₂) h₃
      (h₂₃.mono (inter_subset_inter_left _ subset_union_right))
  by_cases hnt : T.Nontrivial
  swap
  · rw [Set.not_nontrivial_iff] at hnt
    left
    intro x hx
    obtain ⟨y, hy⟩ := h₂.2.nonempty
    have : x = y := hnt (Or.inl (Or.inl hx)) (Or.inl (Or.inr hy))
    exact Or.inl (this ▸ hy)
  -- a common point
  have hcommon : (H₁ ∩ H₂ ∩ H₃).Nonempty := by
    have hu := hS.hu T (subset_univ _) hT hnt (H₁ ∪ H₂) H₃ (isContinuum_union h₁ h₂ h₁₂) h₃ rfl
    rw [union_inter_distrib_right] at hu
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hd : (H₁ ∩ H₃) ∩ (H₂ ∩ H₃) = ∅ := by
      rw [← hne]; ext x; simp only [mem_inter_iff]; tauto
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hu.2 (H₁ ∩ H₃) (H₂ ∩ H₃)
      (h₁.1.isClosed.inter h₃.1.isClosed) (h₂.1.isClosed.inter h₃.1.isClosed) subset_rfl
      (by rw [hd, inter_empty]) with h | h
    · obtain ⟨x, hx⟩ := h₂₃
      have := h (Or.inr hx)
      have hx' : x ∈ (H₁ ∩ H₃) ∩ (H₂ ∩ H₃) := ⟨this, hx⟩
      rw [hd] at hx'; exact hx'
    · obtain ⟨x, hx⟩ := h₁₃
      have := h (Or.inl ⟨hx.1, hx.2⟩)
      have hx' : x ∈ (H₁ ∩ H₃) ∩ (H₂ ∩ H₃) := ⟨hx, this⟩
      rw [hd] at hx'; exact hx'
  obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := hcommon
  set H₀ := (H₁ ∩ H₂) ∪ (H₂ ∩ H₃) ∪ (H₃ ∩ H₁) with hH₀_def
  have hH₀ : Fold.Q78.IsContinuum H₀ := by
    have c12 := hS.inter_two h₁ h₂ h₁₂
    have c23 := hS.inter_two h₂ h₃ h₂₃
    have c31 := hS.inter_two h₃ h₁ ⟨x, hx3, hx1⟩
    exact isContinuum_union (isContinuum_union c12 c23 ⟨x, ⟨hx1, hx2⟩, ⟨hx2, hx3⟩⟩) c31
      ⟨x, Or.inl ⟨hx1, hx2⟩, ⟨hx3, hx1⟩⟩
  by_contra hcon
  simp only [not_or, not_subset] at hcon
  obtain ⟨⟨a, ha1, ha⟩, ⟨b, hb2, hb⟩, ⟨c, hc3, hc⟩⟩ := hcon
  simp only [mem_union, not_or] at ha hb hc
  have cl1 : closure (H₁ \ (H₂ ∪ H₃)) ⊆ H₁ := closure_minimal diff_subset h₁.1.isClosed
  have cl2 : closure (H₂ \ (H₁ ∪ H₃)) ⊆ H₂ := closure_minimal diff_subset h₂.1.isClosed
  have cl3 : closure (H₃ \ (H₁ ∪ H₂)) ⊆ H₃ := closure_minimal diff_subset h₃.1.isClosed
  refine hS.atriodic T (subset_univ _) ⟨hT, H₀, hH₀, ?_, H₁ \ (H₂ ∪ H₃), H₂ \ (H₁ ∪ H₃),
    H₃ \ (H₁ ∪ H₂), ⟨a, ha1, by simp [ha]⟩, ⟨b, hb2, by simp [hb]⟩, ⟨c, hc3, by simp [hc]⟩, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [hH₀_def, hT_def, mem_union, mem_inter_iff] at hy ⊢
    tauto
  · ext y
    simp only [hH₀_def, hT_def, mem_diff, mem_union, mem_inter_iff]
    tauto
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inl (cl1 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inl (cl2 hy'))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inl (cl1 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inr (cl3 hy'))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inr (cl2 hy))
  · exact Set.disjoint_left.mpr fun y hy hy' => hy.2 (Or.inr (cl3 hy'))

/-- **Property 4.** Of three mutually exclusive subcontinua with interior points, one separates
the other two. -/
theorem prop4_separates (hS : BingS S) {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂) (h₃ : Fold.Q78.IsContinuum H₃)
    (hi₁ : (interior H₁).Nonempty) (hi₂ : (interior H₂).Nonempty) (hi₃ : (interior H₃).Nonempty)
    (d₁₂ : Disjoint H₁ H₂) (d₂₃ : Disjoint H₂ H₃) (d₁₃ : Disjoint H₁ H₃) :
    Separates H₁ H₂ H₃ ∨ Separates H₂ H₁ H₃ ∨ Separates H₃ H₁ H₂ := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨n1, n2, n3⟩ := hcon
  have c1 := h₁.1.isClosed
  have c2 := h₂.1.isClosed
  have c3 := h₃.1.isClosed
  -- the six connectors
  obtain ⟨L12, hL12, a12, b12, m12, m12'⟩ := connector_of_not_separates c3 c1 c2 d₁₃.symm
    d₂₃.symm d₁₂ n3
  obtain ⟨L13, hL13, a13, b13, m13, m13'⟩ := connector_of_not_separates c2 c1 c3 d₁₂.symm d₂₃
    d₁₃ n2
  obtain ⟨L21, hL21, a21, b21, m21, m21'⟩ := connector_of_not_separates c3 c2 c1 d₂₃.symm
    d₁₃.symm d₁₂.symm (fun h => n3 (separates_comm h))
  obtain ⟨L23, hL23, a23, b23, m23, m23'⟩ := connector_of_not_separates c1 c2 c3 d₁₂ d₁₃ d₂₃ n1
  obtain ⟨L31, hL31, a31, b31, m31, m31'⟩ := connector_of_not_separates c2 c3 c1 d₂₃ d₁₂.symm
    d₁₃.symm (fun h => n2 (separates_comm h))
  obtain ⟨L32, hL32, a32, b32, m32, m32'⟩ := connector_of_not_separates c1 c3 c2 d₁₃ d₁₂
    d₂₃.symm (fun h => n1 (separates_comm h))
  -- Bing's `K_i`
  have hK1 : Fold.Q78.IsContinuum (H₁ ∪ L12 ∪ L13) :=
    isContinuum_union (isContinuum_union h₁ hL12 (by rw [inter_comm]; exact m12)) hL13
      (by obtain ⟨x, hx, hx'⟩ := m13; exact ⟨x, Or.inl hx', hx⟩)
  have hK2 : Fold.Q78.IsContinuum (H₂ ∪ L21 ∪ L23) :=
    isContinuum_union (isContinuum_union h₂ hL21 (by rw [inter_comm]; exact m21)) hL23
      (by obtain ⟨x, hx, hx'⟩ := m23; exact ⟨x, Or.inl hx', hx⟩)
  have hK3 : Fold.Q78.IsContinuum (H₃ ∪ L31 ∪ L32) :=
    isContinuum_union (isContinuum_union h₃ hL31 (by rw [inter_comm]; exact m31)) hL32
      (by obtain ⟨x, hx, hx'⟩ := m32; exact ⟨x, Or.inl hx', hx⟩)
  have i12 : ((H₁ ∪ L12 ∪ L13) ∩ (H₂ ∪ L21 ∪ L23)).Nonempty := by
    obtain ⟨x, hx, hx'⟩ := m12'; exact ⟨x, Or.inl (Or.inr hx), Or.inl (Or.inl hx')⟩
  have i23 : ((H₂ ∪ L21 ∪ L23) ∩ (H₃ ∪ L31 ∪ L32)).Nonempty := by
    obtain ⟨x, hx, hx'⟩ := m23'; exact ⟨x, Or.inr hx, Or.inl (Or.inl hx')⟩
  have i13 : ((H₁ ∪ L12 ∪ L13) ∩ (H₃ ∪ L31 ∪ L32)).Nonempty := by
    obtain ⟨x, hx, hx'⟩ := m13'; exact ⟨x, Or.inr hx, Or.inl (Or.inl hx')⟩
  -- an interior point of `H_i` lies in no other `K_j`
  have out : ∀ {H H' L L' : Set S} {x : S}, x ∈ interior H → Disjoint H H' →
      Disjoint L (interior H) → Disjoint L' (interior H) → x ∉ H' ∪ L ∪ L' := by
    intro H H' L L' x hx dHH' dL dL' hx'
    rcases hx' with (h | h) | h
    · exact Set.disjoint_left.mp dHH' (interior_subset hx) h
    · exact Set.disjoint_left.mp dL h hx
    · exact Set.disjoint_left.mp dL' h hx
  rcases prop3_one_in_union hS hK1 hK2 hK3 i12 i23 i13 with h | h | h
  · obtain ⟨x, hx⟩ := hi₁
    rcases h (Or.inl (Or.inl (interior_subset hx))) with h' | h'
    · exact out hx d₁₂ b21 a23 h'
    · exact out hx d₁₃ b31 a32 h'
  · obtain ⟨x, hx⟩ := hi₂
    rcases h (Or.inl (Or.inl (interior_subset hx))) with h' | h'
    · exact out hx d₁₂.symm b12 a13 h'
    · exact out hx d₂₃ a31 b32 h'
  · obtain ⟨x, hx⟩ := hi₃
    rcases h (Or.inl (Or.inl (interior_subset hx))) with h' | h'
    · exact out hx d₁₃.symm a12 b13 h'
    · exact out hx d₂₃.symm a21 b23 h'

/-! ## Helpers for properties 5 and 6 -/

/-- A nonempty open set of `S` is nontrivial (`S` is a nondegenerate continuum). -/
theorem BingS.open_nontrivial (hS : BingS S) {W : Set S} (hW : IsOpen W) (hne : W.Nonempty) :
    W.Nontrivial := by
  haveI := hS.connected
  haveI := hS.nontrivial
  by_contra h
  rw [Set.not_nontrivial_iff] at h
  obtain ⟨x, hx⟩ := hne
  have hWx : W = {x} := h.eq_singleton_of_mem hx
  have hclo : IsClopen W := ⟨by rw [hWx]; exact isClosed_singleton, hW⟩
  rcases isClopen_iff.mp hclo with h' | h'
  · rw [h'] at hx; exact hx
  · obtain ⟨y, hy⟩ := exists_ne x
    have : y ∈ W := h' ▸ mem_univ y
    rw [hWx] at this
    exact hy this

/-- The complement of a subcontinuum is not the union of three nonempty disjoint open sets. -/
theorem BingS.no_three_open (hS : BingS S) {H : Set S} (hH : Fold.Q78.IsContinuum H)
    {A B C : Set S} (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hCn : C.Nonempty) (dAB : Disjoint A B) (dAC : Disjoint A C)
    (dBC : Disjoint B C) (hcov : (univ : Set S) \ H = A ∪ B ∪ C) : False :=
  prop2_components hS hH ⟨A, B, C, hAn, hBn, hCn, hcov, dAB.closure_left hB, dAB.closure_right hA,
    dAC.closure_left hC, dAC.closure_right hA, dBC.closure_left hC, dBC.closure_right hB⟩

/-- **Components of the complement of a subcontinuum are open** (from property 2). -/
theorem BingS.isOpen_component_compl (hS : BingS S) {H : Set S} (hH : Fold.Q78.IsContinuum H)
    {z : S} (hz : z ∉ H) : IsOpen (connectedComponentIn Hᶜ z) := by
  have hO : IsOpen Hᶜ := hH.1.isClosed.isOpen_compl
  by_cases hpc : IsPreconnected Hᶜ
  · rw [hpc.connectedComponentIn hz]; exact hO
  · simp only [IsPreconnected, not_forall, exists_prop] at hpc
    obtain ⟨u, v, hu, hv, hcov, hun, hvn, huv⟩ := hpc
    rw [not_nonempty_iff_eq_empty] at huv
    have dUV : Disjoint (Hᶜ ∩ u) (Hᶜ ∩ v) := by
      rw [Set.disjoint_iff_inter_eq_empty, ← huv]; ext x; simp only [mem_inter_iff]; tauto
    -- the piece containing `z` is connected, hence the component
    have key : ∀ u v : Set S, IsOpen u → IsOpen v → Hᶜ ⊆ u ∪ v → (Hᶜ ∩ u).Nonempty →
        (Hᶜ ∩ v).Nonempty → Disjoint (Hᶜ ∩ u) (Hᶜ ∩ v) → z ∈ u →
        connectedComponentIn Hᶜ z = Hᶜ ∩ u := by
      intro u v hu hv hcov hun hvn dUV hzu
      have hpcu : IsPreconnected (Hᶜ ∩ u) := by
        by_contra hnc
        simp only [IsPreconnected, not_forall, exists_prop] at hnc
        obtain ⟨u₁, v₁, hu₁, hv₁, hcov₁, hun₁, hvn₁, huv₁⟩ := hnc
        rw [not_nonempty_iff_eq_empty] at huv₁
        refine hS.no_three_open hH ((hO.inter hu).inter hu₁) ((hO.inter hu).inter hv₁)
          (hO.inter hv) hun₁ hvn₁ hvn ?_ ?_ ?_ ?_
        · rw [Set.disjoint_iff_inter_eq_empty, ← huv₁]; ext x; simp only [mem_inter_iff]; tauto
        · exact dUV.mono inter_subset_left le_rfl
        · exact dUV.mono inter_subset_left le_rfl
        · ext x
          simp only [mem_diff, mem_univ, true_and, mem_union, mem_inter_iff, mem_compl_iff]
          constructor
          · intro hx
            rcases hcov hx with h | h
            · rcases hcov₁ ⟨hx, h⟩ with h' | h'
              · exact Or.inl (Or.inl ⟨⟨hx, h⟩, h'⟩)
              · exact Or.inl (Or.inr ⟨⟨hx, h⟩, h'⟩)
            · exact Or.inr ⟨hx, h⟩
          · rintro ((⟨⟨hx, _⟩, _⟩ | ⟨⟨hx, _⟩, _⟩) | ⟨hx, _⟩) <;> exact hx
      apply Subset.antisymm
      · have hsub : connectedComponentIn Hᶜ z ⊆ (Hᶜ ∩ u) ∪ (Hᶜ ∩ v) := fun x hx => by
          have hx' := connectedComponentIn_subset _ _ hx
          rcases hcov hx' with h | h
          · exact Or.inl ⟨hx', h⟩
          · exact Or.inr ⟨hx', h⟩
        rcases (isPreconnected_connectedComponentIn).subset_or_subset (hO.inter hu) (hO.inter hv)
          dUV hsub with h | h
        · exact h
        · exact absurd (h (mem_connectedComponentIn hz)) (Set.disjoint_left.mp dUV ⟨hz, hzu⟩)
      · exact hpcu.subset_connectedComponentIn ⟨hz, hzu⟩ inter_subset_left
    rcases hcov hz with hzu | hzv
    · rw [key u v hu hv hcov hun hvn dUV hzu]; exact hO.inter hu
    · rw [key v u hv hu (by rw [union_comm]; exact hcov) hvn hun dUV.symm hzv]; exact hO.inter hv

/-- The part of `Hᶜ` outside one of its components is open. -/
theorem BingS.isOpen_compl_diff_component (hS : BingS S) {H : Set S}
    (hH : Fold.Q78.IsContinuum H) (g : S) : IsOpen ((connectedComponentIn Hᶜ g)ᶜ ∩ Hᶜ) := by
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨hxP, hxH⟩
  refine ⟨connectedComponentIn Hᶜ x, ?_, hS.isOpen_component_compl hH hxH,
    mem_connectedComponentIn hxH⟩
  intro y hy
  refine ⟨fun hyP => hxP ?_, connectedComponentIn_subset _ _ hy⟩
  rw [connectedComponentIn_eq hyP, ← connectedComponentIn_eq hy]
  exact mem_connectedComponentIn hxH

/-- **Filling in the far side.** For a subcontinuum `H` and a connected `G` missing it, the
complement `H'` of the component of `Hᶜ` containing `G` is a continuum containing `H`, missing `G`,
with connected complement, whose points in the closure of the complement lie in `H`. -/
theorem BingS.fill (hS : BingS S) {H G : Set S} (hH : Fold.Q78.IsContinuum H)
    (hG : IsPreconnected G) (hGne : G.Nonempty) (hHG : Disjoint H G) :
    ∃ H', Fold.Q78.IsContinuum H' ∧ H ⊆ H' ∧ Disjoint H' G ∧ IsPreconnected H'ᶜ ∧
      closure H'ᶜ ∩ H' ⊆ H := by
  haveI := hS.connected
  obtain ⟨g, hg⟩ := hGne
  have hgH : g ∉ H := fun h => Set.disjoint_left.mp hHG h hg
  set P := connectedComponentIn Hᶜ g with hP_def
  have hPo : IsOpen P := hS.isOpen_component_compl hH hgH
  have hGP : G ⊆ P :=
    hG.subset_connectedComponentIn hg fun x hx hxH => Set.disjoint_left.mp hHG hxH hx
  have hPH : P ⊆ Hᶜ := connectedComponentIn_subset _ _
  have hHP : H ⊆ Pᶜ := fun x hx hxP => hPH hxP hx
  have key : ∀ u v : Set S, IsClosed u → IsClosed v → Pᶜ ⊆ u ∪ v → Disjoint u v → H ⊆ u →
      Pᶜ ⊆ u := by
    intro u v hu hv hcov huv hHu
    have hw : Pᶜ ∩ v = (Pᶜ ∩ Hᶜ) ∩ uᶜ := by
      ext x
      constructor
      · rintro ⟨hxP, hxv⟩
        exact ⟨⟨hxP, fun hxH => Set.disjoint_left.mp huv (hHu hxH) hxv⟩,
          fun hxu => Set.disjoint_left.mp huv hxu hxv⟩
      · rintro ⟨⟨hxP, _⟩, hxu⟩
        exact ⟨hxP, (hcov hxP).resolve_left hxu⟩
    have hclo : IsClopen (Pᶜ ∩ v) :=
      ⟨hPo.isClosed_compl.inter hv, hw ▸ (hS.isOpen_compl_diff_component hH g).inter
        hu.isOpen_compl⟩
    rcases isClopen_iff.mp hclo with h | h
    · intro x hx
      refine (hcov hx).resolve_right fun hxv => ?_
      have : x ∈ Pᶜ ∩ v := ⟨hx, hxv⟩
      rw [h] at this; exact this
    · exact absurd (h ▸ mem_univ g : g ∈ Pᶜ ∩ v).1 (not_not.mpr (mem_connectedComponentIn hgH))
  refine ⟨Pᶜ, ⟨hPo.isClosed_compl.isCompact, ⟨hH.2.1.mono hHP, ?_⟩⟩, hHP, ?_, ?_, ?_⟩
  · rw [isPreconnected_iff_subset_of_fully_disjoint_closed hPo.isClosed_compl]
    intro u v hu hv hcov huv
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hH.2.2 u v hu hv (hHP.trans hcov)
      (by rw [Set.disjoint_iff_inter_eq_empty.mp huv, inter_empty]) with h | h
    · exact Or.inl (key u v hu hv hcov huv h)
    · exact Or.inr (key v u hv hu (by rw [union_comm]; exact hcov) huv.symm h)
  · exact Set.disjoint_left.mpr fun x hx hxG => hx (hGP hxG)
  · rw [compl_compl]; exact isPreconnected_connectedComponentIn
  · rw [compl_compl]
    rintro z ⟨hzcl, hzP⟩
    by_contra hzH
    obtain ⟨y, hyQ, hyP⟩ := mem_closure_iff.mp hzcl _ (hS.isOpen_component_compl hH hzH)
      (mem_connectedComponentIn hzH)
    apply hzP
    rw [hP_def, connectedComponentIn_eq hyP, ← connectedComponentIn_eq hyQ]
    exact mem_connectedComponentIn hzH

/-- One half of the unicoherence argument: `X ∪ Y ∪ U` is connected. -/
theorem piece_preconnected (hS : BingS S) {X Y U A : Set S} (hX : Fold.Q78.IsContinuum X)
    (hY : Fold.Q78.IsContinuum Y) (dXY : Disjoint X Y) (pX : IsPreconnected Xᶜ)
    (pY : IsPreconnected Yᶜ) (hU : IsOpen U) (hUne : U.Nonempty) (hUX : Disjoint U X)
    (hUY : Disjoint U Y) (hA : IsClosed A) (hAeq : A = X ∪ Y ∪ U) : IsPreconnected A := by
  haveI := hS.connected
  have hXA : X ⊆ A := hAeq ▸ subset_union_left.trans subset_union_left
  have hYA : Y ⊆ A := hAeq ▸ subset_union_right.trans subset_union_left
  have hUA : U ⊆ A := hAeq ▸ subset_union_right
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hA]
  intro a b ha hb hcov hab
  have side : ∀ Z : Set S, Fold.Q78.IsContinuum Z → Z ⊆ A → Z ⊆ a ∨ Z ⊆ b := fun Z hZ hZA =>
    isPreconnected_iff_subset_of_disjoint_closed.mp hZ.2.2 a b ha hb (hZA.trans hcov)
      (by rw [Set.disjoint_iff_inter_eq_empty.mp hab, inter_empty])
  wlog hXa : X ⊆ a generalizing a b
  · rcases side X hX hXA with h | h
    · exact absurd h hXa
    · rw [or_comm]
      exact this b a hb ha (by rw [union_comm]; exact hcov) hab.symm
        (fun Z hZ hZA => (side Z hZ hZA).symm) h
  rcases side Y hY hYA with hYa | hYb
  · left
    have hw : A ∩ b = U ∩ aᶜ := by
      ext x
      constructor
      · rintro ⟨hxA, hxb⟩
        have hxa : x ∉ a := fun hxa => Set.disjoint_left.mp hab hxa hxb
        rw [hAeq] at hxA
        rcases hxA with (h | h) | h
        · exact absurd (hXa h) hxa
        · exact absurd (hYa h) hxa
        · exact ⟨h, hxa⟩
      · rintro ⟨hxU, hxa⟩
        exact ⟨hUA hxU, (hcov (hUA hxU)).resolve_left hxa⟩
    have hclo : IsClopen (A ∩ b) := ⟨hA.inter hb, hw ▸ hU.inter ha.isOpen_compl⟩
    rcases isClopen_iff.mp hclo with h | h
    · intro x hx
      refine (hcov hx).resolve_right fun hxb => ?_
      have : x ∈ A ∩ b := ⟨hx, hxb⟩
      rw [h] at this; exact this
    · obtain ⟨x, hx⟩ := hX.2.1
      exact absurd (h ▸ mem_univ x : x ∈ A ∩ b).2
        (fun hxb => Set.disjoint_left.mp hab (hXa hx) hxb)
  · exfalso
    -- `U` lies in `b` (else `Xᶜ` is disconnected) and in `a` (else `Yᶜ` is)
    have hUb : U ⊆ b := by
      by_contra hnot
      obtain ⟨u, huU, hub⟩ := not_subset.mp hnot
      have hWa : U ∩ bᶜ ⊆ a := fun x hx => (hcov (hUA hx.1)).resolve_right hx.2
      have hsub := subset_of_relClopen pX (hU.inter hb.isOpen_compl)
        (fun x hx hxX => Set.disjoint_left.mp hUX hx.1 hxX)
        (by
          rintro x ⟨hxcl, hxX⟩
          have hxa : x ∈ a := closure_minimal hWa ha hxcl
          have hxA : x ∈ A := closure_minimal (inter_subset_left.trans hUA) hA hxcl
          rw [hAeq] at hxA
          rcases hxA with (h | h) | h
          · exact absurd h hxX
          · exact absurd (hYb h) (fun hxb => Set.disjoint_left.mp hab hxa hxb)
          · exact ⟨h, fun hxb => Set.disjoint_left.mp hab hxa hxb⟩)
        ⟨u, huU, hub⟩
      obtain ⟨y, hy⟩ := hY.2.1
      exact (hsub (fun hyX => Set.disjoint_left.mp dXY hyX hy)).2 (hYb hy)
    have hUa : U ⊆ a := by
      by_contra hnot
      obtain ⟨u, huU, hua⟩ := not_subset.mp hnot
      have hWb : U ∩ aᶜ ⊆ b := fun x hx => (hcov (hUA hx.1)).resolve_left hx.2
      have hsub := subset_of_relClopen pY (hU.inter ha.isOpen_compl)
        (fun x hx hxY => Set.disjoint_left.mp hUY hx.1 hxY)
        (by
          rintro x ⟨hxcl, hxY⟩
          have hxb : x ∈ b := closure_minimal hWb hb hxcl
          have hxA : x ∈ A := closure_minimal (inter_subset_left.trans hUA) hA hxcl
          rw [hAeq] at hxA
          rcases hxA with (h | h) | h
          · exact absurd (hXa h) (fun hxa => Set.disjoint_left.mp hab hxa hxb)
          · exact absurd h hxY
          · exact ⟨h, fun hxa => Set.disjoint_left.mp hab hxa hxb⟩)
        ⟨u, huU, hua⟩
      obtain ⟨x, hx⟩ := hX.2.1
      exact (hsub (fun hxY => Set.disjoint_left.mp dXY hx hxY)).2 (hXa hx)
    obtain ⟨u, hu⟩ := hUne
    exact Set.disjoint_left.mp hab (hUa hu) (hUb hu)

/-- **Unicoherence**: between two disjoint subcontinua with connected complements, the region
`Xᶜ ∩ Yᶜ` is connected. -/
theorem BingS.compl_inter_preconnected (hS : BingS S) {X Y : Set S}
    (hX : Fold.Q78.IsContinuum X) (hY : Fold.Q78.IsContinuum Y) (dXY : Disjoint X Y)
    (pX : IsPreconnected Xᶜ) (pY : IsPreconnected Yᶜ) : IsPreconnected (Xᶜ ∩ Yᶜ) := by
  haveI := hS.connected
  haveI := hS.nontrivial
  set C := Xᶜ ∩ Yᶜ with hC_def
  have hCo : IsOpen C := hX.1.isClosed.isOpen_compl.inter hY.1.isClosed.isOpen_compl
  intro u v hu hv hcov hun hvn
  by_contra huv
  rw [not_nonempty_iff_eq_empty] at huv
  have hpiece : ∀ u v : Set S, IsOpen u → IsOpen v → C ⊆ u ∪ v → (C ∩ u).Nonempty →
      C ∩ (u ∩ v) = ∅ → IsPreconnected (C ∩ v)ᶜ := by
    intro u v hu hv hcov hun huv
    refine piece_preconnected hS hX hY dXY pX pY (hCo.inter hu) hun
      (Set.disjoint_left.mpr fun x hx hxX => hx.1.1 hxX)
      (Set.disjoint_left.mpr fun x hx hxY => hx.1.2 hxY) (hCo.inter hv).isClosed_compl ?_
    ext x
    simp only [mem_compl_iff, mem_inter_iff, not_and, mem_union]
    constructor
    · intro h
      by_cases hxC : x ∈ C
      · exact Or.inr ⟨hxC, (hcov hxC).resolve_right (h hxC)⟩
      · simp only [hC_def, mem_inter_iff, mem_compl_iff, not_and, not_not] at hxC
        by_cases hxX : x ∈ X
        · exact Or.inl (Or.inl hxX)
        · exact Or.inl (Or.inr (hxC hxX))
    · rintro ((h | h) | ⟨hxC, hxu⟩) hxC'
      · exact absurd h hxC'.1
      · exact absurd h hxC'.2
      · intro hxv
        have : x ∈ C ∩ (u ∩ v) := ⟨hxC, hxu, hxv⟩
        rw [huv] at this; exact this
  have hA := hpiece u v hu hv hcov hun huv
  have hB := hpiece v u hv hu (by rw [union_comm]; exact hcov) hvn (by rw [inter_comm v u]; exact huv)
  have hAB : (C ∩ v)ᶜ ∪ (C ∩ u)ᶜ = univ := by
    rw [← compl_inter, compl_eq_univ_diff]
    rw [show C ∩ v ∩ (C ∩ u) = ∅ by
      rw [← huv]; ext x; simp only [mem_inter_iff]; tauto]
    simp
  have huni := hS.hu univ subset_rfl ⟨isCompact_univ, isConnected_univ⟩ nontrivial_univ
    (C ∩ v)ᶜ (C ∩ u)ᶜ ⟨(hCo.inter hv).isClosed_compl.isCompact, ⟨?_, hA⟩⟩
    ⟨(hCo.inter hu).isClosed_compl.isCompact, ⟨?_, hB⟩⟩ hAB
  · have hsub : (C ∩ v)ᶜ ∩ (C ∩ u)ᶜ ⊆ X ∪ Y := by
      intro x ⟨h1, h2⟩
      by_contra hxXY
      simp only [mem_union, not_or] at hxXY
      have hxC : x ∈ C := ⟨hxXY.1, hxXY.2⟩
      rcases hcov hxC with h | h
      · exact h2 ⟨hxC, h⟩
      · exact h1 ⟨hxC, h⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp huni.2 X Y hX.1.isClosed
      hY.1.isClosed hsub (by
        rw [Set.disjoint_iff_inter_eq_empty.mp dXY, inter_empty]) with h | h
    · obtain ⟨y, hy⟩ := hY.2.1
      have hy' : y ∈ (C ∩ v)ᶜ ∩ (C ∩ u)ᶜ :=
        ⟨fun hyC => hyC.1.2 hy, fun hyC => hyC.1.2 hy⟩
      exact Set.disjoint_left.mp dXY (h hy') hy
    · obtain ⟨x, hx⟩ := hX.2.1
      have hx' : x ∈ (C ∩ v)ᶜ ∩ (C ∩ u)ᶜ :=
        ⟨fun hxC => hxC.1.1 hx, fun hxC => hxC.1.1 hx⟩
      exact Set.disjoint_left.mp dXY hx (h hx')
  · obtain ⟨x, hx⟩ := hX.2.1; exact ⟨x, fun hxC => hxC.1.1 hx⟩
  · obtain ⟨x, hx⟩ := hX.2.1; exact ⟨x, fun hxC => hxC.1.1 hx⟩

/-- **The region between two disjoint subcontinua** (Bing's `C`, property 5): an open connected
set missing both whose closure meets both. -/
theorem BingS.exists_between (hS : BingS S) {H₁ H₂ : Set S} (h₁ : Fold.Q78.IsContinuum H₁)
    (h₂ : Fold.Q78.IsContinuum H₂) (d : Disjoint H₁ H₂) :
    ∃ C : Set S, IsOpen C ∧ IsPreconnected C ∧ C.Nonempty ∧ Disjoint C H₁ ∧ Disjoint C H₂ ∧
      (closure C ∩ H₁).Nonempty ∧ (closure C ∩ H₂).Nonempty := by
  haveI := hS.connected
  obtain ⟨X, cX, sX, dX, pX, clX⟩ := hS.fill h₁ h₂.2.2 h₂.2.1 d
  obtain ⟨Y, cY, sY, dY, pY, clY⟩ := hS.fill h₂ cX.2.2 cX.2.1 dX.symm
  have dXY : Disjoint X Y := dY.symm
  set C := Xᶜ ∩ Yᶜ with hC_def
  have hCo : IsOpen C := cX.1.isClosed.isOpen_compl.inter cY.1.isClosed.isOpen_compl
  have hCne : C.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ X Y
      cX.1.isClosed cY.1.isClosed (fun x _ => by
        by_contra hx
        simp only [mem_union, not_or] at hx
        have : x ∈ C := ⟨hx.1, hx.2⟩
        rw [h] at this; exact this)
      (by rw [Set.disjoint_iff_inter_eq_empty.mp dXY, inter_empty]) with h' | h'
    · obtain ⟨y, hy⟩ := cY.2.1
      exact Set.disjoint_left.mp dXY (h' (mem_univ y)) hy
    · obtain ⟨x, hx⟩ := cX.2.1
      exact Set.disjoint_left.mp dXY hx (h' (mem_univ x))
  -- the closure of `C` meets the far continuum
  have meets : ∀ X Y : Set S, Fold.Q78.IsContinuum Y → Disjoint X Y → IsPreconnected Xᶜ →
      IsOpen (Xᶜ ∩ Yᶜ) → (Xᶜ ∩ Yᶜ).Nonempty → (closure (Xᶜ ∩ Yᶜ) ∩ Y).Nonempty := by
    intro X Y cY dXY pX hCo hCne
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hsub := subset_of_relClopen pX hCo inter_subset_left (by
      rintro x ⟨hxcl, hxX⟩
      refine ⟨hxX, fun hxY => ?_⟩
      have : x ∈ closure (Xᶜ ∩ Yᶜ) ∩ Y := ⟨hxcl, hxY⟩
      rw [hno] at this; exact this) hCne
    obtain ⟨y, hy⟩ := cY.2.1
    exact (hsub (fun hyX => Set.disjoint_left.mp dXY hyX hy)).2 hy
  obtain ⟨z₂, hz₂cl, hz₂Y⟩ := meets X Y cY dXY pX hCo hCne
  obtain ⟨z₁, hz₁cl, hz₁X⟩ := meets Y X cX dXY.symm pY (by rw [inter_comm]; exact hCo)
    (by rw [inter_comm]; exact hCne)
  rw [inter_comm] at hz₁cl
  refine ⟨C, hCo, hS.compl_inter_preconnected cX cY dXY pX pY, hCne,
    Set.disjoint_left.mpr fun x hx hx1 => hx.1 (sX hx1),
    Set.disjoint_left.mpr fun x hx hx2 => hx.2 (sY hx2),
    ⟨z₁, hz₁cl, clX ⟨closure_mono inter_subset_left hz₁cl, hz₁X⟩⟩,
    ⟨z₂, hz₂cl, clY ⟨closure_mono inter_subset_right hz₂cl, hz₂Y⟩⟩⟩

/-- **No crossing** (property 3): a subcontinuum of `closure C` meeting both `H₁` and `H₂` contains
all of `C`. -/
theorem no_crossing (hS : BingS S) {H₁ H₂ C L : Set S} (h₁ : Fold.Q78.IsContinuum H₁)
    (h₂ : Fold.Q78.IsContinuum H₂) (hi₁ : (interior H₁).Nonempty)
    (hi₂ : (interior H₂).Nonempty) (d : Disjoint H₁ H₂) (hCc : IsPreconnected C)
    (hC1 : Disjoint C H₁) (hC2 : Disjoint C H₂) (hL : Fold.Q78.IsContinuum L)
    (hLD : L ⊆ closure C) (hL1 : (L ∩ H₁).Nonempty) (hL2 : (L ∩ H₂).Nonempty) {c : S}
    (hc : c ∈ C) (hcL : c ∉ L) : False := by
  have hD : Fold.Q78.IsContinuum (closure C) :=
    ⟨isClosed_closure.isCompact, (IsConnected.closure ⟨⟨c, hc⟩, hCc⟩)⟩
  have e1 : Disjoint (closure C) (interior H₁) :=
    (hC1.mono_right interior_subset).closure_left isOpen_interior
  have e2 : Disjoint (closure C) (interior H₂) :=
    (hC2.mono_right interior_subset).closure_left isOpen_interior
  obtain ⟨l, hl⟩ := hL.2.1
  rcases prop3_one_in_union hS (isContinuum_union h₁ hL (by rw [inter_comm]; exact hL1))
    (isContinuum_union h₂ hL (by rw [inter_comm]; exact hL2)) hD
    ⟨l, Or.inr hl, Or.inr hl⟩ ⟨l, Or.inr hl, hLD hl⟩ ⟨l, Or.inr hl, hLD hl⟩ with h | h | h
  · obtain ⟨x, hx⟩ := hi₁
    rcases h (Or.inl (interior_subset hx)) with (h' | h') | h'
    · exact Set.disjoint_left.mp d (interior_subset hx) h'
    · exact Set.disjoint_left.mp e1 (hLD h') hx
    · exact Set.disjoint_left.mp e1 h' hx
  · obtain ⟨x, hx⟩ := hi₂
    rcases h (Or.inl (interior_subset hx)) with (h' | h') | h'
    · exact Set.disjoint_left.mp d h' (interior_subset hx)
    · exact Set.disjoint_left.mp e2 (hLD h') hx
    · exact Set.disjoint_left.mp e2 h' hx
  · rcases h (subset_closure hc) with (h' | h') | (h' | h')
    · exact Set.disjoint_left.mp hC1 hc h'
    · exact hcL h'
    · exact Set.disjoint_left.mp hC2 hc h'
    · exact hcL h'

/-- **Core of property 5**: the closure of Bing's region `C` contains a subcontinuum with
interior points missing `H₁` and `H₂`. (Bing: `C̄` is the sum of three continua each with an
interior point in neither of the others; the third is obtained from a minimal decomposition.) -/
theorem prop5_core (hS : BingS S) {H₁ H₂ C : Set S} (h₁ : Fold.Q78.IsContinuum H₁)
    (h₂ : Fold.Q78.IsContinuum H₂) (hi₁ : (interior H₁).Nonempty)
    (hi₂ : (interior H₂).Nonempty) (d : Disjoint H₁ H₂) (hCo : IsOpen C) (hCc : IsPreconnected C)
    (hCne : C.Nonempty) (hC1 : Disjoint C H₁) (hC2 : Disjoint C H₂)
    (hz1 : (closure C ∩ H₁).Nonempty) (hz2 : (closure C ∩ H₂).Nonempty) :
    ∃ K, Fold.Q78.IsContinuum K ∧ K ⊆ closure C ∧ Disjoint K H₁ ∧ Disjoint K H₂ ∧
      (interior K).Nonempty := by
  set D := closure C with hD_def
  have hD : Fold.Q78.IsContinuum D := ⟨isClosed_closure.isCompact, IsConnected.closure ⟨hCne, hCc⟩⟩
  have hDnt : D.Nontrivial := (hS.open_nontrivial hCo hCne).mono subset_closure
  obtain ⟨A, B, hA, hB, hAD, hBD, hABD⟩ := hS.hd D (subset_univ _) hD hDnt
  have hAD' : A ⊆ D := hABD ▸ subset_union_left
  have hBD' : B ⊆ D := hABD ▸ subset_union_right
  -- private interior points
  have priv : ∀ F G : Set S, IsClosed F → D ⊆ F ∪ G → ¬ D ⊆ F →
      ∃ p ∈ C, p ∉ F ∧ p ∈ interior G := by
    intro F G hF hFG hnot
    obtain ⟨x, hxD, hxF⟩ := not_subset.mp hnot
    obtain ⟨p, hpF, hpC⟩ := mem_closure_iff.mp hxD Fᶜ hF.isOpen_compl hxF
    refine ⟨p, hpC, hpF, interior_maximal (fun y hy => ?_) (hCo.inter hF.isOpen_compl) ⟨hpC, hpF⟩⟩
    exact (hFG (subset_closure hy.1)).resolve_left hy.2
  have hnA : ¬ D ⊆ A := fun h => hAD (Subset.antisymm hAD' h)
  -- a minimal `B'` with `A ∪ B' = D`
  set 𝔉 : Set (Set S) := {B' | Fold.Q78.IsContinuum B' ∧ B' ⊆ B ∧ A ∪ B' = D} with h𝔉
  obtain ⟨B', -, hB'min⟩ := zorn_superset_nonempty 𝔉 (fun c hc _ hcne => by
    refine ⟨⋂₀ c, ⟨prop1_inter_continuum hS hcne (fun K hK => (hc hK).1) ?_, ?_, ?_⟩, ?_⟩
    · obtain ⟨x, hxD, hxA⟩ := not_subset.mp hnA
      refine ⟨x, mem_sInter.mpr fun K hK => ?_⟩
      have := (hc hK).2.2 ▸ hxD
      exact this.resolve_left hxA
    · obtain ⟨K, hK⟩ := hcne
      exact (sInter_subset_of_mem hK).trans (hc hK).2.1
    · apply Subset.antisymm
      · obtain ⟨K, hK⟩ := hcne
        exact union_subset hAD' ((sInter_subset_of_mem hK).trans ((hc hK).2.2 ▸ subset_union_right))
      · intro x hxD
        by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr (mem_sInter.mpr fun K hK => (((hc hK).2.2 ▸ hxD :
            x ∈ A ∪ K)).resolve_left hxA)
    · exact fun s hs => sInter_subset_of_mem hs) B ⟨hB, subset_rfl, hABD⟩
  obtain ⟨hB', hB'B, hAB'⟩ := hB'min.prop
  have hB'D : B' ⊆ D := hB'B.trans hBD'
  obtain ⟨pA, hpAC, hpAB', hpAi⟩ := priv B' A hB'.1.isClosed (by rw [union_comm, hAB'])
    (fun h => hBD (Subset.antisymm hBD' (h.trans hB'B)))
  obtain ⟨q, hqC, -, hqi⟩ := priv A B' hA.1.isClosed hAB'.symm.subset hnA
  have hB'nt : B'.Nontrivial :=
    (hS.open_nontrivial isOpen_interior ⟨q, hqi⟩).mono interior_subset
  obtain ⟨B₁, B₂, hB₁, hB₂, hB₁ne, hB₂ne, hB₁₂⟩ := hS.hd B' (subset_univ _) hB' hB'nt
  have hB₁B' : B₁ ⊆ B' := hB₁₂ ▸ subset_union_left
  have hB₂B' : B₂ ⊆ B' := hB₁₂ ▸ subset_union_right
  have notD : ∀ Bi : Set S, Fold.Q78.IsContinuum Bi → Bi ⊆ B' → Bi ≠ B' → ¬ D ⊆ A ∪ Bi := by
    intro Bi hBi hBiB' hne h
    have hmem : Bi ∈ 𝔉 := ⟨hBi, hBiB'.trans hB'B,
      Subset.antisymm (union_subset hAD' (hBiB'.trans hB'D)) h⟩
    exact hne (Subset.antisymm hBiB' (hB'min.le_of_le hmem hBiB'))
  obtain ⟨p₁, hp₁C, hp₁F, hp₁i⟩ := priv (A ∪ B₂) B₁ (hA.1.isClosed.union hB₂.1.isClosed)
    (by rw [← hAB', ← hB₁₂]; intro x hx; simp only [mem_union] at hx ⊢; tauto)
    (fun h => notD B₂ hB₂ hB₂B' hB₂ne h)
  obtain ⟨p₂, hp₂C, hp₂F, hp₂i⟩ := priv (A ∪ B₁) B₂ (hA.1.isClosed.union hB₁.1.isClosed)
    (by rw [← hAB', ← hB₁₂]; intro x hx; simp only [mem_union] at hx ⊢; tauto)
    (fun h => notD B₁ hB₁ hB₁B' hB₁ne h)
  simp only [mem_union, not_or] at hp₁F hp₂F
  -- if one of the three pieces misses `H₁ ∪ H₂`, it is the required continuum
  by_cases cA : Disjoint A H₁ ∧ Disjoint A H₂
  · exact ⟨A, hA, hAD', cA.1, cA.2, pA, hpAi⟩
  by_cases c1 : Disjoint B₁ H₁ ∧ Disjoint B₁ H₂
  · exact ⟨B₁, hB₁, hB₁B'.trans hB'D, c1.1, c1.2, p₁, hp₁i⟩
  by_cases c2 : Disjoint B₂ H₁ ∧ Disjoint B₂ H₂
  · exact ⟨B₂, hB₂, hB₂B'.trans hB'D, c2.1, c2.2, p₂, hp₂i⟩
  exfalso
  simp only [not_and_or, not_disjoint_iff_nonempty_inter] at cA c1 c2
  have NC := fun {L : Set S} (hL : Fold.Q78.IsContinuum L) (hLD : L ⊆ D) (h1 : (L ∩ H₁).Nonempty)
    (h2 : (L ∩ H₂).Nonempty) {c : S} (hc : c ∈ C) (hcL : c ∉ L) =>
    no_crossing hS h₁ h₂ hi₁ hi₂ d hCc hC1 hC2 hL hLD h1 h2 hc hcL
  -- `A` and `B'` meet
  have hAB'ne : (A ∩ B').Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hD.2.2 A B' hA.1.isClosed
      hB'.1.isClosed hAB'.symm.subset (by rw [h, inter_empty]) with h' | h'
    · have : q ∈ A ∩ B' := ⟨h' (hB'D (interior_subset hqi)), interior_subset hqi⟩
      rw [h] at this; exact this
    · have : pA ∈ A ∩ B' := ⟨interior_subset hpAi, h' (hAD' (interior_subset hpAi))⟩
      rw [h] at this; exact this
  have hA12 : ¬ ((A ∩ H₁).Nonempty ∧ (A ∩ H₂).Nonempty) := fun h =>
    NC hA hAD' h.1 h.2 hp₁C hp₁F.1
  have hB12 : ¬ ((B' ∩ H₁).Nonempty ∧ (B' ∩ H₂).Nonempty) := fun h =>
    NC hB' hB'D h.1 h.2 hpAC hpAB'
  have side : ∀ {H : Set S}, (D ∩ H).Nonempty → (A ∩ H).Nonempty ∨ (B' ∩ H).Nonempty := by
    rintro H ⟨x, hxD, hxH⟩
    rcases (hAB' ▸ hxD : x ∈ A ∪ B') with h | h
    · exact Or.inl ⟨x, h, hxH⟩
    · exact Or.inr ⟨x, h, hxH⟩
  have up1 : ∀ {H : Set S}, (B₁ ∩ H).Nonempty → (B' ∩ H).Nonempty := fun h =>
    h.mono (inter_subset_inter_left _ hB₁B')
  have up2 : ∀ {H : Set S}, (B₂ ∩ H).Nonempty → (B' ∩ H).Nonempty := fun h =>
    h.mono (inter_subset_inter_left _ hB₂B')
  have hAB : (A ∩ B₁).Nonempty ∨ (A ∩ B₂).Nonempty := by
    obtain ⟨x, hxA, hxB'⟩ := hAB'ne
    rcases (hB₁₂ ▸ hxB' : x ∈ B₁ ∪ B₂) with h | h
    · exact Or.inl ⟨x, hxA, h⟩
    · exact Or.inr ⟨x, hxA, h⟩
  have L1 : (A ∩ B₁).Nonempty →
      Fold.Q78.IsContinuum (A ∪ B₁) ∧ A ∪ B₁ ⊆ D ∧ p₂ ∉ A ∪ B₁ := fun h =>
    ⟨isContinuum_union hA hB₁ h, union_subset hAD' (hB₁B'.trans hB'D),
      fun h' => h'.elim hp₂F.1 hp₂F.2⟩
  have L2 : (A ∩ B₂).Nonempty →
      Fold.Q78.IsContinuum (A ∪ B₂) ∧ A ∪ B₂ ⊆ D ∧ p₁ ∉ A ∪ B₂ := fun h =>
    ⟨isContinuum_union hA hB₂ h, union_subset hAD' (hB₂B'.trans hB'D),
      fun h' => h'.elim hp₁F.1 hp₁F.2⟩
  have ml : ∀ {X Y H : Set S}, (X ∩ H).Nonempty → ((X ∪ Y) ∩ H).Nonempty := fun h =>
    h.mono (inter_subset_inter_left _ subset_union_left)
  have mr : ∀ {X Y H : Set S}, (Y ∩ H).Nonempty → ((X ∪ Y) ∩ H).Nonempty := fun h =>
    h.mono (inter_subset_inter_left _ subset_union_right)
  rcases side hz1 with hA1 | hB1
  · rcases side hz2 with hA2 | hB2
    · exact hA12 ⟨hA1, hA2⟩
    · have hB1' : ¬ (B' ∩ H₁).Nonempty := fun h => hB12 ⟨h, hB2⟩
      have e1 : (B₁ ∩ H₂).Nonempty := c1.resolve_left fun h => hB1' (up1 h)
      have e2 : (B₂ ∩ H₂).Nonempty := c2.resolve_left fun h => hB1' (up2 h)
      rcases hAB with h | h
      · obtain ⟨hL, hLD, hc⟩ := L1 h; exact NC hL hLD (ml hA1) (mr e1) hp₂C hc
      · obtain ⟨hL, hLD, hc⟩ := L2 h; exact NC hL hLD (ml hA1) (mr e2) hp₁C hc
  · have hB2' : ¬ (B' ∩ H₂).Nonempty := fun h => hB12 ⟨hB1, h⟩
    have hA2 : (A ∩ H₂).Nonempty := (side hz2).resolve_right hB2'
    have e1 : (B₁ ∩ H₁).Nonempty := c1.resolve_right fun h => hB2' (up1 h)
    have e2 : (B₂ ∩ H₁).Nonempty := c2.resolve_right fun h => hB2' (up2 h)
    rcases hAB with h | h
    · obtain ⟨hL, hLD, hc⟩ := L1 h; exact NC hL hLD (mr e1) (ml hA2) hp₂C hc
    · obtain ⟨hL, hLD, hc⟩ := L2 h; exact NC hL hLD (mr e2) (ml hA2) hp₁C hc

/-! ## Properties 5 and 6 -/

/-- **Property 5.** Two mutually exclusive subcontinua with interior points are separated by a
subcontinuum with interior points. -/
theorem prop5_exists_separating (hS : BingS S) {H₁ H₂ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂)
    (hi₁ : (interior H₁).Nonempty) (hi₂ : (interior H₂).Nonempty) (d : Disjoint H₁ H₂) :
    ∃ K : Set S, Fold.Q78.IsContinuum K ∧ (interior K).Nonempty ∧ Separates K H₁ H₂ := by
  obtain ⟨C, hCo, hCc, hCne, hC1, hC2, hz1, hz2⟩ := hS.exists_between h₁ h₂ d
  obtain ⟨K, hK, hKD, dK1, dK2, hKi⟩ :=
    prop5_core hS h₁ h₂ hi₁ hi₂ d hCo hCc hCne hC1 hC2 hz1 hz2
  refine ⟨K, hK, hKi, ?_⟩
  obtain ⟨k, hk⟩ := hK.2.1
  rcases prop4_separates hS h₁ h₂ hK hi₁ hi₂ hKi d dK2.symm dK1.symm with h | h | h
  · exfalso
    obtain ⟨z, hzcl, hzH⟩ := hz2
    obtain ⟨y, hy⟩ := h₂.2.1
    refine not_separates_of_preconnected (preconnected_through hCc hKD hzcl hzH h₂.2.2) ?_
      ⟨y, Or.inr hy, hy⟩ ⟨k, Or.inl (Or.inr hk), hk⟩ h
    exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hC1, dK1⟩, d.symm⟩
  · exfalso
    obtain ⟨z, hzcl, hzH⟩ := hz1
    obtain ⟨y, hy⟩ := h₁.2.1
    refine not_separates_of_preconnected (preconnected_through hCc hKD hzcl hzH h₁.2.2) ?_
      ⟨y, Or.inr hy, hy⟩ ⟨k, Or.inl (Or.inr hk), hk⟩ h
    exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hC2, dK2⟩, d⟩
  · exact h

/-- A piece of a splitting of the complement of a subcontinuum into two open sets is connected
(property 2). -/
theorem BingS.split_piece_preconnected (hS : BingS S) {H : Set S} (hH : Fold.Q78.IsContinuum H)
    {u v : Set S} (hu : IsOpen u) (hv : IsOpen v) (hcov : Hᶜ ⊆ u ∪ v)
    (hvn : (Hᶜ ∩ v).Nonempty) (dUV : Disjoint (Hᶜ ∩ u) (Hᶜ ∩ v)) : IsPreconnected (Hᶜ ∩ u) := by
  have hO : IsOpen Hᶜ := hH.1.isClosed.isOpen_compl
  by_contra hnc
  simp only [IsPreconnected, not_forall, exists_prop] at hnc
  obtain ⟨u₁, v₁, hu₁, hv₁, hcov₁, hun₁, hvn₁, huv₁⟩ := hnc
  rw [not_nonempty_iff_eq_empty] at huv₁
  refine hS.no_three_open hH ((hO.inter hu).inter hu₁) ((hO.inter hu).inter hv₁)
    (hO.inter hv) hun₁ hvn₁ hvn ?_ ?_ ?_ ?_
  · rw [Set.disjoint_iff_inter_eq_empty, ← huv₁]; ext x; simp only [mem_inter_iff]; tauto
  · exact dUV.mono inter_subset_left le_rfl
  · exact dUV.mono inter_subset_left le_rfl
  · ext x
    simp only [mem_diff, mem_univ, true_and, mem_union, mem_inter_iff, mem_compl_iff]
    constructor
    · intro hx
      rcases hcov hx with h | h
      · rcases hcov₁ ⟨hx, h⟩ with h' | h'
        · exact Or.inl (Or.inl ⟨⟨hx, h⟩, h'⟩)
        · exact Or.inl (Or.inr ⟨⟨hx, h⟩, h'⟩)
      · exact Or.inr ⟨hx, h⟩
    · rintro ((⟨⟨hx, _⟩, _⟩ | ⟨⟨hx, _⟩, _⟩) | ⟨hx, _⟩) <;> exact hx

/-- **Bing's `H(C)`** (property 6): for an open connected `C` whose closure misses the continuum
`H₂` with interior points, there is a continuum containing `H₂` interiorly and missing `closure C`:
the separating continuum `K` of property 5 together with the side of `S \ K` containing `H₂`. -/
theorem BingS.side_continuum (hS : BingS S) {C H₂ : Set S} (hCo : IsOpen C)
    (hCc : IsPreconnected C) (hCne : C.Nonempty) (h₂ : Fold.Q78.IsContinuum H₂)
    (hi₂ : (interior H₂).Nonempty) (d : Disjoint (closure C) H₂) :
    ∃ H', Fold.Q78.IsContinuum H' ∧ H₂ ⊆ interior H' ∧ Disjoint H' (closure C) := by
  haveI := hS.connected
  have hD : Fold.Q78.IsContinuum (closure C) :=
    ⟨isClosed_closure.isCompact, IsConnected.closure ⟨hCne, hCc⟩⟩
  have hDi : (interior (closure C)).Nonempty :=
    hCne.mono (interior_maximal subset_closure hCo)
  obtain ⟨K, hK, -, dK1, dK2, U, V, hU, hV, hUV, hcov, hCU, hH₂V⟩ :=
    prop5_exists_separating hS hD h₂ hDi hi₂ d
  have hKo : IsOpen Kᶜ := hK.1.isClosed.isOpen_compl
  set W := Kᶜ ∩ V with hW_def
  have hWo : IsOpen W := hKo.inter hV
  have hH₂W : H₂ ⊆ W := fun x hx => ⟨fun hxK => Set.disjoint_left.mp dK2 hxK hx, hH₂V hx⟩
  have hCK : closure C ⊆ Kᶜ ∩ U := fun x hx =>
    ⟨fun hxK => Set.disjoint_left.mp dK1 hxK hx, hCU hx⟩
  obtain ⟨y, hy⟩ := h₂.2.1
  obtain ⟨c, hc⟩ := hCne
  have hcovK : Kᶜ ⊆ U ∪ V := fun x hx => hcov ⟨mem_univ x, hx⟩
  have dUVK : Disjoint (Kᶜ ∩ U) (Kᶜ ∩ V) := hUV.mono inter_subset_right inter_subset_right
  have hWpc : IsPreconnected W :=
    hS.split_piece_preconnected hK hV hU (by rw [union_comm]; exact hcovK)
      ⟨c, hCK (subset_closure hc)⟩ dUVK.symm
  have hH'eq : K ∪ W = (Kᶜ ∩ U)ᶜ := by
    ext x
    simp only [hW_def, mem_union, mem_inter_iff, mem_compl_iff, not_and]
    constructor
    · rintro (h | ⟨_, hxV⟩) hxK
      · exact absurd h hxK
      · exact fun hxU => Set.disjoint_left.mp hUV hxU hxV
    · intro h
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hxK, (hcovK hxK).resolve_left (h hxK)⟩
  -- `closure W` meets `K`
  have hz : (closure W ∩ K).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hWcl : closure W ⊆ W := by
      intro x hx
      have hx' : x ∈ (Kᶜ ∩ U)ᶜ := closure_minimal (fun z hz => by
        rw [← hH'eq]; exact Or.inr hz) (hKo.inter hU).isClosed_compl hx
      rw [← hH'eq] at hx'
      rcases hx' with h | h
      · have : x ∈ closure W ∩ K := ⟨hx, h⟩
        rw [hno] at this; exact this.elim
      · exact h
    have hclo : IsClopen W := ⟨closure_subset_iff_isClosed.mp hWcl, hWo⟩
    rcases isClopen_iff.mp hclo with h | h
    · have : y ∈ W := hH₂W hy
      rw [h] at this; exact this
    · have : c ∈ W := h ▸ mem_univ c
      exact Set.disjoint_left.mp dUVK (hCK (subset_closure hc)) this
  obtain ⟨z, hzcl, hzK⟩ := hz
  have hpc : IsPreconnected (W ∪ ∅ ∪ K) :=
    preconnected_through hWpc (empty_subset _) hzcl hzK hK.2.2
  rw [union_empty, union_comm] at hpc
  refine ⟨K ∪ W, ⟨(hH'eq ▸ (hKo.inter hU).isClosed_compl : IsClosed (K ∪ W)).isCompact,
    ⟨⟨y, Or.inr (hH₂W hy)⟩, hpc⟩⟩, hH₂W.trans (interior_maximal subset_union_right hWo), ?_⟩
  rw [hH'eq]
  exact Set.disjoint_left.mpr fun x hx hxC => hx (hCK hxC)

/-- **Property 6.** Between a continuum and a continuum it contains interiorly there is a third,
contained interiorly in the first and containing the second interiorly. -/
theorem prop6_between (hS : BingS S) {H₁ H₂ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (h₂ : Fold.Q78.IsContinuum H₂)
    (hi₂ : (interior H₂).Nonempty) (h₂₁ : H₂ ⊆ interior H₁) :
    ∃ H₃ : Set S, Fold.Q78.IsContinuum H₃ ∧ H₃ ⊆ interior H₁ ∧ H₂ ⊆ interior H₃ := by
  by_cases hH₁ : H₁ = univ
  · subst hH₁
    exact ⟨univ, h₁, by rw [interior_univ], by rw [interior_univ]; exact subset_univ _⟩
  have hO : IsOpen H₁ᶜ := h₁.1.isClosed.isOpen_compl
  have hne : H₁ᶜ.Nonempty := by
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem H₁).mp hH₁; exact ⟨x, hx⟩
  -- a closure of a piece of `H₁ᶜ` misses `H₂`
  have hfar : ∀ C ⊆ H₁ᶜ, Disjoint (closure C) H₂ := fun C hC =>
    ((Set.disjoint_left.mpr fun x hx hx' => hC hx (interior_subset hx')).closure_left
      isOpen_interior).mono_right h₂₁
  have hint : ∀ H : Set S, Disjoint H (closure H₁ᶜ) → H ⊆ interior H₁ := fun H hH x hx => by
    rw [← compl_compl (interior H₁), ← closure_compl]
    exact fun h => Set.disjoint_left.mp hH hx h
  by_cases hpc : IsPreconnected H₁ᶜ
  · obtain ⟨H', hH', hH₂H', dH'⟩ := hS.side_continuum hO hpc hne h₂ hi₂ (hfar _ subset_rfl)
    exact ⟨H', hH', hint H' dH', hH₂H'⟩
  · simp only [IsPreconnected, not_forall, exists_prop] at hpc
    obtain ⟨u, v, hu, hv, hcov, hun, hvn, huv⟩ := hpc
    rw [not_nonempty_iff_eq_empty] at huv
    have dUV : Disjoint (H₁ᶜ ∩ u) (H₁ᶜ ∩ v) := by
      rw [Set.disjoint_iff_inter_eq_empty, ← huv]; ext x; simp only [mem_inter_iff]; tauto
    have pu := hS.split_piece_preconnected h₁ hu hv hcov hvn dUV
    have pv := hS.split_piece_preconnected h₁ hv hu (by rw [union_comm]; exact hcov) hun
      dUV.symm
    obtain ⟨Hu, hHu, hH₂u, dHu⟩ := hS.side_continuum (hO.inter hu) pu hun h₂ hi₂
      (hfar _ inter_subset_left)
    obtain ⟨Hv, hHv, hH₂v, dHv⟩ := hS.side_continuum (hO.inter hv) pv hvn h₂ hi₂
      (hfar _ inter_subset_left)
    have hH₂ne : H₂.Nonempty := h₂.2.1
    refine ⟨Hu ∩ Hv, hS.inter_two hHu hHv (hH₂ne.mono fun x hx =>
      ⟨interior_subset (hH₂u hx), interior_subset (hH₂v hx)⟩), hint _ ?_, ?_⟩
    · have e : closure H₁ᶜ = closure (H₁ᶜ ∩ u) ∪ closure (H₁ᶜ ∩ v) := by
        rw [← closure_union]
        congr 1
        ext x
        simp only [mem_union, mem_inter_iff]
        constructor
        · intro hx
          rcases hcov hx with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      rw [e]
      exact Set.disjoint_union_right.mpr ⟨dHu.mono_left inter_subset_left,
        dHv.mono_left inter_subset_right⟩
    · rw [interior_inter]
      exact subset_inter hH₂u hH₂v

end HPC.Plane
