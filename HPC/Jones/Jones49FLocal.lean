import HPC.Jones.Jones49FTheta

/-!
# Batch 154: local separating points (Jones 1949 Theorem 1, Cases 1 and 2)

* `isLocalSepPoint_of_open_sub_tscc` — a point with a neighbourhood (in `M`) lying on a simple
  closed curve contained in `M` is a local separating point of `M` (Case 1, step 5; also the
  degenerate case `M = J` of Case 2).
* `isLocalSepPoint_of_separation` — if `M − b` is connected and `M − {a, b}` is the union of two
  nonempty separated sets, `a` is a local separating point (Case 2, step 7).
* `uncountable_of_nontrivial` — the instance needed by `jones49_some_order_two`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-- A simple closed curve (in the sense of `jordan_curve_theorem`) is a topological simple closed
curve. -/
theorem tscc_of_homeomorph_circle {J : Set Pt} (hJ : Nonempty (J ≃ₜ Circle)) : TSCC J := by
  obtain ⟨e⟩ := hJ
  have h := tscc_image_embedding (IsEmbedding.subtypeVal.comp e.symm.isEmbedding) tscc_circle
  rwa [image_univ, range_comp, e.symm.range_coe, image_univ, Subtype.range_coe] at h

/-- The preimage in `M` of a preconnected subset of `M` is preconnected. -/
theorem isPreconnected_preimage_val {M S : Set Pt} (hS : IsPreconnected S) (hSM : S ⊆ M) :
    IsPreconnected (Subtype.val ⁻¹' S : Set M) := by
  rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr hSM]
  exact hS

/-- **A point on an open arc of `M` is a local separating point** (Case 1, step 5). If `p` has a
neighbourhood `W` in `M` lying on a simple closed curve `J ⊆ M`, then `p` separates the open set
`W − q` (`q` another point of `J`): split `J` at `p` and `q` into arcs `L₁`, `L₂`; small sub-arcs
of `L₁`, `L₂` at `p` lie in `W − q`. -/
theorem isLocalSepPoint_of_open_sub_tscc {M J : Set Pt} (hJ : TSCC J) (hJM : J ⊆ M) {p : M}
    {W : Set M} (hW : IsOpen W) (hpW : p ∈ W) (hWJ : ∀ z ∈ W, (z : Pt) ∈ J) :
    IsLocalSepPoint p := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12, rfl⟩ := hJ
  have hpJ : (p : Pt) ∈ C₁ ∪ C₂ := hWJ p hpW
  obtain ⟨q, hqJ, hpq⟩ : ∃ q ∈ C₁ ∪ C₂, (p : Pt) ≠ q := by
    by_cases hps : (p : Pt) = s
    · exact ⟨t, Or.inl h₁.right_mem, hps ▸ h₁.ne⟩
    · exact ⟨s, Or.inl h₁.left_mem, hps⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, hLI, hLU⟩ := tscc_split h₁ h₂ h12 hpJ hqJ hpq
  obtain ⟨O, hO, hWO⟩ := isOpen_induced_iff.mp hW
  set R : Set M := W ∩ Subtype.val ⁻¹' {q}ᶜ with hRdef
  have hRo : IsOpen R := hW.inter (isOpen_compl_singleton.preimage continuous_subtype_val)
  have hpR : p ∈ R := ⟨hpW, hpq⟩
  have hmem : ∀ z ∈ W, (z : Pt) ∈ L₁ ∪ L₂ := fun z hz => hLU ▸ hWJ z hz
  have hN : O ∩ {q}ᶜ ∈ 𝓝 (p : Pt) :=
    (hO.inter isOpen_compl_singleton).mem_nhds ⟨show p ∈ Subtype.val ⁻¹' O from hWO ▸ hpW, hpq⟩
  have side : ∀ {L L' : Set Pt}, TArc (p : Pt) q L → L ∩ L' = {(p : Pt), q} → L ⊆ M →
      ((Subtype.val ⁻¹' L'ᶜ : Set M) ∩ (connectedComponentIn R p \ {p})).Nonempty := by
    intro L L' hL hLL' hLM
    obtain ⟨m', M', hM'sub, hM'⟩ := hL.shrink hN
    have hM'M : M' ⊆ M := fun z hz => hLM (hM'sub hz).1
    have hm'M : m' ∈ M := hM'M hM'.right_mem
    have hm'L : m' ∈ L := (hM'sub hM'.right_mem).1
    have hm'q : m' ≠ q := (hM'sub hM'.right_mem).2.2
    refine ⟨⟨m', hm'M⟩, fun h => ?_, ?_, fun h => hM'.ne ?_⟩
    · have : m' ∈ L ∩ L' := ⟨hm'L, h⟩
      rw [hLL'] at this
      rcases this with h' | h'
      · exact hM'.ne h'.symm
      · exact hm'q h'
    · refine (isPreconnected_preimage_val hM'.isPreconnected hM'M).subset_connectedComponentIn
        (show (p : Pt) ∈ M' from hM'.left_mem) ?_ (show m' ∈ M' from hM'.right_mem)
      intro z hz
      have hz' := hM'sub hz
      exact ⟨hWO ▸ hz'.2.1, hz'.2.2⟩
    · exact (congrArg Subtype.val (mem_singleton_iff.mp h)).symm
  have hL₁M : L₁ ⊆ M := fun z hz => hJM (hLU ▸ Or.inl hz)
  have hL₂M : L₂ ⊆ M := fun z hz => hJM (hLU ▸ Or.inr hz)
  refine ⟨R, hRo, hpR, Subtype.val ⁻¹' L₂ᶜ, Subtype.val ⁻¹' L₁ᶜ,
    hL₂.isClosed.isOpen_compl.preimage continuous_subtype_val,
    hL₁.isClosed.isOpen_compl.preimage continuous_subtype_val, ?_, ?_,
    side hL₁ hLI hL₁M, side hL₂ (by rw [inter_comm, hLI]) hL₂M⟩
  · rintro z ⟨hzR, hzp⟩
    by_contra h
    simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at h
    have : (z : Pt) ∈ L₁ ∩ L₂ := ⟨h.2, h.1⟩
    rw [hLI] at this
    rcases this with h' | h'
    · exact hzp (Subtype.ext h')
    · exact hzR.2 h'
  · refine disjoint_left.mpr fun z hz1 hz2 => ?_
    rcases hmem z hz1.2.1.1 with h | h
    · exact hz2.1 h
    · exact hz1.1 h

/-- **A separation of `M − {a, b}` with `M − b` connected makes `a` a local separating point**
(Case 2, step 7): `a` separates the open set `M − b`, whose component containing `a` is all of
`M − b`. -/
theorem isLocalSepPoint_of_separation {M : Set Pt} {a b : M} (hab : a ≠ b)
    (hcyc : IsConnected ({b}ᶜ : Set M)) {X₁ X₂ : Set Pt}
    (hU : X₁ ∪ X₂ = M \ {(a : Pt), (b : Pt)}) (h1 : X₁.Nonempty) (h2 : X₂.Nonempty)
    (hd1 : Disjoint (closure X₁) X₂) (hd2 : Disjoint X₁ (closure X₂)) : IsLocalSepPoint a := by
  have hcc : connectedComponentIn ({b}ᶜ : Set M) a = {b}ᶜ :=
    subset_antisymm (connectedComponentIn_subset _ _)
      (hcyc.isPreconnected.subset_connectedComponentIn hab subset_rfl)
  have hX : ∀ {x : Pt}, x ∈ X₁ ∪ X₂ → ∃ hx : x ∈ M, (⟨x, hx⟩ : M) ∈ ({b}ᶜ : Set M) \ {a} := by
    intro x hx
    rw [hU] at hx
    refine ⟨hx.1, fun h => hx.2 (Or.inr (congrArg Subtype.val h)), fun h => hx.2 (Or.inl ?_)⟩
    exact congrArg Subtype.val (mem_singleton_iff.mp h)
  refine ⟨{b}ᶜ, isOpen_compl_singleton, hab, Subtype.val ⁻¹' (closure X₂)ᶜ,
    Subtype.val ⁻¹' (closure X₁)ᶜ, isClosed_closure.isOpen_compl.preimage continuous_subtype_val,
    isClosed_closure.isOpen_compl.preimage continuous_subtype_val, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzb, hza⟩
    have hz : (z : Pt) ∈ X₁ ∪ X₂ := by
      rw [hU]
      refine ⟨z.2, ?_⟩
      rintro (h | h)
      · exact hza (Subtype.ext h)
      · exact hzb (Subtype.ext h)
    rcases hz with h | h
    · exact Or.inl fun h' => disjoint_left.mp hd2 h h'
    · exact Or.inr fun h' => disjoint_left.mp hd1 h' h
  · refine disjoint_left.mpr fun z hz1 hz2 => ?_
    have hz : (z : Pt) ∈ X₁ ∪ X₂ := by
      rw [hU]
      refine ⟨z.2, ?_⟩
      rintro (h | h)
      · exact hz1.2.2 (Subtype.ext h)
      · exact hz1.2.1 (Subtype.ext h)
    rcases hz with h | h
    · exact hz2.1 (subset_closure h)
    · exact hz1.1 (subset_closure h)
  · obtain ⟨x, hx⟩ := h1
    obtain ⟨hxM, hx'⟩ := hX (Or.inl hx)
    exact ⟨⟨x, hxM⟩, fun h => disjoint_left.mp hd2 hx h, by rw [hcc]; exact hx'⟩
  · obtain ⟨x, hx⟩ := h2
    obtain ⟨hxM, hx'⟩ := hX (Or.inr hx)
    exact ⟨⟨x, hxM⟩, fun h => disjoint_left.mp hd1 h hx, by rw [hcc]; exact hx'⟩

/-- A nondegenerate continuum is uncountable (instance form for `jones49_some_order_two`). -/
theorem uncountable_of_nontrivial {M : Set Pt} [ConnectedSpace M] [Nontrivial M] : Uncountable M :=
  uncountable_of_connected_metrizable

end HPC.Jones
