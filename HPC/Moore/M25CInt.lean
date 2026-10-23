import HPC.Moore.M25CDefs
import HPC.Moore.TSCCCut

/-!
# Batch 147, item A: interiors, arcs and simple closed curves of elements

* `sccInterior_spec`: Theorem 11 restated through `sccInterior`, `sccExterior` (the two domains of
  Theorem 11 are the components with bounded, resp. unbounded, point set).
* `isArcElt_iff_tarc`, `isSCCElt_iff_tscc`: Moore's arcs and simple closed curves of elements are the
  topological arcs `Gen.TArc` and closed curves `Gen.TSCC` of the quotient. One way by the
  cut-point characterizations (`IsCutArc.exists_embedding`, Theorem 10), the other by
  `isCutArc_range` and the cut lemma `Gen.tscc_cut`.
* `isSCCElt_union`: two arcs of elements with only their ends in common form a simple closed curve.
* `mooreRegion_of_restricted`: a restricted region is a Moore region (Theorem 11).
* The hypotheses of the topological F.A. Theorems 24–27 (`Gen.th24_*` … `Gen.th27`) for the
  restricted regions: `arcConn_quot` (F.A. Theorem 15), `th21Prop_restricted` (F.A. Theorem 21, from
  Theorem 11 alone), `ax8Prop_restricted` (Axiom 8), and the exteriors, closures and
  noncompactness.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen

variable {r : Setoid Pt}

section M25CInt

variable (hG : MooreDecomp r)
include hG

omit hG in
/-- The two domains of Theorem 11 are `sccInterior J` and `sccExterior J`. -/
theorem sccInterior_eq_of_split {J I E : Set (Quotient r)} (hIo : IsOpen I) (hIc : IsConnected I)
    (hEo : IsOpen E) (hEc : IsConnected E) (hdis : Disjoint I E) (hu : I ∪ E = Jᶜ)
    (hIb : Bornology.IsBounded (ptsOf r I)) (hEb : ¬ Bornology.IsBounded (ptsOf r E)) :
    sccInterior J = I ∧ sccExterior J = E := by
  have hcI : ∀ x ∈ I, connectedComponentIn Jᶜ x = I := fun x hx =>
    connectedComponentIn_eq_of_split hIo hEo hdis hu.symm hIc.2 hx
  have hcE : ∀ x ∈ E, connectedComponentIn Jᶜ x = E := fun x hx =>
    connectedComponentIn_eq_of_split hEo hIo hdis.symm (by rw [← hu, union_comm]) hEc.2 hx
  have hIJ : ∀ x ∈ I, x ∉ J := fun x hx => (hu ▸ Or.inl hx : x ∈ Jᶜ)
  have hEJ : ∀ x ∈ E, x ∉ J := fun x hx => (hu ▸ Or.inr hx : x ∈ Jᶜ)
  constructor
  · ext x
    refine ⟨fun ⟨hxJ, hb⟩ => ?_, fun hx => ⟨hIJ x hx, by rw [hcI x hx]; exact hIb⟩⟩
    rcases (hu.symm ▸ hxJ : x ∈ I ∪ E) with h | h
    · exact h
    · rw [hcE x h] at hb; exact absurd hb hEb
  · ext x
    refine ⟨fun ⟨hxJ, hb⟩ => ?_, fun hx => ⟨hEJ x hx, by rw [hcE x hx]; exact hEb⟩⟩
    rcases (hu.symm ▸ hxJ : x ∈ I ∪ E) with h | h
    · rw [hcI x h] at hb; exact absurd hIb hb
    · exact h

/-- Theorem 11 in terms of `sccInterior`, `sccExterior`: for a simple closed curve of elements these
are Moore's interior and exterior (open, connected, bounded resp. unbounded, each with boundary `J`),
and `Jᶜ` is their disjoint union. -/
theorem sccInterior_spec {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    IsOpen (sccInterior J) ∧ IsConnected (sccInterior J) ∧
      Bornology.IsBounded (ptsOf r (sccInterior J)) ∧ frontier (sccInterior J) = J ∧
      IsOpen (sccExterior J) ∧ IsConnected (sccExterior J) ∧
      ¬ Bornology.IsBounded (ptsOf r (sccExterior J)) ∧ frontier (sccExterior J) = J ∧
      Disjoint (sccInterior J) (sccExterior J) ∧ sccInterior J ∪ sccExterior J = Jᶜ := by
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hdis, hu, hIb, hEb, hfI, hfE⟩ := m25_theorem11 hG hJ
  obtain ⟨h1, h2⟩ := sccInterior_eq_of_split hIo hIc hEo hEc hdis hu hIb hEb
  rw [h1, h2]
  exact ⟨hIo, hIc, hIb, hfI, hEo, hEc, hEb, hfE, hdis, hu⟩

theorem closure_sccInterior {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    closure (sccInterior J) = sccInterior J ∪ J := by
  obtain ⟨hIo, -, -, hfI, -⟩ := sccInterior_spec hG hJ
  rw [closure_eq_self_union_frontier, hfI]

theorem closure_sccExterior {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    closure (sccExterior J) = sccExterior J ∪ J := by
  obtain ⟨-, -, -, -, -, -, -, hfE, -⟩ := sccInterior_spec hG hJ
  rw [closure_eq_self_union_frontier, hfE]

/-- The exterior is the complement of the closure of the interior. -/
theorem compl_closure_sccInterior {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    (closure (sccInterior J))ᶜ = sccExterior J := by
  obtain ⟨-, -, -, -, -, -, -, -, hdis, hu⟩ := sccInterior_spec hG hJ
  rw [closure_sccInterior hG hJ]
  ext x
  constructor
  · intro hx
    have hxJ : x ∈ Jᶜ := fun h => hx (Or.inr h)
    rw [← hu] at hxJ
    exact hxJ.resolve_left fun h => hx (Or.inl h)
  · rintro hx (h | h)
    · exact disjoint_left.1 hdis h hx
    · exact (hu ▸ Or.inr hx : x ∈ Jᶜ) h

/-- The interior is the complement of the closure of the exterior. -/
theorem compl_closure_sccExterior {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    (closure (sccExterior J))ᶜ = sccInterior J := by
  obtain ⟨-, -, -, -, -, -, -, -, hdis, hu⟩ := sccInterior_spec hG hJ
  rw [closure_sccExterior hG hJ]
  ext x
  constructor
  · intro hx
    have hxJ : x ∈ Jᶜ := fun h => hx (Or.inr h)
    rw [← hu] at hxJ
    exact hxJ.resolve_right fun h => hx (Or.inl h)
  · rintro hx (h | h)
    · exact disjoint_left.1 hdis hx h
    · exact (hu ▸ Or.inl hx : x ∈ Jᶜ) h

theorem t2Space_quot : T2Space (Quotient r) := by
  haveI := quotient_metrizable_plane hG
  infer_instance

/-- **Moore's arcs of elements are the topological arcs of the quotient.** -/
theorem isArcElt_iff_tarc {A B : Quotient r} {H : Set (Quotient r)} :
    IsArcElt A B H ↔ TArc A B H := by
  haveI := quotient_metrizable_plane hG
  constructor
  · intro h
    exact ⟨h.1, h.isCutArc.exists_embedding⟩
  · rintro ⟨-, f, hf, rfl, rfl, rfl⟩
    exact (isCutArc_range hf).isArcElt (isCompact_range hf.continuous).isClosed
      (isBounded_ptsOf_of_isCompact hG (isCompact_range hf.continuous))

/-- Two arcs from `p` to `q` with only `p`, `q` in common form a simple closed curve (used in the
statements of Theorems 15–18: "the simple closed curve formed by these two arcs"). -/
theorem isSCCElt_union {p q : Quotient r} {X Y : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hXY : X ∩ Y = {p, q}) : IsSCCElt (X ∪ Y) := by
  haveI := t2Space_quot hG
  have hX' := (isArcElt_iff_tarc hG).1 hX
  have hY' := (isArcElt_iff_tarc hG).1 hY
  refine ⟨hX.2.1.union hY.2.1, hX.2.2.1.union ⟨p, hX.2.2.2.2.1, hY.2.2.2.2.1⟩ hY.2.2.1,
    ⟨p, Or.inl hX.2.2.2.2.1, q, Or.inl hX.2.2.2.2.2.1, hX.1⟩, ?_, ?_⟩
  · exact hX.2.2.2.1.union hY.2.2.2.1
  · intro x hx y hy hxy
    exact tscc_cut hX' hY' hXY hx hy hxy

/-- **Moore's simple closed curves of elements are the topological closed curves.** -/
theorem isSCCElt_iff_tscc {J : Set (Quotient r)} : IsSCCElt J ↔ TSCC J := by
  constructor
  · intro hJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hJ.2.2.1
    obtain ⟨a, b, ha, hb, hab, hab'⟩ := m25_theorem10 hG hJ hp hq hpq
    exact ⟨p, q, a, b, (isArcElt_iff_tarc hG).1 ha, (isArcElt_iff_tarc hG).1 hb, hab', hab.symm⟩
  · rintro ⟨A, B, C₁, C₂, h₁, h₂, h12, rfl⟩
    exact isSCCElt_union hG ((isArcElt_iff_tarc hG).2 h₁) ((isArcElt_iff_tarc hG).2 h₂) h12

/-- A region in the restricted sense is a region in the original sense (p. 424, proof of Theorem 20:
"Since `R` is also a region in the original sense"). -/
theorem mooreRegion_of_restricted {R : Set (Quotient r)} (hR : restrictedRegion R) :
    mooreRegion R := by
  obtain ⟨J, hJ, rfl⟩ := hR
  obtain ⟨hIo, hIc, hIb, hfI, -⟩ := sccInterior_spec hG hJ
  exact ⟨hIo, hIc, hIb, by rw [hfI]; exact hJ.2.1⟩

/-- **F.A. Theorem 15 for the quotient, topologically**: two distinct elements of a connected open
set of elements are joined by an arc in it. -/
theorem arcConn_quot : ArcConn (Quotient r) := by
  intro U hUo hUc a ha b hb hab
  have h1 := m25_axiom1 hG
  have h4 := m25_axiom4 hG
  have hdom : (spaceOfElts r).IsDomain U := by
    rw [isDomain_iff h1, spaceOfElts_topology hG]; exact ⟨hUo, hUc⟩
  obtain ⟨C, hCU, hC⟩ := m25_fa_theorem15 hG hdom ha hb hab
  rw [isArc_iff_topological h1 h4, spaceOfElts_topology hG] at hC
  haveI := quotient_metrizable_plane hG
  exact ⟨C, hCU, hab, (isIrreducibleConnected_iff_arc hab).1 hC.2⟩

/-- The family of restricted regions. -/
abbrev restrictedRegions (r : Setoid Pt) : Set (Set (Quotient r)) := {R | restrictedRegion R}

/-- An open set inside the closure of an interior lies in the interior. -/
theorem subset_sccInterior_of_isOpen {J U : Set (Quotient r)} (hJ : IsSCCElt J) (hUo : IsOpen U)
    (hU : U ⊆ closure (sccInterior J)) : U ⊆ sccInterior J := by
  obtain ⟨-, -, -, -, hEo, -, -, hfE, -⟩ := sccInterior_spec hG hJ
  intro x hx
  rcases (closure_sccInterior hG hJ ▸ hU hx : x ∈ sccInterior J ∪ J) with h | h
  · exact h
  · exfalso
    have hxE : x ∈ closure (sccExterior J) := frontier_subset_closure (by rw [hfE]; exact h)
    obtain ⟨y, hyU, hyE⟩ := mem_closure_iff.1 hxE U hUo hx
    have := hU hyU
    rw [← compl_compl (closure (sccInterior J)), compl_closure_sccInterior hG hJ] at this
    exact this hyE

/-- **F.A. Theorem 21 for the restricted regions** (from Theorem 11 alone): if the boundary of `R`
lies in the closure of `K`, then `R ⊆ K`. -/
theorem th21Prop_restricted : Th21Prop (restrictedRegions r) := by
  rintro K ⟨JK, hJK, rfl⟩ R ⟨JR, hJR, rfl⟩ hfr
  obtain ⟨hRo, hRc, hRb, hfR, -⟩ := sccInterior_spec hG hJR
  obtain ⟨-, -, -, -, hEo, hEc, hEb, -⟩ := sccInterior_spec hG hJK
  have hdis : Disjoint (sccInterior JR) (sccExterior JK) := by
    rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    intro hne
    have hfd : Disjoint (sccExterior JK) (frontier (sccInterior JR)) := by
      rw [← compl_closure_sccInterior hG hJK]
      exact disjoint_compl_left.mono_right hfr
    have hsub := conn_sub_of_frontier hEc.isPreconnected hfd (by rwa [inter_comm])
    exact hEb (hRb.subset (ptsOf_mono hsub))
  refine subset_sccInterior_of_isOpen hG hJK hRo fun x hx => ?_
  by_contra hxc
  rw [← mem_compl_iff, compl_closure_sccInterior hG hJK] at hxc
  exact disjoint_left.1 hdis hx hxc

/-- **Axiom 8 for the restricted regions**, topologically. -/
theorem ax8Prop_restricted : Ax8Prop (restrictedRegions r) := by
  intro J hJ
  have hJ' := (isSCCElt_iff_tscc hG).2 hJ
  exact ⟨sccInterior J, ⟨J, hJ', rfl⟩, (sccInterior_spec hG hJ').2.2.2.1⟩

theorem isOpen_restricted : ∀ R ∈ restrictedRegions r, IsOpen R := by
  rintro R ⟨J, hJ, rfl⟩; exact (sccInterior_spec hG hJ).1

theorem isPreconnected_restricted : ∀ R ∈ restrictedRegions r, IsPreconnected R := by
  rintro R ⟨J, hJ, rfl⟩; exact (sccInterior_spec hG hJ).2.1.isPreconnected

theorem ext_restricted : ∀ R ∈ restrictedRegions r, IsPreconnected (closure R)ᶜ := by
  rintro R ⟨J, hJ, rfl⟩
  rw [compl_closure_sccInterior hG hJ]; exact (sccInterior_spec hG hJ).2.2.2.2.2.1.isPreconnected

theorem isCompact_closure_restricted : ∀ R ∈ restrictedRegions r, IsCompact (closure R) := by
  rintro R ⟨J, hJ, rfl⟩
  exact isCompact_of_isClosed_bounded isClosed_closure
    (isBounded_ptsOf_closure hG (sccInterior_spec hG hJ).2.2.1)

theorem not_isCompact_univ_quot : ¬ IsCompact (univ : Set (Quotient r)) := by
  intro h
  have hb := isBounded_ptsOf_of_isCompact hG h
  exact not_isBounded_of_forall_nat (T := ptsOf r univ) (fun _ => mem_univ _) hb

/-- `TInt` for the restricted regions: the interior of a simple closed curve of elements. -/
theorem tInt_sccInterior {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    TInt (restrictedRegions r) J (sccInterior J) :=
  ⟨(isSCCElt_iff_tscc hG).1 hJ, ⟨J, hJ, rfl⟩, (sccInterior_spec hG hJ).2.2.2.1⟩

end M25CInt

end HPC.Moore
