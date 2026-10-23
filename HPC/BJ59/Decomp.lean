import HPC.BJ59.CircleFacts
import HPC.HO16.HO16E

/-!
# Batch 198, library: the decomposable case (commission 198, §5)

* `isOpenMap_quotient_mk_of_continuous`: the quotient map of a continuous decomposition is open
  (lower semicontinuity at every element: the saturation of an open set is open);
* `isPseudoArc_Lset'`: the non-degenerate elements of Jones's decomposition of a decomposable
  homogeneous plane continuum are pseudo-arcs (Jones 1955 Theorem 2 with Part F);
* `circle_or_circPAMap_of_decomposable`: a decomposable homogeneous plane continuum is a simple
  closed curve or has an open map onto the circle with pseudo-arc fibres.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones HPC.HO16

/-- **The quotient map of a continuous decomposition is open.** For `U` open, the saturation
`{z | cls z meets U}` is open by lower semicontinuity. -/
theorem isOpenMap_quotient_mk_of_continuous {X : Type*} [MetricSpace X] [CompactSpace X]
    {r : Setoid X} (h : IsContinuousDecomp r) : IsOpenMap (Quotient.mk r) := by
  intro U hU
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨y, hyU, hyz⟩ := hz
  have hy : y ∈ cls r z := mk_eq_mk_iff_mem_cls.1 hyz
  obtain ⟨W, hW, hzW, hWU⟩ := h.2 z y hy U hU hyU
  refine ⟨W, fun z' hz' => ?_, hW, hzW (mem_cls_self z)⟩
  obtain ⟨u, hu, huU⟩ := hWU z' hz'
  exact ⟨u, huU, mk_eq_mk_iff_mem_cls.2 hu⟩

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Jones's elements are pseudo-arcs** (Jones 1955 Theorem 2 with Part F), unconditional. -/
theorem isPseudoArc_Lset' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M)
    (hnt : (Lset x).Nontrivial) : IsPseudoArc (Lset x) := by
  obtain ⟨-, -, hL⟩ := jones55_theorem2' hX hd
  obtain ⟨hconn, hhom, -⟩ := hL x
  set M' : Set Pt := Subtype.val '' Lset x
  let e : Lset x ≃ₜ M' := IsEmbedding.subtypeVal.homeomorphImage _
  have hcpt : IsCompact (Lset x) := (isClosed_Lset x).isCompact
  haveI : CompactSpace (Lset x) := isCompact_iff_compactSpace.1 hcpt
  haveI : ConnectedSpace (Lset x) := isConnected_iff_connectedSpace.1 hconn
  haveI : CompactSpace M' := e.compactSpace
  haveI : ConnectedSpace M' := e.surjective.connectedSpace e.continuous
  have hhom' : IsHomogeneous M' := IsHomogeneous.of_homeomorph e hhom
  have hind' : ¬ IsDecomposableSpace M' := fun h =>
    jones55_elements_indecomposable' hX hd x (IsDecomposableSpace.of_homeomorph e.symm h)
  have hnt' : (univ : Set M').Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnt
    exact ⟨e ⟨a, ha⟩, mem_univ _, e ⟨b, hb⟩, mem_univ _, fun h =>
      hab (congrArg Subtype.val (e.injective h))⟩
  have hPA := isPseudoArc_of_indec_homogeneous ho16_theorem20 M' hhom' hind' hnt'
  exact isPseudoArc_of_homeomorph hPA ((Homeomorph.Set.univ M').trans e.symm)

/-- **The decomposable case**, with circle-likeness as a hypothesis. -/
theorem circle_or_circPAMap_of_decomposable (hX : IsHomogeneous M) (hd : IsDecomposableSpace M)
    (hCL : IsCircleLike (univ : Set M)) :
    Nonempty (M ≃ₜ Circle) ∨ ∃ f : M → Circle, IsCircPAMap f := by
  obtain ⟨hcd, ⟨e⟩, -⟩ := jones55_theorem2' hX hd
  set q : M → Circle := fun x => e (Quotient.mk _ x)
  have hqc : Continuous q := e.continuous.comp continuous_quotient_mk'
  have hqs : Function.Surjective q := e.surjective.comp Quotient.mk_surjective
  have hfib : ∀ x : M, q ⁻¹' {q x} = Lset x := fun x => by
    ext y
    simp only [mem_preimage, mem_singleton_iff, q, e.injective.eq_iff]
    rw [mk_eq_mk_iff_mem_cls, cls_lSetoid hX]
  by_cases hap : IsAposyndetic M
  · left
    have hinj : Function.Injective q := fun x y h => by
      have : y ∈ q ⁻¹' {q x} := h.symm
      rw [hfib, Lset_eq_singleton_of_isAposyndetic hap] at this
      exact this.symm
    exact ⟨hqc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q ⟨hinj, hqs⟩)⟩
  · right
    refine ⟨q, hqc, e.isOpenMap.comp (isOpenMap_quotient_mk_of_continuous hcd), hqs,
      fun z => ?_, hCL⟩
    obtain ⟨x, rfl⟩ := hqs z
    rw [hfib]
    exact isPseudoArc_Lset' hX hd x (jones55_elements hX hap x x).1

end HPC.BJ59
