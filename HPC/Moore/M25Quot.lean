import HPC.Moore.M25Defs
import HPC.Moore.M25Plane

/-!
# Batch 145, items A and B: the space of elements as a quotient

Under `MooreDecomp r` (elements compact, connected, non-separating; Moore's u.s.c.):

* `isClosedMap_mk_plane`: the quotient map is closed. Only compactness of elements and the u.s.c.
  are used: a closed `F` missing the element of `x` misses a thickening of it (compactness), and the
  u.s.c. gives a ball about `x` whose points have their elements inside that thickening.
* `tube U = {q | q̄ ⊆ U}`; for `U` open it is open (`isOpen_tube`), and the tubes of the
  thickenings of `p̄` form a neighbourhood basis of `p` (`mem_nhds_iff_tube`). This identifies
  Moore's limit element (`isLimitElt_iff`) and domain (`m25_domain_iff`).
* `quotient_metrizable_plane`: T1, regular, second countable (tubes of finite unions of basic sets).
* `isPreconnected_ptsOf`: the point set of a preconnected set of elements is preconnected (fibres
  connected, map closed).
* `ptsOf_connectedComponentIn`: for `W` open, the point set of the component of `[x]` in `W` is
  the component of `x` in `W̄`; so components of open sets are open and the quotient is locally
  connected.
* `frontier_eq_image`: for `C` open, `∂C = [∂C̄]`.
* `quot_brouwer`: Brouwer's theorem for sets of elements.
* `m25_theorem1`: Moore's Theorem 1.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

/-! ### Bookkeeping -/

theorem mem_elt_self (x : Pt) : x ∈ elt r x := Setoid.refl x

theorem ptsOf_singleton (x : Pt) : ptsOf r {Quotient.mk r x} = elt r x := by
  ext y
  simp only [ptsOf, mem_preimage, mem_singleton_iff, elt, mem_setOf_eq]
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem mem_ptsOf {H : Set (Quotient r)} {y : Pt} : y ∈ ptsOf r H ↔ Quotient.mk r y ∈ H := Iff.rfl

theorem ptsOf_compl (H : Set (Quotient r)) : ptsOf r Hᶜ = (ptsOf r H)ᶜ := rfl

theorem image_ptsOf (H : Set (Quotient r)) : Quotient.mk r '' ptsOf r H = H :=
  image_preimage_eq H Quotient.mk_surjective

theorem ptsOf_mono {H H' : Set (Quotient r)} (h : H ⊆ H') : ptsOf r H ⊆ ptsOf r H' :=
  preimage_mono h

theorem ptsOf_singleton_nonempty (q : Quotient r) : (ptsOf r {q}).Nonempty := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  exact ⟨x, rfl⟩

theorem isOpen_iff_ptsOf {H : Set (Quotient r)} : IsOpen H ↔ IsOpen (ptsOf r H) :=
  (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage.symm

theorem isClosed_iff_ptsOf {H : Set (Quotient r)} : IsClosed H ↔ IsClosed (ptsOf r H) :=
  (isQuotientMap_quotient_mk' (s := r)).isClosed_preimage.symm

theorem continuous_mk : Continuous (Quotient.mk r) := continuous_quotient_mk'

/-- The *tube* of `U`: the elements contained in `U`. -/
def tube (r : Setoid Pt) (U : Set Pt) : Set (Quotient r) := {q | ptsOf r {q} ⊆ U}

theorem tube_eq_compl_image (U : Set Pt) : tube r U = (Quotient.mk r '' Uᶜ)ᶜ := by
  ext q
  simp only [tube, mem_setOf_eq, mem_compl_iff, mem_image, not_exists, not_and]
  constructor
  · intro h y hy hyq
    exact hy (h (show Quotient.mk r y ∈ ({q} : Set (Quotient r)) from hyq))
  · intro h y hy
    by_contra hyU
    exact h y hyU hy

theorem mem_of_mem_tube {U : Set Pt} {q : Quotient r} {y : Pt} (hq : q ∈ tube r U)
    (hy : Quotient.mk r y = q) : y ∈ U := hq (show Quotient.mk r y ∈ ({q} : Set _) from hy)

theorem ptsOf_tube_subset (U : Set Pt) : ptsOf r (tube r U) ⊆ U := fun _ hy =>
  mem_of_mem_tube hy rfl

/-! ### The quotient map is closed -/

section hG

variable (hG : MooreDecomp r)
include hG

theorem isCompact_ptsOf_singleton (q : Quotient r) : IsCompact (ptsOf r {q}) := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  rw [ptsOf_singleton]; exact hG.compact x

theorem isConnected_ptsOf_singleton (q : Quotient r) : IsConnected (ptsOf r {q}) := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  rw [ptsOf_singleton]; exact hG.connected x

/-- **The u.s.c. in tube form.** If the element of `x` lies in the open set `U`, so do the elements
of all points near `x`. -/
theorem exists_dist_tube {x : Pt} {U : Set Pt} (hU : IsOpen U) (hxU : elt r x ⊆ U) :
    ∃ d > 0, ∀ y, dist y x < d → elt r y ⊆ U := by
  obtain ⟨e, he, heU⟩ := (hG.compact x).exists_thickening_subset_open hU hxU
  obtain ⟨d, hd, hdd⟩ := hG.usc x e he
  refine ⟨d, hd, fun y hy z hz => heU ?_⟩
  rw [mem_thickening_iff_infDist_lt ⟨x, mem_elt_self x⟩]
  refine hdd y ⟨y, mem_elt_self y, ?_⟩ z hz
  exact lt_of_le_of_lt (infDist_le_dist_of_mem (mem_elt_self x)) hy

/-- **Moore's u.s.c. gives the open-set form: the quotient map is closed.** Uses the compactness of
the elements (a closed set missing an element misses a thickening of it). -/
theorem isClosedMap_mk_plane : IsClosedMap (Quotient.mk r) := by
  intro F hF
  rw [isClosed_iff_ptsOf, ← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  have hxF : elt r x ⊆ Fᶜ := fun z hz hzF => hx ⟨z, hzF, Quotient.sound hz⟩
  obtain ⟨d, hd, hdU⟩ := exists_dist_tube hG hF.isOpen_compl hxF
  refine ⟨d, hd, ?_⟩
  rintro y hy ⟨z, hzF, hzy⟩
  exact hdU y hy (Quotient.exact hzy) hzF

theorem isOpen_tube {U : Set Pt} (hU : IsOpen U) : IsOpen (tube r U) := by
  rw [tube_eq_compl_image, isOpen_compl_iff]
  exact isClosedMap_mk_plane hG _ hU.isClosed_compl

omit hG in
theorem mem_tube_thickening (q : Quotient r) {e : ℝ} (he : 0 < e) :
    q ∈ tube r (thickening e (ptsOf r {q})) := self_subset_thickening he _

/-- **The tubes of thickenings of `q̄` form a neighbourhood basis of `q`.** -/
theorem mem_nhds_iff_tube {q : Quotient r} {V : Set (Quotient r)} :
    V ∈ 𝓝 q ↔ ∃ e > 0, tube r (thickening e (ptsOf r {q})) ⊆ V := by
  constructor
  · intro hV
    obtain ⟨W, hWV, hWo, hqW⟩ := mem_nhds_iff.1 hV
    obtain ⟨e, he, heW⟩ := (isCompact_ptsOf_singleton hG q).exists_thickening_subset_open
      (isOpen_iff_ptsOf.1 hWo) (ptsOf_mono (singleton_subset_iff.2 hqW))
    refine ⟨e, he, fun q' hq' => hWV ?_⟩
    obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q'
    have := heW (hq' hy)
    rw [mem_ptsOf, show Quotient.mk r y = q' from hy] at this
    exact this
  · rintro ⟨e, he, heV⟩
    exact Filter.mem_of_superset ((isOpen_tube hG isOpen_thickening).mem_nhds
      (mem_tube_thickening q he)) heV

omit hG in
/-- Moore's upper-distance condition is membership in a tube of a thickening. -/
theorem upper_iff_mem_tube {k p : Quotient r} {e : ℝ} :
    (∀ y, Quotient.mk r y = k → ∀ z ∈ elt r y, ∀ x, Quotient.mk r x = p →
      infDist z (elt r x) < e) ↔ k ∈ tube r (thickening e (ptsOf r {p})) := by
  obtain ⟨x0, rfl⟩ := Quotient.mk_surjective p
  obtain ⟨y0, rfl⟩ := Quotient.mk_surjective k
  constructor
  · intro h z hz
    have hz' : z ∈ elt r y0 := by rw [← ptsOf_singleton]; exact hz
    rw [ptsOf_singleton, mem_thickening_iff_infDist_lt ⟨x0, mem_elt_self x0⟩]
    exact h y0 rfl z hz' x0 rfl
  · intro h y hy z hz x hx
    have hz' : z ∈ ptsOf r {Quotient.mk r y0} := by rw [← hy, ptsOf_singleton]; exact hz
    have := h hz'
    rw [← hx, ptsOf_singleton, mem_thickening_iff_infDist_lt ⟨x, mem_elt_self x⟩] at this
    exact this

/-- **Moore's limit element is accumulation in the quotient topology.** -/
theorem isLimitElt_iff {p : Quotient r} {K : Set (Quotient r)} :
    IsLimitElt p K ↔ AccPt p (Filter.principal K) := by
  rw [accPt_iff_nhds]
  constructor
  · intro h V hV
    obtain ⟨e, he, heV⟩ := (mem_nhds_iff_tube hG).1 hV
    obtain ⟨k, hkK, hkp, hk⟩ := h e he
    exact ⟨k, ⟨heV (upper_iff_mem_tube.1 hk), hkK⟩, hkp⟩
  · intro h e he
    obtain ⟨k, ⟨hkV, hkK⟩, hkp⟩ := h _ ((mem_nhds_iff_tube hG).2 ⟨e, he, subset_rfl⟩)
    exact ⟨k, hkK, hkp, upper_iff_mem_tube.2 hkV⟩

/-- **Moore's domains are the connected open sets** (p. 417). -/
theorem m25_domain_iff {D : Set (Quotient r)} :
    (IsConnected D ∧ ∀ x, Quotient.mk r x ∈ D → ∃ d > 0, ∀ y,
        (∀ z ∈ elt r y, infDist z (elt r x) < d) → Quotient.mk r y ∈ D) ↔
      IsConnected D ∧ IsOpen D := by
  refine and_congr_right fun _ => ?_
  have key : ∀ (x y : Pt) (d : ℝ), (∀ z ∈ elt r y, infDist z (elt r x) < d) ↔
      Quotient.mk r y ∈ tube r (thickening d (ptsOf r {Quotient.mk r x})) := by
    intro x y d
    rw [← upper_iff_mem_tube]
    constructor
    · intro h y' hy' z hz x' hx'
      rw [elt_eq hx'.symm] at *
      rw [elt_eq hy'] at hz
      exact h z hz
    · intro h z hz
      exact h y rfl z hz x rfl
  constructor
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨d, hd, hdD⟩ := h x hq
    refine (mem_nhds_iff_tube hG).2 ⟨d, hd, fun q' hq' => ?_⟩
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q'
    exact hdD y ((key x y d).2 hq')
  · intro h x hx
    obtain ⟨d, hd, hdD⟩ := (mem_nhds_iff_tube hG).1 (h.mem_nhds hx)
    exact ⟨d, hd, fun y hy => hdD ((key x y d).1 hy)⟩
where
  elt_eq {a b : Pt} (h : Quotient.mk r a = Quotient.mk r b) : elt r a = elt r b := by
    rw [← ptsOf_singleton, h, ptsOf_singleton]

/-! ### Metrizability -/

theorem t1Space_quot : T1Space (Quotient r) := by
  refine ⟨fun q => ?_⟩
  rw [isClosed_iff_ptsOf]
  exact (isCompact_ptsOf_singleton hG q).isClosed

theorem regularSpace_quot : RegularSpace (Quotient r) := by
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun q V hV => ?_
  obtain ⟨W, hWV, hWo, hqW⟩ := mem_nhds_iff.1 hV
  obtain ⟨e, he, heW⟩ := (isCompact_ptsOf_singleton hG q).exists_thickening_subset_open
    (isOpen_iff_ptsOf.1 hWo) (ptsOf_mono (singleton_subset_iff.2 hqW))
  refine ⟨Quotient.mk r '' cthickening (e / 2) (ptsOf r {q}), ?_,
    isClosedMap_mk_plane hG _ isClosed_cthickening, ?_⟩
  · refine Filter.mem_of_superset ((isOpen_tube hG isOpen_thickening).mem_nhds
      (mem_tube_thickening q (half_pos he))) fun q' hq' => ?_
    obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q'
    exact ⟨y, thickening_subset_cthickening _ _ (hq' hy), hy⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hWV (heW (cthickening_subset_thickening' he (half_lt_self he) _ hy))

theorem secondCountable_quot : SecondCountableTopology (Quotient r) := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Pt
  set B : Set (Set (Quotient r)) := (fun s : Set (Set Pt) => tube r (⋃₀ s)) ''
    {s | s.Finite ∧ s ⊆ b} with hB
  have hBc : B.Countable := (countable_setOf_finite_subset hbc).image _
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hBc
  · rintro _ ⟨s, ⟨-, hsb⟩, rfl⟩
    exact isOpen_tube hG (isOpen_sUnion fun u hu => hb.isOpen (hsb hu))
  · intro q V hqV hV
    have hcov : ptsOf r {q} ⊆ ⋃ u : {u ∈ b | u ⊆ ptsOf r V}, (u : Set Pt) := by
      intro z hz
      have hzV : z ∈ ptsOf r V := ptsOf_mono (singleton_subset_iff.2 hqV) hz
      obtain ⟨u, hub, hzu, huV⟩ := hb.exists_subset_of_mem_open hzV (isOpen_iff_ptsOf.1 hV)
      exact mem_iUnion.2 ⟨⟨u, hub, huV⟩, hzu⟩
    obtain ⟨t, ht⟩ := (isCompact_ptsOf_singleton hG q).elim_finite_subcover _
      (fun u => hb.isOpen u.2.1) hcov
    refine ⟨tube r (⋃₀ ((fun u : {u ∈ b | u ⊆ ptsOf r V} => (u : Set Pt)) '' (t : Set _))),
      ⟨_, ⟨(t.finite_toSet.image _), ?_⟩, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨u, -, rfl⟩; exact u.2.1
    · intro z hz
      obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.1 (ht hz)
      exact mem_sUnion.2 ⟨u, ⟨u, hu, rfl⟩, hzu⟩
    · intro q' hq'
      obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q'
      obtain ⟨_, ⟨u, -, rfl⟩, hyu⟩ := mem_sUnion.1 (hq' hy)
      have := u.2.2 hyu
      rw [mem_ptsOf, show Quotient.mk r y = q' from hy] at this
      exact this

/-- **The quotient is metrizable**: T1, regular, second countable (Urysohn). -/
theorem quotient_metrizable_plane : TopologicalSpace.MetrizableSpace (Quotient r) := by
  haveI := t1Space_quot hG
  haveI := regularSpace_quot hG
  haveI := secondCountable_quot hG
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable _

/-- The quotient map is proper (closed, compact fibres). -/
theorem isProperMap_mk : IsProperMap (Quotient.mk r) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨continuous_mk, isClosedMap_mk_plane hG, isCompact_ptsOf_singleton hG⟩

/-! ### Connectedness and components -/

/-- **The point set of a preconnected set of elements is preconnected** (the fibres are connected
and the map is closed). -/
theorem isPreconnected_ptsOf {C : Set (Quotient r)} (hC : IsPreconnected C) :
    IsPreconnected (ptsOf r C) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hAuv hAuv'
  have hfib : ∀ q ∈ C, ptsOf r {q} ⊆ u ∨ ptsOf r {q} ⊆ v := fun q hq =>
    isPreconnected_iff_subset_of_disjoint.1 (isConnected_ptsOf_singleton hG q).isPreconnected u v
      hu hv ((ptsOf_mono (singleton_subset_iff.2 hq)).trans hAuv)
      (eq_empty_of_subset_empty fun z hz => hAuv' ▸
        ⟨ptsOf_mono (singleton_subset_iff.2 hq) hz.1, hz.2⟩)
  have hC' : C ⊆ tube r u ∪ tube r v := fun q hq => hfib q hq
  have hdisj : C ∩ (tube r u ∩ tube r v) = ∅ := by
    refine eq_empty_of_forall_notMem fun q ⟨hq, hqu, hqv⟩ => ?_
    obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q
    have hyC : y ∈ ptsOf r C := ptsOf_mono (singleton_subset_iff.2 hq) hy
    exact (eq_empty_iff_forall_notMem.1 hAuv') y ⟨hyC, hqu hy, hqv hy⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hC _ _ (isOpen_tube hG hu) (isOpen_tube hG hv)
    hC' hdisj with h | h
  · exact Or.inl fun y hy => mem_of_mem_tube (h hy) rfl
  · exact Or.inr fun y hy => mem_of_mem_tube (h hy) rfl

theorem isConnected_ptsOf {C : Set (Quotient r)} (hC : IsConnected C) :
    IsConnected (ptsOf r C) := by
  refine ⟨?_, isPreconnected_ptsOf hG hC.isPreconnected⟩
  obtain ⟨q, hq⟩ := hC.nonempty
  obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q
  exact ⟨y, ptsOf_mono (singleton_subset_iff.2 hq) hy⟩

/-- **Components correspond.** For any set `W` of elements, the point set of the component of `[x]` in `W` is the
component of `x` in `W̄`. -/
theorem ptsOf_connectedComponentIn {W : Set (Quotient r)} (x : Pt) :
    ptsOf r (connectedComponentIn W (Quotient.mk r x)) = connectedComponentIn (ptsOf r W) x := by
  by_cases hx : Quotient.mk r x ∈ W
  · apply Subset.antisymm
    · exact (isPreconnected_ptsOf hG isPreconnected_connectedComponentIn).subset_connectedComponentIn
        (mem_connectedComponentIn hx) (ptsOf_mono (connectedComponentIn_subset _ _))
    · intro y hy
      have himg : Quotient.mk r '' connectedComponentIn (ptsOf r W) x ⊆
          connectedComponentIn W (Quotient.mk r x) :=
        (isPreconnected_connectedComponentIn.image _ continuous_mk.continuousOn).subset_connectedComponentIn
          ⟨x, mem_connectedComponentIn (show x ∈ ptsOf r W from hx), rfl⟩
          (by rintro _ ⟨z, hz, rfl⟩; exact connectedComponentIn_subset (ptsOf r W) x hz)
      exact himg ⟨y, hy, rfl⟩
  · rw [connectedComponentIn_eq_empty hx,
      connectedComponentIn_eq_empty (show x ∉ ptsOf r W from hx)]
    rfl

theorem isOpen_connectedComponentIn_quot {W : Set (Quotient r)} (hW : IsOpen W) (q : Quotient r) :
    IsOpen (connectedComponentIn W q) := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  rw [isOpen_iff_ptsOf, ptsOf_connectedComponentIn hG]
  exact (isOpen_iff_ptsOf.1 hW).connectedComponentIn

/-- **The space of elements is locally connected.** -/
theorem locallyConnectedSpace_quot : LocallyConnectedSpace (Quotient r) :=
  locallyConnectedSpace_iff_connectedComponentIn_open.2 fun _ hF q _ =>
    isOpen_connectedComponentIn_quot hG hF q

/-- For `C` open, the frontier of `C` consists of the elements meeting the frontier of `C̄`. -/
theorem frontier_eq_image {C : Set (Quotient r)} (hC : IsOpen C) :
    frontier C = Quotient.mk r '' frontier (ptsOf r C) := by
  have hcl : closure C = Quotient.mk r '' closure (ptsOf r C) := by
    apply Subset.antisymm
    · refine closure_minimal ?_ (isClosedMap_mk_plane hG _ isClosed_closure)
      intro q hq
      obtain ⟨y, hy⟩ := ptsOf_singleton_nonempty q
      exact ⟨y, subset_closure (ptsOf_mono (singleton_subset_iff.2 hq) hy), hy⟩
    · calc Quotient.mk r '' closure (ptsOf r C) ⊆ closure (Quotient.mk r '' ptsOf r C) :=
            image_closure_subset_closure_image continuous_mk
        _ = closure C := by rw [image_ptsOf]
  rw [hC.frontier_eq, (isOpen_iff_ptsOf.1 hC).frontier_eq, hcl]
  ext q
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hq⟩
    exact ⟨y, ⟨hy, hq⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyC⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hyC⟩

/-- **Brouwer's theorem for sets of elements.** The frontier of a component of the complement of
a closed connected set of elements is connected (Brouwer in the plane, through
`ptsOf_connectedComponentIn` and `frontier_eq_image`). -/
theorem quot_brouwer {F : Set (Quotient r)} (hF : IsClosed F) (hFc : IsConnected F)
    {q : Quotient r} (hq : q ∉ F) : IsConnected (frontier (connectedComponentIn Fᶜ q)) := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  rw [frontier_eq_image hG (isOpen_connectedComponentIn_quot hG hF.isOpen_compl _),
    ptsOf_connectedComponentIn hG, ptsOf_compl]
  exact (brouwer_boundary (isClosed_iff_ptsOf.1 hF) (isConnected_ptsOf hG hFc)
    ⟨x, hq, rfl⟩).image _ continuous_mk.continuousOn

/-- **Theorem 1** (p. 418). If `K` is a set of points and `H` the set of elements meeting `K`, then
`H` is closed if `K` is closed (the quotient map is closed) and connected if `K` is connected (it
is continuous). -/
theorem m25_theorem1 {K : Set Pt} :
    (IsClosed K → IsClosed (Quotient.mk r '' K)) ∧
      (IsConnected K → IsConnected (Quotient.mk r '' K)) :=
  ⟨fun h => isClosedMap_mk_plane hG K h, fun h => h.image _ continuous_mk.continuousOn⟩

end hG

/-- **The converse of `isClosedMap_mk_plane`** (check 10 of the commission): if the elements are
compact and the quotient map is closed, Moore's distance form of upper semicontinuity holds. With
`isClosedMap_mk_plane` (which uses only the compactness of the elements and Moore's u.s.c.), the two
forms are equivalent for decompositions into compact sets. -/
theorem usc_of_isClosedMap (hc : ∀ x, IsCompact (elt r x)) (hcl : IsClosedMap (Quotient.mk r)) :
    ∀ x, ∀ e > 0, ∃ d > 0, ∀ y, (∃ p ∈ elt r y, infDist p (elt r x) < d) →
      ∀ p ∈ elt r y, infDist p (elt r x) < e := by
  intro x e he
  have hne : (elt r x).Nonempty := ⟨x, mem_elt_self x⟩
  set V : Set (Quotient r) := (Quotient.mk r '' (thickening e (elt r x))ᶜ)ᶜ
  have hVo : IsOpen V := (hcl _ isOpen_thickening.isClosed_compl).isOpen_compl
  have hW : elt r x ⊆ Quotient.mk r ⁻¹' V := by
    rintro z hz ⟨w, hw, hwz⟩
    apply hw
    have hwx : w ∈ elt r x := Setoid.trans (Quotient.exact hwz) hz
    exact self_subset_thickening he _ hwx
  obtain ⟨d, hd, hdW⟩ := (hc x).exists_thickening_subset_open (hVo.preimage continuous_mk) hW
  refine ⟨d, hd, fun y ⟨p, hp, hpd⟩ q hq => ?_⟩
  have hpV : Quotient.mk r p ∈ V := hdW ((mem_thickening_iff_infDist_lt hne).2 hpd)
  by_contra hqe
  apply hpV
  refine ⟨q, fun hq' => hqe ((mem_thickening_iff_infDist_lt hne).1 hq'), ?_⟩
  exact Quotient.sound (Setoid.trans hq (Setoid.symm hp))

end HPC.Moore
