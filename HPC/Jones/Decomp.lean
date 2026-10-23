import HPC.Jones.Jones48

/-!
# Batch 136, item A: upper semicontinuous decompositions

§§1–2 of the batch-136 skeleton (`doc/batches/skeletons/Jones55-batch136.lean`). The definitions
`AposAtT`, `IsAposyndeticT`, `cls`, `IsUSCDecomp`, `LSCAt`, `IsContinuousDecomp` are the skeleton's,
unchanged.

A decomposition of the compact metric space `X` is a `Setoid X`; its decomposition space is
Mathlib's `Quotient r` with the quotient topology. Results:

* `isClosedMap_mk`, `t2Space_quotient`, `secondCountable_quotient`, `metrizableSpace_quotient`:
  for an u.s.c. decomposition into closed sets the quotient map is closed and the decomposition
  space is a compact metrizable space (Hausdorff and second countable, then Urysohn's metrization
  theorem `TopologicalSpace.metrizableSpace_of_t3_secondCountable`);
* `isContinuum_preimage`: for a monotone u.s.c. decomposition the preimage of a subcontinuum is a
  subcontinuum;
* `exists_homeomorph_quotient`: a homeomorphism permuting the elements descends;
* `residual_lscAt` (Kuratowski; Fort 1951): the classes at which the decomposition is continuous
  form a residual set of the decomposition space, by the route of COMMISSION-batch136.md item A
  (for each basic open `B` the set `π(cl B)` of classes meeting `cl B` is closed; discontinuity at a
  class puts it on the frontier of one of these countably many closed sets; frontiers of closed
  sets are nowhere dense); `exists_lscAt`: Baire's theorem in the decomposition space;
* `lscAt_homeomorph`: continuity at an element is carried by a homeomorphism that permutes the
  elements (used for Jones 1955: continuity at one element plus homogeneity gives continuity).
-/

namespace HPC.Jones

open Set Topology Filter Metric

/-! ## §1. Aposyndesis for a topological space -/

section Top

variable {Y : Type*} [TopologicalSpace Y]

/-- `AposAt`, for a topological space. Same body as `AposAt`, with `Fold.Q78.IsContinuum H`
unfolded to `IsCompact H ∧ IsConnected H`.

*Shape change:* the skeleton writes `Fold.Q78.IsContinuum H`, which is declared under
`[MetricSpace X]` and does not elaborate for a topological space (instance failure); its body is
used instead. -/
def AposAtT (x y : Y) : Prop :=
  ∃ H U : Set Y, (IsCompact H ∧ IsConnected H) ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ H ∧ y ∉ H

/-- Aposyndetic, for a topological space. -/
def IsAposyndeticT (Y : Type*) [TopologicalSpace Y] : Prop := ∀ x y : Y, x ≠ y → AposAtT x y

end Top

/-- For a metric space `AposAtT` is `AposAt` (same body). -/
theorem aposAtT_iff {X : Type*} [MetricSpace X] (x y : X) : AposAtT x y ↔ AposAt x y :=
  Iff.rfl

/-! ## §2. Upper semicontinuous decompositions -/

section Decomp

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The element of the decomposition containing `x`. -/
def cls (r : Setoid X) (x : X) : Set X := {y | r y x}

/-- **Upper semicontinuous decomposition into closed sets** (Moore 1925, p. 416, restated with open
sets). Each element is closed, and if an element lies in an open `U`, then so does every element
meeting some open `V` around it. -/
structure IsUSCDecomp (r : Setoid X) : Prop where
  closed : ∀ x, IsClosed (cls r x)
  usc : ∀ x U, IsOpen U → cls r x ⊆ U →
    ∃ V, IsOpen V ∧ cls r x ⊆ V ∧ ∀ z ∈ V, cls r z ⊆ U

/-- **Lower semicontinuity at an element** ("`G` is continuous at `g`" for an u.s.c. `G`): every
element near `g` comes near every point of `g`. -/
def LSCAt (r : Setoid X) (x : X) : Prop :=
  ∀ y ∈ cls r x, ∀ V, IsOpen V → y ∈ V →
    ∃ W, IsOpen W ∧ cls r x ⊆ W ∧ ∀ z ∈ W, (cls r z ∩ V).Nonempty

/-- A **continuous** decomposition: u.s.c. and l.s.c. at every element. -/
def IsContinuousDecomp (r : Setoid X) : Prop := IsUSCDecomp r ∧ ∀ x, LSCAt r x

variable {r : Setoid X}

omit [MetricSpace X] [CompactSpace X] in
theorem mem_cls_iff {x y : X} : y ∈ cls r x ↔ r y x := Iff.rfl

omit [MetricSpace X] [CompactSpace X] in
theorem mem_cls_self (x : X) : x ∈ cls r x := r.iseqv.refl x

omit [MetricSpace X] [CompactSpace X] in
theorem mk_eq_mk_iff_mem_cls {x y : X} : Quotient.mk r y = Quotient.mk r x ↔ y ∈ cls r x :=
  Quotient.eq

omit [MetricSpace X] [CompactSpace X] in
theorem cls_eq_of_mem {x y : X} (h : y ∈ cls r x) : cls r y = cls r x := by
  ext z
  exact ⟨fun hz => r.iseqv.trans hz h, fun hz => r.iseqv.trans hz (r.iseqv.symm h)⟩

/-- The classes contained in `U`, as a subset of the decomposition space. -/
def satIn (r : Setoid X) (U : Set X) : Set (Quotient r) :=
  {q | ∀ z, Quotient.mk r z = q → z ∈ U}

omit [MetricSpace X] [CompactSpace X] in
theorem mk_mem_satIn {U : Set X} {x : X} : Quotient.mk r x ∈ satIn r U ↔ cls r x ⊆ U :=
  ⟨fun h _ hz => h _ (mk_eq_mk_iff_mem_cls.mpr hz), fun h _ hz => h (mk_eq_mk_iff_mem_cls.mp hz)⟩

omit [MetricSpace X] [CompactSpace X] in
theorem preimage_satIn (U : Set X) : Quotient.mk r ⁻¹' satIn r U = {x | cls r x ⊆ U} := by
  ext x
  exact mk_mem_satIn

omit [CompactSpace X] in
/-- The points whose class lies in an open set form an open set. -/
theorem isOpen_setOf_cls_subset (h : IsUSCDecomp r) {U : Set X} (hU : IsOpen U) :
    IsOpen {x | cls r x ⊆ U} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := h.usc x U hU hx
  exact ⟨V, hVU, hV, hxV (mem_cls_self x)⟩

omit [CompactSpace X] in
theorem isOpen_satIn (h : IsUSCDecomp r) {U : Set X} (hU : IsOpen U) : IsOpen (satIn r U) := by
  rw [← (isQuotientMap_quotient_mk' (s := r)).isOpen_preimage]
  exact (preimage_satIn U).symm ▸ isOpen_setOf_cls_subset h hU

omit [CompactSpace X] in
/-- The quotient map of an u.s.c. decomposition is closed. -/
theorem isClosedMap_mk (h : IsUSCDecomp r) : IsClosedMap (Quotient.mk r) := by
  intro F hF
  rw [← (isQuotientMap_quotient_mk' (s := r)).isClosed_preimage]
  have he : (Quotient.mk' ⁻¹' (Quotient.mk r '' F) : Set X) = {x | cls r x ⊆ Fᶜ}ᶜ := by
    ext x
    simp only [mem_preimage, mem_image, mem_compl_iff, mem_setOf_eq, not_subset, not_not]
    constructor
    · rintro ⟨y, hyF, hy⟩
      exact ⟨y, mk_eq_mk_iff_mem_cls.mp hy, hyF⟩
    · rintro ⟨y, hy, hyF⟩
      exact ⟨y, hyF, mk_eq_mk_iff_mem_cls.mpr hy⟩
  rw [he, isClosed_compl_iff]
  exact isOpen_setOf_cls_subset h hF.isOpen_compl

omit [CompactSpace X] in
theorem t2Space_quotient (h : IsUSCDecomp r) : T2Space (Quotient r) := by
  refine ⟨fun q₁ q₂ hne => ?_⟩
  induction q₁ using Quotient.inductionOn with | h x => ?_
  induction q₂ using Quotient.inductionOn with | h y => ?_
  have hdisj : Disjoint (cls r x) (cls r y) := by
    rw [disjoint_left]
    intro z hzx hzy
    exact hne (Quotient.sound (r.iseqv.trans (r.iseqv.symm hzx) hzy))
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := normal_separation (h.closed x) (h.closed y) hdisj
  refine ⟨satIn r U, satIn r V, isOpen_satIn h hU, isOpen_satIn h hV, mk_mem_satIn.mpr hxU,
    mk_mem_satIn.mpr hyV, ?_⟩
  rw [disjoint_left]
  intro q hqU hqV
  induction q using Quotient.inductionOn with | h z => ?_
  exact disjoint_left.mp hUV (mk_mem_satIn.mp hqU (mem_cls_self z))
    (mk_mem_satIn.mp hqV (mem_cls_self z))

omit [CompactSpace X] in
/-- A compact set inside an open set is inside a finite union of basic open sets contained in the
open set. -/
theorem exists_finite_basis_cover {B : Set (Set X)} (hB : TopologicalSpace.IsTopologicalBasis B)
    {K W : Set X} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ t : Set (Set X), t.Finite ∧ t ⊆ B ∧ K ⊆ ⋃₀ t ∧ ⋃₀ t ⊆ W := by
  classical
  set S : Set (Set X) := {b | b ∈ B ∧ b ⊆ W}
  have hcov : K ⊆ ⋃ b : S, (b : Set X) := by
    intro x hx
    obtain ⟨b, hbB, hxb, hbW⟩ := hB.exists_subset_of_mem_open (hKW hx) hW
    exact mem_iUnion.mpr ⟨⟨b, hbB, hbW⟩, hxb⟩
  obtain ⟨u, hu⟩ := hK.elim_finite_subcover (fun b : S => (b : Set X))
    (fun b => hB.isOpen b.2.1) hcov
  refine ⟨(fun b : S => (b : Set X)) '' (u : Set S), (u.finite_toSet.image _), ?_, ?_, ?_⟩
  · rintro _ ⟨b, -, rfl⟩
    exact b.2.1
  · intro x hx
    obtain ⟨b, hbu, hxb⟩ := mem_iUnion₂.mp (hu hx)
    exact ⟨b, ⟨b, hbu, rfl⟩, hxb⟩
  · rintro x ⟨_, ⟨b, -, rfl⟩, hxb⟩
    exact b.2.2 hxb

theorem secondCountable_quotient (h : IsUSCDecomp r) :
    SecondCountableTopology (Quotient r) := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  set 𝓑 : Set (Set (Quotient r)) :=
    (fun t : Set (Set X) => satIn r (⋃₀ t)) '' {t | t.Finite ∧ t ⊆ B}
  have hcount : 𝓑.Countable := (countable_setOf_finite_subset hBc).image _
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology
    hcount
  · rintro _ ⟨t, ⟨-, htB⟩, rfl⟩
    exact isOpen_satIn h (isOpen_sUnion fun b hb => hB.isOpen (htB hb))
  · intro q O hqO hO
    induction q using Quotient.inductionOn with | h x => ?_
    have hW : IsOpen (Quotient.mk r ⁻¹' O) := hO.preimage continuous_quotient_mk'
    have hsub : cls r x ⊆ Quotient.mk r ⁻¹' O := fun z hz => by
      show Quotient.mk r z ∈ O
      rw [mk_eq_mk_iff_mem_cls.mpr hz]
      exact hqO
    obtain ⟨t, htf, htB, hxt, htW⟩ :=
      exists_finite_basis_cover hB (h.closed x).isCompact hW hsub
    refine ⟨satIn r (⋃₀ t), ⟨t, ⟨htf, htB⟩, rfl⟩, mk_mem_satIn.mpr hxt, ?_⟩
    intro q' hq'
    induction q' using Quotient.inductionOn with | h z => ?_
    exact htW (mk_mem_satIn.mp hq' (mem_cls_self z))

/-- **The decomposition space is compact metrizable.** -/
theorem metrizableSpace_quotient (h : IsUSCDecomp r) :
    TopologicalSpace.MetrizableSpace (Quotient r) := by
  haveI := t2Space_quotient h
  haveI := secondCountable_quotient h
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable _

/-- Monotone decompositions: preimages of subcontinua are subcontinua.

*Shape change:* the hypothesis `Fold.Q78.IsContinuum K` of the skeleton does not elaborate on the
topological space `Quotient r` (it is declared under `[MetricSpace X]`); its body
`IsCompact K ∧ IsConnected K` is used. -/
theorem isContinuum_preimage (h : IsUSCDecomp r) (hconn : ∀ x, IsConnected (cls r x))
    {K : Set (Quotient r)} (hK : IsCompact K ∧ IsConnected K) :
    Fold.Q78.IsContinuum (Quotient.mk r ⁻¹' K) := by
  haveI := t2Space_quotient h
  have hcl : IsClosed (Quotient.mk r ⁻¹' K) := hK.1.isClosed.preimage continuous_quotient_mk'
  refine ⟨hcl.isCompact, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hK.2.nonempty
    induction q using Quotient.inductionOn with | h x => ?_
    exact ⟨x, hq⟩
  · rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv hcov hdisj
    -- the classes in `K` inside `u`, resp. `v`
    set Ku := Quotient.mk r '' (Quotient.mk r ⁻¹' K ∩ u)
    set Kv := Quotient.mk r '' (Quotient.mk r ⁻¹' K ∩ v)
    have hKu : IsClosed Ku := isClosedMap_mk h _ (hcl.inter hu)
    have hKv : IsClosed Kv := isClosedMap_mk h _ (hcl.inter hv)
    -- each class over `K` lies in `u` or in `v`
    have hcls : ∀ x, Quotient.mk r x ∈ K → cls r x ⊆ u ∨ cls r x ⊆ v := by
      intro x hx
      have hsub : cls r x ⊆ Quotient.mk r ⁻¹' K := fun z hz => by
        show Quotient.mk r z ∈ K
        rw [mk_eq_mk_iff_mem_cls.mpr hz]
        exact hx
      have hd : cls r x ∩ (u ∩ v) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro z ⟨hz, hzu, hzv⟩
        exact (eq_empty_iff_forall_notMem.mp hdisj) z ⟨hsub hz, hzu, hzv⟩
      exact (isPreconnected_iff_subset_of_disjoint_closed.mp (hconn x).isPreconnected) u v hu hv
        (hsub.trans hcov) hd
    have hcovK : K ⊆ Ku ∪ Kv := by
      intro q hq
      induction q using Quotient.inductionOn with | h x => ?_
      rcases hcls x hq with hxu | hxv
      · exact Or.inl ⟨x, ⟨hq, hxu (mem_cls_self x)⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hq, hxv (mem_cls_self x)⟩, rfl⟩
    have hdK : K ∩ (Ku ∩ Kv) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro q ⟨hq, ⟨a, ⟨-, hau⟩, rfl⟩, ⟨b, ⟨-, hbv⟩, hb⟩⟩
      have hb' : b ∈ cls r a := mk_eq_mk_iff_mem_cls.mp hb
      have hab : a ∈ cls r b := r.iseqv.symm hb'
      rcases hcls a hq with hxu | hxv
      · exact (eq_empty_iff_forall_notMem.mp hdisj) b
          ⟨(show Quotient.mk r b ∈ K from hb ▸ hq), hxu hb', hbv⟩
      · exact (eq_empty_iff_forall_notMem.mp hdisj) a
          ⟨hq, hau, hxv (mem_cls_self a)⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hK.2.isPreconnected) Ku Kv hKu hKv
      hcovK hdK with hsu | hsv
    · left
      intro x hx
      obtain ⟨y, ⟨-, hyu⟩, hy⟩ := hsu hx
      rcases hcls x hx with hxu | hxv
      · exact hxu (mem_cls_self x)
      · exfalso
        have hyx : y ∈ cls r x := mk_eq_mk_iff_mem_cls.mp hy
        exact (eq_empty_iff_forall_notMem.mp hdisj) y
          ⟨(show Quotient.mk r y ∈ K from hy ▸ hx), hyu, hxv hyx⟩
    · right
      intro x hx
      obtain ⟨y, ⟨-, hyv⟩, hy⟩ := hsv hx
      rcases hcls x hx with hxu | hxv
      · exfalso
        have hyx : y ∈ cls r x := mk_eq_mk_iff_mem_cls.mp hy
        exact (eq_empty_iff_forall_notMem.mp hdisj) y
          ⟨(show Quotient.mk r y ∈ K from hy ▸ hx), hxu hyx, hyv⟩
      · exact hxv (mem_cls_self x)

omit [CompactSpace X] in
/-- **Homeomorphisms that permute the elements descend to the decomposition space.** -/
theorem exists_homeomorph_quotient (T : X ≃ₜ X) (hT : ∀ x y, r x y ↔ r (T x) (T y)) :
    ∃ S : Quotient r ≃ₜ Quotient r, ∀ x, S (Quotient.mk r x) = Quotient.mk r (T x) := by
  have h1 : ∀ a b, r a b → r (T a) (T b) := fun a b hab => (hT a b).1 hab
  have h2 : ∀ a b, r a b → r (T.symm a) (T.symm b) := fun a b hab => by
    rw [hT, T.apply_symm_apply, T.apply_symm_apply]
    exact hab
  let S : Quotient r ≃ₜ Quotient r :=
    { toFun := Quotient.map' T h1
      invFun := Quotient.map' T.symm h2
      left_inv := fun q => by
        induction q using Quotient.inductionOn with | h x => ?_
        show Quotient.mk r (T.symm (T x)) = Quotient.mk r x
        rw [T.symm_apply_apply]
      right_inv := fun q => by
        induction q using Quotient.inductionOn with | h x => ?_
        show Quotient.mk r (T (T.symm x)) = Quotient.mk r x
        rw [T.apply_symm_apply]
      continuous_toFun := T.continuous.quotient_map' h1
      continuous_invFun := T.symm.continuous.quotient_map' h2 }
  exact ⟨S, fun x => rfl⟩

/-- **A closed equivalence relation on a compact metric space is an u.s.c. decomposition into
closed sets.** -/
theorem isUSCDecomp_of_isClosed (hr : IsClosed {p : X × X | r p.1 p.2}) : IsUSCDecomp r := by
  refine ⟨fun x => ?_, fun x U hU hxU => ?_⟩
  · exact hr.preimage (continuous_id.prodMk continuous_const)
  · refine ⟨{z | cls r z ⊆ U}, ?_, fun z hz => by
      show cls r z ⊆ U
      rw [cls_eq_of_mem hz]
      exact hxU, fun z hz => hz⟩
    have he : {z | cls r z ⊆ U}ᶜ = Prod.snd '' ({p : X × X | r p.1 p.2} ∩ Prod.fst ⁻¹' Uᶜ) := by
      ext z
      simp only [mem_compl_iff, mem_setOf_eq, not_subset, mem_image, mem_inter_iff,
        mem_preimage, Prod.exists, exists_eq_right]
      exact ⟨fun ⟨w, hw, hwU⟩ => ⟨w, hw, hwU⟩, fun ⟨w, hw, hwU⟩ => ⟨w, hw, hwU⟩⟩
    rw [← isClosed_compl_iff, he]
    exact isClosed_snd_image (hr.inter (hU.isClosed_compl.preimage continuous_fst))

/-- The frontier of a closed set has dense complement. -/
theorem dense_compl_frontier_of_isClosed {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    (hA : IsClosed A) : Dense (frontier A)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, hA.frontier_eq, eq_empty_iff_forall_notMem]
  intro q hq
  have h1 : interior (A \ interior A) ⊆ interior A :=
    interior_maximal (interior_subset.trans diff_subset) isOpen_interior
  exact (interior_subset hq).2 (h1 hq)

/-- **The theorem Jones 1955 uses without statement:** an u.s.c. decomposition of a compact metric
space into closed sets is continuous at the elements of a residual subset of the decomposition
space. (Kuratowski; Fort's theorem on semicontinuous set-valued maps.) Shape: the set of classes
at which `r` is l.s.c. is residual in `Quotient r`. -/
theorem residual_lscAt (h : IsUSCDecomp r) :
    {q : Quotient r | ∀ x, Quotient.mk r x = q → LSCAt r x} ∈ residual (Quotient r) := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  set A : Set X → Set (Quotient r) := fun b => Quotient.mk r '' closure b
  have hA : ∀ b, IsClosed (A b) := fun b => isClosedMap_mk h _ isClosed_closure
  have hres : (⋂ b ∈ B, (frontier (A b))ᶜ) ∈ residual (Quotient r) :=
    (countable_bInter_mem hBc).mpr fun b _ =>
      residual_of_dense_open isClosed_frontier.isOpen_compl (dense_compl_frontier_of_isClosed (hA b))
  refine mem_of_superset hres fun q hq x hxq => ?_
  subst hxq
  intro y hy V hV hyV
  by_contra hno
  push_neg at hno
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV y hyV
  obtain ⟨b, hbB, hyb, hbs⟩ := hB.exists_subset_of_mem_open (mem_ball_self (half_pos hε))
    isOpen_ball
  have hclV : closure b ⊆ V :=
    (closure_minimal (hbs.trans ball_subset_closedBall) isClosed_closedBall).trans
      ((closedBall_subset_ball (half_lt_self hε)).trans hεV)
  have hqA : Quotient.mk r x ∈ A b := ⟨y, subset_closure hyb, mk_eq_mk_iff_mem_cls.mpr hy⟩
  have hqint : Quotient.mk r x ∈ interior (A b) := by
    have := mem_iInter₂.mp hq b hbB
    rw [(hA b).frontier_eq] at this
    by_contra hni
    exact this ⟨hqA, hni⟩
  have hW : IsOpen (Quotient.mk r ⁻¹' interior (A b)) :=
    isOpen_interior.preimage continuous_quotient_mk'
  have hxW : cls r x ⊆ Quotient.mk r ⁻¹' interior (A b) := fun z hz => by
    show Quotient.mk r z ∈ interior (A b)
    rw [mk_eq_mk_iff_mem_cls.mpr hz]
    exact hqint
  obtain ⟨z, hzW, hz⟩ := hno _ hW hxW
  obtain ⟨w, hwb, hwz⟩ := interior_subset (show Quotient.mk r z ∈ interior (A b) from hzW)
  have hwz' : w ∈ cls r z := mk_eq_mk_iff_mem_cls.mp hwz
  exact (eq_empty_iff_forall_notMem.mp hz) w ⟨hwz', hclV hwb⟩

/-- Consequence used: in a nonempty space, some element is a point of continuity. -/
theorem exists_lscAt [Nonempty X] (h : IsUSCDecomp r) : ∃ x, LSCAt r x := by
  haveI := t2Space_quotient h
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary X)⟩
  obtain ⟨q, hq⟩ := (dense_of_mem_residual (residual_lscAt h)).nonempty
  induction q using Quotient.inductionOn with | h x => ?_
  exact ⟨x, hq x rfl⟩

omit [CompactSpace X] in
/-- **Continuity at an element is a topological property of the decomposition:** a homeomorphism
`T` of `X` permuting the elements carries continuity at `cls x` to continuity at `cls (T x)`. -/
theorem lscAt_homeomorph (T : X ≃ₜ X) (hT : ∀ x y, r x y ↔ r (T x) (T y)) {x : X}
    (hx : LSCAt r x) : LSCAt r (T x) := by
  have himg : ∀ a, cls r (T a) = T '' cls r a := by
    intro a
    ext z
    constructor
    · intro hz
      refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
      show r (T.symm z) a
      rw [hT, T.apply_symm_apply]
      exact hz
    · rintro ⟨w, hw, rfl⟩
      exact (hT w a).1 hw
  intro y hy V hV hyV
  rw [himg] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨W, hW, hxW, hWV⟩ := hx y' hy' (T ⁻¹' V) (hV.preimage T.continuous) hyV
  refine ⟨T.symm ⁻¹' W, hW.preimage T.symm.continuous, ?_, fun z hz => ?_⟩
  · rw [himg]
    rintro _ ⟨w, hw, rfl⟩
    show T.symm (T w) ∈ W
    rw [T.symm_apply_apply]
    exact hxW hw
  · obtain ⟨u, hu, huV⟩ := hWV _ hz
    refine ⟨T u, ?_, huV⟩
    have : cls r (T (T.symm z)) = T '' cls r (T.symm z) := himg _
    rw [T.apply_symm_apply] at this
    rw [this]
    exact ⟨u, hu, rfl⟩

end Decomp

end HPC.Jones
