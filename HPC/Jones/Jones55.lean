import HPC.Jones.Decomp
import HPC.Jones.Whyburn
import HPC.Jones.Jones55Core
import HPC.Jones.Jones51Thm1

/-!
# Batch 136: decomposition spaces; Whyburn 1939 (6.2), (6.21); Jones 1951 Theorem 1;
# Jones 1955 Theorem 1

Umbrella module for batch 136 (skeleton: `doc/batches/skeletons/Jones55-batch136.lean`).

* §1–§2 (item A): `HPC/Jones/Decomp.lean` — `AposAtT`, `IsAposyndeticT`, `aposAtT_iff`; `cls`,
  `IsUSCDecomp`, `LSCAt`, `IsContinuousDecomp`; `isClosedMap_mk`, `t2Space_quotient`,
  `secondCountable_quotient`, `metrizableSpace_quotient`, `isContinuum_preimage`,
  `exists_homeomorph_quotient`, `residual_lscAt`, `exists_lscAt`.
* §3 (item B): `HPC/Jones/Whyburn.lean` — `semiLocConn_of_isAposyndetic`, `whyburn_6_1`,
  `whyburn_6_2`, `whyburn_6_21`.
* §4 (item C): `HPC/Jones/Jones51Thm1.lean` — `jones51_theorem1`.
* §5 (item D): `HPC/Jones/Jones55Core.lean` (definitions `Lset`, `CutsFrom`, `lRel`, `lSetoid`,
  `Lset_compl`; the spreading lemma; claims (1)–(12); `N_o = L_o`; properties (a)–(f) of p. 739)
  and this file (the conclusions of Theorem 1).

**Shape changes in §5** (each recorded at its statement): the skeleton's `include hX hd` is
replaced by explicit hypotheses; `hd : IsDecomposableSpace X` is kept only where it is used
(`jones55_a`, for the nondegeneracy of the decomposition space). (b), (c), u.s.c., continuity and
the statement about the elements hold for every homogeneous compact metric continuum.
-/

namespace HPC.Jones

open Set Topology Filter Metric

section Jones55

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Each `L_x` is a continuum (p. 738: "It follows from Theorem 3 of [11] that `N_o` is a
continuum", with `N_o = M − U_o = L_o`). Jones 1948 Theorem 3 gives this for every `x`, with no
homogeneity: `theorem3`. -/
theorem jones55_isContinuum (x : X) : Fold.Q78.IsContinuum (Lset x) := isContinuum_Lset x

omit [ConnectedSpace X] in
/-- **Jones 1955, Theorem 1 (b).** The sets `L_x` are mutually exclusive: `y ∈ L_x` iff
`L_y = L_x`.

*Shape change:* `hd` is dropped (not used). *Proof change:* by the spreading lemma
(`aposAt_of_isContinuum_interior`, from the Effros theorem) and the Lemma of Jones 1951, not by
Jones's claims (9)–(12) and his case argument on p. 738. -/
theorem jones55_b (hX : IsHomogeneous X) {x y : X} : y ∈ Lset x ↔ Lset y = Lset x :=
  mem_Lset_iff_Lset_eq hX

omit [ConnectedSpace X] in
/-- **Jones 1955, Theorem 1 (c).** A subcontinuum meeting `L_x` and its complement contains
`L_x`.

*Shape change:* `hd` is dropped (not used). -/
theorem jones55_c (hX : IsHomogeneous X) {x : X} {K : Set X} (hK : Fold.Q78.IsContinuum K)
    (h1 : (K ∩ Lset x).Nonempty) (h2 : (K \ Lset x).Nonempty) : Lset x ⊆ K :=
  Lset_subset_of_meets hX hK h1 h2

/-- The elements of `lSetoid X` are the sets `L_x`. -/
theorem cls_lSetoid (hX : IsHomogeneous X) (x : X) : cls (lSetoid X) x = Lset x := by
  ext y
  exact (jones55_b hX).symm

/-- The relation of `lSetoid X` is "not aposyndetic at the first point with respect to the
second"; in particular it is closed in `X × X`. -/
theorem isClosed_lSetoid (hX : IsHomogeneous X) :
    IsClosed {p : X × X | (lSetoid X) p.1 p.2} := by
  have he : {p : X × X | (lSetoid X) p.1 p.2} = {p : X × X | ¬ AposAt p.1 p.2} := by
    ext p
    show Lset p.1 = Lset p.2 ↔ ¬ AposAt p.1 p.2
    rw [← jones55_b hX, mem_Lset_iff]
  rw [he]
  exact isClosed_setOf_not_aposAt

/-- `G` is upper semicontinuous (p. 739).

*Shape change:* `hd` is dropped (not used). *Proof change:* Jones argues by convergent sequences
of elements and (f); here the relation is closed in `X × X` (`isClosed_lSetoid`), and a closed
equivalence relation on a compact metric space is u.s.c. (`isUSCDecomp_of_isClosed`). -/
theorem jones55_usc (hX : IsHomogeneous X) : IsUSCDecomp (lSetoid X) :=
  isUSCDecomp_of_isClosed (isClosed_lSetoid hX)

/-- Homeomorphisms permute the elements `L_x`. -/
theorem lSetoid_homeomorph (T : X ≃ₜ X) (a b : X) : (lSetoid X) a b ↔ (lSetoid X) (T a) (T b) := by
  show Lset a = Lset b ↔ Lset (T a) = Lset (T b)
  rw [Lset_homeomorph, Lset_homeomorph]
  exact T.injective.image_injective.eq_iff.symm

/-- `G` is continuous (p. 739, last sentence of the proof: residual continuity + homogeneity).

*Shape change:* `hd` is dropped (not used). As printed: `G` is continuous at some element
(`exists_lscAt`, the unstated theorem: `residual_lscAt`), and a homeomorphism permuting the
elements carries continuity at an element to continuity at its image (`lscAt_homeomorph`). -/
theorem jones55_continuous (hX : IsHomogeneous X) : IsContinuousDecomp (lSetoid X) := by
  refine ⟨jones55_usc hX, fun x => ?_⟩
  obtain ⟨x₀, h₀⟩ := exists_lscAt (jones55_usc hX)
  obtain ⟨T, hT⟩ := hX x₀ x
  have := lscAt_homeomorph T (lSetoid_homeomorph T) h₀
  rwa [hT] at this

/-- **Jones 1955, Theorem 1 (a).** "With respect to its elements (as points) `G` is a homogeneous,
aposyndetic, compact, metric continuum", and `G` is nondegenerate.

Aposyndesis is not argued by Jones (COMMISSION-batch136 §3, item 2); the proof here is the
commissioner's sketch: for `g ≠ g′`, `x ∈ g`, `y ∈ g′`, a continuum `K` containing a neighbourhood
`V` of `y` and missing `x` misses `g` by (c); its image is a continuum missing `g`, and by lower
semicontinuity at `g′` it contains the open set of elements lying in a neighbourhood `W` of `g′`
whose elements all meet `V`. -/
theorem jones55_a (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) :
    CompactSpace (Quotient (lSetoid X)) ∧ ConnectedSpace (Quotient (lSetoid X)) ∧
      TopologicalSpace.MetrizableSpace (Quotient (lSetoid X)) ∧
      Nontrivial (Quotient (lSetoid X)) ∧ IsHomogeneous (Quotient (lSetoid X)) ∧
      IsAposyndeticT (Quotient (lSetoid X)) := by
  have husc := jones55_usc hX
  have hcont := jones55_continuous hX
  refine ⟨inferInstance, inferInstance, metrizableSpace_quotient husc, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy, hap⟩ := theorem8.mp hd
    refine ⟨⟨Quotient.mk _ x, Quotient.mk _ y, fun h => ?_⟩⟩
    have hx : x ∈ cls (lSetoid X) y := mk_eq_mk_iff_mem_cls.mp h
    rw [cls_lSetoid hX, mem_Lset_iff] at hx
    exact hx hap
  · intro q₁ q₂
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    obtain ⟨T, hT⟩ := hX a b
    obtain ⟨S, hS⟩ := exists_homeomorph_quotient T (lSetoid_homeomorph T)
    exact ⟨S, by rw [hS, hT]⟩
  · intro q₁ q₂ hne
    induction q₁ using Quotient.inductionOn with | h y => ?_
    induction q₂ using Quotient.inductionOn with | h x => ?_
    have hyx : y ∉ Lset x := fun h => hne (mk_eq_mk_iff_mem_cls.mpr ((cls_lSetoid hX x).symm ▸ h))
    have hap : AposAt y x := by rwa [mem_Lset_iff, not_not] at hyx
    obtain ⟨K, V, hK, hV, hyV, hVK, hxK⟩ := hap
    obtain ⟨W, hW, hyW, hWV⟩ := hcont.2 y y (mem_cls_self y) V hV hyV
    refine ⟨Quotient.mk _ '' K, satIn (lSetoid X) W,
      ⟨hK.1.image continuous_quotient_mk', hK.2.image _ continuous_quotient_mk'.continuousOn⟩,
      isOpen_satIn husc hW, mk_mem_satIn.mpr hyW, ?_, ?_⟩
    · intro q hq
      induction q using Quotient.inductionOn with | h z => ?_
      obtain ⟨v, hvz, hvV⟩ := hWV z (mk_mem_satIn.mp hq (mem_cls_self z))
      exact ⟨v, hVK hvV, mk_eq_mk_iff_mem_cls.mpr hvz⟩
    · rintro ⟨k, hk, hkx⟩
      have hkL : k ∈ Lset x := (cls_lSetoid hX x) ▸ mk_eq_mk_iff_mem_cls.mp hkx
      exact hxK (jones55_c hX hK ⟨k, hk, hkL⟩ ⟨y, hVK hyV, hyx⟩ (mem_Lset_self x))

omit [ConnectedSpace X] in
/-- Each element of `G` is homogeneous (p. 739: "So `G` is a collection of mutually exclusive,
homogeneous, nondegenerate continua … and each two elements of `G` are homeomorphic"). Stated in
the degenerate-free case of the proof: `M` not aposyndetic.

*Shape change:* `hd` is dropped (not used). -/
theorem jones55_elements (hX : IsHomogeneous X) (hna : ¬ IsAposyndetic X) (x y : X) :
    (Lset x).Nontrivial ∧ Nonempty (Lset x ≃ₜ Lset y) ∧
      ∀ a b : Lset x, ∃ T : Lset x ≃ₜ Lset x, T a = b := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsAposyndetic at hna
    push_neg at hna
    obtain ⟨a, b, hab, hn⟩ := hna
    obtain ⟨T, hT⟩ := hX b x
    refine ⟨T a, ?_, x, mem_Lset_self x, fun h => hab (T.injective (h.trans hT.symm))⟩
    rw [← hT, Lset_homeomorph]
    exact mem_image_of_mem _ (mem_Lset_iff.mpr hn)
  · obtain ⟨T, hT⟩ := hX x y
    have he : T '' Lset x = Lset y := by rw [← hT, Lset_homeomorph]
    exact ⟨(T.image (Lset x)).trans (Homeomorph.setCongr he)⟩
  · intro a b
    obtain ⟨T, hT⟩ := hX a b
    have hLa : Lset (a : X) = Lset x := (jones55_b hX).mp a.2
    have hLb : Lset (b : X) = Lset x := (jones55_b hX).mp b.2
    have he : T '' Lset x = Lset x := by
      rw [← hLa, ← Lset_homeomorph, hT, hLb, hLa]
    refine ⟨(T.image (Lset x)).trans (Homeomorph.setCongr he), ?_⟩
    apply Subtype.ext
    exact hT

end Jones55

end HPC.Jones
