import HPC.BJ59.Thm7Core
import HPC.BJ59.Transfer

/-!
# Batch 199, library: Bing–Jones Theorem 7, first sentence, in a metric space
(commission 199, §6)

The pseudo-arc `P` is a compact space; the traces of the links of `D` on `P` form a chain of `P`
(`traceChain`), Theorem 7 holds there (`bj7_compact`), and the resulting chain of `P` lifts back to
a chain of the ambient space in Bing–Jones's sense inside the links of `D`
(`exists_bjChain_shrink'`).
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- The traces of the links of a chain on a connected set `P` that they cover and all meet. -/
def traceChain {P : Set X} (hP : IsPreconnected P) {n : ℕ} (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) : Chain P n where
  link j := Subtype.val ⁻¹' D.link j
  isOpen j := (D.isOpen j).preimage continuous_subtype_val
  adjacent i j := by
    have hpre : IsPreconnected (univ : Set P) :=
      Subtype.preconnectedSpace hP |>.isPreconnected_univ
    have hdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
        Subtype.val ⁻¹' D.link i ∩ Subtype.val ⁻¹' D.link j = (∅ : Set P) := fun i j hij =>
      eq_empty_of_forall_notMem fun x hx => by
        have := (D.adjacent i j).1 ⟨x, hx.1, hx.2⟩
        omega
    have hcov : (univ : Set P) ⊆ ⋃ j, Subtype.val ⁻¹' D.link j := fun x _ => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hDP x.2)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hne : ∀ j, (Subtype.val ⁻¹' D.link j ∩ (univ : Set P)).Nonempty := fun j => by
      obtain ⟨x, hxD, hxP⟩ := hDp j
      exact ⟨⟨x, hxP⟩, hxD, mem_univ _⟩
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      rw [hdisj i j h'] at h
      exact not_nonempty_empty h
    · intro h
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact adjacent_meet_of_cover hpre _ (fun j => (D.isOpen j).preimage continuous_subtype_val)
          hcov hne hdisj i j (by omega)
      · have : i = j := Fin.ext heq
        subst this
        obtain ⟨x, hx, -⟩ := hne i
        exact ⟨x, hx, hx⟩
      · rw [inter_comm]
        exact adjacent_meet_of_cover hpre _ (fun j => (D.isOpen j).preimage continuous_subtype_val)
          hcov hne hdisj j i (by omega)

/-- **Bing–Jones, Theorem 7, first sentence.** -/
theorem bj_theorem7' {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  classical
  haveI : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.1.1
  have hPS : IsPseudoArc (univ : Set P) :=
    isPseudoArc_subtype_of_image (by rw [Subtype.coe_image_univ]; exact hP)
  set T := traceChain hP.1.1.2.isPreconnected D hDP hDp
  obtain ⟨E, hEcov, hET⟩ := bj7_compact hPS T (fun x _ => mem_iUnion.1 (hDP x.2) |>.elim
    fun j hj => mem_iUnion.2 ⟨j, hj⟩) H hH hHs
  -- lift the links
  choose W hWo hWE using fun i => isOpen_induced_iff.1 (E.isOpen i)
  set V : Fin m → Set X := fun i => W i ∩ D.link (H i)
  have hVo : ∀ i, IsOpen (V i) := fun i => (hWo i).inter (D.isOpen _)
  have hmemE : ∀ i (x : P), x ∈ E.link i → (x : X) ∈ V i := fun i x hx =>
    ⟨show x ∈ Subtype.val ⁻¹' W i by rw [hWE i]; exact hx, hET i hx⟩
  have hmemV : ∀ i (x : X) (hx : x ∈ P), x ∈ V i → (⟨x, hx⟩ : P) ∈ E.link i := fun i x hx hV => by
    rw [← hWE i]; exact hV.1
  obtain ⟨E', hBJ, hcov, hmeet, hsub⟩ := exists_bjChain_shrink' hP.1.1 V hVo
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hEcov (mem_univ (⟨x, hx⟩ : P)))
      exact mem_iUnion.2 ⟨i, hmemE i _ hi⟩)
    (fun i => by
      obtain ⟨x, hx⟩ := E.link_nonempty i
      exact ⟨x, hmemE i x hx, x.2⟩)
    (fun _ => ∅) (fun _ => ⟨isCompact_empty, empty_subset _⟩)
    (fun i j hij => by
      rw [Set.disjoint_left]
      rintro x (⟨hxi, hxP⟩ | hx) (⟨hxj, -⟩ | hx')
      · have := (E.adjacent i j).1 ⟨_, hmemV i x hxP hxi, hmemV j x hxP hxj⟩
        omega
      all_goals simp_all)
  exact ⟨E', hBJ, hcov, hmeet, fun i => subset_closure.trans ((hsub i).1.trans inter_subset_right)⟩

end HPC.BJ59
