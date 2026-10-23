import HPC.Jones.Jones55Core

/-!
# Batch 136, item C: Jones 1951, Theorem 1

F. B. Jones, *Certain homogeneous unicoherent indecomposable continua*, Proc. AMS 2 (1951),
855–859, Theorem 1: a homogeneous, hereditarily unicoherent, compact metric continuum is
indecomposable.

**The proof is not Jones's.** Jones builds the sets `U`, `H`, `N_o`, shows that the translates of
`H` form an u.s.c. decomposition `G`, passes to the decomposition space `M′`, and applies Whyburn
(6.21) in `M′` together with the hereditary unicoherence of `M′`. Here the decomposition space is
not needed. By Jones 1955 Theorem 1 (b) (`mem_Lset_iff_Lset_eq`, proved in `Jones55Core` from the
Effros theorem) the sets `L_x` partition `X` into closed sets. If `X` is decomposable, there are
`a`, `b` with `L_a ≠ L_b`. Let `J` be a subcontinuum irreducible about `{a, b}`; by hereditary
unicoherence (on `M` itself) `J` lies in every continuum containing `a` and `b`. `J` is connected,
so it is not covered by the disjoint closed sets `L_a`, `L_b`: some `c ∈ J` lies in a third element.
Then `a`, `b ∈ M − L_c = U_c`, and claim (5) of Jones 1955 (no point cuts two points of `U_c`;
Bing's Corollary 2 and homogeneity) gives a continuum through `a`, `b` missing `c`. It contains
`J ∋ c`: a contradiction.
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- In a hereditarily unicoherent space, two subcontinua with a common point meet in a
subcontinuum. -/
theorem isContinuum_inter_of_hu (hhu : HPC.Plane.IsHereditarilyUnicoherent (univ : Set X))
    {A B : Set X} (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAB : (A ∩ B).Nonempty) : Fold.Q78.IsContinuum (A ∩ B) := by
  refine ⟨hA.1.inter_right hB.1.isClosed, ?_⟩
  have hU : Fold.Q78.IsContinuum (A ∪ B) :=
    ⟨hA.1.union hB.1, IsConnected.union hAB hA.2 hB.2⟩
  by_cases hnt : (A ∪ B).Nontrivial
  · exact hhu (A ∪ B) (subset_univ _) hU hnt A B hA hB rfl
  · obtain ⟨z, hz⟩ := hAB
    have hsub : (A ∪ B).Subsingleton := not_nontrivial_iff.mp hnt
    have he : A ∩ B = {z} := by
      refine eq_singleton_iff_unique_mem.mpr ⟨hz, fun w hw => ?_⟩
      exact hsub (Or.inl hw.1) (Or.inl hz.1)
    rw [he]
    exact isConnected_singleton

/-- **Jones 1951, Theorem 1.** A homogeneous hereditarily unicoherent compact metric continuum is
indecomposable.

*Shape change:* the skeleton's `[Nontrivial X]` is dropped: a decomposable continuum is
nondegenerate (`nontrivial_of_isDecomposableSpace`), so the statement needs no such hypothesis.
Hereditary unicoherence is used on `X` only. -/
theorem jones51_theorem1 [ConnectedSpace X] (hX : IsHomogeneous X)
    (hhu : HPC.Plane.IsHereditarilyUnicoherent (univ : Set X)) : ¬ IsDecomposableSpace X := by
  intro hd
  haveI := nontrivial_of_isDecomposableSpace hd
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨b, hb⟩ := aposSet_nonempty hX hd a
  have hbLa : b ∉ Lset a := by
    rw [Lset_eq_compl, notMem_compl_iff]
    exact hb
  have haLb : a ∉ Lset b := fun h => hbLa (by
    rw [(mem_Lset_iff_Lset_eq hX).mp h]
    exact mem_Lset_self b)
  obtain ⟨J, -, hJc, hJab, hJirr⟩ := HPC.Plane.exists_irreducibleAbout (M := univ)
    isContinuum_univ (subset_univ ({a, b} : Set X)) ⟨a, mem_insert a _⟩
  have haJ : a ∈ J := hJab (mem_insert a _)
  have hbJ : b ∈ J := hJab (mem_insert_of_mem a rfl)
  -- `J` lies in every continuum through `a` and `b`
  have hJmin : ∀ K : Set X, Fold.Q78.IsContinuum K → a ∈ K → b ∈ K → J ⊆ K := by
    intro K hK haK hbK
    have hJK := isContinuum_inter_of_hu hhu hJc hK ⟨a, haJ, haK⟩
    have he := hJirr (J ∩ K) hJK inter_subset_left
      (insert_subset ⟨haJ, haK⟩ (singleton_subset_iff.mpr ⟨hbJ, hbK⟩))
    rw [← he]
    exact inter_subset_right
  -- a point of `J` in a third element
  obtain ⟨c, hcJ, hca, hcb⟩ : ∃ c ∈ J, c ∉ Lset a ∧ c ∉ Lset b := by
    by_contra hno
    push_neg at hno
    have hcov : J ⊆ Lset a ∪ Lset b := fun c hc => by
      by_cases hca : c ∈ Lset a
      · exact Or.inl hca
      · exact Or.inr (hno c hc hca)
    have hdisj : J ∩ (Lset a ∩ Lset b) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨-, hza, hzb⟩
      exact haLb ((mem_Lset_iff_Lset_eq hX).mpr
        (((mem_Lset_iff_Lset_eq hX).mp hza).symm.trans ((mem_Lset_iff_Lset_eq hX).mp hzb)))
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hJc.2.isPreconnected _ _
      (isClosed_Lset a) (isClosed_Lset b) hcov hdisj with h | h
    · exact hbLa (h hbJ)
    · exact haLb (h haJ)
  -- `a` and `b` are in `U_c`
  have hmem : ∀ w, w ∉ Lset c → w ∈ aposSet c := fun w hw => by
    rwa [Lset_eq_compl, notMem_compl_iff] at hw
  have haLc : a ∉ Lset c := fun h => hca (((mem_Lset_iff_Lset_eq hX).mp h) ▸ mem_Lset_self c)
  have hbLc : b ∉ Lset c := fun h => hcb (((mem_Lset_iff_Lset_eq hX).mp h) ▸ mem_Lset_self c)
  obtain ⟨K, hK, haK, hbK, hcK⟩ :=
    exists_continuum_of_mem_aposSet hX (hmem a haLc) (hmem b hbLc)
  exact hcK (hJmin K hK haK hbK hcJ)

end HPC.Jones
