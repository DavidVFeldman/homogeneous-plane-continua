import HPC.Moore.Sec7Th42

/-!
# Moore, F.A. (1916), §7: Theorem 41, Case I (batch 139)

Moore's proof of Theorem 41 (p. 155) splits into two cases.

* **Case I**: `J₁` and `J₂` have at most one point in common. Moore: "it easily follows that either
  `I₁` is in `I₂` or `I₂` is in `I₁`" (commission check 6, first sentence). This is
  `fa_theorem41_caseI_nested`, and Theorem 41 in this case is `fa_theorem41_caseI`.
* **Case II, first sub-case**: "If every point of `J₁` is within or on `J₂` then `J` is `J₂`"
  (`fa_theorem41_of_subset`, Theorem 21).
* **Case II** proper (`J₁ ∩ J₂` has at least two points, each curve has a point without the other)
  ends with "It may be proved that `J` is a closed
  curve satisfying the requirements of Theorem 41"; it is left open (see `OPEN.md`).

Proof of Case I. If `J₂` misses `I₁`, then `I₁` (connected, meeting `I₂`) misses the boundary
`J₂` of `I₂`, so `I₁ ⊆ I₂`. Otherwise `J₂` has a point `x` within `J₁`. It has no point `y`
without `J₁`: the two arcs of `J₂` from `x` to `y` would each meet `J₁` (they are connected and
go from `I₁` to the exterior of `I₁`), at points other than `x`, `y`, hence at two different
points of `J₁ ∩ J₂`. So `J₂ ⊆ I₁ + J₁ = I₁'`, and Theorem 21 gives `I₂ ⊆ I₁`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A closed curve `J₂` meeting both the interior and the exterior of a closed curve `J₁` meets
`J₁` in two different points. *Axioms used: 1, 2, 3, 4, 5₁, 7.* -/
theorem two_meets_of_in_out (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7) {J₁ I₁ J₂ : Set S}
    (hI₁ : σ.IsInteriorOf J₁ I₁) (hJ₂ : σ.IsSCC J₂) {x y : S} (hx : x ∈ J₂) (hxI : x ∈ I₁)
    (hy : y ∈ J₂) (hyE : y ∈ (@closure S σ.topology I₁)ᶜ) :
    ∃ z₁ z₂, z₁ ∈ J₁ ∩ J₂ ∧ z₂ ∈ J₁ ∩ J₂ ∧ z₁ ≠ z₂ := by
  letI := σ.topology
  obtain ⟨hIo, -, -, -, hEo, -, -, -, -, hdisIJ, hdisEJ, hcompl, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI₁
  have hxy : x ≠ y := by
    rintro rfl; exact hyE (subset_closure hxI)
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ₂ hx hy hxy
  have hD₁t := (isArc_iff_tarc h1 h3 h4 h51).mp hD₁
  have hD₂t := (isArc_iff_tarc h1 h3 h4 h51).mp hD₂
  have hdisIE : Disjoint I₁ (closure I₁)ᶜ := disjoint_compl_right.mono_left subset_closure
  -- a connected set from `x` to `y` meets `J₁`
  have meet : ∀ D : Set S, IsPreconnected D → x ∈ D → y ∈ D → ∃ z ∈ D, z ∈ J₁ := by
    intro D hD hxD hyD
    by_contra hno
    push_neg at hno
    have hsub : D ⊆ I₁ ∪ (closure I₁)ᶜ := fun z hz => hcompl ▸ hno z hz
    rcases hD.subset_or_subset hIo hEo hdisIE hsub with h | h
    · exact hdisIE.ne_of_mem (h hyD) hyE rfl
    · exact hdisIE.ne_of_mem hxI (h hxD) rfl
  obtain ⟨z₁, hz₁D, hz₁J⟩ := meet D₁ hD₁t.isPreconnected hD₁t.left_mem hD₁t.right_mem
  obtain ⟨z₂, hz₂D, hz₂J⟩ := meet D₂ hD₂t.isPreconnected hD₂t.left_mem hD₂t.right_mem
  have hxJ : x ∉ J₁ := fun h => disjoint_left.mp hdisIJ hxI h
  have hyJ : y ∉ J₁ := fun h => disjoint_left.mp hdisEJ hyE h
  refine ⟨z₁, z₂, ⟨hz₁J, hDu ▸ Or.inl hz₁D⟩, ⟨hz₂J, hDu ▸ Or.inr hz₂D⟩, ?_⟩
  rintro rfl
  have : z₁ ∈ D₁ ∩ D₂ := ⟨hz₁D, hz₂D⟩
  rw [hDi] at this
  rcases this with h | h
  · exact hxJ (h ▸ hz₁J)
  · exact hyJ ((mem_singleton_iff.mp h) ▸ hz₁J)

/-- **Theorem 41, Case I** (p. 155: "it easily follows that either `I₁` is in `I₂` or `I₂` is in
`I₁`"). If the closed curves `J₁`, `J₂` have at most one point in common and their interiors
meet, one interior contains the other. *Axioms used: 1, 2, 3, 4, 5, 7.* -/
theorem fa_theorem41_caseI_nested (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) {J₁ J₂ I₁ I₂ : Set S}
    (hI₁ : σ.IsInteriorOf J₁ I₁) (hI₂ : σ.IsInteriorOf J₂ I₂) (hmeet : (I₁ ∩ I₂).Nonempty)
    (hsing : (J₁ ∩ J₂).Subsingleton) : I₁ ⊆ I₂ ∨ I₂ ⊆ I₁ := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, hI₁c, -, hfr₁, -, -, -, -, hcl₁, -, -, hcompl₁, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI₁
  obtain ⟨-, -, -, hfr₂, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₂
  by_cases hJI : ∃ x ∈ J₂, x ∈ I₁
  · right
    obtain ⟨x, hxJ, hxI⟩ := hJI
    refine th21Prop h1 h3 h4 h5 h7 I₁ hI₁.2.1 I₂ hI₂.2.1 ?_
    rw [hfr₂]
    intro y hy
    by_contra hyE
    obtain ⟨z₁, z₂, hz₁, hz₂, hne⟩ :=
      two_meets_of_in_out h1 h2 h3 h4 h51 h7 hI₁ hI₂.1 hxJ hxI hy hyE
    exact hne (hsing hz₁ hz₂)
  · left
    push_neg at hJI
    refine conn_sub_of_frontier hI₁c ?_ (by rwa [inter_comm] at hmeet ⊢)
    rw [hfr₂, disjoint_left]
    intro y hyI hyJ
    exact hJI y hyJ hyI

/-- **Theorem 41 in Case I**: if the closed curves `J₁`, `J₂` have at most one point in common and
their interiors meet, the larger of the two curves satisfies the conclusion of Theorem 41.
*Axioms used: 1, 2, 3, 4, 5, 7.* -/
theorem fa_theorem41_caseI (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) {J₁ J₂ I₁ I₂ : Set S} (hI₁ : σ.IsInteriorOf J₁ I₁)
    (hI₂ : σ.IsInteriorOf J₂ I₂) (hmeet : (I₁ ∩ I₂).Nonempty) (hsing : (J₁ ∩ J₂).Subsingleton) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  rcases fa_theorem41_caseI_nested h1 h2 h3 h4 h5 h7 hI₁ hI₂ hmeet hsing with h | h
  · exact ⟨J₂, I₂, subset_union_right, hI₂, union_subset h subset_rfl⟩
  · exact ⟨J₁, I₁, subset_union_left, hI₁, union_subset subset_rfl h⟩

/-- **Theorem 41, first sub-case of Case II** (p. 155: "If every point of `J₁` is within or on
`J₂` then `J` is `J₂`"). Theorem 21: the boundary `J₁` of `I₁` lies in `I₂' = I₂ + J₂`, so
`I₁ ⊆ I₂`. No assumption on `J₁ ∩ J₂` and none on `I₁ ∩ I₂` is needed.
*Axioms used: 1, 3, 4, 5, 7.* -/
theorem fa_theorem41_of_subset (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) {J₁ J₂ I₁ I₂ : Set S} (hI₁ : σ.IsInteriorOf J₁ I₁)
    (hI₂ : σ.IsInteriorOf J₂ I₂) (hsub : J₁ ⊆ I₂ ∪ J₂) :
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I := by
  letI := σ.topology
  have h12 : I₁ ⊆ I₂ := by
    refine th21Prop h1 h3 h4 h5 h7 I₂ hI₂.2.1 I₁ hI₁.2.1 ?_
    have hfr₁ : frontier I₁ = J₁ := by rw [← bdry_eq_frontier h1]; exact hI₁.2.2
    have hfr₂ : frontier I₂ = J₂ := by rw [← bdry_eq_frontier h1]; exact hI₂.2.2
    rw [hfr₁]
    intro x hx
    rcases hsub hx with h | h
    · exact subset_closure h
    · exact frontier_subset_closure (hfr₂ ▸ h)
  exact ⟨J₂, I₂, subset_union_right, hI₂, union_subset h12 subset_rfl⟩

end HPC.Moore
