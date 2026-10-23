import HPC.Moore.Sec6Plane

/-!
# Moore, F.A. (1916), §6: the bridge, Theorems 20–23, and the interior of a closed curve
(batch 138, items A and B)

* The bridge from Moore's notions to the topological setting of `Sec6Plane.lean`:
  `bdry_eq_frontier`, `ext_eq_compl_closure`, `isArc_iff_tarc`, `isSCC_iff_tscc`,
  `isInteriorOf_iff`, `arcConn`, `locallyConnectedSpace`.
* **Theorem 20** (`fa_theorem20`): from Axiom 7 alone.
* **Theorem 21** (`fa_theorem21`): Moore's proof.
* **Theorem 22** (`fa_theorem22`): the whole space is connected; this is batch 137's
  `isConn_univ` (Axioms 1, 3, 4, 5). Moore's hint (Theorem 19, Axioms 2, 3, Theorem 20) is not
  needed.
* **The interior of a closed curve** (`existsUnique_interior`): unnumbered; existence by Axiom 8,
  uniqueness by Theorem 21.
* **Theorem 23** (`fa_theorem23`): Moore's proof, with the two points `A₁`, `B₁` obtained as a
  last and a first point. The printed form (no `R ≠ ∅`) is refuted (`not_fa_theorem23_printed`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-! ### The bridge -/

section Bridge1

variable (h1 : σ.Axiom1)
include h1

/-- Moore's boundary is the topological frontier. *Axioms used: 1.* -/
theorem bdry_eq_frontier (M : Set S) : σ.bdry M = @frontier S σ.topology M := by
  letI := σ.topology
  have hb := isTopologicalBasis_region h1
  ext x
  rw [frontier_eq_closure_inter_closure, mem_inter_iff, hb.mem_closure_iff, hb.mem_closure_iff]
  simp only [Space.bdry, mem_setOf_eq]
  constructor
  · intro h; exact ⟨fun R hR hx => (h R hR hx).1, fun R hR hx => (h R hR hx).2⟩
  · rintro ⟨h₁, h₂⟩ R hR hx; exact ⟨h₁ R hR hx, h₂ R hR hx⟩

/-- Moore's exterior is the complement of the closure. *Axioms used: 1.* -/
theorem ext_eq_compl_closure (M : Set S) : σ.ext M = (@closure S σ.topology M)ᶜ := by
  rw [Space.ext, cl_eq_closure h1]

/-- The regions are connected open sets forming a basis, so the space is locally connected.
*Axioms used: 1, 2.* -/
theorem locallyConnectedSpace (h2 : σ.Axiom2) : @LocallyConnectedSpace S σ.topology := by
  letI := σ.topology
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨R, hR, hxR, hRU⟩ := (mem_nhds_iff_region h1).mp hU
  exact ⟨R, hRU, isOpen_region hR, hxR, ⟨x, hxR⟩, (isConn_iff h1).mp (h2 R hR)⟩

/-- Every open set about `P` contains, with its closure, a region about `P`. *Axioms used: 1.* -/
theorem exists_region_closure_subset {U : Set S} (hU : @IsOpen S σ.topology U) {P : S}
    (hP : P ∈ U) : ∃ K ∈ σ.region, P ∈ K ∧ @closure S σ.topology K ⊆ U := by
  obtain ⟨R, hR, hPR, hRU⟩ := (isOpen_iff_region h1).mp hU P hP
  obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset h1 hR hPR
  exact ⟨K, hK, hPK, (cl_eq_closure h1 K ▸ hcl).trans hRU⟩

/-- Axiom 5 makes the space non-compact. *Axioms used: 1, 5.* -/
theorem not_isCompact_univ (h5 : σ.Axiom5) : ¬ @IsCompact S σ.topology univ := by
  letI := σ.topology
  intro hK
  obtain ⟨M, hM, hlim⟩ := h5
  obtain ⟨x, -, hx⟩ := hM.exists_accPt_of_subset_isCompact hK (subset_univ M)
  exact hlim x ((isLimitPt_iff h1).mpr hx)

end Bridge1

section Bridge2

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- Moore arcs are the topological arcs of `Sec6Arc.lean`. *Axioms used: 1, 3, 4, 5₁*
(batch 137's `isArc_iff`). -/
theorem isArc_iff_tarc {A B : S} {C : Set S} : σ.IsArc A B C ↔ @TArc S σ.topology A B C :=
  isArc_iff h1 h3 h4 h51

theorem isSCC_iff_tscc {J : Set S} : σ.IsSCC J ↔ @TSCC S σ.topology J := by
  simp only [Space.IsSCC, TSCC, isArc_iff_tarc h1 h3 h4 h51]

theorem isInteriorOf_iff {J R : Set S} :
    σ.IsInteriorOf J R ↔ @TInt S σ.topology σ.region J R := by
  rw [Space.IsInteriorOf, isSCC_iff_tscc h1 h3 h4 h51, bdry_eq_frontier h1]; rfl

/-- **Theorem 15**, in the form used in §6. *Axioms used: 1, 2, 3, 4, 5₁.* -/
theorem arcConn (h2 : σ.Axiom2) : @ArcConn S σ.topology := by
  intro U hUo hUc a ha b hb hab
  obtain ⟨C, hCU, hC⟩ := exists_arc_of_isOpen_isPreconnected h1 h2 h3 h4 h51 hUo hUc ha hb hab
  exact ⟨C, hCU, (isArc_iff_tarc h1 h3 h4 h51).mp hC⟩

end Bridge2

/-! ### Theorems 20–22 -/

/-- **Theorem 20.** Every point of the boundary of a region is a limit point of its exterior.
(\"Can easily be proved with the help of Axiom 7\"; no proof printed.) *Axioms used: 7.*
Proof: for a region `R̄` about `P`, Axiom 7 gives a region `L ⊆ R̄` in the exterior of `R` and a
region `L̄ ∋ P` with every boundary point of `R` in `L̄` a boundary point of `L`; so `P` is a
boundary point of `L`, and `L̄` contains a point of `L`, which is not `P`.
**Shape change:** only Axiom 7 is assumed (the skeleton's section assumes Axioms 1–8). -/
theorem fa_theorem20 (h7 : σ.Axiom7) {R : Set S} (hR : R ∈ σ.region) {P : S}
    (hP : P ∈ σ.bdry R) : σ.IsLimitPt P (σ.ext R) := by
  intro R' hR' hPR'
  obtain ⟨L, hL, L', hL', hLR', -, hPL', hLext, hbd⟩ := h7 R hR R' hR' P hPR' hP
  obtain ⟨x, hxL', hxL⟩ := (hbd ⟨hP, hPL'⟩ L' hL' hPL').1
  refine ⟨x, hLext hxL, hLR' hxL, fun h => ?_⟩
  exact hLext hxL (h ▸ Or.inr hP)

/-- Theorem 20, topologically: the boundary of a region lies in the closure of its exterior.
*Axioms used: 1, 7.* -/
theorem frontier_subset_closure_ext (h1 : σ.Axiom1) (h7 : σ.Axiom7) {R : Set S}
    (hR : R ∈ σ.region) :
    @frontier S σ.topology R ⊆ @closure S σ.topology (@closure S σ.topology R)ᶜ := by
  letI := σ.topology
  intro P hP
  rw [← bdry_eq_frontier h1] at hP
  have hlim := fa_theorem20 h7 hR hP
  rw [(isTopologicalBasis_region h1).mem_closure_iff]
  intro R' hR' hPR'
  obtain ⟨x, hx, hxR', -⟩ := hlim R' hR' hPR'
  exact ⟨x, hxR', by rwa [← ext_eq_compl_closure h1]⟩

/-- **Theorem 21.** If `K`, `R` are regions and the boundary of `R` lies in `K'`, then `R ⊆ K`.
*Axioms used: 1, 3, 4, 5, 7.* Moore's proof: the exterior `S − K'` is connected (Axiom 3) and is
not inside `R'` (Theorem 18: `R'` is compact, `S` is not); were it to meet `R` it would meet the
boundary of `R`, which lies in `K'`. So `R ⊆ K'`, and a point of `R` on the boundary of `K` would
be a limit point of `S − K'` (Theorem 20). **Shape change:** the axioms are made explicit. -/
theorem fa_theorem21 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) {K R : Set S} (hK : K ∈ σ.region) (hR : R ∈ σ.region)
    (h : σ.bdry R ⊆ σ.cl K) : R ⊆ K := by
  letI := σ.topology
  rw [bdry_eq_frontier h1, cl_eq_closure h1] at h
  have hRo : IsOpen R := isOpen_region hR
  have hKo : IsOpen K := isOpen_region hK
  have hE : IsPreconnected (closure K)ᶜ := by
    have := (isConn_iff h1).mp (h3 K hK); rwa [ext_eq_compl_closure h1] at this
  have hEnot : ¬ (closure K)ᶜ ⊆ closure R := by
    intro hsub
    apply not_isCompact_univ h1 h5
    have : (univ : Set S) = closure K ∪ closure R := by
      refine (eq_univ_of_forall fun x => ?_).symm
      by_cases hx : x ∈ closure K
      · exact Or.inl hx
      · exact Or.inr (hsub hx)
    rw [this]
    exact (isCompact_closure_region h1 h4 hK).union (isCompact_closure_region h1 h4 hR)
  have hER : (closure K)ᶜ ∩ R = ∅ := by
    by_contra hne'
    have hne := nonempty_iff_ne_empty.mpr hne'
    have hsub : (closure K)ᶜ ⊆ R ∪ (closure R)ᶜ := by
      intro x hx
      by_cases hxR : x ∈ R
      · exact Or.inl hxR
      · right; intro hxc
        exact hx (h (mem_frontier_of_mem_closure hRo hxc hxR))
    have := hE.subset_left_of_subset_union hRo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub hne
    exact hEnot (this.trans subset_closure)
  intro x hxR
  have hxK : x ∈ closure K := by
    by_contra hx
    exact (eq_empty_iff_forall_notMem.mp hER) x ⟨hx, hxR⟩
  by_contra hxK'
  have hfr : x ∈ frontier K := mem_frontier_of_mem_closure hKo hxK hxK'
  obtain ⟨y, hyR, hyE⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure_ext h1 h7 hK hfr) R
    (hRo.mem_nhds hxR)
  exact (eq_empty_iff_forall_notMem.mp hER) y ⟨hyE, hyR⟩

/-- Theorem 21 in the form `Th21Prop`. -/
theorem th21Prop (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) : @Th21Prop S σ.topology σ.region := by
  intro K hK R hR h
  refine fa_theorem21 h1 h3 h4 h5 h7 hK hR ?_
  rwa [bdry_eq_frontier h1, cl_eq_closure h1]

/-- **Theorem 22.** The set of all points is connected. *Axioms used: 1, 3, 4, 5.* This is batch
137's `isConn_univ`: if `S = U ⊔ V` with `U`, `V` open and nonempty, Axiom 3 applied to a region
inside `U` makes `U` compact (Axiom 4), likewise `V`, against Axiom 5. **Shape change:** the
axioms are made explicit; Moore's hint (Theorem 19, Axioms 2 and 3, Theorem 20) is not used. -/
theorem fa_theorem22 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5) :
    σ.IsConn univ :=
  isConn_univ h1 h3 h4 h5

/-- Axiom 8 in the form `Ax8Prop`. -/
theorem ax8Prop (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
    (h8 : σ.Axiom8) : @Ax8Prop S σ.topology σ.region := by
  intro J hJ
  obtain ⟨R, hR, hRJ⟩ := h8 J ((isSCC_iff_tscc h1 h3 h4 h51).mpr hJ)
  exact ⟨R, hR, by rwa [← bdry_eq_frontier h1]⟩

/-- **The interior of a closed curve** (unnumbered; the convention \"the interior of `J`\" is used
from the proof of Theorem 23 on and never defined in F.A.). Every closed curve has exactly one
interior. Existence is Axiom 8; uniqueness is Theorem 21 applied both ways.
*Axioms used: 1, 3, 4, 5, 7, 8.* **Shape change:** the axioms are made explicit. -/
theorem existsUnique_interior (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J : Set S} (hJ : σ.IsSCC J) :
    ∃! R, σ.IsInteriorOf J R := by
  obtain ⟨R, hR, hRJ⟩ := h8 J hJ
  refine ⟨R, ⟨hJ, hR, hRJ⟩, fun R' ⟨_, hR', hR'J⟩ => subset_antisymm ?_ ?_⟩
  · exact fa_theorem21 h1 h3 h4 h5 h7 hR hR' (hR'J ▸ hRJ ▸ fun x hx => Or.inr hx)
  · exact fa_theorem21 h1 h3 h4 h5 h7 hR' hR (hRJ ▸ hR'J ▸ fun x hx => Or.inr hx)

/-! ### Theorem 23 -/

/-- **Theorem 23.** No (nonempty) region is a subset of an arc. *Axioms used: 1, 2, 3, 4, 5₁, 8.*
Moore's proof: a point `O` of `R` other than `A`, `B` (Theorem 4); a region `K` about `O` whose
closure misses `A` and `B`; an arc `AXB` without `K` (Theorem 16). `A₁` is the last point of
`AXB` on the interval `AO`, `B₁` the first point after `A₁` on `OB` (here: the first point of
`BXA` on `AO`, then the first point from there on `OB`). The interval `A₁OB₁` and the arc of
`AXB` from `A₁` to `B₁` form a closed curve `J`; `O` is on the boundary of its interior `R₁`
(Axiom 8), and a region about `O` inside `R` missing `AA₁ + B₁B` lies in `J` and meets `R₁`.
**Shape change:** `R.Nonempty` is added (the empty region refutes the printed form:
`not_fa_theorem23_printed`); the axioms are made explicit, with Axiom 5₁ for Axiom 5. -/
theorem fa_theorem23 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h8 : σ.Axiom8) {R : Set S} (hR : R ∈ σ.region)
    (hne : R.Nonempty) {A B : S} {C : Set S} (hC : σ.IsArc A B C) : ¬ R ⊆ C := by
  letI := σ.topology
  haveI := t2Space h1
  intro hRC
  rw [isArc_iff_tarc h1 h3 h4 h51] at hC
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hC
  obtain ⟨O, hOR, hOAB⟩ := ((fa_theorem4 h1 h3 h51 hR hne).diff (toFinite {f 0, f 1})).nonempty
  obtain ⟨o, rfl⟩ := hRC hOR
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hOAB
  have ho0 : 0 < o := lt_of_le_of_ne nonneg' fun e => hOAB.1 (by rw [← e])
  have ho1 : o < 1 := lt_of_le_of_ne le_one' fun e => hOAB.2 (by rw [e])
  -- a region `K` about `O` whose closure misses `A` and `B`
  have hABc : IsClosed ({f 0, f 1} : Set S) := (toFinite _).isClosed
  obtain ⟨K, hK, hOK, hKcl⟩ := exists_region_closure_subset h1 hABc.isOpen_compl
    (by simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact hOAB)
  have hA : f 0 ∈ (closure K)ᶜ := fun h => hKcl h (by simp)
  have hB : f 1 ∈ (closure K)ᶜ := fun h => hKcl h (by simp)
  have hE : IsPreconnected (closure K)ᶜ := by
    have := (isConn_iff h1).mp (h3 K hK); rwa [ext_eq_compl_closure h1] at this
  obtain ⟨Z, hZE, hZ⟩ := arcConn h1 h3 h4 h51 h2 _ isClosed_closure.isOpen_compl hE _ hA _ hB
    (fun e => zero_ne_one' unitInterval (hf.injective e))
  have hOZ : f o ∉ Z := fun h => hZE h (subset_closure hOK)
  -- the last point of `AXB` on `AO`, then the first point after it on `OB`
  have hc1 : IsClosed (f '' Icc 0 o) := (isCompact_Icc.image hf.continuous).isClosed
  have hc2 : IsClosed (f '' Icc o 1) := (isCompact_Icc.image hf.continuous).isClosed
  obtain ⟨P₁, hP₁, Z₁, hZ₁Z, hZ₁, hZ₁c⟩ := hZ.symm.first_point hc1
    ⟨f 0, hZ.left_mem, mem_image_of_mem _ ⟨le_rfl, nonneg'⟩⟩
    (fun ⟨u, hu, hu1⟩ => by
      have := hf.injective hu1; subst this; exact absurd hu.2 (not_le.mpr ho1))
  obtain ⟨a, ⟨-, hao⟩, rfl⟩ := hP₁
  have hao' : a < o := lt_of_le_of_ne hao fun e => hOZ (e ▸ hZ₁Z hZ₁.right_mem)
  obtain ⟨Q₁, hQ₁, Z₂, hZ₂Z₁, hZ₂, hZ₂c⟩ := hZ₁.symm.first_point hc2
    ⟨f 1, hZ₁.left_mem, mem_image_of_mem _ ⟨le_one', le_rfl⟩⟩
    (fun ⟨u, hu, hua⟩ => by
      have := hf.injective hua; subst this; exact absurd hu.1 (not_le.mpr hao'))
  obtain ⟨b, ⟨hob, -⟩, rfl⟩ := hQ₁
  have hob' : o < b := lt_of_le_of_ne hob fun e => hOZ (e ▸ hZ₁Z (hZ₂Z₁ hZ₂.right_mem))
  have hab : a < b := hao'.trans hob'
  -- the closed curve `J`
  have hZ₂f : Z₂ ∩ range f ⊆ {f a, f b} := by
    rintro _ ⟨hx, u, rfl⟩
    rcases le_total u o with hu | hu
    · left
      have : f u ∈ Z₁ ∩ f '' Icc 0 o := ⟨hZ₂Z₁ hx, mem_image_of_mem _ ⟨nonneg', hu⟩⟩
      rwa [hZ₁c] at this
    · right
      have : f u ∈ Z₂ ∩ f '' Icc o 1 := ⟨hx, mem_image_of_mem _ ⟨hu, le_one'⟩⟩
      rwa [hZ₂c] at this
  have hJ : TSCC (f '' Icc a b ∪ Z₂) := by
    refine ⟨f a, f b, _, _, TArc.image_Icc hf hab, hZ₂, ?_, rfl⟩
    apply subset_antisymm
    · rintro x ⟨hx1, hx2⟩
      exact hZ₂f ⟨hx2, image_subset_range _ _ hx1⟩
    · rintro x hx
      rcases hx with rfl | rfl
      · exact ⟨mem_image_of_mem _ ⟨le_rfl, hab.le⟩, hZ₂.left_mem⟩
      · exact ⟨mem_image_of_mem _ ⟨hab.le, le_rfl⟩, hZ₂.right_mem⟩
  obtain ⟨R₁, hR₁, hR₁J⟩ := ax8Prop h1 h3 h4 h51 h8 _ hJ
  have hOJ : f o ∈ frontier R₁ := hR₁J ▸ Or.inl (mem_image_of_mem _ ⟨hao'.le, hob'.le⟩)
  -- a region about `O` inside `R` missing `AA₁ + B₁B`
  have hcl : IsClosed (f '' Icc 0 a ∪ f '' Icc b 1) :=
    (isCompact_Icc.image hf.continuous).isClosed.union
      (isCompact_Icc.image hf.continuous).isClosed
  have hOU : f o ∈ R ∩ (f '' Icc 0 a ∪ f '' Icc b 1)ᶜ := by
    refine ⟨hOR, ?_⟩
    rintro (⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩) <;> have := hf.injective hu' <;> subst this
    · exact absurd hu.2 (not_le.mpr hao')
    · exact absurd hu.1 (not_le.mpr hob')
  obtain ⟨y, ⟨hyR, hyc⟩, hyR₁⟩ := mem_closure_iff_nhds.mp hOJ.1 _
    (((isOpen_region hR).inter hcl.isOpen_compl).mem_nhds hOU)
  obtain ⟨u, rfl⟩ := hRC hyR
  have hu : u ∈ Icc a b := by
    simp only [mem_compl_iff, mem_union, mem_image, not_or, not_exists, not_and] at hyc
    exact ⟨not_lt.mp fun h => hyc.1 u ⟨nonneg', h.le⟩ rfl,
      not_lt.mp fun h => hyc.2 u ⟨h.le, le_one'⟩ rfl⟩
  have : f u ∈ frontier R₁ := hR₁J ▸ Or.inl (mem_image_of_mem _ hu)
  exact notMem_of_mem_frontier (isOpen_region hR₁) this hyR₁

/-- **Theorem 23 as printed is not a consequence of Axioms 1–8** (unless they have no model): in
the space with `∅` added to the regions (batch 137, `withEmpty`), which satisfies Axioms 1–8,
the region `∅` is a subset of every arc, and arcs exist. -/
theorem not_fa_theorem23_printed (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) :
    σ.withEmpty.Axiom1 ∧ σ.withEmpty.Axiom2 ∧ σ.withEmpty.Axiom3 ∧ σ.withEmpty.Axiom4 ∧
      σ.withEmpty.Axiom5 ∧ σ.withEmpty.Axiom6 ∧ σ.withEmpty.Axiom7 ∧ σ.withEmpty.Axiom8 ∧
      ¬ ∀ R ∈ σ.withEmpty.region, ∀ A B : S, ∀ C : Set S, σ.withEmpty.IsArc A B C →
        ¬ R ⊆ C := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := not_fa_theorem4_printed h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun h => ?_⟩
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨P, -⟩ := axiom5₁_of_axiom5 h5
  obtain ⟨R, hR, hPR⟩ := Space.exists_region_mem h1 P
  obtain ⟨Q, hQR, hQP⟩ := exists_ne_of_region h1 h3 h51 hR hPR
  obtain ⟨C, -, hC⟩ := (fa_theorem16 h1 h2 h3 h4 h51 hR).1 P hPR Q hQR hQP.symm
  exact h ∅ (mem_insert _ _) P Q C (Space.isArc_withEmpty.mpr hC) (empty_subset _)

end HPC.Moore
