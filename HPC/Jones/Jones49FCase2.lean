import HPC.Jones.Jones49FLocal

/-!
# Batch 154: Jones 1949 Theorem 1, Case 2 (item C)

* `TArc.first_point_split` — the first point of an arc on a closed set, with both pieces.
* `exists_domain_meeting` — steps 1–2: a complementary domain `U` of `M` whose boundary meets both
  `H` and `K` (the interior of a trimmed arc `T`).
* `exists_theta_arcs` — step 4: the arc `AxB` of `C` and the complementary arc.
* `jones49_case2_sep` — steps 3–7.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen unitInterval

/-- **The first point, with both pieces.** On an arc from `x` to `y`, neither in the closed set `Z`,
meeting `Z`, the first point `A` on `Z` splits the arc into `xA` (meeting `Z` only in `A`) and
`Ay`. -/
theorem _root_.HPC.Moore.Gen.TArc.first_point_split {X : Type*} [TopologicalSpace X] [T2Space X]
    {x y : X} {P Z : Set X} (h : TArc x y P) (hZ : IsClosed Z) (hne : (P ∩ Z).Nonempty)
    (hx : x ∉ Z) (hy : y ∉ Z) :
    ∃ A ∈ Z, ∃ Γ₁ Γ₂ : Set X, TArc x A Γ₁ ∧ TArc A y Γ₂ ∧ Γ₁ ∪ Γ₂ = P ∧ Γ₁ ∩ Γ₂ = {A} ∧
      Γ₁ ∩ Z = {A} := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  have hT : IsClosed (f ⁻¹' Z) := hZ.preimage hf.continuous
  have hTne : (f ⁻¹' Z).Nonempty := by
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hne; exact ⟨t, ht⟩
  set t := sInf (f ⁻¹' Z)
  have htT : t ∈ f ⁻¹' Z := hT.csInf_mem hTne ⟨0, fun _ _ => nonneg'⟩
  have ht0 : 0 < t := lt_of_le_of_ne nonneg' fun e => hx (e ▸ htT)
  have ht1 : t < 1 := lt_of_le_of_ne le_one' fun e => hy (e ▸ htT)
  refine ⟨f t, htT, f '' Icc 0 t, f '' Icc t 1, TArc.image_Icc hf ht0, TArc.image_Icc hf ht1, ?_,
    ?_, ?_⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc nonneg' le_one', ← image_univ]
    congr 1
    ext s; simp only [mem_Icc, mem_univ, iff_true]; exact ⟨nonneg', le_one'⟩
  · rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton nonneg' le_one', image_singleton]
  · ext z
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨u, ⟨-, hut⟩, rfl⟩, hu⟩
      rw [le_antisymm hut (csInf_le ⟨0, fun _ _ => nonneg'⟩ hu)]
    · rintro rfl
      exact ⟨⟨t, ⟨nonneg', le_rfl⟩, rfl⟩, htT⟩

/-- **Case 2, steps 1–2: the arc `T` and the element `U`.** `M` is closed, `M − J = H + K` with `H`,
`K` separated (here: cut out by open sets `u`, `v`), and `M − J` lies in a connected open set `E`
missing `J`. An arc in `E` from `H` to `K` (`exists_tarc_of_isOpen_plane`), trimmed at its last
point on `H̄` and then its first point on `K̄` (`TArc.first_point`), has its interior in `Mᶜ`; the
component `U` of `Mᶜ` containing it has a point `x` of `H` and a point `y` of `K` on its boundary.
-/
theorem exists_domain_meeting {M J E u v : Set Pt} (hM : IsClosed M) (hEo : IsOpen E)
    (hEc : IsConnected E) (hEJ : Disjoint E J) (hME : M \ J ⊆ E) (hu : IsOpen u) (hv : IsOpen v)
    (hcov : M \ J ⊆ u ∪ v) (huv : Disjoint (M \ J ∩ u) v) {h k : Pt} (hh : h ∈ M \ J ∩ u)
    (hk : k ∈ M \ J ∩ v) :
    ∃ x ∈ M \ J ∩ u, ∃ y ∈ M \ J ∩ v, ∃ w ∉ M, x ∈ frontier (connectedComponentIn Mᶜ w) ∧
      y ∈ frontier (connectedComponentIn Mᶜ w) := by
  set H := M \ J ∩ u
  set K := M \ J ∩ v
  have huv' : Disjoint u (M \ J ∩ v) := disjoint_left.mpr fun z hzu hz =>
    disjoint_left.mp huv ⟨hz.1, hzu⟩ hz.2
  have hhk : h ≠ k := fun e => disjoint_left.mp huv hh (e ▸ hk.2)
  -- closure points of `H` in `E` are in `H`; same for `K`
  have hclH : ∀ z ∈ closure H, z ∈ E → z ∈ H := by
    intro z hz hzE
    have hzM : z ∈ M := closure_minimal (inter_subset_left.trans diff_subset) hM hz
    have hzJ : z ∉ J := fun h => disjoint_left.mp hEJ hzE h
    rcases hcov ⟨hzM, hzJ⟩ with h' | h'
    · exact ⟨⟨hzM, hzJ⟩, h'⟩
    · exact absurd (mem_closure_iff.mp hz v hv h') (by
        rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty]; exact huv.symm)
  have hclK : ∀ z ∈ closure K, z ∈ E → z ∈ K := by
    intro z hz hzE
    have hzM : z ∈ M := closure_minimal (inter_subset_left.trans diff_subset) hM hz
    have hzJ : z ∉ J := fun h => disjoint_left.mp hEJ hzE h
    rcases hcov ⟨hzM, hzJ⟩ with h' | h'
    · exact absurd (mem_closure_iff.mp hz u hu h') (by
        rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty]; exact huv')
    · exact ⟨⟨hzM, hzJ⟩, h'⟩
  obtain ⟨T₀, hT₀E, hT₀⟩ := exists_tarc_of_isOpen_plane hEo hEc (hME hh.1) (hME hk.1) hhk
  -- last point on `H̄`
  have hkH : k ∉ closure H := fun hc => disjoint_left.mp huv (hclH k hc (hME hk.1)) hk.2
  obtain ⟨x, hxH, C₁, hC₁T, hC₁, hC₁H⟩ :=
    hT₀.symm.first_point isClosed_closure ⟨h, hT₀.left_mem, subset_closure hh⟩ hkH
  have hxE : x ∈ E := hT₀E (hC₁T hC₁.right_mem)
  have hxH' : x ∈ H := hclH x hxH hxE
  -- then first point on `K̄`
  have hxK : x ∉ closure K := fun hc => disjoint_left.mp huv hxH' (hclK x hc hxE).2
  obtain ⟨y, hyK, C₂, hC₂C₁, hC₂, hC₂K⟩ :=
    hC₁.symm.first_point isClosed_closure ⟨k, hC₁.left_mem, subset_closure hk⟩ hxK
  have hyK' : y ∈ K := hclK y hyK (hT₀E (hC₁T (hC₂C₁ hC₂.right_mem)))
  -- the interior of `C₂` misses `M`
  have hint : Disjoint (C₂ \ {x, y}) M := by
    refine disjoint_left.mpr fun z hz hzM => ?_
    have hzC₁ : z ∈ C₁ := hC₂C₁ hz.1
    have hzE : z ∈ E := hT₀E (hC₁T hzC₁)
    have hzJ : z ∉ J := fun h => disjoint_left.mp hEJ hzE h
    rcases hcov ⟨hzM, hzJ⟩ with h' | h'
    · have : z ∈ C₁ ∩ closure H := ⟨hzC₁, subset_closure ⟨⟨hzM, hzJ⟩, h'⟩⟩
      rw [hC₁H] at this
      exact hz.2 (Or.inl this)
    · have : z ∈ C₂ ∩ closure K := ⟨hz.1, subset_closure ⟨⟨hzM, hzJ⟩, h'⟩⟩
      rw [hC₂K] at this
      exact hz.2 (Or.inr this)
  obtain ⟨w, hw⟩ := hC₂.nonempty_diff
  have hwM : w ∉ M := fun h => disjoint_left.mp hint hw h
  have hsub : C₂ \ {x, y} ⊆ connectedComponentIn Mᶜ w :=
    hC₂.isPreconnected_diff.subset_connectedComponentIn hw fun z hz hzM =>
      disjoint_left.mp hint hz hzM
  have hO : IsOpen (connectedComponentIn Mᶜ w) := hM.isOpen_compl.connectedComponentIn
  have hfr : ∀ z ∈ C₂, z ∈ M → z ∈ frontier (connectedComponentIn Mᶜ w) := fun z hz hzM =>
    mem_frontier_of_mem_closure hO (closure_mono hsub (hC₂.subset_closure_diff hz))
      fun h => connectedComponentIn_subset _ _ h hzM
  exact ⟨x, hxH', y, hyK', w, hwM, hfr x hC₂.left_mem hxH'.1.1, hfr y hC₂.right_mem hyK'.1.1⟩

/-- **Case 2, step 4: the arc `AxB`.** In a simple closed curve `C` through `x`, `y ∉ J` such that
every arc of `C` from `x` to `y` meets the closed set `J`, the component of `C − C·J` containing `x`
is an open arc whose ends `A ≠ B` lie on `J`: `C = L + L'` with `L`, `L'` arcs from `A` to `B`,
`L · L' = {A, B}` and `L · J = {A, B}`. -/
theorem exists_theta_arcs {C J : Set Pt} (hC : TSCC C) (hJ : IsClosed J) {x y : Pt} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : x ≠ y) (hxJ : x ∉ J) (hyJ : y ∉ J)
    (hmeet : ∀ P ⊆ C, TArc x y P → (P ∩ J).Nonempty) :
    ∃ A ∈ J, ∃ B ∈ J, ∃ L L' : Set Pt, TArc A B L ∧ TArc A B L' ∧ L ∩ L' = {A, B} ∧
      L ∪ L' = C ∧ L ∩ J = {A, B} := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12, rfl⟩ := hC
  obtain ⟨P₁, P₂, hP₁, hP₂, hPI, hPU⟩ := tscc_split h₁ h₂ h12 hx hy hxy
  have hP₁C : P₁ ⊆ C₁ ∪ C₂ := hPU ▸ subset_union_left
  have hP₂C : P₂ ⊆ C₁ ∪ C₂ := hPU ▸ subset_union_right
  obtain ⟨A, hAJ, Γ₁, Γ₂, hΓ₁, hΓ₂, hΓU, hΓI, hΓJ⟩ :=
    hP₁.first_point_split hJ (hmeet P₁ hP₁C hP₁) hxJ hyJ
  obtain ⟨B, hBJ, Δ₁, Δ₂, hΔ₁, hΔ₂, hΔU, hΔI, hΔJ⟩ :=
    hP₂.first_point_split hJ (hmeet P₂ hP₂C hP₂) hxJ hyJ
  have hAx : A ≠ x := fun e => hxJ (e ▸ hAJ)
  have hAy : A ≠ y := fun e => hyJ (e ▸ hAJ)
  have hBx : B ≠ x := fun e => hxJ (e ▸ hBJ)
  have hBy : B ≠ y := fun e => hyJ (e ▸ hBJ)
  have hΓ₁P : Γ₁ ⊆ P₁ := hΓU ▸ subset_union_left
  have hΓ₂P : Γ₂ ⊆ P₁ := hΓU ▸ subset_union_right
  have hΔ₁P : Δ₁ ⊆ P₂ := hΔU ▸ subset_union_left
  have hΔ₂P : Δ₂ ⊆ P₂ := hΔU ▸ subset_union_right
  have inP : ∀ {z}, z ∈ P₁ → z ∈ P₂ → z = x ∨ z = y := fun h1 h2 => by
    have : _ ∈ P₁ ∩ P₂ := ⟨h1, h2⟩; rwa [hPI] at this
  have yΓ₁ : y ∉ Γ₁ := fun h => hAy.symm (by
    have : y ∈ Γ₁ ∩ Γ₂ := ⟨h, hΓ₂.right_mem⟩; rwa [hΓI] at this)
  have yΔ₁ : y ∉ Δ₁ := fun h => hBy.symm (by
    have : y ∈ Δ₁ ∩ Δ₂ := ⟨h, hΔ₂.right_mem⟩; rwa [hΔI] at this)
  have xΓ₂ : x ∉ Γ₂ := fun h => hAx.symm (by
    have : x ∈ Γ₁ ∩ Γ₂ := ⟨hΓ₁.left_mem, h⟩; rwa [hΓI] at this)
  have xΔ₂ : x ∉ Δ₂ := fun h => hBx.symm (by
    have : x ∈ Δ₁ ∩ Δ₂ := ⟨hΔ₁.left_mem, h⟩; rwa [hΔI] at this)
  have hAB : A ≠ B := fun e => by
    rcases inP (hΓ₁P hΓ₁.right_mem) (e ▸ hΔ₁P hΔ₁.right_mem : A ∈ P₂) with h | h
    exacts [hAx h, hAy h]
  have hL : TArc A B (Γ₁ ∪ Δ₁) := by
    refine hΓ₁.symm.union hΔ₁ (subset_antisymm ?_ ?_)
    · rintro z ⟨h1, h2⟩
      rcases inP (hΓ₁P h1) (hΔ₁P h2) with rfl | rfl
      · rfl
      · exact absurd h1 yΓ₁
    · rintro z rfl; exact ⟨hΓ₁.left_mem, hΔ₁.left_mem⟩
  have hL' : TArc A B (Γ₂ ∪ Δ₂) := by
    refine hΓ₂.union hΔ₂.symm (subset_antisymm ?_ ?_)
    · rintro z ⟨h1, h2⟩
      rcases inP (hΓ₂P h1) (hΔ₂P h2) with rfl | rfl
      · exact absurd h1 xΓ₂
      · rfl
    · rintro z rfl; exact ⟨hΓ₂.right_mem, hΔ₂.right_mem⟩
  refine ⟨A, hAJ, B, hBJ, Γ₁ ∪ Δ₁, Γ₂ ∪ Δ₂, hL, hL', ?_, ?_, ?_⟩
  · apply subset_antisymm
    · rintro z ⟨h1 | h1, h2 | h2⟩
      · left; have : z ∈ Γ₁ ∩ Γ₂ := ⟨h1, h2⟩; rwa [hΓI] at this
      · exfalso
        rcases inP (hΓ₁P h1) (hΔ₂P h2) with rfl | rfl
        exacts [xΔ₂ h2, yΓ₁ h1]
      · exfalso
        rcases inP (hΓ₂P h2) (hΔ₁P h1) with rfl | rfl
        exacts [xΓ₂ h2, yΔ₁ h1]
      · right; have : z ∈ Δ₁ ∩ Δ₂ := ⟨h1, h2⟩; rwa [hΔI] at this
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl hΓ₁.right_mem, Or.inl hΓ₂.left_mem⟩
      · exact ⟨Or.inr hΔ₁.right_mem, Or.inr hΔ₂.left_mem⟩
  · rw [← hPU, ← hΓU, ← hΔU]
    ext z; simp only [mem_union]; tauto
  · rw [union_inter_distrib_right, hΓJ, hΔJ]; rfl

/-- Two arcs from `A` to `B`, one inside `J`, the other meeting `J` only in `A`, `B`, meet only in
`A`, `B`. -/
theorem inter_eq_pair_of_sub {A B : Pt} {J J₁ L : Set Pt} (hJ₁ : TArc A B J₁) (hL : TArc A B L)
    (hJ₁J : J₁ ⊆ J) (hLJ : L ∩ J = {A, B}) : J₁ ∩ L = {A, B} := by
  apply subset_antisymm
  · rintro z ⟨h1, hl⟩; rw [← hLJ]; exact ⟨hl, hJ₁J h1⟩
  · rintro z (rfl | rfl)
    exacts [⟨hJ₁.left_mem, hL.left_mem⟩, ⟨hJ₁.right_mem, hL.right_mem⟩]

/-- **Case 2 of Jones 1949, from cyclicity and semi-local connectedness.** If `M − J` is not
connected (`J` the boundary of the complementary domain `D` of `x`), `M` has a local separating
point. Steps: `J` is a simple closed curve (`whyburn39_corollary1`); if `M = J` every point is a
local separating point; otherwise `M − J = H + K` (cut out by open `u`, `v`), the arc `T` and the
domain `U` (`exists_domain_meeting`), `C = ∂U` a simple closed curve meeting `J`, the arc `AxB`
(`exists_theta_arcs`), the separation of `M − (A + B)` (`theta_separation`), and `A` separates the
connected open set `M − B` (`isLocalSepPoint_of_separation`). Homogeneity and the absence of
points of order 2 are not used. -/
theorem jones49_case2_core {M : Set Pt} [CompactSpace M] [ConnectedSpace M]
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M)
    (h2 : ¬ IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    ∃ A : M, IsLocalSepPoint A := by
  have hMk : IsCompact M := isCompact_iff_compactSpace.mpr ‹_›
  have hMc : IsConnected M := isConnected_iff_connectedSpace.mpr ‹_›
  set D := connectedComponentIn Mᶜ x with hDdef
  set J := frontier D with hJdef
  have hJ : TSCC J := tscc_of_homeomorph_circle (whyburn39_corollary1 hMk hMc hS hcyc hx)
  have hJM : J ⊆ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hMk.isClosed x
  have hDo : IsOpen D := hMk.isClosed.isOpen_compl.connectedComponentIn
  have hDM : Disjoint D M :=
    disjoint_left.mpr fun z hz hzM => connectedComponentIn_subset _ _ hz hzM
  have hDne : D.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hJcl : IsClosed J := isClosed_frontier
  by_cases hMJ : M ⊆ J
  · obtain ⟨p⟩ := (inferInstance : Nonempty M)
    exact ⟨p, isLocalSepPoint_of_open_sub_tscc hJ hJM isOpen_univ (mem_univ p)
      fun z _ => hMJ z.2⟩
  obtain ⟨m₀, hm₀M, hm₀J⟩ := not_subset.mp hMJ
  have himg : Subtype.val '' ((Subtype.val ⁻¹' J)ᶜ : Set M) = M \ J := by
    rw [← preimage_compl, Subtype.image_preimage_coe, diff_eq]
  have hnc : ¬ IsPreconnected (M \ J) := by
    intro hpc
    apply h2
    refine ⟨⟨⟨m₀, hm₀M⟩, hm₀J⟩, ?_⟩
    rw [← IsInducing.subtypeVal.isPreconnected_image, himg]; exact hpc
  simp only [IsPreconnected, not_forall, exists_prop] at hnc
  obtain ⟨u, v, hu, hv, hcov, ⟨h, hh⟩, ⟨k, hk⟩, huv⟩ := hnc
  rw [not_nonempty_iff_eq_empty] at huv
  have huv' : Disjoint (M \ J ∩ u) v := by
    rw [disjoint_iff_inter_eq_empty, inter_assoc]; exact huv
  -- the side `E` of `J` containing `M − J`
  set E := connectedComponentIn Jᶜ m₀
  have hEo : IsOpen E := hJcl.isOpen_compl.connectedComponentIn
  have hEc : IsConnected E := isConnected_connectedComponentIn_iff.mpr hm₀J
  have hEJ : Disjoint E J :=
    disjoint_left.mpr fun z hz hzJ => connectedComponentIn_subset _ _ hz hzJ
  have hME : M \ J ⊆ E := fun z hz =>
    mem_cc_of_not_mem_domain hJ hDo isPreconnected_connectedComponentIn hDne rfl
      (fun h => disjoint_left.mp hDM h hz.1) hz.2 (fun h => disjoint_left.mp hDM h hm₀M) hm₀J
  obtain ⟨x₁, hx₁, y₁, hy₁, w, hwM, hx₁U, hy₁U⟩ :=
    exists_domain_meeting hMk.isClosed hEo hEc hEJ hME hu hv hcov huv' hh hk
  set U := connectedComponentIn Mᶜ w with hUdef
  set C := frontier U with hCdef
  have hC : TSCC C := tscc_of_homeomorph_circle (whyburn39_corollary1 hMk hMc hS hcyc hwM)
  have hCM : C ⊆ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hMk.isClosed w
  have hx₁y₁ : x₁ ≠ y₁ := fun e => disjoint_left.mp huv' hx₁ (e ▸ hy₁.2)
  have hmeet : ∀ P ⊆ C, TArc x₁ y₁ P → (P ∩ J).Nonempty := by
    intro P hPC hP
    by_contra hPJ
    rw [not_nonempty_iff_eq_empty] at hPJ
    have hPMJ : P ⊆ M \ J := fun z hz =>
      ⟨hCM (hPC hz), fun hzJ => (hPJ ▸ ⟨hz, hzJ⟩ : z ∈ (∅ : Set Pt))⟩
    obtain ⟨z, hzP, hzu, hzv⟩ := hP.isPreconnected u v hu hv (hPMJ.trans hcov)
      ⟨x₁, hP.left_mem, hx₁.2⟩ ⟨y₁, hP.right_mem, hy₁.2⟩
    exact disjoint_left.mp huv' ⟨hPMJ hzP, hzu⟩ hzv
  obtain ⟨A, hAJ, B, hBJ, L, L', hL, hL', hLL', hLU, hLJ⟩ :=
    exists_theta_arcs hC hJcl hx₁U hy₁U hx₁y₁ hx₁.1.2 hy₁.1.2 hmeet
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12, hJeq⟩ := hJ
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJI, hJU⟩ :=
    tscc_split h₁ h₂ h12 (hJeq ▸ hAJ) (hJeq ▸ hBJ) hL.ne
  rw [← hJeq] at hJU
  have hJ₁J : J₁ ⊆ J := hJU ▸ subset_union_left
  have hJ₂J : J₂ ⊆ J := hJU ▸ subset_union_right
  have hUo : IsOpen U := hMk.isClosed.isOpen_compl.connectedComponentIn
  have hUM : Disjoint U M :=
    disjoint_left.mpr fun z hz hzM => connectedComponentIn_subset _ _ hz hzM
  have hUD : Disjoint U D := by
    rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    rintro ⟨z, hzU, hzD⟩
    have hUD : U = D := by
      rw [hUdef, connectedComponentIn_eq hzU, hDdef, connectedComponentIn_eq hzD]
    exact hx₁.1.2 (show x₁ ∈ frontier D from hUD ▸ hx₁U)
  obtain ⟨X₁, X₂, hXU, hX₁, hX₂, hd1, hd2⟩ :=
    theta_separation hJ₁ hJ₂ hL hL' hJI (inter_eq_pair_of_sub hJ₁ hL hJ₁J hLJ)
      (inter_eq_pair_of_sub hJ₂ hL hJ₂J hLJ) hLL'
      (union_subset (union_subset (hJ₁J.trans hJM) (hJ₂J.trans hJM))
        ((hLU ▸ subset_union_left : L ⊆ C).trans hCM))
      hDo isPreconnected_connectedComponentIn hDne hJU.symm hDM hUo
      isPreconnected_connectedComponentIn ⟨w, mem_connectedComponentIn hwM⟩ hLU.symm hUM hUD
  refine ⟨⟨A, hJM hAJ⟩, isLocalSepPoint_of_separation (b := ⟨B, hJM hBJ⟩)
    (fun e => hL.ne (congrArg Subtype.val e)) (hcyc _) hXU hX₁ hX₂ hd1 hd2⟩

end HPC.Jones
