import HPC.Moore.FA

/-!
# Moore, F.A. (1916), §6: a toolkit of arcs in a Hausdorff space (batch 138)

Moore's arguments in §6 manipulate arcs constantly: sub-arcs, first points, gluing two arcs, and
extracting an arc from the union of two arcs that meet. Batch 137 identified Moore arcs with
embedded copies of `[0, 1]` (`isArc_iff`). Here that topological notion (`Gen.TArc`) is developed
in an arbitrary Hausdorff space, independently of Moore's regions; the bridge back to Moore's
`IsArc` is `isArc_iff_tarc` (`HPC/Moore/Sec6Plane.lean`).

| fact | here |
|---|---|
| reversal, compactness, closedness | `TArc.symm`, `TArc.isCompact`, `TArc.isClosed` |
| sub-arcs `f '' [s, t]` | `TArc.image_Icc`, `TArc.exists_sub` |
| the open arc is connected, nonempty, dense in the arc | `TArc.isPreconnected_diff`, `TArc.nonempty_diff`, `TArc.subset_closure_diff` |
| first point on a closed set | `TArc.first_point` |
| gluing (two arcs `PQ`, `QR` meeting only in `Q`) | `TArc.union` |
| an arc `PR` inside the union of two meeting arcs | `TArc.join` |
| a connected set missing the boundary of `U` lies in `U` or in `S − U'` | `conn_sub_of_frontier`, `conn_sub_ext_of_frontier` |
-/

namespace HPC.Moore

open Set Topology unitInterval

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- An arc from `A` to `B` in the topological sense: the image of an embedding of `[0, 1]`
sending `0 ↦ A`, `1 ↦ B`. -/
def TArc (A B : X) (C : Set X) : Prop :=
  A ≠ B ∧ ∃ f : I → X, IsEmbedding f ∧ range f = C ∧ f 0 = A ∧ f 1 = B

/-- A simple closed curve in the topological sense: two arcs with only their endpoints in
common. -/
def TSCC (J : Set X) : Prop :=
  ∃ A B : X, ∃ C₁ C₂ : Set X, TArc A B C₁ ∧ TArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ J = C₁ ∪ C₂

/-! ### Connected sets and boundaries -/

/-- A preconnected set that misses the boundary of `U` and meets `U` lies in `U`. -/
theorem conn_sub_of_frontier {C U : Set X} (hC : IsPreconnected C) (hd : Disjoint C (frontier U))
    (hne : (C ∩ U).Nonempty) : C ⊆ U := by
  have hsub : C ⊆ interior U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases h : x ∈ closure U
    · left
      by_contra hi
      exact disjoint_left.mp hd hx ⟨h, hi⟩
    · exact Or.inr h
  obtain ⟨x, hxC, hxU⟩ := hne
  have hxi : x ∈ interior U := by
    rcases hsub hxC with h | h
    · exact h
    · exact absurd (subset_closure hxU) h
  exact (hC.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure) hsub ⟨x, hxC, hxi⟩).trans
    interior_subset

/-- A preconnected set that misses the boundary of `U` and meets `S − U'` lies in `S − U'`. -/
theorem conn_sub_ext_of_frontier {C U : Set X} (hC : IsPreconnected C)
    (hd : Disjoint C (frontier U)) (hne : (C ∩ (closure U)ᶜ).Nonempty) : C ⊆ (closure U)ᶜ := by
  refine conn_sub_of_frontier hC (hd.mono_right ?_) hne
  rw [frontier_compl]
  exact frontier_closure_subset

/-! ### Basic facts -/

theorem TArc.ne {A B : X} {C : Set X} (h : TArc A B C) : A ≠ B := h.1

theorem TArc.left_mem {A B : X} {C : Set X} (h : TArc A B C) : A ∈ C := by
  obtain ⟨-, f, -, rfl, rfl, -⟩ := h; exact mem_range_self _

theorem TArc.right_mem {A B : X} {C : Set X} (h : TArc A B C) : B ∈ C := by
  obtain ⟨-, f, -, rfl, -, rfl⟩ := h; exact mem_range_self _

theorem TArc.isCompact {A B : X} {C : Set X} (h : TArc A B C) : IsCompact C := by
  obtain ⟨-, f, hf, rfl, -⟩ := h; exact isCompact_range hf.continuous

theorem TArc.isPreconnected {A B : X} {C : Set X} (h : TArc A B C) : IsPreconnected C := by
  obtain ⟨-, f, hf, rfl, -⟩ := h; exact isPreconnected_range hf.continuous

variable [T2Space X]

theorem TArc.isClosed {A B : X} {C : Set X} (h : TArc A B C) : IsClosed C := h.isCompact.isClosed

theorem TArc.of_inj {f : I → X} (hf : Continuous f) (hinj : Function.Injective f) :
    TArc (f 0) (f 1) (range f) := by
  refine ⟨fun h => ?_, f, (hf.isClosedEmbedding hinj).isEmbedding, rfl, rfl, rfl⟩
  have := congrArg Subtype.val (hinj h)
  simp at this

theorem TArc.symm {A B : X} {C : Set X} (h : TArc A B C) : TArc B A C := by
  obtain ⟨hAB, f, hf, rfl, rfl, rfl⟩ := h
  have := TArc.of_inj (hf.continuous.comp continuous_symm)
    (hf.injective.comp symm_involutive.injective)
  simpa [range_comp, symm_involutive.surjective.range_eq] using this

/-! ### Sub-arcs -/

/-- The affine map `[0, 1] → [s, t]`. -/
def affI (s t : I) (hst : s ≤ t) (u : I) : I :=
  ⟨s + u * (t - s), by
    have h1 : (0 : ℝ) ≤ u * (t - s) := mul_nonneg u.2.1 (sub_nonneg.mpr hst)
    have h2 : (u : ℝ) * (t - s) ≤ t - s := mul_le_of_le_one_left (sub_nonneg.mpr hst) u.2.2
    exact ⟨by linarith [s.2.1], by linarith [t.2.2]⟩⟩

theorem continuous_affI (s t : I) (hst : s ≤ t) : Continuous (affI s t hst) :=
  Continuous.subtype_mk (by fun_prop) _

theorem affI_injective {s t : I} (hst : s < t) : Function.Injective (affI s t hst.le) := by
  intro u v h
  have h' := congrArg Subtype.val h
  simp only [affI] at h'
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  exact Subtype.ext (mul_right_cancel₀ hts.ne' (by linarith))

theorem range_affI {s t : I} (hst : s < t) : range (affI s t hst.le) = Icc s t := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    have h2 : (u : ℝ) * (t - s) ≤ t - s := mul_le_of_le_one_left (sub_nonneg.mpr hst.le) u.2.2
    have h1 : (0 : ℝ) ≤ u * (t - s) := mul_nonneg u.2.1 (sub_nonneg.mpr hst.le)
    constructor
    · show (s : ℝ) ≤ s + u * (t - s); linarith
    · show (s : ℝ) + u * (t - s) ≤ t; linarith
  · rintro ⟨hsv, hvt⟩
    have hsv' : (s : ℝ) ≤ v := hsv
    have hvt' : (v : ℝ) ≤ t := hvt
    have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
    refine ⟨⟨(v - s) / (t - s), div_nonneg (by linarith) hts.le,
      (div_le_one hts).mpr (by linarith)⟩, Subtype.ext ?_⟩
    simp only [affI]
    field_simp
    ring

theorem affI_zero (s t : I) (hst : s ≤ t) : affI s t hst 0 = s := by
  apply Subtype.ext; simp [affI]

theorem affI_one (s t : I) (hst : s ≤ t) : affI s t hst 1 = t := by
  apply Subtype.ext; simp [affI]

/-- The image of a nondegenerate interval under an embedding of `[0, 1]` is an arc. -/
theorem TArc.image_Icc {f : I → X} (hf : IsEmbedding f) {s t : I} (hst : s < t) :
    TArc (f s) (f t) (f '' Icc s t) := by
  have := TArc.of_inj (hf.continuous.comp (continuous_affI s t hst.le))
    (hf.injective.comp (affI_injective hst))
  simpa [range_comp, range_affI hst, affI_zero, affI_one] using this

theorem TArc.image_uIcc {f : I → X} (hf : IsEmbedding f) {s t : I} (hst : s ≠ t) :
    TArc (f s) (f t) (f '' uIcc s t) := by
  rcases lt_or_gt_of_ne hst with h | h
  · rw [uIcc_of_le h.le]; exact TArc.image_Icc hf h
  · rw [uIcc_of_ge h.le]; exact (TArc.image_Icc hf h).symm

/-- Two distinct points of an arc bound a sub-arc. -/
theorem TArc.exists_sub {A B P Q : X} {C : Set X} (h : TArc A B C) (hP : P ∈ C) (hQ : Q ∈ C)
    (hPQ : P ≠ Q) : ∃ C' ⊆ C, TArc P Q C' := by
  obtain ⟨-, f, hf, rfl, -, -⟩ := h
  obtain ⟨p, rfl⟩ := hP
  obtain ⟨q, rfl⟩ := hQ
  exact ⟨_, image_subset_range _ _, TArc.image_uIcc hf fun e => hPQ (e ▸ rfl)⟩

/-! ### The open arc -/

theorem closure_Ioo_unitInterval : closure (Ioo (0 : I) 1) = univ := by
  rw [closure_Ioo (by simp)]
  ext x; simp only [mem_Icc, mem_univ, iff_true]; exact ⟨nonneg', le_one'⟩

omit [T2Space X] in
theorem TArc.diff_eq {f : I → X} (hf : IsEmbedding f) :
    range f \ {f 0, f 1} = f '' Ioo 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨t, ⟨lt_of_le_of_ne nonneg' fun e => hz.1 (by rw [← e]),
      lt_of_le_of_ne le_one' fun e => hz.2 (by rw [e])⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => h0.ne' (hf.injective e), fun e => h1.ne (hf.injective e)⟩

omit [T2Space X] in
theorem TArc.isPreconnected_diff {A B : X} {C : Set X} (h : TArc A B C) :
    IsPreconnected (C \ {A, B}) := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  rw [TArc.diff_eq hf]
  exact isPreconnected_Ioo.image _ hf.continuous.continuousOn

omit [T2Space X] in
theorem TArc.nonempty_diff {A B : X} {C : Set X} (h : TArc A B C) : (C \ {A, B}).Nonempty := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  rw [TArc.diff_eq hf]
  refine ⟨f ⟨1 / 2, by norm_num, by norm_num⟩, mem_image_of_mem _ ⟨?_, ?_⟩⟩
  · show (0 : ℝ) < 1 / 2; norm_num
  · show (1 / 2 : ℝ) < 1; norm_num

omit [T2Space X] in
theorem TArc.subset_closure_diff {A B : X} {C : Set X} (h : TArc A B C) :
    C ⊆ closure (C \ {A, B}) := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  rw [TArc.diff_eq hf]
  rintro _ ⟨t, rfl⟩
  have : t ∈ closure (Ioo (0 : I) 1) := by rw [closure_Ioo_unitInterval]; trivial
  exact image_closure_subset_closure_image hf.continuous (mem_image_of_mem f this)

omit [T2Space X] in
theorem TArc.isPreconnected_diff_right {A B : X} {C : Set X} (h : TArc A B C) :
    IsPreconnected (C \ {B}) := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  have : range f \ {f 1} = f '' Ico 0 1 := by
    ext z
    simp only [mem_diff, mem_range, mem_singleton_iff, mem_image, mem_Ico]
    constructor
    · rintro ⟨⟨t, rfl⟩, h1⟩
      exact ⟨t, ⟨nonneg', lt_of_le_of_ne le_one' fun e => h1 (by rw [e])⟩, rfl⟩
    · rintro ⟨t, ⟨-, h1⟩, rfl⟩
      exact ⟨⟨t, rfl⟩, fun e => h1.ne (hf.injective e)⟩
  rw [this]
  exact isPreconnected_Ico.image _ hf.continuous.continuousOn

omit [T2Space X] in
theorem TArc.mem_closure_diff_right {A B : X} {C : Set X} (h : TArc A B C) :
    B ∈ closure (C \ {B}) :=
  closure_mono (diff_subset_diff_right (by simp)) (h.subset_closure_diff h.right_mem)

/-! ### First points, gluing, joining -/

/-- **The first point** of the arc `AB` (from `A`) on a closed set `Z` not containing `A`: a point
`P ∈ Z` and a sub-arc `AP` meeting `Z` only in `P`. -/
theorem TArc.first_point {A B : X} {C Z : Set X} (h : TArc A B C) (hZ : IsClosed Z)
    (hne : (C ∩ Z).Nonempty) (hA : A ∉ Z) :
    ∃ P ∈ Z, ∃ C' ⊆ C, TArc A P C' ∧ C' ∩ Z = {P} := by
  obtain ⟨-, f, hf, rfl, rfl, -⟩ := h
  have hT : IsClosed (f ⁻¹' Z) := hZ.preimage hf.continuous
  have hTne : (f ⁻¹' Z).Nonempty := by
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hne; exact ⟨t, ht⟩
  set t := sInf (f ⁻¹' Z)
  have htT : t ∈ f ⁻¹' Z := hT.csInf_mem hTne ⟨0, fun _ _ => nonneg'⟩
  have ht0 : 0 < t := lt_of_le_of_ne nonneg' fun e => hA (e ▸ htT)
  refine ⟨f t, htT, f '' Icc 0 t, image_subset_range _ _, TArc.image_Icc hf ht0, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_image, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨u, ⟨-, hut⟩, rfl⟩, hu⟩
    rw [le_antisymm hut (csInf_le ⟨0, fun _ _ => nonneg'⟩ hu)]
  · rintro rfl
    exact ⟨⟨t, ⟨nonneg', le_rfl⟩, rfl⟩, htT⟩

/-- **Gluing.** Two arcs `PQ`, `QR` meeting only in `Q` form an arc `PR`. -/
theorem TArc.union {P Q R : X} {D E : Set X} (hD : TArc P Q D) (hE : TArc Q R E)
    (hDE : D ∩ E = {Q}) : TArc P R (D ∪ E) := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hD
  obtain ⟨-, g, hg, rfl, hg0, rfl⟩ := hE
  let γ : Path (f 0) (f 1) := ⟨⟨f, hf.continuous⟩, rfl, rfl⟩
  let δ : Path (f 1) (g 1) := ⟨⟨g, hg.continuous⟩, hg0, rfl⟩
  have hinj : Function.Injective (γ.trans δ) := by
    have key : ∀ u v : I, (u : ℝ) ≤ 1 / 2 → ¬ (v : ℝ) ≤ 1 / 2 → (γ.trans δ) u = (γ.trans δ) v →
        False := by
      intro u v hu hv huv
      rw [Path.trans_apply, Path.trans_apply, dif_pos hu, dif_neg hv] at huv
      have key2 : ∀ a b : I, (a : ℝ) = 2 * u → (b : ℝ) = 2 * v - 1 → f a = g b → False := by
        intro a b ha hb hab
        have hmem : f a ∈ range f ∩ range g := ⟨mem_range_self _, ⟨_, hab.symm⟩⟩
        rw [hDE, mem_singleton_iff] at hmem
        have h1 : (a : ℝ) = 1 := congrArg Subtype.val (hf.injective hmem)
        have h3 : (b : ℝ) = 0 :=
          congrArg Subtype.val (hg.injective ((hab.symm.trans hmem).trans hg0.symm))
        linarith
      exact key2 _ _ rfl rfl huv
    intro u v huv
    by_cases hu : (u : ℝ) ≤ 1 / 2 <;> by_cases hv : (v : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, Path.trans_apply, dif_pos hu, dif_pos hv] at huv
      have := congrArg Subtype.val (hf.injective huv)
      exact Subtype.ext (by simp at this; linarith)
    · exact (key u v hu hv huv).elim
    · exact (key v u hv hu huv.symm).elim
    · rw [Path.trans_apply, Path.trans_apply, dif_neg hu, dif_neg hv] at huv
      have := congrArg Subtype.val (hg.injective huv)
      exact Subtype.ext (by simp at this; linarith)
  have := TArc.of_inj (γ.trans δ).continuous hinj
  rw [Path.trans_range] at this
  simpa using this

/-- **Joining.** If the arcs `PQ` and `RT` meet and `P ≠ R`, their union contains an arc
`PR`. -/
theorem TArc.join {P Q R T : X} {α β : Set X} (hα : TArc P Q α) (hβ : TArc R T β)
    (hne : (α ∩ β).Nonempty) (hPR : P ≠ R) : ∃ γ ⊆ α ∪ β, TArc P R γ := by
  by_cases hPβ : P ∈ β
  · obtain ⟨γ, hγ, hγa⟩ := hβ.exists_sub hPβ hβ.left_mem hPR
    exact ⟨γ, hγ.trans subset_union_right, hγa⟩
  obtain ⟨M, hMβ, α', hα'α, hα', hα'β⟩ := hα.first_point hβ.isClosed hne hPβ
  by_cases hMR : M = R
  · subst hMR; exact ⟨α', hα'α.trans subset_union_left, hα'⟩
  obtain ⟨β', hβ'β, hβ'⟩ := hβ.exists_sub hMβ hβ.left_mem hMR
  refine ⟨α' ∪ β', union_subset_union hα'α hβ'β, hα'.union hβ' ?_⟩
  apply subset_antisymm
  · exact (inter_subset_inter_right _ hβ'β).trans hα'β.subset
  · rintro _ rfl; exact ⟨hα'.right_mem, hβ'.left_mem⟩

end Gen

end HPC.Moore
