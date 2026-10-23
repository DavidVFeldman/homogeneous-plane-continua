import HPC.HO16.Lemma6

/-!
# Batch 194, §4: simple folds exist (H–O pp. 185–186)

The construction of commission 194, §4: refine a decomposition of `G` so that `G₁, G₂, G₃` are
unions of edges and the points of `∂G₁ ∪ ∂G₃` are vertices (§3.0), subdivide every edge at its
midpoint, and lift the edges of `Gᵢ` to `E × ℝ` by heights at the vertices:
`h₁ = 1` on `∂G₁` and `0` elsewhere, height `1` for `F₂`, `h₃ = 1` on `∂G₃` and `2` elsewhere.

General tools: `exists_midpoint_subdivision` and the lifting lemmas `liftG_*` (the lift of a
decomposition by vertex heights is a PL graph on which `Prod.fst` is injective).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Midpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem midpoint_eq_lineMap_half (a b : E) :
    midpoint ℝ a b = AffineMap.lineMap a b (1 / 2 : ℝ) := by
  rw [midpoint, one_div, invOf_eq_inv]

theorem right_not_mem_segment_left_mid {a b : E} (h : a ≠ b) :
    b ∉ segment ℝ a (midpoint ℝ a b) := by
  intro hb
  have hinj : Function.Injective (AffineMap.lineMap a b : ℝ → E) :=
    AffineMap.lineMap_injective ℝ h
  have hs : segment ℝ a (midpoint ℝ a b) = AffineMap.lineMap a b '' uIcc (0 : ℝ) (1 / 2) := by
    rw [← Subdiv.segment_lineMap, AffineMap.lineMap_apply_zero, midpoint_eq_lineMap_half]
  rw [hs] at hb
  obtain ⟨u, hu, he⟩ := hb
  rw [hinj (he.trans (AffineMap.lineMap_apply_one a b).symm), uIcc_of_le (by norm_num)] at hu
  norm_num at hu

theorem left_not_mem_segment_mid_right {a b : E} (h : a ≠ b) :
    a ∉ segment ℝ (midpoint ℝ a b) b := by
  intro ha
  have hinj : Function.Injective (AffineMap.lineMap a b : ℝ → E) :=
    AffineMap.lineMap_injective ℝ h
  have hs : segment ℝ (midpoint ℝ a b) b = AffineMap.lineMap a b '' uIcc (1 / 2 : ℝ) 1 := by
    rw [← Subdiv.segment_lineMap, AffineMap.lineMap_apply_one, midpoint_eq_lineMap_half]
  rw [hs] at ha
  obtain ⟨u, hu, he⟩ := ha
  rw [hinj (he.trans (AffineMap.lineMap_apply_zero a b).symm), uIcc_of_le (by norm_num)] at hu
  norm_num at hu

/-- Facts about the two halves of an edge. -/
theorem half_facts {s σ : E × E} (hs : s.1 ≠ s.2)
    (hσ : σ = (s.1, midpoint ℝ s.1 s.2) ∨ σ = (midpoint ℝ s.1 s.2, s.2)) :
    σ.1 ≠ σ.2 ∧ segment ℝ σ.1 σ.2 ⊆ segment ℝ s.1 s.2 ∧
      (∀ v, (v = s.1 ∨ v = s.2) → v ∈ segment ℝ σ.1 σ.2 → v = σ.1 ∨ v = σ.2) ∧
      (σ.1 = midpoint ℝ s.1 s.2 ∨ σ.2 = midpoint ℝ s.1 s.2) := by
  have hm : midpoint ℝ s.1 s.2 ∈ segment ℝ s.1 s.2 := midpoint_mem_segment _ _
  have hma : midpoint ℝ s.1 s.2 ≠ s.1 := fun h => hs ((midpoint_eq_left_iff ℝ).1 h)
  have hmb : midpoint ℝ s.1 s.2 ≠ s.2 := fun h => hs ((midpoint_eq_right_iff ℝ).1 h)
  rcases hσ with rfl | rfl
  · refine ⟨hma.symm, (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hm, ?_,
      Or.inr rfl⟩
    rintro v (rfl | rfl) hv
    · exact Or.inl rfl
    · exact absurd hv (right_not_mem_segment_left_mid hs)
  · refine ⟨hmb, (convex_segment _ _).segment_subset hm (right_mem_segment ℝ _ _), ?_,
      Or.inl rfl⟩
    rintro v (rfl | rfl) hv
    · exact absurd hv (left_not_mem_segment_mid_right hs)
    · exact Or.inr rfl

/-- **Midpoint subdivision** of a decomposition. -/
theorem exists_midpoint_subdivision {S₀ : Finset (E × E)} (hne : ∀ s ∈ S₀, s.1 ≠ s.2)
    (hdis : PairwiseEndpoints S₀) :
    ∃ S : Finset (E × E), (∀ σ ∈ S, σ.1 ≠ σ.2) ∧ PairwiseEndpoints S ∧
      (∀ σ ∈ S, ∃ s ∈ S₀, segment ℝ σ.1 σ.2 ⊆ segment ℝ s.1 s.2) ∧
      (∀ s ∈ S₀, ∀ x ∈ segment ℝ s.1 s.2, ∃ σ ∈ S, x ∈ segment ℝ σ.1 σ.2 ∧
        segment ℝ σ.1 σ.2 ⊆ segment ℝ s.1 s.2) ∧
      (∀ s ∈ S₀, ∃ σ ∈ S, σ.1 = s.1) ∧ (∀ s ∈ S₀, ∃ σ ∈ S, σ.2 = s.2) ∧
      (∀ σ ∈ S, ∃ w, (w = σ.1 ∨ w = σ.2) ∧ ∀ s ∈ S₀, w ≠ s.1 ∧ w ≠ s.2) := by
  classical
  set S := S₀.biUnion (fun s => {(s.1, midpoint ℝ s.1 s.2), (midpoint ℝ s.1 s.2, s.2)})
  have hmem : ∀ σ, σ ∈ S ↔ ∃ s ∈ S₀,
      σ = (s.1, midpoint ℝ s.1 s.2) ∨ σ = (midpoint ℝ s.1 s.2, s.2) := by
    intro σ
    simp only [S, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  have hmidnv : ∀ s ∈ S₀, ∀ s'' ∈ S₀,
      midpoint ℝ s.1 s.2 ≠ s''.1 ∧ midpoint ℝ s.1 s.2 ≠ s''.2 := by
    intro s hs s'' hs''
    have hm : midpoint ℝ s.1 s.2 ∈ segment ℝ s.1 s.2 := midpoint_mem_segment _ _
    have hma : midpoint ℝ s.1 s.2 ≠ s.1 := fun h => hne s hs ((midpoint_eq_left_iff ℝ).1 h)
    have hmb : midpoint ℝ s.1 s.2 ≠ s.2 := fun h => hne s hs ((midpoint_eq_right_iff ℝ).1 h)
    by_cases hss : s = s''
    · subst hss; exact ⟨hma, hmb⟩
    · have key : ∀ w ∈ segment ℝ s''.1 s''.2, midpoint ℝ s.1 s.2 ≠ w := by
        intro w hw hmw
        rcases (hdis s hs s'' hs'' hss ⟨hm, hmw ▸ hw⟩).1 with h | h
        · exact hma h
        · exact hmb h
      exact ⟨key _ (left_mem_segment ℝ _ _), key _ (right_mem_segment ℝ _ _)⟩
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨s, hs, h⟩ := (hmem σ).1 hσ
    exact (half_facts (hne s hs) h).1
  · intro σ hσ σ' hσ' hne' x ⟨hx, hx'⟩
    obtain ⟨s, hs, h⟩ := (hmem σ).1 hσ
    obtain ⟨s', hs', h'⟩ := (hmem σ').1 hσ'
    obtain ⟨-, hsub, hend, -⟩ := half_facts (hne s hs) h
    obtain ⟨-, hsub', hend', -⟩ := half_facts (hne s' hs') h'
    by_cases hss : s = s'
    · subst hss
      -- the two different halves of `s` meet only at the midpoint
      have hm : midpoint ℝ s.1 s.2 ∈ segment ℝ s.1 s.2 := midpoint_mem_segment _ _
      have hma : midpoint ℝ s.1 s.2 ≠ s.1 :=
        fun h => hne s hs ((midpoint_eq_left_iff ℝ).1 h)
      have hmb : midpoint ℝ s.1 s.2 ≠ s.2 :=
        fun h => hne s hs ((midpoint_eq_right_iff ℝ).1 h)
      rcases h with rfl | rfl <;> rcases h' with h' | h' <;> subst h'
      · exact absurd rfl hne'
      · have : x = midpoint ℝ s.1 s.2 :=
          eq_of_mem_segment_halves hm hma hmb (by rwa [segment_symm] at hx) hx'
        subst this
        exact ⟨Or.inr rfl, Or.inl rfl⟩
      · have : x = midpoint ℝ s.1 s.2 :=
          eq_of_mem_segment_halves hm hma hmb (by rwa [segment_symm] at hx') hx
        subst this
        exact ⟨Or.inl rfl, Or.inr rfl⟩
      · exact absurd rfl hne'
    · obtain ⟨h1, h2⟩ := hdis s hs s' hs' hss ⟨hsub hx, hsub' hx'⟩
      exact ⟨hend x h1 hx, hend' x h2 hx'⟩
  · intro σ hσ
    obtain ⟨s, hs, h⟩ := (hmem σ).1 hσ
    exact ⟨s, hs, (half_facts (hne s hs) h).2.1⟩
  · intro s hs x hx
    have hm : midpoint ℝ s.1 s.2 ∈ segment ℝ s.1 s.2 := midpoint_mem_segment _ _
    rcases segment_subset_union_of_mem hm hx with h | h
    · refine ⟨(s.1, midpoint ℝ s.1 s.2), (hmem _).2 ⟨s, hs, Or.inl rfl⟩, ?_,
        (half_facts (hne s hs) (Or.inl rfl)).2.1⟩
      rw [segment_symm]; exact h
    · exact ⟨(midpoint ℝ s.1 s.2, s.2), (hmem _).2 ⟨s, hs, Or.inr rfl⟩, h,
        (half_facts (hne s hs) (Or.inr rfl)).2.1⟩
  · intro s hs
    exact ⟨(s.1, midpoint ℝ s.1 s.2), (hmem _).2 ⟨s, hs, Or.inl rfl⟩, rfl⟩
  · intro s hs
    exact ⟨(midpoint ℝ s.1 s.2, s.2), (hmem _).2 ⟨s, hs, Or.inr rfl⟩, rfl⟩
  · intro σ hσ
    obtain ⟨s, hs, h⟩ := (hmem σ).1 hσ
    rcases (half_facts (hne s hs) h).2.2.2 with h' | h'
    · exact ⟨σ.1, Or.inl rfl, fun s'' hs'' => h' ▸ hmidnv s hs s'' hs''⟩
    · exact ⟨σ.2, Or.inr rfl, fun s'' hs'' => h' ▸ hmidnv s hs s'' hs''⟩

end Midpoint

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lift of a family of edges by vertex heights `h`. -/
def liftG (S : Finset (E × E)) (h : E → ℝ) : Set (E × ℝ) :=
  ⋃ s ∈ S, segment ℝ (s.1, h s.1) (s.2, h s.2)

theorem lineMap_real (α β u : ℝ) : AffineMap.lineMap α β u = (1 - u) * α + u * β := by
  rw [AffineMap.lineMap_apply_module]; simp [smul_eq_mul]

theorem lineMap_prod (a b : E) (α β u : ℝ) :
    AffineMap.lineMap (a, α) (b, β) u = (AffineMap.lineMap a b u, AffineMap.lineMap α β u) := by
  ext <;> simp [AffineMap.lineMap_apply_module]

theorem mem_lift_segment {a b : E} {α β : ℝ} {x : E × ℝ} :
    x ∈ segment ℝ (a, α) (b, β) ↔
      ∃ u ∈ Icc (0 : ℝ) 1, x = (AffineMap.lineMap a b u, AffineMap.lineMap α β u) := by
  rw [Subdiv.mem_segment_iff_lineMap]
  simp only [lineMap_prod]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

theorem fst_mem_of_mem_lift_segment {a b : E} {α β : ℝ} {x : E × ℝ}
    (hx : x ∈ segment ℝ (a, α) (b, β)) : x.1 ∈ segment ℝ a b := by
  obtain ⟨u, hu, rfl⟩ := mem_lift_segment.1 hx
  exact Subdiv.mem_segment_iff_lineMap.2 ⟨u, hu, rfl⟩

theorem lift_point_left {a b : E} (hab : a ≠ b) {α β : ℝ} {x : E × ℝ}
    (hx : x ∈ segment ℝ (a, α) (b, β)) (h1 : x.1 = a) : x = (a, α) := by
  obtain ⟨u, -, rfl⟩ := mem_lift_segment.1 hx
  have hu : u = 0 := AffineMap.lineMap_injective ℝ hab (h1.trans (AffineMap.lineMap_apply_zero a b).symm)
  subst hu
  simp

theorem lift_point_right {a b : E} (hab : a ≠ b) {α β : ℝ} {x : E × ℝ}
    (hx : x ∈ segment ℝ (a, α) (b, β)) (h1 : x.1 = b) : x = (b, β) := by
  obtain ⟨u, -, rfl⟩ := mem_lift_segment.1 hx
  have hu : u = 1 := AffineMap.lineMap_injective ℝ hab (h1.trans (AffineMap.lineMap_apply_one a b).symm)
  subst hu
  simp

theorem image_fst_lift_segment (a b : E) (α β : ℝ) :
    Prod.fst '' segment ℝ (a, α) (b, β) = segment ℝ a b :=
  image_segment ℝ (LinearMap.fst ℝ E ℝ).toAffineMap (a, α) (b, β)

/-- Two lifted edges over one point: the point is a common vertex or the edges coincide. -/
theorem lift_inter_cases {S S₁ S₂ : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2)
    (hdis : PairwiseEndpoints S) (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (h k : E → ℝ) {x : E × ℝ}
    (hx : x ∈ liftG S₁ h) (hx' : x ∈ liftG S₂ k) :
    ∃ s ∈ S₁, ∃ u ∈ Icc (0 : ℝ) 1, x.1 = AffineMap.lineMap s.1 s.2 u ∧
      x.2 = AffineMap.lineMap (h s.1) (h s.2) u ∧
      ((u = 0 ∧ h s.1 = k s.1) ∨ (u = 1 ∧ h s.2 = k s.2) ∨
        (s ∈ S₂ ∧ AffineMap.lineMap (h s.1) (h s.2) u = AffineMap.lineMap (k s.1) (k s.2) u)) := by
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
  obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.1 hx'
  have hxs0 := hxs
  obtain ⟨u, hu, rfl⟩ := mem_lift_segment.1 hxs
  refine ⟨s, hs, u, hu, rfl, rfl, ?_⟩
  have hab := hne s (h₁ hs)
  have hinj : Function.Injective (AffineMap.lineMap s.1 s.2 : ℝ → E) :=
    AffineMap.lineMap_injective ℝ hab
  by_cases hss : s = s'
  · subst hss
    obtain ⟨u', -, he⟩ := mem_lift_segment.1 hxs'
    have h1 : u = u' := hinj (congrArg Prod.fst he)
    subst h1
    exact Or.inr (Or.inr ⟨hs', congrArg Prod.snd he⟩)
  · have hy := hdis s (h₁ hs) s' (h₂ hs') hss
      ⟨fst_mem_of_mem_lift_segment hxs0, fst_mem_of_mem_lift_segment hxs'⟩
    obtain ⟨hy1, hy2⟩ := hy
    have hne' := hne s' (h₂ hs')
    -- the lifted point over a vertex of `s'` has height `k` of that vertex
    have hk : ∀ v, (AffineMap.lineMap s.1 s.2 u : E) = v → (v = s'.1 ∨ v = s'.2) →
        AffineMap.lineMap (h s.1) (h s.2) u = k v := by
      rintro v hv (rfl | rfl)
      · exact congrArg Prod.snd (lift_point_left hne' hxs' hv)
      · exact congrArg Prod.snd (lift_point_right hne' hxs' hv)
    rcases hy1 with hy1 | hy1
    · have hu0 : u = 0 := hinj (hy1.trans (AffineMap.lineMap_apply_zero _ _).symm)
      subst hu0
      left
      refine ⟨rfl, ?_⟩
      have := hk s.1 hy1 (by rw [← hy1]; exact hy2)
      simpa using this
    · rw [mem_singleton_iff] at hy1
      have hu1 : u = 1 := hinj (hy1.trans (AffineMap.lineMap_apply_one _ _).symm)
      subst hu1
      right; left
      refine ⟨rfl, ?_⟩
      have := hk s.2 hy1 (by rw [← hy1]; exact hy2)
      simpa using this

/-- The lift of a decomposition is a PL graph, `Prod.fst` is injective on it, and it projects
onto the union of the edges. -/
theorem liftG_props {S : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2) (hdis : PairwiseEndpoints S)
    (h : E → ℝ) :
    IsPLGraph (liftG S h) ∧ InjOn Prod.fst (liftG S h) ∧
      Prod.fst '' liftG S h = ⋃ s ∈ S, segment ℝ s.1 s.2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨S.image (fun s => ((s.1, h s.1), (s.2, h s.2))), ?_, ?_, ?_⟩
    · simp only [Finset.mem_image]
      rintro _ ⟨s, hs, rfl⟩ he
      exact hne s hs (congrArg Prod.fst he)
    · rw [liftG, Finset.set_biUnion_finset_image]
    · simp only [Finset.mem_image]
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hne' x ⟨hx, hx'⟩
      have hss : s ≠ s' := by rintro rfl; exact hne' rfl
      obtain ⟨h1, h2⟩ := hdis s hs s' hs' hss
        ⟨fst_mem_of_mem_lift_segment hx, fst_mem_of_mem_lift_segment hx'⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (lift_point_left (hne s hs) hx h1)
        · exact Or.inr (lift_point_right (hne s hs) hx (mem_singleton_iff.1 h1))
      · rcases h2 with h2 | h2
        · exact Or.inl (lift_point_left (hne s' hs') hx' h2)
        · exact Or.inr (lift_point_right (hne s' hs') hx' (mem_singleton_iff.1 h2))
  · intro x hx x' hx' he
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.1 hx'
    have hab := hne s hs
    have hinj : Function.Injective (AffineMap.lineMap s.1 s.2 : ℝ → E) :=
      AffineMap.lineMap_injective ℝ hab
    by_cases hss : s = s'
    · subst hss
      obtain ⟨u, -, rfl⟩ := mem_lift_segment.1 hxs
      obtain ⟨u', -, rfl⟩ := mem_lift_segment.1 hxs'
      have : u = u' := hinj he
      subst this; rfl
    · obtain ⟨h1, h2⟩ := hdis s hs s' hs' hss
        ⟨fst_mem_of_mem_lift_segment hxs, by rw [he]; exact fst_mem_of_mem_lift_segment hxs'⟩
      have hne' := hne s' hs'
      have e1 : ∀ v, x.1 = v → (v = s.1 ∨ v = s.2) → x = (v, h v) := by
        rintro v hv (rfl | rfl)
        · exact lift_point_left hab hxs hv
        · exact lift_point_right hab hxs hv
      have e2 : ∀ v, x'.1 = v → (v = s'.1 ∨ v = s'.2) → x' = (v, h v) := by
        rintro v hv (rfl | rfl)
        · exact lift_point_left hne' hxs' hv
        · exact lift_point_right hne' hxs' hv
      have hy1 : x.1 = s.1 ∨ x.1 = s.2 := by
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (mem_singleton_iff.1 h1)
      have hy2 : x.1 = s'.1 ∨ x.1 = s'.2 := by
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (mem_singleton_iff.1 h2)
      rw [e1 _ rfl hy1, e2 _ he.symm hy2]
  · rw [liftG, image_iUnion₂]
    simp only [image_fst_lift_segment]

end Lift

section Exists

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineMap_lt_lineMap {α β γ δ u : ℝ} (h1 : α < γ) (h2 : β < δ) (hu : u ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap α β u < AffineMap.lineMap γ δ u := by
  rw [lineMap_real, lineMap_real]
  obtain ⟨hu0, hu1⟩ := hu
  rcases lt_or_eq_of_le hu1 with h | h
  · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 h1), mul_nonneg hu0 (sub_nonneg.2 h2.le)]
  · subst h; simp; linarith

theorem PairwiseEndpoints.mono {S T : Finset (E × E)} (h : PairwiseEndpoints S) (hT : T ⊆ S) :
    PairwiseEndpoints T :=
  fun s hs s' hs' => h s (hT hs) s' (hT hs')

/-- **The construction of pp. 185–186**, inside `E × ℝ`: every triple satisfying (F1)–(F3) is
the triple of a simple fold. (H–O: "It is straightforward to see that this is a well defined
simple fold".) -/
theorem exists_simpleFold {G G₁ G₂ G₃ : Set E} (h : IsFoldTriple G G₁ G₂ G₃) :
    ∃ F₁ F₂ F₃ : Set (E × ℝ), IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ := by
  classical
  have hG := h.isPLGraph
  have hfin₃ := h.relFrontier_left_finite
  have hfin₁ := h.relFrontier_right_finite
  have h' := h
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, hF3⟩ := h'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  set B₃ := relFrontier G G₁ with hB₃
  set B₁ := relFrontier G G₃ with hB₁
  have hB₃G₂ : B₃ ⊆ G₂ := by
    rw [hB₃, relFrontier_left_eq hG₁c hG₃c hcov hG₂]; exact inter_subset_right
  have hB₁G₂ : B₁ ⊆ G₂ := by
    rw [hB₁, relFrontier_right_eq hG₁c hG₃c hcov hG₂]; exact inter_subset_right
  have hB13 : Disjoint B₃ B₁ := relFrontier_disjoint hG₁c hG₃c hcov hG₂ hF3
  have hG₂G₁ : G₂ ⊆ G₁ := hG₂ ▸ inter_subset_left
  have hG₂G₃ : G₂ ⊆ G₃ := hG₂ ▸ inter_subset_right
  have hG₁G : G₁ ⊆ G := hcov ▸ subset_union_left
  have hG₃G : G₃ ⊆ G := hcov ▸ subset_union_right
  set P : Finset E := hfin₃.toFinset ∪ hfin₁.toFinset with hP
  have hPmem : ∀ p, p ∈ P ↔ p ∈ B₃ ∨ p ∈ B₁ := by
    intro p; simp [hP]
  obtain ⟨S₀, hne₀, hGS₀, hdis₀, hcov₀, -, hvert₀⟩ :=
    hG.exists_refinement (k := 3) ![G₁, G₂, G₃]
      (fun i => by fin_cases i <;> simp [hG₁, hG₂P, hG₃])
      (fun i => by fin_cases i <;> simp [hG₁G, hG₃G, hG₂G₁.trans hG₁G]) P
      (fun p hp => by
        rcases (hPmem p).1 hp with h | h
        · exact hG₁G (hG₂G₁ (hB₃G₂ h))
        · exact hG₁G (hG₂G₁ (hB₁G₂ h)))
  have hc₁ : ∀ x ∈ G₁, ∃ s ∈ S₀, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ G₁ := hcov₀ 0
  have hc₂ : ∀ x ∈ G₂, ∃ s ∈ S₀, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ G₂ := hcov₀ 1
  have hc₃ : ∀ x ∈ G₃, ∃ s ∈ S₀, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ G₃ := hcov₀ 2
  obtain ⟨S, hne, hdis, hSS₀, hcovS, hv1, hv2, hgood⟩ := exists_midpoint_subdivision hne₀ hdis₀
  have hcS : ∀ A : Set E, (∀ x ∈ A, ∃ s ∈ S₀, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A) →
      ∀ x ∈ A, ∃ σ ∈ S, x ∈ segment ℝ σ.1 σ.2 ∧ segment ℝ σ.1 σ.2 ⊆ A := by
    intro A hA x hx
    obtain ⟨s, hs, hxs, hsA⟩ := hA x hx
    obtain ⟨σ, hσ, hxσ, hσs⟩ := hcovS s hs x hxs
    exact ⟨σ, hσ, hxσ, hσs.trans hsA⟩
  have hU : ∀ A : Set E, (∀ x ∈ A, ∃ s ∈ S₀, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A) →
      (⋃ σ ∈ S.filter (fun σ => segment ℝ σ.1 σ.2 ⊆ A), segment ℝ σ.1 σ.2) = A := by
    intro A hA
    apply Subset.antisymm
    · intro x hx
      obtain ⟨σ, hσ, hxσ⟩ := mem_iUnion₂.1 hx
      exact (Finset.mem_filter.1 hσ).2 hxσ
    · intro x hx
      obtain ⟨σ, hσ, hxσ, hσA⟩ := hcS A hA x hx
      exact mem_biUnion (Finset.mem_filter.2 ⟨hσ, hσA⟩) hxσ
  have hvB : ∀ v, (v ∈ B₃ ∨ v ∈ B₁) → ∃ σ ∈ S, v = σ.1 ∨ v = σ.2 := by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := hvert₀ v ((hPmem v).2 hv)
    rcases hvs with hvs | hvs
    · obtain ⟨σ, hσ, he⟩ := hv1 s hs
      exact ⟨σ, hσ, Or.inl (hvs.trans he.symm)⟩
    · obtain ⟨σ, hσ, he⟩ := hv2 s hs
      exact ⟨σ, hσ, Or.inr (hvs.trans he.symm)⟩
  have hgood' : ∀ σ ∈ S, ∃ w, (w = σ.1 ∨ w = σ.2) ∧ w ∉ B₃ ∧ w ∉ B₁ := by
    intro σ hσ
    obtain ⟨w, hw, hwv⟩ := hgood σ hσ
    have hwP : w ∉ P := by
      intro hwP
      obtain ⟨s, hs, hws⟩ := hvert₀ w hwP
      rcases hws with h | h
      · exact (hwv s hs).1 h
      · exact (hwv s hs).2 h
    exact ⟨w, hw, fun h => hwP ((hPmem w).2 (Or.inl h)),
      fun h => hwP ((hPmem w).2 (Or.inr h))⟩
  have hedge : ∀ v ∈ G₂, (v ∈ B₃ ∨ v ∈ B₁) →
      ∃ σ ∈ S, segment ℝ σ.1 σ.2 ⊆ G₂ ∧ (v = σ.1 ∨ v = σ.2) := by
    intro v hv hB
    obtain ⟨τ, hτ, hvτ⟩ := hvB v hB
    obtain ⟨σ, hσ, hvσ, hσG⟩ := hcS G₂ hc₂ v hv
    by_cases hστ : σ = τ
    · subst hστ; exact ⟨σ, hσ, hσG, hvτ⟩
    · have hvτ' : v ∈ segment ℝ τ.1 τ.2 := by
        rcases hvτ with h | h <;> rw [h]
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hdis σ hσ τ hτ hστ ⟨hvσ, hvτ'⟩).1 with h | h
      · exact ⟨σ, hσ, hσG, Or.inl h⟩
      · exact ⟨σ, hσ, hσG, Or.inr (mem_singleton_iff.1 h)⟩
  set h₁ : E → ℝ := fun v => if v ∈ B₃ then 1 else 0 with hh₁
  set h₃ : E → ℝ := fun v => if v ∈ B₁ then 1 else 2 with hh₃
  set S₁ := S.filter (fun σ => segment ℝ σ.1 σ.2 ⊆ G₁) with hS₁
  set S₂ := S.filter (fun σ => segment ℝ σ.1 σ.2 ⊆ G₂) with hS₂
  set S₃ := S.filter (fun σ => segment ℝ σ.1 σ.2 ⊆ G₃) with hS₃
  have hneT : ∀ T ⊆ S, ∀ σ ∈ T, σ.1 ≠ σ.2 := fun T hT σ hσ => hne σ (hT hσ)
  obtain ⟨hP₁, hi₁, he₁⟩ := liftG_props (hneT S₁ (Finset.filter_subset _ _))
    (hdis.mono (Finset.filter_subset _ _)) h₁
  obtain ⟨hP₂, hi₂, he₂⟩ := liftG_props (hneT S₂ (Finset.filter_subset _ _))
    (hdis.mono (Finset.filter_subset _ _)) (fun _ => (1 : ℝ))
  obtain ⟨hP₃, hi₃, he₃⟩ := liftG_props (hneT S₃ (Finset.filter_subset _ _))
    (hdis.mono (Finset.filter_subset _ _)) h₃
  have hlt : ∀ v, h₁ v < h₃ v := by
    intro v
    by_cases h3 : v ∈ B₃
    · have h1 : v ∉ B₁ := fun h1 => hB13.ne_of_mem h3 h1 rfl
      simp only [hh₁, hh₃, h3, h1, if_true, if_false]; norm_num
    · simp only [hh₁, hh₃, h3, if_false]; split_ifs <;> norm_num
  refine ⟨liftG S₁ h₁, liftG S₂ (fun _ => 1), liftG S₃ h₃, h, hP₁, hP₂, hP₃,
    hi₁, he₁.trans (hU G₁ hc₁), hi₂, he₂.trans (hU G₂ hc₂), hi₃, he₃.trans (hU G₃ hc₃),
    ?_, ?_, ?_⟩
  · -- `φ(F₁ ∩ F₂) = ∂G₁`
    ext y
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      obtain ⟨σ, hσ, u, hu, hx1', -, hcase⟩ := lift_inter_cases hne hdis
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) h₁ (fun _ => (1 : ℝ)) hx1 hx2
      rcases hcase with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨-, he⟩
      · rw [hx1', AffineMap.lineMap_apply_zero]
        by_contra hn
        have h0 : h₁ _ = 0 := if_neg hn
        rw [h0] at he; norm_num at he
      · rw [hx1', AffineMap.lineMap_apply_one]
        by_contra hn
        have h0 : h₁ _ = 0 := if_neg hn
        rw [h0] at he; norm_num at he
      · obtain ⟨w, hw, hw3, -⟩ := hgood' σ (Finset.mem_filter.1 hσ).1
        rw [lineMap_real, lineMap_real] at he
        by_cases ha : σ.1 ∈ B₃ <;> by_cases hb : σ.2 ∈ B₃ <;>
          simp only [hh₁, ha, hb, if_true, if_false] at he
        · exfalso; rcases hw with rfl | rfl
          exacts [hw3 ha, hw3 hb]
        · have : u = 0 := by linarith
          rw [hx1', this, AffineMap.lineMap_apply_zero]; exact ha
        · have : u = 1 := by linarith
          rw [hx1', this, AffineMap.lineMap_apply_one]; exact hb
        · exfalso; linarith
    · intro hy
      obtain ⟨σ, hσ, hσG, hyσ⟩ := hedge y (hB₃G₂ hy) (Or.inl hy)
      have hy1 : h₁ y = 1 := if_pos hy
      have hpt1 : (y, (1 : ℝ)) ∈ segment ℝ (σ.1, h₁ σ.1) (σ.2, h₁ σ.2) := by
        rcases hyσ with e | e <;> rw [e] at hy1 ⊢ <;> rw [← hy1]
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      have hpt2 : (y, (1 : ℝ)) ∈ segment ℝ (σ.1, (1 : ℝ)) (σ.2, (1 : ℝ)) := by
        rcases hyσ with e | e <;> rw [e]
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      exact ⟨(y, 1), ⟨mem_biUnion (Finset.mem_filter.2 ⟨hσ, hσG.trans hG₂G₁⟩) hpt1,
        mem_biUnion (Finset.mem_filter.2 ⟨hσ, hσG⟩) hpt2⟩, rfl⟩
  · -- `φ(F₂ ∩ F₃) = ∂G₃`
    ext y
    constructor
    · rintro ⟨x, ⟨hx2, hx3⟩, rfl⟩
      obtain ⟨σ, hσ, u, hu, hx1', -, hcase⟩ := lift_inter_cases hne hdis
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) h₃ (fun _ => (1 : ℝ)) hx3 hx2
      rcases hcase with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨-, he⟩
      · rw [hx1', AffineMap.lineMap_apply_zero]
        by_contra hn
        have h0 : h₃ _ = 2 := if_neg hn
        rw [h0] at he; norm_num at he
      · rw [hx1', AffineMap.lineMap_apply_one]
        by_contra hn
        have h0 : h₃ _ = 2 := if_neg hn
        rw [h0] at he; norm_num at he
      · obtain ⟨w, hw, -, hw1⟩ := hgood' σ (Finset.mem_filter.1 hσ).1
        rw [lineMap_real, lineMap_real] at he
        by_cases ha : σ.1 ∈ B₁ <;> by_cases hb : σ.2 ∈ B₁ <;>
          simp only [hh₃, ha, hb, if_true, if_false] at he
        · exfalso; rcases hw with rfl | rfl
          exacts [hw1 ha, hw1 hb]
        · have : u = 0 := by linarith
          rw [hx1', this, AffineMap.lineMap_apply_zero]; exact ha
        · have : u = 1 := by linarith
          rw [hx1', this, AffineMap.lineMap_apply_one]; exact hb
        · exfalso; linarith
    · intro hy
      obtain ⟨σ, hσ, hσG, hyσ⟩ := hedge y (hB₁G₂ hy) (Or.inr hy)
      have hy3 : h₃ y = 1 := if_pos hy
      have hpt3 : (y, (1 : ℝ)) ∈ segment ℝ (σ.1, h₃ σ.1) (σ.2, h₃ σ.2) := by
        rcases hyσ with e | e <;> rw [e] at hy3 ⊢ <;> rw [← hy3]
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      have hpt2 : (y, (1 : ℝ)) ∈ segment ℝ (σ.1, (1 : ℝ)) (σ.2, (1 : ℝ)) := by
        rcases hyσ with e | e <;> rw [e]
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      exact ⟨(y, 1), ⟨mem_biUnion (Finset.mem_filter.2 ⟨hσ, hσG⟩) hpt2,
        mem_biUnion (Finset.mem_filter.2 ⟨hσ, hσG.trans hG₂G₃⟩) hpt3⟩, rfl⟩
  · -- `F₁ ∩ F₃ = ∅`
    rw [Set.disjoint_left]
    intro x hx1 hx3
    obtain ⟨σ, -, u, hu, -, -, hcase⟩ := lift_inter_cases hne hdis
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) h₁ h₃ hx1 hx3
    rcases hcase with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · exact (hlt σ.1).ne he
    · exact (hlt σ.2).ne he
    · exact (lineMap_lt_lineMap (hlt σ.1) (hlt σ.2) hu).ne he

end Exists

end HPC.HO16
