import HPC.HO16.Sides

/-!
# Batch 195, §§4–6: tools for straight sets and stairwell structures

* straight sets: compactness, `π(𝓔(S)) = ∂π(S)`;
* restriction to a component `C` of `G` (`C` is clopen in `G`): frontiers, end sets, straight
  sets, consistent complements, ordinary points and generic families relative to `C`;
* the parity count behind Claim 14.1 (`parity_count`).
-/

/-- `omega`, after unfolding interval membership (`Set.mem_Icc` etc.) in all hypotheses. -/
macro "icc_omega" : tactic =>
  `(tactic| ((try simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo] at *); omega))

namespace HPC.HO16

open Set Topology Metric Filter

section StairLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Straight sets -/

theorem IsStraight.isCompact {G : Set E} {S : Set (E × ℝ)} (hG : IsPLGraph G)
    (hS : IsStraight G S) : IsCompact S :=
  (hG.isCompact.prod isCompact_Icc).of_isClosed_subset hS.2.1 hS.1

theorem IsStraight.image_subset {G : Set E} {S : Set (E × ℝ)} (hS : IsStraight G S) :
    Prod.fst '' S ⊆ G := by
  rintro _ ⟨q, hq, rfl⟩
  exact (hS.1 hq).1

/-- `π(𝓔(S)) = ∂π(S)` for a straight `S`. -/
theorem IsStraight.image_endSet {G : Set E} {S : Set (E × ℝ)} (hS : IsStraight G S) :
    Prod.fst '' endSet G S = relFrontier G (Prod.fst '' S) := by
  rw [endSet, image_inter_preimage]
  refine inter_eq_right.2 fun y hy => ?_
  have := hy.1
  rwa [hS.2.2.2.isCompact.isClosed.closure_eq] at this

omit [NormedSpace ℝ E] in
theorem endSet_subset (G : Set E) (S : Set (E × ℝ)) : endSet G S ⊆ S := inter_subset_left

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Images of disjoint subsets of a set on which `π` is injective are disjoint. -/
theorem disjoint_image_fst_of_injOn {S X Y : Set (E × ℝ)} (hinj : InjOn Prod.fst S)
    (hX : X ⊆ S) (hY : Y ⊆ S) (h : Disjoint X Y) :
    Disjoint (Prod.fst '' X) (Prod.fst '' Y) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', hqq⟩
  have := hinj (hY hq') (hX hq) hqq
  subst this
  exact Set.disjoint_left.1 h hq hq'

omit [NormedSpace ℝ E] in
/-- Every set has consistent complement relative to `∅`. -/
theorem hasConsCompl_empty (G A : Set E) : HasConsCompl G A ∅ :=
  fun _ _ => Or.inr (disjoint_empty _)

/-! ### Restriction to a component -/

theorem IsPLGraph.isClosed_comp {G : Set E} (hG : IsPLGraph G) (p : E) :
    IsClosed (_root_.connectedComponentIn G p) :=
  (hG.connectedComponentIn p).isCompact.isClosed

theorem IsPLGraph.comp_relOpen {G : Set E} (hG : IsPLGraph G) (p : E) :
    ∀ y ∈ _root_.connectedComponentIn G p, _root_.connectedComponentIn G p ∈ 𝓝[G] y := by
  intro y hy
  have := hG.compDiff_mem_nhdsWithin isClosed_empty (x := p) (y := y) (by rwa [diff_empty])
  rwa [diff_empty] at this

theorem IsPLGraph.closure_inter_comp {G Y : Set E} (hG : IsPLGraph G) (p : E) (hY : Y ⊆ G) :
    closure (Y ∩ _root_.connectedComponentIn G p) = closure Y ∩ _root_.connectedComponentIn G p := by
  obtain ⟨O, hO, hCO⟩ := exists_open_eq_inter (connectedComponentIn_subset G p)
    (hG.comp_relOpen p)
  apply Subset.antisymm
  · exact (closure_inter_subset_inter_closure _ _).trans
      (inter_subset_inter_right _ (hG.isClosed_comp p).closure_subset)
  · rintro z ⟨hzY, hzC⟩
    have hzO : z ∈ O := by rw [hCO] at hzC; exact hzC.2
    have := hO.inter_closure ⟨hzO, hzY⟩
    refine closure_mono ?_ this
    rintro w ⟨hwO, hwY⟩
    refine ⟨hwY, ?_⟩
    rw [hCO]
    exact ⟨hY hwY, hwO⟩

theorem IsPLGraph.relFrontier_inter_comp {G X : Set E} (hG : IsPLGraph G) (p : E) (hX : X ⊆ G) :
    relFrontier (_root_.connectedComponentIn G p) (X ∩ _root_.connectedComponentIn G p) =
      relFrontier G X ∩ _root_.connectedComponentIn G p := by
  have h1 : _root_.connectedComponentIn G p \ (X ∩ _root_.connectedComponentIn G p) =
      (G \ X) ∩ _root_.connectedComponentIn G p := by
    ext z
    constructor
    · rintro ⟨hzC, hz⟩
      exact ⟨⟨connectedComponentIn_subset G p hzC, fun h => hz ⟨h, hzC⟩⟩, hzC⟩
    · rintro ⟨⟨-, hzX⟩, hzC⟩
      exact ⟨hzC, fun h => hzX h.1⟩
  rw [relFrontier, relFrontier, h1, hG.closure_inter_comp p hX,
    hG.closure_inter_comp p diff_subset]
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, -⟩
    exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨⟨h1, h2⟩, h3, h2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem image_fst_inter_star {G : Set E} {T : Set (E × ℝ)} (hT : T ⊆ G ×ˢ Icc (0 : ℝ) 1)
    (D : Set E) : Prod.fst '' (T ∩ D ×ˢ Icc (0 : ℝ) 1) = Prod.fst '' T ∩ D := by
  apply Subset.antisymm
  · rintro _ ⟨q, ⟨hqT, hqD, -⟩, rfl⟩
    exact ⟨⟨q, hqT, rfl⟩, hqD⟩
  · rintro _ ⟨⟨q, hqT, rfl⟩, hqD⟩
    exact ⟨q, ⟨hqT, hqD, (hT hqT).2⟩, rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem image_fst_inter_star_subset (T : Set (E × ℝ)) (D : Set E) :
    Prod.fst '' (T ∩ D ×ˢ Icc (0 : ℝ) 1) ⊆ Prod.fst '' T ∩ D := by
  rintro _ ⟨q, ⟨hqT, hqD, -⟩, rfl⟩
  exact ⟨⟨q, hqT, rfl⟩, hqD⟩

theorem IsPLGraph.endSet_inter_comp {G : Set E} (hG : IsPLGraph G) (p : E) {T : Set (E × ℝ)}
    (hT : T ⊆ G ×ˢ Icc (0 : ℝ) 1) :
    endSet (_root_.connectedComponentIn G p) (T ∩ _root_.connectedComponentIn G p ×ˢ Icc (0 : ℝ) 1) =
      endSet G T ∩ _root_.connectedComponentIn G p ×ˢ Icc (0 : ℝ) 1 := by
  have hπ : Prod.fst '' T ⊆ G := by rintro _ ⟨q, hq, rfl⟩; exact (hT hq).1
  rw [endSet, endSet, image_fst_inter_star hT, hG.relFrontier_inter_comp p hπ]
  ext q
  constructor
  · rintro ⟨⟨hqT, hqC⟩, hq1, -⟩
    exact ⟨⟨hqT, hq1⟩, hqC⟩
  · rintro ⟨⟨hqT, hq1⟩, hqC⟩
    exact ⟨⟨hqT, hqC⟩, hq1, hqC.1⟩

theorem IsStraight.inter_comp {G : Set E} (hG : IsPLGraph G) (p : E) {T : Set (E × ℝ)}
    (hT : IsStraight G T) :
    IsStraight (_root_.connectedComponentIn G p) (T ∩ _root_.connectedComponentIn G p ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨hTG, hTc, hinj, hPL⟩ := hT
  refine ⟨inter_subset_right, hTc.inter ((hG.isClosed_comp p).prod isClosed_Icc),
    hinj.mono inter_subset_left, ?_⟩
  rw [image_fst_inter_star hTG]
  exact hG.inter_connectedComponentIn hPL (by rintro _ ⟨q, hq, rfl⟩; exact (hTG hq).1) p

omit [NormedSpace ℝ E] in
theorem comp_diff_inter_comp {G X : Set E} (p : E) {x : E}
    (hx : x ∈ _root_.connectedComponentIn G p) (hxX : x ∉ X) :
    _root_.connectedComponentIn (_root_.connectedComponentIn G p \ (X ∩ _root_.connectedComponentIn G p)) x =
      _root_.connectedComponentIn (G \ X) x := by
  have hCx : _root_.connectedComponentIn G p = _root_.connectedComponentIn G x := connectedComponentIn_eq hx
  have hxG : x ∈ G := connectedComponentIn_subset G p hx
  apply Subset.antisymm
  · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hx, fun h => hxX h.1⟩) ?_
    intro z hz
    have hz' := connectedComponentIn_subset _ _ hz
    exact ⟨connectedComponentIn_subset G p hz'.1, fun h => hz'.2 ⟨h, hz'.1⟩⟩
  · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hxG, hxX⟩) ?_
    intro z hz
    have hzC : z ∈ _root_.connectedComponentIn G p := by
      rw [hCx]
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (show x ∈ G \ X from ⟨hxG, hxX⟩))
        ((connectedComponentIn_subset _ _).trans diff_subset) hz
    exact ⟨hzC, fun h => (connectedComponentIn_subset _ _ hz).2 h.1⟩

theorem HasConsCompl.inter_comp {G X B : Set E} (hG : IsPLGraph G) (p : E)
    (h : HasConsCompl G X B) :
    HasConsCompl (_root_.connectedComponentIn G p) (X ∩ _root_.connectedComponentIn G p)
      (B ∩ _root_.connectedComponentIn G p) := by
  intro x hx
  obtain ⟨hxC, hxX⟩ := hx
  have hxX' : x ∉ X := fun h => hxX ⟨h, hxC⟩
  have hxG : x ∈ G := connectedComponentIn_subset G p hxC
  rw [comp_diff_inter_comp p hxC hxX']
  have hsub : _root_.connectedComponentIn (G \ X) x ⊆ _root_.connectedComponentIn G p := by
    rw [connectedComponentIn_eq hxC]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hxG, hxX'⟩) ((connectedComponentIn_subset _ _).trans diff_subset)
  have hfr : relFrontier (_root_.connectedComponentIn G p) (_root_.connectedComponentIn (G \ X) x) =
      relFrontier G (_root_.connectedComponentIn (G \ X) x) ∩ _root_.connectedComponentIn G p := by
    have := hG.relFrontier_inter_comp p (comp_subset_G (X := X) x)
    rwa [inter_eq_left.2 hsub] at this
  rw [hfr]
  rcases h x ⟨hxG, hxX'⟩ with h1 | h1
  · exact Or.inl (inter_subset_inter_left _ h1)
  · exact Or.inr (h1.mono inter_subset_left inter_subset_left)

theorem IsOrdinaryPt.comp {G : Set E} (p : E) {x : E} (hx : x ∈ _root_.connectedComponentIn G p)
    (h : IsOrdinaryPt G x) : IsOrdinaryPt (_root_.connectedComponentIn G p) x := by
  obtain ⟨a, b, ha, hb, hab, hsub, hnhds⟩ := h
  have hpre : IsPreconnected (segment ℝ a x ∪ segment ℝ x b) :=
    (convex_segment a x).isPreconnected.union x (right_mem_segment ℝ a x)
      (left_mem_segment ℝ x b) (convex_segment x b).isPreconnected
  have hsubC : segment ℝ a x ∪ segment ℝ x b ⊆ _root_.connectedComponentIn G p := by
    rw [connectedComponentIn_eq hx]
    exact hpre.subset_connectedComponentIn (Or.inl (right_mem_segment ℝ a x)) hsub
  exact ⟨a, b, ha, hb, hab, hsubC, nhdsWithin_mono x (connectedComponentIn_subset G p) hnhds⟩

theorem forall₂_exists_of_mem {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | @cons a' b' l₁ l₂ hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b', by simp, hab⟩
    · obtain ⟨b, hb, hR⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

/-- A generic family stays generic after shrinking its members into a subgraph `C` whose
ordinary points include those of `G` lying in `C`. -/
theorem IsGeneric.of_forall₂ {G C : Set E} (hC : ∀ x ∈ C, IsOrdinaryPt G x → IsOrdinaryPt C x)
    {L' L : List (Set E)} (h₂ : List.Forall₂ (fun B' B => B' ⊆ B ∩ C) L' L)
    (h : IsGeneric G L) : IsGeneric C L' := by
  induction h₂ with
  | nil => exact ⟨by simp, List.Pairwise.nil⟩
  | @cons a b l₁ l₂ hab hrest ih =>
    obtain ⟨h1, h2⟩ := h
    rw [List.pairwise_cons] at h2
    have ih' := ih ⟨fun B hB => h1 B (List.mem_cons_of_mem _ hB), h2.2⟩
    refine ⟨?_, List.pairwise_cons.2 ⟨?_, ih'.2⟩⟩
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · obtain ⟨hf, -, ho⟩ := h1 b (by simp)
        exact ⟨hf.subset (hab.trans inter_subset_left), hab.trans inter_subset_right,
          fun x hx => hC x (hab hx).2 (ho x (hab hx).1)⟩
      · exact ih'.1 B hB
    · intro B' hB'
      obtain ⟨B, hB, hsub⟩ := forall₂_exists_of_mem hrest hB'
      exact (h2.1 B hB).mono (hab.trans inter_subset_left) (hsub.trans inter_subset_left)

/-- A generic family stays generic along a permutation. -/
theorem IsGeneric.perm {G : Set E} {L L' : List (Set E)} (h : IsGeneric G L) (hp : L.Perm L') :
    IsGeneric G L' :=
  ⟨fun B hB => h.1 B (hp.mem_iff.2 hB), (hp.pairwise_iff fun h => h.symm).1 h.2⟩

/-- A sublist of a generic family is generic. -/
theorem IsGeneric.sublist {G : Set E} {L L' : List (Set E)} (h : IsGeneric G L)
    (hs : L'.Sublist L) : IsGeneric G L' :=
  ⟨fun B hB => h.1 B (hs.subset hB), h.2.sublist hs⟩

/-! ### The parity count of Claim 14.1 -/

/-- For `χ₀, …, χ_m` with `χ₀` true and never two consecutive false values, the number of
`i ∈ [1, m]` with `χ_{i-1}` and `χ_i` true has the parity of `m + [¬ χ_m]`. -/
theorem parity_count (χ : ℕ → Prop) [DecidablePred χ] (h0 : χ 0) :
    ∀ m, (∀ i < m, χ i ∨ χ (i + 1)) →
      ((∑ i ∈ Finset.Icc 1 m, if χ (i - 1) ∧ χ i then 1 else 0) + m +
        (if χ m then 0 else 1)) % 2 = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [h0]
  | succ m ih =>
    intro hor
    have ih' := ih fun i hi => hor i (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    have hm := hor m (by omega)
    by_cases h1 : χ m <;> by_cases h2 : χ (m + 1) <;> simp [h1, h2] at ih' hm ⊢ <;> omega

end StairLib

end HPC.HO16
