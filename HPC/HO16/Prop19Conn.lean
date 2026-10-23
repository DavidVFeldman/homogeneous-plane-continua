import HPC.HO16.Prop19

/-!
# Batch 196, §3: Proposition 19 for a connected fold (`ho16_prop19`)

H–O p. 209: restrict the structure of `ho16_prop19_full` to a component `C` of `F` with
`φ(C) = G` (Proposition 7, `ho16_prop7`). Every set of the structure meets `C⋆`: the levels
`i ≠ i₀` because `φ(C) = G`; `S′_{i₀}`, `P′₁`, `P′₂` because each contains `φ⋆⁻¹(γ) ∩ (∂F₃)⋆` and
`C` meets `∂F₃` (Lemma 6 (6), `P19.comp_meets_F₂₃`). Then Observations 13 and 16 for components
(`ho16_obs13_comp`, `ho16_obs16_comp`, with `G := F`).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19Conn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem relFrontier_eq_empty_of_superset {G A : Set E} (h : G ⊆ A) : relFrontier G A = ∅ := by
  rw [relFrontier, diff_eq_empty.2 h, closure_empty, inter_empty]

theorem foldPre_inter_comp {F C S : Set (E × ℝ)} (hCF : C ⊆ F) :
    foldPre F S ∩ C ×ˢ Icc (0 : ℝ) 1 = foldPre C S := by
  ext q
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨⟨hCF h.1.1, h.1.2⟩, h.2⟩, h.1⟩⟩

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

theorem relFrontier_G₁_ne : (relFrontier G (Prod.fst '' P₁)).Nonempty := by
  rw [H.fold.2.2.2.1]; exact H.hE.image _

theorem relFrontier_G₃_ne :
    (relFrontier G (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀))).Nonempty := by
  rw [H.fold.2.2.2.2.1]; exact H.hγ.image _

/-- H–O p. 209, \"clearly C meets ∂F₃ by Lemma 6 (6)\": a connected `C ⊆ F` with `φ(C) = G` meets
`F₂ ∩ F₃`. -/
theorem comp_meets_F₂₃ {C : Set (E × ℝ)} (hC : IsPreconnected C) (hCF : C ⊆ F₁ ∪ F₂ ∪ F₃)
    (hCG : Prod.fst '' C = G) : (C ∩ (F₂ ∩ F₃)).Nonempty := by
  by_contra hne
  have hD : Disjoint C (F₂ ∩ F₃) :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
  rcases H.comp_side hC hCF hD with h | h
  · have hsub : G ⊆ sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) := by
      intro y hy
      rw [← hCG] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← H.img₃]; exact ⟨x, h hx, rfl⟩
    have := H.relFrontier_G₃_ne
    rw [relFrontier_eq_empty_of_superset hsub] at this
    exact this.ne_empty rfl
  · have hG₂₁ : Prod.fst '' P₂ ⊆ Prod.fst '' P₁ := by
      rw [H.fold.1.2.2.2.2.2.2.2.1]; exact inter_subset_left
    have hsub : G ⊆ Prod.fst '' P₁ := by
      intro y hy
      rw [← hCG] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← H.img₁]
      rcases h hx with h1 | h2
      · exact ⟨x, h1, rfl⟩
      · rw [H.img₁]; exact hG₂₁ (by rw [← H.img₂]; exact ⟨x, h2, rfl⟩)
    have := H.relFrontier_G₁_ne
    rw [relFrontier_eq_empty_of_superset hsub] at this
    exact this.ne_empty rfl

/-- The levels `i ≠ i₀` meet `C⋆` when `φ(C) = G`. -/
theorem T'_meets {C : Set (E × ℝ)} (hCF : C ⊆ F₁ ∪ F₂ ∪ F₃) (hCG : Prod.fst '' C = G)
    {i : ℕ} (hi : i ∈ Icc 1 k) (hne : i ≠ i₀) :
    (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty := by
  obtain ⟨⟨t, ht⟩, hT⟩ := H.T_straight hi
  obtain ⟨p, hp, hpt⟩ : t.1 ∈ Prod.fst '' C := by rw [hCG]; exact (hT.1 ht).1
  rw [p19T_ne _ _ _ _ _ _ hne]
  exact ⟨_, lift_mem_foldPre hT.1 hCF ht hp hpt⟩

/-- The point over `γ` at a point of `C ∩ ∂F₃`. -/
theorem γ_lift {C : Set (E × ℝ)} {z : E × ℝ} (hz : z ∈ C ∩ (F₂ ∩ F₃)) :
    ∃ t ∈ γ, ((z, t.2) : (E × ℝ) × ℝ) ∈ C ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ X : Set (E × ℝ), γ ⊆ X → ((z, t.2) : (E × ℝ) × ℝ) ∈ foldPre (F₁ ∪ F₂ ∪ F₃) X) := by
  obtain ⟨t, ht, htz⟩ : z.1 ∈ Prod.fst '' γ := by rw [← H.fr23]; exact ⟨z, hz.2, rfl⟩
  have h2 : t.2 ∈ Icc (0 : ℝ) 1 := (H.γ_subG ht).2
  refine ⟨t, ht, ⟨hz.1, h2⟩, fun X hX => ⟨⟨Or.inr hz.2.2, h2⟩, ?_⟩⟩
  show (z.1, t.2) ∈ X
  rw [← htz]; exact hX ht

end P19

/-- **H–O Proposition 19** (p. 202): \"Then there exists a simple fold φ: F→G such that F is
connected, and φ⋆⁻¹(S) contains a set S′ with a broken stairwell structure of height k with a pit
at level i₀+1 if i₀<k, or simply a stairwell structure of height k if i₀=k.\" -/
theorem ho16_prop19 {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hγ : γ.Nonempty)
    (hE : (endSet G P₁).Nonempty) :
    ∃ (G₁ G₂ G₃ : Set E) (F₁ F₂ F₃ : Set (E × ℝ)), IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ ∧
      IsConnected (F₁ ∪ F₂ ∪ F₃) ∧
      ∃ S' : Set ((E × ℝ) × ℝ), S' ⊆ foldPre (F₁ ∪ F₂ ∪ F₃) S ∧
        (i₀ < k → HasBrokenStairwell (F₁ ∪ F₂ ∪ F₃) S' k (i₀ + 1)) ∧
        (i₀ = k → HasStairwell (F₁ ∪ F₂ ∪ F₃) S' k) := by
  obtain ⟨F₁, F₂, F₃, hF⟩ := exists_simpleFold (ho16_prop19_fold hG hconn h hE).1
  have H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃ := ⟨hG, hconn, h, hγ, hE, hF⟩
  obtain ⟨⟨p, hp, hp1, hp3⟩, hrest⟩ := ho16_prop7 hF hconn H.relFrontier_G₁_ne H.relFrontier_G₃_ne
  obtain ⟨hCG, hFC⟩ := hrest p hp hp1 hp3
  set F := F₁ ∪ F₂ ∪ F₃ with hFdef
  set C := connectedComponentIn F p with hCdef
  have hCF : C ⊆ F := connectedComponentIn_subset _ _
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.2 hp
  have hunion : F₁ ∩ C ∪ F₂ ∩ C ∪ F₃ ∩ C = C := by
    rw [← union_inter_distrib_right, ← union_inter_distrib_right]
    exact inter_eq_right.2 hCF
  obtain ⟨z, hz⟩ := H.comp_meets_F₂₃ hCconn.isPreconnected hCF hCG
  obtain ⟨t, ht, hzC, hzX⟩ := H.γ_lift hz
  have hzT : ((z, t.2) : (E × ℝ) × ℝ) ∈ p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀ := by
    rw [p19T_self]; exact Or.inr ⟨hzX _ H.γ_sub_Ti₀, hz.2.2, hzC.2⟩
  have hTne : ∀ i ∈ Icc 1 k, (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    fun i hi => by
      rcases eq_or_ne i i₀ with rfl | hne
      · exact ⟨_, hzT, hzC⟩
      · exact H.T'_meets hCF hCG hi hne
  have hP'₁ : ((foldPre F P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨_, ⟨hzX _ H.γ_sub_P₂, Or.inr hz.2.1, hzC.2⟩, hzC⟩
  have hP'₂ : ((foldPre F (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨_, ⟨hzX _ H.γ_sub_Ti₀, Or.inr hz.2.1, hzC.2⟩, hzC⟩
  obtain ⟨hsub, hbr, hst⟩ := ho16_prop19_full hG hconn h hγ hE hF
  refine ⟨_, _, _, _, _, _, hFC, by rw [hunion]; exact hCconn, ?_⟩
  rw [hunion]
  by_cases hk : i₀ < k
  · refine ⟨_, ?_, fun _ => ⟨_, _, _, _, _,
      ho16_obs16_comp H.FPL (hbr hk) hCdef hTne hP'₁ hP'₂⟩, fun h' => absurd h' (by omega)⟩
    rw [← foldPre_inter_comp hCF]
    exact inter_subset_inter_left _ hsub
  · have hk' : i₀ = k := le_antisymm H.i₀_le (not_lt.1 hk)
    refine ⟨_, ?_, fun h' => absurd h' hk, fun _ => ⟨_, _,
      ho16_obs13_comp H.FPL (hst hk') hCdef hTne⟩⟩
    rw [← foldPre_inter_comp hCF]
    refine inter_subset_inter_left _ (subset_trans ?_ hsub)
    exact subset_union_left.trans subset_union_left

/-- **Proposition 19 as a named `Prop` holds.** -/
theorem hoProp19_holds : HOProp19 := fun _ _ _ _ _ _ _ _ _ _ _ _ hG hconn h hγ hE =>
  ho16_prop19 hG hconn h hγ hE

end Prop19Conn

end HPC.HO16
