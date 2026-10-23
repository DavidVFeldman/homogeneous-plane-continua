import HPC.HO16.LadderStair2

/-!
# Batch 197, §5: uniform subdivision of a decomposition

Every edge `s` of a decomposition is cut into `n` equal pieces at the points
`subPt n s p = lineMap s.1 s.2 (p / n)`; the `p`-th piece is oriented by a Boolean `o s p`. The
result is again a decomposition of the same set (`subdiv_ne`, `biUnion_subdiv`,
`pairwiseEndpoints_subdiv`), with pieces `n` times shorter (`dist_subEdge`).
-/

namespace HPC.HO16

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The subdivision points of an edge. -/
def subPt (n : ℕ) (s : E × E) (p : ℕ) : E := AffineMap.lineMap s.1 s.2 ((p : ℝ) / n)

/-- The `p`-th piece of the edge `s`, oriented backwards when `o s p`. -/
def subEdge (n : ℕ) (o : E × E → ℕ → Bool) (s : E × E) (p : ℕ) : E × E :=
  if o s p then (subPt n s (p + 1), subPt n s p) else (subPt n s p, subPt n s (p + 1))

open Classical in
/-- The uniform subdivision of a family of edges. -/
def subdiv (S : Finset (E × E)) (n : ℕ) (o : E × E → ℕ → Bool) : Finset (E × E) :=
  S.biUnion fun s => (Finset.range n).image (subEdge n o s)

theorem mem_subdiv {S : Finset (E × E)} {n : ℕ} {o : E × E → ℕ → Bool} {σ : E × E} :
    σ ∈ subdiv S n o ↔ ∃ s ∈ S, ∃ p < n, subEdge n o s p = σ := by
  classical
  simp only [subdiv, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]

theorem subPt_zero (n : ℕ) (s : E × E) : subPt n s 0 = s.1 := by
  simp [subPt]

theorem subPt_n {n : ℕ} (hn : n ≠ 0) (s : E × E) : subPt n s n = s.2 := by
  simp [subPt, hn]

theorem segment_subEdge {n : ℕ} (o : E × E → ℕ → Bool) (s : E × E) (p : ℕ) :
    segment ℝ (subEdge n o s p).1 (subEdge n o s p).2 =
      AffineMap.lineMap s.1 s.2 '' Icc ((p : ℝ) / n) (((p + 1 : ℕ) : ℝ) / n) := by
  have hle : (p : ℝ) / n ≤ ((p + 1 : ℕ) : ℝ) / n :=
    div_le_div_of_nonneg_right (by push_cast; linarith) (Nat.cast_nonneg n)
  have h : segment ℝ (subPt n s p) (subPt n s (p + 1)) =
      AffineMap.lineMap s.1 s.2 '' Icc ((p : ℝ) / n) (((p + 1 : ℕ) : ℝ) / n) := by
    rw [subPt, subPt, ← segment_eq_Icc hle, image_segment]
  unfold subEdge
  split_ifs
  · rw [segment_symm]; exact h
  · exact h

theorem Icc_sub_unit {n p : ℕ} (hp : p < n) :
    Icc ((p : ℝ) / n) (((p + 1 : ℕ) : ℝ) / n) ⊆ Icc 0 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  intro μ hμ
  refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hn.le) hμ.1, le_trans hμ.2 ?_⟩
  rw [div_le_one hn]; exact_mod_cast hp

theorem segment_subEdge_subset {n p : ℕ} (hp : p < n) (o : E × E → ℕ → Bool) (s : E × E) :
    segment ℝ (subEdge n o s p).1 (subEdge n o s p).2 ⊆ segment ℝ s.1 s.2 := by
  rw [segment_subEdge, segment_eq_image_lineMap]
  exact image_mono (Icc_sub_unit hp)

theorem subdiv_ne {S : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2) {n : ℕ}
    (o : E × E → ℕ → Bool) : ∀ σ ∈ subdiv S n o, σ.1 ≠ σ.2 := by
  intro σ hσ
  obtain ⟨s, hs, p, hp, rfl⟩ := mem_subdiv.1 hσ
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : subPt n s p ≠ subPt n s (p + 1) := by
    intro h
    have := lineMap_inj (hne s hs) h
    field_simp at this
    push_cast at this
    linarith
  unfold subEdge
  split_ifs
  · exact key.symm
  · exact key

theorem biUnion_subdiv {S : Finset (E × E)} {n : ℕ} (hn : n ≠ 0) (o : E × E → ℕ → Bool) :
    (⋃ σ ∈ subdiv S n o, segment ℝ σ.1 σ.2) = ⋃ s ∈ S, segment ℝ s.1 s.2 := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun σ hσ => ?_
    obtain ⟨s, hs, p, hp, rfl⟩ := mem_subdiv.1 hσ
    exact (segment_subEdge_subset hp o s).trans
      (subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs)
  · refine iUnion₂_subset fun s hs => ?_
    intro x hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨μ, hμ, rfl⟩ := hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    set p := min (⌊μ * n⌋₊) (n - 1) with hpdef
    have hp : p < n := by omega
    have hμp : μ ∈ Icc ((p : ℝ) / n) (((p + 1 : ℕ) : ℝ) / n) := by
      constructor
      · rw [div_le_iff₀ hn']
        calc (p : ℝ) ≤ ⌊μ * n⌋₊ := by exact_mod_cast min_le_left _ _
          _ ≤ μ * n := Nat.floor_le (mul_nonneg hμ.1 hn'.le)
      · rw [le_div_iff₀ hn']
        rcases le_total (⌊μ * n⌋₊) (n - 1) with h | h
        · rw [hpdef, min_eq_left h]
          push_cast
          exact (Nat.lt_floor_add_one _).le
        · rw [hpdef, min_eq_right h]
          have : ((n - 1 + 1 : ℕ) : ℝ) = n := by
            congr 1; omega
          rw [this]
          nlinarith [hμ.2]
    refine mem_iUnion₂.2 ⟨subEdge n o s p, mem_subdiv.2 ⟨s, hs, p, hp, rfl⟩, ?_⟩
    rw [segment_subEdge]
    exact ⟨μ, hμp, rfl⟩

theorem mem_ends_subEdge {s : E × E} (hs : s.1 ≠ s.2) {n p : ℕ} (hp : p < n)
    (o : E × E → ℕ → Bool) {μ : ℝ} (hμ : μ ∈ Icc ((p : ℝ) / n) (((p + 1 : ℕ) : ℝ) / n))
    (hx : AffineMap.lineMap s.1 s.2 μ ∈ ({s.1, s.2} : Set E)) :
    AffineMap.lineMap s.1 s.2 μ ∈ ({(subEdge n o s p).1, (subEdge n o s p).2} : Set E) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hset : ({(subEdge n o s p).1, (subEdge n o s p).2} : Set E) =
      {subPt n s p, subPt n s (p + 1)} := by
    unfold subEdge; split_ifs
    · exact pair_comm _ _
    · rfl
  rw [hset]
  rcases hx with hx | hx
  · have hμ0 := (lineMap_eq_left_iff hs).1 hx
    subst hμ0
    have : (p : ℝ) / n ≤ 0 := hμ.1
    have hp0 : p = 0 := by
      have : (p : ℝ) ≤ 0 := by
        rwa [div_le_iff₀ hn', zero_mul] at this
      exact_mod_cast le_antisymm this (Nat.cast_nonneg p)
    subst hp0
    left; rw [subPt_zero]; exact hx
  · have hμ1 := (lineMap_eq_right_iff hs).1 (Set.mem_singleton_iff.1 hx)
    subst hμ1
    have : (1 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) / n := hμ.2
    rw [le_div_iff₀ hn', one_mul] at this
    have hpn : p + 1 = n := by
      have : n ≤ p + 1 := by exact_mod_cast this
      omega
    right
    rw [Set.mem_singleton_iff, hpn, subPt_n (by omega)]
    exact Set.mem_singleton_iff.1 hx

theorem pairwiseEndpoints_subdiv {S : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2)
    (hdis : PairwiseEndpoints S) {n : ℕ} (o : E × E → ℕ → Bool) :
    PairwiseEndpoints (subdiv S n o) := by
  intro σ hσ σ' hσ' hσσ x ⟨hx, hx'⟩
  obtain ⟨s, hs, p, hp, rfl⟩ := mem_subdiv.1 hσ
  obtain ⟨s', hs', p', hp', rfl⟩ := mem_subdiv.1 hσ'
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [segment_subEdge] at hx hx'
  obtain ⟨μ, hμ, rfl⟩ := hx
  obtain ⟨μ', hμ', hμμ⟩ := hx'
  by_cases hss : s = s'
  · subst hss
    have := lineMap_inj (hne s hs) hμμ
    rw [this] at hμ'
    have hset : ∀ r, ({(subEdge n o s r).1, (subEdge n o s r).2} : Set E) =
        {subPt n s r, subPt n s (r + 1)} := by
      intro r; unfold subEdge; split_ifs
      · exact pair_comm _ _
      · rfl
    rw [hset, hset]
    rcases lt_trichotomy p p' with h | h | h
    · have e1 : μ ≤ ((p + 1 : ℕ) : ℝ) / n := hμ.2
      have e2 : (p' : ℝ) / n ≤ μ := hμ'.1
      have e3 : ((p + 1 : ℕ) : ℝ) / n ≤ (p' : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hn'.le
      have hμe : μ = ((p + 1 : ℕ) : ℝ) / n := le_antisymm e1 (e3.trans e2)
      have hpp : (p' : ℝ) = ((p + 1 : ℕ) : ℝ) := by
        have := le_antisymm (e2.trans hμe.le) e3
        field_simp at this; exact this
      have hpp' : p' = p + 1 := by exact_mod_cast hpp
      subst hpp'
      exact ⟨Or.inr (by rw [hμe]; rfl), Or.inl (by rw [hμe]; rfl)⟩
    · subst h; exact absurd rfl hσσ
    · have e1 : μ ≤ ((p' + 1 : ℕ) : ℝ) / n := hμ'.2
      have e2 : (p : ℝ) / n ≤ μ := hμ.1
      have e3 : ((p' + 1 : ℕ) : ℝ) / n ≤ (p : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hn'.le
      have hμe : μ = ((p' + 1 : ℕ) : ℝ) / n := le_antisymm e1 (e3.trans e2)
      have hpp : (p : ℝ) = ((p' + 1 : ℕ) : ℝ) := by
        have := le_antisymm (e2.trans hμe.le) e3
        field_simp at this; exact this
      have hpp' : p = p' + 1 := by exact_mod_cast hpp
      subst hpp'
      exact ⟨Or.inl (by rw [hμe]; rfl), Or.inr (by rw [hμe]; rfl)⟩
  · have h1 : AffineMap.lineMap s.1 s.2 μ ∈ segment ℝ s.1 s.2 := by
      rw [segment_eq_image_lineMap]; exact ⟨μ, Icc_sub_unit hp hμ, rfl⟩
    have h2 : AffineMap.lineMap s.1 s.2 μ ∈ segment ℝ s'.1 s'.2 := by
      rw [← hμμ, segment_eq_image_lineMap]; exact ⟨μ', Icc_sub_unit hp' hμ', rfl⟩
    obtain ⟨k1, k2⟩ := hdis s hs s' hs' hss ⟨h1, h2⟩
    refine ⟨mem_ends_subEdge (hne s hs) hp o hμ k1, ?_⟩
    rw [← hμμ] at k2 ⊢
    exact mem_ends_subEdge (hne s' hs') hp' o hμ' k2

theorem dist_subEdge {n p : ℕ} (hn : n ≠ 0) (o : E × E → ℕ → Bool) (s : E × E) :
    dist (subEdge n o s p).1 (subEdge n o s p).2 = dist s.1 s.2 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : dist (subPt n s p) (subPt n s (p + 1)) = dist s.1 s.2 / n := by
    rw [subPt, subPt, dist_lineMap_lineMap, Real.dist_eq]
    have : (p : ℝ) / n - ((p + 1 : ℕ) : ℝ) / n = -(1 / n) := by
      push_cast; field_simp; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
    ring
  unfold subEdge; split_ifs
  · rw [dist_comm]; exact h
  · exact h

end

end HPC.HO16
