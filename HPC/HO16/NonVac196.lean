import HPC.HO16.HO16D
import HPC.HO16.StairExample

/-!
# Batch 196, §6: non-vacuity

* `prop19_example_stair`: `ho16_prop19` with `i₀ = k` applied to batch 195's
  `prop19_fold_example` (height 1, pit at level 1, over `[0, 3]`).
* `prop19_example_broken`: `ho16_prop19` with `i₀ < k` applied to the structure of §4
  (`ho16_p208_false`: height 3, pit at level 2, over `[0, 10]`).
* `lift_stairwell_example`: every hypothesis of `ho16_lift_stairwell` is met (batch 195's
  stairwell of height 3 over `[0, 3]`, `X` a point).
* `hoThm15_segment_hyps`: a segment with `M = G × {½}` meets the hypotheses of `HOThm15`.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-- **Non-vacuity of `ho16_prop19`, `i₀ = k`**: a connected simple fold of `[0, 3]` whose
`φ⋆⁻¹(S)` contains a set with a stairwell structure of height 1. -/
theorem prop19_example_stair :
    ∃ (G₁ G₂ G₃ : Set ℝ) (F₁ F₂ F₃ : Set (ℝ × ℝ)),
      IsSimpleFoldOf (Icc (0 : ℝ) 3) G₁ G₂ G₃ F₁ F₂ F₃ ∧ IsConnected (F₁ ∪ F₂ ∪ F₃) ∧
      ∃ S' : Set ((ℝ × ℝ) × ℝ), HasStairwell (F₁ ∪ F₂ ∪ F₃) S' 1 := by
  obtain ⟨S, T, α, γ, P₁, P₂, hG, hc, hB, hγ, hE⟩ := prop19_fold_example
  obtain ⟨G₁, G₂, G₃, F₁, F₂, F₃, hF, hFc, S', -, -, h⟩ :=
    ho16_prop19 hG hc hB hγ hE
  exact ⟨G₁, G₂, G₃, F₁, F₂, F₃, hF, hFc, S', h rfl⟩

/-- **Non-vacuity of `ho16_prop19`, `i₀ < k`**: the structure of §4 (height 3, pit at level 2)
meets every hypothesis, and the proposition gives a connected simple fold of `[0, 10]` whose
`φ⋆⁻¹(S)` contains a set with a broken stairwell structure of height 3 with a pit at level 3. -/
theorem prop19_example_broken :
    ∃ (G : Set ℝ) (G₁ G₂ G₃ : Set ℝ) (F₁ F₂ F₃ : Set (ℝ × ℝ)), IsPLGraph G ∧ IsConnected G ∧
      IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ ∧ IsConnected (F₁ ∪ F₂ ∪ F₃) ∧
      ∃ S' : Set ((ℝ × ℝ) × ℝ), HasBrokenStairwell (F₁ ∪ F₂ ∪ F₃) S' 3 3 := by
  obtain ⟨G, S, T, α, γ, P₁, P₂, -, hG, hc, hB, hγ, hE, -⟩ := ho16_p208_false
  obtain ⟨G₁, G₂, G₃, F₁, F₂, F₃, hF, hFc, S', -, h, -⟩ :=
    ho16_prop19 hG hc hB hγ hE
  exact ⟨G, G₁, G₂, G₃, F₁, F₂, F₃, hG, hc, hF, hFc, S', h (by norm_num)⟩

theorem isHereditarilyIndecomposable_univ_unit :
    IsHereditarilyIndecomposable (univ : Set Unit) := by
  intro K _ hK
  have hKu : K = univ := Subsingleton.eq_univ_of_nonempty hK.2.nonempty
  refine ⟨hK, fun A B hA _ _ _ _ => Or.inl ?_⟩
  rw [hKu]; exact Subsingleton.eq_univ_of_nonempty hA.2.nonempty

/-- **Non-vacuity of `ho16_lift_stairwell`**: its hypotheses are met by the stairwell of height 3
over `G = [0, 3]` of batch 195, `X` a point and `f` constant. -/
theorem lift_stairwell_example :
    ∃ S : Set (ℝ × ℝ), HasStairwell (Icc (0 : ℝ) 3) S 3 ∧
      ∃ h : Unit → ℝ × ℝ, Continuous h ∧ (∀ x, h x ∈ S) ∧ ∀ x, dist (1 : ℝ) (h x).1 < 1 := by
  obtain ⟨S, T, α, hS, -⟩ := stairwell_example
  refine ⟨S, ⟨T, α, hS⟩, ?_⟩
  exact ho16_lift_stairwell 3 (by decide) ℝ (Icc 0 3) (isPLGraph_Icc (by norm_num))
    (isConnected_Icc (by norm_num)) S ⟨T, α, hS⟩ Unit isHereditarilyIndecomposable_univ_unit
    (fun _ => 1) continuous_const (fun _ => ⟨by norm_num, by norm_num⟩) 1 one_pos

/-- **Degenerate inputs of `HOThm15`**: a segment `G = [0, 1]` with `M = G × {½}` meets every
hypothesis of `HOThm15` (with `U = univ`; `V₀ = {t < ½}`, `V₁ = {t > ½}` witness the separation).
Empty `G` is excluded by connectedness. -/
theorem hoThm15_segment_hyps :
    IsPLGraph (Icc (0 : ℝ) 1) ∧ IsConnected (Icc (0 : ℝ) 1) ∧
      Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ) ⊆ Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧
      SeparatesIn (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ))
        (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ)) ∧
      IsOpen (univ : Set (ℝ × ℝ)) ∧ Icc (0 : ℝ) 1 ×ˢ ({1 / 2} : Set ℝ) ⊆ univ := by
  refine ⟨isPLGraph_Icc (by norm_num), isConnected_Icc (by norm_num), ?_,
    ⟨{p | p.2 < 1 / 2}, {p | 1 / 2 < p.2}, isOpen_lt continuous_snd continuous_const,
      isOpen_lt continuous_const continuous_snd, ?_, ?_, ?_, ?_⟩, isOpen_univ, subset_univ _⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    exact ⟨hx, by rw [hy]; norm_num, by rw [hy]; norm_num⟩
  · rintro ⟨x, y⟩ ⟨⟨hx, -⟩, hM⟩
    have : y ≠ 1 / 2 := fun h => hM ⟨hx, h⟩
    rcases lt_or_gt_of_ne this with h | h
    · exact Or.inl h
    · exact Or.inr h
  · ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h1, h2⟩, -⟩
    linarith
  · rintro ⟨x, y⟩ ⟨-, hy⟩
    simp only [mem_singleton_iff] at hy
    show y < 1 / 2
    rw [hy]; norm_num
  · rintro ⟨x, y⟩ ⟨-, hy⟩
    simp only [mem_singleton_iff] at hy
    show 1 / 2 < y
    rw [hy]; norm_num

end HPC.HO16
