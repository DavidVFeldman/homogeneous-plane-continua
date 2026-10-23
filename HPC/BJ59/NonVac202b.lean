import HPC.BJ59.NonVac202
import HPC.BJ59.Thm10Induct

/-!
# Batch 202, §8: non-degenerate inputs for the batch-201 statements

The omission of batch 201 (commission 202 §8): the non-degenerate witnesses for `BJStep`,
`BJThm10`, `bj_theorem8_cor_sub`, `bj_theorem5_window` and `exists_window_set` waited for a
continuous snake-like arc of pseudo-arcs. A half of the plane circle of pseudo-arcs is one
(`exists_snakeArcPA`). On it, with one-link chains where a chain is needed, the hypotheses of each
statement hold, and its conclusion is obtained.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-- **A continuous snake-like arc of pseudo-arcs**: a half of the plane circle of pseudo-arcs.
Its end fibres are pseudo-arcs, in particular non-degenerate. -/
theorem exists_snakeArcPA : ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X)
    (f : X → unitInterval), IsContArcPA f ∧ IsSnakeLike (univ : Set X) := by
  obtain ⟨C, hC⟩ := bjPlaneExample
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC
  haveI := hf.compactSpace
  haveI : CompactSpace (halfSet f 1) :=
    isCompact_iff_compactSpace.1 (isClosed_halfSet hf.cont 1).isCompact
  exact ⟨halfSet f 1, inferInstance, inferInstance, halfMap f (Or.inl rfl),
    isContArcPA_halfMap hf (Or.inl rfl), isSnakeLike_halfSet hf (Or.inl rfl)⟩

/-- **`BJThm10` on a non-degenerate input**: the half `X` with `f = g`; the identities of the end
fibres extend to a fibre-preserving homeomorphism. The end fibres are non-degenerate. -/
theorem nonvac_bjThm10 : ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X)
    (f : X → unitInterval), IsContArcPA f ∧ IsSnakeLike (univ : Set X) ∧
      (f ⁻¹' {0}).Nontrivial ∧ (f ⁻¹' {1}).Nontrivial ∧
      ∃ H : X ≃ₜ X, (∀ x, f (H x) = f x) ∧
        (∀ x (hx : x ∈ f ⁻¹' {0}), H x = ((Homeomorph.refl (f ⁻¹' {0})) ⟨x, hx⟩ : X)) ∧
        ∀ x (hx : x ∈ f ⁻¹' {1}), H x = ((Homeomorph.refl (f ⁻¹' {1})) ⟨x, hx⟩ : X) := by
  obtain ⟨X, i1, i2, f, hf, hS⟩ := exists_snakeArcPA
  exact ⟨X, i1, i2, f, hf, hS, (hf.2.2.2 0).2.2, (hf.2.2.2 1).2.2,
    bjThm10 X X f f hf hf hS hS (Homeomorph.refl _) (Homeomorph.refl _)⟩

/-- **`BJStep` on a non-degenerate input**: on the half, the initial stage (one-link chains)
satisfies every hypothesis of the step, and the step gives `δ`-chains `E'` for every `δ > 0`. -/
theorem nonvac_bjStep : ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X)
    (f : X → unitInterval), IsContArcPA f ∧ IsSnakeLike (univ : Set X) ∧
      (f ⁻¹' {0}).Nontrivial ∧
      ∃ (s : BJStage X X) (ε : ℝ),
        s.Good f f (Homeomorph.refl _) (Homeomorph.refl _) ε ∧
        ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (E' : Chain X N) (K : Fin N → Fin s.n),
          univ ⊆ E'.union ∧ IsBJChain E' ∧ IsEpsChain E' δ ∧ HasPrivatePoints E' ∧
          IsFibreChainMap f f E' s.D K := by
  obtain ⟨X, i1, i2, f, hf, hS⟩ := exists_snakeArcPA
  obtain ⟨s, ε, hs⟩ := BJStage.exists_init hf hf (Homeomorph.refl (f ⁻¹' {0}))
    (Homeomorph.refl (f ⁻¹' {1}))
  refine ⟨X, i1, i2, f, hf, hS, (hf.2.2.2 0).2.2, s, ε, hs, fun δ hδ => ?_⟩
  obtain ⟨hcD, hcE, -, -, hpD, -, -, hfE, hcm, hend, -, -⟩ := hs
  obtain ⟨N, E', K, h1, h2, h3, h4, h5, -, -⟩ := bj_step X X f f hf hf hS hS
    (Homeomorph.refl _) (Homeomorph.refl _) s.n s.m s.D s.E s.H hcD hcE hpD hfE hcm hend δ hδ
  exact ⟨N, E', K, h1, h2, h3, h4, h5⟩

/-- **`bj_theorem8_cor_sub` on a non-degenerate input**: the half, the window `[0, 1]`, the
one-link chain and `H₁ = id`. -/
theorem nonvac_bj_theorem8_cor_sub : ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X)
    (g : X → unitInterval), IsContArcPA g ∧ IsSnakeLike (univ : Set X) ∧
      (g ⁻¹' {0}).Nontrivial ∧
      ∃ ε > 0, ∀ (N : ℕ) (F : Chain X N), IsEpsChain F ε → g ⁻¹' Icc 0 1 ⊆ F.union →
        ∃ R : Fin N → Fin 1, IsChainMap R := by
  obtain ⟨X, i1, i2, g, hg, hS⟩ := exists_snakeArcPA
  haveI : Nonempty X := ⟨(hg.2.2.1 0).choose⟩
  have hcov : g ⁻¹' Icc 0 1 ⊆ (oneLinkChain X).union := fun x _ =>
    mem_iUnion.2 ⟨0, mem_univ x⟩
  have hEf : ∀ t ∈ Icc (0 : unitInterval) 1, ∀ j, ((oneLinkChain X).link j ∩ g ⁻¹' {t}).Nonempty :=
    fun t _ j => ⟨(hg.2.2.1 t).choose, mem_univ _, (hg.2.2.1 t).choose_spec⟩
  have hid : IsChainMap (id : Fin 1 → Fin 1) := fun i j h => h
  obtain ⟨ε, hε, h⟩ := bj_theorem8_cor_sub hg hS (a := 0) (b := 1)
    (show (0 : unitInterval) < 1 from by
      show ((0 : unitInterval) : ℝ) < ((1 : unitInterval) : ℝ); simp)
    (Or.inl rfl) (oneLinkChain X) hcov hEf id hid Function.surjective_id
  refine ⟨X, i1, i2, g, hg, hS, (hg.2.2.2 0).2.2, ε, hε, fun N F hF hFc => ?_⟩
  obtain ⟨R, hR, -⟩ := h N F hF hFc
  exact ⟨R, hR⟩

/-- **`exists_window_set` and `bj_theorem5_window` on a non-degenerate input**: on the half, the
window `[0, 1]` and the one-link chain, a transition set `U` exists, and the complement of `U`
splits into closed sets containing the two end fibres. -/
theorem nonvac_bj_theorem5_window : ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X)
    (g : X → unitInterval), IsContArcPA g ∧ IsSnakeLike (univ : Set X) ∧
      (g ⁻¹' {0}).Nontrivial ∧
      ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ g ⁻¹' Ioo 0 1 ∧
        ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧
          g ⁻¹' Icc 0 0 ⊆ A ∧ g ⁻¹' Icc 1 1 ⊆ B := by
  obtain ⟨X, i1, i2, g, hg, hS⟩ := exists_snakeArcPA
  haveI : Nonempty X := ⟨(hg.2.2.1 0).choose⟩
  have hab : (0 : unitInterval) < 1 := by
    show ((0 : unitInterval) : ℝ) < ((1 : unitInterval) : ℝ); simp
  have hTf : ∀ s ∈ Icc (0 : unitInterval) 1, ∀ k : Fin 1, 0 ≤ k.val → k.val ≤ 0 →
      ((oneLinkChain X).link k ∩ g ⁻¹' {s}).Nonempty :=
    fun s _ k _ _ => ⟨(hg.2.2.1 s).choose, mem_univ _, (hg.2.2.1 s).choose_spec⟩
  obtain ⟨U, hU, hUne, hUab, hUcl, hFU⟩ := exists_window_set hg hab (oneLinkChain X) hTf
    (y := 0) le_rfl le_rfl
  obtain ⟨A, B, hA, hB, hAB, hABU, hA0, hB1, -⟩ := bj_theorem5_window hg hS hab
    (oneLinkChain X) (le_refl 0) hTf
    (fun x _ => mem_iUnion₂.2 ⟨0, ⟨le_rfl, le_rfl⟩, mem_univ x⟩) hU hUne hUab
    ⟨0, le_rfl, le_rfl, hUcl⟩ hFU
  exact ⟨X, i1, i2, g, hg, hS, (hg.2.2.2 0).2.2, U, hU, hUne, hUab, A, B, hA, hB, hAB, hABU,
    hA0, hB1⟩

end HPC.BJ59
