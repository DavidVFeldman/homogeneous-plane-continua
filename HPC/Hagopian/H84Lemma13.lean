import HPC.Hagopian.H84Regular13

/-!
# Batch 187, §2: Lemma 13, assembly

* `exists_chain84_core`: the numbers `x`, `δ` of p. 339 with every bound used later.
* `chainLinks84_runsStraight_aux`, `chainLinks84_regular_aux`: the batch-186 shapes.
* `hagopian84_lemma13_aux`: Lemma 13, assembled with Lemma 12 as in the batch-186 note.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Lemma13

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- The numbers of p. 339, with all bounds: `x` (`exists_x84`), and `δ < ε` below the radius of
`chainLinks84_chain_aux` and half the gap radius of `exists_gap84`. -/
theorem exists_chain84_core (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) {A B : Set M} (hA : IsClosed A)
    (hAE : Disjoint A E) (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ (x : Fin 16 → unitInterval) (δ : ℝ), 0 < δ ∧ δ < ε ∧ StrictMono x ∧ x 0 = 0 ∧ x 15 = 1 ∧
      GapBound84 k x δ ∧ IsChain5 (chainLinks84 k x δ) ∧ IsNormal5 (chainLinks84 k x δ) ∧
      (⋃ i, chainLinks84 k x δ i) ⊆ Aᶜ ∧
      closure (chainLinks84 k x δ 0 ∪ chainLinks84 k x δ 4) ⊆ B ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
        h '' E ⊆ ⋃ i, chainLinks84 k x δ i ∧
        h '' layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        h '' layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
  obtain ⟨x, hx, hx0, hx15, hxB⟩ := exists_x84 hE hB hBE
  obtain ⟨δ₀, hδ₀, hall⟩ := chainLinks84_chain_aux hX hE hA hAE hB hx hx0 hx15 hxB
  obtain ⟨ρ, hρ, hgap⟩ := exists_gap84 hE hx
  set δ := min δ₀ (min (ρ / 2) (ε / 2)) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by linarith))
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hch, hn, hAc, hBc, hh⟩ := hall δ hδ hδ₀'
  refine ⟨x, δ, hδ, by linarith, hx, hx0, hx15, fun j hj a b ha hb => ?_, hch, hn, hAc, hBc, hh⟩
  have := hgap j hj a b ha hb
  linarith

/-- **Lemma 13, steps (1)–(6)** in the batch-186 shape `chainLinks84_runsStraight`. -/
theorem chainLinks84_runsStraight_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε)
    {A B : Set M} (hA : IsClosed A) (hAE : Disjoint A E) (hB : IsOpen B)
    (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ (x : Fin 16 → unitInterval) (δ : ℝ), 0 < δ ∧ δ < ε ∧ StrictMono x ∧ x 0 = 0 ∧ x 15 = 1 ∧
      IsChain5 (chainLinks84 k x δ) ∧ IsNormal5 (chainLinks84 k x δ) ∧
      (⋃ i, chainLinks84 k x δ i) ⊆ Aᶜ ∧
      closure (chainLinks84 k x δ 0 ∪ chainLinks84 k x δ 4) ⊆ B ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧ RunsStraight g (chainLinks84 k x δ) ∧
        layer g 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        layer g 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
  obtain ⟨x, δ, hδ, hδε, hx, hx0, hx15, hgap, hch, hn, hAc, hBc, hall⟩ :=
    exists_chain84_core hX hE hε hA hAE hB hBE
  refine ⟨x, δ, hδ, hδε, hx, hx0, hx15, hch, hn, hAc, hBc, fun h hh => ?_⟩
  obtain ⟨hcov, h0, h1⟩ := hall h hh
  obtain ⟨g, hg, hgl⟩ := exists_image_map h hE
  refine ⟨g, hg, translate_runsStraight84 hX hi hE hx hx0 hx15 hgap hch h hh hcov h0 h1 rfl hgl,
    ?_, ?_⟩
  · rw [show layer g 0 = h '' layer k 0 from hgl {0}]; exact h0
  · rw [show layer g 1 = h '' layer k 1 from hgl {1}]; exact h1

/-- **Lemma 13, regularity** in the batch-186 shape `chainLinks84_regular`: for links through which
every `δ`-translate of `E` runs straight (with end layers in `L 0 ∖ Cl L 1` and `L 4 ∖ Cl L 3`),
the chain is regular and the closure of each component of `⋃𝔏′` is an essential subcontinuum of a
`δ`-translate of `E`. -/
theorem chainLinks84_regular_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {x : Fin 16 → unitInterval} {δ : ℝ}
    (hch : IsChain5 (chainLinks84 k x δ)) (hn : IsNormal5 (chainLinks84 k x δ))
    (hrs : ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧ RunsStraight g (chainLinks84 k x δ) ∧
        layer g 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        layer g 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3)) :
    IsRegular5 (chainLinks84 k x δ) ∧ ∀ y ∈ midUnion (chainLinks84 k x δ),
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) ∧ ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧
        IsEssential84 g (closure (connectedComponentIn (midUnion (chainLinks84 k x δ)) y)) := by
  have key : ∀ y ∈ midUnion (chainLinks84 k x δ),
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) ∧ ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧
        IsEssential84 g (closure (connectedComponentIn (midUnion (chainLinks84 k x δ)) y)) ∧
        ∃ d : closure (connectedComponentIn (midUnion (chainLinks84 k x δ)) y) → unitInterval,
          IsMinimalAdmissible (closure (connectedComponentIn (midUnion (chainLinks84 k x δ)) y))
            d ∧ RunsStraight d (chainLinks84 k x δ) := by
    intro y hy
    have hyL : ∃ j, y ∈ chainLinks84 k x δ j := by
      rcases hy with (hy | hy) | hy
      · exact ⟨1, hy⟩
      · exact ⟨2, hy⟩
      · exact ⟨3, hy⟩
    obtain ⟨j, hj⟩ := hyL
    rw [chainLinks84_eq] at hj
    simp only [WsetOf, mem_iUnion] at hj
    obtain ⟨v, hv, h, hh, rfl⟩ := hj
    obtain ⟨g, hg, hgrs, hg0, hg1⟩ := hrs h hh
    have hyG : h v ∈ h '' E := ⟨v, layerSet_subset' k _ hv, rfl⟩
    obtain ⟨hess, d, hd, hdrs⟩ := strand_of_runsStraight84 hX hi hch hn hg hgrs hg0 hg1 hyG hy
    exact ⟨h, hh, g, hg, hess, d, hd, hdrs⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨-, -, -, -, -, d, hd, hdrs⟩ := key y hy
    exact ⟨d, hd, hdrs⟩
  · obtain ⟨h, hh, g, hg, hess, -⟩ := key y hy
    exact ⟨h, hh, g, hg, hess⟩

/-- **Lemma 13** (pp. 339–341), in the batch-186 shape, assembled as in the batch-186 note:
`chainLinks84_runsStraight_aux`, `chainLinks84_regular_aux`, `E` runs straight through `𝔏`
(the identity in (6)), Lemma 12, `⋃𝒫 ⊆ ⋃𝔏 ⊆ M ∖ A`, `Cl(P 0 ∪ P 4) ⊆ Cl(L 0 ∪ L 4) ⊆ B`, and the
components of `⋃𝒫′` are components of `⋃𝔏′`. -/
theorem hagopian84_lemma13_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) {A B : Set M}
    (hA : IsClosed A) (hAE : Disjoint A E) (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ P, IsChain5 P ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P ∧
      (⋃ i, P i) ⊆ Aᶜ ∧ closure (P 0 ∪ P 4) ⊆ B ∧
      ∀ x ∈ midUnion P, ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) ∧
        ∃ g : (h '' E) → unitInterval, IsMinimalAdmissible (h '' E) g ∧
          IsEssential84 g (closure (connectedComponentIn (midUnion P) x)) := by
  obtain ⟨x, δ, hδ, hδε, hx, hx0, hx15, hgap, hch, hn, hAc, hBc, hall⟩ :=
    exists_chain84_core hX hE hε hA hAE hB hBE
  have hrs : ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∃ g : (h '' E) → unitInterval,
      IsMinimalAdmissible (h '' E) g ∧ RunsStraight g (chainLinks84 k x δ) ∧
      layer g 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
      layer g 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
    intro h hh
    obtain ⟨hcov, h0, h1⟩ := hall h hh
    obtain ⟨g, hg, hgl⟩ := exists_image_map h hE
    refine ⟨g, hg, translate_runsStraight84 hX hi hE hx hx0 hx15 hgap hch h hh hcov h0 h1 rfl hgl,
      ?_, ?_⟩
    · rw [show layer g 0 = h '' layer k 0 from hgl {0}]; exact h0
    · rw [show layer g 1 = h '' layer k 1 from hgl {1}]; exact h1
  obtain ⟨hreg, hess⟩ := chainLinks84_regular_aux hX hi hch hn hrs
  -- `E` itself runs straight (the identity)
  have hid : ∀ v, dist v ((Homeomorph.refl M) v) < δ := fun v => by simpa using hδ
  obtain ⟨hcov, h0, h1⟩ := hall (Homeomorph.refl M) hid
  have hEeq : E = (Homeomorph.refl M) '' E := by simp
  have hErs : RunsStraight k (chainLinks84 k x δ) :=
    translate_runsStraight84 hX hi hE hx hx0 hx15 hgap hch _ hid hcov h0 h1 hEeq
      (fun S => by simp)
  have hk0 : layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) := by
    simpa using h0
  have hk1 : layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
    simpa using h1
  obtain ⟨P, ⟨hPc, hPL⟩, hPf, hPn, hPr, hPrs, hcomp⟩ :=
    hagopian84_lemma12 hX hi hE hch hn hreg hErs hk0 hk1
  refine ⟨P, hPc, hPf, hPn, hPr, hPrs, ?_, ?_, fun y hy => ?_⟩
  · exact (iUnion_mono hPL).trans hAc
  · exact (closure_mono (union_subset_union (hPL 0) (hPL 4))).trans hBc
  · have hyL : y ∈ midUnion (chainLinks84 k x δ) := by
      rcases hy with (hy | hy) | hy
      · exact Or.inl (Or.inl (hPL 1 hy))
      · exact Or.inl (Or.inr (hPL 2 hy))
      · exact Or.inr (hPL 3 hy)
    obtain ⟨h, hh, g, hg, hg'⟩ := hess y hyL
    refine ⟨h, fun v => (hh v).trans hδε, g, hg, ?_⟩
    rw [hcomp y hy]
    exact hg'

end Lemma13

end HPC.Hagopian
