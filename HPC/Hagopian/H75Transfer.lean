import HPC.Hagopian.H75Basic
import HPC.Hagopian.H75KurScale

/-!
# Batch 155: passing between a continuum `E ⊆ X` and the space `E`

Kuratowski's construction (`H75Kur*.lean`) works in a compact connected space `Y` irreducible
between two of its points. Lemma 2 is stated for a subset `E` of an ambient metric space. This file
transfers continua, indecomposability and irreducibility along `Subtype.val : E → X`, and assembles
the sufficiency half of Lemma 2 for subsets (`isTypeA'_of_decomposable`).
-/

namespace HPC.Hagopian

open Set Topology

variable {X : Type*} [MetricSpace X] {E : Set X}

theorem isContinuum_val_image {K : Set E} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (Subtype.val '' K) :=
  ⟨hK.1.image continuous_subtype_val, hK.2.image _ continuous_subtype_val.continuousOn⟩

theorem isContinuum_val_preimage {K : Set X} (hKE : K ⊆ E) (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (Subtype.val ⁻¹' K : Set E) := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' K : Set E) = K := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hKE]
  refine ⟨?_, ?_⟩
  · rw [IsInducing.subtypeVal.isCompact_iff, himg]; exact hK.1
  · obtain ⟨x, hx⟩ := hK.2.1
    refine ⟨⟨⟨x, hKE hx⟩, hx⟩, ?_⟩
    rw [← IsInducing.subtypeVal.isPreconnected_image, himg]; exact hK.2.2

theorem isIndecomposable_val_image {K : Set E} (hK : Fold.Q78.IsIndecomposable K) :
    Fold.Q78.IsIndecomposable (Subtype.val '' K) := by
  refine ⟨isContinuum_val_image hK.1, fun A B hA hB hAK hBK hAB => ?_⟩
  have hAE : A ⊆ E := hAK.trans (image_subset_range _ _ |>.trans Subtype.range_coe.subset)
  have hBE : B ⊆ E := hBK.trans (image_subset_range _ _ |>.trans Subtype.range_coe.subset)
  have hpre : ∀ S : Set X, S ⊆ Subtype.val '' K → Subtype.val ⁻¹' S ⊆ K := by
    intro S hS x hx
    obtain ⟨y, hy, hyx⟩ := hS hx
    rwa [Subtype.ext hyx] at hy
  have hun : Subtype.val ⁻¹' A ∪ Subtype.val ⁻¹' B = K := by
    rw [← preimage_union, hAB, Subtype.val_injective.preimage_image]
  have himgA : Subtype.val '' (Subtype.val ⁻¹' A : Set E) = A := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hAE]
  have himgB : Subtype.val '' (Subtype.val ⁻¹' B : Set E) = B := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hBE]
  rcases hK.2 _ _ (isContinuum_val_preimage hAE hA) (isContinuum_val_preimage hBE hB)
    (hpre A hAK) (hpre B hBK) hun with h | h
  · left; rw [← h, himgA]
  · right; rw [← h, himgB]

/-- Irreducibility of a subset transfers to the space. -/
theorem irrBetween_of_isIrreducibleBetween {a b : X} (hE : IsIrreducibleBetween E a b) :
    haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.1.1
    IrrBetween (⟨a, hE.2.1⟩ : E) ⟨b, hE.2.2.1⟩ := by
  intro K hK ha hb
  have h := hE.2.2.2 _ (isContinuum_val_image hK) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    ⟨_, ha, rfl⟩ ⟨_, hb, rfl⟩
  refine eq_univ_of_forall fun y => ?_
  have : (y : X) ∈ Subtype.val '' K := by rw [h]; exact y.2
  obtain ⟨z, hz, hzy⟩ := this
  rwa [Subtype.ext hzy] at hz

/-- **Sufficiency in Lemma 2** for a subset `E` of `X`. -/
theorem isTypeA'_of_decomposable {a b : X} (hE : IsIrreducibleBetween E a b)
    (hH : ∀ K ⊆ E, Fold.Q78.IsContinuum K →
      (interior (Subtype.val ⁻¹' K : Set E)).Nonempty → ¬ Fold.Q78.IsIndecomposable K) :
    IsTypeA' E := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.1.1
  haveI : ConnectedSpace E := isConnected_iff_connectedSpace.mp hE.1.2
  have hH' : ∀ K : Set E, Fold.Q78.IsContinuum K → (interior K).Nonempty →
      ¬ Fold.Q78.IsIndecomposable K := by
    intro K hK hint hind
    refine hH _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) (isContinuum_val_image hK) ?_
      (isIndecomposable_val_image hind)
    rwa [Subtype.val_injective.preimage_image]
  obtain ⟨k, hkc, hks, hkf, hk0⟩ := exists_typeA'_map (irrBetween_of_isIrreducibleBetween hE) hH'
  exact ⟨⟨a, b, hE⟩, k, ⟨hkc, hks, hkf⟩, hk0⟩

end HPC.Hagopian
