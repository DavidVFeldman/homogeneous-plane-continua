import HPC.Hagopian.Hagopian76I

/-!
# Batch 165, item A.1–A.2: no hair on `E`; preimages of continua under `π`

`hagopian76_no_hair` (commission 165 §1, step 1) and `preimage_pi_isContinuum` (step 2).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Preimages of continua under a closed map with connected fibres.** For a continuous map `f`
from a compact space to a Hausdorff space and a closed preconnected `C ⊆ range f` over whose points
the fibres are preconnected, `f⁻¹[C]` is preconnected. -/
theorem isPreconnected_preimage_of_fibres {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f) {C : Set Y}
    (hCc : IsClosed C) (hC : IsPreconnected C) (hCf : C ⊆ range f)
    (hfib : ∀ y ∈ C, IsPreconnected (f ⁻¹' {y})) : IsPreconnected (f ⁻¹' C) := by
  have hP : IsClosed (f ⁻¹' C) := hCc.preimage hf
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro A B hA hB hPAB hdis
  set A' := f ⁻¹' C ∩ A
  set B' := f ⁻¹' C ∩ B
  have hA' : IsClosed A' := hP.inter hA
  have hB' : IsClosed B' := hP.inter hB
  have hfA : IsClosed (f '' A') := (hA'.isCompact.image hf).isClosed
  have hfB : IsClosed (f '' B') := (hB'.isCompact.image hf).isClosed
  have hCAB : C ⊆ f '' A' ∪ f '' B' := by
    intro y hy
    obtain ⟨x, rfl⟩ := hCf hy
    rcases hPAB hy with h | h
    · exact Or.inl ⟨x, ⟨hy, h⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hy, h⟩, rfl⟩
  have hdisAB : C ∩ (f '' A' ∩ f '' B') = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hy, ⟨a, ⟨-, ha⟩, rfl⟩, ⟨b, ⟨-, hb⟩, hba⟩⟩
    have hfy : f ⁻¹' {f a} ⊆ f ⁻¹' C := fun z hz => by
      rw [mem_preimage, mem_singleton_iff.1 hz]; exact hy
    have hsub : f ⁻¹' {f a} ⊆ A ∪ B := hfy.trans hPAB
    have hd : f ⁻¹' {f a} ∩ (A ∩ B) = ∅ :=
      eq_empty_of_subset_empty fun z ⟨hz, hzAB⟩ => by
        rw [← hdis]; exact ⟨hfy hz, hzAB⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 (hfib _ hy)) A B hA hB hsub hd with h | h
    · have : b ∈ A := h (by simp [hba])
      exact (eq_empty_iff_forall_notMem.1 hdis) b ⟨by simp [mem_preimage, hba, hy], this, hb⟩
    · have : a ∈ B := h (by simp)
      exact (eq_empty_iff_forall_notMem.1 hdis) a ⟨hy, ha, this⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hC) _ _ hfA hfB hCAB hdisAB with h | h
  · left
    intro x hx
    rcases hPAB hx with h' | h'
    · exact h'
    · exfalso
      have hfx : f x ∈ C ∩ (f '' A' ∩ f '' B') := ⟨hx, h hx, x, ⟨hx, h'⟩, rfl⟩
      rw [hdisAB] at hfx; exact hfx
  · right
    intro x hx
    rcases hPAB hx with h' | h'
    · exfalso
      have hfx : f x ∈ C ∩ (f '' A' ∩ f '' B') := ⟨hx, ⟨x, ⟨hx, h'⟩, rfl⟩, h hx⟩
      rw [hdisAB] at hfx; exact hfx
    · exact h'

section NoHair

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **No continuum leaves `E` through its middle** (commission 165 §1, step 1). -/
theorem no_hair_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {Q : Set M}
    (hQ : Fold.Q78.IsContinuum Q) (hQE : (Q ∩ E).Nonempty) (h0 : Disjoint Q (layer k 0))
    (h1 : Disjoint Q (layer k 1)) : Q ⊆ E := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  set k' := unitInterval.symm ∘ k with hk'
  have hE' : IsMinimalAdmissible E k' := hE.symm_comp
  have hk'0 : layer k' 0 = layer k 1 := by rw [layer_symm_comp, unitInterval.symm_zero]
  have hEX : IsExtensionAway E (layer k 0) E := ⟨subset_rfl, k, hE, rfl⟩
  have hEZ : IsExtensionAway E (layer k' 0) E := ⟨subset_rfl, k', hE', rfl⟩
  have hQX := subset_extUnion_of_meets hX hHU hAT hEX hQ h0 hQE
  have hQZ := subset_extUnion_of_meets hX hHU hAT hEZ hQ (by rw [hk'0]; exact h1) hQE
  rw [hk'0] at hQZ
  intro q hq
  obtain ⟨K, hK, hqK⟩ := hQX hq
  obtain ⟨K', hK', hqK'⟩ := hQZ hq
  exact ext_inter_subset hX hi hE hK hK' ⟨hqK, hqK'⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- The fibres of `π` on `M` are layers or points, so connected. -/
theorem isConnected_pi_fibre {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (x₀ : M) :
    IsConnected {x : M | π (x : Pt) = π (x₀ : Pt)} := by
  by_cases hx₀ : (x₀ : Pt) ∈ toPt E
  · obtain ⟨e, he⟩ := mem_toPt_iff.1 hx₀
    have heq : {x : M | π (x : Pt) = π (x₀ : Pt)} = layer k (k e) := by
      ext x
      rw [mem_setOf_eq, hπS, ← he]
      change (x : Pt) ∈ HPC.Moore.elt (layerSetoid k) ((e : M) : Pt) ↔ _
      rw [elt_layerSetoid_of_mem]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [← Subtype.ext hyx]
      · intro h; exact ⟨x, h, rfl⟩
    rw [heq]
    exact (isContinuum_layer_min hE (k e)).2
  · have heq : {x : M | π (x : Pt) = π (x₀ : Pt)} = {x₀} := by
      ext x
      rw [mem_setOf_eq, hπS, mem_singleton_iff]
      change (x : Pt) ∈ HPC.Moore.elt (layerSetoid k) (x₀ : Pt) ↔ _
      rw [elt_layerSetoid_of_notMem k hx₀, mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
    rw [heq]
    exact isConnected_singleton

omit [ConnectedSpace M] in
/-- **`π` pulls continua of `π[M]` back to continua of `M`** (commission 165 §1, step 2). -/
theorem preimage_pi_isContinuum_aux {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {C : Set Pt} (hC : Fold.Q78.IsContinuum C) (hCM : C ⊆ π '' M) :
    Fold.Q78.IsContinuum {x : M | π (x : Pt) ∈ C} := by
  set f : M → Pt := fun x => π (x : Pt) with hf
  have hfc : Continuous f := hπc.comp continuous_subtype_val
  have hCc : IsClosed C := hC.1.isClosed
  have hrange : C ⊆ range f := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hCM hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpre : {x : M | π (x : Pt) ∈ C} = f ⁻¹' C := rfl
  rw [hpre]
  refine ⟨(hCc.preimage hfc).isCompact, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hC.2.1
    obtain ⟨x, hx⟩ := hrange hy
    exact ⟨x, by rw [mem_preimage, hx]; exact hy⟩
  · refine isPreconnected_preimage_of_fibres hfc hCc hC.2.2 hrange ?_
    intro y hy
    obtain ⟨x₀, rfl⟩ := hrange hy
    exact (isConnected_pi_fibre hE hπS x₀).2

end NoHair

end HPC.Hagopian
