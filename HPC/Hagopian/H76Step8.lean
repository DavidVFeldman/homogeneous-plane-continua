import HPC.Hagopian.H76Lemma6

/-!
# Batch 160, item A: Lemma 6, step 8 — `Cl R(X, E) = Cl R(E)`

Hagopian 1976, p. 343: "assume there exists an extension `Q` of `E` away from `Z` that is not
contained in `Cl R(X, E)`. By Lemma 2, there exist homeomorphisms `f₁` and `f₂` of `M` onto `M` near
the identity such that `Q ∪ f₁[Q] ∪ f₂[Q] ∪ Cl R(X, E)` is a triod (see the second paragraph in the
proof of Theorem 1 of [5])."

The proof here uses the second paragraph of the proof of Theorem 1 of [5] directly, in the form of
`hagopian75_no_indecomposable_interior`, with no homeomorphisms. Write `I = Cl R(X, E)`, which is
indecomposable (`lemma6_X_aux`), and let `c ∈ Q − I`.
* If `I ⊆ Q`, then `I` meets two layers of `Q` (it contains `Z = e⁻¹(0)` and `X`), and a continuum
  meeting two layers of a continuum with a minimal admissible map is decomposable
  (`false_of_indec_subset_layers`).
* Otherwise take `b ∈ I` lying in no proper subcontinuum of `I` through a point `p ∈ X`
  (`T13.exists_not_mem_proper_subcontinua`, the composant argument); then `b ∉ Q`. An irreducible
  continuum `E'` from `b` to `c` in `I ∪ Q` contains `I` (`(E' ∩ I) ∪ (Q ∩ I)` is a subcontinuum of
  `I` through `p` and `b`, so it is `I`, and `I` is indecomposable), and `I` has interior in `E'`
  (it contains `E' − Q ∋ b`): this contradicts `hagopian75_no_indecomposable_interior`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Step8

variable {M : Set Pt}

theorem mem_layerSet_val {X : Type*} {E : Set X} {k : E → unitInterval} {S : Set unitInterval}
    {y : E} : (y : X) ∈ layerSet k S ↔ k y ∈ S := val_mem_img

theorem mem_layer_val {X : Type*} {E : Set X} {k : E → unitInterval} {s : unitInterval}
    {y : E} : (y : X) ∈ layer k s ↔ k y = s := val_mem_img

/-- **An indecomposable continuum meets at most one layer.** A subcontinuum of `F` meeting two layers
of a minimal admissible map of `F` is decomposable. -/
theorem false_of_indec_subset_layers (hHU : IsHereditarilyUnicoherent (univ : Set M)) {F : Set M}
    {d : F → unitInterval} {I : Set M} (hI : Fold.Q78.IsIndecomposable I) (hIF : I ⊆ F)
    (y₁ y₂ : F) (h₁ : (y₁ : M) ∈ I) (h₂ : (y₂ : M) ∈ I) (hlt : d y₁ < d y₂)
    (hF : IsMinimalAdmissible F d) : False := by
  have hFc : Fold.Q78.IsContinuum F := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hF; exact hab.1
  obtain ⟨m, hm1, hm2⟩ := exists_between hlt
  have hA₀ : Fold.Q78.IsContinuum (layerSet d (Icc 0 m)) :=
    isContinuum_img hFc.1 hF.2.1 isClosed_Icc isPreconnected_Icc ⟨0, le_rfl, unitInterval.nonneg'⟩
  have hA₁ : Fold.Q78.IsContinuum (layerSet d (Icc m 1)) :=
    isContinuum_img hFc.1 hF.2.1 isClosed_Icc isPreconnected_Icc ⟨1, unitInterval.le_one', le_rfl⟩
  have hy₁ : (y₁ : M) ∈ layerSet d (Icc 0 m) :=
    mem_layerSet_val.2 ⟨unitInterval.nonneg', hm1.le⟩
  have hy₂ : (y₂ : M) ∈ layerSet d (Icc m 1) := mem_layerSet_val.2 ⟨hm2.le, unitInterval.le_one'⟩
  have hB₀ := isContinuum_inter_of_HU hHU hI.1 hA₀ ⟨_, h₁, hy₁⟩
  have hB₁ := isContinuum_inter_of_HU hHU hI.1 hA₁ ⟨_, h₂, hy₂⟩
  have hU : I ∩ layerSet d (Icc 0 m) ∪ I ∩ layerSet d (Icc m 1) = I := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro v hv
    set v' : F := ⟨v, hIF hv⟩
    rcases le_total (d v') m with h | h
    · exact Or.inl ⟨hv, mem_layerSet_val.2 (show d v' ∈ Icc 0 m from ⟨unitInterval.nonneg', h⟩)⟩
    · exact Or.inr ⟨hv, mem_layerSet_val.2 (show d v' ∈ Icc m 1 from ⟨h, unitInterval.le_one'⟩)⟩
  rcases hI.2 _ _ hB₀ hB₁ inter_subset_left inter_subset_left hU with h | h
  · have : (y₂ : M) ∈ I ∩ layerSet d (Icc 0 m) := by rw [h]; exact h₂
    exact absurd (mem_layerSet_val.1 this.2).2 (not_le.2 hm2)
  · have : (y₁ : M) ∈ I ∩ layerSet d (Icc m 1) := by rw [h]; exact h₁
    exact absurd (mem_layerSet_val.1 this.2).1 (not_le.2 hm1)

variable [CompactSpace M] [ConnectedSpace M]

/-- **Step 8.** Every extension of `E` away from `Z` lies in `Cl R(X, E)`. -/
theorem extUnion_one_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    extUnion E (layer k 1) ⊆ closure (extUnion E (layer k 0)) := by
  set I := closure (extUnion E (layer k 0)) with hIdef
  have hI : Fold.Q78.IsIndecomposable I := lemma6_X_aux hX hi hE
  have hHU := hagopian75_lemma1_hu hX hi
  have hEI : E ⊆ I :=
    (IsExtensionAway.subset_extUnion ⟨subset_rfl, k, hE, rfl⟩).trans subset_closure
  rintro c ⟨Q, hQ, hcQ⟩
  by_contra hcI
  have hQc := IsExtensionAway.isContinuum hQ
  obtain ⟨hEQ, e, he, heZ⟩ := hQ
  obtain ⟨p, hp⟩ := hE.2.1.2.1 0
  have hpE : (p : M) ∈ E := p.2
  by_cases hIQ : I ⊆ Q
  · obtain ⟨z, hz⟩ := hE.2.1.2.1 1
    have hzQ : (z : M) ∈ Q := hEQ z.2
    have hze : e ⟨z, hzQ⟩ = 0 := by
      have : (z : M) ∈ layer e 0 := by rw [heZ]; exact ⟨z, hz, rfl⟩
      exact mem_layer_val.1 this
    have hpe : 0 < e ⟨p, hEQ hpE⟩ := by
      refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => ?_
      have : (p : M) ∈ layer k 1 := by rw [← heZ]; exact ⟨⟨p, hEQ hpE⟩, h0.symm, rfl⟩
      have h1 : k p = 1 := by
        obtain ⟨v, hv, hvp⟩ := this
        have : v = p := Subtype.ext hvp
        subst this; exact hv
      exact zero_ne_one (hp.symm.trans h1)
    exact false_of_indec_subset_layers hHU hI hIQ ⟨z, hzQ⟩ ⟨p, hEQ hpE⟩ (hEI z.2) (hEI hpE)
      (by rw [hze]; exact hpe) he
  · obtain ⟨b, hbI, hb⟩ := T13.exists_not_mem_proper_subcontinua hI (hEI hpE)
    have hQI := isContinuum_inter_of_HU hHU hQc hI.1 ⟨p, hEQ hpE, hEI hpE⟩
    have hbQ : b ∉ Q := fun h => hb (Q ∩ I) hQI inter_subset_right
      (fun heq => hIQ (by rw [← heq]; exact inter_subset_left)) ⟨hEQ hpE, hEI hpE⟩ ⟨h, hbI⟩
    have hW : Fold.Q78.IsContinuum (I ∪ Q) := isContinuum_union hI.1 hQc ⟨p, hEI hpE, hEQ hpE⟩
    obtain ⟨E', hE'W, hE'⟩ := exists_irreducible hW (Or.inl hbI) (Or.inr hcQ)
    have hE'I := isContinuum_inter_of_HU hHU hE'.1 hI.1 ⟨b, hE'.2.1, hbI⟩
    obtain ⟨y, hyE', hyI, hyQ⟩ := meets_inter_of_cover hE'.1.2.2 hI.1.1.isClosed hQc.1.isClosed
      hE'W ⟨b, hE'.2.1, hbI⟩ ⟨c, hE'.2.2.1, hcQ⟩
    have hU : Fold.Q78.IsContinuum ((E' ∩ I) ∪ (Q ∩ I)) :=
      isContinuum_union hE'I hQI ⟨y, ⟨hyE', hyI⟩, hyQ, hyI⟩
    have hUeq : (E' ∩ I) ∪ (Q ∩ I) = I := by
      by_contra hne
      exact hb _ hU (union_subset inter_subset_right inter_subset_right) hne
        (Or.inr ⟨hEQ hpE, hEI hpE⟩) (Or.inl ⟨hE'.2.1, hbI⟩)
    rcases hI.2 _ _ hE'I hQI inter_subset_right inter_subset_right hUeq with h | h
    · have hIE' : I ⊆ E' := by rw [← h]; exact inter_subset_left
      refine hagopian75_no_indecomposable_interior hX hi hI.1 hQc ⟨hbI, hbQ⟩ ⟨hcQ, hcI⟩ hE' hE'W I
        hIE' hI.1 ?_ hI
      refine ⟨⟨b, hE'.2.1⟩, ?_⟩
      have hopen : IsOpen ((Subtype.val ⁻¹' Qᶜ) : Set E') :=
        hQc.1.isClosed.isOpen_compl.preimage continuous_subtype_val
      refine interior_maximal ?_ hopen hbQ
      intro v hv
      exact (hE'W v.2).resolve_right hv
    · exact hIQ (by rw [← h]; exact inter_subset_left)

/-- **Step 8.** "`Cl R(X, E) = Cl R(E)`". -/
theorem closure_extUnion_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  apply Subset.antisymm (closure_mono subset_union_left)
  rw [closure_union]
  exact union_subset subset_rfl
    (closure_minimal (extUnion_one_subset hX hi hE) isClosed_closure)

/-- **Lemma 6.** `Cl R(E)` is indecomposable. -/
theorem lemma6_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  rw [← closure_extUnion_aux hX hi hE]
  exact lemma6_X_aux hX hi hE

end Step8

end HPC.Hagopian
