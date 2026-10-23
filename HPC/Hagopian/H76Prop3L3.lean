import HPC.Hagopian.Hagopian76O

/-!
# Batch 171, item A: Property 3 through Lemma 3 (a third route)

Hagopian 1976, p. 347, Property 3: no layer `d⁻¹(v)` of `F` contains a crossing component of
`F ∩ π⁻¹[D]`. By `follows_crossing` (batch 170), the closure of such a component contains the middle
translate `h[k⁻¹((4/11, 7/11))]`, so the layer meets two distinct translated layers `h[k⁻¹(α)]`,
`h[k⁻¹(β)]`. This file shows, by Lemma 3 alone (`lemma3_half` applied to `h⁻¹`):

* `layer_meets_translate_end`: an interior layer `d⁻¹(v)` (`0 < v < 1`) of a type A′ continuum
  `F` that meets two distinct layers `h[k⁻¹(α)]`, `h[k⁻¹(β)]` of a translate `h[E]` meets a
  translated end set `h[k⁻¹(0)]` or `h[k⁻¹(1)]`;
* `translate_params_ordConnected`: the parameters `t` with `d⁻¹(v) ∩ h[k⁻¹(t)] ≠ ∅` form an
  interval (hereditary unicoherence);
* `layer_meets_translate_initial`: hence the layer meets every `h[k⁻¹(t)]` with `t ≤ β`, or every
  one with `t ≥ α`.

So a layer of `F` can contain a middle translate only if it reaches an end set of the translate:
the "end case" left open (report 171 §1.A).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Prop3L3

variable {M : Set Pt}

/-- **Lemma 3 against two translated layers.** An interior layer of a type A′ continuum `F` that
meets two distinct layers of a translate `h[E]` meets one of the translated end sets. -/
theorem layer_meets_translate_end_aux (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    {v : unitInterval} (hv0 : 0 < v) (hv1 : v < 1) (h : M ≃ₜ M) {α β : unitInterval}
    (hαβ : α ≠ β) (hα : (layer d v ∩ h '' layer k α).Nonempty)
    (hβ : (layer d v ∩ h '' layer k β).Nonempty) :
    (layer d v ∩ h '' (layer k 0 ∪ layer k 1)).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have h3 : Disjoint (h.symm '' layer d v) (layer k 0 ∪ layer k 1) := by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxe
    have : x ∈ layer d v ∩ h '' (layer k 0 ∪ layer k 1) := ⟨hx, _, hxe, by simp⟩
    rw [hne] at this
    exact this
  have key : ∀ γ : unitInterval, (layer d v ∩ h '' layer k γ).Nonempty →
      h.symm '' layer d v ⊆ layer k γ := by
    intro γ hγ
    refine lemma3_half hHU hAT hF hE hv0 hv1 h.symm ?_ h3
    obtain ⟨x, hxv, y, hy, rfl⟩ := hγ
    exact ⟨y, hy, h y, hxv, by simp⟩
  obtain ⟨x, hx⟩ := hF.2.1.2.1 v
  have hxv : (x : M) ∈ layer d v := ⟨x, hx, rfl⟩
  have h1 := key α hα ⟨x, hxv, rfl⟩
  have h2 := key β hβ ⟨x, hxv, rfl⟩
  obtain ⟨e, he, he'⟩ := h1
  obtain ⟨e', he2, he2'⟩ := h2
  have hee : e = e' := Subtype.ext (he'.trans he2'.symm)
  subst hee
  exact hαβ ((mem_singleton_iff.1 he).symm.trans (mem_singleton_iff.1 he2))

/-- **The parameters met by a layer form an interval.** For a layer `C = d⁻¹(v)` of `F` and a
translate `h[E]`, the set of `t` with `C ∩ h[k⁻¹(t)] ≠ ∅` is order-connected (it is the image under
`k` of the continuum `E ∩ h⁻¹[C]`, hereditary unicoherence). -/
theorem translate_params_ordConnected (hHU : IsHereditarilyUnicoherent (univ : Set M))
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (v : unitInterval) (h : M ≃ₜ M) :
    OrdConnected {t : unitInterval | (layer d v ∩ h '' layer k t).Nonempty} := by
  set T := {t : unitInterval | (layer d v ∩ h '' layer k t).Nonempty}
  by_cases hT : T.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hT; rw [hT]; exact ordConnected_empty
  obtain ⟨t₀, x₀, hx₀v, y₀, hy₀, rfl⟩ := hT
  have hC : Fold.Q78.IsContinuum (h.symm '' layer d v) :=
    isContinuum_homeo_image h.symm (isContinuum_layer_min hF v)
  have hEc : Fold.Q78.IsContinuum E := hE.1.choose_spec.choose_spec.1
  have hne : (E ∩ h.symm '' layer d v).Nonempty :=
    ⟨y₀, img_subset _ hy₀, h y₀, hx₀v, by simp⟩
  have hJ := isContinuum_inter_of_HU hHU hEc hC hne
  -- `T = k '' (val⁻¹ (E ∩ h⁻¹[C]))`
  have hTeq : T = k '' (Subtype.val ⁻¹' (E ∩ h.symm '' layer d v)) := by
    ext t
    constructor
    · rintro ⟨x, hxv, y, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, ⟨e.2, h e, hxv, by simp⟩, he⟩
    · rintro ⟨e, ⟨-, x, hxv, hxe⟩, rfl⟩
      refine ⟨x, hxv, e, ⟨e, rfl, rfl⟩, ?_⟩
      rw [← hxe]; simp
  have hpre : IsPreconnected (Subtype.val ⁻¹' (E ∩ h.symm '' layer d v) : Set E) := by
    have hsub : E ∩ h.symm '' layer d v ⊆ range (Subtype.val : E → M) := by
      rintro x ⟨hx, -⟩; exact ⟨⟨x, hx⟩, rfl⟩
    rw [← (IsInducing.subtypeVal).isPreconnected_image, image_preimage_eq_of_subset hsub]
    exact hJ.2.isPreconnected
  rw [hTeq]
  exact (hpre.image k hE.2.1.1.continuousOn).ordConnected

/-- **Property 3, reduced to the end case.** If an interior layer `d⁻¹(v)` of `F` meets two
distinct layers `h[k⁻¹(α)]`, `h[k⁻¹(β)]` (`α < β`) of a translate of `E`, then it meets every
`h[k⁻¹(t)]` with `t ≤ β`, or every one with `t ≥ α`; in particular it meets `h[k⁻¹(0)]` or
`h[k⁻¹(1)]`. -/
theorem layer_meets_translate_initial (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    {v : unitInterval} (hv0 : 0 < v) (hv1 : v < 1) (h : M ≃ₜ M) {α β : unitInterval}
    (hαβ : α < β) (hα : (layer d v ∩ h '' layer k α).Nonempty)
    (hβ : (layer d v ∩ h '' layer k β).Nonempty) :
    (∀ t, t ≤ β → (layer d v ∩ h '' layer k t).Nonempty) ∨
      (∀ t, α ≤ t → (layer d v ∩ h '' layer k t).Nonempty) := by
  have hoc := translate_params_ordConnected hHU hE hF v h
  obtain ⟨x, hxv, y, hy | hy, rfl⟩ :=
    layer_meets_translate_end_aux hHU hAT hE hF hv0 hv1 h hαβ.ne hα hβ
  · left
    intro t ht
    have h0 : (0 : unitInterval) ∈ {t | (layer d v ∩ h '' layer k t).Nonempty} :=
      ⟨h y, hxv, y, hy, rfl⟩
    exact hoc.out h0 hβ ⟨unitInterval.nonneg' , ht⟩
  · right
    intro t ht
    have h1 : (1 : unitInterval) ∈ {t | (layer d v ∩ h '' layer k t).Nonempty} :=
      ⟨h y, hxv, y, hy, rfl⟩
    exact hoc.out hα h1 ⟨ht, unitInterval.le_one'⟩

end Prop3L3

end HPC.Hagopian
