import HPC.Plane.NonCut51

/-!
# Batch 95: general facts about end elements used for Theorem 9

Everything here is about an arbitrary space `S` satisfying `BingS` (Bing's standing hypothesis)
and its decomposition `G = {bingElt p}`.

* `isContinuum_side`: Nadler 6.3 in the form used below (the closed side of a separation by a
  closed connected set is a continuum).
* `endElt_no_two_paths`: three distinct elements, one of them an end element; connected sets
  joining the end element to each of the others while missing the third cannot both exist.
* `at_most_two_endElts`: there are at most two end elements.
* `irred_endElt`: if `S` is irreducible from a proper subcontinuum `A` to a point `x`, then the
  element of `x` is an end element disjoint from `A`, and `A` meets every other end element.
* `endElt_inter_contains_endElt`: if an end element `g` of `S` meets a subcontinuum `Y`, then
  `g ∩ Y` contains an end element of `Y` (the generalisation of QB).
* `bingElt_homeo`, `isEndElt_homeo`: elements and end elements are carried by homeomorphisms.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Nadler 6.3, closed form -/

omit [MetricSpace S] [CompactSpace S] in
/-- **Nadler 6.3, closed form.** In a connected space, if `C` is closed and connected and `Cᶜ` is
covered by disjoint open `U`, `V`, each meeting `Cᶜ`, then `(Cᶜ ∩ U) ∪ C` is closed and connected;
its complement is `Cᶜ ∩ V`. -/
theorem isConnected_side {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {C U V : Set X}
    (hC : IsConnected C) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcov : Cᶜ ⊆ U ∪ V) (hA : (Cᶜ ∩ U).Nonempty) (hB : (Cᶜ ∩ V).Nonempty) :
    IsConnected ((Cᶜ ∩ U) ∪ C) := by
  apply isConnected_union_of_separation hC
  refine ⟨hA, hB, hUV.mono inter_subset_right inter_subset_right, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hx
      rcases hcov hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · have : ((↑) ⁻¹' (Cᶜ ∩ U) : Set (Cᶜ : Set X)) = (↑) ⁻¹' U := by ext ⟨y, hy⟩; simp
    rw [this]; exact hU.preimage continuous_subtype_val
  · have : ((↑) ⁻¹' (Cᶜ ∩ V) : Set (Cᶜ : Set X)) = (↑) ⁻¹' V := by ext ⟨y, hy⟩; simp
    rw [this]; exact hV.preimage continuous_subtype_val

omit [MetricSpace S] [CompactSpace S] in
theorem compl_side {X : Type*} {C U V : Set X} (hUV : Disjoint U V) (hcov : Cᶜ ⊆ U ∪ V) :
    ((Cᶜ ∩ U) ∪ C)ᶜ = Cᶜ ∩ V := by
  ext x
  simp only [mem_compl_iff, mem_union, mem_inter_iff, not_or, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases hcov h2 with h | h
    · exact absurd h (h1 h2)
    · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨fun _ hu => absurd h2 (Set.disjoint_left.mp hUV hu), h1⟩

theorem isContinuum_side [ConnectedSpace S] {C U V : Set S} (hCc : IsClosed C)
    (hC : IsConnected C) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcov : Cᶜ ⊆ U ∪ V) (hA : (Cᶜ ∩ U).Nonempty) (hB : (Cᶜ ∩ V).Nonempty) :
    Fold.Q78.IsContinuum ((Cᶜ ∩ U) ∪ C) := by
  refine ⟨IsClosed.isCompact ?_, isConnected_side hC hU hV hUV hcov hA hB⟩
  rw [← isOpen_compl_iff, compl_side hUV hcov]
  exact hCc.isOpen_compl.inter hV

/-! ## End elements -/

/-- **No two paths around an end element.** For three distinct elements `g_r`, `g_a`, `g_b` with
`g_r` an end element, there cannot be both a connected set missing `g_a` and meeting `g_r` and `g_b`
and a connected set missing `g_b` and meeting `g_r` and `g_a` (Theorem 8 (a)). -/
theorem endElt_no_two_paths (hS : BingS S) {r a b : S} (hr : IsEndElt r)
    (hra : bingElt a ≠ bingElt r) (hrb : bingElt b ≠ bingElt r) (hab : bingElt a ≠ bingElt b)
    {T₁ T₂ : Set S} (h1 : IsPreconnected T₁) (h1a : Disjoint T₁ (bingElt a))
    (h1r : (T₁ ∩ bingElt r).Nonempty) (h1b : (T₁ ∩ bingElt b).Nonempty)
    (h2 : IsPreconnected T₂) (h2b : Disjoint T₂ (bingElt b))
    (h2r : (T₂ ∩ bingElt r).Nonempty) (h2a : (T₂ ∩ bingElt a).Nonempty) : False := by
  rcases bingElt_separates_triple hS r a b hra.symm hab hrb.symm with h | h | h
  · exact hr a b hra hrb hab h
  · exact not_separates_of_preconnected h1 h1a h1r h1b h
  · exact not_separates_of_preconnected h2 h2b h2r h2a h

/-- **At most two end elements.** -/
theorem at_most_two_endElts (hS : BingS S) {a b c : S} (ha : IsEndElt a) (hb : IsEndElt b)
    (hc : IsEndElt c) (hab : bingElt a ≠ bingElt b) : bingElt c = bingElt a ∨ bingElt c = bingElt b := by
  by_contra hno
  push_neg at hno
  rcases bingElt_separates_triple hS a b c hab hno.2.symm hno.1.symm with h | h | h
  · exact ha b c hab.symm hno.1 hno.2.symm h
  · exact hb a c hab hno.2 hno.1.symm h
  · exact hc a b hno.1.symm hno.2.symm hab h

/-! ## Irreducibility from a subcontinuum to a point -/

/-- `S` is irreducible from the set `A` to the point `x`: every subcontinuum containing `A` and `x`
is `S`. -/
def IrredTo (A : Set S) (x : S) : Prop :=
  ∀ K : Set S, Fold.Q78.IsContinuum K → A ⊆ K → x ∈ K → K = univ

/-- If `S` is irreducible from a proper subcontinuum `A` to `x`, then `A` misses the element of
`x`. -/
theorem irred_disjoint (hS : BingS S) {A : Set S} (hA : Fold.Q78.IsContinuum A) (hAne : A ≠ univ)
    {x : S} (hirr : IrredTo A x) : Disjoint A (bingElt x) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  have hU := hirr _ (isContinuum_union hA (bingElt_isContinuum hS x) hne) subset_union_left
    (Or.inr (mem_bingElt x))
  obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem A).mp hAne
  have hsub : Aᶜ ⊆ bingElt x := fun z hz => by
    have : z ∈ A ∪ bingElt x := hU ▸ mem_univ z
    exact this.resolve_left hz
  have := interior_maximal hsub hA.1.isClosed.isOpen_compl hy
  rw [bingElt_interior_eq_empty hS] at this
  exact this

/-- If `S` is irreducible from a proper subcontinuum `A` to `x`, the element of `x` is an end
element. -/
theorem irred_isEndElt (hS : BingS S) {A : Set S} (hA : Fold.Q78.IsContinuum A) (hAne : A ≠ univ)
    {x : S} (hirr : IrredTo A x) : IsEndElt x := by
  haveI := hS.connected
  intro q q' hq hq' hqq' hsep
  obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hqU, hq'V⟩ := hsep
  have hdis := irred_disjoint hS hA hAne hirr
  set C := bingElt x
  have hCc : IsClosed C := (bingElt_isContinuum hS x).1.isClosed
  have hCcon : IsConnected C := (bingElt_isContinuum hS x).2
  have hcov' : Cᶜ ⊆ U ∪ V := fun z hz => hcov ⟨mem_univ z, hz⟩
  have hqC : q ∉ C := fun h => Set.disjoint_left.mp d1 h (mem_bingElt q)
  have hq'C : q' ∉ C := fun h => Set.disjoint_left.mp d2 h (mem_bingElt q')
  have hAC : A ⊆ Cᶜ := fun z hz hzC => Set.disjoint_left.mp hdis hz hzC
  have hAUV : A ⊆ U ∪ V := hAC.trans hcov'
  have hxC : x ∈ C := mem_bingElt x
  rcases (isPreconnected_iff_subset_of_disjoint.mp hA.2.2 U V hU hV hAUV (by
    rw [← subset_empty_iff]; intro z ⟨_, h1, h2⟩; exact Set.disjoint_left.mp hUV h1 h2)) with h | h
  · have hK := isContinuum_side hCc hCcon hU hV hUV hcov' ⟨q, hqC, hqU (mem_bingElt q)⟩
      ⟨q', hq'C, hq'V (mem_bingElt q')⟩
    have := hirr _ hK (fun z hz => Or.inl ⟨hAC hz, h hz⟩) (Or.inr hxC)
    have hq'K : q' ∈ (Cᶜ ∩ U) ∪ C := this ▸ mem_univ q'
    rcases hq'K with h' | h'
    · exact Set.disjoint_left.mp hUV h'.2 (hq'V (mem_bingElt q'))
    · exact hq'C h'
  · have hcov'' : Cᶜ ⊆ V ∪ U := by rw [union_comm]; exact hcov'
    have hK := isContinuum_side hCc hCcon hV hU hUV.symm hcov''
      ⟨q', hq'C, hq'V (mem_bingElt q')⟩ ⟨q, hqC, hqU (mem_bingElt q)⟩
    have := hirr _ hK (fun z hz => Or.inl ⟨hAC hz, h hz⟩) (Or.inr hxC)
    have hqK : q ∈ (Cᶜ ∩ V) ∪ C := this ▸ mem_univ q
    rcases hqK with h' | h'
    · exact Set.disjoint_left.mp hUV (hqU (mem_bingElt q)) h'.2
    · exact hqC h'

/-- If `S` is irreducible from a proper subcontinuum `A` to `x`, then `A` meets every end element
other than the element of `x`. -/
theorem irred_meets_endElt (hS : BingS S) {A : Set S} (hA : Fold.Q78.IsContinuum A)
    (hAne : A ≠ univ) {x : S} (hirr : IrredTo A x) {f : S} (hf : IsEndElt f)
    (hfx : bingElt f ≠ bingElt x) : (A ∩ bingElt f).Nonempty := by
  haveI := hS.connected
  by_contra hno
  rw [not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hno
  have hx := irred_isEndElt hS hA hAne hirr
  have hdis := irred_disjoint hS hA hAne hirr
  obtain ⟨a, ha⟩ := hA.2.nonempty
  have hax : bingElt a ≠ bingElt x := fun e =>
    Set.disjoint_left.mp hdis ha (e ▸ mem_bingElt a)
  have haf : bingElt a ≠ bingElt f := fun e =>
    Set.disjoint_left.mp hno ha (e ▸ mem_bingElt a)
  rcases bingElt_separates_triple hS a f x haf hfx hax with h | h | h
  · obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hfU, hxV⟩ := h
    set C := bingElt a
    have hcov' : Cᶜ ⊆ V ∪ U := fun z hz => by
      rw [union_comm]; exact hcov ⟨mem_univ z, hz⟩
    have hfC : f ∉ C := fun h => Set.disjoint_left.mp d1 h (mem_bingElt f)
    have hxC : x ∉ C := fun h => Set.disjoint_left.mp d2 h (mem_bingElt x)
    have hK := isContinuum_side (bingElt_isContinuum hS a).1.isClosed (bingElt_isContinuum hS a).2
      hV hU hUV.symm hcov' ⟨x, hxC, hxV (mem_bingElt x)⟩ ⟨f, hfC, hfU (mem_bingElt f)⟩
    have hKA := isContinuum_union hK hA ⟨a, Or.inr (mem_bingElt a), ha⟩
    have := hirr _ hKA subset_union_right (Or.inl (Or.inl ⟨hxC, hxV (mem_bingElt x)⟩))
    have hfK : f ∈ ((Cᶜ ∩ V) ∪ C) ∪ A := this ▸ mem_univ f
    rcases hfK with (h' | h') | h'
    · exact Set.disjoint_left.mp hUV (hfU (mem_bingElt f)) h'.2
    · exact hfC h'
    · exact Set.disjoint_left.mp hno h' (mem_bingElt f)
  · exact hf a x haf hfx.symm hax h
  · exact hx a f hax hfx haf h

/-! ## An end element meeting a subcontinuum contains an end element of it -/

/-- **QB, general form.** If an end element `g = bingElt r` of `S` meets a subcontinuum `Y`, then
`g` contains an end element of `Y` (elements of `Y` computed in `Y`). -/
theorem endElt_inter_contains_endElt (hS : BingS S) {r : S} (hr : IsEndElt r) {Y : Set S}
    (hY : Fold.Q78.IsContinuum Y) {y₀ : S} (hy₀Y : y₀ ∈ Y) (hy₀ : y₀ ∈ bingElt r) :
    haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hY.1
    ∃ e : Y, IsEndElt e ∧ ((↑) : Y → S) '' bingElt e ⊆ bingElt r := by
  haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hY.1
  by_cases hnt : Y.Nontrivial
  swap
  · rw [Set.not_nontrivial_iff] at hnt
    refine ⟨⟨y₀, hy₀Y⟩, fun q q' _ _ hqq' _ => hqq' (by rw [Subtype.ext (hnt q.2 q'.2)]), ?_⟩
    rintro _ ⟨z, -, rfl⟩
    rw [hnt z.2 hy₀Y]; exact hy₀
  have hSY := bingS_subcontinuum hS hY hnt
  haveI := hSY.connected
  have key : ∀ z : Y, (z : S) ∈ bingElt r → ((↑) : Y → S) '' bingElt z ⊆ bingElt r :=
    fun z hz => by
      have := bingElt_subtype_subset hS hY z
      rwa [(mem_bingElt_iff hS).mp hz] at this
  by_contra hno
  push_neg at hno
  obtain ⟨a', b', hab, ha, hb⟩ := exists_two_endElts hSY
  have off : ∀ e : Y, IsEndElt e → ∀ z ∈ bingElt e, (z : S) ∉ bingElt r := by
    intro e he z hz hzr
    have := key z hzr
    rw [(mem_bingElt_iff hSY).mp hz] at this
    exact hno e he this
  set x : Y := ⟨y₀, hy₀Y⟩
  have hx : ((↑) : Y → S) '' bingElt x ⊆ bingElt r := key x hy₀
  have hxa : bingElt x ≠ bingElt a' := fun e => off a' ha x (e ▸ mem_bingElt x) hy₀
  have hxb : bingElt x ≠ bingElt b' := fun e => off b' hb x (e ▸ mem_bingElt x) hy₀
  rcases bingElt_separates_triple hSY x a' b' hxa hab hxb with h | h | h
  swap
  · exact ha x b' hxa hab.symm hxb h
  swap
  · exact hb x a' hxb hab hxa h
  obtain ⟨-, -, U, V, hU, hV, hUV, hcov, haU, hbV⟩ := h
  set C : Set Y := (↑) ⁻¹' bingElt r with hC_def
  have hCcont : Fold.Q78.IsContinuum C := isContinuum_preimage_val
    (hS.inter_two (bingElt_isContinuum hS r) hY ⟨y₀, hy₀, hy₀Y⟩)
  have hCx : bingElt x ⊆ C := fun z hz => hx ⟨z, hz, rfl⟩
  have hcov' : Cᶜ ⊆ U ∪ V := fun z hz => hcov ⟨trivial, fun hzx => hz (hCx hzx)⟩
  have ha'C : a' ∉ C := off a' ha a' (mem_bingElt a')
  have hb'C : b' ∉ C := off b' hb b' (mem_bingElt b')
  have side : ∀ (U V : Set Y) (a' : Y), IsOpen U → IsOpen V → Disjoint U V → Cᶜ ⊆ U ∪ V →
      a' ∈ U → a' ∉ C →
      Disjoint (((↑) : Y → S) '' ((Cᶜ ∩ V) ∪ C)) (bingElt (a' : S)) := by
    intro U V a' hU hV hUV hcov haU ha'C
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hza
    set D : Set Y := (↑) ⁻¹' bingElt (a' : S)
    have hD : Fold.Q78.IsContinuum D := isContinuum_preimage_val
      (hS.inter_two (bingElt_isContinuum hS a') hY ⟨a', mem_bingElt _, a'.2⟩)
    have hDC : ∀ w ∈ D, w ∉ C := by
      intro w hwD hwC
      have e1 := (mem_bingElt_iff hS).mp hwD
      have e2 := (mem_bingElt_iff hS).mp hwC
      exact ha'C (show (a' : S) ∈ bingElt r from e2 ▸ e1 ▸ mem_bingElt _)
    have hzV : z ∈ V := by
      rcases hz with h | h
      · exact h.2
      · exact absurd h (hDC z hza)
    obtain ⟨w, hwD, hwU, hwV⟩ := hD.2.2 U V hU hV (fun w hw => hcov (hDC w hw))
      ⟨a', mem_bingElt _, haU⟩ ⟨z, hza, hzV⟩
    exact Set.disjoint_left.mp hUV hwU hwV
  have hcov'' : Cᶜ ⊆ V ∪ U := by rw [union_comm]; exact hcov'
  have hT₁ := (isConnected_side hCcont.2 hV hU hUV.symm hcov''
    ⟨b', hb'C, hbV (mem_bingElt b')⟩ ⟨a', ha'C, haU (mem_bingElt a')⟩).image _
    continuous_subtype_val.continuousOn
  have hT₂ := (isConnected_side hCcont.2 hU hV hUV hcov'
    ⟨a', ha'C, haU (mem_bingElt a')⟩ ⟨b', hb'C, hbV (mem_bingElt b')⟩).image _
    continuous_subtype_val.continuousOn
  have d1 := side U V a' hU hV hUV hcov' (haU (mem_bingElt a')) ha'C
  have d2 := side V U b' hV hU hUV.symm hcov'' (hbV (mem_bingElt b')) hb'C
  have hb'T₁ : (b' : S) ∈ ((↑) : Y → S) '' ((Cᶜ ∩ V) ∪ C) :=
    ⟨b', Or.inl ⟨hb'C, hbV (mem_bingElt b')⟩, rfl⟩
  have ha'T₂ : (a' : S) ∈ ((↑) : Y → S) '' ((Cᶜ ∩ U) ∪ C) :=
    ⟨a', Or.inl ⟨ha'C, haU (mem_bingElt a')⟩, rfl⟩
  have hy₀T : ∀ P : Set Y, y₀ ∈ ((↑) : Y → S) '' (P ∪ C) := fun P => ⟨x, Or.inr hy₀, rfl⟩
  exact endElt_no_two_paths hS hr (a := (a' : S)) (b := (b' : S))
    (fun e => ha'C (show (a' : S) ∈ bingElt r from e ▸ mem_bingElt _))
    (fun e => hb'C (show (b' : S) ∈ bingElt r from e ▸ mem_bingElt _))
    (fun e => Set.disjoint_left.mp d1 hb'T₁ (e ▸ mem_bingElt _))
    hT₁.isPreconnected d1 ⟨y₀, hy₀T _, hy₀⟩ ⟨b', hb'T₁, mem_bingElt _⟩
    hT₂.isPreconnected d2 ⟨y₀, hy₀T _, hy₀⟩ ⟨a', ha'T₂, mem_bingElt _⟩

/-! ## Transport along homeomorphisms -/

section Homeo

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

omit [CompactSpace X] [CompactSpace Y] in
theorem isContinuum_preimage_homeo (φ : X ≃ₜ Y) {H : Set Y} (hH : Fold.Q78.IsContinuum H) :
    Fold.Q78.IsContinuum (φ ⁻¹' H) := by
  rw [← φ.image_symm]
  exact ⟨hH.1.image φ.symm.continuous, hH.2.image _ φ.symm.continuous.continuousOn⟩

omit [CompactSpace X] [CompactSpace Y] in
theorem image_bingElt_subset_homeo (φ : X ≃ₜ Y) (p : X) : φ '' bingElt p ⊆ bingElt (φ p) := by
  rintro _ ⟨z, hz, rfl⟩
  refine mem_sInter.mpr fun H ⟨hH, H', hH', hH'H, hpH'⟩ => ?_
  have : z ∈ φ ⁻¹' H := bingElt_subset (isContinuum_preimage_homeo φ hH)
    ⟨φ ⁻¹' H', isContinuum_preimage_homeo φ hH',
      by rw [← φ.preimage_interior]; exact preimage_mono hH'H,
      by rw [← φ.preimage_interior]; exact hpH'⟩ hz
  exact this

omit [CompactSpace X] [CompactSpace Y] in
/-- Elements are carried by homeomorphisms. -/
theorem bingElt_homeo (φ : X ≃ₜ Y) (p : X) : bingElt (φ p) = φ '' bingElt p := by
  refine Subset.antisymm (fun y hy => ?_) (image_bingElt_subset_homeo φ p)
  have := image_bingElt_subset_homeo φ.symm (φ p) ⟨y, hy, rfl⟩
  rw [φ.symm_apply_apply] at this
  exact ⟨_, this, φ.apply_symm_apply y⟩

omit [CompactSpace X] [CompactSpace Y] in
theorem separates_homeo (φ : X ≃ₜ Y)
    {A B C : Set X} (h : Separates A B C) : Separates (φ '' A) (φ '' B) (φ '' C) := by
  obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hB, hC⟩ := h
  refine ⟨(disjoint_image_iff φ.injective).mpr d1, (disjoint_image_iff φ.injective).mpr d2,
    φ '' U, φ '' V, φ.isOpenMap U hU, φ.isOpenMap V hV, (disjoint_image_iff φ.injective).mpr hUV,
    ?_, image_mono hB, image_mono hC⟩
  rintro y ⟨-, hy⟩
  have : φ.symm y ∈ univ \ A := ⟨trivial, fun h => hy ⟨_, h, φ.apply_symm_apply y⟩⟩
  rcases hcov this with h | h
  · exact Or.inl ⟨_, h, φ.apply_symm_apply y⟩
  · exact Or.inr ⟨_, h, φ.apply_symm_apply y⟩

omit [CompactSpace X] [CompactSpace Y] in
/-- End elements are carried by homeomorphisms. -/
theorem isEndElt_homeo (φ : X ≃ₜ Y) {p : X} (hp : IsEndElt p) : IsEndElt (φ p) := by
  intro q q' hq hq' hqq' hsep
  have e : ∀ y : Y, φ.symm '' bingElt y = bingElt (φ.symm y) := fun y =>
    (bingElt_homeo φ.symm y).symm
  have inj := Set.image_injective.mpr φ.symm.injective
  have h := separates_homeo φ.symm hsep
  rw [e, e, e, φ.symm_apply_apply] at h
  refine hp (φ.symm q) (φ.symm q') ?_ ?_ ?_ h
  · rw [← e, ← φ.symm_apply_apply p, ← e]; exact fun h' => hq (inj h')
  · rw [← e, ← φ.symm_apply_apply p, ← e]; exact fun h' => hq' (inj h')
  · rw [← e, ← e]; exact fun h' => hqq' (inj h')

end Homeo

/-! ## Nested subcontinua -/

section Nested

/-- For `h ⊆ W`, the subtype of `W` cut out by `h` is homeomorphic to `h`. -/
def nestHomeo {W h : Set S} (hsub : h ⊆ W) : ((Subtype.val ⁻¹' h : Set W)) ≃ₜ h where
  toFun z := ⟨z.1.1, z.2⟩
  invFun y := ⟨⟨y.1, hsub y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [MetricSpace S] [CompactSpace S] in
theorem image_val_preimage_inclusion {W h : Set S} (hsub : h ⊆ W) (H : Set W) :
    ((↑) : h → S) '' (Set.inclusion hsub ⁻¹' H) = ((↑) : W → S) '' H ∩ h := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨_, hz, rfl⟩, z.2⟩
  · rintro ⟨⟨w, hw, rfl⟩, hxh⟩
    exact ⟨⟨w, hxh⟩, by simpa [Set.inclusion] using hw, rfl⟩

/-- **Elements of a smaller subcontinuum lie in those of a larger one.** For continua `h ⊆ W`, the
element of `y ∈ h` computed in `h` lies in the element of `y` computed in `W`. -/
theorem bingElt_nested_subset (hS : BingS S) {W h : Set S} (hh : Fold.Q78.IsContinuum h)
    (hsub : h ⊆ W) (y : h) :
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
    ((↑) : h → S) '' bingElt y ⊆ ((↑) : W → S) '' bingElt (Set.inclusion hsub y) := by
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨Set.inclusion hsub z, mem_sInter.mpr fun H ⟨hH, H', hH', hH'H, hpH'⟩ => ?_, rfl⟩
  have cont : ∀ K : Set W, Fold.Q78.IsContinuum K → Set.inclusion hsub y ∈ K →
      Fold.Q78.IsContinuum (Set.inclusion hsub ⁻¹' K) := fun K hK hyK =>
    isContinuum_of_image_val (by
      rw [image_val_preimage_inclusion]
      exact hS.inter_two (isContinuum_image_val hK) hh ⟨y, ⟨_, hyK, rfl⟩, y.2⟩)
  have hc := continuous_inclusion hsub
  exact bingElt_subset (cont H hH (interior_subset (hH'H (interior_subset hpH'))))
    ⟨_, cont H' hH' (interior_subset hpH'),
      (preimage_mono hH'H).trans (preimage_interior_subset_interior_preimage hc),
      preimage_interior_subset_interior_preimage hc hpH'⟩ hz

end Nested

/-- **QB, nested form.** For continua `h ⊆ W`, an end element `f` of `W` meeting `h` contains an end
element of `h` (elements of `h` computed in `h`, of `W` in `W`). -/
theorem endElt_nested (hS : BingS S) {W h : Set S} (hW : Fold.Q78.IsContinuum W)
    (hh : Fold.Q78.IsContinuum h) (hsub : h ⊆ W) (hWnt : W.Nontrivial) :
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
    ∀ {f : W}, IsEndElt f → ∀ {y : S}, y ∈ h → y ∈ ((↑) : W → S) '' bingElt f →
      ∃ e : h, IsEndElt e ∧ ((↑) : h → S) '' bingElt e ⊆ ((↑) : W → S) '' bingElt f := by
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
  intro f hf y hyh hyf
  have hSW := bingS_subcontinuum hS hW hWnt
  obtain ⟨w, hwf, rfl⟩ := hyf
  have hY : Fold.Q78.IsContinuum ((↑) ⁻¹' h : Set W) :=
    isContinuum_preimage_val (by rw [inter_eq_left.mpr hsub]; exact hh)
  obtain ⟨e₀, he₀, he₀f⟩ := endElt_inter_contains_endElt hSW hf hY (y₀ := w) hyh hwf
  refine ⟨nestHomeo hsub e₀, isEndElt_homeo _ he₀, ?_⟩
  rw [bingElt_homeo]
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  exact ⟨z.1, he₀f ⟨z, hz, rfl⟩, rfl⟩

omit [CompactSpace S] in
/-- `IrredFromSet` (Bing's irreducibility of `W` from `A` to `p`) is irreducibility of the space
`W`. -/
theorem irredFromSet_iff {W A : Set S} (hW : Fold.Q78.IsContinuum W) (hAW : A ⊆ W) {p : S}
    (hp : p ∈ W) : IrredFromSet W A p ↔ IrredTo (S := W) ((↑) ⁻¹' A) ⟨p, hp⟩ := by
  constructor
  · intro h K hK hAK hpK
    have := h.2.2.2 (((↑) : W → S) '' K) (isContinuum_image_val hK) (Subtype.coe_image_subset _ _)
      (fun a ha => ⟨⟨a, hAW ha⟩, hAK ha, rfl⟩) ⟨_, hpK, rfl⟩
    refine eq_univ_of_forall fun z => ?_
    have hz : (z : S) ∈ ((↑) : W → S) '' K := by rw [this]; exact z.2
    obtain ⟨z', hz', e⟩ := hz
    exact Subtype.ext e ▸ hz'
  · intro h
    refine ⟨hW, hAW, hp, fun K hK hKW hAK hpK => ?_⟩
    have hK' : Fold.Q78.IsContinuum ((↑) ⁻¹' K : Set W) :=
      isContinuum_preimage_val (by rwa [inter_eq_left.mpr hKW])
    have := h _ hK' (fun z hz => hAK hz) hpK
    exact Subset.antisymm hKW fun w hw => (show (⟨w, hw⟩ : W) ∈ ((↑) ⁻¹' K : Set W) from
      this ▸ trivial)

end HPC.Plane
