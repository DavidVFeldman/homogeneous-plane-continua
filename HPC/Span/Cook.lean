import HPC.Span.Defs
import HPC.Plane.EndPoints51
import HPC.Jones.Jones49Why

/-!
# Batch 191, §3–§4: Cook 1967, Theorem 4; Brouwer reduction; Davis's Theorem 1.1 for
# hereditarily indecomposable continua

* `cook67_theorem4`: a map of a compact metric continuum onto a hereditarily indecomposable
  continuum is confluent. The proof uses one closed neighbourhood of the component instead of
  Cook's decreasing sequence `Cₙ` (commission §3, steps 2 and 5): if `q ∈ Q` were missed by
  `f(C)`, a closed `δ`-neighbourhood `N` of `C` misses `f⁻¹(q)`; boundary bumping gives a continuum
  `K ⊆ N` through `x` not inside `C`; `f(K)` meets `Q` and is not inside it, so contains `Q ∋ q`.
* `isContinuum_sInter_chain`, `brouwer_reduction` (§4.1).
* `exists_surjSpanPos_of_surjSemiSpanPos`, `semiSpanZero_of_spanZero` (§4.2).
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-- Two subcontinua of a hereditarily indecomposable set that meet are nested. -/
theorem nested_of_hi {E : Type*} [MetricSpace E] {S : Set E}
    (hHI : IsHereditarilyIndecomposable S) {P Q : Set E} (hP : Fold.Q78.IsContinuum P)
    (hQ : Fold.Q78.IsContinuum Q) (hPS : P ⊆ S) (hQS : Q ⊆ S) (hPQ : (P ∩ Q).Nonempty) :
    P ⊆ Q ∨ Q ⊆ P := by
  obtain ⟨z, hzP, hzQ⟩ := hPQ
  have hU : Fold.Q78.IsContinuum (P ∪ Q) := ⟨hP.1.union hQ.1, IsConnected.union ⟨z, hzP, hzQ⟩ hP.2 hQ.2⟩
  rcases (hHI _ (union_subset hPS hQS) hU).2 P Q hP hQ subset_union_left subset_union_right rfl
    with h | h
  · right; rw [h]; exact subset_union_right
  · left; rw [h]; exact subset_union_left

/-- A subset of a hereditarily indecomposable set is hereditarily indecomposable. -/
theorem hi_mono {E : Type*} [MetricSpace E] {S T : Set E}
    (hHI : IsHereditarilyIndecomposable S) (hTS : T ⊆ S) : IsHereditarilyIndecomposable T :=
  fun K hK hKc => hHI K (hK.trans hTS) hKc

/-- **Cook 1967, Theorem 4** (p. 243). -/
theorem cook67_theorem4 {X E : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [MetricSpace E] {f : X → E} (hf : Continuous f) {S : Set E} (hS : range f = S)
    (hHI : IsHereditarilyIndecomposable S) {Q : Set E} (hQ : Fold.Q78.IsContinuum Q)
    (hQS : Q ⊆ S) {x : X} (hx : f x ∈ Q) : f '' connectedComponentIn (f ⁻¹' Q) x = Q := by
  set C := connectedComponentIn (f ⁻¹' Q) x with hCdef
  have hCQ : C ⊆ f ⁻¹' Q := connectedComponentIn_subset _ _
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.2 hx
  have hQcl : IsClosed (f ⁻¹' Q) := hQ.1.isClosed.preimage hf
  have hCcl : IsClosed C := by
    refine closure_subset_iff_isClosed.1 ?_
    exact hCconn.closure.isPreconnected.subset_connectedComponentIn (subset_closure hxC)
      (closure_minimal hCQ hQcl)
  refine Subset.antisymm (image_subset_iff.2 hCQ) ?_
  intro q hq
  by_contra hqC
  -- a closed neighbourhood `N` of `C` missing `f⁻¹(q)`
  have hopen : IsOpen (f ⁻¹' {q})ᶜ := (isClosed_singleton.preimage hf).isOpen_compl
  have hsub : C ⊆ (f ⁻¹' {q})ᶜ := by
    intro z hz hzq
    exact hqC ⟨z, hz, hzq⟩
  obtain ⟨δ, hδ, hN⟩ := hCcl.isCompact.exists_cthickening_subset_open hopen hsub
  set N := cthickening δ C
  -- a continuum `K ⊆ N` through `x`, not inside `C`
  obtain ⟨K, hKc, hKconn, hKN, hxK, hKC⟩ : ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ N ∧
      x ∈ K ∧ ¬ K ⊆ C := by
    by_cases hNu : N = univ
    · refine ⟨univ, isCompact_univ, isConnected_univ, by rw [hNu], mem_univ _, ?_⟩
      intro hC
      apply hqC
      have : C = univ := eq_univ_of_univ_subset hC
      rw [this, image_univ, hS]
      exact hQS hq
    · obtain ⟨K, hKc, hKconn, hKN, hxK, w, hwK, hwcl⟩ :=
        exists_continuum_bump_compact isPreconnected_univ isClosed_cthickening.isCompact
          (subset_univ N) hNu (self_subset_cthickening C hxC)
      refine ⟨K, hKc, hKconn, hKN, hxK, fun hKC => ?_⟩
      have hwC := hKC hwK
      have hwint : w ∈ interior N :=
        interior_maximal (thickening_subset_cthickening δ C) isOpen_thickening
          (self_subset_thickening hδ C hwC)
      rw [← compl_eq_univ_diff, closure_compl] at hwcl
      exact hwcl hwint
  -- `f(K)` is not inside `Q`, so it contains `Q`
  have hfK : Fold.Q78.IsContinuum (f '' K) := ⟨hKc.image hf, hKconn.image _ hf.continuousOn⟩
  have hnot : ¬ f '' K ⊆ Q := by
    intro h
    exact hKC (hKconn.isPreconnected.subset_connectedComponentIn hxK (image_subset_iff.1 h))
  have hfKS : f '' K ⊆ S := hS ▸ image_subset_range f K
  rcases nested_of_hi hHI hfK hQ hfKS hQS ⟨f x, mem_image_of_mem f hxK, hx⟩ with h | h
  · exact hnot h
  · obtain ⟨k, hk, hkq⟩ := h hq
    exact hN (hKN hk) hkq

section Davis

variable {X : Type*} [MetricSpace X]

/-- A chain of sets, as an indexed family, is directed by `⊇`. -/
theorem directed_of_isChain_supset {α : Type*} {c : Set (Set α)} (hc : IsChain (· ⊆ ·) c) :
    Directed (· ⊇ ·) (fun F : c => (F : Set α)) := by
  intro F G
  rcases eq_or_ne F G with h | h
  · exact ⟨F, le_rfl, h ▸ le_rfl⟩
  rcases hc F.2 G.2 (fun h' => h (Subtype.ext h')) with hFG | hGF
  · exact ⟨F, le_rfl, hFG⟩
  · exact ⟨G, hGF, le_rfl⟩

/-- A directed intersection of compact preconnected sets of a metric space is preconnected. -/
theorem isPreconnected_iInter_directed_compact {ι : Type*} [Nonempty ι] (K : ι → Set X)
    (hd : Directed (· ⊇ ·) K) (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    IsPreconnected (⋂ i, K i) := by
  have hcl : ∀ i, IsClosed (K i) := fun i => (hc i).isClosed
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov ⟨x, hxK, hxt⟩ ⟨y, hyK, hyt'⟩
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  have hA : IsClosed ((⋂ i, K i) ∩ t) := (isClosed_iInter hcl).inter ht
  have hB : IsClosed ((⋂ i, K i) ∩ t') := (isClosed_iInter hcl).inter ht'
  have hAB : Disjoint ((⋂ i, K i) ∩ t) ((⋂ i, K i) ∩ t') := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have : z ∈ (⋂ i, K i) ∩ (t ∩ t') := ⟨hz.1, hz.2, hz'.2⟩
    rw [hemp] at this; exact this
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hAB
  have hsub : (⋂ i, K i) ⊆ U ∪ V := fun z hz => by
    rcases hcov hz with h | h
    · exact Or.inl (hAU ⟨hz, h⟩)
    · exact Or.inr (hBV ⟨hz, h⟩)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨i, hi⟩ := ((hc i₀).diff (hU.union hV)).elim_directed_family_closed K hcl
    (by rw [eq_empty_iff_forall_notMem]; rintro z ⟨⟨-, hz1⟩, hz2⟩; exact hz1 (hsub hz2)) hd
  obtain ⟨j, hj₀, hji⟩ := hd i₀ i
  have hKi : K j ⊆ U ∪ V := fun z hz => by
    by_contra h
    have : z ∈ (K i₀ \ (U ∪ V)) ∩ K i := ⟨⟨hj₀ hz, h⟩, hji hz⟩
    rw [hi] at this; exact this
  rcases isPreconnected_iff_subset_of_disjoint.1 (hp j) U V hU hV hKi
    (by rw [hUV.inter_eq, inter_empty]) with h | h
  · exact disjoint_left.1 hUV (h (mem_iInter.1 hyK j)) (hBV ⟨hyK, hyt'⟩)
  · exact disjoint_left.1 hUV (hAU ⟨hxK, hxt⟩) (h (mem_iInter.1 hxK j))

/-- The intersection of a nonempty chain of compacta meets a closed set `T` met by every member. -/
theorem sInter_chain_inter_nonempty {c : Set (Set X)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hc : ∀ W ∈ c, IsCompact W) {T : Set X} (hT : IsClosed T)
    (hWT : ∀ W ∈ c, (W ∩ T).Nonempty) : (⋂₀ c ∩ T).Nonempty := by
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ⊇ ·) (fun W : c => (W : Set X)) := directed_of_isChain_supset hch
  obtain ⟨W₀, hW₀⟩ := hne
  have := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun W : c => (W : Set X) ∩ T) ?_ (fun W => hWT W W.2)
    (fun W => (hc W W.2).inter_right hT) (fun W => (hc W W.2).isClosed.inter hT)
  · obtain ⟨z, hz⟩ := this
    rw [mem_iInter] at hz
    exact ⟨z, mem_sInter.2 fun W hW => (hz ⟨W, hW⟩).1, (hz ⟨W₀, hW₀⟩).2⟩
  · intro a b
    obtain ⟨d, hda, hdb⟩ := hdir a b
    exact ⟨d, inter_subset_inter_left _ hda, inter_subset_inter_left _ hdb⟩

/-- **§4.1, helper**: the intersection of a nonempty chain of continua is a continuum, and
continuous images commute with it. -/
theorem isContinuum_sInter_chain {c : Set (Set X)} (hne : c.Nonempty) (hch : IsChain (· ⊆ ·) c)
    (hc : ∀ W ∈ c, Fold.Q78.IsContinuum W) :
    Fold.Q78.IsContinuum (⋂₀ c) ∧ ∀ {E : Type*} [MetricSpace E] {φ : X → E}, Continuous φ →
      φ '' (⋂₀ c) = ⋂ W ∈ c, φ '' W := by
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ⊇ ·) (fun W : c => (W : Set X)) := directed_of_isChain_supset hch
  have key := fun T hT hWT => sInter_chain_inter_nonempty hne hch (fun W hW => (hc W hW).1)
    (T := T) hT hWT
  obtain ⟨W₀, hW₀⟩ := hne
  have hcpt : IsCompact (⋂₀ c) := (hc W₀ hW₀).1.of_isClosed_subset
    (isClosed_sInter fun W hW => (hc W hW).1.isClosed) (sInter_subset_of_mem hW₀)
  refine ⟨⟨hcpt, ?_, ?_⟩, ?_⟩
  · simpa using key univ isClosed_univ fun W hW => by simpa using (hc W hW).2.nonempty
  · rw [sInter_eq_iInter]
    exact isPreconnected_iInter_directed_compact _ hdir
      (fun W => (hc W W.2).1) (fun W => (hc W W.2).2.isPreconnected)
  · intro E _ φ hφ
    refine Subset.antisymm (subset_iInter₂ fun W hW => image_mono (sInter_subset_of_mem hW)) ?_
    intro y hy
    rw [mem_iInter₂] at hy
    obtain ⟨z, hz, hzy⟩ := key (φ ⁻¹' {y}) (isClosed_singleton.preimage hφ) fun W hW => by
      obtain ⟨z, hz, hzy⟩ := hy W hW
      exact ⟨z, hz, hzy⟩
    exact ⟨z, hz, hzy⟩

/-- **§4.1, Brouwer reduction.** -/
theorem brouwer_reduction {Z : Set X} (hZ : Fold.Q78.IsContinuum Z) (P : Set X → Prop) (hPZ : P Z)
    (hch : ∀ c : Set (Set X), c.Nonempty → IsChain (· ⊆ ·) c →
      (∀ W ∈ c, Fold.Q78.IsContinuum W ∧ W ⊆ Z ∧ P W) → P (⋂₀ c)) :
    ∃ Z₀ ⊆ Z, Fold.Q78.IsContinuum Z₀ ∧ P Z₀ ∧
      ∀ W ⊆ Z₀, Fold.Q78.IsContinuum W → P W → W = Z₀ := by
  set S : Set (Set X) := {W | W ⊆ Z ∧ Fold.Q78.IsContinuum W ∧ P W}
  obtain ⟨m, hm⟩ := zorn_superset S fun c hcS hc => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Z, ⟨subset_rfl, hZ, hPZ⟩, by simp⟩
    · have hall : ∀ W ∈ c, Fold.Q78.IsContinuum W ∧ W ⊆ Z ∧ P W :=
        fun W hW => ⟨(hcS hW).2.1, (hcS hW).1, (hcS hW).2.2⟩
      obtain ⟨W₀, hW₀⟩ := hne
      exact ⟨⋂₀ c, ⟨(sInter_subset_of_mem hW₀).trans (hcS hW₀).1,
        (isContinuum_sInter_chain.{_, 0} ⟨W₀, hW₀⟩ hc fun W hW => (hall W hW).1).1,
        hch c ⟨W₀, hW₀⟩ hc hall⟩, fun W hW => sInter_subset_of_mem hW⟩
  refine ⟨m, hm.prop.1, hm.prop.2.1, hm.prop.2.2, fun W hW hWc hPW => ?_⟩
  exact hm.eq_of_subset ⟨hW.trans hm.prop.1, hWc, hPW⟩ hW



/-- The component of a point in a closed set of a Hausdorff space is closed. -/
theorem isClosed_connectedComponentIn_of_isClosed' {Y : Type*} [TopologicalSpace Y]
    {F : Set Y} (hF : IsClosed F) (x : Y) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.1 ?_
    exact (isConnected_connectedComponentIn_iff.2 hx).closure.isPreconnected.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset _ _) hF)
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

/-- **§4.2, Davis 1984 (O–T Theorem 1.1) for hereditarily indecomposable `A`**. -/
theorem exists_surjSpanPos_of_surjSemiSpanPos {A : Set X} (hHI : IsHereditarilyIndecomposable A)
    (h : SurjSemiSpanPos A) : ∃ B ⊆ A, Fold.Q78.IsContinuum B ∧ SurjSpanPos B := by
  obtain ⟨Z, hZA, hZ, hoff, h1⟩ := h
  set P : Set (X × X) → Prop := fun W => Prod.snd '' W ⊆ Prod.fst '' W
  have hPZ : P Z := by
    show Prod.snd '' Z ⊆ Prod.fst '' Z
    rw [h1]; exact image_subset_iff.2 fun p hp => (hZA hp).2
  have hch : ∀ c : Set (Set (X × X)), c.Nonempty → IsChain (· ⊆ ·) c →
      (∀ W ∈ c, Fold.Q78.IsContinuum W ∧ W ⊆ Z ∧ P W) → P (⋂₀ c) := by
    intro c hne hc hall
    obtain ⟨-, himg⟩ := isContinuum_sInter_chain hne hc fun W hW => (hall W hW).1
    show Prod.snd '' ⋂₀ c ⊆ Prod.fst '' ⋂₀ c
    rw [himg continuous_snd, himg continuous_fst]
    exact iInter₂_mono fun W hW => (hall W hW).2.2
  obtain ⟨Z₀, hZ₀Z, hZ₀, hP₀, hmin⟩ := brouwer_reduction hZ P hPZ hch
  set B := Prod.fst '' Z₀ with hBdef
  have hBA : B ⊆ A := h1 ▸ image_mono hZ₀Z
  have hB : Fold.Q78.IsContinuum B :=
    ⟨hZ₀.1.image continuous_fst, hZ₀.2.image _ continuous_fst.continuousOn⟩
  have hQc : Fold.Q78.IsContinuum (Prod.snd '' Z₀) :=
    ⟨hZ₀.1.image continuous_snd, hZ₀.2.image _ continuous_snd.continuousOn⟩
  have hQB : Prod.snd '' Z₀ = B := by
    by_contra hne
    haveI : CompactSpace Z₀ := isCompact_iff_compactSpace.mp hZ₀.1
    haveI : ConnectedSpace Z₀ := isConnected_iff_connectedSpace.mp hZ₀.2
    set f : Z₀ → X := fun w => w.1.1 with hfdef
    have hf : Continuous f := continuous_fst.comp continuous_subtype_val
    have hS : range f = B := by
      rw [show f = Prod.fst ∘ Subtype.val from rfl, range_comp, Subtype.range_coe]
    obtain ⟨q, hq⟩ := hQc.2.nonempty
    obtain ⟨w, hw, hwq⟩ := hP₀ hq
    set x : Z₀ := ⟨w, hw⟩
    have hx : f x ∈ Prod.snd '' Z₀ := by show w.1 ∈ _; rw [hwq]; exact hq
    have hcook := cook67_theorem4 hf hS (hi_mono hHI hBA) hQc hP₀ hx
    set C := connectedComponentIn (f ⁻¹' (Prod.snd '' Z₀)) x
    have hCc : IsCompact C := (isClosed_connectedComponentIn_of_isClosed'
      (hQc.1.isClosed.preimage hf) x).isCompact
    set Z' : Set (X × X) := Subtype.val '' C
    have hZ'c : Fold.Q78.IsContinuum Z' :=
      ⟨hCc.image continuous_subtype_val, IsConnected.image (isConnected_connectedComponentIn_iff.2
        (show x ∈ f ⁻¹' (Prod.snd '' Z₀) from hx)) Subtype.val continuous_subtype_val.continuousOn⟩
    have hZ'1 : Prod.fst '' Z' = Prod.snd '' Z₀ := by
      rw [image_image]; exact hcook
    have hPZ' : P Z' := by
      show Prod.snd '' Z' ⊆ Prod.fst '' Z'
      rw [hZ'1]; exact image_mono (Subtype.coe_image_subset _ _)
    have := hmin Z' (Subtype.coe_image_subset _ _) hZ'c hPZ'
    rw [this] at hZ'1
    exact hne hZ'1.symm
  refine ⟨B, hBA, hB, Z₀, fun p hp => ⟨mem_image_of_mem _ hp, hQB ▸ mem_image_of_mem _ hp⟩, hZ₀,
    fun p hp => hoff p (hZ₀Z hp), rfl, hQB⟩

/-- **§4.2, corollary.** -/
theorem semiSpanZero_of_spanZero (hHI : IsHereditarilyIndecomposable (univ : Set X))
    (h : SpanZero X) : SemiSpanZero X := by
  intro A hA hpos
  obtain ⟨B, -, hB, hBpos⟩ := exists_surjSpanPos_of_surjSemiSpanPos (hi_mono hHI (subset_univ A)) hpos
  exact h B hB hBpos

end Davis

end HPC.Span
