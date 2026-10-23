import HPC.Span.Thm36
import HPC.Span.Reembed
import HPC.Span.Crossing

/-!
# Batch 191: Theorem C I — span; Cook 1967; Oversteegen–Tymchatyn 1982, Theorem 3.6 and
# Corollary 3.5 from the strip theorem

The skeleton of commission 191, split under `HPC/Span/`:
* `HPC/Span/Defs.lean` — §2 (definitions, §2.1–§2.4);
* `HPC/Span/Cook.lean` — §3 (Cook 1967, Theorem 4) and §4 (Brouwer reduction, Davis 1.1 for
  hereditarily indecomposable continua);
* `HPC/Span/Thm36.lean` — §5 (`OTCor35`, `TheoremC`, Theorem 3.6 from Corollary 3.5);
* `HPC/Span/Reembed.lean` — §6.1 (E1)–(E3);
* `HPC/Span/Crossing.lean` — §6.2;
* this file — §6.3 (`OTThm32`), §6.4 (Corollary 3.5 from Theorem 3.2), `theoremC_of_thm32`, §7.

Sources: L. G. Oversteegen and E. D. Tymchatyn, *Plane strips and the span of continua, (I)*,
Houston J. Math. 8 (1982), 129–142 (`doc/sources/oversteegen-tymchatyn1982.pdf`); H. Cook,
*Continua which admit only the identity mapping onto non-degenerate subcontinua*, Fund. Math. 60
(1967), 241–249 (`doc/sources/cook1967.pdf`). Route: commission 191.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Hagopian

/-! ## §6.3. The named claim -/

/-- **O–T Theorem 3.2, strip form** (commission §6.3), as a named claim: copies of `Y` hanging from
the left line of the strip `[0, 1] × ℝ`, inside pairwise disjoint crossing continua, with `y`
beyond `X`; only countably many copies of `X` have positive surjective span. -/
def OTThm32 : Prop :=
  ∀ {Y : Type} [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y] (X : Set Y) (x y : Y),
    Fold.Q78.IsContinuum X → x ∈ X →
    ∀ {ι : Type} (K : ι → Set Pt) (h : ι → Y → Pt),
      (∀ i, Fold.Q78.IsContinuum (K i) ∧ K i ⊆ Icc (0 : ℝ) 1 ×ˢ univ ∧
        (∃ z ∈ K i, z.1 = 0) ∧ ∃ z ∈ K i, z.1 = 1) →
      Pairwise (fun i j => Disjoint (K i) (K j)) →
      (∀ i, Continuous (h i) ∧ range (h i) ⊆ K i ∧ (h i x).1 = 0 ∧
        ∀ z ∈ X, (h i z).1 < (h i y).1) →
      {i | SurjSpanPos (h i '' X)}.Countable

/-! ## §6.4. Corollary 3.5 from Theorem 3.2 -/

section Cor35

variable {X : Type*} [MetricSpace X]

/-! ### Helpers for §6.4 -/

/-- A subset `S` of a set `T` is a continuum iff its preimage in the subtype `T` is. -/
theorem isContinuum_preimage_val_iff {E : Type*} [MetricSpace E] {S T : Set E} (hST : S ⊆ T) :
    Fold.Q78.IsContinuum (Subtype.val ⁻¹' S : Set T) ↔ Fold.Q78.IsContinuum S := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set T) = S := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hST]
  constructor
  · rintro ⟨hc, hne, hpc⟩
    rw [Subtype.isCompact_iff, himg] at hc
    rw [← IsInducing.subtypeVal.isPreconnected_image, himg] at hpc
    exact ⟨hc, by rw [← himg]; exact hne.image _, hpc⟩
  · rintro ⟨hc, hne, hpc⟩
    refine ⟨by rw [Subtype.isCompact_iff, himg]; exact hc, ?_, by
      rw [← IsInducing.subtypeVal.isPreconnected_image, himg]; exact hpc⟩
    obtain ⟨z, hz⟩ := hne
    exact ⟨⟨z, hST hz⟩, hz⟩

/-- **Pull-back of positive span** along an injective inducing map. -/
theorem SurjSpanPos.of_image {Y : Type*} [MetricSpace Y] {f : Y → X} (hf : IsInducing f)
    (hinj : Function.Injective f) {S : Set Y} (h : SurjSpanPos (f '' S)) : SurjSpanPos S := by
  obtain ⟨Z, hZS, hZ, hoff, h1, h2⟩ := h
  have hF : IsInducing (Prod.map f f) := hf.prodMap hf
  have hZr : Z ⊆ range (Prod.map f f) := by
    intro p hp
    obtain ⟨⟨a, -, ha⟩, ⟨b, -, hb⟩⟩ := hZS hp
    exact ⟨(a, b), Prod.ext ha hb⟩
  set Z' := Prod.map f f ⁻¹' Z
  have himg : Prod.map f f '' Z' = Z := image_preimage_eq_of_subset hZr
  have hmem : ∀ {a : Y}, f a ∈ f '' S → a ∈ S := fun {a} ⟨s, hs, hsa⟩ => hinj hsa ▸ hs
  refine ⟨Z', fun p hp => ⟨hmem (hZS hp).1, hmem (hZS hp).2⟩,
    ⟨hF.isCompact_preimage' hZ.1 hZr, ?_, ?_⟩, fun p hp h => hoff _ hp (by simp [h]), ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hZ.2.nonempty
    obtain ⟨p', rfl⟩ := hZr hp
    exact ⟨p', hp⟩
  · rw [← hF.isPreconnected_image, himg]; exact hZ.2.isPreconnected
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩; exact hmem (hZS hp).1
    · intro s hs
      obtain ⟨p, hp, hps⟩ := h1.symm ▸ mem_image_of_mem f hs
      obtain ⟨p', rfl⟩ := hZr hp
      exact ⟨p', hp, hinj hps⟩
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩; exact hmem (hZS hp).2
    · intro s hs
      obtain ⟨p, hp, hps⟩ := h2.symm ▸ mem_image_of_mem f hs
      obtain ⟨p', rfl⟩ := hZr hp
      exact ⟨p', hp, hinj hps⟩

/-- Homogeneity is invariant under homeomorphism. -/
theorem isHomogeneous_of_homeomorph {Y : Type*} [TopologicalSpace Y] {W : Type*}
    [TopologicalSpace W] (e : W ≃ₜ Y) (h : IsHomogeneous W) : IsHomogeneous Y := by
  intro x y
  obtain ⟨g, hg⟩ := h (e.symm x) (e.symm y)
  exact ⟨(e.symm.trans g).trans e, by simp [hg]⟩

/-- Indecomposability is invariant under homeomorphism. -/
theorem not_isDecomposableSpace_of_homeomorph {Y : Type*} [MetricSpace Y] (e : X ≃ₜ Y)
    (h : ¬ IsDecomposableSpace X) : ¬ IsDecomposableSpace Y := by
  rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
  refine h ⟨e.symm '' H, e.symm '' K, ⟨hH.1.image e.symm.continuous,
    hH.2.image _ e.symm.continuous.continuousOn⟩, ⟨hK.1.image e.symm.continuous,
    hK.2.image _ e.symm.continuous.continuousOn⟩, fun h' => hHu ?_, fun h' => hKu ?_, ?_⟩
  · simpa [image_image] using congrArg (e '' ·) h'
  · simpa [image_image] using congrArg (e '' ·) h'
  · rw [← image_union, hHK, image_univ, e.symm.range_coe]

/-- Under the sup metric, nearby points have nearby first coordinates. -/
theorem fst_lt_of_dist_lt {a b : Pt} {η : ℝ} (h : dist a b < η) : a.1 < b.1 + η := by
  have : dist a.1 b.1 < η := lt_of_le_of_lt (le_max_left _ _) h
  rw [Real.dist_eq] at this
  linarith [le_abs_self (a.1 - b.1)]

/-- **§6.4, steps 6–9** (the core): the plane continuum `N`, in `x ≥ 0` with the unique point `x₀`
on `x = 0`, contains a continuum `A ∋ x₀` of positive span and a point `q` to the right of `A`.
Then Theorem 3.2 (strip form) fails. -/
theorem cor35_core (h32 : OTThm32) (N : Set Pt) [CompactSpace N] [ConnectedSpace N]
    (hom : IsHomogeneous N) (hi : ¬ IsDecomposableSpace N) (hN0 : ∀ z ∈ N, 0 ≤ z.1) {x₀ : Pt}
    (hx₀N : x₀ ∈ N) (hx₀0 : x₀.1 = 0) (hx₀ : ∀ z ∈ N, z.1 = 0 → z = x₀) {A : Set Pt}
    (hAN : A ⊆ N) (hA : Fold.Q78.IsContinuum A) (hx₀A : x₀ ∈ A) (hpos : SurjSpanPos A) {q : Pt}
    (hqN : q ∈ N) (hq : ∀ z ∈ A, z.1 < q.1) : False := by
  have hHI := hagopian76_theorem1 N hom hi
  have hNc : IsCompact N := isCompact_iff_compactSpace.2 ‹_›
  -- step 6: constants
  obtain ⟨as, has, hsmax⟩ := hA.1.exists_isMaxOn hA.2.nonempty continuous_fst.continuousOn
  obtain ⟨nm, hnm, hmmax⟩ := hNc.exists_isMaxOn ⟨x₀, hx₀N⟩ continuous_fst.continuousOn
  set s := as.1
  set m := nm.1
  have hs0 : 0 ≤ s := hN0 _ (hAN has)
  have hsm : s < m := lt_of_lt_of_le (hq as has) (hmmax hqN)
  set η := (m - s) / 8 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set r := s + 4 * η with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrm : r < m := by rw [hrdef, hηdef]; linarith
  obtain ⟨δ, hδ, heff⟩ := HPC.Effros.effros_homogeneous hom hη
  obtain ⟨ε, hε, hεr, hεδ⟩ : ∃ ε, 0 < ε ∧ ε < r ∧ ∀ z ∈ N, z.1 ≤ ε → dist z x₀ < δ := by
    set C := N \ ball x₀ δ
    rcases C.eq_empty_or_nonempty with hC | hC
    · refine ⟨r / 2, by linarith, by linarith, fun z hz _ => ?_⟩
      by_contra h
      exact (hC ▸ (⟨hz, h⟩ : z ∈ C) : z ∈ (∅ : Set Pt))
    · obtain ⟨c, hcC, hcmin⟩ := (hNc.diff isOpen_ball).exists_isMinOn hC
        continuous_fst.continuousOn
      have hc0 : 0 < c.1 := by
        rcases (hN0 c hcC.1).lt_or_eq with h | h
        · exact h
        · exact absurd (hx₀ c hcC.1 h.symm ▸ mem_ball_self hδ) hcC.2
      refine ⟨min (c.1 / 2) (r / 2), lt_min (by linarith) (by linarith),
        lt_of_le_of_lt (min_le_right _ _) (by linarith), fun z hz hzε => ?_⟩
      by_contra h
      have h1 : c.1 ≤ z.1 := hcmin (show z ∈ C from ⟨hz, h⟩)
      have h2 := min_le_left (c.1 / 2) (r / 2)
      linarith
  -- step 7: the family
  obtain ⟨𝒦, h𝒦c, h𝒦d, h𝒦⟩ := exists_uncountable_crossing N hi hεr
    ⟨x₀, hx₀N, by rw [hx₀0]; exact hε⟩ ⟨nm, hnm, hrm⟩
  -- step 8
  have hxK : ∀ K ∈ 𝒦, ∃ xK ∈ K, xK.1 = ε := fun K hK => (h𝒦 K hK).2.2.1
  have hkK : ∀ K ∈ 𝒦, ∃ kK ∈ K, kK.1 = r := fun K hK => (h𝒦 K hK).2.2.2
  choose! xK hxKK hxKε using hxK
  choose! kK hkKK hkKr using hkK
  have hxKN : ∀ K ∈ 𝒦, xK K ∈ N := fun K hK => ((h𝒦 K hK).1 (hxKK K hK)).1
  have hkKN : ∀ K ∈ 𝒦, kK K ∈ N := fun K hK => ((h𝒦 K hK).1 (hkKK K hK)).1
  set x₀' : N := ⟨x₀, hx₀N⟩
  haveI : Nonempty (N ≃ₜ N) := ⟨Homeomorph.refl N⟩
  have hheff : ∀ K (hK : K ∈ 𝒦), ∃ g : N ≃ₜ N, g x₀' = ⟨xK K, hxKN K hK⟩ ∧
      ∀ z, dist (g z) z < η := by
    intro K hK
    apply heff
    show dist x₀ (xK K) < δ
    rw [dist_comm]
    exact hεδ _ (hxKN K hK) (hxKε K hK).le
  choose! g hgx hgmove using hheff
  set A' : Set N := Subtype.val ⁻¹' A
  have hA' : Fold.Q78.IsContinuum A' := (isContinuum_preimage_val_iff hAN).2 hA
  have hx₀A' : x₀' ∈ A' := hx₀A
  have hKN : ∀ K ∈ 𝒦, K ⊆ N := fun K hK z hz => ((h𝒦 K hK).1 hz).1
  have hK' : ∀ K ∈ 𝒦, Fold.Q78.IsContinuum (Subtype.val ⁻¹' K : Set N) := fun K hK =>
    (isContinuum_preimage_val_iff (hKN K hK)).2 (h𝒦 K hK).2.1
  have hmove1 : ∀ K ∈ 𝒦, ∀ z : N, ((g K z : N) : Pt).1 < (z : Pt).1 + η := fun K hK z =>
    fst_lt_of_dist_lt (hgmove K hK z)
  have hmove2 : ∀ K ∈ 𝒦, ∀ z : N, (z : Pt).1 < ((g K z : N) : Pt).1 + η := fun K hK z =>
    fst_lt_of_dist_lt (by rw [dist_comm]; exact hgmove K hK z)
  have hgA : ∀ K ∈ 𝒦, g K '' A' ⊆ Subtype.val ⁻¹' K := by
    intro K hK
    have hc : Fold.Q78.IsContinuum (g K '' A') :=
      ⟨hA'.1.image (g K).continuous, hA'.2.image _ (g K).continuous.continuousOn⟩
    rcases nested_of_hi hHI hc (hK' K hK) (subset_univ _) (subset_univ _)
        ⟨g K x₀', mem_image_of_mem _ hx₀A', by
          show ((g K x₀' : N) : Pt) ∈ K; rw [hgx K hK]; exact hxKK K hK⟩ with h | h
    · exact h
    · exfalso
      obtain ⟨a, haA, ha⟩ := h (show (⟨kK K, hkKN K hK⟩ : N) ∈ Subtype.val ⁻¹' K from hkKK K hK)
      have h1 := hmove1 K hK a
      rw [ha] at h1
      have h2 : (a : Pt).1 ≤ s := hsmax haA
      simp only at h1
      rw [hkKr K hK] at h1
      linarith
  -- the continua `B_K` and their intersection `B`
  set c : Set (Set N) := (fun K => g K ⁻¹' (Subtype.val ⁻¹' K)) '' 𝒦
  have hcA : ∀ W ∈ c, A' ⊆ W := by
    rintro _ ⟨K, hK, rfl⟩ a ha
    exact hgA K hK (mem_image_of_mem _ ha)
  have hcC : ∀ W ∈ c, Fold.Q78.IsContinuum W := by
    rintro _ ⟨K, hK, rfl⟩
    show Fold.Q78.IsContinuum (g K ⁻¹' (Subtype.val ⁻¹' K))
    rw [← (g K).image_symm]
    exact ⟨(hK' K hK).1.image (g K).symm.continuous,
      (hK' K hK).2.image _ (g K).symm.continuous.continuousOn⟩
  have hch : IsChain (· ⊆ ·) c := by
    rintro W₁ hW₁ W₂ hW₂ -
    exact nested_of_hi hHI (hcC W₁ hW₁) (hcC W₂ hW₂) (subset_univ _) (subset_univ _)
      ⟨x₀', hcA W₁ hW₁ hx₀A', hcA W₂ hW₂ hx₀A'⟩
  have h𝒦ne : 𝒦.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact h𝒦c (h ▸ countable_empty)
  have hcne : c.Nonempty := h𝒦ne.image _
  set B := ⋂₀ c
  have hB : Fold.Q78.IsContinuum B := (isContinuum_sInter_chain.{_, 0} hcne hch hcC).1
  have hA'B : A' ⊆ B := fun a ha => mem_sInter.2 fun W hW => hcA W hW ha
  obtain ⟨y, hyB, hyr⟩ := sInter_chain_inter_nonempty hcne hch (fun W hW => (hcC W hW).1)
    (T := {z : N | r - η ≤ (z : Pt).1})
    (isClosed_le continuous_const (continuous_fst.comp continuous_subtype_val)) (by
      rintro _ ⟨K, hK, rfl⟩
      refine ⟨(g K).symm ⟨kK K, hkKN K hK⟩, ?_, ?_⟩
      · show ((g K ((g K).symm ⟨kK K, hkKN K hK⟩) : N) : Pt) ∈ K
        rw [Homeomorph.apply_symm_apply]; exact hkKK K hK
      · have := hmove1 K hK ((g K).symm ⟨kK K, hkKN K hK⟩)
        rw [Homeomorph.apply_symm_apply] at this
        show r - η ≤ _
        simp only at this
        rw [hkKr K hK] at this
        linarith)
  have hgB : ∀ K ∈ 𝒦, ∀ w ∈ B, ((g K w : N) : Pt) ∈ K := fun K hK w hw =>
    mem_sInter.1 hw _ ⟨K, hK, rfl⟩
  -- step 9: Theorem 3.2
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB.1
  haveI : ConnectedSpace B := isConnected_iff_connectedSpace.mp hB.2
  set ρ : Pt → Pt := fun z => ((z.1 - ε) / (r - ε), z.2) with hρdef
  have hrε : 0 < r - ε := by linarith
  have hρc : Continuous ρ := by rw [hρdef]; fun_prop
  have hρinj : Function.Injective ρ := by
    intro z w h
    simp only [hρdef, Prod.mk.injEq] at h
    refine Prod.ext ?_ h.2
    have := h.1
    field_simp at this
    linarith
  have hρmono : ∀ z w : Pt, z.1 < w.1 → (ρ z).1 < (ρ w).1 := fun z w h => by
    simp only [hρdef]
    exact div_lt_div_of_pos_right (by linarith) hrε
  set Xs : Set B := Subtype.val ⁻¹' A'
  have hXs : Fold.Q78.IsContinuum Xs := (isContinuum_preimage_val_iff hA'B).2 hA'
  set xs : B := ⟨x₀', hA'B hx₀A'⟩
  set ys : B := ⟨y, hyB⟩
  set Kf : 𝒦 → Set Pt := fun K => ρ '' K.1
  set hf : 𝒦 → B → Pt := fun K w => ρ ((g K.1 w.1 : N) : Pt)
  have hfc : ∀ K : 𝒦, Continuous (hf K) := fun K =>
    hρc.comp (continuous_subtype_val.comp ((g K.1).continuous.comp continuous_subtype_val))
  have hfinj : ∀ K : 𝒦, Function.Injective (hf K) := fun K w w' h =>
    Subtype.ext ((g K.1).injective (Subtype.ext (hρinj h)))
  have hcount := h32 (Y := B) Xs xs ys hXs hx₀A' (ι := 𝒦) Kf hf
    (by
      intro K
      obtain ⟨hKsub, hKc, ⟨z₁, hz₁, hz₁a⟩, ⟨z₂, hz₂, hz₂b⟩⟩ := h𝒦 K.1 K.2
      refine ⟨⟨hKc.1.image hρc, hKc.2.image _ hρc.continuousOn⟩, ?_, ⟨ρ z₁, mem_image_of_mem _ hz₁,
        by simp [hρdef, hz₁a]⟩, ⟨ρ z₂, mem_image_of_mem _ hz₂, by
          simp only [hρdef, hz₂b]; exact div_self hrε.ne'⟩⟩
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨-, ⟨h1, h2⟩, -⟩ := hKsub hz
      refine ⟨⟨div_nonneg (by linarith) hrε.le, (div_le_one hrε).2 (by linarith)⟩, mem_univ _⟩)
    (by
      intro K L hKL
      have hne : K.1 ≠ L.1 := fun h => hKL (Subtype.ext h)
      have := h𝒦d K.2 L.2 hne
      rw [Function.onFun, id, id] at this
      exact (disjoint_image_iff hρinj).2 this)
    (by
      intro K
      refine ⟨hfc K, ?_, ?_, ?_⟩
      · rintro _ ⟨w, rfl⟩
        exact mem_image_of_mem _ (hgB K.1 K.2 w.1 w.2)
      · show (ρ ((g K.1 x₀' : N) : Pt)).1 = 0
        rw [hgx K.1 K.2]
        simp [hρdef, hxKε K.1 K.2]
      · intro z hz
        apply hρmono
        have h1 := hmove1 K.1 K.2 z.1
        have h2 := hmove2 K.1 K.2 y
        have h3 : ((z.1 : N) : Pt).1 ≤ s := hsmax hz
        have h4 : r - η ≤ (y : Pt).1 := hyr
        show ((g K.1 z.1 : N) : Pt).1 < ((g K.1 y : N) : Pt).1
        rw [hrdef] at h4
        linarith)
  -- every copy has positive span
  have hXpos : SurjSpanPos Xs := by
    apply SurjSpanPos.of_image (f := fun w : B => (w.1 : Pt))
      (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
      (Subtype.val_injective.comp Subtype.val_injective)
    have : (fun w : B => (w.1 : Pt)) '' Xs = A := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact hw
      · intro hz
        exact ⟨⟨⟨z, hAN hz⟩, hA'B hz⟩, hz, rfl⟩
    rw [this]; exact hpos
  have hall : {K : 𝒦 | SurjSpanPos (hf K '' Xs)} = univ :=
    eq_univ_of_forall fun K => hXpos.image (hfc K) (hfinj K).injOn
  rw [hall, countable_univ_iff, countable_coe_iff] at hcount
  exact h𝒦c hcount

/-- **O–T Corollary 3.5** from Theorem 3.2 (commission §6.4). -/
theorem ot82_cor35_of_thm32 (h32 : OTThm32) : OTCor35 := by
  intro M _ _ hX hi A₀ hA₀ hA₀u hpos₀
  have hHI := hagopian76_theorem1 M hX hi
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 ‹_›
  -- step 2 (Davis)
  obtain ⟨A₁, hA₁A₀, hA₁, hpos₁⟩ :=
    exists_surjSpanPos_of_surjSemiSpanPos (fun K hK hKc => hHI K (subset_univ K) hKc) hpos₀
  have hA₁u : A₁ ≠ univ := fun h => hA₀u (eq_univ_of_univ_subset (h ▸ hA₁A₀))
  -- step 3 (E1)
  obtain ⟨z₀, -⟩ := hA₁.2.nonempty
  obtain ⟨Φ, x₀, hx₀M, hΦx₀, hΦpos⟩ := exists_homeomorph_unique_leftmost hMc ⟨z₀.1, z₀.2⟩
  set M' := Φ '' M
  haveI : CompactSpace M' := isCompact_iff_compactSpace.mp (hMc.image Φ.continuous)
  haveI : ConnectedSpace M' := isConnected_iff_connectedSpace.mp
    ((isConnected_iff_connectedSpace.mpr ‹ConnectedSpace M›).image _ Φ.continuous.continuousOn)
  set e₁ : M ≃ₜ M' := Φ.image M
  have hX' : IsHomogeneous M' := isHomogeneous_of_homeomorph e₁ hX
  have hi' : ¬ IsDecomposableSpace M' := not_isDecomposableSpace_of_homeomorph e₁ hi
  set x₀' : Pt := Φ x₀
  have hx₀'M : x₀' ∈ M' := mem_image_of_mem _ hx₀M
  have hM'0 : ∀ z ∈ M', 0 ≤ z.1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases h : z = x₀
    · rw [h, hΦx₀]
    · exact (hΦpos z hz h).le
  have hM'x₀ : ∀ z ∈ M', z.1 = 0 → z = x₀' := by
    rintro _ ⟨z, hz, rfl⟩ h
    by_cases h' : z = x₀
    · rw [h']
    · exact absurd h (hΦpos z hz h').ne'
  -- step 4 (homogeneity)
  obtain ⟨a₁, ha₁⟩ := hA₁.2.nonempty
  obtain ⟨gh, hgh⟩ := hX' (e₁ a₁) ⟨x₀', hx₀'M⟩
  set φ : M → Pt := fun w => ((gh (e₁ w) : M') : Pt)
  have hφc : Continuous φ :=
    continuous_subtype_val.comp (gh.continuous.comp e₁.continuous)
  have hφinj : Function.Injective φ := fun w w' h =>
    e₁.injective (gh.injective (Subtype.ext h))
  set A := φ '' A₁
  have hA : Fold.Q78.IsContinuum A := ⟨hA₁.1.image hφc, hA₁.2.image _ hφc.continuousOn⟩
  have hposA : SurjSpanPos A := hpos₁.image hφc hφinj.injOn
  have hx₀A : x₀' ∈ A := ⟨a₁, ha₁, by simp only [φ]; rw [hgh]⟩
  have hAM' : A ⊆ M' := by rintro _ ⟨w, -, rfl⟩; exact (gh (e₁ w)).2
  set A₂ : Set M' := gh '' (e₁ '' A₁)
  have hA₂ : Fold.Q78.IsContinuum A₂ :=
    ⟨(hA₁.1.image e₁.continuous).image gh.continuous,
      (hA₁.2.image _ e₁.continuous.continuousOn).image _ gh.continuous.continuousOn⟩
  have hA₂u : A₂ ≠ univ := by
    intro h
    apply hA₁u
    refine eq_univ_of_forall fun w => ?_
    obtain ⟨_, ⟨v, hv, rfl⟩, hvw⟩ := (h ▸ mem_univ (gh (e₁ w)) : gh (e₁ w) ∈ A₂)
    exact e₁.injective (gh.injective hvw) ▸ hv
  have hA₂A : toPt A₂ = A := by
    simp only [toPt, A₂, A, φ, image_image]
  -- step 5 (E2, E3)
  have hns : ¬ SeparatesPlane A := hA₂A ▸ no_proper_subcontinuum_separates hX' hi' hA₂ hA₂u
  have hUc := isConnected_rightHalf_diff hA hns (x₀ := x₀') fun z hz h => hM'x₀ z (hAM' hz) h
  set U := {z : Pt | 0 < z.1} \ A
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_fst).sdiff hA.1.isClosed
  obtain ⟨p, hpM', hpA⟩ : ∃ p ∈ M', p ∉ A := by
    by_contra h
    push_neg at h
    apply hA₂u
    refine eq_univ_of_forall fun w => ?_
    obtain ⟨v, hv, hvw⟩ := hA₂A.symm ▸ h w.1 w.2
    exact Subtype.ext hvw ▸ hv
  have hpU : p ∈ U := by
    refine ⟨?_, hpA⟩
    rcases (hM'0 p hpM').lt_or_eq with h | h
    · exact h
    · exact absurd (hM'x₀ p hpM' h.symm ▸ hx₀A) hpA
  obtain ⟨as, has, hsmax⟩ := hA.1.exists_isMaxOn hA.2.nonempty continuous_fst.continuousOn
  set q : Pt := (as.1 + 1, 0)
  have hqA : ∀ z ∈ A, z.1 < q.1 := fun z hz => by
    have h1 : z.1 ≤ as.1 := hsmax hz
    show z.1 < as.1 + 1
    linarith
  have hqU : q ∈ U := by
    refine ⟨?_, fun h => (lt_irrefl _ (hqA q h))⟩
    have := hM'0 as (hAM' has)
    show 0 < as.1 + 1
    linarith
  obtain ⟨T, hTp, hTU⟩ := exists_homeomorph_push hUo hUc hpU hqU
  have hTUU : ∀ z ∈ U, T z ∈ U := by
    intro z hz
    by_contra h
    have : T (T z) = T z := hTU _ h
    have := T.injective this
    rw [this] at h
    exact h hz
  set M'' := T '' M'
  haveI : CompactSpace M'' := isCompact_iff_compactSpace.mp
    ((isCompact_iff_compactSpace.2 ‹CompactSpace M'›).image T.continuous)
  haveI : ConnectedSpace M'' := isConnected_iff_connectedSpace.mp
    ((isConnected_iff_connectedSpace.mpr ‹ConnectedSpace M'›).image _ T.continuous.continuousOn)
  set e₂ : M' ≃ₜ M'' := T.image M'
  have hAfix : ∀ z ∈ A, T z = z := fun z hz => hTU z fun h => h.2 hz
  refine cor35_core h32 M'' (isHomogeneous_of_homeomorph e₂ hX')
    (not_isDecomposableSpace_of_homeomorph e₂ hi') ?_ (x₀ := x₀')
    ⟨x₀', hx₀'M, hAfix x₀' hx₀A⟩ ?_ ?_ (fun z hz => ⟨z, hAM' hz, hAfix z hz⟩) hA hx₀A hposA
    ⟨p, hpM', hTp⟩ hqA
  · rintro _ ⟨z, hz, rfl⟩
    by_cases h : z ∈ U
    · exact (hTUU z h).1.le
    · rw [hTU z h]; exact hM'0 z hz
  · show x₀'.1 = 0
    exact hΦx₀
  · rintro _ ⟨z, hz, rfl⟩ h0
    by_cases h : z ∈ U
    · exact absurd h0 (hTUU z h).1.ne'
    · rw [hTU z h] at h0 ⊢; exact hM'x₀ z hz h0

end Cor35

/-- **Theorem C from Theorem 3.2.** -/
theorem theoremC_of_thm32 (h32 : OTThm32) : TheoremC :=
  theoremC_of_cor35 (ot82_cor35_of_thm32 h32)

/-! ## §7. `crossing_traces_separated`: proved in batch 192, see `HPC/Span/OT82Order.lean`. -/

end HPC.Span
