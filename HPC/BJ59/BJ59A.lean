import HPC.BJ59.Decomp
import HPC.BJ59.Thm56
import HPC.BJ59.Thm5

/-!
# Batch 198: Part G, I — the circle of pseudo-arcs (Bing–Jones 1959), top down

The skeleton of commission 198, §§4–6 (the definitions and named inputs of §§2–3 are in
`HPC/BJ59/Defs.lean`, verbatim). Library lemmas are in the other files of `HPC/BJ59/`.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
171–192 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Route: commission 198.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §4. From Theorem 10: homogeneity and uniqueness of circles of pseudo-arcs -/

/-- **Each circle of pseudo-arcs is homogeneous** (Bing–Jones pp. 173, 189, "It follows from
Theorem 10"; the step is supplied by commission §4). -/
theorem isHomogeneous_of_isCircleOfPA (h10 : BJThm10) {X : Type} [MetricSpace X]
    (hX : IsCircleOfPA X) : IsHomogeneous X := by
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hX
  exact isHomogeneous_of_isCircPAMap h10 hf

/-- **Any two circles of pseudo-arcs are homeomorphic** (Bing–Jones pp. 173, 189). -/
theorem homeomorph_of_isCircleOfPA (h10 : BJThm10) {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (hX : IsCircleOfPA X) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) := by
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hX
  obtain ⟨g, hg⟩ := isCircleOfPA_iff.1 hY
  exact homeomorph_of_isCircPAMap h10 hf hg

/-! ## §5. The decomposable case and the classification -/

/-- The circle is homogeneous. -/
theorem isHomogeneous_circle : IsHomogeneous Circle := by
  exact isHomogeneous_circle'

/-- **Jones's elements are pseudo-arcs** (Jones 1955 Theorem 2 with Part F), unconditional: in a
decomposable homogeneous plane continuum, each non-degenerate element of Jones's decomposition is
a pseudo-arc. -/
theorem isPseudoArc_Lset {M : Set Pt} [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hd : IsDecomposableSpace M) (x : M) (hnt : (Lset x).Nontrivial) : IsPseudoArc (Lset x) := by
  exact isPseudoArc_Lset' hX hd x hnt

/-- **The decomposable case**: a decomposable homogeneous plane continuum is a simple closed curve
or a circle of pseudo-arcs. -/
theorem circle_or_circleOfPA_of_decomposable (hCL : HOCircleLike) {M : Set Pt} [CompactSpace M]
    [ConnectedSpace M] (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ IsCircleOfPA M := by
  rcases circle_or_circPAMap_of_decomposable hX hd (hCL M ‹_› ‹_› hX hd) with h | h
  · exact Or.inl h
  · exact Or.inr (isCircleOfPA_iff.2 h)

/-- **The classification, both directions** (H–O p. 180, with Bing–Jones for the third class). -/
theorem ho16_classification (h10 : BJThm10) (hCL : HOCircleLike) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  constructor
  · intro hX
    by_cases hd : IsDecomposableSpace M
    · rcases circle_or_circleOfPA_of_decomposable hCL hX hd with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ((ho16_indec_homogeneous_iff M hnt).1 ⟨hX, hd⟩))
  · rintro (he | h | h)
    · obtain ⟨e⟩ := he
      exact IsHomogeneous.of_homeomorph e.symm isHomogeneous_circle
    · exact (ho16_pseudoArc_indec_homogeneous M h).1
    · exact isHomogeneous_of_isCircleOfPA h10 h

/-- **The classification of homogeneous plane continua**: there are three plane continua, the
circle, the pseudo-arc and a circle of pseudo-arcs, each homogeneous, no two homeomorphic, and
every non-degenerate plane continuum is homogeneous iff it is homeomorphic to one of them. -/
theorem ho16_classification_plane (h10 : BJThm10) (hCL : HOCircleLike) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  obtain ⟨C₁, ⟨e₁⟩⟩ := exists_plane_circle
  obtain ⟨C₂, hC₂⟩ := isPseudoArc_plane
  obtain ⟨C₃, hC₃⟩ := hEx
  have hom₁ : IsHomogeneous C₁ := IsHomogeneous.of_homeomorph e₁.symm isHomogeneous_circle
  have hom₂ : IsHomogeneous C₂ := fun x y => by
    obtain ⟨T, hT⟩ := homogeneous_of_isPseudoArc hC₂ x y x.2 y.2
    exact ⟨T, hT⟩
  have hom₃ : IsHomogeneous C₃ := isHomogeneous_of_isCircleOfPA h10 hC₃
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC₃
  have hd₁ : IsDecomposableSpace C₁ := IsDecomposableSpace.of_homeomorph e₁.symm
    isDecomposableSpace_circle
  have hd₂ : ¬ IsDecomposableSpace C₂ := not_isDecomposableSpace_of_isIndecomposable_univ
    (isIndecomposable_univ_of_isIndecomposable (hC₂.2.1 C₂ subset_rfl hC₂.1.1))
  have hd₃ : IsDecomposableSpace C₃ := isDecomposableSpace_of_isCircPAMap hf
  have h13 : IsEmpty (C₁ ≃ₜ C₃) := by
    refine ⟨fun Φ => ?_⟩
    set ψ : C₃ ≃ₜ Circle := Φ.symm.trans e₁
    set F : Set C₃ := f ⁻¹' {1}
    have hK : IsPseudoArc (ψ '' F) := isPseudoArc_of_homeomorph (hf.fib 1) (ψ.image F)
    refine not_isPseudoArc_of_ne_univ_circle (fun hu => ?_) hK
    obtain ⟨x, hx⟩ := hf.surj (Circle.exp Real.pi)
    obtain ⟨y, hy, hyx⟩ : ψ x ∈ ψ '' F := hu ▸ mem_univ _
    have : y = x := ψ.injective hyx
    subst this
    have h1 : f y = 1 := hy
    rw [hx] at h1
    exact circle_exp_pi_ne_one h1
  refine ⟨C₁, C₂, C₃, ⟨⟨e₁⟩, hC₂, hC₃⟩, ⟨hom₁, hom₂, hom₃⟩,
    ⟨⟨fun Φ => hd₂ (IsDecomposableSpace.of_homeomorph Φ hd₁)⟩, h13,
      ⟨fun Φ => hd₂ (IsDecomposableSpace.of_homeomorph Φ.symm hd₃)⟩⟩, ?_⟩
  intro M hMc hMk hMnt
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.1 hMk
  have hnt : (univ : Set M).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hMnt
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩
  constructor
  · intro hX
    rcases (ho16_classification h10 hCL M hnt).1 hX with he | h | h
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨e.trans e₁.symm⟩
    · obtain ⟨e⟩ := theorem1_HIC' h hC₂
      exact Or.inr (Or.inl ⟨(Homeomorph.Set.univ M).symm.trans e⟩)
    · exact Or.inr (Or.inr (homeomorph_of_isCircleOfPA h10 h hC₃))
  · rintro (he | he | he) <;> obtain ⟨e⟩ := he
    · exact IsHomogeneous.of_homeomorph e.symm hom₁
    · exact IsHomogeneous.of_homeomorph e.symm hom₂
    · exact IsHomogeneous.of_homeomorph e.symm hom₃

/-! ## §6. Bing–Jones §§3–4: snake-like arcs of continua; chain maps -/

section Section3

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Bing–Jones, Theorem 2** (p. 174). -/
theorem bj_theorem2 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {a b c d : unitInterval} (h0a : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hd1 : d < 1) :
    ∃ ε > 0, ∀ (n : ℕ) (D : Chain X n), IsEpsChain D ε → univ ⊆ D.union →
      ∀ i j k : Fin n, (D.link i ∩ f ⁻¹' Icc 0 a).Nonempty →
        (D.link j ∩ f ⁻¹' Icc b c).Nonempty → (D.link k ∩ f ⁻¹' Icc d 1).Nonempty →
          (i < j ∧ j < k) ∨ (k < j ∧ j < i) := by
  exact theorem2_arc hf.1 hf.2.1 (fun t => (hf.2.2 t).2.isPreconnected) hab hbc hcd

/-- **Bing–Jones, Theorem 3** (pp. 174–175): an `ε`-chain from `g₀` to `g₁`. -/
theorem bj_theorem3 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain X (m + 1)), IsEpsChain D ε ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ f ⁻¹' {0}).Nonempty ∧ (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty := by
  exact theorem3_arc hf.1 hf.2.1 (fun t => (hf.2.2 t).2.isPreconnected) hS hε

/-- **Bing–Jones, Theorem 4** (p. 175): a non-empty open set missing the end elements separates
them. -/
theorem bj_theorem4 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hU01 : Disjoint U (f ⁻¹' {0, 1})) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B := by
  obtain ⟨p, hp⟩ := hUne
  have hε := posFn_pos hU hp
  obtain ⟨m, D, hD, hcov, h0, h1⟩ :=
    theorem3_arc hf.1 hf.2.1 (fun t => (hf.2.2 t).2.isPreconnected) hS hε
  obtain ⟨l, hl⟩ := mem_iUnion.1 (hcov (mem_univ p))
  have hlU : D.link l ⊆ U := by
    intro y hy
    by_contra hyU
    have hdist : dist p y < posFn U p :=
      lt_of_le_of_lt (dist_le_diam_of_mem (hD l).1 hl hy) (hD l).2
    have hpos : posFn U p = infDist p Uᶜ := by unfold posFn; rw [if_pos ⟨y, hyU⟩]
    rw [hpos] at hdist
    exact absurd (infDist_le_dist_of_mem (show y ∈ Uᶜ from hyU)) (not_le.2 hdist)
  exact theorem4_of_chain hU hU01 (hf.2.2 0).2.isPreconnected (hf.2.2 1).2.isPreconnected D hcov
    h0 h1 l hlU

/-- **Bing–Jones, Theorem 5, repaired** (pp. 175–176; stretch). Changed hypotheses (commission
§6): `f` open, and no fibre meets a link only inside `Ū` (`hEU`, which implies Bing–Jones's
"E properly covers each g_x"). The hypotheses `hE` and `hUE` turn out not to be needed by the
proof (kept verbatim from the skeleton). -/
theorem bj_theorem5 {f : X → unitInterval} (hf : IsArcOfContinua f) (hfo : IsOpenMap f)
    (hS : IsSnakeLike (univ : Set X)) (hind : ∀ t, Fold.Q78.IsIndecomposable (f ⁻¹' {t}))
    {n : ℕ} (E : Chain X n) (hE : univ ⊆ E.union)
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) (hU01 : Disjoint U (f ⁻¹' {0, 1}))
    (hUE : ∃ i, closure U ⊆ E.link i) (hEU : ∀ t i, ¬ E.link i ∩ f ⁻¹' {t} ⊆ closure U) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B ∧ ∀ t, (∀ i, (E.link i ∩ (A ∩ f ⁻¹' {t})).Nonempty) ∨
        (∀ i, (E.link i ∩ (B ∩ f ⁻¹' {t})).Nonempty) :=
  theorem5_repaired hf hfo hS hind E hU hUne hU01 hEU

/-- **Bing–Jones's Theorem 5 as printed is false** (commission §6): its hypotheses (a chain
properly covering each fibre, `Ū` in a link) do not give its conclusion. -/
theorem bj_theorem5_printed_false : ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X]
    (f : X → unitInterval), IsArcOfContinua f → IsSnakeLike (univ : Set X) →
    (∀ t, Fold.Q78.IsIndecomposable (f ⁻¹' {t})) → ∀ (n : ℕ) (E : Chain X n), univ ⊆ E.union →
    (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) → ∀ U : Set X, IsOpen U → U.Nonempty →
    Disjoint U (f ⁻¹' {0, 1}) → (∃ i, closure U ⊆ E.link i) →
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B ∧ ∀ t, (∀ i, (E.link i ∩ (A ∩ f ⁻¹' {t})).Nonempty) ∨
        (∀ i, (E.link i ∩ (B ∩ f ⁻¹' {t})).Nonempty) := by
  intro h
  set U : Set unitInterval := {x | (1 / 4 : ℝ) < x ∧ (x : ℝ) < 3 / 4}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)
  set x₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hx₀ : x₀ ∈ U := ⟨by norm_num [x₀], by norm_num [x₀]⟩
  have hU01 : Disjoint U (id ⁻¹' {0, 1}) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, h2⟩ (hx | hx)
    · have : (x : ℝ) = 0 := congrArg Subtype.val hx
      linarith
    · have : (x : ℝ) = 1 := congrArg Subtype.val hx
      linarith
  obtain ⟨A, B, -, -, -, hAB, -, -, hall⟩ := h unitInterval id isArcOfContinua_id
    isSnakeLike_univ_unitInterval (fun t => isIndecomposable_singleton t) 1
    (oneLinkChain unitInterval) (fun x _ => mem_iUnion.2 ⟨0, mem_univ x⟩)
    (fun t _ => ⟨t, mem_univ t, rfl⟩) U hU ⟨x₀, hx₀⟩ hU01 ⟨0, subset_univ _⟩
  have hnot : ∀ y ∈ A ∪ B, y ≠ x₀ := fun y hy hyx => by
    rw [hAB] at hy; exact hy (hyx ▸ hx₀)
  rcases hall x₀ with h' | h'
  · obtain ⟨y, -, hyA, hy⟩ := h' 0
    exact hnot y (Or.inl hyA) hy
  · obtain ⟨y, -, hyB, hy⟩ := h' 0
    exact hnot y (Or.inr hyB) hy

end Section3

/-- **Bing–Jones, Theorem 6** (p. 176), on indices: two chain maps of `D` into `E` that each take
a link into `e_{m−1}` (index `m − 2`) agree up to adjacency at some link. -/
theorem bj_theorem6 {n m : ℕ} {H₁ H₂ : Fin n → Fin m} (h₁ : IsChainMap H₁) (h₂ : IsChainMap H₂)
    (h₁e : ∃ i, (H₁ i : ℕ) + 2 = m) (h₂e : ∃ i, (H₂ i : ℕ) + 2 = m) :
    ∃ i, ((H₁ i : ℤ) - H₂ i).natAbs ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₁, hi₁⟩ := h₁e
  obtain ⟨i₂, hi₂⟩ := h₂e
  rcases lt_or_gt_of_ne (show ((H₁ i₂ : ℤ) - H₂ i₂) ≠ 0 by have := hcon i₂; omega) with h | h
  · have hs := sign_persist h₂ h₁ (fun i => by have := hcon i; omega) i₂ i₁
      (by have := hcon i₂; omega)
    have := (H₂ i₁).2
    omega
  · have hs := sign_persist h₁ h₂ hcon i₂ i₂ (by have := hcon i₂; omega)
    have := (H₁ i₂).2
    omega

end HPC.BJ59
