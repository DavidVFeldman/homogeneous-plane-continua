import HPC.Hagopian.H76Prop1

/-!
# Batch 161, item T9

Hagopian 1976, p. 346: "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is the
image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism. Note that the chain
`L − {L₁, L₁₁}` follows `Cl B`."

`T9_aux` proves the first sentence for any open `O` of the plane (Hagopian's `π⁻¹[D]`) with the one
property of `D` that the argument uses:

* **(D)** every point of `M ∩ Cl O` lies in one of the links `L₂, …, L₁₀` (0-indexed `1, …, 9`).

and for any connected `B ⊆ M ∩ O` meeting one of these links (Hagopian: a component meeting
`L₄ ∪ … ∪ L₈`). Property 1 gives an `ε₁`-homeomorphism `h` with a point of `B` in `h[E]` and the
elevenths of `h[E]` in the links of `L`; by (D) and `IsEps1.ends`, `Cl B` misses `h[k⁻¹(0) ∪ k⁻¹(1)]`;
by atriodicity (`subset_of_meets_avoids`, the 1975 ¶9 triod — Hagopian's "Lemma 5" step is not
needed for this) `Cl B ⊆ h[E]`. Hence `h⁻¹[Cl B]` is a subcontinuum of `E`.

*Essential*: `h⁻¹[Cl B]` is essential to `R(E)` as soon as it meets two layers of `E`; this holds when
`Cl B` meets two links `Lₐ`, `L_c` with `c ≥ a + 3` (a layer of `h[E]` lies in one link). That `Cl B`
reaches far apart links (Hagopian's "`L − {L₁, L₁₁}` follows `Cl B`") depends on the position of
`D` in collar coordinates (T6–T8), which is not formalized; it is recorded as a hypothesis.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section T9

variable {M : Set Pt}

theorem subset_Rset {X : Type*} [MetricSpace X] {E : Set X} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : E ⊆ Rset k := fun _ hx =>
  Or.inl ⟨E, ⟨subset_rfl, k, hE, rfl⟩, hx⟩

/-- **T9** (p. 346), first sentence, for an open `O` with property (D). -/
theorem T9_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) {L : Fin 11 → Set Pt}
    (hLch : IsPlaneChain L) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {O : Set Pt}
    (hO : ∀ x : M, (x : Pt) ∈ closure O → ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j)
    {B : Set M} (hBc : IsPreconnected B) (hBO : toPt B ⊆ O) {y : M} (hyB : y ∈ B) {i : Fin 11}
    (hi1 : 1 ≤ (i : ℕ)) (hi9 : (i : ℕ) ≤ 9) (hyL : (y : Pt) ∈ L i) :
    ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
      Fold.Q78.IsContinuum (h ⁻¹' closure B) ∧ h ⁻¹' closure B ⊆ E ∧
      ∀ a c : Fin 11, (a : ℕ) + 3 ≤ c → (toPt (closure B) ∩ L a).Nonempty →
        (toPt (closure B) ∩ L c).Nonempty → IsEssential k (h ⁻¹' closure B) := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨h, hh, hyE, hpieces⟩ := hP1 y i hi1 hi9 hyL
  obtain ⟨b, hbE, hb⟩ := exists_image_map h hE
  -- `Cl B` is a continuum
  have hclB : Fold.Q78.IsContinuum (closure B) :=
    ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyB⟩, hBc.closure⟩
  -- every point of `Cl B` is in a middle link
  have hmid : ∀ x ∈ closure B, ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j := by
    intro x hx
    apply hO
    exact closure_mono hBO (image_closure_subset_closure_image continuous_subtype_val ⟨x, hx, rfl⟩)
  -- `Cl B` misses the images of the end sets
  have havoid : Disjoint (closure B) (layer b 0 ∪ layer b 1) := by
    rw [disjoint_left]
    intro x hx hxe
    have hxe' : x ∈ h '' (layer k 0 ∪ layer k 1) := by
      rcases hxe with h0 | h1
      · have : x ∈ layerSet b {0} := h0
        rw [hb] at this
        exact image_mono subset_union_left this
      · have : x ∈ layerSet b {1} := h1
        rw [hb] at this
        exact image_mono subset_union_right this
    obtain ⟨e, he0, rfl⟩ := hxe'
    obtain ⟨j, hj1, hj9, hxj⟩ := hmid _ hx
    obtain ⟨_, ⟨m, hm, rfl⟩, hxm⟩ :=
      mem_thickening_iff.1 (chainG_subset_thickening k ε₁ j (hLG j hxj))
    have h1 := he.ends e he0 m (piece_subset_middle k hj1 hj9 hm)
    have h2 := hh e
    rw [Subtype.dist_eq] at h1 h2
    have := dist_triangle (e : Pt) ((h e : M) : Pt) (m : Pt)
    have := he.pos
    linarith
  have hhE : Fold.Q78.IsContinuum (h '' E) := by
    obtain ⟨⟨a₀, b₀, hab⟩, -, -⟩ := hbE
    exact hab.1
  have hsub : closure B ⊆ h '' E :=
    subset_of_meets_avoids hHU hAT hhE hbE.2.1 hclB ⟨y, hyE, subset_closure hyB⟩ havoid
  have hpre : h ⁻¹' closure B ⊆ E := by
    intro x hx
    obtain ⟨e, he, hex⟩ := hsub hx
    rw [← h.injective hex]
    exact he
  have hpreC : Fold.Q78.IsContinuum (h ⁻¹' closure B) := by
    rw [← h.image_symm]
    exact isContinuum_homeo_image h.symm hclB
  refine ⟨h, hh, hsub, hpreC, hpre, fun a c hac ha hc => ?_⟩
  refine ⟨hpre.trans (subset_Rset hE), hpreC, E, k, subset_rfl, hE, Or.inl rfl, ?_⟩
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hx₁a⟩ := ha
  obtain ⟨_, ⟨x₂, hx₂, rfl⟩, hx₂c⟩ := hc
  obtain ⟨e₁, he₁E, rfl⟩ := hsub hx₁
  obtain ⟨e₂, he₂E, rfl⟩ := hsub hx₂
  set f₁ : E := ⟨e₁, he₁E⟩
  set f₂ : E := ⟨e₂, he₂E⟩
  refine ⟨k f₁, k f₂, fun heq => ?_, ⟨e₁, hx₁, f₁, rfl, rfl⟩, ⟨e₂, hx₂, f₂, rfl, rfl⟩⟩
  obtain ⟨m, hm⟩ := exists_elev (k f₁)
  have hm₂ : k f₂ ∈ elev m := heq ▸ hm
  have hin : ∀ f : E, k f ∈ elev m → (((h f : M)) : Pt) ∈ L m := fun f hf =>
    hpieces m ⟨h f, ⟨f, by rw [piece_succ]; exact ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
  have h1 := (hLch.meets m a).1 ⟨_, hin f₁ hm, hx₁a⟩
  have h2 := (hLch.meets m c).1 ⟨_, hin f₂ hm₂, hx₂c⟩
  omega

end T9

end HPC.Hagopian
