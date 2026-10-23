import HPC.Hagopian.H75KurMap

/-!
# Batch 155: a scale in Kuratowski's family `D` (Kuratowski §48 VII, Theorem 3)

If every subcontinuum with interior is decomposable, Kuratowski's family `D` is a chain without jumps
(`H75Kur.lean`). A countable basis of `Y` gives a countable subfamily `𝒞` dense in `D`
(`exists_countable_dense_D`); with `∅` and `Y` removed, `𝒞` is a countable dense linear order without
end points, hence (Cantor) order-isomorphic to `ℚ ∩ (0, 1)`. Indexing by this isomorphism gives a
scale (`exists_scale`), and so a type A′ map (`exists_typeA'_map`). This replaces Kuratowski's
Theorem 3 ("`D` has the order type of the interval") by the order type of its countable dense part.
-/

namespace HPC.Hagopian

open Set Topology

section Scale

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y] {a b : Y}

/-- A countable subfamily of `D`, dense in `D` (strictly between any two members lies one of it). -/
theorem exists_countable_dense_D (hirr : IrrBetween a b)
    (hH : ∀ K : Set Y, Fold.Q78.IsContinuum K → (interior K).Nonempty →
      ¬ Fold.Q78.IsIndecomposable K) :
    ∃ 𝒞 : Set (Set Y), 𝒞.Countable ∧ (∀ C ∈ 𝒞, IsDElt a C) ∧
      ∀ D₁ D₂, IsDElt a D₁ → IsDElt a D₂ → D₁ ⊆ D₂ → D₁ ≠ D₂ →
        ∃ C ∈ 𝒞, D₁ ⊆ C ∧ C ≠ D₁ ∧ C ⊆ D₂ ∧ C ≠ D₂ := by
  classical
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis Y
  let g : Set Y × Set Y → Set Y := fun p =>
    if h : ∃ D, IsDElt a D ∧ p.1 ⊆ D ∧ Disjoint p.2 D then h.choose else ∅
  refine ⟨g '' (B ×ˢ B), (hBc.prod hBc).image g, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    simp only [g]
    split_ifs with h
    · exact h.choose_spec.1
    · exact isDElt_empty
  · intro D₁ D₂ h₁ h₂ h12 hne
    obtain ⟨D, hD, hD1, hDne1, hD2, hDne2⟩ := IsDElt.exists_between hirr hH h₁ h₂ h12 hne
    obtain ⟨u, huD, hu1⟩ := exists_interior_not_mem hD.1 h₁.isClosed
      (fun h => hDne1 (Subset.antisymm h hD1))
    obtain ⟨v, hvD, hv1⟩ := exists_interior_not_mem h₂.1 hD.isClosed
      (fun h => hDne2 (Subset.antisymm hD2 h))
    obtain ⟨U, hUB, huU, hUsub⟩ := hB.exists_subset_of_mem_open
      (show u ∈ interior D \ D₁ from ⟨huD, hu1⟩) (isOpen_interior.sdiff h₁.isClosed)
    obtain ⟨V, hVB, hvV, hVsub⟩ := hB.exists_subset_of_mem_open
      (show v ∈ interior D₂ \ D from ⟨hvD, hv1⟩) (isOpen_interior.sdiff hD.isClosed)
    have hex : ∃ D', IsDElt a D' ∧ U ⊆ D' ∧ Disjoint V D' :=
      ⟨D, hD, fun x hx => interior_subset (hUsub hx).1,
        disjoint_left.2 fun x hx hxD => (hVsub hx).2 hxD⟩
    have hspec : IsDElt a (g (U, V)) ∧ U ⊆ g (U, V) ∧ Disjoint V (g (U, V)) := by
      simp only [g, dif_pos hex]; exact hex.choose_spec
    obtain ⟨hCe, hUC, hVC⟩ := hspec
    have hvD₂ : v ∈ D₂ := interior_subset (hVsub hvV).1
    refine ⟨g (U, V), ⟨(U, V), ⟨hUB, hVB⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rcases IsDElt.chain hirr h₁ hCe with h | h
      · exact h
      · exact absurd (h (hUC huU)) (hUsub huU).2
    · intro h; exact (hUsub huU).2 (h ▸ hUC huU)
    · rcases IsDElt.chain hirr hCe h₂ with h | h
      · exact h
      · exact absurd (h hvD₂) (disjoint_left.1 hVC hvV)
    · intro h; exact disjoint_left.1 hVC hvV (h ▸ hvD₂)

/-- **A scale exists** when every subcontinuum with interior is decomposable. -/
theorem exists_scale (hirr : IrrBetween a b)
    (hH : ∀ K : Set Y, Fold.Q78.IsContinuum K → (interior K).Nonempty →
      ¬ Fold.Q78.IsIndecomposable K) :
    ∃ E : ℚ → Set Y, IsDScale a E := by
  classical
  obtain ⟨𝒞, hcount, h𝒞, hdense⟩ := exists_countable_dense_D hirr hH
  have hYne : (∅ : Set Y) ≠ univ := fun h => (h ▸ mem_univ a : a ∈ (∅ : Set Y))
  let T := {C : Set Y // C ∈ 𝒞 ∧ C ≠ ∅ ∧ C ≠ univ}
  have htot : ∀ x y : T, x ≤ y ∨ y ≤ x := fun x y => IsDElt.chain hirr (h𝒞 _ x.2.1) (h𝒞 _ y.2.1)
  letI : LinearOrder T :=
    { (inferInstance : PartialOrder T) with
      le_total := htot
      toDecidableLE := Classical.decRel _ }
  have hlt : ∀ x y : T, x < y ↔ x.1 ⊆ y.1 ∧ x.1 ≠ y.1 := fun x y =>
    Subtype.coe_lt_coe.symm.trans lt_iff_le_and_ne
  haveI : Countable T := by
    haveI := hcount.to_subtype
    exact Function.Injective.countable (f := fun x : T => (⟨x.1, x.2.1⟩ : 𝒞))
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
  haveI : DenselyOrdered T := ⟨fun x y hxy => by
    rw [hlt] at hxy
    obtain ⟨C, hC, h1, h2, h3, h4⟩ := hdense x.1 y.1 (h𝒞 _ x.2.1) (h𝒞 _ y.2.1) hxy.1 hxy.2
    refine ⟨⟨C, hC, ?_, ?_⟩, (hlt _ _).2 ⟨h1, Ne.symm h2⟩, (hlt _ _).2 ⟨h3, h4⟩⟩
    · intro he; rw [he] at h1; exact x.2.2.1 (subset_empty_iff.1 h1)
    · intro hu; rw [hu] at h3; exact y.2.2.2 (univ_subset_iff.1 h3)⟩
  haveI : NoMinOrder T := ⟨fun x => by
    obtain ⟨C, hC, -, h2, h3, h4⟩ := hdense ∅ x.1 isDElt_empty (h𝒞 _ x.2.1) (empty_subset _)
      (Ne.symm x.2.2.1)
    exact ⟨⟨C, hC, h2, fun hu => x.2.2.2 (univ_subset_iff.1 (hu ▸ h3))⟩, (hlt _ _).2 ⟨h3, h4⟩⟩⟩
  haveI : NoMaxOrder T := ⟨fun x => by
    obtain ⟨C, hC, h1, h2, -, h4⟩ := hdense x.1 univ (h𝒞 _ x.2.1) isDElt_univ (subset_univ _)
      x.2.2.2
    refine ⟨⟨C, hC, fun he => x.2.2.1 (subset_empty_iff.1 (he ▸ h1)), h4⟩,
      (hlt _ _).2 ⟨h1, Ne.symm h2⟩⟩⟩
  haveI : Nonempty T := by
    obtain ⟨C, hC, -, h2, -, h4⟩ := hdense ∅ univ isDElt_empty isDElt_univ (empty_subset _) hYne
    exact ⟨⟨C, hC, h2, h4⟩⟩
  haveI : Nonempty (Ioo (0 : ℚ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨φ⟩ := Order.iso_of_countable_dense T (Ioo (0 : ℚ) 1)
  let E : ℚ → Set Y := fun q =>
    if h : q ∈ Ioo (0 : ℚ) 1 then (φ.symm ⟨q, h⟩).1 else if q ≤ 0 then ∅ else univ
  have hlo : ∀ q : ℚ, q ≤ 0 → E q = ∅ := fun q hq => by
    simp only [E, dif_neg (fun h : q ∈ Ioo (0 : ℚ) 1 => not_lt.2 hq h.1), if_pos hq]
  have hhi : ∀ q : ℚ, 1 ≤ q → E q = univ := fun q hq => by
    simp only [E, dif_neg (fun h : q ∈ Ioo (0 : ℚ) 1 => not_lt.2 hq h.2),
      if_neg (not_le.2 (zero_lt_one.trans_le hq))]
  have hmid : ∀ q : ℚ, ∀ h : q ∈ Ioo (0 : ℚ) 1, E q = (φ.symm ⟨q, h⟩).1 := fun q h => by
    simp only [E, dif_pos h]
  refine ⟨E, fun q => ?_, fun q q' hqq' => ?_, fun q q' hqq' hq1 hq'0 => ?_, hlo, hhi, ?_⟩
  · by_cases h : q ∈ Ioo (0 : ℚ) 1
    · rw [hmid q h]; exact h𝒞 _ (φ.symm _).2.1
    · rcases not_and_or.1 h with h | h
      · rw [hlo q (not_lt.1 h)]; exact isDElt_empty
      · rw [hhi q (not_lt.1 h)]; exact isDElt_univ
  · by_cases h0 : q ≤ 0
    · rw [hlo q h0]; exact empty_subset _
    by_cases h1 : 1 ≤ q'
    · rw [hhi q' h1]; exact subset_univ _
    push_neg at h0 h1
    have hq : q ∈ Ioo (0 : ℚ) 1 := ⟨h0, hqq'.trans_lt h1⟩
    have hq' : q' ∈ Ioo (0 : ℚ) 1 := ⟨h0.trans_le hqq', h1⟩
    rw [hmid q hq, hmid q' hq']
    exact φ.symm.monotone (Subtype.mk_le_mk.2 hqq')
  · by_cases h0 : q ≤ 0
    · rw [hlo q h0]
      by_cases h1 : q' < 1
      · rw [hmid q' ⟨hq'0, h1⟩]; exact Ne.symm (φ.symm _).2.2.1
      · rw [hhi q' (not_lt.1 h1)]; exact hYne
    push_neg at h0
    rw [hmid q ⟨h0, hq1⟩]
    by_cases h1 : q' < 1
    · rw [hmid q' ⟨hq'0, h1⟩]
      exact ((hlt _ _).1 (φ.symm.strictMono (Subtype.mk_lt_mk.2 hqq'))).2
    · rw [hhi q' (not_lt.1 h1)]; exact (φ.symm _).2.2.2
  · intro D₁ D₂ h₁ h₂ h12 hne
    obtain ⟨C, hC, h1, h2, h3, h4⟩ := hdense D₁ D₂ h₁ h₂ h12 hne
    have hC0 : C ≠ ∅ := fun he => h2 (by rw [he] at h1 ⊢; exact (subset_empty_iff.1 h1).symm)
    have hCu : C ≠ univ := fun hu => h4 (by rw [hu] at h3 ⊢; exact (univ_subset_iff.1 h3).symm)
    set x : T := ⟨C, hC, hC0, hCu⟩
    refine ⟨(φ x).1, ?_⟩
    rw [hmid _ (φ x).2]
    simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, x]
    exact ⟨h1, h2, h3, h4⟩

/-- **Sufficiency in Lemma 2, intrinsic form.** If `Y` is irreducible between `a` and `b` and every
subcontinuum with interior is decomposable, `Y` has an admissible map whose fibres have empty
interior. -/
theorem exists_typeA'_map (hirr : IrrBetween a b)
    (hH : ∀ K : Set Y, Fold.Q78.IsContinuum K → (interior K).Nonempty →
      ¬ Fold.Q78.IsIndecomposable K) :
    ∃ k : Y → unitInterval, Continuous k ∧ Function.Surjective k ∧
      (∀ t, IsConnected (k ⁻¹' {t})) ∧ ∀ t, interior (k ⁻¹' {t}) = ∅ := by
  obtain ⟨E, hE⟩ := exists_scale hirr hH
  exact scaleMap_spec hirr hE

end Scale

end HPC.Hagopian
