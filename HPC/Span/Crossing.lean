import HPC.Span.Defs
import HPC.Plane.Ingram68Star
import HPC.Hagopian.Hagopian75

/-!
# Batch 191, §6.2: crossing continua

* `exists_crossing_subcontinuum` (the cut wire, via `HPC.Plane.exists_split_of_no_continuum`).
* `exists_uncountable_crossing`: one crossing continuum in each composant.
-/

namespace HPC.Span

open Set Topology Metric HPC.Plane HPC.Jones HPC.Hagopian

/-- **§6.2 (cut wire)**: a continuum with points left of `x = a` and right of `x = b` contains a
subcontinuum of the closed strip meeting both lines. -/
theorem exists_crossing_subcontinuum {P : Set Pt} (hP : Fold.Q78.IsContinuum P) {a b : ℝ}
    (hab : a < b) (hl : ∃ z ∈ P, z.1 < a) (hr : ∃ z ∈ P, b < z.1) :
    ∃ K ⊆ P ∩ (Icc a b ×ˢ univ), Fold.Q78.IsContinuum K ∧ (∃ z ∈ K, z.1 = a) ∧
      ∃ z ∈ K, z.1 = b := by
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP.1
  haveI : ConnectedSpace P := isConnected_iff_connectedSpace.mp hP.2
  set g : P → ℝ := fun z => z.1.1 with hgdef
  have hg : Continuous g := continuous_fst.comp continuous_subtype_val
  set F : Set P := g ⁻¹' Icc a b
  set E₁ : Set P := g ⁻¹' {a}
  set E₂ : Set P := g ⁻¹' {b}
  by_contra hno
  obtain ⟨F₁, F₂, hF₁, hF₂, hdisj, hFeq, hE₁, hE₂⟩ := exists_split_of_no_continuum (S := P)
    (F := F) (E₁ := E₁) (E₂ := E₂) (isClosed_Icc.preimage hg)
    (fun z hz => by
      show g z ∈ Icc a b
      rw [show g z = a from hz]; exact ⟨le_rfl, hab.le⟩)
    (fun z hz => by
      show g z ∈ Icc a b
      rw [show g z = b from hz]; exact ⟨hab.le, le_rfl⟩)
    (isClosed_singleton.preimage hg) (isClosed_singleton.preimage hg) (by
      intro C hC hCF ⟨c₁, hc₁C, hc₁⟩ ⟨c₂, hc₂C, hc₂⟩
      refine hno ⟨Subtype.val '' C, ?_, ⟨hC.1.image continuous_subtype_val,
        hC.2.image _ continuous_subtype_val.continuousOn⟩, ⟨c₁.1, mem_image_of_mem _ hc₁C, hc₁⟩,
        ⟨c₂.1, mem_image_of_mem _ hc₂C, hc₂⟩⟩
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c.2, hCF hc, mem_univ _⟩)
  -- the two closed sets covering `P`
  set L : Set P := g ⁻¹' Iic a ∪ F₁
  set R : Set P := g ⁻¹' Ici b ∪ F₂
  have hLc : IsClosed L := (isClosed_Iic.preimage hg).union hF₁
  have hRc : IsClosed R := (isClosed_Ici.preimage hg).union hF₂
  have hLR : Disjoint L R := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · have h1 : g z ≤ a := hz
      have h2 : b ≤ g z := hz'
      linarith
    · have h1 : g z ≤ a := hz
      have hzF : z ∈ F := hFeq ▸ (Or.inr hz' : z ∈ F₁ ∪ F₂)
      have h2 : a ≤ g z := hzF.1
      have : z ∈ E₁ := show g z = a from le_antisymm h1 h2
      exact Set.disjoint_left.1 hdisj (hE₁ this) hz'
    · have h1 : b ≤ g z := hz'
      have hzF : z ∈ F := hFeq ▸ (Or.inl hz : z ∈ F₁ ∪ F₂)
      have h2 : g z ≤ b := hzF.2
      have : z ∈ E₂ := show g z = b from le_antisymm h2 h1
      exact Set.disjoint_left.1 hdisj hz (hE₂ this)
    · exact Set.disjoint_left.1 hdisj hz hz'
  have hcov : L ∪ R = univ := by
    refine eq_univ_of_forall fun z => ?_
    by_cases h1 : g z ≤ a
    · exact Or.inl (Or.inl h1)
    by_cases h2 : b ≤ g z
    · exact Or.inr (Or.inl h2)
    have hzF : z ∈ F := ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩
    rw [hFeq] at hzF
    rcases hzF with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  have hLR' : L = Rᶜ := by
    ext z
    refine ⟨fun hzL hzR => Set.disjoint_left.1 hLR hzL hzR, fun hz => ?_⟩
    rcases (hcov ▸ mem_univ z : z ∈ L ∪ R) with h | h
    · exact h
    · exact absurd h hz
  have hLo : IsClopen L := ⟨hLc, hLR' ▸ hRc.isOpen_compl⟩
  obtain ⟨p, hpP, hpa⟩ := hl
  obtain ⟨q, hqP, hqb⟩ := hr
  have hpL : (⟨p, hpP⟩ : P) ∈ L := Or.inl (show g ⟨p, hpP⟩ ≤ a from hpa.le)
  have hqR : (⟨q, hqP⟩ : P) ∈ R := Or.inl (show b ≤ g ⟨q, hqP⟩ from hqb.le)
  rcases isClopen_iff.1 hLo with h | h
  · rw [h] at hpL; exact hpL
  · exact Set.disjoint_left.1 hLR (h ▸ mem_univ _) hqR

/-- A point of the composant of `x` has the same composant (indecomposable case). -/
theorem composant_eq_of_mem {X : Type*} [MetricSpace X] (hi : ¬ IsDecomposableSpace X) {x y : X}
    (hy : y ∈ Jones.composant x) (hyy : y ∈ Jones.composant y) :
    Jones.composant y = Jones.composant x := by
  rcases composant_eq_or_disjoint hi y x with h | h
  · exact h
  · exact absurd hy (Set.disjoint_left.1 h hyy)

/-- **§6.2**: an indecomposable plane continuum with points on both sides of a closed strip contains
uncountably many pairwise disjoint continua crossing the strip (one in each composant). -/
theorem exists_uncountable_crossing (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hi : ¬ IsDecomposableSpace M) {a b : ℝ} (hab : a < b) (hl : ∃ z ∈ M, z.1 < a)
    (hr : ∃ z ∈ M, b < z.1) :
    ∃ 𝒦 : Set (Set Pt), ¬ 𝒦.Countable ∧ 𝒦.PairwiseDisjoint id ∧
      ∀ K ∈ 𝒦, K ⊆ M ∩ (Icc a b ×ˢ univ) ∧ Fold.Q78.IsContinuum K ∧ (∃ z ∈ K, z.1 = a) ∧
        ∃ z ∈ K, z.1 = b := by
  obtain ⟨l, hlM, hla⟩ := hl
  obtain ⟨r, hrM, hrb⟩ := hr
  haveI : Nontrivial M := ⟨⟨⟨l, hlM⟩, ⟨r, hrM⟩, fun h => by
    have : l = r := congrArg Subtype.val h
    rw [this] at hla; linarith⟩⟩
  -- every point lies in its own composant
  have hself : ∀ x : M, x ∈ Jones.composant x := by
    intro x
    obtain ⟨y, hy⟩ := exists_ne x
    refine ⟨{x}, ⟨isCompact_singleton, isConnected_singleton⟩, fun h => hy ?_, rfl, rfl⟩
    exact (h ▸ mem_univ y : y ∈ ({x} : Set M))
  -- each composant contains a crossing continuum
  have hex : ∀ κ ∈ range (Jones.composant : M → Set M), ∃ K : Set Pt,
      K ⊆ Subtype.val '' κ ∧ K ⊆ M ∩ (Icc a b ×ˢ univ) ∧ Fold.Q78.IsContinuum K ∧
        (∃ z ∈ K, z.1 = a) ∧ ∃ z ∈ K, z.1 = b := by
    rintro _ ⟨x, rfl⟩
    have hopen : ∀ (U : Set M), IsOpen U → U.Nonempty → ∃ p ∈ U, p ∈ Jones.composant x :=
      fun U hU hne => by
        obtain ⟨p, hpU, hpc⟩ := (composant_dense x).inter_open_nonempty U hU hne
        exact ⟨p, hpU, hpc⟩
    obtain ⟨p, hpa, hpx⟩ := hopen {z : M | z.1.1 < a}
      (isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const) ⟨⟨l, hlM⟩, hla⟩
    have hcp : Jones.composant p = Jones.composant x := composant_eq_of_mem hi hpx (hself p)
    obtain ⟨q, hqb, hqp⟩ := hopen {z : M | b < z.1.1}
      (isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)) ⟨⟨r, hrM⟩, hrb⟩
    rw [← hcp] at hqp
    obtain ⟨L, hL, hLu, hpL, hqL⟩ := hqp
    have hLc : Fold.Q78.IsContinuum (Subtype.val '' L) :=
      ⟨hL.1.image continuous_subtype_val, hL.2.image _ continuous_subtype_val.continuousOn⟩
    obtain ⟨K, hKsub, hK, hKa, hKb⟩ := exists_crossing_subcontinuum hLc hab
      ⟨p.1, mem_image_of_mem _ hpL, hpa⟩ ⟨q.1, mem_image_of_mem _ hqL, hqb⟩
    refine ⟨K, fun z hz => ?_, fun z hz => ?_, hK, hKa, hKb⟩
    · obtain ⟨w, hwL, hwz⟩ := (hKsub hz).1
      refine ⟨w, ?_, hwz⟩
      rw [← hcp]
      exact ⟨L, hL, hLu, hpL, hwL⟩
    · obtain ⟨w, -, hwz⟩ := (hKsub hz).1
      exact ⟨hwz ▸ w.2, (hKsub hz).2⟩
  choose! Kc hKc using hex
  refine ⟨Kc '' range (Jones.composant : M → Set M), ?_, ?_, ?_⟩
  · intro hcount
    apply uncountable_composants hi
    -- recover the composant from its continuum
    set ψ : Set Pt → Set M := fun K => {y | ∃ x : M, Kc (Jones.composant x) = K ∧
      y ∈ Jones.composant x}
    refine (hcount.image ψ).mono ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨Kc (Jones.composant x), mem_image_of_mem _ ⟨x, rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨x', hx', hy⟩
      obtain ⟨k, hk⟩ := (hKc _ ⟨x', rfl⟩).2.2.1.2.nonempty
      obtain ⟨w, hw, rfl⟩ := (hKc _ ⟨x', rfl⟩).1 hk
      rw [hx'] at hk
      obtain ⟨w', hw', hww'⟩ := (hKc _ ⟨x, rfl⟩).1 hk
      have hw'' : w' = w := Subtype.ext hww'
      subst hw''
      rw [← composant_eq_of_mem hi hw' (hself w'), composant_eq_of_mem hi hw (hself w')]
      exact hy
    · intro hy
      exact ⟨x, rfl, hy⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩ hne
    rcases composant_eq_or_disjoint hi x y with h | h
    · exact absurd (by rw [h]) hne
    · rw [Function.onFun, Set.disjoint_left]
      intro z hzx hzy
      obtain ⟨w, hw, rfl⟩ := (hKc _ ⟨x, rfl⟩).1 hzx
      obtain ⟨w', hw', hww'⟩ := (hKc _ ⟨y, rfl⟩).1 hzy
      have : w' = w := Subtype.ext hww'
      subst this
      exact Set.disjoint_left.1 h hw hw'
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (hKc _ ⟨x, rfl⟩).2

end HPC.Span
