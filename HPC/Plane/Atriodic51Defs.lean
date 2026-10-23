import HPC.Plane.Recon91

/-!
# Bing 1951 (*Snake-like continua*), §4, part one: definitions and general topology

The definitions of the batch-92 skeleton (`Atriodic51.lean`, split into three files; see
`HPC/Plane/Atriodic51.lean`), unchanged, and the general-topology facts used for properties 1–6
and Theorem 8 that do not involve Bing's standing hypothesis.

Throughout, `S` is a compact metric space which is itself the continuum (Bing: "we suppose that
`S` is all of the space"); "continuum" means `Fold.Q78.IsContinuum` (nonempty compact connected).
`A` contains `B` *interiorly* means `B ⊆ interior A`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A *triod*: a continuum `M` containing a subcontinuum `N` such that `M \ N` is the union of
three mutually separated nonempty sets (Bing 1951, §1). -/
def IsTriod (M : Set S) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∃ N : Set S, Fold.Q78.IsContinuum N ∧ N ⊆ M ∧
    ∃ A B C : Set S, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ M \ N = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C)

/-- *Atriodic*: contains no triod. -/
def IsAtriodic (M : Set S) : Prop := ∀ T ⊆ M, ¬ IsTriod T

/-- *Unicoherent*: whenever the continuum is the union of two subcontinua, their intersection is
connected. -/
def IsUnicoherent (M : Set S) : Prop :=
  ∀ H K : Set S, Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K → H ∪ K = M → IsConnected (H ∩ K)

/-- *Hereditarily unicoherent*: every nondegenerate subcontinuum is unicoherent. -/
def IsHereditarilyUnicoherent (M : Set S) : Prop :=
  ∀ K ⊆ M, Fold.Q78.IsContinuum K → K.Nontrivial → IsUnicoherent K

/-- *Hereditarily decomposable*: every nondegenerate subcontinuum is the union of two proper
subcontinua. -/
def IsHereditarilyDecomposable (M : Set S) : Prop :=
  ∀ K ⊆ M, Fold.Q78.IsContinuum K → K.Nontrivial →
    ∃ A B : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ K ∧ B ≠ K ∧ A ∪ B = K

/-- **Bing's standing hypothesis for §4**: the whole space is a nondegenerate (compact) continuum,
atriodic, hereditarily unicoherent and hereditarily decomposable. -/
structure BingS (S : Type*) [MetricSpace S] [CompactSpace S] : Prop where
  connected : ConnectedSpace S
  nontrivial : Nontrivial S
  atriodic : IsAtriodic (univ : Set S)
  hu : IsHereditarilyUnicoherent (univ : Set S)
  hd : IsHereditarilyDecomposable (univ : Set S)

/-- A set `A` *separates* `B` from `C` in `S`: `B` and `C` lie in different components of
`S \ A` — stated as: `S \ A` is the union of two separated sets, one containing `B`, the other `C`
(Bing: "one of them separates the other two from each other in `S`"). -/
def Separates (A B C : Set S) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
    (univ : Set S) \ A ⊆ U ∪ V ∧ B ⊆ U ∧ C ⊆ V

/-! ## General topology -/

theorem cc_dichotomy {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {B C : Set Y} (hB : IsClosed B) (hC : IsClosed C) :
    (∃ y, (connectedComponent y ∩ B).Nonempty ∧ (connectedComponent y ∩ C).Nonempty) ∨
      ∃ W, IsClopen W ∧ B ⊆ W ∧ Disjoint W C := by
  by_cases h : Disjoint (ConnectedComponents.mk '' B) (ConnectedComponents.mk '' C)
  · right
    obtain ⟨V, hV, hBV, hVC⟩ := exists_clopen_of_closed_subset_open
      ((hB.isCompact.image ConnectedComponents.continuous_coe).isClosed)
      ((hC.isCompact.image ConnectedComponents.continuous_coe).isClosed.isOpen_compl)
      (subset_compl_iff_disjoint_right.mpr h)
    refine ⟨ConnectedComponents.mk ⁻¹' V, hV.preimage ConnectedComponents.continuous_coe,
      fun b hb => hBV ⟨b, hb, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro y hy hyC
    exact hVC hy ⟨y, hyC, rfl⟩
  · left
    obtain ⟨z, ⟨b, hb, rfl⟩, ⟨c, hc, hbc⟩⟩ := not_disjoint_iff.mp h
    rw [ConnectedComponents.coe_eq_coe] at hbc
    refine ⟨b, ⟨b, mem_connectedComponent, hb⟩, ⟨c, ?_, hc⟩⟩
    rw [← hbc]; exact mem_connectedComponent

omit [CompactSpace S] in
theorem isContinuum_union {A B : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (h : (A ∩ B).Nonempty) : Fold.Q78.IsContinuum (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := h
  exact ⟨hA.1.union hB.1, ⟨⟨x, Or.inl hxA⟩, hA.2.2.union x hxA hxB hB.2.2⟩⟩

theorem isContinuum_of_closed {K : Set S} (hK : IsClosed K) (hc : IsConnected K) :
    Fold.Q78.IsContinuum K := ⟨hK.isCompact, hc⟩

/-- **Dichotomy in a closed set.** In a closed `X ⊇ B`, either a subcontinuum of `X` meets both
`B` and `C`, or `X` splits into two closed pieces, one containing `B` and missing `C`. -/
theorem closed_dichotomy {X B C : Set S} (hX : IsClosed X) (hB : IsClosed B) (hC : IsClosed C)
    (hBX : B ⊆ X) :
    (∃ L ⊆ X, Fold.Q78.IsContinuum L ∧ (L ∩ B).Nonempty ∧ (L ∩ C).Nonempty) ∨
      ∃ W ⊆ X, IsClosed W ∧ IsClosed (X \ W) ∧ B ⊆ W ∧ Disjoint W C := by
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hX.isCompact
  rcases cc_dichotomy (Y := ↥X) (hB.preimage continuous_subtype_val)
    (hC.preimage continuous_subtype_val)
    with ⟨y, ⟨z, hz, hzB⟩, ⟨w, hw, hwC⟩⟩ | ⟨W, hW, hBW, hWC⟩
  · left
    refine ⟨Subtype.val '' connectedComponent y, Subtype.coe_image_subset _ _,
      ⟨(isClosed_connectedComponent.isCompact).image continuous_subtype_val,
        isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn⟩,
      ⟨z.1, ⟨z, hz, rfl⟩, hzB⟩, ⟨w.1, ⟨w, hw, rfl⟩, hwC⟩⟩
  · right
    have hXW : X \ Subtype.val '' W = Subtype.val '' Wᶜ := by
      ext x
      constructor
      · rintro ⟨hxX, hxW⟩
        exact ⟨⟨x, hxX⟩, fun h => hxW ⟨⟨x, hxX⟩, h, rfl⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.2, ?_⟩
        rintro ⟨w, hw, hwz⟩
        exact hz (Subtype.ext hwz ▸ hw)
    refine ⟨Subtype.val '' W, Subtype.coe_image_subset _ _,
      (hW.isClosed.isCompact.image continuous_subtype_val).isClosed, ?_,
      fun b hb => ⟨⟨b, hBX hb⟩, hBW hb, rfl⟩, ?_⟩
    · rw [hXW]; exact (hW.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
    · rw [Set.disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ hzC
      exact Set.disjoint_left.mp hWC hz hzC

omit [CompactSpace S] in
theorem separates_comm {A B C : Set S} : Separates A B C → Separates A C B := by
  rintro ⟨h1, h2, U, V, hU, hV, hUV, hcov, hB, hC⟩
  exact ⟨h2, h1, V, U, hV, hU, hUV.symm, by rw [union_comm]; exact hcov, hC, hB⟩

/-- If `A` does not separate `B` from `C` (closed, pairwise disjoint), some continuum avoiding the
interiors of `A` and `C` meets `B` and `C`. -/
theorem connector_of_not_separates {A B C : Set S} (hA : IsClosed A) (hB : IsClosed B)
    (hC : IsClosed C) (dAB : Disjoint A B) (dAC : Disjoint A C) (dBC : Disjoint B C)
    (hns : ¬ Separates A B C) :
    ∃ L, Fold.Q78.IsContinuum L ∧ Disjoint L (interior A) ∧ Disjoint L (interior C) ∧
      (L ∩ B).Nonempty ∧ (L ∩ C).Nonempty := by
  set X := (interior A ∪ interior C)ᶜ with hX_def
  have hXc : IsClosed X := (isOpen_interior.union isOpen_interior).isClosed_compl
  have hBX : B ⊆ X := fun b hb hb' => hb'.elim
    (fun h => Set.disjoint_left.mp dAB (interior_subset h) hb)
    (fun h => Set.disjoint_left.mp dBC hb (interior_subset h))
  rcases closed_dichotomy hXc hB hC hBX with ⟨L, hLX, hL, hLB, hLC⟩ | ⟨W, hWX, hW, hXW, hBW, hWC⟩
  · refine ⟨L, hL, ?_, ?_, hLB, hLC⟩
    · exact Set.disjoint_left.mpr fun x hx hxA => hLX hx (Or.inl hxA)
    · exact Set.disjoint_left.mpr fun x hx hxC => hLX hx (Or.inr hxC)
  · exfalso
    apply hns
    refine ⟨dAB, dAC, ((X \ W) ∪ C ∪ A)ᶜ, (W ∪ A)ᶜ, ((hXW.union hC).union hA).isOpen_compl,
      (hW.union hA).isOpen_compl, ?_, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [mem_compl_iff, mem_union, not_or] at hx1 hx2
      have hxX : x ∉ X := fun hxX => hx1.1.1 ⟨hxX, hx2.1⟩
      simp only [hX_def, mem_compl_iff, not_not, mem_union] at hxX
      rcases hxX with h | h
      · exact hx1.2 (interior_subset h)
      · exact hx1.1.2 (interior_subset h)
    · intro x ⟨_, hxA⟩
      by_cases hxW : x ∈ W
      · left
        simp only [mem_compl_iff, mem_union, not_or]
        exact ⟨⟨fun h => h.2 hxW, fun h => Set.disjoint_left.mp hWC hxW h⟩, hxA⟩
      · right
        simp only [mem_compl_iff, mem_union, not_or]
        exact ⟨hxW, hxA⟩
    · intro b hb
      simp only [mem_compl_iff, mem_union, not_or]
      exact ⟨⟨fun h => h.2 (hBW hb), fun h => Set.disjoint_left.mp dBC hb h⟩,
        fun h => Set.disjoint_left.mp dAB h hb⟩
    · intro c hc
      simp only [mem_compl_iff, mem_union, not_or]
      exact ⟨fun h => Set.disjoint_left.mp hWC h hc, fun h => Set.disjoint_left.mp dAC h hc⟩

omit [CompactSpace S] in
/-- A connected set `T` containing a nonempty open `W` that is closed in `T` lies in `W`. -/
theorem subset_of_relClopen {T W : Set S} (hT : IsPreconnected T) (hW : IsOpen W)
    (hWT : W ⊆ T) (hcl : closure W ∩ T ⊆ W) (hne : W.Nonempty) : T ⊆ W := by
  have hcov : T ⊆ W ∪ (closure W)ᶜ := fun x hx => by
    by_cases h : x ∈ closure W
    · exact Or.inl (hcl ⟨h, hx⟩)
    · exact Or.inr h
  by_contra hnot
  obtain ⟨x, hxT, hxW⟩ := not_subset.mp hnot
  have hx2 : x ∈ (closure W)ᶜ := (hcov hxT).resolve_left hxW
  obtain ⟨w, hw⟩ := hne
  obtain ⟨z, _, hz1, hz2⟩ := hT W (closure W)ᶜ hW isClosed_closure.isOpen_compl hcov
    ⟨w, hWT hw, hw⟩ ⟨x, hxT, hx2⟩
  exact hz2 (subset_closure hz1)

omit [CompactSpace S] in
/-- A connected set missing `A` and meeting `B` and `C` shows that `A` does not separate them. -/
theorem not_separates_of_preconnected {A B C T : Set S} (hT : IsPreconnected T)
    (hTA : Disjoint T A) (hB : (T ∩ B).Nonempty) (hC : (T ∩ C).Nonempty) :
    ¬ Separates A B C := by
  rintro ⟨-, -, U, V, hU, hV, hUV, hcov, hBU, hCV⟩
  obtain ⟨x, -, hxU, hxV⟩ := hT U V hU hV
    (fun x hx => hcov ⟨mem_univ x, fun hxA => Set.disjoint_left.mp hTA hx hxA⟩)
    (hB.mono (inter_subset_inter_right _ hBU)) (hC.mono (inter_subset_inter_right _ hCV))
  exact Set.disjoint_left.mp hUV hxU hxV

omit [CompactSpace S] in
/-- `C ∪ K ∪ H` is connected when `K ⊆ closure C` and the connected `H` meets `closure C`. -/
theorem preconnected_through {C K H : Set S} (hC : IsPreconnected C) (hK : K ⊆ closure C)
    {z : S} (hzC : z ∈ closure C) (hzH : z ∈ H) (hH : IsPreconnected H) :
    IsPreconnected (C ∪ K ∪ H) := by
  have h1 : IsPreconnected (C ∪ K ∪ {z}) :=
    hC.subset_closure (subset_union_left.trans subset_union_left)
      (union_subset (union_subset subset_closure hK) (singleton_subset_iff.mpr hzC))
  have h2 := h1.union z (Or.inr rfl) hzH hH
  have e : C ∪ K ∪ {z} ∪ H = C ∪ K ∪ H := by
    ext x; simp only [mem_union, mem_singleton_iff]
    constructor
    · rintro (((h | h) | rfl) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr hzH
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
  rwa [e] at h2

end HPC.Plane
