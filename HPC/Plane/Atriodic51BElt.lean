import HPC.Plane.Atriodic51CounterArc

/-!
# Bing 1951, §4: Theorem 8 with Bing's own elements (batch 93)

Bing's definition (p. 658): "for each point `p` let `g_p` denote the intersection of all continua
which contain interiorly a continuum that contains `p` interiorly". The two definitions of the
batch-93 skeleton (`ContainsNested`, `bingElt`) are moved here, unchanged, so that the supporting
files can use them; `HPC/Plane/Atriodic51B.lean` imports this file.

The heart of the file is `not_mem_bingElt_of` (Bing's `K_2`, `K_4` argument) and the partition
property `bingElt_partition` built on it; upper semicontinuity, (a), (b), (c) are transferred from
the batch-92 arguments for `gElt`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- `H` *contains interiorly a continuum that contains `p` interiorly*. -/
def ContainsNested (H : Set S) (p : S) : Prop :=
  ∃ H' : Set S, Fold.Q78.IsContinuum H' ∧ H' ⊆ interior H ∧ p ∈ interior H'

/-- **Bing's elements** (p. 658): the intersection of all continua which contain interiorly a
continuum that contains `p` interiorly. -/
def bingElt (p : S) : Set S := ⋂₀ {H : Set S | Fold.Q78.IsContinuum H ∧ ContainsNested H p}

/-! ## Basic facts -/

omit [CompactSpace S] in
theorem ContainsNested.mem_interior {H : Set S} {p : S} (h : ContainsNested H p) :
    p ∈ interior H := by
  obtain ⟨H', -, hH'H, hp⟩ := h
  exact hH'H (interior_subset hp)

omit [CompactSpace S] in
theorem bingElt_subset {p : S} {H : Set S} (hH : Fold.Q78.IsContinuum H)
    (hN : ContainsNested H p) : bingElt p ⊆ H :=
  sInter_subset_of_mem ⟨hH, hN⟩

omit [CompactSpace S] in
theorem mem_bingElt (p : S) : p ∈ bingElt p :=
  mem_sInter.mpr fun _ hH => interior_subset hH.2.mem_interior

omit [CompactSpace S] in
/-- A point outside `bingElt p` is outside some continuum containing `p` "doubly interiorly". -/
theorem exists_of_not_mem_bingElt {p x : S} (hx : x ∉ bingElt p) :
    ∃ H, Fold.Q78.IsContinuum H ∧ ContainsNested H p ∧ x ∉ H := by
  by_contra hno
  push_neg at hno
  exact hx (mem_sInter.mpr fun H hH => hno H hH.1 hH.2)

theorem BingS.univ_containsNested (hS : BingS S) (p : S) :
    Fold.Q78.IsContinuum (univ : Set S) ∧ ContainsNested (univ : Set S) p := by
  refine ⟨(hS.univ_nbhd p).1, univ, (hS.univ_nbhd p).1, ?_, (hS.univ_nbhd p).2⟩
  rw [interior_univ]

theorem bingElt_isContinuum (hS : BingS S) (p : S) : Fold.Q78.IsContinuum (bingElt p) :=
  prop1_inter_continuum hS ⟨univ, hS.univ_containsNested p⟩ (fun _ hH => hH.1) ⟨p, mem_bingElt p⟩

omit [CompactSpace S] in
/-- **The bridge to batch 92**: the one-layer element lies in Bing's element. -/
theorem gElt_subset_bingElt (p : S) : gElt p ⊆ bingElt p :=
  subset_sInter fun _ hH => gElt_subset hH.1 hH.2.mem_interior

/-- The continua containing `p` doubly interiorly are closed under intersection. -/
theorem BingS.nested_inter (hS : BingS S) {p : S} {H K : Set S} (hH : Fold.Q78.IsContinuum H)
    (hHp : ContainsNested H p) (hK : Fold.Q78.IsContinuum K) (hKp : ContainsNested K p) :
    Fold.Q78.IsContinuum (H ∩ K) ∧ ContainsNested (H ∩ K) p := by
  obtain ⟨H', hH', hH'H, hpH'⟩ := hHp
  obtain ⟨K', hK', hK'K, hpK'⟩ := hKp
  refine ⟨hS.inter_two hH hK ⟨p, interior_subset (hH'H (interior_subset hpH')),
    interior_subset (hK'K (interior_subset hpK'))⟩, H' ∩ K',
    hS.inter_two hH' hK' ⟨p, interior_subset hpH', interior_subset hpK'⟩, ?_, ?_⟩
  · rw [interior_inter]; exact inter_subset_inter hH'H hK'K
  · rw [interior_inter]; exact ⟨hpH', hpK'⟩

/-- **Neighbourhood form**: inside any open set containing `bingElt p` there is a continuum
containing `p` doubly interiorly (compactness). -/
theorem BingS.exists_nested_subset (hS : BingS S) {p : S} {U : Set S} (hU : IsOpen U)
    (hg : bingElt p ⊆ U) : ∃ H, Fold.Q78.IsContinuum H ∧ ContainsNested H p ∧ H ⊆ U := by
  classical
  set T : Set (Set S) := {H : Set S | Fold.Q78.IsContinuum H ∧ ContainsNested H p} with hT
  have hfin : ∀ u : Finset T, Fold.Q78.IsContinuum (⋂ i ∈ u, (i : Set S)) ∧
      ContainsNested (⋂ i ∈ u, (i : Set S)) p := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using hS.univ_containsNested p
    | insert a u _ ih =>
      rw [Finset.set_biInter_insert]
      exact hS.nested_inter a.2.1 a.2.2 ih.1 ih.2
  obtain ⟨u, hu⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun i : T => (i : Set S)) (fun i => i.2.1.1.isClosed) (by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_iInter, mem_empty_iff_false, iff_false,
        not_and]
      intro hxU hall
      exact hxU (hg (mem_sInter.mpr fun H hH => hall ⟨H, hH⟩)))
  refine ⟨_, (hfin u).1, (hfin u).2, fun x hx => ?_⟩
  by_contra hxU
  have : x ∈ Uᶜ ∩ ⋂ i ∈ u, (i : Set S) := ⟨hxU, hx⟩
  rw [hu] at this; exact this

/-! ## The partition property -/

/-- **Bing's `K_2`, `K_4`.** If `H₂ ⊆ int H₄` are continua, `q ∈ int H₂` and `p ∉ H₄`, then
`q ∉ bingElt p`. With `C_i` the component of `S − H_i` through `p` (open, by property 2), the
continuum `K₂ = cl C₂` contains interiorly the continuum `K₄ = cl C₄`, which contains `p`
interiorly, and `q ∉ K₂`. The point of the flag: `cl C₄ ⊆ C₂`. A point `y ∈ cl C₄` is not in `H₂`
(the open set `int H₄ ⊇ H₂` misses `C₄`), and `cl C₂ ∖ H₂ ⊆ C₂` because the components of `S − H₂`
are open. -/
theorem not_mem_bingElt_of (hS : BingS S) {p q : S} {H₂ H₄ : Set S}
    (h₂ : Fold.Q78.IsContinuum H₂) (h₄ : Fold.Q78.IsContinuum H₄) (h₂₄ : H₂ ⊆ interior H₄)
    (hq : q ∈ interior H₂) (hp : p ∉ H₄) : q ∉ bingElt p := by
  have hp2 : p ∉ H₂ := fun h => hp (interior_subset (h₂₄ h))
  set C₂ := connectedComponentIn H₂ᶜ p with hC₂
  set C₄ := connectedComponentIn H₄ᶜ p with hC₄
  have o₂ : IsOpen C₂ := hS.isOpen_component_compl h₂ hp2
  have o₄ : IsOpen C₄ := hS.isOpen_component_compl h₄ hp
  have hC₄₂ : C₄ ⊆ C₂ :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hp)
      ((connectedComponentIn_subset _ _).trans
        (compl_subset_compl.mpr (h₂₄.trans interior_subset)))
  have hcl : closure C₄ ⊆ C₂ := by
    intro y hy
    have hyH₂ : y ∉ H₂ := by
      intro hyH
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy _ isOpen_interior (h₂₄ hyH)
      exact connectedComponentIn_subset _ _ hz2 (interior_subset hz1)
    obtain ⟨z, hzy, hzC⟩ := mem_closure_iff.mp (closure_mono hC₄₂ hy) _
      (hS.isOpen_component_compl h₂ hyH₂) (mem_connectedComponentIn hyH₂)
    rw [hC₂, connectedComponentIn_eq hzC, ← connectedComponentIn_eq hzy]
    exact mem_connectedComponentIn hyH₂
  have hK₂ : Fold.Q78.IsContinuum (closure C₂) :=
    isContinuum_of_closed isClosed_closure (isConnected_connectedComponentIn_iff.mpr hp2).closure
  have hK₄ : Fold.Q78.IsContinuum (closure C₄) :=
    isContinuum_of_closed isClosed_closure (isConnected_connectedComponentIn_iff.mpr hp).closure
  have hN : ContainsNested (closure C₂) p :=
    ⟨closure C₄, hK₄, hcl.trans (interior_maximal subset_closure o₂),
      interior_maximal subset_closure o₄ (mem_connectedComponentIn hp)⟩
  intro hqg
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (bingElt_subset hK₂ hN hqg) _ isOpen_interior hq
  exact connectedComponentIn_subset _ _ hz2 (interior_subset hz1)

/-- Bing's paragraph on the partition, in both directions: if `q ∈ g_p` then `p ∈ g_q` and
`g_p ⊆ g_q`. -/
theorem bingElt_mem_imp (hS : BingS S) {p q : S} (hq : q ∈ bingElt p) :
    p ∈ bingElt q ∧ bingElt p ⊆ bingElt q := by
  constructor
  · by_contra hpq
    obtain ⟨H₁, h₁, ⟨H₂, h₂, h₂₁, hq₂⟩, hpH₁⟩ := exists_of_not_mem_bingElt hpq
    exact not_mem_bingElt_of hS h₂ h₁ h₂₁ hq₂ hpH₁ hq
  · intro p' hp'
    by_contra hp'q
    obtain ⟨H₁, h₁, ⟨H₂, h₂, h₂₁, hq₂⟩, hp'H₁⟩ := exists_of_not_mem_bingElt hp'q
    obtain ⟨H₃, h₃, h₃₁, h₂₃⟩ := prop6_between hS h₁ h₂ ⟨q, hq₂⟩ h₂₁
    obtain ⟨H₄, h₄, h₄₃, h₂₄⟩ := prop6_between hS h₃ h₂ ⟨q, hq₂⟩ h₂₃
    by_cases hpH₄ : p ∈ H₄
    · exact hp'H₁ (bingElt_subset h₁ ⟨H₃, h₃, h₃₁, h₄₃ hpH₄⟩ hp')
    · exact not_mem_bingElt_of hS h₂ h₄ h₂₄ hq₂ hpH₄ hq

/-- **Theorem 8, partition**: the elements `bingElt p` partition `S`. -/
theorem bingElt_partition (hS : BingS S) (p q : S) (hq : q ∈ bingElt p) :
    bingElt p = bingElt q :=
  Subset.antisymm (bingElt_mem_imp hS hq).2 (bingElt_mem_imp hS (bingElt_mem_imp hS hq).1).2

theorem bingElt_disjoint (hS : BingS S) {p q : S} (h : bingElt p ≠ bingElt q) :
    Disjoint (bingElt p) (bingElt q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  exact h ((bingElt_partition hS p x hxp).trans (bingElt_partition hS q x hxq).symm)

/-! ## Upper semicontinuity, (a), (b), (c) -/

/-- **Upper semicontinuity.** -/
theorem bingElt_usc (hS : BingS S) (U : Set S) (hU : IsOpen U) :
    IsOpen (⋃ q ∈ {q | bingElt q ⊆ U}, bingElt q) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨q, hqU, hxq⟩ := mem_iUnion₂.mp hx
  have hxU : bingElt x ⊆ U := (bingElt_partition hS q x hxq) ▸ hqU
  obtain ⟨H, hH, ⟨H', hH', hH'H, hxH'⟩, hHU⟩ := hS.exists_nested_subset hU hxU
  refine ⟨interior H', fun y hy => mem_iUnion₂.mpr ⟨y,
    (bingElt_subset hH ⟨H', hH', hH'H, hy⟩).trans hHU, mem_bingElt y⟩, isOpen_interior, hxH'⟩

/-- **Theorem 8 (b)**: no element has interior points. As for `gElt`; the side continuum `Z`
contains `K₁` interiorly and `K₁` contains `x₁` interiorly, which is exactly the two layers. -/
theorem bingElt_interior_eq_empty (hS : BingS S) (p : S) : interior (bingElt p) = ∅ := by
  by_contra hne
  obtain ⟨K₁, K₂, hK₁, hK₂, hK₁g, hK₂g, d, hi₁, hi₂⟩ :=
    hS.two_disjoint_with_interior isOpen_interior (nonempty_iff_ne_empty.mpr hne)
      (bingElt_isContinuum hS p) interior_subset
  obtain ⟨K, hK, -, hsep⟩ := prop5_exists_separating hS hK₁ hK₂ hi₁ hi₂ d
  obtain ⟨Z, hZ, -, hK₁Z, dZ⟩ := hS.side_of_separates hK hsep hK₁.2.1 hK₂.2.1
  obtain ⟨x₁, hx₁⟩ := hi₁
  obtain ⟨x₂, hx₂⟩ := hi₂
  have h1 : bingElt x₁ ⊆ Z := bingElt_subset hZ ⟨K₁, hK₁, hK₁Z, hx₁⟩
  have h2 : x₂ ∈ bingElt x₁ :=
    bingElt_partition hS p x₁ (hK₁g (interior_subset hx₁)) ▸ hK₂g (interior_subset hx₂)
  exact Set.disjoint_left.mp dZ (h1 h2) (interior_subset hx₂)

omit [CompactSpace S] in
/-- Enlarging the separating set: if `A` separates `B` from `C` and `A ⊆ A'` with `A'` closed and
disjoint from `B` and `C`, then `A'` separates `B` from `C`. -/
theorem separates_enlarge {A A' B C : Set S} (h : Separates A B C) (hAA' : A ⊆ A')
    (hA' : IsClosed A') (dB : Disjoint A' B) (dC : Disjoint A' C) : Separates A' B C := by
  obtain ⟨-, -, U, V, hU, hV, hUV, hcov, hBU, hCV⟩ := h
  refine ⟨dB, dC, U ∩ A'ᶜ, V ∩ A'ᶜ, hU.inter hA'.isOpen_compl, hV.inter hA'.isOpen_compl,
    hUV.mono inter_subset_left inter_subset_left, ?_, ?_, ?_⟩
  · rintro x ⟨-, hx⟩
    rcases hcov ⟨mem_univ x, fun h => hx (hAA' h)⟩ with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  · exact fun x hx => ⟨hBU hx, fun h => Set.disjoint_left.mp dB h hx⟩
  · exact fun x hx => ⟨hCV hx, fun h => Set.disjoint_left.mp dC h hx⟩

/-- **From neighbourhood continua to elements**, for `bingElt`: batch 92's `gElt_separates_of`
gives the separation by `gElt p`, and `bingElt p` (closed, inside `H₁`) is an enlargement of it. -/
theorem bingElt_separates_of (hS : BingS S) {p : S} {H₁ H₂ H₃ : Set S}
    (h₁ : Fold.Q78.IsContinuum H₁) (hp : ContainsNested H₁ p) (h₂ : Fold.Q78.IsContinuum H₂)
    (h₃ : Fold.Q78.IsContinuum H₃) (hi₂ : (interior H₂).Nonempty)
    (hi₃ : (interior H₃).Nonempty) (d₁₂ : Disjoint H₁ H₂) (d₂₃ : Disjoint H₂ H₃)
    (d₁₃ : Disjoint H₁ H₃) (hsep : Separates H₁ H₂ H₃) : Separates (bingElt p) H₂ H₃ := by
  have hsub := bingElt_subset h₁ hp
  exact separates_enlarge (gElt_separates_of hS h₁ hp.mem_interior h₂ h₃ hi₂ hi₃ d₁₂ d₂₃ d₁₃
    hsep) (gElt_subset_bingElt p) (bingElt_isContinuum hS p).1.isClosed (d₁₂.mono_left hsub)
    (d₁₃.mono_left hsub)

/-- **Theorem 8 (a)**: of three distinct elements one separates the other two. -/
theorem bingElt_separates_triple (hS : BingS S) (p q r : S) (hpq : bingElt p ≠ bingElt q)
    (hqr : bingElt q ≠ bingElt r) (hpr : bingElt p ≠ bingElt r) :
    Separates (bingElt p) (bingElt q) (bingElt r) ∨ Separates (bingElt q) (bingElt p) (bingElt r) ∨
      Separates (bingElt r) (bingElt p) (bingElt q) := by
  have cp := (bingElt_isContinuum hS p).1
  have cq := (bingElt_isContinuum hS q).1
  have cr := (bingElt_isContinuum hS r).1
  obtain ⟨U₁₂, U₂₁, o₁₂, o₂₁, s₁₂, s₂₁, d₁₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact cp cq (bingElt_disjoint hS hpq)
  obtain ⟨U₁₃, U₃₁, o₁₃, o₃₁, s₁₃, s₃₁, d₁₃⟩ :=
    SeparatedNhds.of_isCompact_isCompact cp cr (bingElt_disjoint hS hpr)
  obtain ⟨U₂₃, U₃₂, o₂₃, o₃₂, s₂₃, s₃₂, d₂₃⟩ :=
    SeparatedNhds.of_isCompact_isCompact cq cr (bingElt_disjoint hS hqr)
  obtain ⟨H₁, h₁, hp₁, hH₁⟩ := hS.exists_nested_subset (o₁₂.inter o₁₃) (subset_inter s₁₂ s₁₃)
  obtain ⟨H₂, h₂, hp₂, hH₂⟩ := hS.exists_nested_subset (o₂₁.inter o₂₃) (subset_inter s₂₁ s₂₃)
  obtain ⟨H₃, h₃, hp₃, hH₃⟩ := hS.exists_nested_subset (o₃₁.inter o₃₂) (subset_inter s₃₁ s₃₂)
  have e₁₂ : Disjoint H₁ H₂ :=
    d₁₂.mono (hH₁.trans inter_subset_left) (hH₂.trans inter_subset_left)
  have e₁₃ : Disjoint H₁ H₃ :=
    d₁₃.mono (hH₁.trans inter_subset_right) (hH₃.trans inter_subset_left)
  have e₂₃ : Disjoint H₂ H₃ :=
    d₂₃.mono (hH₂.trans inter_subset_right) (hH₃.trans inter_subset_right)
  have g₁ := bingElt_subset h₁ hp₁
  have g₂ := bingElt_subset h₂ hp₂
  have g₃ := bingElt_subset h₃ hp₃
  have i₁ : (interior H₁).Nonempty := ⟨p, hp₁.mem_interior⟩
  have i₂ : (interior H₂).Nonempty := ⟨q, hp₂.mem_interior⟩
  have i₃ : (interior H₃).Nonempty := ⟨r, hp₃.mem_interior⟩
  rcases prop4_separates hS h₁ h₂ h₃ i₁ i₂ i₃ e₁₂ e₂₃ e₁₃ with h | h | h
  · exact Or.inl (separates_mono (bingElt_separates_of hS h₁ hp₁ h₂ h₃ i₂ i₃ e₁₂ e₂₃
      e₁₃ h) g₂ g₃)
  · exact Or.inr (Or.inl (separates_mono (bingElt_separates_of hS h₂ hp₂ h₁ h₃ i₁ i₃
      e₁₂.symm e₁₃ e₂₃ h) g₁ g₃))
  · exact Or.inr (Or.inr (separates_mono (bingElt_separates_of hS h₃ hp₃ h₁ h₂ i₁ i₂
      e₁₃.symm e₁₂ e₂₃.symm h) g₁ g₂))

/-- **Theorem 8 (c)**: a subcontinuum meeting two different end elements is `S` (the batch-92
argument for `gElt`, renamed). -/
theorem bingElt_irreducible (hS : BingS S) (r s : S)
    (hr : ∀ q q' : S, bingElt q ≠ bingElt r → bingElt q' ≠ bingElt r → bingElt q ≠ bingElt q' →
      ¬ Separates (bingElt r) (bingElt q) (bingElt q'))
    (hs : ∀ q q' : S, bingElt q ≠ bingElt s → bingElt q' ≠ bingElt s → bingElt q ≠ bingElt q' →
      ¬ Separates (bingElt s) (bingElt q) (bingElt q'))
    (hrs : bingElt r ≠ bingElt s) (M : Set S) (hM : Fold.Q78.IsContinuum M) (hrM : r ∈ M)
    (hsM : s ∈ M) : M = univ := by
  by_contra hMne
  obtain ⟨x₁, hx₁⟩ := (ne_univ_iff_exists_notMem M).mp hMne
  have hint := bingElt_interior_eq_empty hS
  have hMo : IsOpen Mᶜ := hM.1.isClosed.isOpen_compl
  have hcl : ∀ q, IsClosed (bingElt q) := fun q => (bingElt_isContinuum hS q).1.isClosed
  have notsub : ∀ F : Set S, interior F = ∅ → (Mᶜ).Nonempty → ¬ Mᶜ ⊆ F := fun F hF hne h => by
    obtain ⟨y, hy⟩ := hne
    have := interior_maximal h hMo hy
    rw [hF] at this; exact this
  obtain ⟨x₂, hx₂M, hx₂g⟩ := not_subset.mp (notsub _ (hint x₁) ⟨x₁, hx₁⟩)
  obtain ⟨x₃, hx₃M, hx₃g⟩ := not_subset.mp (notsub _
    (by rw [interior_union_isClosed_of_interior_empty (hcl x₁) (hint x₂)]; exact hint x₁)
    ⟨x₁, hx₁⟩)
  simp only [mem_union, not_or] at hx₃g
  have ne : ∀ {a b : S}, a ∉ bingElt b → bingElt a ≠ bingElt b :=
    fun h e => h (e ▸ mem_bingElt _)
  have meets : ∀ x : S, (bingElt x ∩ M).Nonempty := by
    intro x
    by_contra hno
    rw [not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hno
    have hxr : bingElt x ≠ bingElt r := fun e =>
      Set.disjoint_left.mp hno (e ▸ mem_bingElt r : r ∈ bingElt x) hrM
    have hxs : bingElt x ≠ bingElt s := fun e =>
      Set.disjoint_left.mp hno (e ▸ mem_bingElt s : s ∈ bingElt x) hsM
    rcases bingElt_separates_triple hS x r s hxr hrs hxs with h | h | h
    · exact not_separates_of_preconnected hM.2.2 hno.symm ⟨r, hrM, mem_bingElt r⟩
        ⟨s, hsM, mem_bingElt s⟩ h
    · exact hr x s hxr hrs.symm hxs h
    · exact hs x r hxs hrs hxr h
  set T := M ∪ bingElt x₁ ∪ bingElt x₂ ∪ bingElt x₃ with hT_def
  have hT : Fold.Q78.IsContinuum T := by
    have c1 := isContinuum_union hM (bingElt_isContinuum hS x₁)
      (by rw [inter_comm]; exact meets x₁)
    have c2 := isContinuum_union c1 (bingElt_isContinuum hS x₂) (by
      obtain ⟨y, hy, hyM⟩ := meets x₂; exact ⟨y, Or.inl hyM, hy⟩)
    exact isContinuum_union c2 (bingElt_isContinuum hS x₃) (by
      obtain ⟨y, hy, hyM⟩ := meets x₃; exact ⟨y, Or.inl (Or.inl hyM), hy⟩)
  have d12 := bingElt_disjoint hS (ne hx₂g).symm
  have d13 := bingElt_disjoint hS (ne hx₃g.1).symm
  have d23 := bingElt_disjoint hS (ne hx₃g.2).symm
  have cl : ∀ q, closure (bingElt q \ M) ⊆ bingElt q := fun q => closure_minimal diff_subset (hcl q)
  refine hS.atriodic T (subset_univ _) ⟨hT, M, hM, subset_union_left.trans
    (subset_union_left.trans subset_union_left), bingElt x₁ \ M, bingElt x₂ \ M, bingElt x₃ \ M,
    ⟨x₁, mem_bingElt x₁, hx₁⟩, ⟨x₂, mem_bingElt x₂, hx₂M⟩, ⟨x₃, mem_bingElt x₃, hx₃M⟩, ?_,
    (d12.mono (cl x₁) diff_subset), (d12.mono diff_subset (cl x₂)),
    (d13.mono (cl x₁) diff_subset), (d13.mono diff_subset (cl x₃)),
    (d23.mono (cl x₂) diff_subset), (d23.mono diff_subset (cl x₃))⟩
  ext y
  simp only [hT_def, mem_diff, mem_union]
  tauto

end HPC.Plane
