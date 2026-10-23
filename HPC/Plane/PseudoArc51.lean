import HPC.Plane.EndPoints51
import HPC.PseudoArc.Recon86Chain
import HPC.Plane.PA51Lift
import HPC.Plane.PA51Counter

/-!
# Bing, *Concerning hereditarily indecomposable continua* (Pacific J. Math. 1 (1951), 43–51),
# Theorem 1 and its consequences

Batch 88 (COMMISSION-batch88.md). The skeleton's definition and nine statements. Seven are proved
as stated. Two are **false as stated** and are kept below in comments, each with a Lean refutation
and a reshaped, proved replacement:

* `theorem12_of` (Theorem 12 with `IsCompact Δ.M` in place of a compact ambient space): refuted by
  `theorem12_of_false`. A description in a non-complete space can describe a compact set that is
  not connected (`PA51.exists_description_compact_disconnected`: the plane description with every
  point of its continuum except `P`, `Q` removed from the plane). Reshaped: the links of each
  description lie in a compact set, as in `Transfer.lean`.
* `isPseudoArc_of_description` (same hypothesis `IsCompact Δ.M`): refuted by
  `isPseudoArc_of_description_false`, same counterexample. Reshaped: links in a compact set
  (`isPseudoArc_of_description`), or a compact ambient space (`isPseudoArc_of_description'`).

`theorem1_HIC`, `theorem1_HIC'`, `isPseudoArc_iff_endPoints` keep their statements, and so do
`exists_description_of_chainable_HI`, `homogeneous_of_isPseudoArc`, `isPseudoArc_of_subcontinuum`
and `oppositeEndPoints_of_composants`. Added: `homeomorphic_subcontinuum`, `theorem1_snake`,
`isPseudoArc_plane`, `pseudoArc_unique`, `exists_not_mem_composant`.

The proof of Theorem 1 (`exists_description_of_chainable_HI`) is in `PA51Crook.lean` (crookedness
eventually, Bing's first paragraph, with a corrected choice of witnesses), `PA51Pre.lean` (the
sequence of mutually crooked chains, and the description from `p` to `q`, in the compact space
`M`), and `PA51Lift.lean` (from the space `M` back to `X`).

`IsSnakeLike` (= Bing's "can be chained"), `IsEpsChain`, `IsEndPoint`, `OppositeEndPoints`,
`IsHereditarilyIndecomposable` are from `Snake51.lean` / `EndPoints51.lean`; `composant` from
`PseudoArc/Statements79.lean`; `Description` from `PseudoArc/Description.lean`.
-/

namespace HPC.Plane

open Set

variable {X : Type*} [MetricSpace X]

/-- **A pseudo-arc**: a nondegenerate chainable hereditarily indecomposable (compact) continuum
(Bing 1951, p. 45: "all of these continua are topologically equivalent and are pseudo-arcs"). -/
def IsPseudoArc (M : Set X) : Prop :=
  IsSnakeLike M ∧ IsHereditarilyIndecomposable M ∧ M.Nontrivial

/-- **The body of Bing's proof of Theorem 1**: a nondegenerate chainable hereditarily
indecomposable continuum with two points in different composants admits a description from the
one to the other whose continuum is `M`. (COMMISSION-batch88.md §2–3.) -/
theorem exists_description_of_chainable_HI {M : Set X} (hM : IsPseudoArc M) {p q : X}
    (hp : p ∈ M) (hq : q ∈ M) (hpq : q ∉ composant M p) :
    ∃ Δ : Description X p q, Δ.M = M := by
  obtain ⟨hs, hh, hnd⟩ := hM
  obtain ⟨Δ', hΔ'⟩ := PA51.exists_description_sub hs hh hnd hp hq hpq
  exact PA51.lift_description hs.1.1 hp hq Δ' hΔ'

-- Commented-out statement `theorem12_of` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- The described continuum of a description whose links lie in `K` is homeomorphic (by the
identity) to that of its restriction to `K`. -/
def restrictHomeo {P Q : X} (Δ : Description X P Q) (K : Set X)
    (hK : ∀ i t, (Δ.D i).link t ⊆ K) : (Δ.restrict K hK).M ≃ₜ Δ.M where
  toFun z := ⟨z.1.1, (Set.ext_iff.mp (Δ.restrict_M K hK) z.1).mp z.2⟩
  invFun z := ⟨⟨z.1, Δ.M_subset K hK z.2⟩, (Set.ext_iff.mp (Δ.restrict_M K hK) _).mpr z.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Bing 1948, Theorem 12, without a compact ambient space** (reshaped): two descriptions whose
links lie in compact sets have homeomorphic continua with the end points corresponding. -/
theorem theorem12_of {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂] {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂) (h₁ : P₁ ≠ Q₁) (h₂ : P₂ ≠ Q₂)
    (K₁ : Set X₁) (hK₁ : ∀ i t, (Δ₁.D i).link t ⊆ K₁) (hK₁c : IsCompact K₁)
    (K₂ : Set X₂) (hK₂ : ∀ i t, (Δ₂.D i).link t ⊆ K₂) (hK₂c : IsCompact K₂) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M,
      T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ := by
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁c
  haveI : CompactSpace K₂ := isCompact_iff_compactSpace.mp hK₂c
  obtain ⟨T, hTP, hTQ⟩ := theorem12 (Δ₁.restrict K₁ hK₁) (Δ₂.restrict K₂ hK₂)
    (fun h => h₁ (congrArg Subtype.val h)) (fun h => h₂ (congrArg Subtype.val h))
  refine ⟨((restrictHomeo Δ₁ K₁ hK₁).symm.trans T).trans (restrictHomeo Δ₂ K₂ hK₂), ?_, ?_⟩
  · show restrictHomeo Δ₂ K₂ hK₂ (T ((restrictHomeo Δ₁ K₁ hK₁).symm _)) = _
    have e : (restrictHomeo Δ₁ K₁ hK₁).symm ⟨P₁, Δ₁.P_mem_M⟩ =
        ⟨⟨P₁, Δ₁.P_mem_of K₁ hK₁ 0⟩, (Δ₁.restrict K₁ hK₁).P_mem_M⟩ := rfl
    rw [e, hTP]
    rfl
  · show restrictHomeo Δ₂ K₂ hK₂ (T ((restrictHomeo Δ₁ K₁ hK₁).symm _)) = _
    have e : (restrictHomeo Δ₁ K₁ hK₁).symm ⟨Q₁, Δ₁.Q_mem_M⟩ =
        ⟨⟨Q₁, Δ₁.Q_mem_of K₁ hK₁ 0⟩, (Δ₁.restrict K₁ hK₁).Q_mem_M⟩ := rfl
    rw [e, hTQ]
    rfl

/-- **The skeleton's `theorem12_of` is false**: there are descriptions `Δ₁`, `Δ₂` with `P ≠ Q`
and compact continua that are not homeomorphic (`Δ₁.M` has two points, `Δ₂.M` is the plane
pseudo-arc). -/
theorem theorem12_of_false : ¬ ∀ (X₁ X₂ : Type) [MetricSpace X₁] [MetricSpace X₂] (P₁ Q₁ : X₁)
    (P₂ Q₂ : X₂) (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂), P₁ ≠ Q₁ → P₂ ≠ Q₂ →
      IsCompact Δ₁.M → IsCompact Δ₂.M → ∃ T : Δ₁.M ≃ₜ Δ₂.M,
        T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ := by
  intro h
  obtain ⟨Y, _, P, Q, Δ, hPQ, hc, hnc⟩ := PA51.exists_description_compact_disconnected
  obtain ⟨P₀, Q₀, hPQ₀, ⟨Δ₀⟩⟩ := exists_description_plane
  obtain ⟨hKc, hK⟩ := Description.links_subset_compact Δ₀
  have hcont := Δ₀.isContinuum_M_of _ hK hKc
  obtain ⟨T, -, -⟩ := h Y Pt P Q P₀ Q₀ Δ Δ₀ hPQ hPQ₀ hc hcont.1
  haveI : ConnectedSpace Δ₀.M := isConnected_iff_connectedSpace.mp hcont.2
  haveI : ConnectedSpace Δ.M := T.symm.surjective.connectedSpace T.symm.continuous
  exact hnc (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected

/-- **Bing 1951 (Pacific J. Math.), Theorem 1, the "in fact" clause.** -/
theorem theorem1_HIC {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') {p q : X} {p' q' : X'}
    (hp : p ∈ M) (hq : q ∈ M) (hpq : q ∉ composant M p)
    (hp' : p' ∈ M') (hq' : q' ∈ M') (hpq' : q' ∉ composant M' p') :
    ∃ T : M ≃ₜ M', T ⟨p, hp⟩ = ⟨p', hp'⟩ ∧ T ⟨q, hq⟩ = ⟨q', hq'⟩ := by
  obtain ⟨hs, hh, hnd⟩ := hM
  obtain ⟨hs', hh', hnd'⟩ := hM'
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hs.1.1
  haveI : CompactSpace M' := isCompact_iff_compactSpace.mp hs'.1.1
  obtain ⟨Δ₁, hΔ₁⟩ := PA51.exists_description_sub hs hh hnd hp hq hpq
  obtain ⟨Δ₂, hΔ₂⟩ := PA51.exists_description_sub hs' hh' hnd' hp' hq' hpq'
  have hne₁ : (⟨p, hp⟩ : M) ≠ ⟨q, hq⟩ := fun h =>
    PA51.ne_of_not_mem_composant hnd hp hpq (congrArg Subtype.val h)
  have hne₂ : (⟨p', hp'⟩ : M') ≠ ⟨q', hq'⟩ := fun h =>
    PA51.ne_of_not_mem_composant hnd' hp' hpq' (congrArg Subtype.val h)
  obtain ⟨T, hTP, hTQ⟩ := theorem12 Δ₁ Δ₂ hne₁ hne₂
  let e₁ : M ≃ₜ Δ₁.M := (Homeomorph.Set.univ M).symm.trans (Homeomorph.setCongr hΔ₁.symm)
  let e₂ : M' ≃ₜ Δ₂.M := (Homeomorph.Set.univ M').symm.trans (Homeomorph.setCongr hΔ₂.symm)
  refine ⟨(e₁.trans T).trans e₂.symm, ?_, ?_⟩
  · show e₂.symm (T (e₁ ⟨p, hp⟩)) = _
    have e : e₁ ⟨p, hp⟩ = ⟨⟨p, hp⟩, Δ₁.P_mem_M⟩ := rfl
    rw [e, hTP]
    rfl
  · show e₂.symm (T (e₁ ⟨q, hq⟩)) = _
    have e : e₁ ⟨q, hq⟩ = ⟨⟨q, hq⟩, Δ₁.Q_mem_M⟩ := rfl
    rw [e, hTQ]
    rfl

/-- Every point of a pseudo-arc has a point of the pseudo-arc outside its composant
(`composant_ne_of_indecomposable`, Bing 1948 batch 81, applied in the compact space `M`). -/
theorem exists_not_mem_composant {M : Set X} (hM : IsPseudoArc M) {p : X} (hp : p ∈ M) :
    ∃ q ∈ M, q ∉ composant M p := by
  obtain ⟨hs, hh, hnd⟩ := hM
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hs.1.1
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.mp hs.1.2
  have hcont : Fold.Q78.IsContinuum (univ : Set M) := ⟨isCompact_univ, isConnected_univ⟩
  have hnd' : (univ : Set M).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnd
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩
  have hne := composant_ne_of_indecomposable (PA51.hI_sub hh univ hcont) hnd' (mem_univ ⟨p, hp⟩)
  obtain ⟨y, -, hy⟩ : ∃ y ∈ (univ : Set M), y ∉ composant univ ⟨p, hp⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hne (Subset.antisymm (sUnion_subset fun K hK => hK.2.1) hcon)
  refine ⟨y.1, y.2, fun hyc => hy ?_⟩
  obtain ⟨K, ⟨hK, hKM, hKne, hpK⟩, hyK⟩ := mem_sUnion.mp hyc
  refine mem_sUnion.mpr ⟨Subtype.val ⁻¹' K, ⟨⟨?_, ?_⟩, subset_univ _, ?_, hpK⟩, hyK⟩
  · exact hs.1.1.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK.1
  · refine ⟨⟨⟨p, hp⟩, hpK⟩, ?_⟩
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hKM]
    exact hK.2.isPreconnected
  · intro h
    apply hKne
    refine Subset.antisymm hKM fun x hx => ?_
    have : (⟨x, hx⟩ : M) ∈ Subtype.val ⁻¹' K := h ▸ mem_univ _
    exact this

/-- **Theorem 1**: any two pseudo-arcs are homeomorphic. (Also *Snake-like continua*, Theorem 1.) -/
theorem theorem1_HIC' {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') : Nonempty (M ≃ₜ M') := by
  obtain ⟨p, hp, -⟩ := hM.2.2
  obtain ⟨p', hp', -⟩ := hM'.2.2
  obtain ⟨q, hq, hpq⟩ := exists_not_mem_composant hM hp
  obtain ⟨q', hq', hpq'⟩ := exists_not_mem_composant hM' hp'
  obtain ⟨T, -⟩ := theorem1_HIC hM hM' hp hq hpq hp' hq' hpq'
  exact ⟨T⟩

/-- A pseudo-arc is homogeneous (Bing, p. 45). -/
theorem homogeneous_of_isPseudoArc {M : Set X} (hM : IsPseudoArc M) (p q : X) (hp : p ∈ M)
    (hq : q ∈ M) : ∃ T : M ≃ₜ M, T ⟨p, hp⟩ = ⟨q, hq⟩ := by
  obtain ⟨r, hr, hpr⟩ := exists_not_mem_composant hM hp
  obtain ⟨s, hs, hqs⟩ := exists_not_mem_composant hM hq
  obtain ⟨T, hT, -⟩ := theorem1_HIC hM hM hp hr hpr hq hs hqs
  exact ⟨T, hT⟩

/-- A nondegenerate subcontinuum of a pseudo-arc is a pseudo-arc, hence homeomorphic to it
(Bing, p. 45; Moise's property). -/
theorem isPseudoArc_of_subcontinuum {M K : Set X} (hM : IsPseudoArc M) (hK : K ⊆ M)
    (hKc : Fold.Q78.IsContinuum K) (hKnd : K.Nontrivial) : IsPseudoArc K := by
  refine ⟨⟨hKc, fun ε hε => ?_⟩, fun L hL hLc => hM.2.1 L (hL.trans hK) hLc, hKnd⟩
  obtain ⟨n, D, hD, hMD⟩ := hM.1.2 ε hε
  exact ⟨n, D, hD, hK.trans hMD⟩

/-- A pseudo-arc is homeomorphic to each of its nondegenerate subcontinua (Bing, p. 45). -/
theorem homeomorphic_subcontinuum {M K : Set X} (hM : IsPseudoArc M) (hK : K ⊆ M)
    (hKc : Fold.Q78.IsContinuum K) (hKnd : K.Nontrivial) : Nonempty (K ≃ₜ M) :=
  theorem1_HIC' (isPseudoArc_of_subcontinuum hM hK hKc hKnd) hM

-- Commented-out statement `isPseudoArc_of_description` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- **The continuum of a description is a pseudo-arc** (reshaped: the links lie in a compact
set; this covers the plane continuum of `Plane.pseudoArc_exists`). -/
theorem isPseudoArc_of_description {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    (K : Set X) (hK : ∀ i t, (Δ.D i).link t ⊆ K) (hKc : IsCompact K) : IsPseudoArc Δ.M := by
  refine ⟨⟨Δ.isContinuum_M_of K hK hKc, fun ε hε => ?_⟩, fun L hL hLc => Description.theorem10 Δ L
    hL hLc, ⟨P, Δ.P_mem_M, Q, Δ.Q_mem_M, hPQ⟩⟩
  obtain ⟨i, hi⟩ := (Δ.ε_tendsto.eventually (gt_mem_nhds hε)).exists
  exact ⟨Δ.n i, Δ.D i, fun t => ⟨Δ.bdd i t, (Δ.diam_le i t).trans_lt hi⟩, Δ.M_subset_union i⟩

/-- The continuum of a description in a compact space is a pseudo-arc. -/
theorem isPseudoArc_of_description' [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) : IsPseudoArc Δ.M :=
  isPseudoArc_of_description Δ hPQ univ (fun _ _ => subset_univ _) isCompact_univ

/-- **The skeleton's `isPseudoArc_of_description` is false.** -/
theorem isPseudoArc_of_description_false : ¬ ∀ (Y : Type) [MetricSpace Y] (P Q : Y)
    (Δ : Description Y P Q), P ≠ Q → IsCompact Δ.M → IsPseudoArc Δ.M := by
  intro h
  obtain ⟨Y, _, P, Q, Δ, hPQ, hc, hnc⟩ := PA51.exists_description_compact_disconnected
  exact hnc (h Y P Q Δ hPQ hc).1.1.2.isPreconnected

/-- **A pseudo-arc in the plane**: the continuum of `Plane.exists_description_plane`. -/
theorem isPseudoArc_plane : ∃ M₀ : Set Pt, IsPseudoArc M₀ := by
  obtain ⟨P, Q, hPQ, ⟨Δ⟩⟩ := exists_description_plane
  obtain ⟨hKc, hK⟩ := Description.links_subset_compact Δ
  exact ⟨Δ.M, isPseudoArc_of_description Δ hPQ _ hK hKc⟩

/-- **The pseudo-arc is unique**: every pseudo-arc is homeomorphic to the plane pseudo-arc. -/
theorem pseudoArc_unique : ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧
    ∀ (Y : Type*) [MetricSpace Y] (M : Set Y), IsPseudoArc M → Nonempty (M ≃ₜ M₀) := by
  obtain ⟨M₀, hM₀⟩ := isPseudoArc_plane
  exact ⟨M₀, hM₀, fun Y _ M hM => theorem1_HIC' hM hM₀⟩

/-- Points of different composants of a pseudo-arc are opposite end points of it (Bing 1951,
*Snake-like continua*, proof of Theorem 16, necessity, citing this paper's Theorem 1). -/
theorem oppositeEndPoints_of_composants {M : Set X} (hM : IsPseudoArc M) {p q : X} (hp : p ∈ M)
    (hq : q ∈ M) (hpq : q ∉ composant M p) : OppositeEndPoints M p q := by
  obtain ⟨Δ, hΔ⟩ := exists_description_of_chainable_HI hM hp hq hpq
  intro ε hε
  obtain ⟨i, hi⟩ := (Δ.ε_tendsto.eventually (gt_mem_nhds hε)).exists
  exact ⟨Δ.n i, Δ.D i, fun t => ⟨Δ.bdd i t, (Δ.diam_le i t).trans_lt hi⟩,
    hΔ ▸ Δ.M_subset_union i, Δ.isFrom i⟩

/-- **Bing 1951 (*Snake-like continua*), Theorem 16, complete**: a nondegenerate snake-like
continuum is a pseudo-arc iff each of its points is an end point. Sufficiency is batch 85's
`exists_not_endPoint_of_not_HI`. -/
theorem isPseudoArc_iff_endPoints {M : Set X} (hM : IsSnakeLike M) (hnd : M.Nontrivial) :
    IsPseudoArc M ↔ ∀ p ∈ M, IsEndPoint M p := by
  constructor
  · intro hPA p hp
    obtain ⟨q, hq, hpq⟩ := exists_not_mem_composant hPA hp
    refine ⟨hp, fun ε hε => ?_⟩
    obtain ⟨n, E, hEε, hcov, hn, hP, -, hPo, -⟩ := oppositeEndPoints_of_composants hPA hp hq hpq ε hε
    exact ⟨n, E, hn, hEε, hcov, hP, fun j hj hpj => hj (congrArg Fin.val (hPo j hpj))⟩
  · intro h
    refine ⟨hM, ?_, hnd⟩
    by_contra hHI
    obtain ⟨p, hp, hne⟩ := exists_not_endPoint_of_not_HI hHI
    exact hne (h p hp)

/-- **Bing 1951 (*Snake-like continua*), Theorem 1**: two nondegenerate snake-like hereditarily
indecomposable continua are homeomorphic. -/
theorem theorem1_snake {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsSnakeLike M) (hMh : IsHereditarilyIndecomposable M) (hnd : M.Nontrivial)
    (hM' : IsSnakeLike M') (hMh' : IsHereditarilyIndecomposable M') (hnd' : M'.Nontrivial) :
    Nonempty (M ≃ₜ M') :=
  theorem1_HIC' ⟨hM, hMh, hnd⟩ ⟨hM', hMh', hnd'⟩

end HPC.Plane
