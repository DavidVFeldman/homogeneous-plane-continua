import HPC.Hagopian.H84Quot

/-!
# Batch 184: Hagopian 1976, Theorem 1 by Jones's plan (Hagopian 1984)

Source: C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984), 333–347
(`doc/sources/hagopian1984.pdf`; journal page = PDF page + 331). Route: commission 184 §1;
transcription and dictionary: `doc/notes/hagopian84.md`.

**Setting** (commission 184 §4): a plane continuum `M` (`M : Set Pt`, compact, connected),
homogeneous and indecomposable. Atriodicity and hereditary unicoherence come from
`hagopian75_lemma1`; Lemma 5 (continuity of the decomposition) from `hagopian76_lemma5`.
Hagopian's "continuum of type λ" with "the decomposition" is a minimal admissible pair `(E, k)`
(`IsMinimalAdmissible`); the decomposition is unique (`hagopian75_lemma3_unique`).

Proved here:
* §3: `exists_plane_quotient_of_monotone`, `indecomposable_of_monotone_image`,
  `hagopian76_theorem1_of_jones`, `hagopian75_theorem1_of_noArc`;
* §4: `hagopian84_lemma1` (with `Wset84`), `hagopian84_lemma6`, `hagopian84_lemma11` (with
  `N = M`).

The definitions of §3 of the paper (essential subcontinuum, 5-linked chains, free, normal, runs
straight, regular, ordered refinement, `Ω(𝒫)`, `Δ(𝒫)`) are rendered below. The statements of Lemmas
7, 8, 10, 12–16, of the arc in `M/𝔇` and of Theorem 1 with `N = M` are given at the end of the file,
commented out, each with its `OPEN` note (see `OPEN.md`, batch 184).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §3. The named `Prop`s and the assembly -/

/-- **The arc step** (Bing 1960, the indecomposable case; F. B. Jones, Houston J. Math. 1 (1975)):
no indecomposable homogeneous plane continuum contains an arc. Named `Prop`; its source is decided
later (commission 184 §1, step 5). -/
def NoArcIndecHomPlane : Prop :=
  ∀ (Q : Set Pt) [CompactSpace Q] [ConnectedSpace Q], IsHomogeneous Q →
    ¬ IsDecomposableSpace Q → ∀ α : Set Q, ¬ Nonempty (α ≃ₜ unitInterval)

/-- **Jones's decomposition** (Hagopian 1984, p. 346: "Find a monotone decomposition `𝔇` of `M`
such that `M/𝔇` is a homogeneous plane continuum that contains an arc"), from Theorem 1 (p. 342)
with `N = M`, for a plane `M`. The quotient is given as a map `q`: continuous, onto, with connected
fibres, each fibre a proper subset of `M`; the quotient is homogeneous and contains an arc.
Planarity of the quotient is not asked here: it is proved in the assembly (Moore 1925,
`exists_plane_quotient_of_monotone`).

*Shape:* as in the skeleton, unchanged. The fibres are not required to be nondegenerate (if every
element of `𝔇` is a point, `q` is a homeomorphism and `Y ≅ M`). -/
def Hagopian84Decomp : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
    ¬ IsDecomposableSpace M → ¬ IsHereditarilyIndecomposable (univ : Set M) →
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompactSpace Y) (q : M → Y),
      Continuous q ∧ Function.Surjective q ∧ (∀ y, IsConnected (q ⁻¹' {y})) ∧
        (∀ y, q ⁻¹' {y} ≠ univ) ∧ IsHomogeneous Y ∧ ∃ α : Set Y, Nonempty (α ≃ₜ unitInterval)

section Assembly

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3, the plane quotient** (Moore 1925 Theorem 22, as in `exists_quotient_plane`): for `q` as
in `Hagopian84Decomp`, some compact set in the plane is homeomorphic to `Y`.

*Shape* (skeleton: `True`, shape left open): `M` a homogeneous indecomposable plane continuum;
`q : M → Y` continuous and onto a compact Hausdorff space, with connected fibres, each fibre `≠ M`.
Conclusion: a compact `Q ⊆ R²` with `Y ≃ₜ Q`.

*Proof* (`exists_plane_quotient_of_monotone_aux`, `H84Quot.lean`): the plane is decomposed into the
fibres of `q` and the points off `M` (`fibreSetoid`). The fibres are proper subcontinua of `M`, so
they do not separate the plane (`no_proper_subcontinuum_separates`); upper semicontinuity comes
from compactness (`fibre_usc`). Moore 1925 Theorem 22 (`m25_theorem22`) makes the quotient the plane,
and `Y` maps homeomorphically onto the image of `M`. -/
theorem exists_plane_quotient_of_monotone (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] {q : M → Y} (hq : Continuous q)
    (hqs : Function.Surjective q) (hf : ∀ y, IsConnected (q ⁻¹' {y}))
    (hne : ∀ y, q ⁻¹' {y} ≠ univ) : ∃ Q : Set Pt, IsCompact Q ∧ Nonempty (Y ≃ₜ Q) :=
  exists_plane_quotient_of_monotone_aux hX hi hq hqs hf hne

end Assembly

/-- **§3, monotone images**: a monotone image of an indecomposable continuum is indecomposable.

*Shape* (skeleton: `True`): `X` compact metric, `q : X → Y` continuous onto a metric space, with
connected fibres. Then `X` indecomposable implies `Y` indecomposable.

*Proof* (`isDecomposableSpace_of_monotone_image`): the preimages of two proper subcontinua covering
`Y` are proper subcontinua covering `X`; a preimage of a subcontinuum is a subcontinuum because `q`
is closed with connected fibres (`isPreconnected_preimage_of_monotone`). -/
theorem indecomposable_of_monotone_image {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {q : X → Y} (hq : Continuous q) (hqs : Function.Surjective q)
    (hf : ∀ y, IsConnected (q ⁻¹' {y})) (hX : ¬ IsDecomposableSpace X) :
    ¬ IsDecomposableSpace Y :=
  fun hY => hX (isDecomposableSpace_of_monotone_image hq hqs hf hY)

/-- **§3, the assembly** (Hagopian 1984, p. 346, Corollary 3 by Jones's plan): Theorem 1 of 1976
from Jones's decomposition and the arc step.

*Proof.* Suppose `M` has a decomposable subcontinuum, and take `q : M → Y` from `hD`. By
`exists_plane_quotient_of_monotone`, `Y` is homeomorphic to a compact plane set `Q`. `Q` is connected
(an image of `M`), homogeneous (as `Y` is), indecomposable (`indecomposable_of_monotone_image`, then
transport by the homeomorphism), and contains an arc (the image of the arc of `Y`). This contradicts
`hA`.

*Non-vacuity* (report §3): both hypotheses are used in a proof by contradiction about an `M` that
Theorem 1 says does not exist; `hA` is Bing's published theorem; `hD` alone does not give the
conclusion. -/
theorem hagopian76_theorem1_of_jones (hD : Hagopian84Decomp) (hA : NoArcIndecHomPlane) :
    Hagopian76Thm1 := by
  intro M _ _ hX hi
  by_contra hH
  obtain ⟨Y, _, _, q, hqc, hqs, hqf, hqne, hYh, α, ⟨hα⟩⟩ := hD M hX hi hH
  obtain ⟨Q, hQc, ⟨e⟩⟩ := exists_plane_quotient_of_monotone hX hi hqc hqs hqf hqne
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hQc
  haveI : ConnectedSpace Y := hqs.connectedSpace hqc
  haveI : ConnectedSpace Q := e.surjective.connectedSpace e.continuous
  have hQi : ¬ IsDecomposableSpace Q := fun hd =>
    indecomposable_of_monotone_image hqc hqs hqf hi (hd.of_homeomorph e.symm)
  exact hA Q (hYh.of_homeomorph e) hQi (e '' α) ⟨(e.image α).symm.trans hα⟩

section Theorem1Of75

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3, Hagopian 1975 Theorem 1, paragraph 4 supplied** ("for otherwise, `E` would contain an arc
… and `M` would be a simple closed curve"): `hagopian75_theorem1_of_layer` without `hnd`, from
`NoArcIndecHomPlane` and `exists_arc_of_degenerate_layers`.

*Shape* (skeleton: `True`): the statement of `hagopian75_theorem1_of_layer` with the hypothesis
`hnd` replaced by `hA : NoArcIndecHomPlane`.

*Proof.* If some interior layer is nondegenerate, `hagopian75_theorem1_of_layer`. Otherwise every
interior layer is degenerate and `E` contains an arc (`exists_arc_of_degenerate_layers`), so `M`
contains an arc, against `hA` applied to `M` itself.

*Non-vacuity:* `hA` is used inside a proof by contradiction (the case where every interior layer
is degenerate is shown not to occur); it is not equivalent to the conclusion. -/
theorem hagopian75_theorem1_of_noArc (hA : NoArcIndecHomPlane) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) :
    ∃ Y ⊆ E, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y := by
  by_cases hnd : ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ (layer k s).Nontrivial
  · exact hagopian75_theorem1_of_layer hX hi hE hk hk0 hnd
  · have hdeg : ∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton := fun s h0 h1 =>
      Set.not_nontrivial_iff.1 fun h => hnd ⟨s, h0, h1, h⟩
    obtain ⟨a, b, hab⟩ := hE
    obtain ⟨A, -, hA'⟩ := exists_arc_of_degenerate_layers hab.1.1 hk hdeg
    exact absurd hA' (hA M hX hi A)

end Theorem1Of75

/-! ## §4. The definitions of §3 of the paper and Lemma 6 -/

section Defs84

variable {M : Set Pt}

/-- **Essential subcontinuum** (Hagopian 1984, p. 336): "A continuum `H` in `E` is an *essential
subcontinuum* of `E` if `H` intersects more than one element of the decomposition of `E`." Not the
1976 `IsEssential` (essential to `R(E)`). -/
def IsEssential84 {E : Set M} (k : E → unitInterval) (H : Set M) : Prop :=
  H ⊆ E ∧ Fold.Q78.IsContinuum H ∧
    ∃ t₁ t₂, t₁ ≠ t₂ ∧ (H ∩ layer k t₁).Nonempty ∧ (H ∩ layer k t₂).Nonempty

/-- A **5-linked chain** in `M` (p. 338; the chain of p. 334): open sets `L₀, …, L₄` of `M` (the
paper's `L₁, …, L₅`) with `Lᵢ ∩ Lⱼ ≠ ∅` if and only if `|i − j| ≤ 1`. -/
structure IsChain5 (L : Fin 5 → Set M) : Prop where
  isOpen : ∀ i, IsOpen (L i)
  inter_iff : ∀ i j : Fin 5, (L i ∩ L j).Nonempty ↔ (i : ℕ) ≤ j + 1 ∧ (j : ℕ) ≤ i + 1

/-- `⋃𝔏′`, the union of the 3-linked subchain `{Lᵢ : 2 ≤ i ≤ 4}` (p. 338; here `L₁ ∪ L₂ ∪ L₃`). -/
def midUnion (L : Fin 5 → Set M) : Set M := L 1 ∪ L 2 ∪ L 3

/-- **Free** (p. 338): "`Bd(L₁ ∪ L₅)∖Cl ⋃𝔏′` contains `Bd ⋃𝔏`" (boundary and closure in `M`). -/
def IsFree5 (L : Fin 5 → Set M) : Prop :=
  frontier (⋃ i, L i) ⊆ frontier (L 0 ∪ L 4) \ closure (midUnion L)

/-- **Normal** (p. 338): "`Cl Lᵢ ∩ Cl Lⱼ = ∅` whenever `|i − j| > 1`". -/
def IsNormal5 (L : Fin 5 → Set M) : Prop :=
  ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (closure (L i)) (closure (L j))

/-- **Runs straight through** (pp. 338–339), conditions (1)–(5). -/
def RunsStraight {E : Set M} (k : E → unitInterval) (L : Fin 5 → Set M) : Prop :=
  E ⊆ ⋃ i, L i ∧ layer k 0 ⊆ L 0 \ L 1 ∧ layer k 1 ⊆ L 4 \ L 3 ∧
    (∀ r i, (layer k r ∩ frontier (L i)).Nonempty → layer k r ⊆ frontier (L i)) ∧
    ∀ r t i, r < t → layer k r ∪ layer k t ⊆ L i → layerSet k (Icc r t) ⊆ L i

/-- **Regular** (p. 339): "for each component `K` of `⋃𝔏′`, the set `Cl K` is a continuum of type λ
that runs straight through `𝔏`". The components are `connectedComponentIn (midUnion L) x`. -/
def IsRegular5 (L : Fin 5 → Set M) : Prop :=
  ∀ x ∈ midUnion L, ∃ d : closure (connectedComponentIn (midUnion L) x) → unitInterval,
    IsMinimalAdmissible (closure (connectedComponentIn (midUnion L) x)) d ∧ RunsStraight d L

/-- **Ordered refinement** (p. 339): "for each `i`, the link `Lᵢ` contains `Pᵢ`" (and `𝒫` is a
chain). -/
def IsOrderedRefinement5 (P L : Fin 5 → Set M) : Prop :=
  IsChain5 P ∧ ∀ i, P i ⊆ L i

/-- **`Ω(𝒫)`** (p. 341): the elements of the decompositions of the closures of the components of
`⋃𝒫′`. -/
def Omega5 (P : Fin 5 → Set M) : Set (Set M) :=
  {Z | ∃ x ∈ midUnion P, ∃ d : closure (connectedComponentIn (midUnion P) x) → unitInterval,
    IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) d ∧ ∃ t, Z = layer d t}

/-- **`Δ(𝒫)`** (p. 341): the elements of `Ω(𝒫)` that miss `Cl(P₁ ∪ P₅)`. -/
def Delta5 (P : Fin 5 → Set M) : Set (Set M) :=
  {Z | Z ∈ Omega5 P ∧ Disjoint Z (closure (P 0 ∪ P 4))}

end Defs84

section Lemma1

/-- **`W(x, ε)`** (p. 335): "`{y ∈ M: an ε-homeomorphism of M onto M takes x to y}`", where an
ε-homeomorphism moves no point `ε` or more. -/
def Wset84 {X : Type*} [MetricSpace X] (x : X) (ε : ℝ) : Set X :=
  {y | ∃ h : X ≃ₜ X, (∀ v, dist v (h v) < ε) ∧ h x = y}

/-- **Lemma 1** (p. 335): "For every positive number `ε` and every point `x` of `M`, the set
`W(x, ε)` is open in `M`." Stated for any compact homogeneous metric space; `ε > 0` is not needed
(for `ε ≤ 0` the set is empty).

*Proof* ("a short argument [10, Lemma 4, proof] involving E. G. Effros' … theorem"): if `h` is an
ε-homeomorphism with `h(x) = y`, its largest displacement is `ε − η` with `η > 0` (compactness);
Effros (`effros_homogeneous`) gives `δ` such that each `z` within `δ` of `y` is `g(y)` for some
`g` moving points less than `η`; then `g ∘ h` is an ε-homeomorphism taking `x` to `z`. -/
theorem hagopian84_lemma1 {X : Type*} [MetricSpace X] [CompactSpace X] (hX : IsHomogeneous X)
    (x : X) (ε : ℝ) : IsOpen (Wset84 x ε) := by
  rw [Metric.isOpen_iff]
  rintro y ⟨h, hh, rfl⟩
  haveI : Nonempty X := ⟨x⟩
  obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (f := fun v => dist v (h v)) (continuous_id.dist h.continuous).continuousOn
  set η := ε - dist v₀ (h v₀) with hηdef
  have hη : 0 < η := sub_pos.2 (hh v₀)
  obtain ⟨δ, hδ, hg⟩ := HPC.Effros.effros_homogeneous hX hη
  refine ⟨δ, hδ, fun z hz => ?_⟩
  rw [mem_ball] at hz
  obtain ⟨g, hgz, hgm⟩ := hg (h x) z (by rw [dist_comm]; exact hz)
  refine ⟨h.trans g, fun v => ?_, by simp [hgz]⟩
  have h1 : dist v (h v) ≤ dist v₀ (h v₀) := hv₀ (mem_univ v)
  have h2 : dist (g (h v)) (h v) < η := hgm (h v)
  have h3 : dist v (g (h v)) ≤ dist v (h v) + dist (h v) (g (h v)) := dist_triangle _ _ _
  rw [dist_comm (h v)] at h3
  simp only [Homeomorph.trans_apply]
  linarith

end Lemma1

section Lemma6

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 6** (p. 336): "If `H` is an essential subcontinuum of `E`, then `H` is a continuum of
type λ and every element of the decomposition of `H` is an element of the decomposition of `E`."

*Shape* (skeleton: `True`): `M` a homogeneous indecomposable plane continuum, `(E, k)` minimal
admissible, `H` essential in `E` (`IsEssential84`). Conclusion: `H = k⁻¹[[a, b]]` for some `a < b`,
`H` is of type A′, and for every minimal admissible map `e` of `H` each layer of `e` is a layer of
`k` (the decomposition of `H` is unique, `hagopian75_lemma3_unique`, so this is "every element of
the decomposition of `H`").

*Proof.* Lemma 5 (`lsc_of_minimalAdmissible`) and `isTypeA'_of_subcontinuum` give
`H = k⁻¹[[a, b]]`; `minimalAdmissible_restrict` gives a minimal admissible map `e₀` of `H` whose
layers are layers of `k`; any other `e` has the same layers as `e₀` (uniqueness). This replaces
Thomas's Theorem 8 [26] (the "irreducibility properties of `E`"). -/
theorem hagopian84_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M} (hH : IsEssential84 k H) :
    (∃ a b : unitInterval, a < b ∧ H = layerSet k (Icc a b)) ∧ IsTypeA' H ∧
      ∀ e : H → unitInterval, IsMinimalAdmissible H e → ∀ t, ∃ s, layer e t = layer k s := by
  obtain ⟨hHE, hHc, t₁, t₂, ht, h₁, h₂⟩ := hH
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  obtain ⟨a, b, hab, hHeq, hTA⟩ :=
    isTypeA'_of_subcontinuum hE (lsc_of_minimalAdmissible hX hi hE) hHE hHc ht h₁ h₂
  refine ⟨⟨a, b, hab, hHeq⟩, hTA, ?_⟩
  subst hHeq
  obtain ⟨e₀, he₀, hlay⟩ := minimalAdmissible_restrict hX hi hE hab
  intro e he t
  obtain ⟨x, hx⟩ := he.2.1.2.1 t
  have huniq := hagopian75_lemma3_unique he.1 he.2.1 he.2.2 he₀.2.1 he₀.2.2
  refine ⟨restrictParam a b hab.le (e₀ x), ?_⟩
  rw [← hlay]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (huniq w x).1 (by rw [mem_preimage, mem_singleton_iff] at hw; rw [hw, hx]), rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    rw [mem_preimage, mem_singleton_iff] at hw ⊢
    rw [← hx]; exact (huniq w x).2 hw


/-- **Lemma 11 with `N = M`** (p. 338): "If `N` is an indecomposable subcontinuum of `M` that
contains `E`, then `Cl ⋃𝔖(k⁻¹(0), E)` is an indecomposable subcontinuum of `N`." With `N = M` the
first half is automatic, and the second is the 1976 argument ("paragraphs 2 through 11 in the proof
of Lemma 6 of [11]"), proved as `hagopian76_lemma6_X`. The general `N` needs Lemma 10 (open). -/
theorem hagopian84_lemma11 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (extUnion E (layer k 0))) :=
  hagopian76_lemma6_X hX hi hE

end Lemma6

/-! ## §4–§5. Open items (statements; see `OPEN.md`, batch 184)

The setting of each is `M : Set Pt` compact connected, `hX : IsHomogeneous M`,
`hi : ¬ IsDecomposableSpace M`, `(E, k)` minimal admissible. -/

-- `hagopian84_lemma7`: proved in batch 185, `Hagopian76AC.lean` (`H84Lemma7.lean`).

/- OPEN (batch 184): `hagopian84_lemma8` (p. 337). Obstruction: Lemma 7; then the gluing of the
two decompositions into a monotone continuous decomposition of `E ∪ F` whose quotient is "the union
of two arcs", and the step from atriodic, no simple closed curve, to an arc (unargued; ledger H84.5).
theorem hagopian84_lemma8 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hFE : (F ∩ E).Nonempty)
    (hmiss : Disjoint F (layer k 0) ∨ Disjoint F (layer k 1)) : F ⊆ Rset k := by
  sorry
-/

/- OPEN (batch 184): `hagopian84_lemma10` (p. 338), not needed with `N = M` (then it is trivial).
Obstruction: the triod `N ∪ F ∪ f[F] ∪ g[F]` needs `F`, `f[F]`, `g[F]` disjoint ("By Lemma 2") and
the composant argument; not attempted.
theorem hagopian84_lemma10 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E N : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (hN : Fold.Q78.IsIndecomposable N)
    (hEN : E ⊆ N) : extUnion E (layer k 0) ⊆ N := by
  sorry
-/

-- `hagopian84_lemma12`: proved in batch 186, `Hagopian84B.lean` (`H84Lemma12.lean`).

-- `hagopian84_lemma13`: proved in batch 187, `Hagopian84C.lean` (`H84Lemma13.lean`).

-- `hagopian84_lemma14`: proved in batch 186, `Hagopian84B.lean` (`H84Lemma1415.lean`).

-- `hagopian84_lemma15`: proved in batch 186, `Hagopian84B.lean` (`H84Lemma1415.lean`).

-- `hagopian84_lemma16`: proved in batch 187, `Hagopian84C.lean` (`H84Strand.lean`).

-- `hagopian84_quotient_arc`: proved in batch 188 as the `arc` field of `CoverData84.isJonesDecomp`
-- (`Hagopian84D.lean`), carried to the quotient by `hagopian84Decomp_of_package`.

-- `hagopian84_decomp`: proved in batch 188, `Hagopian84D.lean`.

-- `hagopian76_theorem1_jones`: proved in batch 188, `Hagopian84D.lean`.

end HPC.Hagopian
