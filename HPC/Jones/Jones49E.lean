import HPC.Jones.Jones49EAcc
import HPC.Jones.Jones49EPlane

/-!
# Batch 153: Whyburn 1939, §14 Corollary 1 — boundaries of complementary domains of a
compact semi-locally-connected cyclic plane continuum are simple closed curves

From the batch-153 skeleton (`doc/batches/skeletons/Jones49E-batch153.lean`). All six items are
proved; the proofs are in `Jones49EArc.lean` (items A, B), `Jones49EAcc.lean` (item C),
`Jones49EPlane.lean` (item D and the θ-curve lemma of item F) and `Jones49ETheta.lean` (item E).
Statements A–D and F are verbatim; the shape of E was left open and is recorded at the statement.

Source: Whyburn, *Semi-locally-connected sets*, Amer. J. Math. 61 (1939), p. 749: "COROLLARY 1. If
`M` is a compact plane semi-locally-connected cyclic continuum, the boundary of every complementary
domain of `M` is a simple closed curve." (Stated without proof; footnote 16 refers to Wilder 1938,
Theorem 8a, first corollary.) Route: REPORT-batch150 §5 (d) and REPORT-batch152 §8. *Cyclic*: no cut
points.

Jones 1949 (p. 113) uses it as "Hence each element of `G` is a simple domain [6, 7]. Let the simple
closed curve `J` denote the boundary of an element `D` of `G`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane HPC.Moore.Gen

/-- A simple polygonal arc is a topological arc (bridge from `IsSimplePolyArc` to `TArc`). -/
theorem tarc_of_isSimplePolyArc {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) :
    TArc p q α :=
  tarc_of_isSimplePolyArc' h

/-- **The arc theorem for Peano continua** (Moore–Mazurkiewicz; e.g. Whyburn, *Analytic Topology*,
Ch. II; Nadler 8.23): two distinct points of a locally connected compact connected metric space are
joined by an arc.

*Route (batch 153):* neither `exists_tarc_of_seq` nor a new chain construction. Moore's own
nested-chain proof of F.A. Theorem 15 is already formalized for any metric space with a family of
"regions" that are connected open sets with compact closures, small ones inside any neighbourhood
(`HPC.Moore.exists_irreducible`, batch 137). Taking the regions to be all connected open sets of `X`
gives a compact connected set irreducible between `a` and `b`, an arc by
`isIrreducibleConnected_iff_arc`. The general form, for a connected open subset of a compact locally
connected metric space, is `exists_tarc_in_open`; item E uses it in `X − c`. -/
theorem exists_tarc_of_locallyConnected {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyConnectedSpace X] {a b : X} (hab : a ≠ b) :
    ∃ C : Set X, TArc a b C :=
  exists_tarc_of_locallyConnected' hab

/-- **Accessibility.** For `M` compact, connected, semi-locally connected and cyclic, every boundary
point `p` of a complementary domain `R` is the end of an arc from any point of `R` lying, except
for `p`, in `R`. Proof (`accessible_of_cyclic'`): the route of REPORT-batch152 §8 —
`local_join_of_noncut` at `p`, polygonal arcs (item A) in shrinking balls, radii
`ρₙ₊₂ ≤ min (ρₙ₊₁ / 2) (dist (p, βₙ))`, Moore's limit arc `exists_tarc_of_seq`, and `TArc.join`. -/
theorem accessible_of_cyclic {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) {p : Pt} (hp : p ∈ frontier (connectedComponentIn Mᶜ x)) {y : Pt}
    (hy : y ∈ connectedComponentIn Mᶜ x) (hyp : y ≠ p) :
    ∃ C : Set Pt, TArc y p C ∧ C \ {p} ⊆ connectedComponentIn Mᶜ x :=
  accessible_of_cyclic' hM hMc hS hcyc hx hp hy hyp

/-- **The boundary is cyclic.** Every cut point of `B = ∂R` is a cut point of `M`; `M` is cyclic.

*Route changed (batch 153):* not the two-sided Jordan-curve construction of the commission, but
Janiszewski's theorem (`frontier_cyclic'`). If `B − z = U ∪ V` is a separation, `P = U + z` and
`Q = V + z` are compact with `P · Q = z` connected, so the components `R_P`, `R_Q` of `Pᶜ`, `Qᶜ`
containing `R` meet only in `R` (Janiszewski); `V ⊆ R_P`, `U ⊆ R_Q`, and `M · R_Q` is open and
closed in `M − z`, containing `U` and missing `V`. Accessibility, the Jordan curve theorem and
`tscc_homeomorph_circle` are not needed. The hypotheses `hMc` and `hS` are kept as in the skeleton
but are not used (only compactness and cyclicity of `M` are). -/
theorem frontier_cyclic {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) :
    ∀ z : frontier (connectedComponentIn Mᶜ x),
      IsConnected ({z}ᶜ : Set (frontier (connectedComponentIn Mᶜ x))) :=
  frontier_cyclic' hM hcyc hx

/-- **A θ-curve in a cyclic Peano continuum that is not a circle.** *Shape chosen (batch 153):* a
compact, locally connected, connected metric space with no cut points which is not itself a simple
closed curve (`¬ TSCC univ`, two arcs with only their ends in common) contains three arcs with
common ends `a ≠ b`, any two of which have only `a` and `b` in common. The θ route was taken
rather than the plane route (every point of `B` of order 2, then `menger_order_two`): with the arc
theorem (item B, for connected open sets) the θ-curve is three first-point trims
(`exists_scc_of_cyclic`, `exists_theta_of_cyclic`), whereas the plane route needs a finite order at
every point of `B`, which nothing available supplies. Connectedness of `X` is needed: a two-point
discrete space has no cut points in this sense. -/
theorem theta_of_cyclic_peano {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] (hcyc : ∀ z : X, IsConnected ({z}ᶜ : Set X))
    (hnot : ¬ TSCC (univ : Set X)) :
    ∃ (a b : X) (K₁ K₂ K₃ : Set X), TArc a b K₁ ∧ TArc a b K₂ ∧ TArc a b K₃ ∧
      K₁ ∩ K₂ = {a, b} ∧ K₁ ∩ K₃ = {a, b} ∧ K₂ ∩ K₃ = {a, b} :=
  exists_theta_of_cyclic hcyc hnot

/-- An arc in a subspace is an arc in the whole space. -/
theorem _root_.HPC.Moore.Gen.TArc.subtype_val {X : Type*} [TopologicalSpace X] {S : Set X}
    {a b : S} {C : Set S} (h : TArc a b C) : TArc (a : X) (b : X) (Subtype.val '' C) := by
  obtain ⟨hab, f, hf, rfl, rfl, rfl⟩ := h
  exact ⟨fun e => hab (Subtype.ext e), Subtype.val ∘ f, IsEmbedding.subtypeVal.comp hf,
    range_comp _ _, rfl, rfl⟩

theorem image_val_inter_pair {X : Type*} {S : Set X} {a b : S} {K L : Set S}
    (h : K ∩ L = {a, b}) : Subtype.val '' K ∩ Subtype.val '' L = {(a : X), (b : X)} := by
  rw [← image_inter Subtype.val_injective, h, image_pair]

/-- **Whyburn 1939, Corollary 1.** `B = ∂R` is a locally connected continuum
(`whyburn39_theorem14`, `isConnected_frontier_complDomain`) without cut points (item D). If it is
not a simple closed curve it contains a θ-curve (item E, applied in the subspace `B`); all three
arcs lie in `B ⊆ R̄` while `R` is connected and misses them, against the θ-curve lemma
`theta_not_subset_closure` (Jordan curve theorem three times and Janiszewski's theorem). So `B` is
a simple closed curve, homeomorphic to `Circle` by `tscc_homeomorph_circle`. -/
theorem whyburn39_corollary1 {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) : Nonempty (frontier (connectedComponentIn Mᶜ x) ≃ₜ Circle) := by
  set R := connectedComponentIn Mᶜ x with hRdef
  set B := frontier R with hBdef
  by_cases hT : TSCC B
  · exact tscc_homeomorph_circle hT
  exfalso
  have hBM : B ⊆ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hM.isClosed x
  have hBc : IsCompact B := hM.of_isClosed_subset isClosed_frontier hBM
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 hBc
  haveI : ConnectedSpace B :=
    isConnected_iff_connectedSpace.1 (isConnected_frontier_complDomain hM hMc hx)
  haveI : LocallyConnectedSpace B := whyburn39_theorem14 hM hMc hS hx
  have hnot : ¬ TSCC (univ : Set B) := by
    rintro ⟨a, b, C₁, C₂, h₁, h₂, h12, hU⟩
    refine hT ⟨a, b, _, _, h₁.subtype_val, h₂.subtype_val, image_val_inter_pair h12, ?_⟩
    rw [← image_union, ← hU, image_univ, Subtype.range_coe]
  obtain ⟨a, b, K₁, K₂, K₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    theta_of_cyclic_peano (frontier_cyclic hM hMc hS hcyc hx) hnot
  have hRo : IsOpen R := hM.isClosed.isOpen_compl.connectedComponentIn
  have hθB : Subtype.val '' K₁ ∪ Subtype.val '' K₂ ∪ Subtype.val '' K₃ ⊆ B :=
    union_subset (union_subset (Subtype.coe_image_subset _ _) (Subtype.coe_image_subset _ _))
      (Subtype.coe_image_subset _ _)
  refine theta_not_subset_closure h₁.subtype_val h₂.subtype_val h₃.subtype_val
    (image_val_inter_pair h12) (image_val_inter_pair h13) (image_val_inter_pair h23)
    (D := R) isPreconnected_connectedComponentIn ?_ (hθB.trans frontier_subset_closure)
  refine disjoint_left.mpr fun y hyR hyθ => ?_
  have : y ∈ R ∩ frontier R := ⟨hyR, hθB hyθ⟩
  rw [hRo.inter_frontier_eq] at this
  exact this

end HPC.Jones
