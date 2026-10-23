import HPC.Plane.Snake51

/-!
# Batch 88: a description whose continuum is compact but not connected

Counterexample to the skeleton's `theorem12_of` and `isPseudoArc_of_description` as stated
(COMMISSION-batch88.md; `PseudoArc51.lean`). Take the plane description `Δ₀` from `P` to `Q`
(batch 84) and remove from the plane every point of its continuum `M₀` except `P` and `Q`. Since
`M₀` is hereditarily indecomposable it contains no square, so it has empty interior, and every
nonempty open set of the plane still meets the remaining space `Y`. The links of `Δ₀`, cut down to
`Y`, still form a description, now of `M₀ ∩ Y = {P, Q}`: compact, with `P ≠ Q`, but not connected
(and so not homeomorphic to `M₀`, and not a pseudo-arc).

The point: `Description` allows a non-complete ambient space, and compactness of the described
set does not make up for it; the repository's Theorems 12 and 13 assume a compact ambient space,
or (`Transfer.lean`) links inside a compact set.
-/

namespace HPC.Plane

open Set Metric

namespace PA51

/-- A hereditarily indecomposable subset of the plane has empty interior: it contains no square,
a square being the union of two proper sub-rectangles. -/
theorem interior_eq_empty_of_HI {M : Set Pt}
    (hHI : ∀ K : Set Pt, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K) :
    interior M = ∅ := by
  by_contra hne
  obtain ⟨⟨a, b⟩, hx⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hx
  have hball' : ball (a, b) r ⊆ M := hball.trans interior_subset
  set I := Icc (b - r / 2) (b + r / 2)
  set S := Icc (a - r / 2) (a + r / 2) ×ˢ I
  set A := Icc (a - r / 2) a ×ˢ I
  set B := Icc a (a + r / 2) ×ˢ I
  have hSM : S ⊆ M := by
    rintro ⟨u, v⟩ ⟨⟨h1, h2⟩, h3, h4⟩
    apply hball'
    rw [← ball_prod_same]
    refine ⟨?_, ?_⟩ <;> rw [Real.ball_eq_Ioo] <;> constructor <;> linarith
  have hIc : IsConnected I := isConnected_Icc (by linarith)
  have hcont : ∀ c d : ℝ, c ≤ d → Fold.Q78.IsContinuum (Icc c d ×ˢ I) := fun c d hcd =>
    ⟨isCompact_Icc.prod isCompact_Icc, (isConnected_Icc hcd).prod hIc⟩
  have hAB : A ∪ B = S := by
    simp only [A, B, S, ← union_prod]
    rw [Icc_union_Icc_eq_Icc (by linarith) (by linarith)]
  have hbI : b ∈ I := ⟨by linarith, by linarith⟩
  rcases (hHI S hSM (hcont _ _ (by linarith))).2 A B (hcont _ _ (by linarith))
    (hcont _ _ (by linarith)) (hAB ▸ subset_union_left) (hAB ▸ subset_union_right) hAB with h | h
  · have : (a + r / 2, b) ∈ A := h ▸ (⟨⟨by linarith, by linarith⟩, hbI⟩ : (a + r / 2, b) ∈ S)
    have := this.1.2
    linarith
  · have : (a - r / 2, b) ∈ B := h ▸ (⟨⟨by linarith, by linarith⟩, hbI⟩ : (a - r / 2, b) ∈ S)
    have := this.1.1
    linarith

variable {X : Type*} [MetricSpace X]

/-- The restriction of a chain to a subspace meeting every nonempty open set. -/
def denseChain {n : ℕ} (D : Chain X n) (Y : Set X)
    (hY : ∀ U : Set X, IsOpen U → U.Nonempty → (U ∩ Y).Nonempty) : Chain Y n where
  link j := Subtype.val ⁻¹' D.link j
  isOpen j := (D.isOpen j).preimage continuous_subtype_val
  adjacent i j := by
    rw [← D.adjacent]
    constructor
    · rintro ⟨z, h1, h2⟩; exact ⟨z.1, h1, h2⟩
    · intro h
      obtain ⟨z, ⟨h1, h2⟩, hz⟩ := hY _ ((D.isOpen i).inter (D.isOpen j)) h
      exact ⟨⟨z, hz⟩, h1, h2⟩

/-- The restriction of a description to a subspace containing `P`, `Q` and meeting every
nonempty open set. -/
noncomputable def denseDescription {P Q : X} (Δ : Description X P Q) (Y : Set X)
    (hY : ∀ U : Set X, IsOpen U → U.Nonempty → (U ∩ Y).Nonempty) (hP : P ∈ Y) (hQ : Q ∈ Y) :
    Description Y ⟨P, hP⟩ ⟨Q, hQ⟩ where
  n := Δ.n
  D i := denseChain (Δ.D i) Y hY
  isFrom i := by
    obtain ⟨hn, hP', hQ', hPo, hQo⟩ := Δ.isFrom i
    exact ⟨hn, hP', hQ', fun j hj => hPo j hj, fun j hj => hQo j hj⟩
  crooked i := by
    obtain ⟨href, hcr⟩ := Δ.crooked i
    refine ⟨fun t => ?_, fun h k hk a b ha hb => ?_⟩
    · obtain ⟨s, hs⟩ := href t
      exact ⟨s, preimage_mono hs⟩
    · have ha' : ((Δ.D (i + 1)).link a ∩ (Δ.D i).link h).Nonempty := by
        obtain ⟨z, h1, h2⟩ := ha; exact ⟨z.1, h1, h2⟩
      have hb' : ((Δ.D (i + 1)).link b ∩ (Δ.D i).link k).Nonempty := by
        obtain ⟨z, h1, h2⟩ := hb; exact ⟨z.1, h1, h2⟩
      obtain ⟨r, s, hb2, hr, hs⟩ := hcr h k hk a b ha' hb'
      exact ⟨r, s, hb2, preimage_mono hr, preimage_mono hs⟩
  closure_subset i t := by
    obtain ⟨s, hs⟩ := Δ.closure_subset i t
    exact ⟨s, (continuous_subtype_val.closure_preimage_subset _).trans (preimage_mono hs)⟩
  ε := Δ.ε
  ε_pos := Δ.ε_pos
  ε_tendsto := Δ.ε_tendsto
  bdd i t := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (Δ.bdd i t)
    exact Metric.isBounded_iff.mpr ⟨C, fun a ha b hb => hC ha hb⟩
  diam_le i t := by
    refine le_trans ?_ (Δ.diam_le i t)
    rw [← isometry_subtype_coe.diam_image]
    exact diam_mono (image_preimage_subset _ _) (Δ.bdd i t)

theorem denseDescription_M {P Q : X} (Δ : Description X P Q) (Y : Set X)
    (hY : ∀ U : Set X, IsOpen U → U.Nonempty → (U ∩ Y).Nonempty) (hP : P ∈ Y) (hQ : Q ∈ Y) :
    (denseDescription Δ Y hY hP hQ).M = Subtype.val ⁻¹' Δ.M := by
  ext z
  simp [Description.M, Chain.union, denseDescription, denseChain]

/-- **A description with compact, disconnected continuum.** -/
theorem exists_description_compact_disconnected :
    ∃ (Y : Type) (_ : MetricSpace Y) (P Q : Y) (Δ : Description Y P Q),
      P ≠ Q ∧ IsCompact Δ.M ∧ ¬ IsPreconnected Δ.M := by
  obtain ⟨P, Q, hPQ, ⟨Δ₀⟩⟩ := exists_description_plane
  set M₀ := Δ₀.M
  have hint : interior M₀ = ∅ := interior_eq_empty_of_HI (Description.theorem10 Δ₀)
  set Y : Set Pt := {x | x ∉ M₀ ∨ x = P ∨ x = Q}
  have hY : ∀ U : Set Pt, IsOpen U → U.Nonempty → (U ∩ Y).Nonempty := by
    intro U hU hne
    by_contra hcon
    have hsub : U ⊆ M₀ := by
      intro x hx
      by_contra hxM
      exact hcon ⟨x, hx, Or.inl hxM⟩
    have : U ⊆ interior M₀ := interior_maximal hsub hU
    rw [hint] at this
    obtain ⟨x, hx⟩ := hne
    exact this hx
  have hP : P ∈ Y := Or.inr (Or.inl rfl)
  have hQ : Q ∈ Y := Or.inr (Or.inr rfl)
  set Δ := denseDescription Δ₀ Y hY hP hQ
  have hM : Δ.M ⊆ {⟨P, hP⟩, ⟨Q, hQ⟩} := by
    intro z hz
    rw [denseDescription_M] at hz
    rcases z.2 with h | h | h
    · exact absurd hz h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hfin : Δ.M.Finite := (Set.toFinite _).subset hM
  have hPQ' : (⟨P, hP⟩ : Y) ≠ ⟨Q, hQ⟩ := fun h => hPQ (congrArg Subtype.val h)
  refine ⟨Y, inferInstance, ⟨P, hP⟩, ⟨Q, hQ⟩, Δ, hPQ', hfin.isCompact, fun hconn => ?_⟩
  haveI : Finite Δ.M := hfin.to_subtype
  have hsub := (isPreconnected_iff_preconnectedSpace.mp hconn).isPreconnected_univ.subsingleton
  exact hPQ' (congrArg Subtype.val (hsub (mem_univ ⟨_, Δ.P_mem_M⟩) (mem_univ ⟨_, Δ.Q_mem_M⟩)))

end PA51

end HPC.Plane
