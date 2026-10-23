import HPC.Hagopian.H75Defs
import HPC.Plane.SorgenfreyLemmas

/-!
# Batch 155, item C: Moore's triod theorem — the statement, and the bridge to `HPC.Plane.IsTriod`

* `MooreTriodStatement`: the plane contains no uncountable family of mutually disjoint triods
  (Moore 1962, Theorem 84, p. 222, in the form Lemma 1 uses). It is proved as `mooreTriodStatement`
  (`H75MooreB.lean`); the supporting lemmas that need it take it as the hypothesis `hmoore`, which
  `Hagopian75.lean` discharges.
* `isTriodSet_image`: an injective inducing map (for instance `Subtype.val`, or `Subtype.val ∘ h` with
  `h` a homeomorphism) carries a triod `IsTriod T` of a compact space to a triod `IsTriodSet` of the
  target. This is the bridge of item C between `IsTriodSet` (in the plane) and `HPC.Plane.IsTriod`
  (in the subtype `M`).
* `not_isTriod_univ_of_indecomposable`: an indecomposable continuum is not a triod (a triod is the
  union of the two proper subcontinua `X₁` and `X₂ ∪ X₃` of a weak triod, Nadler 11.25).
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane

/-- **Moore's triod theorem** (Moore 1962, Theorem 84, p. 222), as a proposition: every family of
mutually disjoint triods in the plane is countable. -/
def MooreTriodStatement : Prop :=
  ∀ (ι : Type) (T : ι → Set Pt), (∀ i, IsTriodSet (T i)) → Pairwise (Function.onFun Disjoint T) →
    Countable ι

variable {S : Type*} [MetricSpace S] [CompactSpace S] {Y : Type*} [MetricSpace Y]

omit [CompactSpace S] in
theorem disjoint_closure_image_of_isInducing {g : S → Y} (hg : IsInducing g) {A B : Set S}
    (h : Disjoint (closure A) B) : Disjoint (closure (g '' A)) (g '' B) := by
  rw [Set.disjoint_left]
  rintro _ hx ⟨b, hb, rfl⟩
  have : b ∈ closure A := by
    rw [hg.closure_eq_preimage_closure_image]; exact hx
  exact Set.disjoint_left.mp h this hb

omit [CompactSpace S] in
/-- **The bridge** from `HPC.Plane.IsTriod` to `IsTriodSet`. -/
theorem isTriodSet_image {g : S → Y} (hg : IsInducing g) (hgi : Function.Injective g) {T : Set S}
    (hT : IsTriod T) : IsTriodSet (g '' T) := by
  obtain ⟨hTc, N, hN, hNT, A, B, C, hA, hB, hC, heq, d1, d2, d3, d4, d5, d6⟩ := hT
  have hcont : ∀ {K : Set S}, Fold.Q78.IsContinuum K → Fold.Q78.IsContinuum (g '' K) :=
    fun hK => ⟨hK.1.image hg.continuous, hK.2.image _ hg.continuous.continuousOn⟩
  refine ⟨hcont hTc, _, hcont hN, image_mono hNT, _, _, _,
    hA.image _, hB.image _, hC.image _, ?_, disjoint_closure_image_of_isInducing hg d1,
    (disjoint_closure_image_of_isInducing hg d2.symm).symm,
    disjoint_closure_image_of_isInducing hg d3,
    (disjoint_closure_image_of_isInducing hg d4.symm).symm,
    disjoint_closure_image_of_isInducing hg d5,
    (disjoint_closure_image_of_isInducing hg d6.symm).symm⟩
  rw [← image_diff hgi, heq, image_union, image_union]

omit [CompactSpace S] in
/-- A triod has two distinct points. -/
theorem IsTriod.nontrivial {T : Set S} (hT : IsTriod T) : T.Nontrivial := by
  obtain ⟨-, N, -, -, A, B, C, ⟨a, ha⟩, ⟨b, hb⟩, -, heq, d1, -⟩ := hT
  have haT : a ∈ T \ N := by rw [heq]; exact Or.inl (Or.inl ha)
  have hbT : b ∈ T \ N := by rw [heq]; exact Or.inl (Or.inr hb)
  refine ⟨a, haT.1, b, hbT.1, fun hab => ?_⟩
  subst hab
  exact d1.le_bot ⟨subset_closure ha, hb⟩

variable [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- An indecomposable continuum is not a triod. -/
theorem not_isTriod_univ_of_indecomposable (hi : ¬ Jones.IsDecomposableSpace S) :
    ¬ IsTriod (univ : Set S) := by
  intro hT
  obtain ⟨X₁, X₂, X₃, ⟨-, h₁, h₂, h₃, hcov, n₁, n₂, n₃⟩, c, ⟨-, hc2⟩, hc3⟩ :=
    isWeakTriod_of_isTriod hT
  have h23 : Fold.Q78.IsContinuum (X₂ ∪ X₃) := isContinuum_union h₂ h₃ ⟨c, hc2, hc3⟩
  refine hi ⟨X₁, X₂ ∪ X₃, h₁, h23, ?_, ?_, ?_⟩
  · intro h; apply n₂; rw [h, univ_union]; exact subset_univ _
  · intro h; apply n₁; rw [h]; exact subset_univ _
  · rw [← union_assoc, ← hcov]

end HPC.Hagopian
