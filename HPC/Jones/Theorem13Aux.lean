import HPC.Jones.Theorem6

/-!
# Batch 135: Jones 1948, Theorem 13 — general lemmas

Three facts used in Jones's proof of Theorem 13, in general form:

* `exists_mem_dist_eq` — a closed set `W`, open away from a ball about `A`, which reaches distance
  `≥ a` from `A`, meets the sphere of radius `a` (connectedness);
* `exists_split_of_not_aposAt` — Jones's \"`M − V₁` is the sum of two mutually exclusive closed
  sets `Q₁` and `W₁` each of which contains a point of `M − U(A, ε)`\": if `X` is not aposyndetic
  at `q` with respect to `x ∈ V`, the closed set `X − V` cannot have all of a neighbourhood `P` of
  `q` in one component (that component would be a continuum containing a neighbourhood of `q` and
  missing `x`);
* `separation_nested` — Jones's \"consequently `Q₂` contains `Q₁` and `W₁` contains `W₂`\".
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

omit [CompactSpace X] in
/-- **The sphere lemma.** Let `W` be closed with `W ∩ {ρ < d(·, A)}` open, and `w₀ ∈ W` with
`a ≤ d(w₀, A)`, where `0 ≤ ρ < a`. Then `W` has a point at distance exactly `a` from `A`. -/
theorem exists_mem_dist_eq {W : Set X} (hW : IsClosed W) {A : X} {ρ a : ℝ}
    (hWo : IsOpen (W ∩ {p | ρ < dist p A})) (hρ : 0 ≤ ρ) (hρa : ρ < a) {w₀ : X} (hw₀ : w₀ ∈ W)
    (haw : a ≤ dist w₀ A) : ∃ w ∈ W, dist w A = a := by
  by_contra hcon
  push_neg at hcon
  set S := W ∩ {p | a ≤ dist p A} with hS
  have hScl : IsClosed S := hW.inter (isClosed_le continuous_const (continuous_id.dist
    continuous_const))
  have hSeq : S = (W ∩ {p | ρ < dist p A}) ∩ {p | a < dist p A} := by
    ext p
    simp only [hS, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hpW, hpa⟩
      exact ⟨⟨hpW, by linarith⟩, lt_of_le_of_ne hpa (fun h => hcon p hpW h.symm)⟩
    · rintro ⟨⟨hpW, -⟩, hpa⟩
      exact ⟨hpW, hpa.le⟩
  have hSop : IsOpen S := by
    rw [hSeq]; exact hWo.inter (isOpen_lt continuous_const (continuous_id.dist continuous_const))
  rcases isClopen_iff.mp ⟨hScl, hSop⟩ with h | h
  · have : w₀ ∈ S := ⟨hw₀, haw⟩
    rw [h] at this; exact this
  · have : A ∈ S := h ▸ mem_univ A
    have h' : a ≤ dist A A := this.2
    rw [dist_self] at h'; linarith

omit [ConnectedSpace X] in
/-- **Jones's splitting.** Let `V` be open, `x ∈ V`, `P` with `P ∩ V = ∅`, and `O` open
with `q ∈ O ⊆ P`. If `X` is not aposyndetic at `q` with respect to `x`, then `X − V` is the union
of two disjoint closed sets each of which meets `P`. -/
theorem exists_split_of_not_aposAt {V P O : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V)
    (hPV : Disjoint P V) (hO : IsOpen O) {q : X} (hqO : q ∈ O) (hOP : O ⊆ P)
    (hna : ¬ AposAt q x) :
    ∃ W Q : Set X, IsClosed W ∧ IsClosed Q ∧ Disjoint W Q ∧ W ∪ Q = Vᶜ ∧ (W ∩ P).Nonempty ∧
      (Q ∩ P).Nonempty := by
  by_contra hno
  have hPVc : P ⊆ Vᶜ := fun p hp hpV => Set.disjoint_left.mp hPV hp hpV
  have hqP : q ∈ P := hOP hqO
  -- every point of `P` is joined to `q` by a continuum in `X − V`
  have hL : ∀ b ∈ P, ∃ L ⊆ Vᶜ, Fold.Q78.IsContinuum L ∧ q ∈ L ∧ b ∈ L := by
    intro b hb
    rcases Plane.closed_dichotomy hV.isClosed_compl isClosed_singleton isClosed_singleton
      (singleton_subset_iff.mpr (hPVc hqP)) with
      ⟨L, hLV, hL, ⟨q', hq'L, hq'⟩, ⟨b', hb'L, hb'⟩⟩ | ⟨W', hW'V, hW'cl, hW'c, hqW', hW'b⟩
    · rw [mem_singleton_iff] at hq' hb'
      subst hq' hb'
      exact ⟨L, hLV, hL, hq'L, hb'L⟩
    · exfalso
      apply hno
      refine ⟨Vᶜ \ W', W', hW'c, hW'cl, disjoint_sdiff_left, ?_, ⟨b, ⟨hPVc hb, ?_⟩, hb⟩,
        ⟨q, hqW' rfl, hqP⟩⟩
      · exact diff_union_of_subset hW'V
      · exact fun h => Set.disjoint_left.mp hW'b h rfl
  choose L hLV hL hqL hbL using hL
  set S : Set X := ⋃ b ∈ P, L b ‹_› with hS
  have hSV : S ⊆ Vᶜ := iUnion₂_subset fun b hb => hLV b hb
  have hPS : P ⊆ S := fun b hb => mem_iUnion₂.mpr ⟨b, hb, hbL b hb⟩
  have hSpre : IsPreconnected S := by
    refine isPreconnected_of_forall q fun y hy => ?_
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
    exact ⟨L b hb, subset_iUnion₂ (s := fun b hb => L b hb) b hb, hqL b hb, hyb,
      (hL b hb).2.isPreconnected⟩
  refine hna ⟨closure S, O, ⟨isClosed_closure.isCompact, ⟨q, subset_closure (hPS hqP)⟩,
    hSpre.closure⟩, hO, hqO, hOP.trans (hPS.trans subset_closure), fun hx => ?_⟩
  exact closure_minimal hSV hV.isClosed_compl hx hxV

omit [CompactSpace X] in
/-- **Nested separations.** Let `X − V₁ = W₁ ∪ Q₁` and `X − V₂ = W₂ ∪ Q₂` (closed, disjoint) with
`V₁` nonempty, `closure V₁ ⊆ Q₂` and `closure V₂ ⊆ W₁`. Then `W₂ ⊆ W₁` and `Q₁ ⊆ Q₂`. -/
theorem separation_nested {V₁ V₂ W₁ Q₁ W₂ Q₂ : Set X} (hV₁ne : V₁.Nonempty)
    (hW₁ : IsClosed W₁) (hQ₂ : IsClosed Q₂) (hWQ₁ : Disjoint W₁ Q₁) (hcov₁ : W₁ ∪ Q₁ = V₁ᶜ)
    (hWQ₂ : Disjoint W₂ Q₂) (hcov₂ : W₂ ∪ Q₂ = V₂ᶜ) (h₁ : closure V₁ ⊆ Q₂)
    (h₂ : closure V₂ ⊆ W₁) (hW₂ : IsClosed W₂) (hQ₁ : IsClosed Q₁) :
    W₂ ⊆ W₁ ∧ Q₁ ⊆ Q₂ := by
  have hmem₁ : ∀ z, z ∉ V₁ → z ∈ W₁ ∨ z ∈ Q₁ := fun z hz => by
    have : z ∈ W₁ ∪ Q₁ := hcov₁ ▸ hz
    exact this
  have hmem₂ : ∀ z, z ∉ V₂ → z ∈ W₂ ∨ z ∈ Q₂ := fun z hz => by
    have : z ∈ W₂ ∪ Q₂ := hcov₂ ▸ hz
    exact this
  set S := W₂ ∩ Q₁ with hS
  have hSeq : S = Q₂ᶜ ∩ W₁ᶜ := by
    ext z
    constructor
    · rintro ⟨hz₂, hz₁⟩
      exact ⟨fun h => Set.disjoint_left.mp hWQ₂ hz₂ h, fun h => Set.disjoint_left.mp hWQ₁ h hz₁⟩
    · rintro ⟨hzQ₂, hzW₁⟩
      have hzV₁ : z ∉ V₁ := fun h => hzQ₂ (h₁ (subset_closure h))
      have hzV₂ : z ∉ V₂ := fun h => hzW₁ (h₂ (subset_closure h))
      exact ⟨(hmem₂ z hzV₂).resolve_right hzQ₂, (hmem₁ z hzV₁).resolve_left hzW₁⟩
  have hScl : IsClosed S := hW₂.inter hQ₁
  have hSop : IsOpen S := by rw [hSeq]; exact hQ₂.isOpen_compl.inter hW₁.isOpen_compl
  have hSe : S = ∅ := by
    rcases isClopen_iff.mp ⟨hScl, hSop⟩ with h | h
    · exact h
    · obtain ⟨v, hv⟩ := hV₁ne
      have : v ∈ S := h ▸ mem_univ v
      have hv' : v ∈ V₁ᶜ := hcov₁ ▸ Or.inr this.2
      exact absurd hv hv'
  constructor
  · intro z hz
    have hzV₁ : z ∉ V₁ := fun h => Set.disjoint_left.mp hWQ₂ hz (h₁ (subset_closure h))
    refine (hmem₁ z hzV₁).resolve_right fun hzQ => ?_
    have : z ∈ S := ⟨hz, hzQ⟩
    rw [hSe] at this; exact this
  · intro z hz
    have hzV₂ : z ∉ V₂ := fun h => Set.disjoint_left.mp hWQ₁ (h₂ (subset_closure h)) hz
    refine (hmem₂ z hzV₂).resolve_left fun hzW => ?_
    have : z ∈ S := ⟨hzW, hz⟩
    rw [hSe] at this; exact this

end HPC.Jones
