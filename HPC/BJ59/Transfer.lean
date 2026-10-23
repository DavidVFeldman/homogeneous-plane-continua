import HPC.Plane.EpsMap98
import HPC.Plane.Monotone51
import HPC.Plane.PseudoArc51

/-!
# Batch 198, library: snake-likeness and pseudo-arcs are topological

The library's `IsSnakeLike` and `IsPseudoArc` are stated for subsets of a metric space, with chains
of open sets of the ambient space. This file shows that both pass along homeomorphisms between
such subsets, when the target space is compact:

* `exists_epsMap_of_chain`: a set covered by an `ε`-chain has an `ε`-map to `ℝ` (the barycentre
  of the indices, weighted by the distances to the complements of the links);
* `isSnakeLike_of_homeomorph` (through the `ε`-map criterion `isSnakeLike_of_epsMap`, batch 98,
  and the Tietze extension theorem);
* `isHereditarilyIndecomposable_of_homeomorph` (through `isHereditarilyIndecomposable_image`);
* `isPseudoArc_of_homeomorph`, and the transfers between a set and the subtype it spans.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

section EpsMap

variable {X : Type*} [MetricSpace X]

open Classical in
/-- A nonnegative continuous function, positive exactly on the open set `U`. -/
noncomputable def posFn (U : Set X) : X → ℝ := fun x => if Uᶜ.Nonempty then infDist x Uᶜ else 1

theorem continuous_posFn (U : Set X) : Continuous (posFn U) := by
  unfold posFn; split_ifs
  · exact continuous_infDist_pt _
  · exact continuous_const

theorem posFn_nonneg (U : Set X) (x : X) : 0 ≤ posFn U x := by
  unfold posFn; split_ifs
  · exact infDist_nonneg
  · exact zero_le_one

theorem posFn_pos {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) : 0 < posFn U x := by
  unfold posFn; split_ifs with h
  · exact (hU.isClosed_compl.notMem_iff_infDist_pos h).1 (fun h' => h' hx)
  · exact one_pos

theorem posFn_zero {U : Set X} {x : X} (hx : x ∉ U) : posFn U x = 0 := by
  unfold posFn; rw [if_pos ⟨x, hx⟩]; exact infDist_zero_of_mem hx

/-- **An `ε`-chain gives an `ε`-map.** If `K` is covered by an `ε`-chain `D`, the weighted mean of
the indices of the links containing a point is a continuous real function on `K` whose fibres have
diameter less than `ε`: its integer part is the first link containing the point. -/
theorem exists_epsMap_of_chain {K : Set X} {n : ℕ} (D : Chain X n) {ε : ℝ} (hD : IsEpsChain D ε)
    (hK : K ⊆ D.union) :
    ∃ g : K → ℝ, Continuous g ∧ ∀ x y : K, g x = g y → dist x y < ε := by
  classical
  set w : Fin n → X → ℝ := fun i => posFn (D.link i)
  set S : X → ℝ := fun x => ∑ i, w i x
  set N : X → ℝ := fun x => ∑ i : Fin n, ((i : ℕ) : ℝ) * w i x
  have hSpos : ∀ x ∈ K, 0 < S x := fun x hx => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hK hx)
    exact Finset.sum_pos' (fun j _ => posFn_nonneg _ _)
      ⟨i, Finset.mem_univ _, posFn_pos (D.isOpen i) hi⟩
  have hkey : ∀ x ∈ K, ∀ p : Fin n, x ∈ D.link p → (∀ k : Fin n, k < p → x ∉ D.link k) →
      ((p : ℕ) : ℝ) * S x ≤ N x ∧ N x < (((p : ℕ) : ℝ) + 1) * S x := by
    intro x _ p hp hmin
    have hz : ∀ k : Fin n, w k x ≠ 0 → (k : ℕ) = p ∨ (k : ℕ) = p + 1 := by
      intro k hk
      have hxk : x ∈ D.link k := by
        by_contra h; exact hk (posFn_zero h)
      have h1 : ¬ k < p := fun h => hmin k h hxk
      have h2 := (D.adjacent p k).1 ⟨x, hp, hxk⟩
      rw [not_lt, Fin.le_def] at h1
      omega
    constructor
    · have : N x - ((p : ℕ) : ℝ) * S x = ∑ i : Fin n, (((i : ℕ) : ℝ) - p) * w i x := by
        simp only [N, S, Finset.mul_sum]; rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h0 : 0 ≤ ∑ i : Fin n, (((i : ℕ) : ℝ) - p) * w i x := Finset.sum_nonneg fun k _ => by
        by_cases hk : w k x = 0
        · rw [hk, mul_zero]
        · rcases hz k hk with h | h
          · rw [show ((k : ℕ) : ℝ) = p by exact_mod_cast h]; simp
          · apply mul_nonneg _ (posFn_nonneg _ _)
            rw [show ((k : ℕ) : ℝ) = p + 1 by exact_mod_cast h]; linarith
      linarith
    · have : (((p : ℕ) : ℝ) + 1) * S x - N x =
          ∑ i : Fin n, (((p : ℕ) : ℝ) + 1 - i) * w i x := by
        simp only [N, S, Finset.mul_sum]; rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h0 : 0 < ∑ i : Fin n, (((p : ℕ) : ℝ) + 1 - i) * w i x := by
        apply Finset.sum_pos'
        · intro k _
          by_cases hk : w k x = 0
          · rw [hk, mul_zero]
          · rcases hz k hk with h | h
            · apply mul_nonneg _ (posFn_nonneg _ _)
              rw [show ((k : ℕ) : ℝ) = p by exact_mod_cast h]; linarith
            · rw [show ((k : ℕ) : ℝ) = p + 1 by exact_mod_cast h]; simp
        · exact ⟨p, Finset.mem_univ _, by
            have := posFn_pos (D.isOpen p) hp
            simp only [w]; nlinarith⟩
      linarith
  refine ⟨fun x => N x / S x, ?_, ?_⟩
  · have hN : Continuous N := continuous_finset_sum _ fun i _ =>
      continuous_const.mul (continuous_posFn _)
    have hS : Continuous S := continuous_finset_sum _ fun i _ => continuous_posFn _
    exact (hN.comp continuous_subtype_val).div (hS.comp continuous_subtype_val)
      fun x => (hSpos x x.2).ne'
  · have hmin : ∀ x ∈ K, ∃ p : Fin n, x ∈ D.link p ∧ ∀ k : Fin n, k < p → x ∉ D.link k := by
      intro x hx
      have hex : ∃ i, x ∈ D.link i := mem_iUnion.1 (hK hx)
      have hne : (Finset.univ.filter fun i => x ∈ D.link i).Nonempty := by
        obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hi]⟩
      refine ⟨Finset.min' _ hne, ?_, ?_⟩
      · have := Finset.min'_mem _ hne
        simpa using this
      · intro k hk hxk
        have := Finset.min'_le (Finset.univ.filter fun i => x ∈ D.link i) k (by simp [hxk])
        exact absurd hk (not_lt.2 this)
    intro x y hxy
    obtain ⟨p, hp, hpm⟩ := hmin x x.2
    obtain ⟨q, hq, hqm⟩ := hmin y y.2
    have e1 := hkey x x.2 p hp hpm
    have e2 := hkey y y.2 q hq hqm
    have sx := hSpos x x.2
    have sy := hSpos y y.2
    have a1 : ((p : ℕ) : ℝ) ≤ N x / S x := (le_div_iff₀ sx).2 e1.1
    have a2 : N x / S x < (p : ℕ) + 1 := (div_lt_iff₀ sx).2 e1.2
    have b1 : ((q : ℕ) : ℝ) ≤ N y / S y := (le_div_iff₀ sy).2 e2.1
    have b2 : N y / S y < (q : ℕ) + 1 := (div_lt_iff₀ sy).2 e2.2
    simp only at hxy
    have hpq : p = q := by
      have h1 : ((p : ℕ) : ℝ) < (q : ℕ) + 1 := by linarith
      have h2 : ((q : ℕ) : ℝ) < (p : ℕ) + 1 := by linarith
      have h1' : (p : ℕ) < q + 1 := by exact_mod_cast h1
      have h2' : (q : ℕ) < p + 1 := by exact_mod_cast h2
      exact Fin.ext (by omega)
    subst hpq
    rw [Subtype.dist_eq]
    exact lt_of_le_of_lt (dist_le_diam_of_mem (hD p).1 hp hq) (hD p).2

/-- A snake-like set has `ε`-maps to `ℝ` for every `ε > 0`. -/
theorem exists_epsMap_of_isSnakeLike {K : Set X} (hK : IsSnakeLike K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : K → ℝ, Continuous g ∧ ∀ x y : K, g x = g y → dist x y < ε := by
  obtain ⟨n, D, hD, hKD⟩ := hK.2 ε hε
  exact exists_epsMap_of_chain D hD hKD

end EpsMap

section Homeo

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A continuum is carried to a continuum by a homeomorphism of the sets. -/
theorem isContinuum_of_homeomorph {A : Set X} {B : Set Y} (hA : Fold.Q78.IsContinuum A)
    (e : A ≃ₜ B) : Fold.Q78.IsContinuum B := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA.1
  haveI : ConnectedSpace A := isConnected_iff_connectedSpace.1 hA.2
  haveI : CompactSpace B := e.compactSpace
  haveI : ConnectedSpace B := e.surjective.connectedSpace e.continuous
  exact ⟨isCompact_iff_compactSpace.2 inferInstance, isConnected_iff_connectedSpace.2 inferInstance⟩

/-- **Snake-likeness is topological** (into a compact space): a set homeomorphic to a snake-like
set is snake-like. -/
theorem isSnakeLike_of_homeomorph [CompactSpace Y] {A : Set X} {B : Set Y} (hA : IsSnakeLike A)
    (e : A ≃ₜ B) : IsSnakeLike B := by
  have hB := isContinuum_of_homeomorph hA.1 e
  refine isSnakeLike_of_epsMap hB fun ε hε => ?_
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA.1.1
  obtain ⟨δ, hδ, hδe⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous e.continuous) ε hε
  obtain ⟨g, hg, hgf⟩ := exists_epsMap_of_isSnakeLike hA hδ
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hB.1.isClosed
    ⟨g ∘ e.symm, hg.comp e.symm.continuous⟩
  refine ⟨F, F.continuous, fun x hx y hy hxy => ?_⟩
  have hx' : F x = g (e.symm ⟨x, hx⟩) := by
    have := congrArg (fun φ : C(B, ℝ) => φ ⟨x, hx⟩) hF; simpa using this
  have hy' : F y = g (e.symm ⟨y, hy⟩) := by
    have := congrArg (fun φ : C(B, ℝ) => φ ⟨y, hy⟩) hF; simpa using this
  have h1 := hgf _ _ (hx'.symm.trans (hxy.trans hy'))
  have h2 := hδe h1
  rw [e.apply_symm_apply, e.apply_symm_apply] at h2
  exact h2

/-- **Hereditary indecomposability is topological**: a set homeomorphic to a hereditarily
indecomposable continuum is hereditarily indecomposable. -/
theorem isHereditarilyIndecomposable_of_homeomorph {A : Set X} {B : Set Y}
    (hA : Fold.Q78.IsContinuum A) (hHI : IsHereditarilyIndecomposable A) (e : A ≃ₜ B) :
    IsHereditarilyIndecomposable B := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA.2.nonempty
  let F : X → Y := fun x => if h : x ∈ A then (e ⟨x, h⟩ : Y) else (e ⟨a₀, ha₀⟩ : Y)
  have hFA : ∀ x (h : x ∈ A), F x = (e ⟨x, h⟩ : Y) := fun x h => dif_pos h
  refine isHereditarilyIndecomposable_image (f := F) hA hHI ⟨?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : A.restrict F = fun x : A => (e x : Y) := funext fun x => hFA x x.2
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · ext y; constructor
    · rintro ⟨x, hx, rfl⟩; rw [hFA x hx]; exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩ : X), (e.symm ⟨y, hy⟩).2, ?_⟩
      rw [hFA _ (e.symm ⟨y, hy⟩).2]; simp
  · intro y hy
    have : A ∩ F ⁻¹' {y} = {(e.symm ⟨y, hy⟩ : X)} := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hxy⟩
        rw [hFA x hx] at hxy
        have : e ⟨x, hx⟩ = ⟨y, hy⟩ := Subtype.ext hxy
        rw [← this, e.symm_apply_apply]
      · rintro rfl
        refine ⟨(e.symm ⟨y, hy⟩).2, ?_⟩
        rw [hFA _ (e.symm ⟨y, hy⟩).2]; simp
    rw [this]; exact isConnected_singleton

/-- **Being a pseudo-arc is topological** (into a compact space). -/
theorem isPseudoArc_of_homeomorph [CompactSpace Y] {A : Set X} {B : Set Y} (hA : IsPseudoArc A)
    (e : A ≃ₜ B) : IsPseudoArc B := by
  refine ⟨isSnakeLike_of_homeomorph hA.1 e,
    isHereditarilyIndecomposable_of_homeomorph hA.1.1 hA.2.1 e, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hA.2.2
  refine ⟨e ⟨a, ha⟩, (e ⟨a, ha⟩).2, e ⟨b, hb⟩, (e ⟨b, hb⟩).2, fun h => hab ?_⟩
  have := e.injective (Subtype.ext h)
  exact congrArg Subtype.val this

/-- A pseudo-arc in the ambient space, lying in `T`, is a pseudo-arc of the (compact) subtype. -/
theorem isPseudoArc_subtype_of_image {T : Set X} [CompactSpace T] {S : Set T}
    (h : IsPseudoArc (Subtype.val '' S : Set X)) : IsPseudoArc S :=
  isPseudoArc_of_homeomorph h (IsEmbedding.subtypeVal.homeomorphImage S).symm

/-- A pseudo-arc of a subtype is a pseudo-arc of the (compact) ambient space. -/
theorem isPseudoArc_image_of_subtype [CompactSpace X] {T : Set X} {S : Set T}
    (h : IsPseudoArc S) : IsPseudoArc (Subtype.val '' S : Set X) :=
  isPseudoArc_of_homeomorph h (IsEmbedding.subtypeVal.homeomorphImage S)

/-- A snake-like set `A` is snake-like as the whole of the subtype `A`. -/
theorem isSnakeLike_univ_of_isSnakeLike {A : Set X} (h : IsSnakeLike A) :
    IsSnakeLike (univ : Set A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 h.1.1
  exact isSnakeLike_of_homeomorph h (Homeomorph.Set.univ A).symm

end Homeo

end HPC.BJ59
