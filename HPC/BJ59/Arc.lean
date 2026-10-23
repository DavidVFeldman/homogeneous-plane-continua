import HPC.BJ59.Order

/-!
# Batch 198, library: snake-like arcs of continua (Bing–Jones, Theorems 2 and 4)

`f : X → [0, 1]` is a continuous surjection of a compact metric space with connected fibres;
`G(a, b) = f⁻¹[a, b]`.

* `isPreconnected_preimage_Icc`: `G(a, b)` is connected (`f` is closed and monotone).
* `theorem2_arc`: Bing–Jones's Theorem 2, from `order_core`.
* `theorem4_of_chain`: Bing–Jones's Theorem 4, from a chain as in Theorem 3.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

section Monotone

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]

/-- **Preimages under a monotone map** (as `HPC.Hagopian.isPreconnected_preimage_of_monotone`,
with the surjectivity weakened to `A ⊆ range q`). -/
theorem isPreconnected_preimage_of_monotone' {q : X → Y} (hq : Continuous q)
    (hf : ∀ y, IsPreconnected (q ⁻¹' {y})) {A : Set Y} (hA : IsPreconnected A)
    (hAr : A ⊆ range q) : IsPreconnected (q ⁻¹' A) := by
  rw [isPreconnected_closed_iff] at hA ⊢
  intro u v hu hv huv hu' hv'
  have hqc : IsClosedMap q := hq.isClosedMap
  obtain ⟨y, hyA, ⟨x₁, hx₁u, hx₁y⟩, ⟨x₂, hx₂v, hx₂y⟩⟩ :=
    hA (q '' u) (q '' v) (hqc u hu) (hqc v hv) (fun y hy => by
      obtain ⟨x, rfl⟩ := hAr hy
      rcases huv (show x ∈ q ⁻¹' A from hy) with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · exact Or.inr ⟨x, h, rfl⟩)
      (by obtain ⟨x, hxA, hxu⟩ := hu'; exact ⟨q x, hxA, x, hxu, rfl⟩)
      (by obtain ⟨x, hxA, hxv⟩ := hv'; exact ⟨q x, hxA, x, hxv, rfl⟩)
  have hF := hf y
  rw [isPreconnected_closed_iff] at hF
  obtain ⟨z, hz, hzu, hzv⟩ := hF u v hu hv
    (fun z hz => huv (by have h : q z = y := hz; show q z ∈ A; rw [h]; exact hyA))
    ⟨x₁, hx₁y, hx₁u⟩ ⟨x₂, hx₂y, hx₂v⟩
  refine ⟨z, ?_, hzu, hzv⟩
  have h : q z = y := hz
  show q z ∈ A
  rw [h]; exact hyA

end Monotone

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- `G(a, b)` is connected. -/
theorem isPreconnected_preimage_Icc {f : X → unitInterval} (hfc : Continuous f)
    (hfs : Function.Surjective f) (hfib : ∀ t, IsPreconnected (f ⁻¹' {t})) (a b : unitInterval) :
    IsPreconnected (f ⁻¹' Icc a b) :=
  isPreconnected_preimage_of_monotone' hfc hfib isPreconnected_Icc
    (fun t _ => hfs t)

/-- `G(a, b)` is compact. -/
theorem isCompact_preimage_Icc {f : X → unitInterval} (hfc : Continuous f) (a b : unitInterval) :
    IsCompact (f ⁻¹' Icc a b) :=
  (isClosed_Icc.preimage hfc).isCompact

/-- **Bing–Jones, Theorem 2** (p. 174), with explicit hypotheses. -/
theorem theorem2_arc {f : X → unitInterval} (hfc : Continuous f) (hfs : Function.Surjective f)
    (hfib : ∀ t, IsPreconnected (f ⁻¹' {t})) {a b c d : unitInterval} (hab : a < b)
    (hbc : b < c) (hcd : c < d) :
    ∃ ε > 0, ∀ (n : ℕ) (D : Chain X n), IsEpsChain D ε → univ ⊆ D.union →
      ∀ i j k : Fin n, (D.link i ∩ f ⁻¹' Icc 0 a).Nonempty →
        (D.link j ∩ f ⁻¹' Icc b c).Nonempty → (D.link k ∩ f ⁻¹' Icc d 1).Nonempty →
          (i < j ∧ j < k) ∨ (k < j ∧ j < i) := by
  set P0a := f ⁻¹' Icc 0 a
  set Pbc := f ⁻¹' Icc b c
  set Pd1 := f ⁻¹' Icc d 1
  set P0b := f ⁻¹' Icc 0 b
  set Pc1 := f ⁻¹' Icc c 1
  have hdisj : ∀ {p q r s : unitInterval}, q < r → Disjoint (f ⁻¹' Icc p q) (f ⁻¹' Icc r s) :=
    fun hqr => Set.disjoint_left.2 fun x hx hx' => absurd (hx.2.trans_lt hqr) (not_lt.2 hx'.1)
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_sep_of_disjoint (isCompact_preimage_Icc hfc _ _)
    (isCompact_preimage_Icc hfc _ _) (hdisj hab : Disjoint P0a Pbc)
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_sep_of_disjoint (isCompact_preimage_Icc hfc _ _)
    (isCompact_preimage_Icc hfc _ _) (hdisj hcd : Disjoint Pbc Pd1)
  obtain ⟨ε₃, hε₃, h₃⟩ := exists_sep_of_disjoint (isCompact_preimage_Icc hfc _ _)
    (isCompact_preimage_Icc hfc _ _) (hdisj hbc : Disjoint P0b Pc1)
  refine ⟨min ε₁ (min ε₂ (ε₃ / 2)), by positivity, ?_⟩
  intro n D hD hcov i j k hi hj hk
  set ε := min ε₁ (min ε₂ (ε₃ / 2))
  have e1 : ε ≤ ε₁ := min_le_left _ _
  have e2 : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : 2 * ε ≤ ε₃ := by
    have : ε ≤ ε₃ / 2 := (min_le_right _ _).trans (min_le_right _ _); linarith
  have s1 : ∀ x ∈ P0a, ∀ y ∈ Pbc, ε ≤ dist x y := fun x hx y hy => e1.trans (h₁ x hx y hy)
  have s2 : ∀ x ∈ Pbc, ∀ y ∈ Pd1, ε ≤ dist x y := fun x hx y hy => e2.trans (h₂ x hx y hy)
  have s3 : ∀ x ∈ P0b, ∀ y ∈ Pc1, 2 * ε ≤ dist x y := fun x hx y hy => e3.trans (h₃ x hx y hy)
  have s3' : ∀ x ∈ Pc1, ∀ y ∈ P0b, 2 * ε ≤ dist x y := fun x hx y hy => by
    rw [dist_comm]; exact s3 y hy x hx
  have hA1 : P0a ⊆ P0b := preimage_mono (Icc_subset_Icc le_rfl hab.le)
  have hA3 : Pd1 ⊆ Pc1 := preimage_mono (Icc_subset_Icc hcd.le le_rfl)
  have hC : ∀ x, x ∈ P0b ∨ x ∈ Pc1 ∨ x ∈ Pbc := fun x => by
    rcases le_or_gt (f x) b with h | h
    · exact Or.inl ⟨unitInterval.nonneg', h⟩
    rcases le_or_gt c (f x) with h' | h'
    · exact Or.inr (Or.inl ⟨h', unitInterval.le_one'⟩)
    · exact Or.inr (Or.inr ⟨h.le, h'.le⟩)
  have hC' : ∀ x, x ∈ Pc1 ∨ x ∈ P0b ∨ x ∈ Pbc := fun x => by
    rcases hC x with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hPc := isPreconnected_preimage_Icc hfc hfs hfib
  have hik : i ≠ k := by
    rintro rfl
    obtain ⟨x, hx, hxA⟩ := hi
    obtain ⟨y, hy, hyA⟩ := hk
    exact not_meets_adjacent hD s3 i i (by simp) ⟨⟨x, hx, hA1 hxA⟩, ⟨y, hy, hA3 hyA⟩⟩
  rcases lt_or_gt_of_ne hik with h | h
  · exact Or.inl (order_core D hcov (hPc _ _) (hPc _ _) (hPc _ _) hA1 hA3 hC
      (fun l l' hl => not_meets_adjacent hD s3 l l' hl)
      (fun l => not_meets_both hD s1 l) (fun l => not_meets_both hD s2 l) h hi hj hk)
  · exact Or.inr (order_core D hcov (hPc _ _) (hPc _ _) (hPc _ _) hA3 hA1 hC'
      (fun l l' hl => not_meets_adjacent hD s3' l l' hl)
      (fun l hl => not_meets_both hD s2 l ⟨hl.2, hl.1⟩)
      (fun l hl => not_meets_both hD s1 l ⟨hl.2, hl.1⟩) h hk hj hi)

omit [CompactSpace X] in
/-- **Bing–Jones, Theorem 4** (p. 175), from a chain as in Theorem 3: with an `ε`-chain from `g₀`
to `g₁`, where `ε` is less than the distance from a point `p ∈ U` to `X − U`, the link through `p`
lies in `U`, and the links before and after it split `X − U`. -/
theorem theorem4_explicit {f : X → unitInterval} {U : Set X} (hU : IsOpen U)
    (hU01 : Disjoint U (f ⁻¹' {0, 1})) (hg₀ : IsPreconnected (f ⁻¹' {0}))
    (hg₁ : IsPreconnected (f ⁻¹' {1})) {m : ℕ} (D : Chain X (m + 1)) (hcov : univ ⊆ D.union)
    (h0 : (D.link 0 ∩ f ⁻¹' {0}).Nonempty) (h1 : (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty)
    (l : Fin (m + 1)) (hlU : D.link l ⊆ U) :
    IsClosed (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : t < l), D.link t) ∧
      IsClosed (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : l < t), D.link t) ∧
      Disjoint (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : t < l), D.link t)
        (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : l < t), D.link t) ∧
      (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : t < l), D.link t) ∪
        (Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : l < t), D.link t) = Uᶜ ∧
      f ⁻¹' {0} ⊆ Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : t < l), D.link t ∧
      f ⁻¹' {1} ⊆ Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : l < t), D.link t := by
  set A : Set X := Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : t < l), D.link t
  set B : Set X := Uᶜ ∩ ⋃ t : Fin (m + 1), ⋃ (_ : l < t), D.link t
  have hmem : ∀ x : X, ∃ t, x ∈ D.link t := fun x => mem_iUnion.1 (hcov (mem_univ x))
  have hAeq : A = Uᶜ \ ⋃ t : Fin (m + 1), ⋃ (_ : l ≤ t), D.link t := by
    ext x; simp only [A, mem_inter_iff, mem_diff, mem_iUnion, not_exists, mem_compl_iff]
    constructor
    · rintro ⟨hxU, t, htl, hxt⟩
      refine ⟨hxU, fun t' hlt' hxt' => ?_⟩
      rcases eq_or_lt_of_le hlt' with h | h
      · exact hxU (hlU (h ▸ hxt'))
      · have := (D.adjacent t t').1 ⟨x, hxt, hxt'⟩
        rw [Fin.lt_def] at htl h; omega
    · rintro ⟨hxU, hx⟩
      obtain ⟨t, ht⟩ := hmem x
      refine ⟨hxU, t, ?_, ht⟩
      by_contra h; push_neg at h; exact hx t h ht
  have hBeq : B = Uᶜ \ ⋃ t : Fin (m + 1), ⋃ (_ : t ≤ l), D.link t := by
    ext x; simp only [B, mem_inter_iff, mem_diff, mem_iUnion, not_exists, mem_compl_iff]
    constructor
    · rintro ⟨hxU, t, hlt, hxt⟩
      refine ⟨hxU, fun t' htl' hxt' => ?_⟩
      rcases eq_or_lt_of_le htl' with h | h
      · exact hxU (hlU (h ▸ hxt'))
      · have := (D.adjacent t t').1 ⟨x, hxt, hxt'⟩
        rw [Fin.lt_def] at hlt h; omega
    · rintro ⟨hxU, hx⟩
      obtain ⟨t, ht⟩ := hmem x
      refine ⟨hxU, t, ?_, ht⟩
      by_contra h; push_neg at h; exact hx t h ht
  have hAc : IsClosed A := by
    rw [hAeq]
    exact hU.isClosed_compl.sdiff (isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t)
  have hBc : IsClosed B := by
    rw [hBeq]
    exact hU.isClosed_compl.sdiff (isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t)
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨-, hx'⟩
    simp only [mem_iUnion] at hx hx'
    obtain ⟨t, htl, hxt⟩ := hx
    obtain ⟨t', hlt', hxt'⟩ := hx'
    have := (D.adjacent t t').1 ⟨x, hxt, hxt'⟩
    rw [Fin.lt_def] at htl hlt'; omega
  have hcup : A ∪ B = Uᶜ := by
    ext x; constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hx
      obtain ⟨t, ht⟩ := hmem x
      rcases lt_trichotomy t l with h | rfl | h
      · exact Or.inl ⟨hx, mem_iUnion₂.2 ⟨t, h, ht⟩⟩
      · exact absurd (hlU ht) hx
      · exact Or.inr ⟨hx, mem_iUnion₂.2 ⟨t, h, ht⟩⟩
  have hgU : ∀ s ∈ ({0, 1} : Set unitInterval), f ⁻¹' {s} ⊆ Uᶜ := fun s hs x hx hxU =>
    Set.disjoint_left.1 hU01 hxU (show f x ∈ ({0, 1} : Set unitInterval) by
      rw [show f x = s from hx]; exact hs)
  have hsplit : ∀ s ∈ ({0, 1} : Set unitInterval), IsPreconnected (f ⁻¹' {s}) →
      f ⁻¹' {s} ⊆ A ∨ f ⁻¹' {s} ⊆ B := fun s hs hg =>
    isPreconnected_iff_subset_of_disjoint_closed.1 hg A B hAc hBc
      (by rw [hcup]; exact hgU s hs) (by rw [Set.disjoint_iff_inter_eq_empty.1 hAB, inter_empty])
  refine ⟨hAc, hBc, hAB, hcup, ?_, ?_⟩
  · rcases hsplit 0 (by simp) hg₀ with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx0, hx⟩ := h0
      have hxU := hgU 0 (by simp) hx
      rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
      · have h0l : (0 : Fin (m + 1)) = l := Fin.ext (by simp [hl])
        exact hxU (hlU (h0l ▸ hx0))
      · exact Set.disjoint_left.1 hAB ⟨hxU, mem_iUnion₂.2 ⟨0, Fin.lt_def.2 hl, hx0⟩⟩ (h hx)
  · rcases hsplit 1 (by simp) hg₁ with h | h
    · exfalso
      obtain ⟨x, hx0, hx⟩ := h1
      have hxU := hgU 1 (by simp) hx
      rcases eq_or_lt_of_le (Fin.le_last l) with hl | hl
      · exact hxU (hlU (hl ▸ hx0))
      · exact Set.disjoint_left.1 hAB (h hx) ⟨hxU, mem_iUnion₂.2 ⟨_, hl, hx0⟩⟩
    · exact h

omit [CompactSpace X] in
/-- **Bing–Jones, Theorem 4** (p. 175), from a chain as in Theorem 3 (`theorem4_explicit`). -/
theorem theorem4_of_chain {f : X → unitInterval} {U : Set X} (hU : IsOpen U)
    (hU01 : Disjoint U (f ⁻¹' {0, 1})) (hg₀ : IsPreconnected (f ⁻¹' {0}))
    (hg₁ : IsPreconnected (f ⁻¹' {1})) {m : ℕ} (D : Chain X (m + 1)) (hcov : univ ⊆ D.union)
    (h0 : (D.link 0 ∩ f ⁻¹' {0}).Nonempty) (h1 : (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty)
    (l : Fin (m + 1)) (hlU : D.link l ⊆ U) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B :=
  ⟨_, _, theorem4_explicit hU hU01 hg₀ hg₁ D hcov h0 h1 l hlU⟩

end HPC.BJ59
