import HPC.Moore.Sec6Arc
import HPC.Moore.ArcChar

/-!
# Limit arcs (batch 138, for Theorem 32)

Moore's proof of Theorem 32 ends with an infinite sequence of arcs converging to the point `B`,
whose union with `B` is \"easily seen\" to be an arc (\"It is easily seen that `B` is a limit point
of `CX₁ + CX₂ + ⋯` and that `τ` is connected and contains no proper connected subset that contains
`B` and `C`\"). This file proves the general statement used here (`Gen.tarc_of_seq`): if the arcs
`εₙ` from `yₙ` to `yₙ₊₁` meet only consecutively, in the points `yₙ₊₁`, and converge to `B`, then
`B + ε₀ + ε₁ + ⋯` is an arc from `y₀` to `B`. The proof is Moore's: the set is compact (the
`εₙ` converge to `B`), connected, and irreducible between `y₀` and `B` (a point `z ≠ B` other
than `y₀` cuts it), so it is an arc by the arc characterization of batch 137
(`isIrreducibleConnected_iff_arc`).
-/

namespace HPC.Moore

open Set Topology Filter
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X]

/-- A point `z` of an arc `AB`, other than `A` and `B`, splits it into arcs `Az` and `zB` with only
`z` in common. -/
theorem TArc.split [T2Space X] {A B z : X} {Γ : Set X} (h : TArc A B Γ) (hz : z ∈ Γ)
    (hzA : z ≠ A) (hzB : z ≠ B) :
    ∃ Γ₁ Γ₂, TArc A z Γ₁ ∧ TArc z B Γ₂ ∧ Γ₁ ∪ Γ₂ = Γ ∧ Γ₁ ∩ Γ₂ = {z} := by
  obtain ⟨-, φ, hφ, rfl, rfl, rfl⟩ := h
  obtain ⟨c, rfl⟩ := hz
  have hc0 : 0 < c := lt_of_le_of_ne nonneg' (fun e => hzA (by rw [← e]))
  have hc1 : c < 1 := lt_of_le_of_ne le_one' (fun e => hzB (by rw [e]))
  refine ⟨φ '' Icc 0 c, φ '' Icc c 1, TArc.image_Icc hφ hc0, TArc.image_Icc hφ hc1, ?_, ?_⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc nonneg' le_one', ← image_univ]
    congr 1
    ext t; simp only [mem_Icc, mem_univ, iff_true]; exact ⟨nonneg', le_one'⟩
  · rw [← image_inter hφ.injective, Icc_inter_Icc_eq_singleton nonneg' le_one', image_singleton]

/-- `B` together with a sequence of compact sets converging to `B` is compact. -/
theorem isCompact_insert_iUnion {B : X} {ε : ℕ → Set X} (hc : ∀ n, IsCompact (ε n))
    (hlim : ∀ U ∈ 𝓝 B, ∀ᶠ n in atTop, ε n ⊆ U) : IsCompact (insert B (⋃ n, ε n)) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcover (mem_insert B _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim (U i₀) ((hU i₀).mem_nhds hi₀))
  have : ∀ n, ∃ t : Finset ι, ε n ⊆ ⋃ i ∈ t, U i := fun n =>
    (hc n).elim_finite_subcover U hU
      ((subset_iUnion ε n).trans ((subset_insert _ _).trans hcover))
  choose t ht using this
  refine ⟨insert i₀ ((Finset.range N).biUnion t), ?_⟩
  rintro x (rfl | hx)
  · exact mem_biUnion (Finset.mem_insert_self _ _) hi₀
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    by_cases hnN : n < N
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht n hn)
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hnN, hi⟩), hxi⟩
    · exact mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hN n (not_lt.mp hnN) hn⟩

/-- **Limit arcs.** If the arcs `εₙ` from `yₙ` to `yₙ₊₁` meet only consecutively, in the points
`yₙ₊₁`, miss `B`, and converge to `B`, then `B + ε₀ + ε₁ + ⋯` is an arc from `y₀` to `B`. -/
theorem tarc_of_seq [TopologicalSpace.MetrizableSpace X] {y : ℕ → X} {ε : ℕ → Set X} {B : X}
    (harc : ∀ n, TArc (y n) (y (n + 1)) (ε n))
    (hcons : ∀ n, ε n ∩ ε (n + 1) = {y (n + 1)})
    (hdisj : ∀ n m, n + 2 ≤ m → Disjoint (ε n) (ε m))
    (hB : ∀ n, B ∉ ε n)
    (hlim : ∀ U ∈ 𝓝 B, ∀ᶠ n in atTop, ε n ⊆ U) :
    TArc (y 0) B (insert B (⋃ n, ε n)) := by
  set τ := insert B (⋃ n, ε n) with hτ
  -- the initial arcs `Γ n = ε 0 + ⋯ + ε n` and the tails
  set Γ : ℕ → Set X := fun n => ⋃ k ∈ Iic n, ε k with hΓ
  set T : ℕ → Set X := fun n => insert B (⋃ k, ε (n + k)) with hT
  have hΓT : ∀ n, Γ n ∩ T (n + 1) ⊆ {y (n + 1)} := by
    intro n x ⟨hx1, hx2⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx1
    rcases hx2 with rfl | hx2
    · exact absurd hxk (hB k)
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx2
    have hk' : k ≤ n := hk
    by_cases hkn : k = n ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hkn
      rw [← hcons k]; exact ⟨hxk, by simpa using hxj⟩
    · exfalso
      have : k + 2 ≤ n + 1 + j := by omega
      exact disjoint_left.mp (hdisj k _ this) hxk hxj
  have hΓarc : ∀ n, TArc (y 0) (y (n + 1)) (Γ n) := by
    intro n
    induction n with
    | zero => simpa [hΓ] using harc 0
    | succ n ih =>
      have heq : Γ (n + 1) = Γ n ∪ ε (n + 1) := by
        ext x
        simp only [hΓ, mem_iUnion, mem_Iic, mem_union, exists_prop]
        constructor
        · rintro ⟨k, hk, hx⟩
          rcases Nat.lt_or_ge k (n + 1) with h | h
          · exact Or.inl ⟨k, by omega, hx⟩
          · exact Or.inr (by rwa [show k = n + 1 by omega] at hx)
        · rintro (⟨k, hk, hx⟩ | hx)
          · exact ⟨k, by omega, hx⟩
          · exact ⟨n + 1, le_rfl, hx⟩
      rw [heq]
      refine ih.union (harc (n + 1)) ?_
      apply subset_antisymm
      · rintro x ⟨hx1, hx2⟩
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx1
        have hk' : k ≤ n := hk
        rcases Nat.lt_or_ge k n with h | h
        · exact absurd hxk (disjoint_right.mp (hdisj k (n + 1) (by omega)) hx2)
        · obtain rfl : k = n := by omega
          rw [← hcons k]; exact ⟨hxk, hx2⟩
      · rintro x rfl
        exact ⟨mem_iUnion₂.mpr ⟨n, mem_Iic.mpr le_rfl, (harc n).right_mem⟩, (harc (n + 1)).left_mem⟩
  have hTc : ∀ n, IsCompact (T n) := fun n =>
    isCompact_insert_iUnion (fun k => (harc (n + k)).isCompact) fun U hU => by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim U hU)
      exact eventually_atTop.mpr ⟨N, fun k hk => hN _ (by omega)⟩
  have hτT : τ = T 0 := by simp [hτ, hT]
  have hτsplit : ∀ n, τ ⊆ Γ n ∪ T (n + 1) := by
    intro n x hx
    rcases hx with rfl | hx
    · exact Or.inr (mem_insert _ _)
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    rcases Nat.lt_or_ge n k with h | h
    · refine Or.inr (Or.inr (mem_iUnion.mpr ⟨k - (n + 1), ?_⟩))
      rwa [show n + 1 + (k - (n + 1)) = k by omega]
    · exact Or.inl (mem_iUnion₂.mpr ⟨k, mem_Iic.mpr h, hxk⟩)
  have hΓτ : ∀ n, Γ n ⊆ τ := fun n x hx => by
    obtain ⟨k, -, hxk⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨k, hxk⟩)
  have hTτ : ∀ n, T n ⊆ τ := fun n x hx => by
    rcases hx with rfl | hx
    · exact mem_insert _ _
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨n + k, hxk⟩)
  have hy0B : y 0 ≠ B := fun e => hB 0 (e ▸ (harc 0).left_mem)
  -- compact and connected
  have hτc : IsCompact τ := hτT ▸ hTc 0
  have hpc : IsPreconnected (⋃ n, ε n) :=
    IsPreconnected.iUnion_of_chain (fun n => (harc n).isPreconnected) fun n =>
      ⟨y (n + 1), (harc n).right_mem, (harc (n + 1)).left_mem⟩
  have hτconn : IsConnected τ := by
    refine ⟨⟨B, mem_insert _ _⟩, hpc.subset_closure (subset_insert _ _) ?_⟩
    rintro x (rfl | hx)
    · rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨n, hn⟩ := (hlim U hU).exists
      exact ⟨y n, hn (harc n).left_mem, mem_iUnion.mpr ⟨n, (harc n).left_mem⟩⟩
    · exact subset_closure hx
  -- irreducible
  have hirr : ∀ H ⊆ τ, H ≠ τ → y 0 ∈ H → B ∈ H → ¬ IsConnected H := by
    intro H hHτ hne hy0 hBH hH
    obtain ⟨z, hzτ, hzH⟩ : ∃ z ∈ τ, z ∉ H := by
      by_contra hc
      push_neg at hc
      exact hne (subset_antisymm hHτ hc)
    have hzB : z ≠ B := fun e => hzH (e ▸ hBH)
    have hzy : z ≠ y 0 := fun e => hzH (e ▸ hy0)
    obtain ⟨k, hzk⟩ := mem_iUnion.mp (hzτ.resolve_left hzB)
    have hzΓ : z ∈ Γ (k + 1) := mem_iUnion₂.mpr ⟨k, mem_Iic.mpr (Nat.le_succ k), hzk⟩
    have hzy' : z ≠ y (k + 1 + 1) := by
      intro e
      have : z ∈ ε (k + 2) := e ▸ (harc (k + 2)).left_mem
      exact disjoint_left.mp (hdisj k (k + 2) le_rfl) hzk this
    obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓu, hΓi⟩ := (hΓarc (k + 1)).split hzΓ hzy hzy'
    have hcov : H ⊆ Γ₁ ∪ (Γ₂ ∪ T (k + 1 + 1)) := by
      intro x hx
      rcases hτsplit (k + 1) (hHτ hx) with h | h
      · rw [← hΓu] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hint : H ∩ (Γ₁ ∩ (Γ₂ ∪ T (k + 1 + 1))) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
      intro hxH hx1 hx2
      have hxz : x = z := by
        rcases hx2 with hx2 | hx2
        · have : x ∈ Γ₁ ∩ Γ₂ := ⟨hx1, hx2⟩
          rwa [hΓi] at this
        · have hxΓ : x ∈ Γ (k + 1) := hΓu ▸ Or.inl hx1
          have := hΓT (k + 1) ⟨hxΓ, hx2⟩
          rw [mem_singleton_iff] at this
          have : x ∈ Γ₁ ∩ Γ₂ := ⟨hx1, this ▸ hΓ₂.right_mem⟩
          rwa [hΓi] at this
      exact hzH (hxz ▸ hxH)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hH.isPreconnected Γ₁ _ hΓ₁.isClosed
      (hΓ₂.isClosed.union (hTc _).isClosed) hcov hint with h | h
    · have : B ∈ Γ (k + 1) := hΓu ▸ Or.inl (h hBH)
      obtain ⟨j, -, hj⟩ := mem_iUnion₂.mp this
      exact hB j hj
    · rcases h hy0 with h | h
      · have : y 0 ∈ Γ₁ ∩ Γ₂ := ⟨hΓ₁.left_mem, h⟩
        rw [hΓi] at this
        exact hzy this.symm
      · rcases h with h | h
        · exact hy0B h
        · obtain ⟨j, hj⟩ := mem_iUnion.mp h
          exact disjoint_left.mp (hdisj 0 _ (by omega)) (harc 0).left_mem hj
  obtain ⟨φ, hφ, hφr, hφ0, hφ1⟩ := (isIrreducibleConnected_iff_arc hy0B).mp
    ⟨hτc, hτconn, Or.inr (mem_iUnion.mpr ⟨0, (harc 0).left_mem⟩), mem_insert _ _, hirr⟩
  exact ⟨hy0B, φ, hφ, hφr, hφ0, hφ1⟩

/-- **Limit arcs, with trimming** (Moore's \"first point\" construction in the proof of Theorem
32). If the arcs `βₙ` from `xₙ` to `xₙ₊₁` are disjoint unless consecutive, `x₀ ∉ β₁`, and they
miss `B` and converge to `B`, then `B + β₀ + β₁ + ⋯` contains an arc from `x₀` to `B`: each `βₙ`
is cut down to its piece `εₙ` from `yₙ` to its first point `yₙ₊₁` on `βₙ₊₁`. -/
theorem exists_tarc_of_seq [TopologicalSpace.MetrizableSpace X] {x : ℕ → X} {β : ℕ → Set X}
    {B : X} (harc : ∀ n, TArc (x n) (x (n + 1)) (β n))
    (hdisj : ∀ n m, n + 2 ≤ m → Disjoint (β n) (β m)) (hx0 : x 0 ∉ β 1)
    (hB : ∀ n, B ∉ β n) (hlim : ∀ U ∈ 𝓝 B, ∀ᶠ n in atTop, β n ⊆ U) :
    ∃ τ ⊆ insert B (⋃ n, β n), TArc (x 0) B τ := by
  have step : ∀ n (y : X), y ∈ β n ∧ y ∉ β (n + 1) → ∃ y' : X,
      (y' ∈ β (n + 1) ∧ y' ∉ β (n + 1 + 1)) ∧ ∃ ε ⊆ β n, TArc y y' ε ∧ ε ∩ β (n + 1) = {y'} := by
    rintro n y ⟨hy, hy'⟩
    have hyx : y ≠ x (n + 1) := fun e => hy' (e ▸ (harc (n + 1)).left_mem)
    obtain ⟨σ', hσ'β, hσ'⟩ := (harc n).exists_sub hy (harc n).right_mem hyx
    obtain ⟨y', hy'Z, ε, hεσ, hε, hεZ⟩ := hσ'.first_point (harc (n + 1)).isClosed
      ⟨x (n + 1), hσ'.right_mem, (harc (n + 1)).left_mem⟩ hy'
    refine ⟨y', ⟨hy'Z, fun h => disjoint_left.mp (hdisj n (n + 1 + 1) le_rfl)
      (hσ'β (hεσ hε.right_mem)) h⟩, ε, hεσ.trans hσ'β, hε, hεZ⟩
  choose! g hg using step
  let Y : ℕ → X := fun n => Nat.rec (x 0) (fun k yk => g k yk) n
  have hY : ∀ n, Y n ∈ β n ∧ Y n ∉ β (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨(harc 0).left_mem, hx0⟩
    | succ n ih => exact (hg n (Y n) ih).1
  choose! e heβ he heZ using fun n => (hg n (Y n) (hY n)).2
  have hY1 : ∀ n, Y (n + 1) = g n (Y n) := fun n => rfl
  have harc' : ∀ n, TArc (Y n) (Y (n + 1)) (e n) := fun n => by rw [hY1]; exact he n
  refine ⟨_, ?_, tarc_of_seq (y := Y) (ε := e) harc' (fun n => ?_) (fun n m hnm => ?_)
    (fun n h => hB n (heβ n h)) (fun U hU => (hlim U hU).mono fun n hn => (heβ n).trans hn)⟩
  · rintro z (rfl | hz)
    · exact mem_insert _ _
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact Or.inr (mem_iUnion.mpr ⟨n, heβ n hn⟩)
  · apply subset_antisymm
    · rintro z ⟨hz1, hz2⟩
      have : z ∈ e n ∩ β (n + 1) := ⟨hz1, heβ (n + 1) hz2⟩
      rwa [heZ n, ← hY1] at this
    · rintro z rfl
      exact ⟨(harc' n).right_mem, (harc' (n + 1)).left_mem⟩
  · exact (hdisj n m hnm).mono (heβ n) (heβ m)

end Gen

end HPC.Moore
