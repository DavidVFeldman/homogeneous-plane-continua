import HPC.BJ59.Thm10Lib

/-!
# Batch 201: runs of links

Minimal covering runs, the run of links meeting a preconnected set, and the discrete
intermediate value property of chain maps.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Runs

variable {X : Type*} [MetricSpace X]

/-- A nonempty covered set has a covering run from which neither end link can be dropped. -/
theorem exists_minimal_run {n : ℕ} (D : Chain X n) {C : Set X} (hC : C.Nonempty)
    (hcov : C ⊆ D.union) :
    ∃ r s : ℕ, r ≤ s ∧ s < n ∧ C ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ s), D.link j ∧
      ¬ C ⊆ ⋃ (j : Fin n) (_ : r + 1 ≤ j.val ∧ j.val ≤ s), D.link j ∧
      ¬ C ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val + 1 ≤ s), D.link j := by
  classical
  obtain ⟨z, hz⟩ := hC
  obtain ⟨j₀, -⟩ := mem_iUnion.1 (hcov hz)
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  have hex : ∃ d, ∃ r, r + d < n ∧ C ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ r + d), D.link j :=
    ⟨n - 1, 0, by omega, fun x hx => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hx)
      exact mem_iUnion₂.2 ⟨j, ⟨Nat.zero_le _, by omega⟩, hj⟩⟩
  set d := Nat.find hex with hd
  obtain ⟨r, hrn, hrc⟩ := Nat.find_spec hex
  refine ⟨r, r + d, by omega, hrn, hrc, fun h => ?_, fun h => ?_⟩
  · rcases Nat.eq_zero_or_pos d with h0 | h0
    · obtain ⟨j, hj, -⟩ := mem_iUnion₂.1 (h hz)
      omega
    · have := Nat.find_min hex (show d - 1 < d by omega)
      apply this
      refine ⟨r + 1, by omega, fun x hx => ?_⟩
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (h hx)
      exact mem_iUnion₂.2 ⟨j, ⟨hj.1, by omega⟩, hxj⟩
  · rcases Nat.eq_zero_or_pos d with h0 | h0
    · obtain ⟨j, hj, -⟩ := mem_iUnion₂.1 (h hz)
      omega
    · have := Nat.find_min hex (show d - 1 < d by omega)
      apply this
      refine ⟨r, by omega, fun x hx => ?_⟩
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (h hx)
      exact mem_iUnion₂.2 ⟨j, ⟨hj.1, by omega⟩, hxj⟩

/-- The links meeting a nonempty preconnected covered set form a run covering it. -/
theorem exists_run_meeting {N : ℕ} (F : Chain X N) {S : Set X} (hS : IsPreconnected S)
    (hne : S.Nonempty) (hcov : S ⊆ F.union) :
    ∃ t u : ℕ, t ≤ u ∧ u < N ∧
      (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ S).Nonempty) ∧
      S ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k ∧
      ∀ k : Fin N, (F.link k ∩ S).Nonempty → t ≤ k.val ∧ k.val ≤ u := by
  classical
  set I := Finset.univ.filter (fun k : Fin N => (F.link k ∩ S).Nonempty) with hI
  obtain ⟨z, hz⟩ := hne
  obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 (hcov hz)
  have hIne : I.Nonempty := ⟨k₀, by simp [hI]; exact ⟨z, hk₀, hz⟩⟩
  set t := I.min' hIne with ht
  set u := I.max' hIne with hu
  have htI : t ∈ I := I.min'_mem hIne
  have huI : u ∈ I := I.max'_mem hIne
  simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at htI huI
  refine ⟨t.val, u.val, I.min'_le _ (I.max'_mem hIne), u.isLt, fun k hk1 hk2 => ?_,
    fun x hx => ?_, fun k hk => ?_⟩
  · have := meets_between F hS hcov (i := t) (j := u) (by obtain ⟨w, h1, h2⟩ := htI; exact ⟨w, h2, h1⟩)
      (by obtain ⟨w, h1, h2⟩ := huI; exact ⟨w, h2, h1⟩) k (by omega) (by omega)
    obtain ⟨w, h1, h2⟩ := this
    exact ⟨w, h2, h1⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hx)
    have hkI : k ∈ I := by simp [hI]; exact ⟨x, hk, hx⟩
    exact mem_iUnion₂.2 ⟨k, ⟨I.min'_le _ hkI, I.le_max' _ hkI⟩, hk⟩
  · have hkI : k ∈ I := by simp [hI]; exact hk
    exact ⟨I.min'_le _ hkI, I.le_max' _ hkI⟩

end Runs

/-- Discrete intermediate values for a sequence with steps of at most one. -/
theorem exists_eq_of_steps (φ : ℕ → ℕ) (hφ : ∀ k, φ k ≤ φ (k + 1) + 1 ∧ φ (k + 1) ≤ φ k + 1) :
    ∀ (d p v : ℕ), min (φ p) (φ (p + d)) ≤ v → v ≤ max (φ p) (φ (p + d)) →
      ∃ k, p ≤ k ∧ k ≤ p + d ∧ φ k = v := by
  intro d
  induction d with
  | zero => intro p v h1 h2; exact ⟨p, le_rfl, le_rfl, by simp at h1 h2; omega⟩
  | succ d ih =>
    intro p v h1 h2
    by_cases hv : φ p = v
    · exact ⟨p, le_rfl, by omega, hv⟩
    · have h := hφ p
      rw [show p + (d + 1) = p + 1 + d by omega] at h1 h2
      obtain ⟨k, hk1, hk2, hk⟩ := ih (p + 1) v (by omega) (by omega)
      exact ⟨k, by omega, by omega, hk⟩

/-- The image of a run under a chain map is a run. -/
theorem chainMap_ivt {n m : ℕ} {H : Fin n → Fin m} (hH : IsChainMap H) {i i' : Fin n}
    (hii' : i ≤ i') {v : ℕ} (h1 : min (H i).val (H i').val ≤ v)
    (h2 : v ≤ max (H i).val (H i').val) :
    ∃ j : Fin n, i ≤ j ∧ j ≤ i' ∧ (H j).val = v := by
  set φ : ℕ → ℕ := fun k => (H ⟨min k (n - 1), by have := i.isLt; omega⟩).val with hφ
  have hstep : ∀ k, φ k ≤ φ (k + 1) + 1 ∧ φ (k + 1) ≤ φ k + 1 := by
    intro k
    have := hH ⟨min k (n - 1), by have := i.isLt; omega⟩ ⟨min (k + 1) (n - 1),
      by have := i.isLt; omega⟩ (by simp only; omega)
    simp only [hφ]
    omega
  have hφi : ∀ j : Fin n, φ j.val = (H j).val := fun j => by
    simp only [hφ]; congr 3; have := j.isLt; omega
  obtain ⟨k, hk1, hk2, hk⟩ := exists_eq_of_steps φ hstep (i'.val - i.val) i.val v
    (by rw [show i.val + (i'.val - i.val) = i'.val by have : i.val ≤ i'.val := hii'; omega,
      hφi, hφi]; exact h1)
    (by rw [show i.val + (i'.val - i.val) = i'.val by have : i.val ≤ i'.val := hii'; omega,
      hφi, hφi]; exact h2)
  have hkn : k < n := by have := i'.isLt; have : i.val ≤ i'.val := hii'; omega
  refine ⟨⟨k, hkn⟩, show i.val ≤ k from hk1, show k ≤ i'.val by
    have : i.val ≤ i'.val := hii'; omega, ?_⟩
  rw [← hφi ⟨k, hkn⟩]; exact hk

end HPC.BJ59
