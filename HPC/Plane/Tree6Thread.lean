import HPC.Plane.Tree6Cut

/-!
# Batch 118, auxiliary: chains of simple arcs

* an open chain of simple arcs `A 0, …, A (m-1)` (`A i` from `P i` to `P (i+1)`, consecutive ones
  meeting only at their common end, others disjoint) is a simple arc (`chain_sarc`);
* a closed chain of `m ≥ 3` such arcs is a simple closed polygon (`closed_chain_polygon`).
-/

namespace HPC.Plane

open Set Metric

/-- **An open chain of simple arcs is a simple arc.** -/
theorem chain_sarc (A : ℕ → Set Pt) (P : ℕ → Pt) (m : ℕ) (hm : 1 ≤ m)
    (harc : ∀ i < m, ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = P i ∧ v (n - 1) = P (i + 1) ∧
      A i = vpath v n)
    (hcons : ∀ i, i + 1 < m → A i ∩ A (i + 1) = {P (i + 1)})
    (hdis : ∀ i j, i + 1 < j → j < m → Disjoint (A i) (A j)) :
    ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = P 0 ∧ v (n - 1) = P m ∧
      vpath v n = ⋃ i ∈ Finset.range m, A i := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨v, n, hv, h0, h1, hA⟩ := harc 0 (by omega)
    exact ⟨v, n, hv, h0, h1, by simp [hA]⟩
  | succ m hm ih =>
    obtain ⟨v, n, hv, h0, h1, hU⟩ := ih (fun i hi => harc i (by omega))
      (fun i hi => hcons i (by omega)) (fun i j hij hj => hdis i j hij (by omega))
    obtain ⟨u, k, hu, hu0, hu1, hA⟩ := harc m (by omega)
    have hvu : v (n - 1) = u 0 := by rw [h1, hu0]
    have hmeet : vpath v n ∩ vpath u k = {u 0} := by
      apply subset_antisymm
      · rintro y ⟨hy1, hy2⟩
        rw [hU] at hy1
        rw [← hA] at hy2
        simp only [mem_iUnion, Finset.mem_range] at hy1
        obtain ⟨i, hi, hyi⟩ := hy1
        by_cases him : i + 1 = m
        · have := hcons i (by omega)
          rw [him] at this
          rw [hu0, ← him]
          rw [← him] at hy2
          rw [← him] at this
          exact (this ▸ (⟨hyi, hy2⟩ : y ∈ A i ∩ A (i + 1)))
        · exact absurd hy2 ((hdis i m (by omega) (by omega)).notMem_of_mem_left hyi)
      · rintro y rfl
        exact ⟨hvu ▸ hv.end_mem, hu.start_mem⟩
    refine ⟨vcat v n u, n + k - 1, hv.concat hu hvu hmeet, ?_, ?_, ?_⟩
    · simp [vcat, show 0 < n by have := hv.1; omega, h0]
    · have hk := hu.1
      have hn := hv.1
      simp only [vcat, show ¬ (n + k - 1 - 1 < n) by omega, if_false]
      rw [show n + k - 1 - 1 - (n - 1) = k - 1 by omega, hu1]
    · rw [vpath_vcat (by have := hv.1; omega) (by have := hu.1; omega) hvu, hU, ← hA,
        Finset.range_add_one, Finset.set_biUnion_insert, union_comm]

/-- **A closed chain of `m ≥ 3` simple arcs is a simple closed polygon.** -/
theorem closed_chain_polygon (A : ℕ → Set Pt) (P : ℕ → Pt) (m : ℕ) (hm : 3 ≤ m)
    (hP : P m = P 0)
    (harc : ∀ i < m, ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = P i ∧ v (n - 1) = P (i + 1) ∧
      A i = vpath v n)
    (hcons : ∀ i, i + 1 < m → A i ∩ A (i + 1) = {P (i + 1)})
    (hwrap : A (m - 1) ∩ A 0 = {P 0})
    (hdis : ∀ i j, i + 1 < j → j < m → ¬ (i = 0 ∧ j = m - 1) → Disjoint (A i) (A j)) :
    IsSimpleClosedPolygon (⋃ i ∈ Finset.range m, A i) := by
  obtain ⟨v, n, hv, h0, h1, hU⟩ := chain_sarc A P (m - 1) (by omega)
    (fun i hi => harc i (by omega)) (fun i hi => hcons i (by omega))
    (fun i j hij hj => hdis i j hij (by omega) (by omega))
  obtain ⟨u, k, hu, hu0, hu1, hA⟩ := harc (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega, hP] at hu1
  have hvu : v (n - 1) = u 0 := by rw [h1, hu0]
  have huv : u (k - 1) = v 0 := by rw [hu1, h0]
  have hmeet : vpath v n ∩ vpath u k = {v 0, u 0} := by
    apply subset_antisymm
    · rintro y ⟨hy1, hy2⟩
      rw [hU] at hy1
      rw [← hA] at hy2
      simp only [mem_iUnion, Finset.mem_range] at hy1
      obtain ⟨i, hi, hyi⟩ := hy1
      by_cases hi0 : i = 0
      · subst hi0
        have : y ∈ A (m - 1) ∩ A 0 := ⟨hy2, hyi⟩
        rw [hwrap] at this
        exact Or.inl (h0 ▸ this)
      · by_cases him : i + 1 = m - 1
        · have := hcons i (by omega)
          have hy : y ∈ A i ∩ A (i + 1) := ⟨hyi, him ▸ hy2⟩
          rw [this, him] at hy
          exact Or.inr (hu0 ▸ hy)
        · exact absurd hy2 ((hdis i (m - 1) (by omega) (by omega) (by omega)).notMem_of_mem_left
            hyi)
    · rintro y (rfl | rfl)
      · exact ⟨hv.start_mem, huv ▸ hu.end_mem⟩
      · exact ⟨hvu ▸ hv.end_mem, hu.start_mem⟩
  have := isSimpleClosedPolygon_of_two_arcs hv hu hvu huv hmeet
  rwa [hU, ← hA, union_comm, ← Finset.set_biUnion_insert, ← Finset.range_add_one,
    show m - 1 + 1 = m by omega] at this

end HPC.Plane
