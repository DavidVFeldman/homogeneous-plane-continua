import HPC.BJ59.Thm9E
import HPC.BJ59.BJ59B

/-!
# Batch 200, §5: Bing–Jones's two simplifications (Theorem 9, pp. 179–180)

* `bj9_core`: from two chains with the same number of links, each link with a private point, to a
  pair `D′`, `E′` matched by index (the second simplification, `bj9_Dside` and `bj9_Eside`);
* `bj9_base` (verbatim): the first simplification (consolidating `D` along `H`) followed by
  `bj9_core`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Base

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **The second simplification**, with private points on both sides. -/
theorem bj9_core {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {m : ℕ}
    (hm : 0 < m) (D : Chain X m) (E : Chain Y m) (hD : IsBJChain D)
    (hDP : P ⊆ D.union) (hEQ : Q ⊆ E.union)
    (hDpr : ∀ i, ∃ p ∈ P ∩ D.link i, ∀ j, j ≠ i → p ∉ closure (D.link j))
    (hEpr : ∀ i, ∃ q ∈ Q ∩ E.link i, ∀ j, j ≠ i → q ∉ closure (E.link j)) :
    ∃ (N : ℕ) (D' : Chain X N) (E' : Chain Y N), IsBJChain D' ∧ IsBJChain E' ∧
      P ⊆ D'.union ∧ Q ⊆ E'.union ∧
      (∀ j, ∃ p ∈ P ∩ D'.link j, ∀ j', j' ≠ j → p ∉ closure (D'.link j')) ∧
      (∀ j, ∃ q ∈ Q ∩ E'.link j, ∀ j', j' ≠ j → q ∉ closure (E'.link j')) ∧
      ∀ (i : Fin m) (j : Fin N) (p : X), p ∈ P → p ∈ D.link i → p ∈ D'.link j →
        closure (E'.link j) ⊆ E.link i := by
  obtain ⟨D1, hD1bj, hPD1, hD1P, hD1A⟩ := bj9_Dside hP hm D hD hDP hDpr
  obtain ⟨E1, hE1bj, hQE1, hE1Q, hE1A⟩ := bj9_Eside hQ hm E hEQ hEpr
  obtain ⟨D2, hD2bj, hPD2, hD2s, hD2pr⟩ := exists_privatePoint_shrink hP.1.1 hP.2.2 D1 hD1bj hPD1
    (fun j => (hD1P j))
  obtain ⟨E2, hE2bj, hQE2, hE2s, hE2pr⟩ := exists_privatePoint_shrink hQ.1.1 hQ.2.2 E1 hE1bj hQE1
    (fun j => (hE1Q j))
  refine ⟨4 * m - 3, D2, E2, hD2bj, hE2bj, hPD2, hQE2, hD2pr, hE2pr, ?_⟩
  intro i j p hp hpi hpj
  have hA := hD1A j i.val p hp (mem_linkN_of_mem D i hpi) (hD2s j hpj)
  have h1 := hE1A j i.val hA
  rw [E.linkN_of_lt i.isLt] at h1
  exact (closure_mono (hE2s j)).trans h1

/-- **Bing–Jones's two simplifications** (pp. 179–180), as one lemma: a pair of chains with the
same number of links, matched by index, whose correspondence refines `H` with closures. -/
theorem bj9_base {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ (N : ℕ) (D' : Chain X N) (E' : Chain Y N), IsBJChain D' ∧ IsBJChain E' ∧
      P ⊆ D'.union ∧ (∀ j, (D'.link j ∩ P).Nonempty) ∧
      Q ⊆ E'.union ∧ (∀ j, (E'.link j ∩ Q).Nonempty) ∧
      (∀ j, ∃ p ∈ P ∩ D'.link j, ∀ j', j' ≠ j → p ∉ closure (D'.link j')) ∧
      (∀ j, ∃ q ∈ Q ∩ E'.link j, ∀ j', j' ≠ j → q ∉ closure (E'.link j')) ∧
      ∀ (i : Fin n) (j : Fin N) (p : X), p ∈ P → p ∈ D.link i → p ∈ D'.link j →
        closure (E'.link j) ⊆ E.link (H i) := by
  classical
  have hHs : Function.Surjective H := fun j => by
    obtain ⟨i, hi, -⟩ := hHo j; exact ⟨i, hi⟩
  have hPne : P.Nonempty := hP.2.2.nonempty
  obtain ⟨q0, hq0⟩ := hQ.2.2.nonempty
  obtain ⟨j0, -⟩ := mem_iUnion.1 (hEQ hq0)
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) j0.isLt
  obtain ⟨D'', hD''bj, hPD'', -, hD''⟩ := exists_consolidation hP.1.1.2.isPreconnected hPne D hD
    hDP hDp H hH hHs
  -- private points of the consolidation
  have hD''pr : ∀ j, ∃ p ∈ P ∩ D''.link j, ∀ j', j' ≠ j → p ∉ closure (D''.link j') := by
    intro j
    obtain ⟨i, hi, p, ⟨hpP, hpi⟩, hpr⟩ := hHo j
    refine ⟨p, ⟨hpP, ?_⟩, ?_⟩
    · rw [hD'' j]; exact mem_iUnion₂.2 ⟨i, congrArg Fin.val hi, hpi⟩
    · intro j' hj' hpc
      rw [hD'' j', closure_biUnion_links D (fun a => (H a).val = j'.val)] at hpc
      obtain ⟨i', hi', hpc⟩ := mem_iUnion₂.1 hpc
      refine hpr i' ?_ hpc
      rintro rfl
      exact hj' (Fin.ext (by rw [← hi', hi]))
  obtain ⟨E0, hE0bj, hQE0, hE0s, hE0pr⟩ := exists_privatePoint_shrink hQ.1.1 hQ.2.2 E hE hEQ hEq
  obtain ⟨N, D', E', hD'bj, hE'bj, hPD', hQE', hD'pr, hE'pr, hcl⟩ :=
    bj9_core hP hQ hm D'' E0 hD''bj hPD'' hQE0 hD''pr hE0pr
  refine ⟨N, D', E', hD'bj, hE'bj, hPD', fun j => ?_, hQE', fun j => ?_, hD'pr, hE'pr, ?_⟩
  · obtain ⟨p, ⟨hpP, hpj⟩, -⟩ := hD'pr j; exact ⟨p, hpj, hpP⟩
  · obtain ⟨q, ⟨hqQ, hqj⟩, -⟩ := hE'pr j; exact ⟨q, hqj, hqQ⟩
  · intro i j p hp hpi hpj
    have hp'' : p ∈ D''.link (H i) := by
      rw [hD'' (H i)]; exact mem_iUnion₂.2 ⟨i, rfl, hpi⟩
    exact (hcl (H i) j p hp hp'' hpj).trans (hE0s (H i))

end Base

end HPC.BJ59
