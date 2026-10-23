import HPC.Fold.Theorem4
import HPC.Fold.T9Blocks

/-!
# Batch 86: the end-link clause of Theorem 3 in the cases that are settled

`theorem3_end` (`HPC/Fold/Theorem4.lean`) stays open. Proved here, with its exact conclusion:

* `theorem3_end_of_injective`: any injective block map with `β i = 0` (every block one link)
  satisfies the three-link clause and the end-link clause;
* `theorem3_end_at_first` / `theorem3_end_at_last`: hence the clause holds when the basepoint is
  an end link (`β = id`, resp. the reversal) — batch 82's remark, now in Lean;
* `theorem3_end_of_three`: it holds when `D` has exactly three links (then "the first three" and
  "the last three" links are all of `D`), from `theorem3`.
-/

namespace HPC.Fold

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- An injective block map (every block a single link) satisfies the three-link clause and the
end-link clause of `theorem3_end`. -/
theorem theorem3_end_of_injective {n k : ℕ} (hk : 3 ≤ k) {E : Chain X n} {D : Chain X k}
    (hcr : E.IsCrookedIn' D) {q : ℕ} (β' : Fin n → Fin q) (hβ' : IsBlockMap β')
    (hinj : Function.Injective β') :
    (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  have hsingle : ∀ (t : Fin n) (S : Set X), E.link t ⊆ S → (E.ofBlocks β' hβ').link (β' t) ⊆ S :=
    fun t S h => ofBlocks_link_subset E hβ' (β' t) S fun t' ht' => by
      rw [hinj ht']; exact h
  refine ⟨fun u => ?_, fun t _ => ⟨fun hmeet => ?_, fun hmeet => ?_⟩⟩
  · obtain ⟨t, rfl⟩ := hβ'.surj u
    obtain ⟨s, hs⟩ := hcr.1 t
    exact ⟨s.val, hsingle t _ (hs.trans (link_subset_unionRange D s le_rfl (by omega)))⟩
  · obtain ⟨s, hs⟩ := hcr.1 t
    obtain ⟨x, hx1, hx2⟩ := hmeet
    have hadj := (D.adjacent_iff s ⟨0, by omega⟩).mp ⟨x, hs hx1, hx2⟩
    simp only at hadj
    exact hsingle t _ (hs.trans (link_subset_unionRange D s (Nat.zero_le _) (by omega)))
  · obtain ⟨s, hs⟩ := hcr.1 t
    obtain ⟨x, hx1, hx2⟩ := hmeet
    have hadj := (D.adjacent_iff s ⟨k - 1, by omega⟩).mp ⟨x, hs hx1, hx2⟩
    simp only at hadj
    have := s.isLt
    exact hsingle t _ (hs.trans (link_subset_unionRange D s (by omega) (by omega)))

/-- **`theorem3_end` at the first link**: basepoint `i = 0`, with `β = id`. -/
theorem theorem3_end_at_first {n k : ℕ} (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) (hi : i.val = 0) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  have hβ : IsBlockMap (id : Fin n → Fin n) :=
    ⟨Function.surjective_id, fun a b h => by simp only [id]; omega⟩
  obtain ⟨h1, h2⟩ := theorem3_end_of_injective hk hcr id hβ Function.injective_id
  exact ⟨n, id, hβ, hi, h1, h2⟩

/-- **`theorem3_end` at the last link**: basepoint `i = n - 1`, with the reversal. -/
theorem theorem3_end_at_last {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) (hi : i.val = n - 1) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  have hβ : IsBlockMap (Fin.rev : Fin n → Fin n) :=
    ⟨Fin.rev_surjective, fun a b h => by simp only [Fin.val_rev]; omega⟩
  obtain ⟨h1, h2⟩ := theorem3_end_of_injective hk hcr Fin.rev hβ Fin.rev_injective
  exact ⟨n, Fin.rev, hβ, by simp only [Fin.val_rev]; omega, h1, h2⟩

/-- **`theorem3_end` for a three-link `D`**: the end-link clause is then implied by `theorem3`. -/
theorem theorem3_end_of_three {n k : ℕ} (hn : 0 < n) (hk : k = 3)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  subst hk
  obtain ⟨q, β', hβ', h0, hblk⟩ := theorem3 hn hcr i
  have hall : ∀ u, (E.ofBlocks β' hβ').link u ⊆ D.unionRange 0 3 := fun u =>
    ofBlocks_link_subset E hβ' u _ fun t _ => by
      obtain ⟨s, hs⟩ := hcr.1 t
      exact hs.trans (link_subset_unionRange D s (Nat.zero_le _) (by have := s.isLt; omega))
  exact ⟨q, β', hβ', h0, hblk, fun t _ => ⟨fun _ => hall _, fun _ => hall _⟩⟩

end HPC.Fold
