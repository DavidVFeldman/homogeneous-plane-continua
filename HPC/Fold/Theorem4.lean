import HPC.Fold.Open
import HPC.Fold.Splice78
import HPC.Fold.Theorem3Bing

/-!
# Bing 1948, Theorem 4 (block reading, three-link form), and the end-link clause of Theorem 3

Batch 78. `theorem4` is proved (its construction lives in `HPC.Fold.Splice78`);
`theorem3_end` is proved in batch 123 from `HPC.Fold.theorem3_bing` (`HPC/Fold/Theorem3Bing.lean`).

Conventions: `E` is the fine chain (Bing's `D`), `D` the coarse chain (Bing's `E`); a
consolidation is `E.ofBlocks β hβ`; "in the sum of three consecutive links of `D`" is
`⊆ D.unionRange j 3`.
-/

namespace HPC.Fold

open HPC.Chain

/-- **Bing 1948, Theorem 3 with the end-link clause** (block reading, three-link form). In
addition to the conclusion of `theorem3`: if an end link of `E` meets the first link of `D`,
the block containing it lies in the first three links of `D`; if it meets the last link of `D`,
in the last three.

Proved in batch 123 from `Theorem3Bing` (`theorem3_end_of_bing`). The hypothesis `hn : 0 < n` is
part of the commissioned statement but is not needed by the proof. -/
theorem theorem3_end {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) :=
  theorem3_end_of_bing hk hcr i

/-- **Bing 1948, Theorem 4** (block reading, three-link form). If some link of `E` between `r`
and `s` meets the first link of `D` and some link between `r` and `s` meets the last, then `E`
has a block consolidation, every block in three consecutive links of `D`, in which `E.link r`
opens the first block and `E.link s` closes the last.

The hypothesis `hn : 0 < n` is part of the commissioned statement but is not needed by the
proof (it follows from the existence of `r : Fin n`). -/
theorem theorem4 {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  obtain ⟨hl, hrl, hls, hlm⟩ := hlow
  obtain ⟨hh, hrh, hhs, hhm⟩ := hhigh
  have hρl : (hcr.1.minIdx hl).val ≤ 1 := by
    have := minIdx_near_of_inter hcr.1 hl ⟨0, by omega⟩ hlm
    simp only at this; omega
  have hρh : k - 2 ≤ (hcr.1.minIdx hh).val := by
    have := minIdx_near_of_inter hcr.1 hh ⟨k - 1, by omega⟩ hhm
    have := (hcr.1.minIdx hh).isLt
    simp only at *; omega
  have hρσ : ∀ t, (hcr.1.minIdx t).val ≤ (hcr.1.maxIdx t).val := fun t =>
    minIdx_le hcr.1 t (maxIdx_subset hcr.1 t)
  by_cases hk7 : 7 ≤ k
  · rcases lt_trichotomy hl hh with h1 | h1 | h1
    · exact B78.theorem4_core (by omega) hcr r hl hh s hrl h1 hhs hlm hhm
    · exfalso; rw [h1] at hρl; omega
    · -- the low link comes second: reverse the coarse chain
      have hrev0 : Fin.rev (⟨0, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
        Fin.ext (by simp [Fin.val_rev])
      have hrev1 : Fin.rev (⟨k - 1, by omega⟩ : Fin k) = ⟨0, by omega⟩ :=
        Fin.ext (by simp [Fin.val_rev]; omega)
      have hlm' : (E.link hh ∩ D.reverse.link ⟨0, by omega⟩).Nonempty := by
        rw [reverse_link, hrev0]; exact hhm
      have hhm' : (E.link hl ∩ D.reverse.link ⟨k - 1, by omega⟩).Nonempty := by
        rw [reverse_link, hrev1]; exact hlm
      obtain ⟨q, β', hβ', h0, hq, hblk⟩ :=
        B78.theorem4_core (by omega) hcr.reverse_right r hh hl s hrh h1 hls hlm' hhm'
      exact ⟨q, β', hβ', h0, hq, fun u => by
        obtain ⟨j, hj⟩ := hblk u
        exact ⟨k - 3 - j, hj.trans (B78.unionRange_reverse D j)⟩⟩
  · -- at most six coarse links: every link lies in the first three or in the last three
    have hA : ∀ t, (hcr.1.minIdx t).val ≤ 2 → E.link t ⊆ D.unionRange 0 3 := fun t ht =>
      B78.link_sub_of_level hcr.1 t 0 (Or.inl ⟨by omega, by omega⟩)
    have hB : ∀ t, k - 3 ≤ (hcr.1.maxIdx t).val → E.link t ⊆ D.unionRange (k - 3) 3 :=
      fun t ht => B78.link_sub_of_level hcr.1 t (k - 3)
        (Or.inr ⟨by omega, by have := (hcr.1.maxIdx t).isLt; omega⟩)
    by_cases hk3 : k = 3
    · subst hk3
      refine B78.assemble r s (fun _ => 0) (fun _ _ _ => by simp) rfl (fun _ => le_rfl) ?_
      intro v
      exact ⟨0, fun t _ => hA t (by have := (hcr.1.minIdx t).isLt; omega)⟩
    · have hAB : ∀ t, (hcr.1.minIdx t).val ≤ 2 ∨ k - 3 ≤ (hcr.1.maxIdx t).val := by
        intro t; have := hρσ t; omega
      have hBA : ∀ t, k - 3 ≤ (hcr.1.maxIdx t).val ∨ (hcr.1.minIdx t).val ≤ 2 :=
        fun t => (hAB t).symm
      have hAl : (hcr.1.minIdx hl).val ≤ 2 := by omega
      have hBh : k - 3 ≤ (hcr.1.maxIdx hh).val := by have := hρσ hh; omega
      have hne : hl ≠ hh := by intro h; rw [h] at hρl; omega
      have hrs' : r < s := by
        rw [Fin.lt_def]
        rcases Fin.lt_or_lt_of_ne hne with h | h <;> rw [Fin.lt_def] at h <;>
          rw [Fin.le_def] at hrl hls hrh hhs <;> omega
      by_cases hAr : (hcr.1.minIdx r).val ≤ 2
      · by_cases hBs : k - 3 ≤ (hcr.1.maxIdx s).val
        · exact B78.two_window _ _ 0 (k - 3) hAB hA hB r s hrs' hAr (Or.inl hBs)
        · have hAs : (hcr.1.minIdx s).val ≤ 2 := (hAB s).resolve_right hBs
          rcases eq_or_lt_of_le hrh with h | h
          · -- the high link is `r` itself
            rw [← h] at hBh
            exact B78.two_window _ _ (k - 3) 0 hBA hB hA r s hrs' hBh (Or.inl hAs)
          · have hhs' : hh < s := by
              rcases eq_or_lt_of_le hhs with h' | h'
              · exact absurd (h' ▸ hBh) hBs
              · exact h'
            exact B78.two_window _ _ 0 (k - 3) hAB hA hB r s hrs' hAr
              (Or.inr ⟨hAs, hh, h, hhs', hBh⟩)
      · have hBr : k - 3 ≤ (hcr.1.maxIdx r).val := (hAB r).resolve_left hAr
        by_cases hAs : (hcr.1.minIdx s).val ≤ 2
        · exact B78.two_window _ _ (k - 3) 0 hBA hB hA r s hrs' hBr (Or.inl hAs)
        · have hBs : k - 3 ≤ (hcr.1.maxIdx s).val := (hAB s).resolve_left hAs
          rcases eq_or_lt_of_le hrl with h | h
          · rw [← h] at hAl; exact absurd hAl hAr
          · have hls' : hl < s := by
              rcases eq_or_lt_of_le hls with h' | h'
              · exact absurd (h' ▸ hAl) hAs
              · exact h'
            exact B78.two_window _ _ (k - 3) 0 hBA hB hA r s hrs' hBr
              (Or.inr ⟨hBs, hl, h, hls', hAl⟩)

end HPC.Fold
