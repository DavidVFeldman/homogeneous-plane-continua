import HPC.Fold.Theorem4
import HPC.Fold.Pair79Assemble

/-!
# Bing 1948, Theorem 4 with two-link basepoints

Skeleton for batch 79 (saved as `HPC/Fold/Theorem4Pair.lean`, imported by the root `HPC.lean`);
the statement is the skeleton's, unchanged.

A point of a chain lies in at most two links, and those are adjacent. Theorem 13 needs the chain
`F` of Theorem 4 to be a chain *from `R` to `S`* (Bing p. 729: `R` in the first link and in no
other), which by `Q78.isFrom_ofBlocks_iff` means every fine link containing `R` is in block `0`.
So Theorem 4 is needed with a basepoint that is a pair of adjacent links at each end.

*Batch 79:* proved, statement unchanged (three-link windows at every block, the two end blocks
included). The main case (`B79.theorem4_pair_core`, at least six coarse links) splices a prefix
fold and a suffix fold, each of which sends both links of its basepoint pair to its first time
(`B79.pair_prefix_fold`); the fold is read on the least coarse indices or on the greatest,
whichever the exclusion `B79.pair_exclusion` allows. Four and five coarse links are two windows
(`B79.pair_windows`), three coarse links one block.
-/

namespace HPC.Fold

open HPC.Chain

/-- **Theorem 4, two-link basepoints.** As `theorem4`, with the first block containing both
`E.link r` and `E.link (r+1)` and the last block containing both `E.link (s-1)` and `E.link s`.
The degenerate single-link cases are `theorem4`. -/
theorem theorem4_pair {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r r' s' s : Fin n)
    (hr : r'.val = r.val + 1) (hs : s.val = s'.val + 1) (hmid : r' ≤ s')
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' r').val = 0 ∧ (β' s').val = q - 1 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  obtain ⟨hl, hrl, hls, hlm⟩ := hlow
  obtain ⟨hh, hrh, hhs, hhm⟩ := hhigh
  have hρl : (hcr.1.minIdx hl).val ≤ 1 := by
    have := minIdx_near_of_inter hcr.1 hl ⟨0, by omega⟩ hlm
    simp only at this; omega
  have hσh : k - 2 ≤ (hcr.1.maxIdx hh).val := by
    have := minIdx_near_of_inter hcr.1 hh ⟨k - 1, by omega⟩ hhm
    have := minIdx_le hcr.1 hh (maxIdx_subset hcr.1 hh)
    rw [Fin.le_def] at this
    simp only at *; omega
  have hρσ : ∀ t, (hcr.1.minIdx t).val ≤ (hcr.1.maxIdx t).val := fun t =>
    minIdx_le hcr.1 t (maxIdx_subset hcr.1 t)
  have hwid : ∀ t, (hcr.1.maxIdx t).val ≤ (hcr.1.minIdx t).val + 1 := fun t => by
    have := subset_adjacent_of_subset hcr.1 t (minIdx_subset hcr.1 t) (maxIdx_subset hcr.1 t)
    omega
  have hA : ∀ t, (hcr.1.minIdx t).val ≤ 2 → E.link t ⊆ D.unionRange 0 3 := fun t ht =>
    B78.link_sub_of_level hcr.1 t 0 (Or.inl ⟨by omega, by omega⟩)
  rw [Fin.le_def] at hrl hls hrh hhs hmid
  have hsn := s.isLt
  by_cases hk3 : k = 3
  · -- one block
    subst hk3
    refine B79.assemble_pair r r' s' s (fun _ => 0) (fun _ _ _ => by simp) rfl rfl
      (fun _ => le_rfl) rfl ?_
    intro v
    exact ⟨0, fun t _ => hA t (by have := (hcr.1.minIdx t).isLt; omega)⟩
  -- at least four coarse links: `r' < s'`
  have hmid' : r' < s' := by
    rw [Fin.lt_def]
    rcases lt_or_eq_of_le hmid with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hbtw, -, -⟩ := hcr.2 ⟨0, by omega⟩ ⟨k - 1, by omega⟩
        (by simp only; omega) hl hh hlm hhm
      rcases hbtw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp only [gt_iff_lt, Fin.lt_def] at h1 h2 h3 <;>
        omega
  by_cases hk6 : 6 ≤ k
  · rcases lt_trichotomy hl hh with h1 | h1 | h1
    · exact B79.theorem4_pair_core (by omega) hcr r r' s' s hr hs hl hh
        (Fin.le_def.mpr hrl) h1 (Fin.le_def.mpr hhs) hlm hhm
    · exfalso; subst h1; have := hwid hl; omega
    · -- the low link comes second: reverse the coarse chain
      have hrev0 : Fin.rev (⟨0, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
        Fin.ext (by simp [Fin.val_rev])
      have hrev1 : Fin.rev (⟨k - 1, by omega⟩ : Fin k) = ⟨0, by omega⟩ :=
        Fin.ext (by simp [Fin.val_rev]; omega)
      have hlm' : (E.link hh ∩ D.reverse.link ⟨0, by omega⟩).Nonempty := by
        rw [reverse_link, hrev0]; exact hhm
      have hhm' : (E.link hl ∩ D.reverse.link ⟨k - 1, by omega⟩).Nonempty := by
        rw [reverse_link, hrev1]; exact hlm
      obtain ⟨q, β', hβ', h0, h0', hq', hq, hblk⟩ :=
        B79.theorem4_pair_core (by omega) hcr.reverse_right r r' s' s hr hs hh hl
          (Fin.le_def.mpr hrh) h1 (Fin.le_def.mpr hls) hlm' hhm'
      exact ⟨q, β', hβ', h0, h0', hq', hq, fun u => by
        obtain ⟨j, hj⟩ := hblk u
        exact ⟨k - 3 - j, hj.trans (B78.unionRange_reverse D j)⟩⟩
  · -- four or five coarse links: every pair lies in the first three or in the last three
    have hB : ∀ t, k - 3 ≤ (hcr.1.maxIdx t).val → E.link t ⊆ D.unionRange (k - 3) 3 :=
      fun t ht => B78.link_sub_of_level hcr.1 t (k - 3)
        (Or.inr ⟨by omega, by have := (hcr.1.maxIdx t).isLt; omega⟩)
    have hAB : ∀ t, (hcr.1.minIdx t).val ≤ 2 ∨ k - 3 ≤ (hcr.1.maxIdx t).val := by
      intro t; have := hρσ t; omega
    have hBA : ∀ t, k - 3 ≤ (hcr.1.maxIdx t).val ∨ (hcr.1.minIdx t).val ≤ 2 :=
      fun t => (hAB t).symm
    have lip2 : ∀ t t' : Fin n, t'.val = t.val + 1 →
        (hcr.1.minIdx t').val ≤ (hcr.1.minIdx t).val + 1 ∧
        (hcr.1.minIdx t).val ≤ (hcr.1.minIdx t').val + 1 ∧
        (hcr.1.maxIdx t').val ≤ (hcr.1.maxIdx t).val + 1 ∧
        (hcr.1.maxIdx t).val ≤ (hcr.1.maxIdx t').val + 1 := by
      intro t t' h
      have h1 := minIdx_lip hcr.1 t t' h
      have h2 := maxIdx_lip hcr.1 t t' h
      omega
    obtain ⟨a1, a2, a3, a4⟩ := lip2 r r' hr
    obtain ⟨b1, b2, b3, b4⟩ := lip2 s' s hs
    have w1 := hρσ r; have w2 := hρσ r'; have w3 := hρσ s'; have w4 := hρσ s
    have hmid'' : r'.val < s'.val := hmid'
    clear lip2 hlm hhm
    by_cases c1 : ((hcr.1.minIdx r).val ≤ 2 ∧ (hcr.1.minIdx r').val ≤ 2) ∧
        (k - 3 ≤ (hcr.1.maxIdx s').val ∧ k - 3 ≤ (hcr.1.maxIdx s).val)
    · exact B79.pair_windows _ _ 0 (k - 3) hAB hA hB r r' s' s hr hs hmid' c1.1.1 c1.1.2
        (Or.inl c1.2)
    by_cases c2 : (k - 3 ≤ (hcr.1.maxIdx r).val ∧ k - 3 ≤ (hcr.1.maxIdx r').val) ∧
        ((hcr.1.minIdx s').val ≤ 2 ∧ (hcr.1.minIdx s).val ≤ 2)
    · exact B79.pair_windows _ _ (k - 3) 0 hBA hB hA r r' s' s hr hs hmid' c2.1.1 c2.1.2
        (Or.inl c2.2)
    by_cases hRA : (hcr.1.minIdx r).val ≤ 2 ∧ (hcr.1.minIdx r').val ≤ 2
    · -- both pairs in the first window only: the high link lies strictly between
      have hSA : (hcr.1.minIdx s').val ≤ 2 ∧ (hcr.1.minIdx s).val ≤ 2 := by omega
      have h1 : r'.val < hh.val := by
        by_contra hc
        rcases (show hh.val = r.val ∨ hh.val = r'.val by omega) with e | e
        · rw [show hh = r from Fin.ext e] at hσh; omega
        · rw [show hh = r' from Fin.ext e] at hσh; omega
      have h2 : hh.val < s'.val := by
        by_contra hc
        rcases (show hh.val = s'.val ∨ hh.val = s.val by omega) with e | e
        · rw [show hh = s' from Fin.ext e] at hσh; omega
        · rw [show hh = s from Fin.ext e] at hσh; omega
      exact B79.pair_windows _ _ 0 (k - 3) hAB hA hB r r' s' s hr hs hmid' hRA.1 hRA.2
        (Or.inr ⟨hSA.1, hSA.2, hh, h1, h2, by omega⟩)
    · -- both pairs in the last window only: the low link lies strictly between
      have hRB : k - 3 ≤ (hcr.1.maxIdx r).val ∧ k - 3 ≤ (hcr.1.maxIdx r').val := by omega
      have hSB : k - 3 ≤ (hcr.1.maxIdx s').val ∧ k - 3 ≤ (hcr.1.maxIdx s).val := by omega
      have h1 : r'.val < hl.val := by
        by_contra hc
        rcases (show hl.val = r.val ∨ hl.val = r'.val by omega) with e | e
        · rw [show hl = r from Fin.ext e] at hρl; omega
        · rw [show hl = r' from Fin.ext e] at hρl; omega
      have h2 : hl.val < s'.val := by
        by_contra hc
        rcases (show hl.val = s'.val ∨ hl.val = s.val by omega) with e | e
        · rw [show hl = s' from Fin.ext e] at hρl; omega
        · rw [show hl = s from Fin.ext e] at hρl; omega
      exact B79.pair_windows _ _ (k - 3) 0 hBA hB hA r r' s' s hr hs hmid' hRB.1 hRB.2
        (Or.inr ⟨hSB.1, hSB.2, hl, h1, h2, by omega⟩)

end HPC.Fold
