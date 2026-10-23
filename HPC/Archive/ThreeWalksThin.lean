import HPC.Archive.MixedThin
import HPC.Fold.LandmarkW

/-!
# The work item of batch 49, on a thin sequence

`unserved_three_walks` (`HPC/Fold/Mixed.lean`) is the statement the branch `L + 4` of span nine now
rests on: a pair of the branch folding onto neither canonical walk folds onto one of the three
walks `w₃`, `w₄`, `w₅`, both arms onto the same one. For a **thin** sequence it is a theorem, and
the first of the three walks always suffices: `unserved_ceiling_thin` and `unserved_valley_thin`
(`HPC/Fold/MixedThin.lean`) give both arms the two announcements the engine of
`HPC/Fold/Leg3Deep.lean` consumes, and `foldsOnto_leg3deep_branch` turns them into a fold onto
`w₃ = L+3 → L+6 → L+1 → L+8`.

So what separates the general model from the thin one, at this branch, is exactly the second and
third walk: in the thin model the left disjunct of `unserved_three_walks` always holds, and in the
general model it does not (`not_unservedLeg3deep`, `HPC/Fold/CrossWitness.lean`). Of the
hypotheses of `unserved_three_walks`, the two `HighAt` clauses and both ends of the band are not
used here.
-/

namespace HPC.Fold

/-- **The work item of the branch `L + 4`, on a thin sequence.** An unserved pair folds onto the
first of the three walks. -/
theorem unserved_three_walks_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)))
    (hnotVee : ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L))) :
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4))) ∨
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 7) (L + 7))
        (leg3Walk' L (L + 9) (L + 7) (L + 2)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 7) (L + 7))
        (leg3Walk' L (L + 9) (L + 7) (L + 2))) ∨
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 7) (L + 4))
        (leg3Walk L (L + 9) (L + 7) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 7) (L + 4))
        (leg3Walk L (L + 9) (L + 7) (L + 4))) := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  obtain ⟨h8G, h8T⟩ := unserved_ceiling_thin ρ σ i L hlip hcr hthin hLb hHb hp hnotLam
  obtain ⟨hvG, hvT⟩ := unserved_valley_thin ρ σ i L hlip hcr hthin hLb hHb hp hnotVee
  exact Or.inl
    ⟨foldsOnto_leg3deep_branch hmG (armG ρ i) (armG_isLip hlip i) L hG0
        (fun j => hLb _) (fun j => hHb _) hvG h8G,
      foldsOnto_leg3deep_branch hmT (armT ρ i) (armT_isLip hlip i) L hT0
        (fun j => hLb _) (fun j => hHb _) hvT h8T⟩

/-- **The branch `L + 4` on a thin sequence, through the re-split item.** The same conclusion as
`s3_span_nine_mid4_thin`, reached through `unserved_three_walks_thin`: this is the derivation
`s3_span_nine_mid4` performs in the general model, run on a thin sequence, and it checks that the
re-split of batch 49 loses nothing that was already proved. -/
theorem s3_span_nine_mid4_thin_of_three {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hlam : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)
  · exact ⟨_, _, hlam.1, hlam.2⟩
  · by_cases hvee : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)
    · exact ⟨_, _, hvee.1, hvee.2⟩
    · rcases unserved_three_walks_thin ρ σ i L hlip hcr hthin hLb hHb hp hlam hvee with
        ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩

end HPC.Fold
