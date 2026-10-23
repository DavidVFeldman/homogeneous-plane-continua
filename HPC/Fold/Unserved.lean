import HPC.Fold.CeilFar
import HPC.Fold.ProfileK

/-!
# The unserved pairs of the branch `L + 4`, with both crossings proved

With `cross_valley_vee_pair` (`HPC/Fold/ValleyFar.lean`) and `cross_ceil_sentence_far`
(`HPC/Fold/CeilFar.lean`) the two crossings of the branch `L + 4` are theorems, and the work item
`unserved_three_walks` (`HPC/Fold/Mixed.lean`) follows from them by the case analysis of
`unserved_three_walks_or_cross` (`HPC/Fold/ThreeWalks.lean`), which this file repeats in the one
order the two crossings support:

* if an arm fails `Valley4` it fails `Leg3Valley`, so the valley crossing folds **both** arms onto
  the V-walk and the pair is served by it — contrary to the hypothesis. So both arms satisfy
  `Valley4`;
* if an arm fails `Leg3Ceil`, the ceiling crossing gives both arms the sentence of `w₅` (the pair
  is not served by the Λ-walk, by hypothesis), and the criterion of `w₅` folds both arms onto it;
* otherwise both arms satisfy `Valley4` and `Leg3Ceil`, which is the exact criterion of `w₃`.

The file sits upstream of `HPC/Fold/ThreeWalks.lean`, so the two auxiliary steps it needs from
there and from `HPC/Fold/CrossCeil.lean` — the fold onto `w₃` from the two clauses, and the fold
onto `w₄` or `w₅` from the sentence — are re-proved here from the criteria they quote.
-/

namespace HPC.Fold

/-- **The first walk serves a pair whose arms both announce.** The criterion of `w₃`, on a pair;
this is `three_walks_w3_of_land` (`HPC/Fold/ThreeWalks.lean`), which lies downstream. -/
theorem w3_pair_of_land {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hvG : Valley4 (armG ρ i) L) (hcG : Leg3Ceil (armG ρ i) L)
    (hvT : Valley4 (armT ρ i) L) (hcT : Leg3Ceil (armT ρ i) L) :
    FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4)) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  exact ⟨(foldsOnto_leg3deep_iff_landmark hmG (armG ρ i) (armG_isLip hlip i) L hG0
      (fun j => hLb _) (fun j => hHb _)).2 ⟨hvG, hcG⟩,
    (foldsOnto_leg3deep_iff_landmark hmT (armT ρ i) (armT_isLip hlip i) L hT0
      (fun j => hLb _) (fun j => hHb _)).2 ⟨hvT, hcT⟩⟩

/-- **The sentence of `w₄` or `w₅` serves the pair.** This is
`ceil_case_three_walks_of_sentence` (`HPC/Fold/CrossCeil.lean`), which lies downstream. -/
theorem w45_pair_of_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hsent :
      ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
          (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
        ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
          (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L))) :
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 7) (L + 7))
        (leg3Walk' L (L + 9) (L + 7) (L + 2)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 7) (L + 7))
        (leg3Walk' L (L + 9) (L + 7) (L + 2))) ∨
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 7) (L + 4))
        (leg3Walk L (L + 9) (L + 7) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 7) (L + 4))
        (leg3Walk L (L + 9) (L + 7) (L + 4))) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  rcases hsent with ⟨⟨hmG4, hbG⟩, ⟨hmT4, hbT⟩⟩ | ⟨hg5, ht5⟩
  · exact Or.inl
      ⟨foldsOnto_w4_profile_min hmG (armG ρ i) (armG_isLip hlip i) L hG0 (fun j => hLb _)
          (fun j => hHb _) (midW4Min_of_midW4 hmG4) (bottomW4Min_of_bottomW4 hbG),
        foldsOnto_w4_profile_min hmT (armT ρ i) (armT_isLip hlip i) L hT0 (fun j => hLb _)
          (fun j => hHb _) (midW4Min_of_midW4 hmT4) (bottomW4Min_of_bottomW4 hbT)⟩
  · exact Or.inr
      ⟨(foldsOnto_w5_iff_landmark hmG (armG ρ i) (armG_isLip hlip i) L hG0 (fun j => hLb _)
          (fun j => hHb _)).2 hg5,
        (foldsOnto_w5_iff_landmark hmT (armT ρ i) (armT_isLip hlip i) L hT0 (fun j => hLb _)
          (fun j => hHb _)).2 ht5⟩

/-- **The work item of the branch `L + 4`: three walks serve every unserved pair.** A pair of the
branch served by neither canonical walk folds onto `w₃`, onto `w₄`, or onto `w₅` — both arms onto
the same walk. -/
theorem unserved_three_walks_far {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
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
  -- both arms satisfy the valley clause, or the pair is served by the V-walk
  have hvalley : Valley4 (armG ρ i) L ∧ Valley4 (armT ρ i) L := by
    constructor
    · by_contra hc
      exact hnotVee (cross_valley_vee_pair ρ σ i L hcr hLb hHb hp
        (Or.inl (fun h => hc (valley4_of_leg3Valley h))))
    · by_contra hc
      exact hnotVee (cross_valley_vee_pair ρ σ i L hcr hLb hHb hp
        (Or.inr (fun h => hc (valley4_of_leg3Valley h))))
  by_cases hcG : Leg3Ceil (armG ρ i) L
  · by_cases hcT : Leg3Ceil (armT ρ i) L
    · exact Or.inl (w3_pair_of_land ρ i L hlip hLb hHb hp hvalley.1 hcG hvalley.2 hcT)
    · exact Or.inr (w45_pair_of_sentence ρ i L hlip hLb hHb hp
        (cross_ceil_sentence_far ρ σ i L hlip hcr hLb hHb hp (Or.inr hcT) hnotLam))
  · exact Or.inr (w45_pair_of_sentence ρ i L hlip hLb hHb hp
      (cross_ceil_sentence_far ρ σ i L hlip hcr hLb hHb hp (Or.inl hcG) hnotLam))

end HPC.Fold
