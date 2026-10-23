import HPC.Fold.ThreeWalks
import HPC.Fold.CeilFar

/-!
# The ceiling case of the branch `L + 4`, as a crossing

The branch `L + 4` rests on `unserved_three_walks` (`HPC/Fold/Mixed.lean`), and
`unserved_three_walks_or_cross` (`HPC/Fold/ThreeWalks.lean`) says what is left of it: either both
arms meet the two clauses of `w₃` and the pair folds onto it, or some arm fails one of them and is
served by a canonical walk on its own, while the pair is not. The valley half of that crossing is
`cross_valley_profile`; this file is the ceiling half, which the commission of batch 52 asks in
sentence form.

Two things are proved here and one is asked.

* `not_foldsOnto_w3_of_not_leg3Ceil`: an arm failing `Leg3Ceil` does not fold onto `w₃`. So in the
  ceiling case the first of the three walks is out, whatever the other arm does — this is
  `leg3Ceil_of_foldsOnto_leg3` read backwards, and it is why the question is asked of `w₄` and
  `w₅` only.
* `leg3Ceil_other_of_not_lam`: if one arm fails `Leg3Ceil` and the pair does not fold onto the
  Λ-walk, the *other* arm satisfies `Leg3Ceil`. The failing arm folds onto the Λ-walk by
  `leg3Ceil_or_lam`, so if the other one failed too the pair would be served by that walk.
* `CrossCeilSentence` is the question: in that configuration, do both arms satisfy the sentence of
  `w₄`, or do both satisfy the sentence of `w₅`? By the criteria of batch 51 this is exactly "the
  pair folds onto `w₄`, or onto `w₅`", and with `ceil_case_three_walks_of_sentence` it settles the
  ceiling case of the work item.

**After batch 56 it is a theorem.** `HPC/Fold/CeilFar.lean` removes both residual configurations
by reading the crookedness clause of the faithful model at the ascent's own level and pinning the
links it returns with the timing law of Theorem 7: a link whose interval reaches `L + 7` is five
steps from a basepoint at `L + 4`, and one reaching `L + 8` is twelve, where the one-arm clauses
see only three and four. `cross_ceil_sentence` below is `cross_ceil_sentence_far`.

**The route, as it stood after batch 53.** It is now known which two
clauses the item is short of. `HPC/Fold/CeilArm.lean` proves the two halves that are statements about
arms alone — the arm failing `Leg3Ceil` satisfies `Valley5`, and the arm that does not fold onto
the Λ-walk satisfies `TopW5` — so what is left is `CeilCrossGap`: `TopW5` on the failing arm and
`Valley5` on the other one. `cross_ceil_sentence_of_gap` derives the item from that pair, with the
second disjunct (the sentence of `w₅`). `HPC/Fold/CeilCross.lean` then proves both clauses across
the basepoint outside two named local configurations, `CeilPeakResidual` and `CeilHighResidual`,
so `cross_ceil_sentence_of_not_residual` is the item for every pair avoiding them — 183 of the 192
configurations of the corpus of `census-batch53.c`.

What the censuses say. Over the corpus of `census-batch52.c` — 1 369 faithful pairs, 41 391 of
1 349 834 links non-thin, 256 183 basepoints of the branch — 12 373 basepoints have an arm failing
`Leg3Ceil`, and 521 of those also miss the Λ-walk, which is the configuration the question is about.
At every one of the 521 the answer is yes: both arms satisfy the sentence of `w₄` or both satisfy
the sentence of `w₅`. (Without the second hypothesis the implication is false: 168 basepoints have
an arm failing `Leg3Ceil` and satisfy neither sentence, and all of them are served by the Λ-walk.)
-/

namespace HPC.Fold

/-- **An arm failing the ceiling clause does not fold onto `w₃`.** -/
theorem not_foldsOnto_w3_of_not_leg3Ceil {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ¬ Leg3Ceil f L) :
    ¬ FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) :=
  fun hf => h (leg3Ceil_of_foldsOnto_leg3 hf)

/-- **In the ceiling case the pair is not served by `w₃`.** -/
theorem not_w3_pair_of_not_leg3Ceil {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L) :
    ¬ (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
          (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
        FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
          (leg3Walk L (L + 9) (L + 6) (L + 4))) := by
  rintro ⟨h1, h2⟩
  rcases hfail with h | h
  · exact not_foldsOnto_w3_of_not_leg3Ceil h h1
  · exact not_foldsOnto_w3_of_not_leg3Ceil h h2

/-- **The other arm satisfies the ceiling clause.** If one arm of a pair of the branch fails
`Leg3Ceil` and the pair does not fold onto the Λ-walk, the other arm satisfies `Leg3Ceil`. -/
theorem leg3Ceil_other_of_not_lam {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    (¬ Leg3Ceil (armG ρ i) L → Leg3Ceil (armT ρ i) L) ∧
      (¬ Leg3Ceil (armT ρ i) L → Leg3Ceil (armG ρ i) L) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  -- if both arms failed, both would fold onto the Λ-walk and the pair would be served by it
  have key : Leg3Ceil (armG ρ i) L ∨ Leg3Ceil (armT ρ i) L := by
    by_contra hc
    push_neg at hc
    rcases leg3Ceil_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
      (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with h | hlG
    · exact hc.1 h
    · rcases leg3Ceil_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with h | hlT
      · exact hc.2 h
      · exact hnotLam ⟨hlG, hlT⟩
  exact ⟨fun hg => key.resolve_left hg, fun ht => key.resolve_right ht⟩

/-- **The ceiling crossing, as the commission asks it.** A pair of the branch `L + 4` with an arm
failing `Leg3Ceil` — so that that arm folds onto the Λ-walk alone — and with the pair itself not
folding onto the Λ-walk satisfies the sentence of `w₄` on both arms, or the sentence of `w₅` on
both arms.

This is the ceiling half of what is left of `unserved_three_walks`, in the form the valley half
(`cross_valley_profile`) is asked in. It is *not* the refuted `cross_ceil_profile`: that asked the
pair to fold onto the Λ-walk, and batch 49 exhibited a pair where it does not. What is asked here
is that the pair is then served by one of the two remaining walks, which is what every census of
this repository finds. -/
theorem cross_ceil_sentence {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hG : HighAt (armG ρ i) (L + 1) (L + 8)) (hT : HighAt (armT ρ i) (L + 1) (L + 8))
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
        (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
      ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
        (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L)) :=
  cross_ceil_sentence_far ρ σ i L hlip hcr hLb hHb hp hfail hnotLam

/-- **The ceiling case of the work item follows.** With `cross_ceil_sentence`, a pair of the branch
with an arm failing `Leg3Ceil` and not served by the Λ-walk folds onto `w₄` or onto `w₅` — both
arms onto the same one. -/
theorem ceil_case_three_walks_of_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
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

end HPC.Fold
