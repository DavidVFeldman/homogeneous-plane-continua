import HPC.Fold.ProfileP
import HPC.Fold.Mixed

/-!
# The work item of the branch is three sentences

`unserved_three_walks` (`HPC/Fold/Mixed.lean`) offers an unserved pair of the branch `L + 4` three
walks and asks that one of them folds *both* arms. Since batch 48 the first of the three has an
exact criterion; this batch gives the other two one (`foldsOnto_w4_iff_landmark`,
`foldsOnto_w5_iff_landmark`). The three criteria together turn the work item into a statement with
no `FoldsOnto` in it at all.

`ThreeWalksSentence g t L` is the disjunction of the three landmark sentences, each read on *both*
arms, and `three_walks_iff_sentence` says it is equivalent — for 1-Lipschitz arms of the band based
at `L + 4` — to the conclusion of the work item. So what is left of `unserved_three_walks` is
`unserved_three_walks_sentence`: an unserved pair of the branch satisfies the sentence. That is the
form in which the question of the commission — whether three walks are enough, and whether a fourth
is needed — is a statement about crookedness and three explicit sentences about the levels of the
two arms.

The three sentences are not the same sentence three times:

| walk | what is asked of each arm |
|---|---|
| `w₃ = L+3 → L+6 → L+1 → L+8` | `Leg3Land`: descents to `L + 1` announced at `L + 5`, ascents to `L + 8` announced at `L + 5` then `L + 2` |
| `w₄ = L+3 → L+2 → L+8 → L+1` | `MidW4`: ascents to `L + 5` announced at `L + 3`; `BottomW4`: descents to `L` announced at `L + 3` then `L + 7` |
| `w₅ = L+3 → L+7 → L+1 → L+8` | `Valley5`: descents to `L + 1` announced at `L + 6`; `TopW5`: ascents to `L + 9` announced at `L + 6` then `L + 2` |
-/

namespace HPC.Fold

/-- **The sentence of the three walks, read on a pair of arms.** One of the three landmark
sentences holds of both arms. -/
def ThreeWalksSentence {mg mt : ℕ} (g : Fin mg → ℤ) (t : Fin mt → ℤ) (L : ℤ) : Prop :=
  (Leg3Land g L ∧ Leg3Land t L) ∨
  ((MidW4 g L ∧ BottomW4 g L) ∧ (MidW4 t L ∧ BottomW4 t L)) ∨
  ((Valley5 g L ∧ TopW5 g L) ∧ (Valley5 t L ∧ TopW5 t L))

/-- **The conclusion of the work item is the sentence.** For two 1-Lipschitz arms of the band
`[L, L + 9]` based at `L + 4`, the two arms fold onto one of the three walks — both onto the same
one — exactly when one of the three landmark sentences holds of both. -/
theorem three_walks_iff_sentence {mg mt : ℕ} (hg : 0 < mg) (ht : 0 < mt)
    (g : Fin mg → ℤ) (t : Fin mt → ℤ) (hglip : IsLip g) (htlip : IsLip t) (L : ℤ)
    (hg0 : g ⟨0, hg⟩ = L + 4) (ht0 : t ⟨0, ht⟩ = L + 4)
    (hgL : ∀ j, L ≤ g j) (hgH : ∀ j, g j ≤ L + 9)
    (htL : ∀ j, L ≤ t j) (htH : ∀ j, t j ≤ L + 9) :
    ((FoldsOnto g (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)))) ↔
      ThreeWalksSentence g t L := by
  have hw3g := foldsOnto_leg3deep_iff_landmark hg g hglip L hg0 hgL hgH
  have hw3t := foldsOnto_leg3deep_iff_landmark ht t htlip L ht0 htL htH
  have hw4g := foldsOnto_w4_iff_landmark hg g hglip L hg0 hgL hgH
  have hw4t := foldsOnto_w4_iff_landmark ht t htlip L ht0 htL htH
  have hw5g := foldsOnto_w5_iff_landmark hg g hglip L hg0 hgL hgH
  have hw5t := foldsOnto_w5_iff_landmark ht t htlip L ht0 htL htH
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hw3g.1 h1, hw3t.1 h2⟩
    · obtain ⟨hm1, -, hb1⟩ := hw4g.1 h1
      obtain ⟨hm2, -, hb2⟩ := hw4t.1 h2
      exact Or.inr (Or.inl ⟨⟨hm1, hb1⟩, ⟨hm2, hb2⟩⟩)
    · exact Or.inr (Or.inr ⟨hw5g.1 h1, hw5t.1 h2⟩)
  · rintro (⟨h1, h2⟩ | ⟨⟨hm1, hb1⟩, ⟨hm2, hb2⟩⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hw3g.2 h1, hw3t.2 h2⟩
    · exact Or.inr (Or.inl
        ⟨foldsOnto_w4_profile_min hg g hglip L hg0 hgL hgH (midW4Min_of_midW4 hm1)
            (bottomW4Min_of_bottomW4 hb1),
          foldsOnto_w4_profile_min ht t htlip L ht0 htL htH (midW4Min_of_midW4 hm2)
            (bottomW4Min_of_bottomW4 hb2)⟩)
    · exact Or.inr (Or.inr ⟨hw5g.2 h1, hw5t.2 h2⟩)

/-! ## The work item, as a statement about the levels of the two arms -/

/-- **What is left of `unserved_three_walks`.** With the three criteria exact, the work item is
equivalent to this statement: an unserved pair of the branch `L + 4` satisfies one of the three
landmark sentences on both arms. No fold appears in it. -/
theorem unserved_three_walks_of_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hsent : ThreeWalksSentence (armG ρ i) (armT ρ i) L) :
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
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  exact (three_walks_iff_sentence hmG hmT (armG ρ i) (armT ρ i) (armG_isLip hlip i)
    (armT_isLip hlip i) L hG0 hT0 (fun j => hLb _) (fun j => hHb _) (fun j => hLb _)
    (fun j => hHb _)).2 hsent

/-- **The work item and the sentence are the same statement.** At a pair of the branch the
conclusion of `unserved_three_walks` holds exactly when the sentence does, so the item asks
precisely that an unserved pair satisfies one of the three sentences. -/
theorem unserved_three_walks_iff_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4) :
    ((FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
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
          (leg3Walk L (L + 9) (L + 7) (L + 4)))) ↔
      ThreeWalksSentence (armG ρ i) (armT ρ i) L := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  exact three_walks_iff_sentence hmG hmT (armG ρ i) (armT ρ i) (armG_isLip hlip i)
    (armT_isLip hlip i) L hG0 hT0 (fun j => hLb _) (fun j => hHb _) (fun j => hLb _)
    (fun j => hHb _)

/-- **The first walk serves a pair whose arms both announce.** With the criterion of `w₃` exact,
the first disjunct of the work item needs nothing but the two clauses `Valley4` and `Leg3Ceil` on
both arms — no crookedness and no hypothesis on the pair. -/
theorem three_walks_w3_of_land {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
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

/-- **What is left of the work item is a crossing.** At a pair of the branch, either the work
item's conclusion already holds through the first walk, or some arm fails one of the two clauses
of `w₃` — and then, by the two theorems of batch 48, that arm is served by a canonical walk while
the pair is not. So the item asks only what happens across the basepoint, which is what the two
cross items were introduced for. -/
theorem unserved_three_walks_or_cross {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4) :
    (FoldsOnto (armG ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
      FoldsOnto (armT ρ i) (leg3Len L (L + 9) (L + 6) (L + 4))
        (leg3Walk L (L + 9) (L + 6) (L + 4))) ∨
    ((FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∨
        FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) ∨
      (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∨
        FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  rcases valley4_or_vee hmG (armG ρ i) (armG_isLip hlip i) (crookDown_armG hcr i) L hG0
    (fun j => hLb _) (fun j => hHb _) with hvG | h
  · rcases valley4_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
      (fun j => hLb _) (fun j => hHb _) with hvT | h
    · rcases leg3Ceil_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
        (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with hcG | h
      · rcases leg3Ceil_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
          (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with hcT | h
        · exact Or.inl (three_walks_w3_of_land ρ i L hlip hLb hHb hp hvG hcG hvT hcT)
        · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inl (Or.inl h))

/-- **The branch `L + 4` from the sentence.** If every unserved pair of the branch satisfies the
sentence of the three walks, the branch is complete: this is `s3_span_nine_mid4` with the work
item replaced by its landmark form. -/
theorem s3_span_nine_mid4_of_sentence {m : ℕ} (ρ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hsent :
      ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
          FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
      ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
          FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
      ThreeWalksSentence (armG ρ i) (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ), FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hlam : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)
  · exact ⟨_, _, hlam.1, hlam.2⟩
  · by_cases hvee : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)
    · exact ⟨_, _, hvee.1, hvee.2⟩
    · rcases unserved_three_walks_of_sentence ρ i L hlip hLb hHb hp (hsent hlam hvee) with
        ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩

end HPC.Fold
