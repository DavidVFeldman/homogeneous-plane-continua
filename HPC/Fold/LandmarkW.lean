import HPC.Fold.Span8
import HPC.Fold.Landmark

/-!
# The landmark criteria of the other two walks

`unserved_three_walks` (`HPC/Fold/Mixed.lean`) offers an unserved pair of the branch `L + 4` three
walks:

| | walk | as a term | times |
|---|---|---|---|
| `w₃` | `L+3 → L+6 → L+1 → L+8` | `leg3Walk L (L+9) (L+6) (L+4)` | 16 |
| `w₄` | `L+3 → L+2 → L+8 → L+1` | `leg3Walk' L (L+9) (L+7) (L+2)` | 15 |
| `w₅` | `L+3 → L+7 → L+1 → L+8` | `leg3Walk L (L+9) (L+7) (L+4)` | 18 |

`HPC/Fold/Landmark.lean` reads the necessity half of the landmark sentence off the first of them
(`leg3Ceil_of_foldsOnto_leg3`, `leg3Valley4_of_foldsOnto_leg3`) and the valley clause off the third
(`deepValley_of_foldsOnto_leg3deep`). This file does the rest, and the answer is not the same
sentence three times: **which events of an arm a walk announces depends on the walk**, and the
three walks announce different ones.

* `w₃` announces its descents to `L + 1` (`Valley4`) and its ascents to `L + 8` (`Leg3Ceil`);
* `w₄` announces its ascents to `L + 8` (`CeilW4`) and its descents to `L` (`BottomW4`) — but
  **not** its descents to `L + 1`, because the walk's second position already carries `L + 2` and
  so serves `L + 1` at the step one. A guess to the contrary was refuted by the census of this
  batch before it reached Lean: 22 223 arms of the corpus fold onto `w₄` and have a descent to
  `L + 1` earlier than any clause of that kind allows;
* `w₅` announces its descents to `L + 1` (`Valley5`, one level and one step deeper than `w₃`) and
  its ascents to `L + 9` (`TopW5`) — but its ascents to `L + 8` only trivially, because its peak
  position carries `L + 7` and so serves `L + 8` at the step four.

The consequence for the branch is `three_walks_necessary`: a pair served by one of the three walks
has *both* arms meeting one of three named clauses. To refute `unserved_three_walks` at a pair it
is therefore enough to find, for each of the three walks, one arm failing that walk's clause — and
since `HPC/Fold/Decide.lean` the same refutation can also be had directly, by deciding the fold.
-/

namespace HPC.Fold

/-! ## The three clauses -/

/-- **The valley clause of `w₃`.** Before every descent to `L + 1` a time at `L + 5` or above, at
a step at least `3` and at least four steps earlier. -/
def Valley4 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ d.val ∧ L + 5 ≤ f j

/-- **The ceiling clause of `w₄`.** Before every ascent to `L + 8` a time at `L + 3` or below, at
a step at least `1` and at least five steps earlier. -/
def CeilW4 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 1 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ f j ≤ L + 3

/-- **The valley clause of `w₅`.** Before every descent to `L + 1` a time at `L + 6` or above, at
a step at least `4` and at least five steps earlier. -/
def Valley5 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 4 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ L + 6 ≤ f j

/-- **The floor clause of `w₄`.** Before every descent to `L` itself a time at `L + 3` or below
and then a time at `L + 7` or above, with the walk's own gaps. -/
def BottomW4 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L → ∃ j k : Fin m, 1 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
    f j ≤ L + 3 ∧ L + 7 ≤ f k

/-- The valley clause of `w₃` is what `Landmark.lean` proves necessary for `w₃`. -/
theorem valley4_of_foldsOnto_leg3 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4))
      (leg3Walk L (L + 9) (L + 6) (L + 4))) :
    Valley4 f L := leg3Valley4_of_foldsOnto_leg3 h

/-- The valley clause of `w₅` is what `Landmark.lean` proves necessary for `w₅`. -/
theorem valley5_of_foldsOnto_w5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4))
      (leg3Walk L (L + 9) (L + 7) (L + 4))) :
    Valley5 f L := deepValley_of_foldsOnto_leg3deep h

/-! ## The reflected walk `w₄` -/

/-- `w₄` has fifteen positions. -/
theorem leg3Len_w4' (L : ℤ) : leg3Len L (L + 9) (L + 7) (L + 7) = 15 := by
  simp only [leg3Len]
  omega

/-- The levels of `w₄`, position by position: `3,2,3,4,5,6,7,8,7,6,5,4,3,2,1` above `L`. -/
theorem leg3Walk_w4_val (L : ℤ) (u : ℕ) (hu : u < 15) :
    leg3Walk' L (L + 9) (L + 7) (L + 2) u =
      L + (if u ≤ 1 then (3 - u : ℤ) else if u ≤ 7 then (1 + u : ℤ) else (15 - u : ℤ)) := by
  simp only [leg3Walk', leg3Walk]
  split_ifs <;> omega

/-- The landmark of `w₄` at its trough. -/
theorem leg3Walk_w4_one (L : ℤ) : leg3Walk' L (L + 9) (L + 7) (L + 2) 1 = L + 2 := by
  rw [leg3Walk_w4_val L 1 (by norm_num)]
  norm_num

/-- The landmark of `w₄` at its peak. -/
theorem leg3Walk_w4_seven (L : ℤ) : leg3Walk' L (L + 9) (L + 7) (L + 2) 7 = L + 8 := by
  rw [leg3Walk_w4_val L 7 (by norm_num)]
  norm_num

/-- An ascent to `L + 8` is served only by the positions `6`, `7`, `8` of `w₄`. -/
theorem leg3Walk_w4_high_pos {L v : ℤ} {p : ℕ} (hp : p < 15) (hv : L + 8 ≤ v)
    (h : |v - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1) : 6 ≤ p := by
  rw [leg3Walk_w4_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- A descent to `L` is served only by the last position of `w₄`. -/
theorem leg3Walk_w4_bot_pos {L v : ℤ} {p : ℕ} (hp : p < 15) (hv : v ≤ L)
    (h : |v - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1) : 14 ≤ p := by
  rw [leg3Walk_w4_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- **The ceiling clause of `w₄` is necessary.** An arm folding onto `L+3 → L+2 → L+8 → L+1` has,
before every ascent to `L + 8`, a time at `L + 3` or below at a step at least `1` and at least
five steps earlier. -/
theorem ceilW4_of_foldsOnto_w4 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7))
      (leg3Walk' L (L + 9) (L + 7) (L + 2))) :
    CeilW4 f L := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 7) (L + 7) →
      |f d - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1 → 6 ≤ p := by
    intro p hp hpv
    rw [leg3Len_w4'] at hp
    exact leg3Walk_w4_high_pos hp hd hpv
  obtain ⟨j, hj0, hjd, hjv⟩ := foldsOnto_landmark1 h d 1 6 (by norm_num) hpos
  rw [leg3Walk_w4_one, abs_le] at hjv
  exact ⟨j, hj0, by omega, by omega⟩

/-- **The floor clause of `w₄` is necessary.** An arm folding onto `L+3 → L+2 → L+8 → L+1` has,
before every descent to `L` itself, a time at `L + 3` or below and then a time at `L + 7` or
above, with the three gaps the walk's own. -/
theorem bottomW4_of_foldsOnto_w4 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7))
      (leg3Walk' L (L + 9) (L + 7) (L + 2))) :
    BottomW4 f L := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 7) (L + 7) →
      |f d - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1 → 14 ≤ p := by
    intro p hp hpv
    rw [leg3Len_w4'] at hp
    exact leg3Walk_w4_bot_pos hp hd hpv
  obtain ⟨j, k, hj0, hjk, hkd, hjv, hkv⟩ :=
    foldsOnto_landmark2 h d 1 7 14 (by norm_num) (by norm_num) hpos
  rw [leg3Walk_w4_one, abs_le] at hjv
  rw [leg3Walk_w4_seven, abs_le] at hkv
  exact ⟨j, k, hj0, by omega, by omega, by omega, by omega⟩

/-! ## The deep walk `w₅`, at the ceiling -/

/-- The landmark of `w₅` at its trough. -/
theorem leg3Walk_deep_ten (L : ℤ) : leg3Walk L (L + 9) (L + 7) (L + 4) 10 = L + 1 := by
  rw [leg3Walk_deep_val L 10 (by norm_num)]
  norm_num

/-- An ascent to `L + 9` is served only by the last position of `w₅`: the walk's own peak is
`L + 7`, which serves `L + 8` but not `L + 9`. -/
theorem leg3Walk_deep_top_pos {L v : ℤ} {p : ℕ} (hp : p < 18) (hv : L + 9 ≤ v)
    (h : |v - leg3Walk L (L + 9) (L + 7) (L + 4) p| ≤ 1) : 17 ≤ p := by
  rw [leg3Walk_deep_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- **The ceiling clause of `w₅` is necessary.** An arm folding onto `L+3 → L+7 → L+1 → L+8` has,
before every ascent to `L + 9`, a time at `L + 6` or above and then a time at `L + 2` or below,
with the three gaps the walk's own. -/
def TopW5 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
    L + 6 ≤ f j ∧ f k ≤ L + 2

/-- `TopW5` is necessary for a fold onto `w₅`. -/
theorem topW5_of_foldsOnto_w5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4))
      (leg3Walk L (L + 9) (L + 7) (L + 4))) :
    TopW5 f L := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 7) (L + 4) →
      |f d - leg3Walk L (L + 9) (L + 7) (L + 4) p| ≤ 1 → 17 ≤ p := by
    intro p hp hpv
    rw [leg3Len_deep] at hp
    exact leg3Walk_deep_top_pos hp hd hpv
  obtain ⟨j, k, hj0, hjk, hkd, hjv, hkv⟩ :=
    foldsOnto_landmark2 h d 4 10 17 (by norm_num) (by norm_num) hpos
  rw [leg3Walk_deep_four, abs_le] at hjv
  rw [leg3Walk_deep_ten, abs_le] at hkv
  exact ⟨j, k, hj0, by omega, by omega, by omega, by omega⟩

/-! ## Sufficiency for `w₅`

The engine of `HPC/Fold/Leg3Deep.lean` is stated for an arbitrary peak level `K`, and the branch
used it at `K = L + 6`, which is `w₃`. At `K = L + 7` it is `w₅`, and the hypotheses it then asks
are the announcements below. So the third walk has both halves of a criterion: these announcements
suffice, and `Valley5` and `TopW5` are necessary. The two halves do not meet — the announcements
ask a time *at* the peak level where the landmark sentence tolerates one level less, exactly the
gap batch 48 closed for `w₃` — so the criterion for `w₅` is not yet exact. -/

/-- **The deep walk serves an arm that announces its descents and its ascents to the top.** The
engine of batch 44, read at the peak level `L + 7`. Note that the ceiling clause is asked only of
ascents to `L + 9`: the walk's peak already serves `L + 8`, which is what `topW5_of_foldsOnto_w5`
sees from the other side. -/
theorem foldsOnto_w5_branch {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 6 ≤ f k'))
    (hceil : ∀ d : Fin m, L + 9 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ f k ∧ f k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ L + 1 ∧ L + 7 ≤ f k' ∧ f k'' ≤ L + 2)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) := by
  refine foldsOnto_leg3_deep hm f hf L (L + 9) (L + 7) (L + 4) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  · intro d hd
    rcases hvalley d hd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', hkf, by omega⟩
  · intro d hd
    rcases hceil d (by omega) with h | ⟨k, k', ha, hb, hc, he⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨k, k', ha, hb, by omega, he⟩)
    · exact Or.inr (Or.inr h)

/-! ## How the clauses compare -/

/-- The profile clause of batch 48 is stronger than the valley clause of `w₃`: it asks the same
time one step earlier. -/
theorem valley4_of_leg3Valley {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Leg3Valley f L) :
    Valley4 f L := by
  intro d hd
  obtain ⟨j, hj0, hjd, hjf⟩ := h d hd
  exact ⟨j, hj0, by omega, hjf⟩

/-- The valley clause of `w₅` is stronger than that of `w₃`: one level deeper and one step
earlier. -/
theorem valley4_of_valley5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Valley5 f L) : Valley4 f L := by
  intro d hd
  obtain ⟨j, hj0, hjd, hjf⟩ := h d hd
  exact ⟨j, by omega, by omega, by omega⟩

/-- **An arm failing `Valley4` folds onto the V-walk**, by `leg3Valley_or_vee` of batch 48: the
clause it fails is weaker than the one that lemma asks. -/
theorem valley4_or_vee {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcrd : CrookDown f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    Valley4 f L ∨ FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  rcases leg3Valley_or_vee hm f hf hcrd L h0 hL hH with h | h
  · exact Or.inl (valley4_of_leg3Valley h)
  · exact Or.inr h

/-- **Two of the three walks ask `Valley4`.** An arm folding onto `w₃` or onto `w₅` satisfies it,
so an arm that fails it leaves only `w₄` of the three. -/
theorem valley4_of_foldsOnto_w3_or_w5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) ∨
      FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4))) :
    Valley4 f L := by
  rcases h with h | h
  · exact valley4_of_foldsOnto_leg3 h
  · exact valley4_of_valley5 (valley5_of_foldsOnto_w5 h)

/-! ## What the three walks announce, together -/

/-- **The instrument of refutation for `unserved_three_walks`.** If the two arms of a pair fold
onto one of the three walks — both onto the same one — then both arms meet `Leg3Ceil`, or both
meet `CeilW4`, or both meet `Valley5`. So a pair at which each of the three clauses fails on some
arm folds onto none of the three walks. -/
theorem three_walks_necessary {mg mt : ℕ} {g : Fin mg → ℤ} {t : Fin mt → ℤ} {L : ℤ}
    (h : (FoldsOnto g (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2))) ∨
      (FoldsOnto g (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) ∧
        FoldsOnto t (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)))) :
    (Leg3Ceil g L ∧ Leg3Ceil t L) ∨ (CeilW4 g L ∧ CeilW4 t L) ∨ (Valley5 g L ∧ Valley5 t L) := by
  rcases h with ⟨hg, ht⟩ | ⟨hg, ht⟩ | ⟨hg, ht⟩
  · exact Or.inl ⟨leg3Ceil_of_foldsOnto_leg3 hg, leg3Ceil_of_foldsOnto_leg3 ht⟩
  · exact Or.inr (Or.inl ⟨ceilW4_of_foldsOnto_w4 hg, ceilW4_of_foldsOnto_w4 ht⟩)
  · exact Or.inr (Or.inr ⟨valley5_of_foldsOnto_w5 hg, valley5_of_foldsOnto_w5 ht⟩)

end HPC.Fold
