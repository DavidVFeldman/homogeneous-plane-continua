import HPC.Fold.Span8
import HPC.Fold.MixedWitness
import HPC.Fold.Timing
import HPC.Fold.Leg3Deep
import HPC.Fold.Leg3Profile
import HPC.Fold.ValleyFar
import HPC.Fold.Unserved

/-!
# Span nine: the two branches, with both ends attained

`s3_span_nine_of_mid` (`HPC/Fold/CrossArm.lean`) reduces `s3_span_nine` to the two statements
below, which are its hypotheses `key4` and `key5` verbatim.

State of the branch `L + 4` after batch 43, on actual pairs:

* both arms Λ-type (stand at `L + 7` before dropping to `L + 1`): served by the Λ-walk
  (`s3_span_nine_mid_low_of_lam`);
* both arms V-type: served by the V-walk (`s3_span_nine_mid_low_of_veeProfile`);
* mixed: inhabited (`mix_no_common_walk_of_the_two`, and 55 of the 182 branch basepoints of
  `bing 0 9`); every mixed pair met by `census-batch43.c` is served by the four-leg walk `w4`,
  `L+3 → L+6 → L+1 → L+8`, and the witness pair is, in Lean (`mix_served_by_four_leg`);
* no arm of the census fails both criteria — checked, not proved.

## What this file adds

* `ann_dichotomy` — for any two levels `a < b` and any arm, either every descent to `a` is
  preceded by a time at `b`, or every ascent to `b` is preceded by a time at `a`: whichever of
  the two events happens first decides which announcement holds. So *no arm fails both
  criteria*, and that is now proved rather than checked (`arm_lam_or_vee`).
* with the dichotomy, the branch `L + 4` reduces to the mixed configuration alone: the two cases
  in which the two arms announce differently.
* `seq_gap`, `cross_gap_ge`, `cross_gap_le` — Bing's timing law (`minGap`) read across the
  basepoint rather than along one arm, as `armG_gap` and `armT_gap` read it along one arm.
* `mix_events_far` — the quantitative form of the mixed configuration, and the reason a mixed
  pair is not free to be mixed *early*: if the backward arm stands at `L + 1` at its step `dT`
  and the forward arm stands at `L + 7` at its step `dG`, then `dT + dG ≥ 70`, because the
  window between the two times is a faithful crooked sequence of span at least six and `z 6 = 71`.

* `foldsOnto_leg3deep_branch`, `s3_span_nine_mid4_of_valley` — the **third walk**,
  `L+3 → L+6 → L+1 → L+8`, with a criterion of its own, on the engine
  `HPC/Fold/Leg3Deep.lean` proved in batch 44. The branch `L + 4` follows from it and from two
  work items, which say that a pair folding onto neither canonical walk satisfies its two
  hypotheses.

## What batch 45 changes

The ceiling hypothesis of the third walk was stated in batch 44 as `HighAt f L (L + 8)`, and the
work item `unserved_high8` claimed it of every pair that folds onto neither canonical walk. **That
is false**, on an actual pair: `bing 0 9` at its basepoint `278` (`HPC/Fold/Bing9Witness.lean`,
`not_unservedHigh8`; and `census-batch45b.c`, where thirty-three of the 182 branch basepoints of
that chain refute it). The statement is kept, commented out, at the work item below.

What the engine actually consumes is the weaker announcement `CeilAnn`, and the branch is re-split
on it: `valleyBranch_ceiling` derives `CeilAnn` from `HighAt f L (L + 8)` but not conversely,
`foldsOnto_leg3deep_branch` and `s3_span_nine_mid4_of_valley` now ask `CeilAnn`, and
`ceiling_or_lam` — an arm failing `CeilAnn` folds onto the Λ-walk by itself — replaces
`high8_or_lam`. The work item is now `unserved_ceiling`, which holds on every pair of the census.

Also new: `no_low_gap`, `no_low_gap'`, `no_high_gap`, `no_high_gap'` — the crookedness clause read
on a *window*, and `cross_floor_excluded`, `cross_floor_excluded'`, which apply it across the
basepoint. They cut both remaining work items down to the case in which the descending arm's first
descent lands exactly on `L + 1`.

The two work items and the mirror branch at `L + 5` are what is left — in the **general** model.
For a thin sequence `σ = ρ` both work items are proved in `HPC/Fold/MixedThin.lean`, and with
them the branch `L + 4`; `HPC/Fold/ThinSpan9.lean` reflects that branch onto the branch `L + 5`
and so completes span nine there.

## What batch 47 changes

Both work items were refuted in batch 46, on shaved copies of `bing 0 9`, and are kept below,
commented out. The branch is re-split once more, on `unserved_leg3deep`: a pair folding onto
neither canonical walk has both arms folding onto the third walk `L+3 → L+6 → L+1 → L+8`
*itself*, with no announcement in between. That in turn is proved from two work items — the
profile criterion of `HPC/Fold/Leg3Profile.lean`, which is a statement about arms alone, and
`unserved_profile`, which says an unserved pair meets it. That is what the censuses
actually say — over general pairs, at every unserved branch basepoint met so far, it is that one
walk that serves, not a walk chosen pair by pair — and it is what the refutations leave standing:
what batch 46 refuted are the announcements through which `s3_span_nine_mid4_of_valley` reached
the walk, not the fold onto it.

Every `sorry` is a work item.
-/

namespace HPC.Fold

/-! ## The two announcements -/

/-- **The Λ-announcement.** Before the arm ever drops to `L + 1` it stands at `L + 7`. This is
the hypothesis of `s3_span_nine_mid_low_of_lam`. -/
def LamAnn {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, j.val < d.val ∧ L + 7 ≤ f j

/-- **The V-announcement.** Before the arm ever rises to `L + 7` it stands at `L + 1`. This is
the hypothesis of `s3_span_nine_mid_low_of_floor`. -/
def VeeAnn {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 7 ≤ f d → ∃ j : Fin m, j.val < d.val ∧ f j ≤ L + 1

/-- **Whichever event comes first decides.** For any two levels `a < b`, an arbitrary integer
sequence announces its descents to `a` by an earlier time at `b`, or its ascents to `b` by an
earlier time at `a`. No hypothesis on the sequence is used: if both announcements failed, the
first witness of each failure would be an earlier witness for the other. -/
theorem ann_dichotomy {m : ℕ} (f : Fin m → ℤ) (a b : ℤ) (hab : a < b) :
    (∀ d : Fin m, f d ≤ a → ∃ j : Fin m, j.val < d.val ∧ b ≤ f j) ∨
    (∀ d : Fin m, b ≤ f d → ∃ j : Fin m, j.val < d.val ∧ f j ≤ a) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨d1, hd1, hn1⟩, ⟨d2, hd2, hn2⟩⟩ := hc
  rcases lt_trichotomy d1.val d2.val with h | h | h
  · exact absurd hd1 (by have := hn2 d1 h; omega)
  · have : f d1 = f d2 := by rw [Fin.ext h]
    omega
  · exact absurd hd2 (by have := hn1 d2 h; omega)

/-- **No arm fails both criteria.** Every arm of the branch satisfies the Λ-announcement or the
V-announcement; the census of batch 43 checked this over its corpus, and it holds of every
integer sequence whatever. -/
theorem arm_lam_or_vee {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : LamAnn f L ∨ VeeAnn f L :=
  ann_dichotomy f (L + 1) (L + 7) (by omega)

/-! ## The timing law across the basepoint

`armG_gap` and `armT_gap` (`HPC/Fold/Timing.lean`) read `minGap` along one arm. The same
argument reads it between two arbitrary times of the sequence, and so between a time on the
backward arm and a time on the forward arm. -/

/-- **Bing's timing law between two times of the sequence.** If two links of a faithful crooked
sequence stand at levels exactly `d` apart, at times `s < t`, then `z d ≤ t - s + 1`. -/
theorem seq_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (s t : Fin n)
    (hst : s.val < t.val) (d : ℕ) (hd : ρ s + d = ρ t ∨ ρ t + d = ρ s) :
    z d ≤ t.val - s.val + 1 := by
  have hsn := s.isLt
  have htn := t.isLt
  have hrestr := isCrookedIvF_restrict hcr s.val t.val (by omega) htn
  set m : ℕ := t.val - s.val with hm
  have hmpos : 0 < m := by omega
  have hne : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  have hS : (⟨s.val + (0 : ℕ), by omega⟩ : Fin n) = s := Fin.ext (by simp)
  have hT : (⟨s.val + m, by omega⟩ : Fin n) = t := Fin.ext (by simp; omega)
  have hles : ρ s ≤ σ s := hcr.le _
  have hlet : ρ t ≤ σ t := hcr.le _
  have key : z d ≤ m + 1 := by
    rcases hd with h | h
    · refine minGap d hrestr ⟨0, by omega⟩ ⟨m, by omega⟩ (ρ s) ?_ ?_ ?_ ?_ hne
      · simp only [hS]; exact le_refl _
      · simp only [hS]; exact hles
      · simp only [hT]; omega
      · simp only [hT]; rw [show ρ s + (d : ℤ) = ρ t from h]; exact hlet
    · refine minGap d hrestr ⟨m, by omega⟩ ⟨0, by omega⟩ (ρ t) ?_ ?_ ?_ ?_ (Ne.symm hne)
      · simp only [hT]; exact le_refl _
      · simp only [hT]; exact hlet
      · simp only [hS]; omega
      · simp only [hS]; rw [show ρ t + (d : ℤ) = ρ s from h]; exact hles
  omega

/-- **The timing law across the basepoint, forward arm high.** If the backward arm at its step
`dT` stands at least `D` levels below the forward arm at its step `dG`, then `z D ≤ dT + dG + 1`:
the window between the two times is itself a faithful crooked sequence, and `minGap` counts its
links. -/
theorem cross_gap_ge {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val)) (D : ℕ)
    (h : armT ρ i dT + D ≤ armG ρ i dG) :
    z D ≤ dT.val + dG.val + 1 := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  set a : Fin n := ⟨i.val - dT.val, by omega⟩ with ha
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hb
  have hav : armT ρ i dT = ρ a := rfl
  have hbv : armG ρ i dG = ρ b := rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : z 0 = 1 := rfl
    omega
  · have hab : a.val < b.val := by
      by_contra hc
      have : a = b := Fin.ext (by simp only [ha, hb] at *; omega)
      rw [this] at hav
      omega
    set E : ℕ := (ρ b - ρ a).toNat with hE
    have hEeq : (E : ℤ) = ρ b - ρ a := Int.toNat_of_nonneg (by omega)
    have hDE : D ≤ E := by omega
    have hgap := seq_gap hcr a b hab E (Or.inl (by omega))
    have := z_mono hDE
    simp only [ha, hb] at hgap
    omega

/-- **The timing law across the basepoint, backward arm high.** The reflection of
`cross_gap_ge`. -/
theorem cross_gap_le {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val)) (D : ℕ)
    (h : armG ρ i dG + D ≤ armT ρ i dT) :
    z D ≤ dT.val + dG.val + 1 := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  set a : Fin n := ⟨i.val - dT.val, by omega⟩ with ha
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hb
  have hav : armT ρ i dT = ρ a := rfl
  have hbv : armG ρ i dG = ρ b := rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : z 0 = 1 := rfl
    omega
  · have hab : a.val < b.val := by
      by_contra hc
      have : a = b := Fin.ext (by simp only [ha, hb] at *; omega)
      rw [this] at hav
      omega
    set E : ℕ := (ρ a - ρ b).toNat with hE
    have hEeq : (E : ℤ) = ρ a - ρ b := Int.toNat_of_nonneg (by omega)
    have hDE : D ≤ E := by omega
    have hgap := seq_gap hcr a b hab E (Or.inr (by omega))
    have := z_mono hDE
    simp only [ha, hb] at hgap
    omega

/-- **A mixed pair cannot be mixed early.** If the backward arm stands at `L + 1` at its step
`dT` and the forward arm stands at `L + 7` at its step `dG` — the two events that make a pair
mixed — then `dT + dG ≥ 70`. The two times are six levels apart, and a faithful crooked sequence
needs `z 6 = 71` links to span six levels. -/
theorem mix_events_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 1) (hG : L + 7 ≤ armG ρ i dG) :
    70 ≤ dT.val + dG.val := by
  have h := cross_gap_ge hcr i dT dG 6 (by push_cast; omega)
  have hz : z 6 = 71 := by decide
  omega

/-- The mirror of `mix_events_far`: the forward arm at the floor and the backward arm at the
ceiling. -/
theorem mix_events_far' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L + 1) (hT : L + 7 ≤ armT ρ i dT) :
    70 ≤ dT.val + dG.val := by
  have h := cross_gap_le hcr i dT dG 6 (by push_cast; omega)
  have hz : z 6 = 71 := by decide
  omega

/-! ## Two exclusions across the basepoint

`no_split_low_before_high` (`HPC/Fold/CrossArm.lean`) forbids a low time before the basepoint and
a high time after it when the two arms stay away from the two ends *everywhere*. The four
statements below are the same clause read on a *window*: only the times strictly between the two
are constrained, so they apply to the part of an arm before its first descent, which is what the
two work items below are about. Each is one application of the crookedness clause: the clause
puts a time within one of the lower level strictly between the two, and that is what the window
hypothesis forbids. -/

/-- **No low gap, the low time first.** Between a time at `A` or below and a later time at
`A + 3` or above, some time stands at `A + 1` or below. -/
theorem no_low_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (A : ℤ) (s t : Fin n)
    (hst : s.val < t.val) (hs : ρ s ≤ A) (ht : A + 3 ≤ ρ t)
    (hmid : ∀ r : Fin n, s.val < r.val → r.val < t.val → A + 2 ≤ ρ r) : False := by
  obtain ⟨u, u', h1, h2, h3, -, -, -, h7⟩ := crookUp_seq hcr s t hst (by omega)
  exact absurd (hmid u' (by omega) h3) (by omega)

/-- **No low gap, the low time last.** The reflection of `no_low_gap` in time. -/
theorem no_low_gap' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (A : ℤ) (s t : Fin n)
    (hst : s.val < t.val) (hs : A + 3 ≤ ρ s) (ht : ρ t ≤ A)
    (hmid : ∀ r : Fin n, s.val < r.val → r.val < t.val → A + 2 ≤ ρ r) : False := by
  obtain ⟨u, u', h1, h2, h3, h4, h5, -, -⟩ := crookDown_seq hcr s t hst (by omega)
  exact absurd (hmid u (by omega) (by omega)) (by omega)

/-- **No high gap, the high time last.** Between a time at `B - 3` or below and a later time at
`B` or above, some time stands at `B - 2` or above. -/
theorem no_high_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (B : ℤ) (s t : Fin n)
    (hst : s.val < t.val) (hs : ρ s ≤ B - 3) (ht : B ≤ ρ t)
    (hmid : ∀ r : Fin n, s.val < r.val → r.val < t.val → ρ r ≤ B - 3) : False := by
  obtain ⟨u, u', h1, h2, h3, h4, -, -, -⟩ := crookUp_seq hcr s t hst (by omega)
  exact absurd (hmid u h1 (by omega)) (by omega)

/-- **No high gap, the high time first.** The reflection of `no_high_gap` in time. -/
theorem no_high_gap' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (B : ℤ) (s t : Fin n)
    (hst : s.val < t.val) (hs : B ≤ ρ s) (ht : ρ t ≤ B - 3)
    (hmid : ∀ r : Fin n, s.val < r.val → r.val < t.val → ρ r ≤ B - 3) : False := by
  obtain ⟨u, u', h1, h2, h3, -, -, h6, -⟩ := crookDown_seq hcr s t hst (by omega)
  exact absurd (hmid u' (by omega) h3) (by omega)

/-- **The floor is not reached on one arm while the other climbs three levels.** If the backward
arm reaches the floor `L` at its step `dT`, standing at `L + 2` or above before that step, then
the forward arm cannot stand three levels above the basepoint at a step before which it, too,
stays at `L + 2` or above: the crookedness clause between the two times would put a time at
`L + 1` or below between them, and there is none. -/
theorem cross_floor_excluded {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 4) (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L)
    (hTmid : ∀ k : Fin (i.val + 1), k.val < dT.val → L + 2 ≤ armT ρ i k)
    (hG : L + 3 ≤ armG ρ i dG)
    (hGmid : ∀ k : Fin (n - i.val), k.val < dG.val → L + 2 ≤ armG ρ i k) : False := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  have hTpos : 0 < dT.val := by
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · exfalso
      have hz : dT = (⟨0, by omega⟩ : Fin (i.val + 1)) := Fin.ext (by omega)
      have h0 : armT ρ i (⟨0, by omega⟩ : Fin (i.val + 1)) = ρ i := rfl
      rw [hz, h0, hp] at hT
      omega
    · exact h
  have htv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
  have hgv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
  refine no_low_gap hcr L ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩
    (show i.val - dT.val < i.val + dG.val by omega) (by rw [← htv]; exact hT)
    (by rw [← hgv]; exact hG) ?_
  intro r hr1' hr2'
  have hr1 : i.val - dT.val < r.val := hr1'
  have hr2 : r.val < i.val + dG.val := hr2'
  rcases Nat.lt_or_ge i.val r.val with hri | hri
  · have := hGmid ⟨r.val - i.val, by omega⟩ (by simp; omega)
    rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this
  · have := hTmid ⟨i.val - r.val, by omega⟩ (by simp; omega)
    rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri] at this

/-- The reflection of `cross_floor_excluded` in the basepoint: the forward arm reaches the floor
and the backward arm climbs. -/
theorem cross_floor_excluded' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 4) (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L)
    (hGmid : ∀ k : Fin (n - i.val), k.val < dG.val → L + 2 ≤ armG ρ i k)
    (hT : L + 3 ≤ armT ρ i dT)
    (hTmid : ∀ k : Fin (i.val + 1), k.val < dT.val → L + 2 ≤ armT ρ i k) : False := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  have hGpos : 0 < dG.val := by
    rcases Nat.eq_zero_or_pos dG.val with h | h
    · exfalso
      have hz : dG = (⟨0, by omega⟩ : Fin (n - i.val)) := Fin.ext (by omega)
      have h0 : armG ρ i (⟨0, by omega⟩ : Fin (n - i.val)) = ρ i := rfl
      rw [hz, h0, hp] at hG
      omega
    · exact h
  have htv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
  have hgv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
  refine no_low_gap' hcr L ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩
    (show i.val - dT.val < i.val + dG.val by omega) (by rw [← htv]; exact hT)
    (by rw [← hgv]; exact hG) ?_
  intro r hr1' hr2'
  have hr1 : i.val - dT.val < r.val := hr1'
  have hr2 : r.val < i.val + dG.val := hr2'
  rcases Nat.lt_or_ge i.val r.val with hri | hri
  · have := hGmid ⟨r.val - i.val, by omega⟩ (by simp; omega)
    rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this
  · have := hTmid ⟨i.val - r.val, by omega⟩ (by simp; omega)
    rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri] at this

/-! ## The two work items, in the thin form of the model

In the thin form `σ = ρ` of the faithful model every link is a point, and the crookedness clause
says more than `CrookUp` does: the intermediate link *meets* the level `k - 1` exactly, so in the
thin form it stands there. That one level is the whole difference, and it settles both work items:
each reduces to a configuration across the basepoint in which the clause produces a time at
`L + 7` (respectively `L + 6`) where the hypotheses allow at most `L + 6` (respectively `L + 5`).

In the general model the same application produces a link with `ρ = L + 6` and `σ = L + 7`, which
nothing so far excludes; that is where the two work items are still open, and it is the first
place in this development where the thin form is doing work. -/

/-- **The ceiling configuration is impossible on a thin sequence.** Reading the times of the two
arms as times of the sequence: `t` before the basepoint `c` at `L + 1` or below, with the arm at
`L + 6` or below in between; `g` after it at `L + 8` or above, with the sequence at `L + 2` or
above in between and with no time at `L + 7` or above followed, before `g`, by one at `L + 2` or
below. The crookedness clause between `t` and `g` puts a time at `L + 7` and, after it, one at
`L + 2`, and both sides of the basepoint forbid that. -/
theorem cross_ceiling_thin {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hthin : ∀ u, σ u = ρ u) (L : ℤ) (t c g : Fin n)
    (htc : t.val < c.val) (hcg : c.val ≤ g.val)
    (ht : ρ t ≤ L + 1) (hg : L + 8 ≤ ρ g)
    (hmid : ∀ r : Fin n, t.val < r.val → r.val < g.val → L + 2 ≤ ρ r)
    (hTtop : ∀ r : Fin n, t.val < r.val → r.val < c.val → ρ r ≤ L + 6)
    (hnopat : ∀ r r' : Fin n, c.val ≤ r.val → r.val < r'.val → r'.val < g.val →
      L + 7 ≤ ρ r → L + 2 < ρ r') : False := by
  have htg : t.val < g.val := by omega
  by_cases hfloor : ρ t ≤ L
  · exact no_low_gap hcr L t g htg hfloor (by omega) hmid
  · obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
      hcr.crooked t g (Fin.lt_def.mpr htg) (L + 1) (ρ g)
        ⟨t, by simp, by omega, by rw [hthin]; omega⟩
        ⟨g, by simp, by omega, by rw [hthin]⟩
        (by rw [abs_of_nonpos] <;> omega)
    obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
    rw [hthin] at hr2 hr'2
    have hrv : L + 7 ≤ ρ r := by omega
    have hr'v : ρ r' = L + 2 := by omega
    have h1' : t.val < r.val := h1
    have h2' : r.val < r'.val := h2
    have h3' : r'.val < g.val := h3
    rcases lt_or_ge r.val c.val with hrc | hrc
    · exact absurd (hTtop r h1' hrc) (by omega)
    · exact absurd (hnopat r r' hrc h2' h3' (by omega)) (by omega)

/-- **The valley configuration is impossible on a thin sequence.** Its counterpart: `s` before
the basepoint `c` at `L + 1` or below, with the arm at `L + 5` or below in between; `e` after it
at `L + 7` or above, with the sequence at `L + 2` or above in between and at `L + 3` or above
from the step four of the forward arm on. The clause between `s` and `e` puts a time at `L + 6`
and, after it, one at `L + 2`: before the basepoint the first is too high, and after it the two
are four levels apart and at most three steps apart. -/
theorem cross_valley_thin {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hthin : ∀ u, σ u = ρ u) (hlip : IsLip ρ) (L : ℤ) (s c e : Fin n)
    (hsc : s.val < c.val) (hce : c.val ≤ e.val)
    (hs : ρ s ≤ L + 1) (he : L + 7 ≤ ρ e)
    (hmid : ∀ r : Fin n, s.val < r.val → r.val < e.val → L + 2 ≤ ρ r)
    (hTtop : ∀ r : Fin n, s.val < r.val → r.val < c.val → ρ r ≤ L + 5)
    (hGno : ∀ r : Fin n, c.val + 4 ≤ r.val → r.val < e.val → L + 3 ≤ ρ r) : False := by
  have hse : s.val < e.val := by omega
  by_cases hfloor : ρ s ≤ L
  · exact no_low_gap hcr L s e hse hfloor (by omega) hmid
  · obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
      hcr.crooked s e (Fin.lt_def.mpr hse) (L + 1) (ρ e)
        ⟨s, by simp, by omega, by rw [hthin]; omega⟩
        ⟨e, by simp, by omega, by rw [hthin]⟩
        (by rw [abs_of_nonpos] <;> omega)
    obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
    rw [hthin] at hr2 hr'2
    have hrv : L + 6 ≤ ρ r := by omega
    have hr'v : ρ r' = L + 2 := by omega
    have h1' : s.val < r.val := h1
    have h2' : r.val < r'.val := h2
    have h3' : r'.val < e.val := h3
    rcases lt_or_ge r.val c.val with hrc | hrc
    · exact absurd (hTtop r h1' hrc) (by omega)
    · have hr'c : r'.val < c.val + 4 := by
        by_contra hcon
        exact absurd (hGno r' (by omega) h3') (by omega)
      have hstep := abs_sub_le_of_isLip hlip (r'.val - r.val) r r' (by omega)
      rw [abs_le] at hstep
      have hcast : ((r'.val - r.val : ℕ) : ℤ) ≤ 3 := by
        have : r'.val - r.val ≤ 3 := by omega
        exact_mod_cast this
      omega

/-! ## The third walk, with a criterion of its own

`HPC/Fold/Leg3Deep.lean` folds an arm based at `L + 4` onto the three-leg walk

```
L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1, L+2, L+3, L+4, L+5, L+6, L+7, L+8
```

— `leg3Walk L (L+9) (L+6) (L+4)`, the walk `L+3 → L+6 → L+1 → L+8` that the censuses of batches
43 and 44 find serving every pair of the branch that the Λ-walk and the V-walk miss. The engine
asks two announcements of the arm; at these parameters the second one is free, because
crookedness supplies it from the branch hypothesis in its `HighAt f L (L + 8)` form:

* **valley.** Every descent to `L + 1` is preceded by a time at `L + 6` or above, or by a time at
  `L + 1` or below followed by one at `L + 5` or above. (The Λ-announcement `LamAnn` implies it.)
* **ceiling.** Every ascent to `L + 8` is announced. This is `valleyBranch_ceiling`: a time at
  `L + 1` or below before the ascent, which `HighAt f L (L + 8)` gives, and one application of
  the crookedness clause between it and the ascent. -/

/-- **The ceiling announcement of the three-leg walk.** The hypothesis `foldsOnto_leg3_deep` asks
of an arm at the ceiling, read at `K = L + 6`: before an ascent to `L + 8` the arm has been at
`L` or below; or at `L + 7` or above and after that at `L + 2` or below; or at `L + 1` or below,
then at `L + 6` or above, then at `L + 2` or below. -/
def CeilAnn {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d →
    (∃ k : Fin m, k.val < d.val ∧ f k ≤ L) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 7 ≤ f k ∧ f k' ≤ L + 2) ∨
    (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
      f k ≤ L + 1 ∧ L + 6 ≤ f k' ∧ f k'' ≤ L + 2)

/-- **The ceiling announcement, from a time at the floor before every ascent.** If every ascent
of the arm to `L + 8` is preceded by a time at `L + 1` or below, the clause `CrookUp` fills in
the rest: between that time and the ascent the arm stands at `L + 6` or above and, after that,
at `L + 2` or below. The converse fails, and that is what the counterexample of this batch turns
on: the announcement is strictly weaker than `HighAt f L (L + 8)`. -/
theorem valleyBranch_ceiling {m : ℕ} {f : Fin m → ℤ} (hcr : CrookUp f) (L : ℤ)
    (hhigh : HighAt f L (L + 8)) : CeilAnn f L := by
  intro d hd
  obtain ⟨e, he, hef⟩ := hhigh d (by omega)
  obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
    hcr.levels (L + 1) (L + 8) (by omega) e d he (by omega) (by omega)
  exact Or.inr (Or.inr ⟨e, u, u', h1, h2, h3, by omega, by omega, by omega⟩)

/-- **An arm of the branch folds onto the third walk.** A 1-Lipschitz crooked arm based at
`L + 4` in the band `[L, L + 9]` whose descents to `L + 1` are announced, and every one of whose
ascents to `L + 8` is announced, folds onto `leg3Walk L (L + 9) (L + 6) (L + 4)`. -/
theorem foldsOnto_leg3deep_branch {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 6 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k'))
    (hceil : CeilAnn f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) := by
  refine foldsOnto_leg3_deep hm f hf L (L + 9) (L + 6) (L + 4) (by omega) (by omega) (by omega)
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

/-- **The third walk serves a pair.** Both arms of a basepoint at `L + 4` whose descents to
`L + 1` are announced and whose ascents to `L + 8` are preceded by a time at `L + 1` or below
fold onto the common walk `L+3 → L+6 → L+1 → L+8`. This is the configuration that the two
canonical walks leave open; no engine in the repository before `HPC/Fold/Leg3Deep.lean` produces
a walk with its valley at `L + 1` and its basepoint at `L + 4`. -/
theorem s3_span_nine_mid4_of_valley {n : ℕ} {ρ : Fin n → ℤ} (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hvG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      (∃ k : Fin (n - i.val), k.val < d.val ∧ L + 6 ≤ armG ρ i k) ∨
      (∃ k k' : Fin (n - i.val), k.val < k'.val ∧ k'.val < d.val ∧
        armG ρ i k ≤ L + 1 ∧ L + 5 ≤ armG ρ i k'))
    (hvT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      (∃ k : Fin (i.val + 1), k.val < d.val ∧ L + 6 ≤ armT ρ i k) ∨
      (∃ k k' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
        armT ρ i k ≤ L + 1 ∧ L + 5 ≤ armT ρ i k'))
    (hhG : CeilAnn (armG ρ i) L) (hhT : CeilAnn (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  refine ⟨leg3Len L (L + 9) (L + 6) (L + 4), leg3Walk L (L + 9) (L + 6) (L + 4), ?_, ?_⟩
  · exact foldsOnto_leg3deep_branch hmG (armG ρ i) (armG_isLip hlip i) L
      hG0 (fun j => hLb _) (fun j => hHb _) hvG hhG
  · exact foldsOnto_leg3deep_branch hmT (armT ρ i) (armT_isLip hlip i) L
      hT0 (fun j => hLb _) (fun j => hHb _) hvT hhT

/-! ## The branch `L + 4`, reduced to the pairs the two canonical walks miss

`s3_span_nine_mid_low_of_lam` and `s3_span_nine_mid_low_of_floor` serve a pair as soon as both
arms announce the same way, and `arm_lam_or_vee` says each arm announces at least one way; so
what is left is the mixed configuration, and there the third walk is available. Its two
hypotheses are *not* consequences of the branch: over the census corpus a quarter of all branch
arms fail each of them. They are consequences — over 20 493 unserved pairs of `census-batch45.c`,
without an exception — of the pair being served by *neither* canonical walk, and that is how the
two work items below are stated. The exact criteria for the two canonical walks are
`foldsOnto_lam_iff_profile` and `foldsOnto_vee_iff_profile`, so the hypotheses `hnotLam`,
`hnotVee` are decidable data about the two arms, not an extra assumption on the sequence.

Which announcement the ceiling item asks matters: with `HighAt f L (L + 8)` in place of `CeilAnn`
the item is false (`not_unservedHigh8`), and with `CeilAnn` the census finds no failure.

`valley_or_vee` and `ceiling_or_lam` cut each work item in half: an arm that fails the valley
announcement is itself served by the V-walk, and an arm that fails the ceiling announcement is
itself served by the Λ-walk. So neither failure can be blamed on the arm that exhibits it, and
what is left in each work item is that the *other* arm then also folds onto that walk — a
statement across the basepoint, of the kind `crookUp_seq`, `cross_floor_excluded` and
`mix_events_far` are there for. `cross_floor_excluded` settles it when the descending arm reaches
the floor `L`; over the census the remaining case always has a time at `L + 2` inside the window,
so one application of the clause does not finish it. -/

/-- The Λ-announcement gives the valley announcement of the third walk. -/
theorem lamAnn_valley {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : LamAnn f L) (d : Fin m)
    (hd : f d ≤ L + 1) :
    (∃ k : Fin m, k.val < d.val ∧ L + 6 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k') := by
  obtain ⟨j, hj, hjf⟩ := h d hd
  exact Or.inl ⟨j, hj, by omega⟩

/-- The V-announcement gives the ceiling hypothesis of the third walk. -/
theorem veeAnn_high8 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : VeeAnn f L) : HighAt f L (L + 8) := by
  intro d hd
  obtain ⟨j, hj, hjf⟩ := h d (by omega)
  exact ⟨j, hj, by omega⟩

/-- **An arm that fails the valley announcement is served by the V-walk.** If the arm stands at
`L + 1` or below at a time before which it has never been at `L + 6`, it folds onto the V-walk
based at `L + 5`: that time is itself the valley witness the descent profile asks for, and the
timing law `crookDown_fall3` puts it at index four or later. So the obstruction to the valley
announcement never lies with the arm that fails it — it lies with the other arm of the pair. -/
theorem foldsOnto_vee_of_valley_fail {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (d0 : Fin m) (hd0 : f d0 ≤ L + 1) (hno : ∀ k : Fin m, k.val < d0.val → f k ≤ L + 5) :
    FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  refine (foldsOnto_vee_iff_profile hm f hf (L + 5) (L + 9) L (by omega)
    (by rw [h0, abs_le]; omega) hL hH).mpr ?_
  rw [critVeeProfile_iff_of_isLip hf (L + 5) L (by omega)]
  intro d hd
  have hdd0 : d0.val < d.val := by
    rcases lt_trichotomy d.val d0.val with h | h | h
    · exact absurd (hno d h) (by omega)
    · exact absurd (congrArg f (Fin.ext h : d = d0)) (by omega)
    · exact h
  have hzero : 0 < d0.val := by
    rcases Nat.eq_zero_or_pos d0.val with h | h
    · exact absurd (congrArg f (Fin.ext h : d0 = (⟨0, hm⟩ : Fin m))) (by omega)
    · exact h
  have hfall := crookDown_fall3 hf hcrd ⟨0, hm⟩ d0 (by simpa using hzero) (by omega)
  simp only at hfall
  exact ⟨d0, hdd0, by omega, by omega⟩

/-- **An arm with an unannounced ascent to `L + 8` is served by the Λ-walk.** If the arm stands
at `L + 8` at a time before which it has never been at `L + 1`, it folds onto the Λ-walk based at
`L + 3`: that time is the peak witness the ascent profile asks for, and `crookUp_climb4` puts it
at index seven or later. -/
theorem foldsOnto_lam_of_high8_fail {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcru : CrookUp f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (d0 : Fin m) (hd0 : L + 8 ≤ f d0) (hno : ∀ k : Fin m, k.val < d0.val → L + 2 ≤ f k) :
    FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  refine foldsOnto_lam_of_profile hm f hf (L + 3) (L + 9) L (by omega)
    (by rw [h0, abs_le]; omega) hL hH ?_
  have hk : κ (L + 3) (L + 9) = L + 8 := by simp only [κ]; omega
  rw [critLamProfile_iff_of_isLip hf, hk]
  intro d hd
  have hdd0 : d0.val < d.val := by
    rcases lt_trichotomy d.val d0.val with h | h | h
    · exact absurd (hno d h) (by omega)
    · exact absurd (congrArg f (Fin.ext h : d = d0)) (by omega)
    · exact h
  have hzero : 0 < d0.val := by
    rcases Nat.eq_zero_or_pos d0.val with h | h
    · exact absurd (congrArg f (Fin.ext h : d0 = (⟨0, hm⟩ : Fin m))) (by omega)
    · exact h
  have hclimb := crookUp_climb4 hf hcru ⟨0, hm⟩ d0 (by simpa using hzero) (by omega)
  simp only at hclimb
  exact ⟨d0, hdd0, by omega, by omega⟩

/-- **Each arm either announces its descents to `L + 1` or is served by the V-walk.** Whichever
way an arm goes, it offers one of the two walks something: the announcement the third walk needs,
or a fold onto the V-walk. -/
theorem valley_or_vee {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcrd : CrookDown f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    (∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 6 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k')) ∨
    FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  by_cases hex : ∃ d0 : Fin m, f d0 ≤ L + 1 ∧ ∀ k : Fin m, k.val < d0.val → f k ≤ L + 5
  · obtain ⟨d0, hd0, hno⟩ := hex
    exact Or.inr (foldsOnto_vee_of_valley_fail hm f hf hcrd L h0 hL hH d0 hd0 hno)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨k, hk, hkf⟩ := hex d hd
    exact Or.inl ⟨k, hk, by omega⟩

/-- **Each arm either has a time at `L + 1` before every ascent to `L + 8`, or is served by the
Λ-walk.** -/
theorem high8_or_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    HighAt f L (L + 8) ∨
    FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  by_cases hex : ∃ d0 : Fin m, L + 8 ≤ f d0 ∧ ∀ k : Fin m, k.val < d0.val → L + 2 ≤ f k
  · obtain ⟨d0, hd0, hno⟩ := hex
    exact Or.inr (foldsOnto_lam_of_high8_fail hm f hf hcru L h0 hL hH d0 hd0 hno)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨k, hk, hkf⟩ := hex d (by omega)
    exact ⟨k, hk, by omega⟩

/-- **An arm with an unannounced ascent to `L + 8` is served by the Λ-walk.** The ceiling
announcement of the three-leg walk fails at a time `d₀` only if the arm has never been at `L + 1`
or below before `d₀`: a time there would, by one application of the crookedness clause between it
and `d₀`, supply the announcement's third clause. So every descent to `L + 1` comes after `d₀`,
and `d₀` itself is the peak witness the ascent profile asks for; `crookUp_climb4` puts it at
index seven or later. -/
theorem foldsOnto_lam_of_ceil_fail {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcru : CrookUp f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (d0 : Fin m) (hd0 : L + 8 ≤ f d0)
    (hno : ¬ ∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d0.val ∧
      f k ≤ L + 1 ∧ L + 6 ≤ f k' ∧ f k'' ≤ L + 2) :
    FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  have hafter : ∀ d : Fin m, f d ≤ L + 1 → d0.val < d.val := by
    intro d hd
    rcases lt_trichotomy d.val d0.val with h | h | h
    · exfalso
      obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
        hcru.levels (L + 1) (L + 8) (by omega) d d0 h hd hd0
      exact hno ⟨d, u, u', h1, h2, h3, hd, by omega, by omega⟩
    · exact absurd (congrArg f (Fin.ext h : d = d0)) (by omega)
    · exact h
  have hzero : 0 < d0.val := by
    rcases Nat.eq_zero_or_pos d0.val with h | h
    · exact absurd (congrArg f (Fin.ext h : d0 = ( ⟨0, hm⟩ : Fin m))) (by omega)
    · exact h
  refine foldsOnto_lam_of_profile hm f hf (L + 3) (L + 9) L (by omega)
    (by rw [h0, abs_le]; omega) hL hH ?_
  have hk : κ (L + 3) (L + 9) = L + 8 := by simp only [κ]; omega
  rw [critLamProfile_iff_of_isLip hf, hk]
  intro d hd
  have hclimb := crookUp_climb4 hf hcru ⟨0, hm⟩ d0 (by simpa using hzero) (by omega)
  simp only at hclimb
  exact ⟨d0, hafter d (by omega), by omega, by omega⟩

/-- **Each arm either announces its ascents to `L + 8` or is served by the Λ-walk.** The ceiling
counterpart of `valley_or_vee`, and the replacement for `high8_or_lam`: what the three-leg walk
asks at the ceiling is `CeilAnn`, not `HighAt f L (L + 8)`, and an arm failing `CeilAnn` folds
onto the Λ-walk. -/
theorem ceiling_or_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    CeilAnn f L ∨ FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  by_cases hex : ∃ d0 : Fin m, L + 8 ≤ f d0 ∧
      ¬ ∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d0.val ∧
        f k ≤ L + 1 ∧ L + 6 ≤ f k' ∧ f k'' ≤ L + 2
  · obtain ⟨d0, hd0, hno⟩ := hex
    exact Or.inr (foldsOnto_lam_of_ceil_fail hm f hf hcru L h0 hL hH d0 hd0 hno)
  · push_neg at hex
    exact Or.inl (fun d hd => Or.inr (Or.inr (hex d hd)))

-- Commented-out statement `unserved_high8` removed in batch 103; see `LEDGER.md`.
-- Commented-out statement `unserved_ceiling`, `unserved_valley` removed in batch 103; see `LEDGER.md`.

/-! ## The work item of the branch `L + 4`, batch 47: the third walk serves every unserved pair

A pair of the branch that folds onto neither canonical walk has *both* arms folding onto the
third walk `L+3 → L+6 → L+1 → L+8` itself — not onto some walk of at most three legs chosen pair
by pair, and with no announcement in between.

This is the statement the refutations of batch 46 leave standing. What they refuted are the two
announcements through which `s3_span_nine_mid4_of_valley` reached this conclusion; the conclusion
itself is exactly what the walk of `HPC/Fold/Leg3Deep.lean` delivers, and the census
`census-batch47b.c` — over general pairs, generated as shavings of `bing 0 9`, verified against
`IsCrookedIvF` and with every fold decided by the dynamic program over `FoldsOnto` — finds it
holding at all 6 340 unserved branch basepoints of the 288 single shavings and at all 451 of
twenty random multiple shavings, the two refuting basepoints of batch 46 among them. No basepoint
of any census in this repository refutes it.

It splits in two. The first half is a statement about arms alone,
`foldsOnto_leg3deep_profile` (`HPC/Fold/Leg3Profile.lean`): the announcements
`foldsOnto_leg3_deep` asks are sufficient and not necessary, because they ask for a time *at* the
peak level `L + 6` where the walk's window tolerance of one means that a time at `L + 5`, late
enough, would do — the same one level by which the general crookedness clause falls short of the
thin one. That half is a **theorem** since batch 48. The second is `unserved_profile` below: an
unserved pair meets the lowered clauses.

## What batch 48 leaves

The second half splits again, and the split is exact. `leg3Valley_or_vee` and `leg3Ceil_or_lam`
(`HPC/Fold/Leg3Profile.lean`) say that an arm *failing* a profile clause is itself served by a
canonical walk: an arm that fails `Leg3Valley` folds onto the V-walk, an arm that fails
`Leg3Ceil` onto the Λ-walk. Two consequences, and they are the shape of what is left.

* Unconditionally (`unserved_profile_one`): at least one arm of an unserved pair satisfies
  `Leg3Valley`, and at least one satisfies `Leg3Ceil`. If both arms failed the same clause, both
  would fold onto the same canonical walk, and the pair would be served by it.
* What remains is therefore a statement *across the basepoint*, and only that: if one arm fails
  a clause, so that it is served by one of the two canonical walks alone, the other arm is served
  by the same walk. That is `cross_valley_profile` and `cross_ceil_profile` below, the two work
  items this batch leaves, and `unserved_profile` is a derivation from them. Neither says anything
  about the arm that fails; both are of the kind `crookUp_seq`, `cross_floor_excluded` and
  `mix_events_far` are there for. -/

/-- **The first cross work item.** If either arm of the pair fails the valley clause, then *both*
arms fold onto the V-walk based at `L + 5`.

The arm that fails does so by `leg3Valley_or_vee`, with no hypothesis on the pair; what the item
asks is that the failure crosses the basepoint. Over the census corpus of `census-batch47b.c` no
unserved pair has an arm failing the clause at all, so the item is never called on there.

Batch 50 reduced the item to one configuration: `cross_valley_dichotomy`
(`HPC/Fold/CrossValley.lean`) proves that either the conclusion holds or the sequence stands at
`L + 2` two or three steps to one side of the basepoint, so the item was a theorem for every pair
avoiding that (`cross_valley_profile_of_not_residual`).

**Batch 56 proves it.** The residual configuration is not an obstruction: reading the crookedness
clause between the failing descent and the ascent and pinning the two links it returns with the
timing law of Theorem 7 (`minGap`) puts the witness the V-criterion asks for ten steps past the
basepoint, so there is nothing to except. The work is `cross_valley_vee_pair`
(`HPC/Fold/ValleyFar.lean`); of the hypotheses below, the two `HighAt` clauses, the Lipschitz
hypothesis (which `IsCrookedIvF` implies) and the two attainment hypotheses are not used. -/
theorem cross_valley_profile {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hLat : ∃ t, ρ t = L) (hHat : ∃ t, ρ t = L + 9)
    (hp : ρ i = L + 4) (hG : HighAt (armG ρ i) (L + 1) (L + 8))
    (hT : HighAt (armT ρ i) (L + 1) (L + 8))
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) :=
  cross_valley_vee_pair ρ σ i L hcr hLb hHb hp hfail

-- Commented-out statement `cross_ceil_profile` removed in batch 103; see `LEDGER.md`.

/-- **One arm of an unserved pair satisfies each profile clause.** Unconditionally: an unserved
pair has an arm satisfying `Leg3Valley` and an arm satisfying `Leg3Ceil` — possibly different
arms, which is exactly the gap the two cross work items fill. If both arms failed the valley
clause both would fold onto the V-walk, and if both failed the ceiling clause both would fold
onto the Λ-walk. -/
theorem unserved_profile_one {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)))
    (hnotVee : ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L))) :
    (Leg3Valley (armG ρ i) L ∨ Leg3Valley (armT ρ i) L) ∧
      (Leg3Ceil (armG ρ i) L ∨ Leg3Ceil (armT ρ i) L) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  constructor
  · rcases leg3Valley_or_vee hmG (armG ρ i) (armG_isLip hlip i) (crookDown_armG hcr i) L hG0
      (fun j => hLb _) (fun j => hHb _) with h | hvG
    · exact Or.inl h
    · rcases leg3Valley_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
        (fun j => hLb _) (fun j => hHb _) with h | hvT
      · exact Or.inr h
      · exact absurd ⟨hvG, hvT⟩ hnotVee
  · rcases leg3Ceil_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
      (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with h | hlG
    · exact Or.inl h
    · rcases leg3Ceil_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with h | hlT
      · exact Or.inr h
      · exact absurd ⟨hlG, hlT⟩ hnotLam

-- Commented-out statement `unserved_profile`, `unserved_leg3deep` removed in batch 103; see `LEDGER.md`.

/-! ## The branch `L + 4`, batch 49: three walks, not one

What the refutation leaves is not that the branch is false but that one walk is not enough. The
basepoint `336` of `bing9sB` is served — by `L+3 → L+2 → L+8 → L+1`, the reflection of the third
walk — and `census-batch49c.c` asks the question over the corpus of `census-batch49b.c`: at the
98 611 unserved branch basepoints of the two thin chains, their 576 single shavings, their 576
single fills and 800 random mixtures, every pair folds onto one of

* `w₃ = L+3 → L+6 → L+1 → L+8` (`leg3Walk L (L+9) (L+6) (L+4)`, sixteen times) — 98 254 pairs;
* `w₄ = L+3 → L+2 → L+8 → L+1` (`leg3Walk' L (L+9) (L+7) (L+2)`, fifteen times) — the reflection
  of `w₃`; it serves 318 of the 357 pairs `w₃` misses;
* `w₅ = L+3 → L+7 → L+1 → L+8` (`leg3Walk L (L+9) (L+7) (L+4)`, eighteen times) — the third walk
  with its peak one level higher; it serves the remaining 39, and 90 764 of the 98 611 in all.

No pair of any census in this repository folds onto none of the three. -/

/-- **The branch `L + 4`: three walks serve every unserved pair.** A pair of the branch that folds
onto neither canonical walk folds onto one of the three walks `w₃`, `w₄`, `w₅` above — both arms
onto the same one. This replaces `unserved_leg3deep`, which asked it of `w₃` alone and is false.

**Batch 56 proves it**, from the two crossings: the valley crossing `cross_valley_vee_pair`
(`HPC/Fold/ValleyFar.lean`) and the ceiling crossing `cross_ceil_sentence_far`
(`HPC/Fold/CeilFar.lean`), assembled in `unserved_three_walks_far` (`HPC/Fold/Unserved.lean`).
With it `s3_span_nine_mid4` below is complete.

Batch 51 gives each of the three walks an exact criterion (`foldsOnto_leg3deep_iff_landmark`,
`foldsOnto_w4_iff_landmark`, `foldsOnto_w5_iff_landmark`), so the conclusion below is equivalent to
the disjunction of three landmark sentences about the levels of the two arms
(`three_walks_iff_sentence`, `HPC/Fold/ThreeWalks.lean`): what the item asks is
`ThreeWalksSentence (armG ρ i) (armT ρ i) L`, and with it the branch is complete
(`s3_span_nine_mid4_of_sentence`). -/
theorem unserved_three_walks {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hLat : ∃ t, ρ t = L) (hHat : ∃ t, ρ t = L + 9)
    (hp : ρ i = L + 4) (hG : HighAt (armG ρ i) (L + 1) (L + 8))
    (hT : HighAt (armT ρ i) (L + 1) (L + 8))
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
        (leg3Walk L (L + 9) (L + 7) (L + 4))) :=
  unserved_three_walks_far ρ σ i L hlip hcr hLb hHb hp hnotLam hnotVee

/-- **The branch `L + 4`, ends attained.** `key4` of `s3_span_nine_of_mid`.

Batch 44 reduced this to two work items and batch 45 re-split it on `CeilAnn`; batch 46 refuted
both items in the general model, batch 47 re-split it on `unserved_leg3deep` — the third walk
serves every unserved pair — and batch 49 refuted that too. The branch rests on
`unserved_three_walks` above: an unserved pair folds onto one of three named walks. Since batch 56
that is a theorem, so the branch is complete, and the case analysis below is all there is to it.

What is known otherwise: for a thin sequence the branch is a theorem (`s3_span_nine_mid4_thin`,
`HPC/Fold/MixedThin.lean`). -/
theorem s3_span_nine_mid4 {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hLat : ∃ t, ρ t = L) (hHat : ∃ t, ρ t = L + 9)
    (hp : ρ i = L + 4) (hG : HighAt (armG ρ i) (L + 1) (L + 8))
    (hT : HighAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hlam : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)
  · exact ⟨_, _, hlam.1, hlam.2⟩
  · by_cases hvee : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)
    · exact ⟨_, _, hvee.1, hvee.2⟩
    · rcases unserved_three_walks ρ σ i L hlip hcr hLb hHb hLat hHat hp hG hT hlam hvee with
        ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩ | ⟨hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩
      · exact ⟨_, _, hfG, hfT⟩

-- Commented-out statement `s3_span_nine_mid5`, `s3_span_nine'` removed in batch 103; see `LEDGER.md`.


end HPC.Fold
