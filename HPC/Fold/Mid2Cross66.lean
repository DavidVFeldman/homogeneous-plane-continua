import HPC.Fold.CrossMid2Fail65

/-!
# What a failure of `Mid2Floor` costs, and what it buys

Batch 65 refuted `CrossMid2L5` and restated the residue of the branch `L + 5` as `CrossMid2L5'`,
the same sentence with the crossing of the trichotomy written out. Two things were left as
measurements there, and this file proves both, and then measures the residue itself against the
arms alone.

## The peak lies on the `w8` side — as a theorem

The batch-65 census reports that at a descent of the partner to exactly `L + 2` at which
`Mid2Floor` fails, the peak the crooked pairing produces lies on the `w8` side and never on the
partner's. That is not an accident of the corpus: the failure of `Mid2Floor` *is* the hypothesis
`cross_peak_valley_armG'` needs. `Mid2Floor` fails at a descent `d` exactly when the arm has no
time at `L + 6` or above at arm index three or more and four steps before `d`; the pairing asks
for no time at `L + 7` or above at arm index four or more and seven steps before `d`, a weaker
demand on a smaller window (`mid2Fail_window`). So

* `crossMid2_peak_on_w8_side` — if the backward arm fails `Mid2Floor`, then at **every** ascent of
  the forward arm to `L + 9` the crooked peak (`L + 7` or above) and the crooked valley (`L + 3`
  or below) are times of the *forward* arm, the peak at arm index five or more, the valley
  twenty-nine steps after it and seventy steps before the ascent;
* `crossMid2_peak_on_w8_side_T` — the mirror, with the two arms exchanged.

## The failure buys the fifth walk on the other side

The same hypothesis is what `leg4Land_w72_of_cross_of_floor_fail` wants, so the failure of the
residue on one arm pays for the other arm's fifth walk in full:

* `leg4Land_w72_of_mid2fail_armT` — in a band that misses the floor, if the backward arm fails
  `Mid2Floor` and the forward arm is served by `w8`, then the forward arm is served by
  `w72 = L+4 → L+7 → L+2 → L+8 → L+1` as well;
* `leg4Land_w72_of_mid2fail_armG` — the mirror.

This cannot by itself close the branch, because the arm that fails `Mid2Floor` is served by
*neither* `w72` nor `w71` nor `w8` (`mid2Floor_of_leg4Land`, batch 65): what the failure buys is a
walk for the other arm only. What it does give is the dichotomy `s3_span_nine_mid5_cross_dich`:
at a basepoint of the branch whose forward arm is served by `w8`, either the partner satisfies
`Mid2Floor` — and then the batch-64 chain applies to it — or the forward arm is served by `w72`.
And `mid2Fail_w3_or_wb` places the failing arm: by the trichotomy it is served by `w3` or by `wb`,
the two reflected walks, which is the tag the census reports for all 310 028 failing arms.

## The residue is not an arm-only fact

`CrossMid2L5'` quantifies over a crooked pair, and it has to. The same sentence read over two
*independent* arms — each 1-Lipschitz, inside the band `[L, L + 9]`, based at `L + 5`, with the
branch hypothesis `LowAt (L + 1) (L + 8)`, and with no one of the three walks of `leg4Land_tri`
serving both — is **false** (`ArmCrossMid2L5`, `not_armCrossMid2L5`). The witness is a pair of
very short arms,

```
g = 5 6 7 8 9        the `w8` side: it never descends, so `w3` and `wb` both fail on it
f = 5 4 3 4 3 2      the partner: it stands at `L + 2` at index five, where `Mid2Floor` asks for
                     a landmark at an index in `[3, 1]`
```

so that all three crossing clauses hold — `f` fails `w8`, `g` fails `w3` and `g` fails `wb` — while
`f` fails `Mid2Floor`. The two arms cannot be the two arms of a crooked basepoint (`g` rises seven
levels monotonically, and crookedness forbids that), which is exactly the point: any proof of
`CrossMid2L5'` must read the pairing between the arms and not each arm on its own. The census of
batch 65 says the same thing numerically — 308 258 basepoints of the corpus have one arm failing
`Mid2Floor` and the other served by `w8`, and none of them is a crossing.
-/

namespace HPC.Fold

/-! ## The window a failure of `Mid2Floor` leaves empty -/

/-- **A failure of `Mid2Floor` at a descent `d` empties the pairing's window.** `Mid2Floor` asks
at `d` for a time at `L + 6` or above at arm index three or more and four steps earlier; the
crooked pairing asks for no time at `L + 7` or above at arm index four or more and seven steps
earlier. The second window is contained in the first, and the second level is higher. -/
theorem mid2Fail_window {m : ℕ} {f : Fin m → ℤ} {L : ℤ} {d : Fin m}
    (hno : ¬ ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 4 ≤ (d.val : ℤ) ∧ L + 6 ≤ f j) :
    ∀ j : Fin m, 4 ≤ j.val → j.val + 7 ≤ d.val → f j ≤ L + 6 := by
  intro j h4 h7
  by_contra hc
  exact hno ⟨j, by omega, by omega, by omega⟩

/-- **The descent at which `Mid2Floor` fails, with the window written out.** -/
theorem mid2Fail_witness {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ¬ Mid2Floor f L) :
    ∃ d : Fin m, f d = L + 2 ∧
      (∀ j : Fin m, 4 ≤ j.val → j.val + 7 ≤ d.val → f j ≤ L + 6) ∧
      ¬ ∃ j : Fin m, 4 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧ L + 7 ≤ f j := by
  classical
  unfold Mid2Floor at h
  push_neg at h
  obtain ⟨d, hd, hno⟩ := h
  have hno' : ¬ ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 4 ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
    rintro ⟨j, h1, h2, h3⟩
    exact absurd (hno j h1 h2) (by omega)
  refine ⟨d, hd, mid2Fail_window hno', ?_⟩
  rintro ⟨j, h1, h2, h3⟩
  exact hno' ⟨j, by omega, by omega, by omega⟩

/-! ## The peak of the crossing pair is a time of the `w8` side -/

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The crooked peak and valley lie on the forward arm.** If the backward arm fails `Mid2Floor`,
then at every ascent of the forward arm to `L + 9` the pairing's peak — at `L + 7` or above, arm
index five or more — and its valley — at `L + 3` or below, twenty-nine steps later and seventy
steps before the ascent — are times of the *forward* arm. This is the census observation of
batch 65 §2.1 as a theorem: no reading of the pairing can place the peak on the partner. -/
theorem crossMid2_peak_on_w8_side (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armT ρ i) L)
    (dG : Fin (n - i.val)) (hG : L + 9 ≤ armG ρ i dG) :
    ∃ R R' : Fin (n - i.val), 5 ≤ R.val ∧ R.val + 29 ≤ R'.val ∧ R'.val + 70 ≤ dG.val ∧
      L + 7 ≤ armG ρ i R ∧ armG ρ i R' ≤ L + 3 := by
  obtain ⟨dT, hdT, hwin, -⟩ := mid2Fail_witness hmid
  obtain ⟨R, R', h1, h2, h3, h4, h5⟩ :=
    cross_peak_valley_armG' hcr i L hp dT dG (by omega) hG hwin
  exact ⟨R, R', h1, h2, h3, h4, by omega⟩

/-- **The mirror: the crossing whose `w8` side is the backward arm.** -/
theorem crossMid2_peak_on_w8_side_T (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armG ρ i) L)
    (dT : Fin (i.val + 1)) (hT : L + 9 ≤ armT ρ i dT) :
    ∃ Rp Rv : Fin (i.val + 1), 5 ≤ Rp.val ∧ Rp.val + 29 ≤ Rv.val ∧ Rv.val + 70 ≤ dT.val ∧
      L + 7 ≤ armT ρ i Rp ∧ armT ρ i Rv ≤ L + 3 := by
  obtain ⟨dG, hdG, hwin, -⟩ := mid2Fail_witness hmid
  obtain ⟨Rp, Rv, h1, h2, h3, h4, h5⟩ :=
    cross_peak_valley_armT' hcr i L hp dT dG (by omega) hT hwin
  exact ⟨Rp, Rv, h1, h2, h3, h4, by omega⟩

/-! ## What the failure buys: the fifth walk on the other side -/

/-- **A partner that fails `Mid2Floor` gives the `w8` side `w72` in full.** In a band that misses
the floor, if the backward arm fails `Mid2Floor` and the forward arm is served by `w8`, then the
forward arm is served by `w72 = L+4 → L+7 → L+2 → L+8 → L+1` as well: the failure supplies, at
every ascent of the forward arm to `L + 9`, exactly the hypothesis
`leg4Land_w72_of_cross_of_floor_fail` asks for. -/
theorem leg4Land_w72_of_mid2fail_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hmid : ¬ Mid2Floor (armT ρ i) L) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  obtain ⟨dT, hdT, -, hfail⟩ := mid2Fail_witness hmid
  refine leg4Land_w72_of_cross_of_floor_fail hcr i L hp hHb hLb h8 ?_
  exact fun dG _ => ⟨dT, by omega, hfail⟩

/-- **The mirror.** -/
theorem leg4Land_w72_of_mid2fail_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hmid : ¬ Mid2Floor (armG ρ i) L) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  obtain ⟨dG, hdG, -, hfail⟩ := mid2Fail_witness hmid
  refine leg4Land_w72_of_cross_of_floor_fail_T hcr i L hp hHb hLb h8 ?_
  exact fun dT _ => ⟨dG, by omega, hfail⟩

/-- **The dichotomy at a basepoint of the branch whose forward arm is served by `w8`.** Either the
partner satisfies `Mid2Floor` — the residue `CrossMid2L5'` asserts this at a crossing, and the
batch-64 chain `leg4Land_w71_of_wb_of_mid2` runs from it — or the forward arm is served by `w72`
in full. -/
theorem s3_span_nine_mid5_cross_dich (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) :
    Mid2Floor (armT ρ i) L ∨ Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  classical
  by_cases hmid : Mid2Floor (armT ρ i) L
  · exact Or.inl hmid
  · exact Or.inr (leg4Land_w72_of_mid2fail_armT hcr i L hp hHb hLb h8 hmid)

/-! ## Where the failing arm sits in the trichotomy -/

/-- **An arm of the branch that fails `Mid2Floor` is served by `w3` or by `wb`.** By the
trichotomy it is served by one of the three walks, and `w8` implies `Mid2Floor`. This is the tag
the batch-65 census reports for every one of the 310 028 failing arms. -/
theorem mid2Fail_w3_or_wb (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hmid : ¬ Mid2Floor (armT ρ i) L) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∨
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  rcases leg4Land_tri_armT ρ i L hlip hLb hHb hp hT with h8 | h3 | hb
  · exact absurd (mid2Floor_of_leg4Land_w8 h8) hmid
  · exact Or.inl h3
  · exact Or.inr hb

end Pair

/-! ## The residue is not an arm-only fact -/

/-- **`CrossMid2L5'` read over two independent arms.** The hypotheses of the residue that are
about one arm at a time — 1-Lipschitz, inside the band, based at `L + 5`, the branch hypothesis —
together with the three crossing clauses, and the same conclusion. The pairing of the two arms by
crookedness is the one hypothesis dropped. -/
def ArmCrossMid2L5 : Prop :=
  ∀ (mG mT : ℕ) (hG0 : 0 < mG) (hT0 : 0 < mT) (g : Fin mG → ℤ) (f : Fin mT → ℤ) (L : ℤ),
    IsLip g → IsLip f →
    (∀ j, L ≤ g j) → (∀ j, g j ≤ L + 9) → (∀ j, L ≤ f j) → (∀ j, f j ≤ L + 9) →
    g ⟨0, hG0⟩ = L + 5 → f ⟨0, hT0⟩ = L + 5 →
    LowAt g (L + 1) (L + 8) → LowAt f (L + 1) (L + 8) →
    ¬ (Leg4Land g (L + 9) (L + 8) (L + 1) (L + 5) ∧
        Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) g) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) g) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4)) →
    (¬ Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor f L) ∧
      (¬ Leg4Land g (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor g L)

/-- The `w8` side of the arm-only witness: it rises from `L + 5` to `L + 9` and stops. -/
def cexG66 : Fin 5 → ℤ := ![5, 6, 7, 8, 9]

/-- The partner of the arm-only witness: it stands at `L + 2` at its index five. -/
def cexT66 : Fin 6 → ℤ := ![5, 4, 3, 4, 3, 2]

theorem cexG66_isLip : IsLip cexG66 := by unfold IsLip cexG66; decide
theorem cexT66_isLip : IsLip cexT66 := by unfold IsLip cexT66; decide

theorem cexG66_lb : ∀ j, (0 : ℤ) ≤ cexG66 j := by unfold cexG66; decide
theorem cexG66_ub : ∀ j, cexG66 j ≤ 0 + 9 := by unfold cexG66; decide
theorem cexT66_lb : ∀ j, (0 : ℤ) ≤ cexT66 j := by unfold cexT66; decide
theorem cexT66_ub : ∀ j, cexT66 j ≤ 0 + 9 := by unfold cexT66; decide

theorem cexG66_base : cexG66 ⟨0, by norm_num⟩ = 0 + 5 := by decide
theorem cexT66_base : cexT66 ⟨0, by norm_num⟩ = 0 + 5 := by decide

/-- Both arms stay above `L + 1`, so the branch hypothesis is vacuous on them. -/
theorem cexG66_lowAt : LowAt cexG66 (0 + 1) (0 + 8) := by unfold LowAt cexG66; decide
theorem cexT66_lowAt : LowAt cexT66 (0 + 1) (0 + 8) := by unfold LowAt cexT66; decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The partner fails `w8`: its descent to `L + 2` at index five has no landmark at all. -/
theorem not_w8_cexT66 : ¬ Leg4Land cexT66 (0 + 9) (0 + 8) (0 + 1) (0 + 5) := by
  unfold Leg4Land cexT66; decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The `w8` side fails `w3`: it never descends to `L + 4`, so the reflected floor clause at its
ascent to `L + 8` has no landmark. -/
theorem not_w3_cexG66 :
    ¬ Leg4Land (armRefl (0 + (0 + 9)) cexG66) (0 + 9) (0 + 6) (0 + 1) (0 + 4) := by
  unfold Leg4Land armRefl cexG66; decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- And it fails `wb`, for the same reason. -/
theorem not_wb_cexG66 :
    ¬ Leg4Land (armRefl (0 + (0 + 9)) cexG66) (0 + 9) (0 + 6) (0 + 2) (0 + 4) := by
  unfold Leg4Land armRefl cexG66; decide

/-- The partner fails `Mid2Floor`: at its index five the clause asks for a landmark at an index in
`[3, 1]`. -/
theorem not_mid2Floor_cexT66 : ¬ Mid2Floor cexT66 0 := by
  unfold Mid2Floor cexT66; decide

/-- **The residue is not an arm-only fact.** Read over two independent arms the sentence is false:
the pairing of the two arms by crookedness is what a proof of `CrossMid2L5'` has to use. -/
theorem not_armCrossMid2L5 : ¬ ArmCrossMid2L5 := by
  intro h
  exact not_mid2Floor_cexT66
    ((h 5 6 (by norm_num) (by norm_num) cexG66 cexT66 0 cexG66_isLip cexT66_isLip
        cexG66_lb cexG66_ub cexT66_lb cexT66_ub cexG66_base cexT66_base
        cexG66_lowAt cexT66_lowAt
        (fun hc => not_w8_cexT66 hc.2) (fun hc => not_w3_cexG66 hc.1)
        (fun hc => not_wb_cexG66 hc.1)).1 not_w8_cexT66)

end HPC.Fold
