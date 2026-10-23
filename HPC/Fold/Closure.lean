import HPC.Fold.Shrink

/-!
# The three conjectures: all three are false as stated, and so is `F2Prime`

**Counterexamples first, as the commission asks.** The three statements posed for this batch —
`ExitReach`, `HighExitValleyOpen`, `LowExitPeak` — are all refuted, by explicit down-crooked
1-Lipschitz sequences. So, by the same mechanism, is `F2Prime` itself, the target of the whole
reduction; `HighExitValley` falls with `HighExitValleyOpen` through `highExitValley_iff_open`.

## What goes wrong

None of the failures is about crookedness, and none contradicts the corpus evidence recorded in
earlier batches. All four statements quantify over the extremes `H` and `L` subject only to
`∀ t, L ≤ ρ t`, `∀ t, ρ t ≤ H` and `L + 3 ≤ H`. Every census — batch 16's 7 042 754 basepoints
included — was taken with `H` and `L` set to the sequence's own maximum and minimum. But a
*strict* bound is admissible in the statements, and the two sides of the dichotomy do not
degrade the same way when it is loosened:

* `hStar = min (max (max dG dT) (max p (L+1))) (max (H-1) p)` is capped at `max (H-1) p`, so
  raising `H` above `max ρ` *raises* the height the Λ side must reach, up to the true demand;
* `lStar = max (min (min lG lT) (min p (H-1))) (min (L+1) p)` is floored at `min (L+1) p`, so
  lowering `L` below `min ρ` *lowers* the depth the V side may stop at.

Tight extremes let the floor and the cap rescue whichever side is in trouble. Slack extremes
remove both protections at once, and then a single sequence can fail both sides. That is
exactly the refuting configuration below: at `ρ = 0,1,2,1,2,2,3,4`, basepoint `2`, the Λ side
fails at the backward arm because `hStar = 3` while the arm's phase-adjusted reach is `2`, and
the V side fails at the forward arm because `lStar` has dropped to `0` while the negated arm's
reach is `-1`. With `L = 0` — the true minimum — `lStar = 1` and the V side holds; with
`L = -1` it does not.

For the valley clauses the mechanism is the same one step further on: `ValleyBefore` asks for a
visit to `L + 1`, and if `L` is two below the true minimum no visit is possible, while `hStar`
is unmoved because it is set by the demands. `PeakBefore` asks for a visit to `H - 1`, which is
unreachable once `H` exceeds the maximum.

## What survives

Everything downstream. `theorem3_of_F2Prime` instantiates `H` and `L` as the maximum and the
minimum of the sequence it builds, so the *tight* form of `F2Prime` is all it ever needed. The
tight forms are stated here — `F2PrimeTight`, `ExitReachTight`, `HighExitValleyTight`,
`HighExitValleyOpenTight`, `LowExitPeakTight`, each with `∃ t, ρ t = L` and `∃ t, ρ t = H`
added — together with

* `f2PrimeTight_of_exitReachTight`: the batch-16 assembly, unchanged, in tight form;
* `highExitValleyTight_iff_open`: the batch-17 shrinking, unchanged, in tight form;
* `theorem3_of_F2PrimeTight`: Bing 1948 Theorem 3, block reading, from `F2PrimeTight` alone.

So the route to Theorem 3 is intact; what has to be re-conjectured is the tight form of the
three. Both attainment hypotheses are needed: dropping either one alone re-admits a
counterexample (`census-batch18.py`).

## Status of the tight conjectures

Not proved and not refuted here. `census-batch18.py` re-ran all five statements in tight form
over every down-crooked 1-Lipschitz sequence of length at most 13 on seven levels — 1 443 481
sequences, 6 684 572 basepoints with `L + 3 ≤ H` — with no failure. In the
slack reading, 3 699 948 instances up to length 11 with `H ≤ max ρ + 2` and `L ≥ min ρ - 2`
were tried; the witnesses below are the smallest found, shortest first and then least slack
(`ExitReach` and `F2Prime` need `L` one below the minimum and nothing else).

Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

/-! ## Tools -/

/-- `NonAscAt` is decidable, so the concrete phases below can be read off by `decide`. -/
instance decidableNonAscAt {m : ℕ} (A : Fin m → ℤ) (t : Fin m) : Decidable (NonAscAt A t) := by
  unfold NonAscAt; infer_instance

/-- The phase at the first index is `0`: a non-ascending step needs a predecessor. -/
theorem phase_at_zero {m : ℕ} (A : Fin m → ℤ) (hm : 0 < m) : phase A ⟨0, hm⟩ = 0 := by
  refine phase_eq_zero A ⟨0, hm⟩ ?_
  rintro ⟨t, ht, hNA⟩
  have htz : t.val ≤ 0 := ht
  exact absurd hNA.1 (by omega)

/-- Hence phase `1` can only occur past the first index. -/
theorem pos_of_phase_eq_one {m : ℕ} (A : Fin m → ℤ) (k : Fin m) (h : phase A k = 1) :
    0 < k.val := by
  by_contra hc
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
  rw [show k = (⟨0, hm⟩ : Fin m) from Fin.ext (show k.val = 0 by omega), phase_at_zero] at h
  omega

/-- An unconditional bound on the phase-adjusted levels bounds `hReach`: the supremum is taken
over a subset of them. -/
theorem hReach_le_of_all {m : ℕ} {A : Fin m → ℤ} (hm : 0 < m) (p c : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hub : ∀ k : Fin m, A k + phase A k ≤ c) : hReach A p ≤ c := by
  classical
  set S : Set ℤ :=
    {v : ℤ | ∃ j : Fin m, A j + phase A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}
  have hne : S.Nonempty := by
    refine ⟨A ⟨0, hm⟩ + phase A ⟨0, hm⟩, ⟨0, hm⟩, rfl, fun j' hj' => ?_⟩
    have hj'z : j'.val ≤ 0 := Fin.le_def.1 hj'
    rw [show j' = (⟨0, hm⟩ : Fin m) from Fin.ext (show j'.val = 0 by omega), h0]
    omega
  refine csSup_le hne ?_
  rintro v ⟨j, rfl, -⟩
  exact hub j

/-- If no index carries a peak and some index is below the window, `SegLam` fails. -/
theorem not_segLam_of_no_peak {m : ℕ} (f : Fin m → ℤ) (p H L h : ℤ)
    (hno : ∀ j : Fin m, f j + phase f j < h) (hbad : ∃ j : Fin m, f j < p - 1) :
    ¬ SegLam f p H L h := by
  rintro ⟨s, t, hst, htm, h1, h2, -, -, -⟩
  obtain ⟨j, hj⟩ := hbad
  have hsm : ¬ s < m := by
    intro hs
    have := h2 hs
    have := hno ⟨s, hs⟩
    omega
  have hjs : j.val < s := by have := j.isLt; omega
  exact absurd (h1 j hjs).1 (by omega)

/-! ## Witness 1: `ExitReach` and `F2Prime`

    ρ = 0, 1, 2, 1, 2, 2, 3, 4    basepoint 2,  p = 2,  H = 4,  L = -1

`H` is the true maximum; `L` is one below the true minimum, which is all the failure needs.
The arms are `G = 2, 1, 2, 2, 3, 4` and `T = 2, 1, 0`, with demands `hStarArm G = 4`,
`lStarArm T = 0`, so `hStar = 3` and `lStar = 0`. The backward arm drops to `p - 2` but its
phase-adjusted reach is only `2`, so the Λ side fails; the forward arm rises to `p + 2` but the
negated arm's reach is `-1 < 0 = -lStar`, so the V side fails. With `L = 0` the floor
`min (L+1) p` puts `lStar` at `1` and the V side holds. -/

def exitSeq : Fin 8 → ℤ := ![0, 1, 2, 1, 2, 2, 3, 4]

/-- Its basepoint. -/
def exitPt : Fin 8 := ⟨2, by omega⟩

/-- The level at the basepoint. -/
theorem exitSeq_pt : exitSeq exitPt = 2 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem exitSeq_isLip : IsLip exitSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [exitSeq]

set_option maxRecDepth 1000000 in
/-- And down-crooked. -/
theorem exitSeq_isCrookedSeq : IsCrookedSeq exitSeq := by unfold IsCrookedSeq; decide

/-- The forward arm's peak demand. -/
theorem exitSeq_hStarArm_G : hStarArm (armG exitSeq exitPt) 2 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- The backward arm's valley demand, in negated form. -/
theorem exitSeq_lStarArm_T : hStarArm (fun j => - armT exitSeq exitPt j) (-2) = 0 :=
  hStarArm_eq_of_attained _ _ _ ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- Hence the bump height is at least `3`. -/
theorem exitSeq_hStar : (3 : ℤ) ≤ hStar exitSeq exitPt 4 (-1) := by
  have h := exitSeq_hStarArm_G
  rw [hStar, exitSeq_pt]
  simp only [le_min_iff, le_max_iff]
  omega

/-- And the valley height is at most `0`: this is where the slack in `L` bites. -/
theorem exitSeq_lStar : lStar exitSeq exitPt 4 (-1) ≤ 0 := by
  have h : lStarArm (armT exitSeq exitPt) 2 = 0 := by
    rw [lStarArm, exitSeq_lStarArm_T]; omega
  rw [lStar, exitSeq_pt]
  simp only [max_le_iff, min_le_iff]
  omega

/-- The backward arm `2, 1, 0` never reaches `2` in the phase-adjusted sense. -/
theorem exitSeq_bound_T (k : Fin (exitPt.val + 1)) :
    armT exitSeq exitPt k + phase (armT exitSeq exitPt) k ≤ 2 := by
  rcases phase_zero_or_one (armT exitSeq exitPt) k with e | e
  · have hb : ∀ k : Fin (exitPt.val + 1), armT exitSeq exitPt k ≤ 2 := by decide
    have := hb k
    omega
  · have hpos := pos_of_phase_eq_one _ _ e
    have hb : ∀ k : Fin (exitPt.val + 1), 0 < k.val → armT exitSeq exitPt k ≤ 1 := by decide
    have := hb k hpos
    omega

/-- The negated forward arm never reaches `0` in the phase-adjusted sense. -/
theorem exitSeq_bound_negG (k : Fin (8 - exitPt.val)) :
    (- armG exitSeq exitPt k) + phase (fun j => - armG exitSeq exitPt j) k ≤ -1 := by
  have hph : ∀ k : Fin (8 - exitPt.val), k.val ≤ 1 →
      ¬ ∃ t : Fin (8 - exitPt.val), t.val ≤ k.val ∧
        NonAscAt (fun j => - armG exitSeq exitPt j) t := by decide
  by_cases hk : k.val ≤ 1
  · rw [phase_eq_zero _ _ (hph k hk)]
    have hb : ∀ k : Fin (8 - exitPt.val), k.val ≤ 1 → 1 ≤ armG exitSeq exitPt k := by decide
    have := hb k hk
    omega
  · have hb : ∀ k : Fin (8 - exitPt.val), ¬ k.val ≤ 1 → 2 ≤ armG exitSeq exitPt k := by decide
    have := hb k hk
    rcases phase_zero_or_one (fun j => - armG exitSeq exitPt j) k with e | e <;> rw [e] <;> omega

/-- So the backward arm's reach falls short of `hStar`. -/
theorem exitSeq_hReach_T : hReach (armT exitSeq exitPt) 2 ≤ 2 :=
  hReach_le_of_all (by omega) 2 2 (by decide) exitSeq_bound_T

/-- And the forward arm's reach falls short of `lStar` on the valley side. -/
theorem exitSeq_hReach_negG : hReach (fun j => - armG exitSeq exitPt j) (-2) ≤ -1 :=
  hReach_le_of_all (by omega) (-2) (-1) (by decide) exitSeq_bound_negG

/-- **`ExitReach` is false.** -/
theorem not_exitReach : ¬ ExitReach := by
  intro h
  have key := h 8 exitSeq exitPt 4 (-1) exitSeq_isLip exitSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num)
  rw [exitSeq_pt] at key
  have hh := exitSeq_hStar
  have hl := exitSeq_lStar
  rcases key with ⟨-, hT⟩ | ⟨hG, -⟩
  · rcases hT with hnd | hr
    · exact hnd ⟨⟨2, by decide⟩, by decide⟩
    · have := exitSeq_hReach_T
      omega
  · rcases hG with hnd | hr
    · exact hnd ⟨⟨5, by decide⟩, by decide⟩
    · have := exitSeq_hReach_negG
      omega

/-- **`F2Prime` is false**, at the same basepoint. -/
theorem not_f2Prime : ¬ F2Prime := by
  intro h
  have key := h 8 exitSeq exitPt 4 (-1) exitSeq_isLip exitSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num)
  rw [exitSeq_pt] at key
  have hh := exitSeq_hStar
  have hl := exitSeq_lStar
  rcases key with ⟨-, hT⟩ | ⟨hG, -⟩
  · refine not_segLam_of_no_peak _ 2 4 (-1) _ (fun j => ?_) ⟨⟨2, by decide⟩, by decide⟩ hT
    have := exitSeq_bound_T j
    omega
  · refine not_segLam_of_no_peak _ (-2) 1 (-4) _ (fun j => ?_) ⟨⟨5, by decide⟩, by decide⟩ hG
    have := exitSeq_bound_negG j
    omega


/-! ## Witness 2: `HighExitValleyOpen` and `HighExitValley`

    ρ = 2, 1, 0, 1, 2, 1, 2, 2, 3, 4    basepoint 0,  p = 2,  H = 4,  L = -2

Both demands are `2`, so `hStar = 2` and the cap does not bind: the basepoint is open. The
forward arm — the whole sequence — reaches `4 > hStar + 1` at its last index, and `s = 0` is
admissible, so the clause asks for a visit to `L + 1 = -1` before it. The sequence never goes
below `0`. -/

def valleySeq : Fin 10 → ℤ := ![2, 1, 0, 1, 2, 1, 2, 2, 3, 4]

/-- Its basepoint. -/
def valleyPt : Fin 10 := ⟨0, by omega⟩

/-- The level at the basepoint. -/
theorem valleySeq_pt : valleySeq valleyPt = 2 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem valleySeq_isLip : IsLip valleySeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [valleySeq]

set_option maxRecDepth 1000000 in
/-- And down-crooked. -/
theorem valleySeq_isCrookedSeq : IsCrookedSeq valleySeq := by unfold IsCrookedSeq; decide

/-- The forward arm's peak demand: it drops to `0` at index `2`. -/
theorem valleySeq_hStarArm_G : hStarArm (armG valleySeq valleyPt) 2 = 2 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- The backward arm is the single point `2`. -/
theorem valleySeq_hStarArm_T : hStarArm (armT valleySeq valleyPt) 2 = 2 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- So the bump height is `2` and the cap `max (H-1) p = 3` does not bind. -/
theorem valleySeq_hStar : hStar valleySeq valleyPt 4 (-2) ≤ 2 := by
  have hG := valleySeq_hStarArm_G
  have hT := valleySeq_hStarArm_T
  rw [hStar, valleySeq_pt]
  simp only [min_le_iff, max_le_iff]
  omega

/-- **`HighExitValleyOpen` is false.** -/
theorem not_highExitValleyOpen : ¬ HighExitValleyOpen := by
  intro h
  have hs := valleySeq_hStar
  have hopen : hStar valleySeq valleyPt 4 (-2) < max ((4 : ℤ) - 1) (valleySeq valleyPt) := by
    rw [valleySeq_pt, show max ((4 : ℤ) - 1) 2 = 3 by decide]
    omega
  obtain ⟨hG, -⟩ := h 10 valleySeq valleyPt 4 (-2) valleySeq_isLip valleySeq_isCrookedSeq
    (by decide) (by decide) (by norm_num) hopen
  have hval := hG 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
  obtain ⟨j, -, -, hj⟩ := hval ⟨9, by decide⟩ (Nat.zero_le _)
    (by rw [show armG valleySeq valleyPt ⟨9, by decide⟩ = 4 from by decide]; omega)
  have hb : ∀ j : Fin (10 - valleyPt.val), 0 ≤ armG valleySeq valleyPt j := by decide
  have := hb j
  omega

/-- **`HighExitValley` is false**, by the same witness. -/
theorem not_highExitValley : ¬ HighExitValley := fun h =>
  not_highExitValleyOpen (highExitValley_iff_open.mp h)

/-! ## Witness 3: `LowExitPeak`

    ρ = 0, 1, 2, 1, 2, 2, 3, 4, 3, 2    basepoint 9,  p = 2,  H = 6,  L = 0

Here `L` is the true minimum and `H` is two above the true maximum. Both valley demands are
`2`, so `lStar = 2`; the backward arm — the whole sequence read from the right — ends at `0`,
below `lStar - 1`, and `s = 0` is admissible, so the peak clause asks for a visit to
`H - 1 = 5` before it. The sequence never exceeds `4`. -/

def peakSeq : Fin 10 → ℤ := ![0, 1, 2, 1, 2, 2, 3, 4, 3, 2]

/-- Its basepoint. -/
def peakPt : Fin 10 := ⟨9, by omega⟩

/-- The level at the basepoint. -/
theorem peakSeq_pt : peakSeq peakPt = 2 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem peakSeq_isLip : IsLip peakSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [peakSeq]

set_option maxRecDepth 1000000 in
/-- And down-crooked. -/
theorem peakSeq_isCrookedSeq : IsCrookedSeq peakSeq := by unfold IsCrookedSeq; decide

/-- The forward arm is the single point `2`. -/
theorem peakSeq_lStarArm_G : lStarArm (armG peakSeq peakPt) 2 = 2 := by
  have : hStarArm (fun j => - armG peakSeq peakPt j) (-2) = -2 :=
    hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  rw [lStarArm, this]; omega

/-- The backward arm's valley demand: it rises to `4` at index `2`. -/
theorem peakSeq_lStarArm_T : lStarArm (armT peakSeq peakPt) 2 = 2 := by
  have : hStarArm (fun j => - armT peakSeq peakPt j) (-2) = -2 :=
    hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  rw [lStarArm, this]; omega

/-- So the valley height is `2`, two above the level the arm ends at. -/
theorem peakSeq_lStar : (2 : ℤ) ≤ lStar peakSeq peakPt 6 0 := by
  have hG := peakSeq_lStarArm_G
  have hT := peakSeq_lStarArm_T
  rw [lStar, peakSeq_pt]
  simp only [le_max_iff, le_min_iff]
  omega

/-- **`LowExitPeak` is false.** -/
theorem not_lowExitPeak : ¬ LowExitPeak := by
  intro h
  have hl := peakSeq_lStar
  obtain ⟨-, hT⟩ := h 10 peakSeq peakPt 6 0 peakSeq_isLip peakSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num)
  have hval := hT 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
  obtain ⟨j, -, -, hj⟩ := hval ⟨9, by decide⟩ (Nat.zero_le _)
    (by
      show - lStar peakSeq peakPt 6 0 + 1 < - armT peakSeq peakPt ⟨9, by decide⟩
      rw [show armT peakSeq peakPt ⟨9, by decide⟩ = 0 from by decide]
      omega)
  have hj' : - armT peakSeq peakPt j ≤ -6 + 1 := hj
  have hb : ∀ j : Fin (peakPt.val + 1), armT peakSeq peakPt j ≤ 4 := by decide
  have := hb j
  omega


/-! ## The repaired statements -/

/-- **`F2Prime`, tight.** `F2Prime` with the extremes required to be attained — which is how
`theorem3_of_F2Prime` supplies them. Not refuted by the witnesses above. -/
def F2PrimeTight : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedSeq ρ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (SegLam (armG ρ i) (ρ i) H L (hStar ρ i H L) ∧
       SegLam (armT ρ i) (ρ i) H L (hStar ρ i H L)) ∨
      (SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L) ∧
       SegVee (armT ρ i) (ρ i) H L (lStar ρ i H L))

/-- **`ExitReach`, tight.** -/
def ExitReachTight : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (OkLam (armG ρ i) (ρ i) (hStar ρ i H L) ∧ OkLam (armT ρ i) (ρ i) (hStar ρ i H L)) ∨
      (OkVee (armG ρ i) (ρ i) (lStar ρ i H L) ∧ OkVee (armT ρ i) (ρ i) (lStar ρ i H L))

/-- **`HighExitValley`, tight.** -/
def HighExitValleyTight : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

/-- **`LowExitPeak`, tight.** -/
def LowExitPeakTight : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        (- armG ρ i j) + phase (fun j' => - armG ρ i j') j < - lStar ρ i H L) →
      ValleyBefore (fun j' => - armG ρ i j') (-H) (- lStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        (- armT ρ i j) + phase (fun j' => - armT ρ i j') j < - lStar ρ i H L) →
      ValleyBefore (fun j' => - armT ρ i j') (-H) (- lStar ρ i H L) s)

/-- The tight form of the non-vacuous core. -/
def HighExitValleyOpenTight : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    hStar ρ i H L < max (H - 1) (ρ i) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

/-- Batch 17's shrinking, in tight form: when the cap binds the valley clause is vacuous. -/
theorem highExitValleyTight_iff_open : HighExitValleyTight ↔ HighExitValleyOpenTight := by
  constructor
  · intro hHEV n ρ i H L hLip hCr hL hH hrange hattL hattH _
    exact hHEV n ρ i H L hLip hCr hL hH hrange hattL hattH
  · intro hOpen n ρ i H L hLip hCr hL hH hrange hattL hattH
    by_cases hopen : hStar ρ i H L < max (H - 1) (ρ i)
    · exact hOpen n ρ i H L hLip hCr hL hH hrange hattL hattH hopen
    · push_neg at hopen
      have hcap : H - 1 ≤ hStar ρ i H L := le_trans (le_max_left _ _) hopen
      exact ⟨fun s _ => valleyBefore_of_cap H L _ (fun j => hH _) hcap s,
        fun s _ => valleyBefore_of_cap H L _ (fun j => hH _) hcap s⟩

/-- Batch 16's assembly, unchanged, in tight form: the two attainment hypotheses are only
passed along. -/
theorem f2PrimeTight_of_exitReachTight (h1 : ExitReachTight) (h2 : HighExitValleyTight)
    (h3 : LowExitPeakTight) : F2PrimeTight := by
  intro n ρ i H L hlip hcr hL hH hLH hattL hattH
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have hLG : ∀ j, L ≤ armG ρ i j := fun j => hL _
  have hLT : ∀ j, L ≤ armT ρ i j := fun j => hL _
  have hHG : ∀ j, armG ρ i j ≤ H := fun j => hH _
  have hHT : ∀ j, armT ρ i j ≤ H := fun j => hH _
  rcases h1 n ρ i H L hlip hcr hL hH hLH hattL hattH with ⟨hokG, hokT⟩ | ⟨hokG, hokT⟩
  · obtain ⟨hvG, hvT⟩ := h2 n ρ i H L hlip hcr hL hH hLH hattL hattH
    refine Or.inl ⟨?_, ?_⟩
    · exact segLam_of_okLam hmG (ρ i) H L _ (armG_isLip hlip i) h0G hLG hHG
        (le_hStar ρ i H L) (hStar_dem_armG ρ i H L) hokG hvG
    · exact segLam_of_okLam hmT (ρ i) H L _ (armT_isLip hlip i) h0T hLT hHT
        (le_hStar ρ i H L) (hStar_dem_armT ρ i H L) hokT hvT
  · obtain ⟨hvG, hvT⟩ := h3 n ρ i H L hlip hcr hL hH hLH hattL hattH
    have hnegG : IsLip (fun j => - armG ρ i j) := by
      intro j j' hjj'
      have := armG_isLip hlip i j j' hjj'
      simp only [abs_le] at this ⊢
      omega
    have hnegT : IsLip (fun j => - armT ρ i j) := by
      intro j j' hjj'
      have := armT_isLip hlip i j j' hjj'
      simp only [abs_le] at this ⊢
      omega
    have hdemG : hStarArm (fun j => - armG ρ i j) (- ρ i) ≤ - lStar ρ i H L ∨
        (-L) - 1 ≤ - lStar ρ i H L := by
      have := lStar_dem_armG ρ i H L
      simp only [lStarArm] at this
      omega
    have hdemT : hStarArm (fun j => - armT ρ i j) (- ρ i) ≤ - lStar ρ i H L ∨
        (-L) - 1 ≤ - lStar ρ i H L := by
      have := lStar_dem_armT ρ i H L
      simp only [lStarArm] at this
      omega
    refine Or.inr ⟨?_, ?_⟩
    · exact segLam_of_okLam hmG (- ρ i) (-L) (-H) _ hnegG (by rw [h0G])
        (fun j => by have := hHG j; omega)
        (fun j => by have := hLG j; omega)
        (by have := lStar_le ρ i H L; omega) hdemG hokG hvG
    · exact segLam_of_okLam hmT (- ρ i) (-L) (-H) _ hnegT (by rw [h0T])
        (fun j => by have := hHT j; omega)
        (fun j => by have := hLT j; omega)
        (by have := lStar_le ρ i H L; omega) hdemT hokT hvT

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, from `F2PrimeTight`. The proof of
`theorem3_of_F2Prime` already builds `H` and `L` as attained extremes, so the tight form is all
that was ever used. -/
theorem theorem3_of_F2PrimeTight (hF2 : F2PrimeTight) {X : Type*} [MetricSpace X] {n k : ℕ}
    (hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedSeq ρ := isCrookedSeq_minIdx hcr
    have hLi : L ≤ ρ i := hLf i
    have hiH : ρ i ≤ H := hHf i
    rcases hF2 n ρ i H L hlip hcrook hLf hHf hcase ⟨tL, hL.symm⟩ ⟨tH, hH.symm⟩ with
      ⟨hG, hT⟩ | ⟨hG, hT⟩
    · exact exists_blocks_first_of_segLam href i (ρ i) H L (hStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [hStar]; omega) (by simp only [hStar]; omega) hLi
        (by simp only [hStar]; omega)
    · exact exists_blocks_first_of_segVee href i (ρ i) H L (lStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [lStar]; omega) (by simp only [lStar]; omega) hiH
        (by simp only [lStar]; omega)

-- Commented-out statement `exitReach`, `highExitValleyOpen`, `lowExitPeak`, `highExitValley`, `f2Prime`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
