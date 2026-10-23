import HPC.Fold.Distance71

/-!
# The valley at `L + 3`: what a running arm is, and what the crossing then owes

Batch 71 reduced the branch's obligation at a high-run crossing to `Valley3BeforeNine` on the
**running** arm — one landmark pair before the arm's first ascent, equivalently `Ceil72`. Batch 72
asks where that statement is a fact. The census (`census-batch72.c`, log `census-batch72.log`)
answers: it is **not** a fact about a running arm of a faithful pair, with or without `LowAt`. Over
the batch-70 corpus, 478 735 running arms at basepoints of the band carry it, 194 076 **fail** it,
and every one of those failures is also a failure at a basepoint of the branch — `LowAt` on both
arms changes nothing. What no failure is, on that corpus, is a **crossing**: at all 229 running arms
at a crossing the statement holds.

This file proves why the crossing is the hypothesis that matters, and what it buys.

* **A running arm is a `w8` arm** (`leg4Land_w8_of_run`, and the two arm forms
  `leg4Land_w8_armG_of_highRun`, `leg4Land_w8_armT_of_highRun`). The `w8` sentence inside the band
  is one clause — every time at `L + 2` or below is preceded, by `L + 7 - (its level)` steps, by a
  time at `L + 7` or above at arm index four or more — and the arm's own ascent serves as that time:
  the run puts every low time after the ascent, and the timing law (`z 7 = 170`) puts it 169 steps
  after, where the clause asks for at most seven. This is why the census sees the same 229 arms in
  its class "a running arm at a crossing" and in its class "the running arm of a high-run crossing".

* **Both arms cannot run high at a crossing** (`not_bothHighRun_of_cross`, the contrapositive
  `not_cross_of_bothHighRun`). If they did, both would be `w8` arms by the theorem above, and `w8`
  would serve both — which the first clause of `TriCrossL5` forbids. This closes the question batch
  71 §2.5 left open and turns its census line "0 of 1351 crossings" into a theorem.

* **Hence the partner's ceiling clause is free** (`deepFirst2_partner_of_cross_highRunG`,
  `ceil72_partner_of_cross_highRunG`, and the mirrors): at a crossing whose forward arm runs high the
  backward arm does not, so it is deep first at `L + 2`, so `ceil72_of_deepFirst2_armT` applies. The
  batch-70 assembly's second hypothesis is therefore discharged in general, and what remains at a
  high-run crossing is exactly one statement about the running arm
  (`s3_span_nine_mid5_of_cross_highRun_ceilRun_armG` and its mirror).

* **The reading of batch 71 §2.3, as a theorem** (`crooked_mid5_low2`, `crooked_low2_mid5`): a link
  carrying `L + 5` and a link carrying `L + 2` put a link carrying `L + 3` between them — the
  descending pairing that names the valley at the counterexample of batch 71. Together with
  `run_peak_armG` / `run_peak_armT`, which give the peak the clause asks for for free (the pairing
  between the basepoint and the ascent puts a link carrying `L + 8` at arm index five or more and
  seven or more before the ascent), the clause is reduced to placing one time at `L + 3` between the
  peak and the ascent (`valley3BeforeNine_of_peak_low`).
-/

namespace HPC.Fold

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-! ## A running arm is a `w8` arm -/

/-- **A running arm of the band is a `w8` arm.** Inside the band `[L, L + 9]` the sentence
`Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)` has only its first clause: every time at `L + 2` or
below must be preceded by a time at `L + 7` or above, at arm index four or more and by at least
`L + 7 -` its level steps. The arm's own first ascent serves: the run puts every low time after it,
and seven levels cost 169 steps where the clause asks for at most seven. -/
theorem leg4Land_w8_of_run (hsep : ArmSep f) (hm : 0 < m) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) {e : Fin m} (he : L + 9 ≤ f e)
    (hrun : ∀ d : Fin m, d.val < e.val → L + 3 ≤ f d) :
    Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5) := by
  have hz4 : z 4 = 13 := by decide
  have hz7 : z 7 = 170 := by decide
  have he12 : 12 ≤ e.val := by
    have hne : (⟨0, hm⟩ : Fin m).val ≠ e.val := by
      intro h
      have : f (⟨0, hm⟩ : Fin m) = f e := by
        congr 1
        exact Fin.ext h
      omega
    rcases hsep 4 ⟨0, hm⟩ e (by push_cast; omega) hne with h | h
    · simp only [hz4] at h; omega
    · simp only [hz4] at h; omega
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hdlev : f d ≤ L + 2 := by omega
    have hde : e.val < d.val := by
      rcases lt_trichotomy d.val e.val with h | h | h
      · have := hrun d h; omega
      · exfalso
        have : f d = f e := by congr 1; exact Fin.ext h
        omega
      · exact h
    have hsep7 : e.val + 169 ≤ d.val := by
      rcases hsep 7 d e (by push_cast; omega) (by omega) with h | h
      · simp only [hz7] at h; omega
      · simp only [hz7] at h; omega
    have := hL d
    exact ⟨e, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    exact absurd (hH d) (by omega)

end Arm

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The forward arm of a high run is a `w8` arm.** -/
theorem leg4Land_w8_armG_of_highRun (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (h : HighRunG ρ i L) :
    Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) := by
  obtain ⟨e, he, hlow⟩ := h
  have hi := i.isLt
  have hm : 0 < n - i.val := by omega
  refine leg4Land_w8_of_run (armG_armSep hcr i) hm ?_ (fun j => hLb _) (fun j => hHb _) he ?_
  · rw [armG_zero ρ i _ rfl]; exact hp
  · intro d hd
    exact hlow d hd

/-- **The backward arm of a high run is a `w8` arm.** -/
theorem leg4Land_w8_armT_of_highRun (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (h : HighRunT ρ i L) :
    Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) := by
  obtain ⟨e, he, hlow⟩ := h
  have hm : 0 < i.val + 1 := Nat.succ_pos _
  refine leg4Land_w8_of_run (armT_armSep hcr i) hm ?_ (fun j => hLb _) (fun j => hHb _) he ?_
  · rw [armT_zero ρ i _ rfl]; exact hp
  · intro d hd
    exact hlow d hd

/-! ## Both arms cannot run high at a crossing -/

/-- **At a crossing at most one arm runs high.** Both running would make both `w8` arms, and the
first clause of the crossing forbids that. The census of batch 71 found `BothHighRunL5` at 16 235
basepoints of the branch and at none of the 1351 crossings; this is that line as a theorem. -/
theorem not_bothHighRun_of_cross (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) : ¬ BothHighRunL5 ρ i L := by
  rintro ⟨hG, hT⟩
  exact hcross.1 ⟨leg4Land_w8_armG_of_highRun hcr i L hp hLb hHb hG,
    leg4Land_w8_armT_of_highRun hcr i L hp hLb hHb hT⟩

/-- **The contrapositive:** a basepoint at which both arms run high is not a crossing. -/
theorem not_cross_of_bothHighRun (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (h : BothHighRunL5 ρ i L) : ¬ TriCrossL5 ρ i L :=
  fun hcross => not_bothHighRun_of_cross hcr i L hp hLb hHb hcross h

/-! ## The partner's ceiling clause, discharged -/

/-- **At a crossing whose forward arm runs high, the backward arm is deep first at `L + 2`.** -/
theorem deepFirst2_partner_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) : DeepFirst2 (armT ρ i) L := by
  by_contra hc
  exact not_bothHighRun_of_cross hcr i L hp hLb hHb hcross ⟨hrun, highRunT_of_not_deepFirst2 i L hc⟩

/-- **The mirror.** -/
theorem deepFirst2_partner_of_cross_highRunT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) : DeepFirst2 (armG ρ i) L := by
  by_contra hc
  exact not_bothHighRun_of_cross hcr i L hp hLb hHb hcross ⟨highRunG_of_not_deepFirst2 i L hc, hrun⟩

/-- **The partner's ceiling clause at a high-run crossing, in general.** The route batch 68 opened
— `Ceil72` from `DeepFirst2` — now always serves the arm across the basepoint from the running one,
because that arm cannot itself run high. -/
theorem ceil72_partner_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) : Ceil72 (armT ρ i) L :=
  ceil72_of_deepFirst2_armT hcr i L hHb
    (deepFirst2_partner_of_cross_highRunG hcr i L hp hLb hHb hcross hrun)

/-- **The mirror.** -/
theorem ceil72_partner_of_cross_highRunT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) : Ceil72 (armG ρ i) L :=
  ceil72_of_deepFirst2_armG hcr i L hHb
    (deepFirst2_partner_of_cross_highRunT hcr i L hp hLb hHb hcross hrun)

/-! ## What the high-run crossing still owes: one clause, on the running arm -/

/-- **The high-run crossing folds as soon as the running arm has its ceiling clause.** The
partner's clause is now free, so the assembly of batch 70 needs nothing of the partner: at a
crossing whose forward arm runs high, `Ceil72` on that arm — equivalently `Valley3BeforeNine`, one
landmark pair before its first ascent — gives a walk serving both arms. -/
theorem s3_span_nine_mid5_of_cross_highRun_ceilRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) (hceilG : Ceil72 (armG ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_ceil_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    hceilG (ceil72_partner_of_cross_highRunG hcr i L hp hLb hHb hcross hrun)

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRun_ceilRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) (hceilT : Ceil72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_ceil_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    (ceil72_partner_of_cross_highRunT hcr i L hp hLb hHb hcross hrun) hceilT

/-! ## The reading that names the valley -/

/-- **The descending pairing from `L + 5` to `L + 2`.** A link carrying `L + 5` and a later link
carrying `L + 2` put a link carrying `L + 3` and then one carrying `L + 4` between them. This is the
reading that names the `Ceil72` valley at the counterexample of batch 71, where no time at `L + 2`
or below lies near the basepoint: its first landmark is a time at `L + 3`. The timing law spaces the
three by two, one and two steps — the two levels of `5 → 3`, the one of `3 → 4`, the two of
`4 → 2` — and nothing in the pairing bounds the landmark from above. -/
theorem crooked_mid5_low2 (hcr : IsCrookedIvF ρ σ) (a b : Fin n) (hab : a.val < b.val) (L : ℤ)
    (ha1 : ρ a ≤ L + 5) (ha2 : L + 5 ≤ σ a) (hb1 : ρ b ≤ L + 2) (hb2 : L + 2 ≤ σ b) :
    ∃ r r' : Fin n, a.val < r.val ∧ r.val < r'.val ∧ r'.val < b.val ∧
      ρ r ≤ L + 3 ∧ L + 3 ≤ σ r ∧ ρ r' ≤ L + 4 ∧ L + 4 ≤ σ r' := by
  obtain ⟨r, r', har, hrr', hr'b, -, hcase⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (L + 5) (L + 2)
      ⟨a, by simp, ha1, ha2⟩ ⟨b, by simp, hb1, hb2⟩ (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  exact ⟨r, r', har, hrr', hr'b, by omega, by omega, by omega, by omega⟩

/-- **The same pairing read the other way.** A link carrying `L + 2` and a later link carrying
`L + 5` put a link carrying `L + 4` and then one carrying `L + 3` between them. -/
theorem crooked_low2_mid5 (hcr : IsCrookedIvF ρ σ) (a b : Fin n) (hab : a.val < b.val) (L : ℤ)
    (ha1 : ρ a ≤ L + 2) (ha2 : L + 2 ≤ σ a) (hb1 : ρ b ≤ L + 5) (hb2 : L + 5 ≤ σ b) :
    ∃ r r' : Fin n, a.val < r.val ∧ r.val < r'.val ∧ r'.val < b.val ∧
      ρ r ≤ L + 4 ∧ L + 4 ≤ σ r ∧ ρ r' ≤ L + 3 ∧ L + 3 ≤ σ r' := by
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (L + 2) (L + 5)
      ⟨a, by simp, ha1, ha2⟩ ⟨b, by simp, hb1, hb2⟩ (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  exact ⟨r, r', har, hrr', hr'b, by omega, by omega, by omega, by omega⟩

/-- **The peak the clause asks for is free on a running arm.** The pairing between the basepoint,
which carries `L + 5`, and the arm's first ascent, which carries `L + 9`, puts a link carrying
`L + 8` — so a time at `L + 7` or above — at arm index five or more and at least seven steps before
the ascent. What a reading of `Ceil72` on a running arm has to place is therefore only the valley. -/
theorem run_peak_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) {e : Fin (n - i.val)} (he : L + 9 ≤ armG ρ i e) :
    ∃ j : Fin (n - i.val), 5 ≤ j.val ∧ j.val + 7 ≤ e.val ∧ L + 7 ≤ armG ρ i j := by
  have hi := i.isLt
  have hel := e.isLt
  have hblt : i.val + e.val < n := by omega
  have hbv : ρ (⟨i.val + e.val, hblt⟩ : Fin n) = armG ρ i e := rfl
  have hb9 : L + 9 ≤ ρ (⟨i.val + e.val, hblt⟩ : Fin n) := by rw [hbv]; exact he
  have hb2 : L + 9 ≤ σ (⟨i.val + e.val, hblt⟩ : Fin n) :=
    le_trans hb9 (hcr.le (⟨i.val + e.val, hblt⟩ : Fin n))
  have hepos : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h0 | hpos
    · exfalso
      have : (⟨i.val + e.val, hblt⟩ : Fin n) = i := Fin.ext (by simp only []; omega)
      rw [this, hp] at hb9
      omega
    · exact hpos
  have hib : i.val < (⟨i.val + e.val, hblt⟩ : Fin n).val := by simp only []; omega
  have hpi1 : ρ i ≤ L + 5 := le_of_eq hp
  have hpi2 : L + 5 ≤ σ i := by have := hcr.le i; omega
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked i ⟨i.val + e.val, hblt⟩ (Fin.lt_def.mpr hib) (L + 5) (L + 9)
      ⟨i, by simp, hpi1, hpi2⟩ ⟨⟨i.val + e.val, hblt⟩, by simp, hHb _, hb2⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hr1' : ρ r ≤ L + 8 := by omega
  have hr2' : L + 8 ≤ σ r := by omega
  have hr'1' : ρ r' ≤ L + 6 := by omega
  have hr'2' : L + 6 ≤ σ r' := by omega
  have hwr := hcr.width r
  have hz3 : z 3 = 6 := by decide
  have hz2 : z 2 = 3 := by decide
  have harv : i.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < (⟨i.val + e.val, hblt⟩ : Fin n).val := hr'b
  simp only [] at hr'bv
  have hir : i.val + 5 ≤ r.val := by
    rcases ivSep hcr i r (by omega) 3 (L + 5) (L + 8) (by push_cast; omega)
      hpi1 hpi2 hr1' hr2' with h | h
    · simp only [hz3] at h; omega
    · simp only [hz3] at h; omega
  have hrr'2 : r.val + 2 ≤ r'.val := by
    rcases ivSep hcr r' r (by omega) 2 (L + 6) (L + 8) (by push_cast; omega)
      hr'1' hr'2' hr1' hr2' with h | h
    · simp only [hz2] at h; omega
    · simp only [hz2] at h; omega
  have hr'b5 : r'.val + 5 ≤ i.val + e.val := by
    rcases ivSep hcr r' ⟨i.val + e.val, hblt⟩ (by simp only []; omega) 3 (L + 6) (L + 9)
      (by push_cast; omega) hr'1' hr'2' (hHb _) hb2 with h | h
    · simp only [hz3] at h; omega
    · simp only [hz3] at h; omega
  have hrn : r.val - i.val < n - i.val := by have := r.isLt; omega
  refine ⟨⟨r.val - i.val, hrn⟩, by simp only []; omega, by simp only []; omega, ?_⟩
  have hval : armG ρ i ⟨r.val - i.val, hrn⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  rw [hval]
  omega

/-- **The mirror, on the backward arm.** -/
theorem run_peak_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) {e : Fin (i.val + 1)} (he : L + 9 ≤ armT ρ i e) :
    ∃ j : Fin (i.val + 1), 5 ≤ j.val ∧ j.val + 7 ≤ e.val ∧ L + 7 ≤ armT ρ i j := by
  have hi := i.isLt
  have hel := e.isLt
  have hblt : i.val - e.val < n := by omega
  have hbv : ρ (⟨i.val - e.val, hblt⟩ : Fin n) = armT ρ i e := rfl
  have hb9 : L + 9 ≤ ρ (⟨i.val - e.val, hblt⟩ : Fin n) := by rw [hbv]; exact he
  have hb2 : L + 9 ≤ σ (⟨i.val - e.val, hblt⟩ : Fin n) :=
    le_trans hb9 (hcr.le (⟨i.val - e.val, hblt⟩ : Fin n))
  have hepos : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h0 | hpos
    · exfalso
      have : (⟨i.val - e.val, hblt⟩ : Fin n) = i := Fin.ext (by simp only []; omega)
      rw [this, hp] at hb9
      omega
    · exact hpos
  have hbi : (⟨i.val - e.val, hblt⟩ : Fin n).val < i.val := by simp only []; omega
  have hpi1 : ρ i ≤ L + 5 := le_of_eq hp
  have hpi2 : L + 5 ≤ σ i := by have := hcr.le i; omega
  obtain ⟨r, r', har, hrr', hr'b, -, hcase⟩ :=
    hcr.crooked ⟨i.val - e.val, hblt⟩ i (Fin.lt_def.mpr hbi) (L + 9) (L + 5)
      ⟨⟨i.val - e.val, hblt⟩, by simp, hHb _, hb2⟩ ⟨i, by simp, hpi1, hpi2⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hr1' : ρ r ≤ L + 6 := by omega
  have hr2' : L + 6 ≤ σ r := by omega
  have hr'1' : ρ r' ≤ L + 8 := by omega
  have hr'2' : L + 8 ≤ σ r' := by omega
  have hwr := hcr.width r'
  have hz3 : z 3 = 6 := by decide
  have hz2 : z 2 = 3 := by decide
  have harv : (⟨i.val - e.val, hblt⟩ : Fin n).val < r.val := har
  simp only [] at harv
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < i.val := hr'b
  have hri : r'.val + 5 ≤ i.val := by
    rcases ivSep hcr i r' (by omega) 3 (L + 5) (L + 8) (by push_cast; omega)
      hpi1 hpi2 hr'1' hr'2' with h | h
    · simp only [hz3] at h; omega
    · simp only [hz3] at h; omega
  have hrr'2 : r.val + 2 ≤ r'.val := by
    rcases ivSep hcr r r' (by omega) 2 (L + 6) (L + 8) (by push_cast; omega)
      hr1' hr2' hr'1' hr'2' with h | h
    · simp only [hz2] at h; omega
    · simp only [hz2] at h; omega
  have hbr5 : i.val - e.val + 5 ≤ r.val := by
    rcases ivSep hcr r ⟨i.val - e.val, hblt⟩ (by simp only []; omega) 3 (L + 6) (L + 9)
      (by push_cast; omega) hr1' hr2' (hHb _) hb2 with h | h
    · simp only [hz3] at h; omega
    · simp only [hz3] at h; omega
  have hrn : i.val - r'.val < i.val + 1 := by omega
  refine ⟨⟨i.val - r'.val, hrn⟩, by simp only []; omega, by simp only []; omega, ?_⟩
  have hval : armT ρ i ⟨i.val - r'.val, hrn⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  rw [hval]
  omega

/-! ## What is left to place -/

/-- **The clause, from one peak and one valley before the first ascent.** With the first ascent
named, the universally quantified spacing of `Valley3BeforeNine` follows from the one at that
ascent, so the landmark pair is all that is needed. -/
theorem valley3BeforeNine_of_peak_low {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (j k e : Fin m)
    (hj : 3 ≤ j.val) (hjk : j.val + 5 ≤ k.val) (hke : k.val + 6 ≤ e.val)
    (hjlev : L + 6 ≤ f j) (hklev : f k ≤ L + 3)
    (hfirst : ∀ d : Fin m, L + 9 ≤ f d → e.val ≤ d.val) :
    Valley3BeforeNine f L := by
  refine ⟨j, k, by exact_mod_cast hj, by exact_mod_cast hjk, hjlev, hklev, fun d hd => ?_⟩
  have := hfirst d hd
  omega

/-! ## What the crossing does give: a low time on the partner's side -/

/-- **At a high-run crossing the partner has a time at `L + 2` or below.** The running arm is a
`w8` arm, so the crossing takes `w8` off the partner; inside the band the `w8` sentence is its first
clause alone, so its failure produces a time of the partner at `L + 2` or below (and the basepoint
itself is not one, being at `L + 5`). What the branch owes is therefore not the existence of that
low time but its **distance**: `NearLowT` asks for one within 67 steps, and batch 71's
counterexample has one at 185. -/
theorem partnerLow_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) :
    ∃ a : Fin n, a.val < i.val ∧ ρ a ≤ L + 2 := by
  have hw8G := leg4Land_w8_armG_of_highRun hcr i L hp hLb hHb hrun
  have hnot : ¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) :=
    fun h => hcross.1 ⟨hw8G, h⟩
  have hB : ∀ d : Fin (i.val + 1), armT ρ i d ≤ (L + 1) - 2 →
      ∃ j k l : Fin (i.val + 1), (L + 8) - (L + 5) + 1 ≤ (j.val : ℤ) ∧
        (j.val : ℤ) + ((L + 8) - (L + 1)) ≤ (k.val : ℤ) ∧
        (k.val : ℤ) + ((L + 9) - 1 - (L + 1)) ≤ (l.val : ℤ) ∧
        (l.val : ℤ) + ((L + 9) - 2 - armT ρ i d) ≤ (d.val : ℤ) ∧
        (L + 8) - 1 ≤ armT ρ i j ∧ armT ρ i k ≤ (L + 1) + 1 ∧ (L + 9) - 2 ≤ armT ρ i l := by
    intro d hd
    exfalso
    have hdn : i.val - d.val < n := by have := i.isLt; have := d.isLt; omega
    have hval : armT ρ i d = ρ ⟨i.val - d.val, hdn⟩ := rfl
    have := hLb (⟨i.val - d.val, hdn⟩ : Fin n)
    rw [hval] at hd
    omega
  have hC : ∀ d : Fin (i.val + 1), (L + 8) + 2 ≤ armT ρ i d →
      ∃ j k : Fin (i.val + 1), (L + 8) - (L + 5) + 1 ≤ (j.val : ℤ) ∧
        (j.val : ℤ) + ((L + 8) - (L + 1)) ≤ (k.val : ℤ) ∧
        (k.val : ℤ) + (armT ρ i d - (L + 1) - 1) ≤ (d.val : ℤ) ∧
        (L + 8) - 1 ≤ armT ρ i j ∧ armT ρ i k ≤ (L + 1) + 1 := by
    intro d hd
    exfalso
    have hdn : i.val - d.val < n := by have := i.isLt; have := d.isLt; omega
    have hval : armT ρ i d = ρ ⟨i.val - d.val, hdn⟩ := rfl
    have := hHb (⟨i.val - d.val, hdn⟩ : Fin n)
    rw [hval] at hd
    omega
  have hA : ¬ (∀ d : Fin (i.val + 1), armT ρ i d ≤ (L + 5) - 3 →
      ∃ j : Fin (i.val + 1), (L + 8) - (L + 5) + 1 ≤ (j.val : ℤ) ∧
        (j.val : ℤ) + ((L + 8) - 1 - armT ρ i d) ≤ (d.val : ℤ) ∧
        (L + 8) - 1 ≤ armT ρ i j) := fun h => hnot ⟨h, hB, hC⟩
  push_neg at hA
  obtain ⟨d, hd, -⟩ := hA
  have hdn : i.val - d.val < n := by have := i.isLt; omega
  have hval : armT ρ i d = ρ ⟨i.val - d.val, hdn⟩ := rfl
  have hdpos : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h0 | hpos
    · exfalso
      rw [armT_zero ρ i d h0, hp] at hd
      omega
    · exact hpos
  refine ⟨⟨i.val - d.val, hdn⟩, by simp only []; have := d.isLt; omega, ?_⟩
  rw [← hval]
  omega

/-- **And that low time is at least 169 steps from the ascent.** The timing law across the
basepoint: the distance from the basepoint to the partner's low time plus the arm index of the
running arm's ascent is at least 169. The census sees the sum equal to 169 at 228 of the 229
high-run crossings of the corpus. -/
theorem partnerLow_sep_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) :
    ∃ a : Fin n, a.val < i.val ∧ ρ a ≤ L + 2 ∧
      ∀ e : Fin (n - i.val), L + 9 ≤ armG ρ i e → 169 ≤ (i.val - a.val) + e.val := by
  obtain ⟨a, hai, ha⟩ := partnerLow_of_cross_highRunG hcr i L hp hLb hHb hcross hrun
  exact ⟨a, hai, ha, fun e he => nearLow_ascent_sep_armG hcr hHb hai ha he⟩

end Pair

end HPC.Fold
