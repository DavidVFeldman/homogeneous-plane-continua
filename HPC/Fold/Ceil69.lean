import HPC.Fold.Ceil68

/-!
# `Ceil72` on the high-running arm, from a low time near the basepoint

Batch 68 left the branch `L + 5` with one clause outstanding: `w72`'s ceiling clause `Ceil72` on the
`w8` side of a crossing where that side runs high — reaches `L + 9` with nothing at `L + 2` or below
before it (`s3_span_nine_mid5_of_cross_highRun_armG`). Batch 69 §2.1 asks which time of the pair
supplies the low landmark the clause wants, since the running arm has no own time at `L + 2` to read
`crooked_peak_valley_high9_mid` from.

**The census answers it, and the answer is a theorem.** `census-batch69.c` reads the 87 high-run
crossings of the corpus one by one: at every one of them the low landmark of `Ceil72` sits at the
level `L + 3` exactly and **seventy** steps before the ascent — which is the crookedness clause's
own spacing (`z 6 = 71`), not an accident of the arm. The time that supplies it is the pairing read
between the **partner's** last time at `L + 2` or below and the running arm's ascent: at all 87 that
time lies within 67 steps of the basepoint, and the clause's spacings then push both of its
landmarks past the basepoint and onto the running arm.

That is what this file proves, with the distance as a hypothesis:

> **`ceil72_at_of_nearLow_armG`.** If some time `a` of the pair before the basepoint is at `L + 2`
> or below and `i ≤ a + 67`, then at every time of the forward arm at `L + 9` the pairing
> `crooked_peak_valley_high9_mid` read between `a` and that ascent returns its peak at `L + 7` or
> above and its valley at `L + 3` or below **as times of the forward arm**, at arm indices `3` or
> more and twenty-nine apart, the valley seventy steps before the ascent. These are exactly the two
> landmarks `Ceil72` asks for.

The high run plays no part in the argument: the hypothesis gives `Ceil72` on the whole arm
(`ceil72_of_nearLowT_armG`), and with it the high-run crossing closes
(`s3_span_nine_mid5_of_cross_highRun_nearLow_armG` and its mirror). The arithmetic is forced: the
clause places the peak `70` after `a` and the valley `29` after the peak, so `a ≥ i - 67` puts the
peak at arm index `3` or more, and the valley is then at arm index `32` or more and at least `70`
steps before the ascent, where the clause asks only for `6`.

What is left of the branch at `L + 5` is therefore the **distance question** named here as
`NearLowT` / `NearLowG`: at a crossing whose `w8` side runs high, is there a time of the pair at
`L + 2` or below within 67 steps across the basepoint? Over the corpus there is at every one of the
87 (`census-batch69.log`); no proof of it is offered here, and the two deep-floor clauses — which
the same census finds hold at all 87 — are the other standing hypothesis.
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## A low time near the basepoint -/

/-- **A low time near the basepoint, on the backward side**: a time of the pair before the
basepoint, at `L + 2` or below, at most 67 steps before it. This is what the forward arm needs to
read the pairing at its own ascents. -/
def NearLowT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, a.val < i.val ∧ i.val ≤ a.val + 67 ∧ ρ a ≤ L + 2

/-- **The mirror: a low time near the basepoint on the forward side.** -/
def NearLowG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, i.val < a.val ∧ a.val ≤ i.val + 67 ∧ ρ a ≤ L + 2

/-! ## The ceiling clause of `w72` at one ascent -/

/-- **`Ceil72` at one ascent of the forward arm, from a low time near the basepoint.** The pairing
between the low time `a` and the ascent returns a peak at `L + 7` or above at least seventy steps
after `a` — hence at arm index three or more — and, twenty-nine steps after that, a valley at
`ρ a + 1 ≤ L + 3` or below, itself seventy steps before the ascent. Both are times of the forward
arm, and they are the two landmarks the clause asks for. -/
theorem ceil72_at_of_nearLow_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (a : Fin n) (hai : a.val < i.val) (hnear : i.val ≤ a.val + 67)
    (ha : ρ a ≤ L + 2) (d : Fin (n - i.val)) (hd : L + 9 ≤ armG ρ i d) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 := by
  have hi := i.isLt
  have hdn := d.isLt
  have hBlt : i.val + d.val < n := by omega
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hBv : ρ B = armG ρ i d := rfl
  have hab : a.val < B.val := by simp only [hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr a B hab L ha (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega)
  have hBval : B.val = i.val + d.val := rfl
  have hjlt : r.val - i.val < n - i.val := by omega
  have hklt : r'.val - i.val < n - i.val := by omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have hub : armG ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror, on the backward arm.** The backward arm runs against the chain, so the pairing is
read from the high link: the peak comes first in arm order and the valley after it. -/
theorem ceil72_at_of_nearLow_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (a : Fin n) (hai : i.val < a.val) (hnear : a.val ≤ i.val + 67)
    (ha : ρ a ≤ L + 2) (d : Fin (i.val + 1)) (hd : L + 9 ≤ armT ρ i d) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 3 := by
  have hi := i.isLt
  have hdn := d.isLt
  have hBlt : i.val - d.val < n := by omega
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hBv : ρ B = armT ρ i d := rfl
  have hab : B.val < a.val := by simp only [hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9_mid hcr B a hab L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) ha
  have hBval : B.val = i.val - d.val := rfl
  have hjlt : i.val - r'.val < i.val + 1 := by omega
  have hklt : i.val - r.val < i.val + 1 := by omega
  have hjv : armT ρ i ⟨i.val - r'.val, hjlt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hkv : armT ρ i ⟨i.val - r.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have hub : armT ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-! ## The clause on the whole arm -/

/-- **A low time near the basepoint on the backward side gives the forward arm `Ceil72` in full.**
The high run plays no part: the clause is read at every ascent of the arm, whether or not the arm
has been low before it. -/
theorem ceil72_of_nearLowT_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hnl : NearLowT ρ i L) : Ceil72 (armG ρ i) L := by
  obtain ⟨a, hai, hnear, ha⟩ := hnl
  intro d hd
  exact ceil72_at_of_nearLow_armG hcr i L hHb a hai hnear ha d hd

/-- **The mirror.** -/
theorem ceil72_of_nearLowG_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hnl : NearLowG ρ i L) : Ceil72 (armT ρ i) L := by
  obtain ⟨a, hai, hnear, ha⟩ := hnl
  intro d hd
  exact ceil72_at_of_nearLow_armT hcr i L hHb a hai hnear ha d hd

/-! ## The high-run crossing, closed on the distance hypothesis -/

/-- **The high-run crossing of the branch `L + 5`, closed where a low time sits near the
basepoint.** This is `s3_span_nine_mid5_of_cross_highRun_armG` with its outstanding clause
discharged: the `w8` side is the forward arm, the partner stops below `L + 9`, the two deep-floor
clauses hold, and the pair has a time at `L + 2` or below within 67 steps before the basepoint. -/
theorem s3_span_nine_mid5_of_cross_highRun_nearLow_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnineT : ∀ j, armT ρ i j ≤ L + 8)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L)
    (hnl : NearLowT ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross h8 hnineT
    hdeepG hdeepT (ceil72_of_nearLowT_armG hcr i L hHb hnl)

/-- **The mirror**, with the `w8` side the backward arm. -/
theorem s3_span_nine_mid5_of_cross_highRun_nearLow_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnineG : ∀ j, armG ρ i j ≤ L + 8)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L)
    (hnl : NearLowG ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross h8 hnineG
    hdeepG hdeepT (ceil72_of_nearLowG_armT hcr i L hHb hnl)

/-! ## The deep-floor clause of `w72` on the running arm -/

/-- **An ascent before every descent to the floor.** On the `w8` side of a high-run crossing the
descents to `L` that the census sees all come after the run to `L + 9`; this is that hypothesis,
written out. -/
def NineBeforeDeep {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L → ∃ e : Fin m, e.val < d.val ∧ L + 9 ≤ f e

/-- **`w72`'s deep-floor clause at one descent of the forward arm**, from a low time near the
basepoint and an ascent to `L + 9` before the descent. The pairing supplies the first two
landmarks, exactly as it does for `Ceil72`; the ascent itself is the third, and the timing is the
plain Lipschitz one — the arm needs `L + 9 - f d` steps to come down from the ascent to the
descent, where the clause asks for `L + 7 - f d`. The descent's own level plays no part, so the
statement is made at an arbitrary later time of the arm. -/
theorem deep72_at_of_nearLow_of_nine_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hHb : ∀ t, ρ t ≤ L + 9) (a : Fin n) (hai : a.val < i.val) (hnear : i.val ≤ a.val + 67)
    (ha : ρ a ≤ L + 2) (d : Fin (n - i.val))
    (e : Fin (n - i.val)) (hed : e.val < d.val) (he : L + 9 ≤ armG ρ i e) :
    ∃ j k l : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧ (l.val : ℤ) + (L + 7 - armG ρ i d) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 ∧ L + 7 ≤ armG ρ i l := by
  have hi := i.isLt
  have hen := e.isLt
  have hBlt : i.val + e.val < n := by omega
  set B : Fin n := ⟨i.val + e.val, hBlt⟩ with hBdef
  have hBv : ρ B = armG ρ i e := rfl
  have hab : a.val < B.val := by simp only [hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr a B hab L ha (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega)
  have hBval : B.val = i.val + e.val := rfl
  have hjlt : r.val - i.val < n - i.val := by omega
  have hklt : r'.val - i.val < n - i.val := by omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  -- the arm needs `L + 9 - armG ρ i d` steps to come down from the ascent to the descent
  have hstep : (e.val : ℤ) + (L + 9 - armG ρ i d) ≤ (d.val : ℤ) :=
    isLip_index_gap' (armG_isLip hlip i) (by omega) _ (by omega)
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · omega
  · rw [hjv]; omega
  · rw [hkv]; omega
  · omega

/-- **The deep-floor clause of `w72` on the forward arm**, from a low time near the basepoint and an
ascent to `L + 9` before every descent to the floor. -/
theorem deep72_of_nearLowT_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hnl : NearLowT ρ i L) (hnine : NineBeforeDeep (armG ρ i) L) :
    Deep72 (armG ρ i) L := by
  obtain ⟨a, hai, hnear, ha⟩ := hnl
  intro d hd
  obtain ⟨e, hed, he⟩ := hnine d hd
  exact deep72_at_of_nearLow_of_nine_armG hcr hlip i L hHb a hai hnear ha d e hed he

/-! ## The case the assembly does not cover -/

/-- **Both arms reach the top of the band.** The assembly of batch 68 assumes the partner stops
below `L + 9`; over the corpus that is every crossing (the `w8` side reaches `L + 9` at 282 of the
461 and the partner at 179, never both — `census-batch68.log`, and 0 of the 87 high-run crossings in
`census-batch69.log`), but no proof of it is known, so the configuration is named here as a case of
the branch rather than excluded. -/
def BothNineL5 {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  (∃ j : Fin (n - i.val), L + 9 ≤ armG ρ i j) ∧ (∃ j : Fin (i.val + 1), L + 9 ≤ armT ρ i j)

/-- **The two cases, named.** Either the backward arm stops below `L + 9` — the hypothesis the
assembly carries — or, where the forward arm has reached `L + 9`, both arms do. -/
theorem armT_no_nine_or_bothNine {i : Fin n} {L : ℤ} (hHb : ∀ t, ρ t ≤ L + 9)
    (e : Fin (n - i.val)) (he : L + 9 ≤ armG ρ i e) :
    (∀ j, armT ρ i j ≤ L + 8) ∨ BothNineL5 ρ i L := by
  by_cases h : ∃ j : Fin (i.val + 1), L + 9 ≤ armT ρ i j
  · exact Or.inr ⟨⟨e, he⟩, h⟩
  · push_neg at h
    exact Or.inl fun j => by have := h j; have := hHb (⟨i.val - j.val, by omega⟩ : Fin n); omega

/-! ## Where the near low time can be read off -/

/-- **A descent of the backward arm within 67 steps of the basepoint is a near low time.** This is
the form the census measures: the partner of a high-running `w8` side fails `w8`, so it has a
descent to `L + 2` or below (`w8_floor_fail_of_not_w8`), and what the argument needs of that descent
is only that it is close to the basepoint. -/
theorem nearLowT_of_armT_low {i : Fin n} {L : ℤ} (e : Fin (i.val + 1)) (he0 : 0 < e.val)
    (henear : e.val ≤ 67) (he : armT ρ i e ≤ L + 2) : NearLowT ρ i L := by
  have hi := i.isLt
  have hen := e.isLt
  refine ⟨⟨i.val - e.val, by omega⟩, ?_, ?_, ?_⟩
  · show i.val - e.val < i.val
    omega
  · show i.val ≤ (i.val - e.val) + 67
    omega
  · show ρ ⟨i.val - e.val, _⟩ ≤ L + 2
    exact he

/-- **The mirror.** -/
theorem nearLowG_of_armG_low {i : Fin n} {L : ℤ} (e : Fin (n - i.val)) (he0 : 0 < e.val)
    (henear : e.val ≤ 67) (he : armG ρ i e ≤ L + 2) : NearLowG ρ i L := by
  have hi := i.isLt
  have hen := e.isLt
  refine ⟨⟨i.val + e.val, by omega⟩, ?_, ?_, ?_⟩
  · show i.val < i.val + e.val
    omega
  · show i.val + e.val ≤ i.val + 67
    omega
  · show ρ ⟨i.val + e.val, _⟩ ≤ L + 2
    exact he

end Pair

end HPC.Fold
