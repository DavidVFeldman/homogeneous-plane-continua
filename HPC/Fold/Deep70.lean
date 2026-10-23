import HPC.Fold.Ceil69

/-!
# The deep-floor clauses of `w72` at a high-run crossing, and the symmetric assembly

Batch 69 left the branch `L + 5` owing three statements about the two arms of one crossing: the
distance (`NearLowT` / `NearLowG`), the partner's deep-floor clause where the band reaches the
floor, and the emptiness of `BothNineL5`. The widened census of batch 70 (`census-batch70.c`,
log `census-batch70.log`) settles two of them, in opposite directions:

* **`BothNineL5` is inhabited.** On a corpus of 7040 faithful pairs of span nine — windows of
  `bing 0 N` for `N = 10, …, 13` at grid and random offsets, the chains outside Bing's family,
  concatenations of Bing blocks, and the shaved, filled and mixed pairs of all of them — both arms
  of a crossing reach `L + 9` at 39 of the 229 high-run crossings and at 67 of the 1351 crossings,
  where the batch-68/69 corpus had none. So the hypothesis `hnineT : ∀ j, armT ρ i j ≤ L + 8` that
  the batch-68 assembly carries is **not** innocuous.
* **The partner's deep-floor clause is a theorem** at a high-run crossing, and so is the running
  arm's; neither needs the distance hypothesis.

Both facts point the same way, and this file draws the consequence: the assembly is made
**symmetric**. `leg4Land_w72_of_tri_of_mid2_of_ceil` is not about the `w8` side of anything — it
reads `w72` off any arm of the branch with `Mid2Floor`, the deep-floor clause and the ceiling
clause. So:

> **`s3_span_nine_mid5_of_cross_ceil_deep`** — at a crossing of the trichotomy, if both arms have
> `Deep72` and `Ceil72`, both fold onto `w72`.

and the two deep-floor clauses are discharged where one arm runs high:

> **`deep72_of_nineBeforeDeep_armG`** (and its mirror) — an arm whose every descent to the floor
> follows one of its own ascents to `L + 9` has `w72`'s deep-floor clause. The pairing is read
> *inside the arm*, from the ascent down to the descent (`crooked_valley_peak_high9_mid`): it
> returns the valley and the peak the clause wants, and the ascent itself is the first landmark.
> No distance hypothesis, and no `NearLow`.
>
> **`deep72_partner_armT_of_highRun_armG`** (and its mirror) — the partner of a high-running arm
> has `w72`'s deep-floor clause. The pairing is read **across the basepoint**, from the partner's
> floor descent to the running arm's link carrying `L + 9`; the high run is exactly what forces its
> two landmarks back onto the partner's arm, since the running arm has nothing at `L + 2` or below
> before its ascent while the pairing's valley is at `L + 1` or below. `Mid2Floor` on the partner
> supplies the third landmark, at the descent to `L + 2` that the Lipschitz law puts between the
> valley and the basepoint. This is the seam batch 70 §2.3 asks about, closed by reading the
> pairing against a link carrying `L + 9` rather than against a time at `L + 8`.

What is left of the branch at `L + 5` is therefore **one** statement, not three: `Ceil72` on an arm
that runs high, which is what `NearLowT` / `NearLowG` buys (`ceil72_of_nearLowT_armG`). The census
finds the distance 56 to 65 at all 229 high-run crossings of the widened corpus, against the bound
67 of that reading.
-/

namespace HPC.Fold

/-! ## A discrete intermediate value theorem for a Lipschitz sequence -/

/-- **A 1-Lipschitz sequence takes every level between two of its values.** -/
theorem exists_eq_between_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) :
    ∀ (d : ℕ) (a b : Fin m), b.val = a.val + d → ∀ v : ℤ, f a ≤ v → v ≤ f b →
      ∃ c : Fin m, a.val ≤ c.val ∧ c.val ≤ b.val ∧ f c = v := by
  intro d
  induction d with
  | zero =>
      intro a b hb v h1 h2
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, le_rfl, le_rfl, le_antisymm h1 h2⟩
  | succ d ih =>
      intro a b hb v h1 h2
      have hbm := b.isLt
      by_cases hv : f a = v
      · exact ⟨a, le_rfl, by omega, hv⟩
      · have hlt : a.val + 1 < m := by omega
        have hstep := hf a ⟨a.val + 1, hlt⟩ rfl
        rw [abs_le] at hstep
        have hle : f ⟨a.val + 1, hlt⟩ ≤ v := by
          have : f a < v := lt_of_le_of_ne h1 hv
          omega
        obtain ⟨c, hc1, hc2, hc3⟩ := ih ⟨a.val + 1, hlt⟩ b (by simp; omega) v hle h2
        exact ⟨c, by simp at hc1; omega, hc2, hc3⟩

/-- **The same, descending.** -/
theorem exists_eq_between_isLip' {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f)
    (d : ℕ) (a b : Fin m) (hb : b.val = a.val + d) (v : ℤ) (h1 : f b ≤ v) (h2 : v ≤ f a) :
    ∃ c : Fin m, a.val ≤ c.val ∧ c.val ≤ b.val ∧ f c = v := by
  have hneg : IsLip (fun t => -f t) := by
    intro j j' hjj'
    have := hf j j' hjj'
    rw [abs_le] at this ⊢
    constructor <;> simp <;> omega
  obtain ⟨c, hc1, hc2, hc3⟩ :=
    exists_eq_between_isLip hneg d a b hb (-v) (by simpa using h2) (by simpa using h1)
  exact ⟨c, hc1, hc2, by simpa using hc3⟩

/-- The same, in the form used below: a level strictly between the values at two indices is taken
strictly between them. -/
theorem exists_eq_strict_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) {a b : Fin m}
    (hab : a.val ≤ b.val) {v : ℤ} (h1 : f a < v) (h2 : v < f b) :
    ∃ c : Fin m, a.val < c.val ∧ c.val < b.val ∧ f c = v := by
  obtain ⟨c, hc1, hc2, hc3⟩ :=
    exists_eq_between_isLip hf (b.val - a.val) a b (by omega) v (by omega) (by omega)
  refine ⟨c, ?_, ?_, hc3⟩
  · rcases Nat.eq_or_lt_of_le hc1 with h | h
    · exact absurd hc3 (by rw [show c = a from Fin.ext h.symm]; omega)
    · exact h
  · rcases Nat.eq_or_lt_of_le hc2 with h | h
    · exact absurd hc3 (by rw [show c = b from Fin.ext h]; omega)
    · exact h

/-- The descending form of the same. -/
theorem exists_eq_strict_isLip' {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) {a b : Fin m}
    (hab : a.val ≤ b.val) {v : ℤ} (h1 : f b < v) (h2 : v < f a) :
    ∃ c : Fin m, a.val < c.val ∧ c.val < b.val ∧ f c = v := by
  obtain ⟨c, hc1, hc2, hc3⟩ :=
    exists_eq_between_isLip' hf (b.val - a.val) a b (by omega) v (by omega) (by omega)
  refine ⟨c, ?_, ?_, hc3⟩
  · rcases Nat.eq_or_lt_of_le hc1 with h | h
    · exact absurd hc3 (by rw [show c = a from Fin.ext h.symm]; omega)
    · exact h
  · rcases Nat.eq_or_lt_of_le hc2 with h | h
    · exact absurd hc3 (by rw [show c = b from Fin.ext h]; omega)
    · exact h

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The high run, named -/

/-- **A high run on the forward arm**: an ascent to `L + 9` with nothing at `L + 2` or below before
it. This is the failure of `DeepFirst2` inside the band, written out. -/
def HighRunG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ e : Fin (n - i.val), L + 9 ≤ armG ρ i e ∧
    ∀ d : Fin (n - i.val), d.val < e.val → L + 3 ≤ armG ρ i d

/-- **The mirror, on the backward arm.** -/
def HighRunT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ e : Fin (i.val + 1), L + 9 ≤ armT ρ i e ∧
    ∀ d : Fin (i.val + 1), d.val < e.val → L + 3 ≤ armT ρ i d

theorem highRunG_of_not_deepFirst2 (i : Fin n) (L : ℤ)
    (h : ¬ DeepFirst2 (armG ρ i) L) : HighRunG ρ i L := by
  unfold DeepFirst2 at h
  push_neg at h
  obtain ⟨e, he, hno⟩ := h
  exact ⟨e, he, fun d hd => by have := hno d hd; omega⟩

theorem highRunT_of_not_deepFirst2 (i : Fin n) (L : ℤ)
    (h : ¬ DeepFirst2 (armT ρ i) L) : HighRunT ρ i L := by
  unfold DeepFirst2 at h
  push_neg at h
  obtain ⟨e, he, hno⟩ := h
  exact ⟨e, he, fun d hd => by have := hno d hd; omega⟩

/-- **A high run puts every descent to the floor after an ascent.** -/
theorem nineBeforeDeep_of_highRunG {i : Fin n} {L : ℤ} (h : HighRunG ρ i L) :
    NineBeforeDeep (armG ρ i) L := by
  obtain ⟨e, he, hlow⟩ := h
  intro d hd
  refine ⟨e, ?_, he⟩
  rcases Nat.lt_trichotomy e.val d.val with h1 | h1 | h1
  · exact h1
  · exact absurd hd (by rw [show d = e from Fin.ext h1.symm]; omega)
  · exact absurd hd (by have := hlow d h1; omega)

/-- **The mirror.** -/
theorem nineBeforeDeep_of_highRunT {i : Fin n} {L : ℤ} (h : HighRunT ρ i L) :
    NineBeforeDeep (armT ρ i) L := by
  obtain ⟨e, he, hlow⟩ := h
  intro d hd
  refine ⟨e, ?_, he⟩
  rcases Nat.lt_trichotomy e.val d.val with h1 | h1 | h1
  · exact h1
  · exact absurd hd (by rw [show d = e from Fin.ext h1.symm]; omega)
  · exact absurd hd (by have := hlow d h1; omega)

/-! ## The deep-floor clause inside one arm -/

/-- **`w72`'s deep-floor clause on the forward arm, from an ascent before the descent.** The
pairing is read inside the arm, from the ascent to the descent: it returns a valley at `L + 1` or
below seventy steps after the ascent and, twenty-nine steps later, a peak at `L + 7` or above,
itself seventy steps before the descent. The ascent is the clause's first landmark, at arm index
four or more by the Lipschitz law. No distance hypothesis is used. -/
theorem deep72_at_of_nine_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d e : Fin (n - i.val)) (hed : e.val < d.val) (he : L + 9 ≤ armG ρ i e)
    (hd : armG ρ i d ≤ L) :
    ∃ j k l : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧ (l.val : ℤ) + (L + 7 - armG ρ i d) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 ∧ L + 7 ≤ armG ρ i l := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have hm : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hAlt : i.val + e.val < n := by omega
  have hBlt : i.val + d.val < n := by omega
  set A : Fin n := ⟨i.val + e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armG ρ i e := rfl
  have hBv : ρ B = armG ρ i d := rfl
  have hab : A.val < B.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9_mid hcr A B hab L (by rw [hAv]; exact hHb _)
      (by have := hcr.le A; rw [hAv] at this; omega) (by rw [hBv]; omega)
  have hAval : A.val = i.val + e.val := rfl
  have hBval : B.val = i.val + d.val := rfl
  have hklt : r.val - i.val < n - i.val := by omega
  have hllt : r'.val - i.val < n - i.val := by omega
  have hkv : armG ρ i ⟨r.val - i.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hlv : armG ρ i ⟨r'.val - i.val, hllt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  -- the ascent is at arm index four or more
  have he3 : 4 ≤ (e.val : ℤ) := by
    have := isLip_index_gap (armG_isLip hlip i) (j := ⟨0, hm⟩) (k := e) (Nat.zero_le _) 4
      (by rw [h0G]; omega)
    simpa using this
  have hdL : armG ρ i d = L := le_antisymm hd (by rw [← hBv]; exact hLb _)
  refine ⟨e, ⟨r.val - i.val, hklt⟩, ⟨r'.val - i.val, hllt⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only [hdL]
    omega
  · omega
  · rw [hkv]
    have : ρ B = L := by rw [hBv, hdL]
    omega
  · rw [hlv]; omega

theorem deep72_of_nineBeforeDeep_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hnine : NineBeforeDeep (armG ρ i) L) : Deep72 (armG ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hnine d hd
  exact deep72_at_of_nine_armG hcr hlip i L hp hLb hHb d e hed he hd

/-- **The mirror, on the backward arm.** -/
theorem deep72_at_of_nine_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d e : Fin (i.val + 1)) (hed : e.val < d.val) (he : L + 9 ≤ armT ρ i e)
    (hd : armT ρ i d ≤ L) :
    ∃ j k l : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧ (l.val : ℤ) + (L + 7 - armT ρ i d) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 3 ∧ L + 7 ≤ armT ρ i l := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have hm : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hAlt : i.val - e.val < n := by omega
  have hBlt : i.val - d.val < n := by omega
  set A : Fin n := ⟨i.val - e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armT ρ i e := rfl
  have hBv : ρ B = armT ρ i d := rfl
  have hab : B.val < A.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr B A hab L (by rw [hBv]; omega)
      (by rw [hAv]; exact hHb _) (by have := hcr.le A; rw [hAv] at this; omega)
  have hAval : A.val = i.val - e.val := rfl
  have hBval : B.val = i.val - d.val := rfl
  have hklt : i.val - r'.val < i.val + 1 := by omega
  have hllt : i.val - r.val < i.val + 1 := by omega
  have hkv : armT ρ i ⟨i.val - r'.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hlv : armT ρ i ⟨i.val - r.val, hllt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  have he3 : 4 ≤ (e.val : ℤ) := by
    have := isLip_index_gap (armT_isLip hlip i) (j := ⟨0, hm⟩) (k := e) (Nat.zero_le _) 4
      (by rw [h0T]; omega)
    simpa using this
  have hdL : armT ρ i d = L := le_antisymm hd (by rw [← hBv]; exact hLb _)
  refine ⟨e, ⟨i.val - r'.val, hklt⟩, ⟨i.val - r.val, hllt⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only [hdL]
    omega
  · omega
  · rw [hkv]
    have : ρ B = L := by rw [hBv, hdL]
    omega
  · rw [hlv]; omega

theorem deep72_of_nineBeforeDeep_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hnine : NineBeforeDeep (armT ρ i) L) : Deep72 (armT ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hnine d hd
  exact deep72_at_of_nine_armT hcr hlip i L hp hLb hHb d e hed he hd

/-! ## The deep-floor clause of the partner, read across the basepoint -/

/-- **The partner of a high-running forward arm has `w72`'s deep-floor clause.** At a descent of
the backward arm to the floor, the pairing is read between that descent and the forward arm's link
carrying `L + 9`. Its valley is at `L + 1` or below, and the high run says the forward arm has
nothing at `L + 2` or below before its ascent, so the valley — and with it the peak before it —
lies on the **backward** arm. `Mid2Floor` on the backward arm supplies the third landmark, read at
the descent to `L + 2` that the Lipschitz law puts between the valley and the basepoint. -/
theorem deep72_partner_armT_of_highRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hrun : HighRunG ρ i L) (hmid : Mid2Floor (armT ρ i) L) : Deep72 (armT ρ i) L := by
  obtain ⟨e, he, hlow⟩ := hrun
  intro dd hdd
  have hi := i.isLt
  have hen := e.isLt
  have hddn := dd.isLt
  -- the descent is not the basepoint
  have hdd0 : 0 < dd.val := by
    rcases Nat.eq_zero_or_pos dd.val with h | h
    · exfalso
      have hb : armT ρ i dd = L + 5 := by
        rw [show dd = ((⟨0, by omega⟩ : Fin (i.val + 1))) from Fin.ext h]
        show ρ ⟨i.val - 0, _⟩ = L + 5
        rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
        exact hp
      omega
    · exact h
  have hclt : i.val - dd.val < n := by omega
  have hBlt : i.val + e.val < n := by omega
  set c : Fin n := ⟨i.val - dd.val, hclt⟩ with hcdef
  set B : Fin n := ⟨i.val + e.val, hBlt⟩ with hBdef
  have hcv : ρ c = armT ρ i dd := rfl
  have hBv : ρ B = armG ρ i e := rfl
  have hcL : ρ c = L := le_antisymm (by rw [hcv]; exact hdd) (hLb _)
  have hcB : c.val < B.val := by simp only [hcdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr c B hcB L (by omega)
      (by rw [hBv]; exact hHb _) (by have := hcr.le B; rw [hBv] at this; omega)
  have hcval : c.val = i.val - dd.val := rfl
  have hBval : B.val = i.val + e.val := rfl
  -- the high run pushes the pairing's valley back onto the backward arm
  have hr'i : r'.val < i.val := by
    by_contra hcon
    push_neg at hcon
    have hlt : r'.val - i.val < n - i.val := by omega
    have hvv : armG ρ i ⟨r'.val - i.val, hlt⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hlow ⟨r'.val - i.val, hlt⟩ (by show r'.val - i.val < e.val; omega)
    rw [hvv] at this
    omega
  -- the third landmark: the descent to `L + 2` between the valley and the basepoint
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    exists_eq_strict_isLip hlip (a := r') (b := i) (by omega) (v := L + 2) (by omega) (by omega)
  have hd2lt : i.val - x.val < i.val + 1 := by omega
  have hd2v : armT ρ i ⟨i.val - x.val, hd2lt⟩ = ρ x := by
    show ρ ⟨i.val - (i.val - x.val), _⟩ = ρ x
    congr 1
    exact Fin.ext (by show i.val - (i.val - x.val) = x.val; omega)
  obtain ⟨j, hj1, hj2, hj3⟩ := hmid ⟨i.val - x.val, hd2lt⟩ (by rw [hd2v, hx3])
  simp only [] at hj2
  have hklt : i.val - r'.val < i.val + 1 := by omega
  have hllt : i.val - r.val < i.val + 1 := by omega
  have hkv : armT ρ i ⟨i.val - r'.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hlv : armT ρ i ⟨i.val - r.val, hllt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  have hddL : armT ρ i dd = L := by rw [← hcv, hcL]
  refine ⟨j, ⟨i.val - r'.val, hklt⟩, ⟨i.val - r.val, hllt⟩, hj1, ?_, ?_, ?_, hj3, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only [hddL]
    omega
  · rw [hkv]; omega
  · rw [hlv]; omega

/-- **The mirror**, with the high run on the backward arm. -/
theorem deep72_partner_armG_of_highRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hrun : HighRunT ρ i L) (hmid : Mid2Floor (armG ρ i) L) : Deep72 (armG ρ i) L := by
  obtain ⟨e, he, hlow⟩ := hrun
  intro dd hdd
  have hi := i.isLt
  have hen := e.isLt
  have hddn := dd.isLt
  have hdd0 : 0 < dd.val := by
    rcases Nat.eq_zero_or_pos dd.val with h | h
    · exfalso
      have hb : armG ρ i dd = L + 5 := by
        rw [show dd = ((⟨0, by omega⟩ : Fin (n - i.val))) from Fin.ext h]
        show ρ ⟨i.val + 0, _⟩ = L + 5
        rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
        exact hp
      omega
    · exact h
  have hclt : i.val + dd.val < n := by omega
  have hBlt : i.val - e.val < n := by omega
  set c : Fin n := ⟨i.val + dd.val, hclt⟩ with hcdef
  set B : Fin n := ⟨i.val - e.val, hBlt⟩ with hBdef
  have hcv : ρ c = armG ρ i dd := rfl
  have hBv : ρ B = armT ρ i e := rfl
  have hcL : ρ c = L := le_antisymm (by rw [hcv]; exact hdd) (hLb _)
  have hBc : B.val < c.val := by simp only [hcdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9_mid hcr B c hBc L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) (by omega)
  have hcval : c.val = i.val + dd.val := rfl
  have hBval : B.val = i.val - e.val := rfl
  -- the high run pushes the pairing's valley forward onto the forward arm
  have hri : i.val < r.val := by
    by_contra hcon
    push_neg at hcon
    have hlt : i.val - r.val < i.val + 1 := by omega
    have hvv : armT ρ i ⟨i.val - r.val, hlt⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hlow ⟨i.val - r.val, hlt⟩ (by show i.val - r.val < e.val; omega)
    rw [hvv] at this
    omega
  -- the third landmark: the descent to `L + 2` between the basepoint and the valley
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    exists_eq_strict_isLip' hlip (a := i) (b := r) (by omega) (v := L + 2) (by omega) (by omega)
  have hd2lt : x.val - i.val < n - i.val := by omega
  have hd2v : armG ρ i ⟨x.val - i.val, hd2lt⟩ = ρ x := by
    show ρ ⟨i.val + (x.val - i.val), _⟩ = ρ x
    congr 1
    exact Fin.ext (by show i.val + (x.val - i.val) = x.val; omega)
  obtain ⟨j, hj1, hj2, hj3⟩ := hmid ⟨x.val - i.val, hd2lt⟩ (by rw [hd2v, hx3])
  simp only [] at hj2
  have hklt : r.val - i.val < n - i.val := by omega
  have hllt : r'.val - i.val < n - i.val := by omega
  have hkv : armG ρ i ⟨r.val - i.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hlv : armG ρ i ⟨r'.val - i.val, hllt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  have hddL : armG ρ i dd = L := by rw [← hcv, hcL]
  refine ⟨j, ⟨r.val - i.val, hklt⟩, ⟨r'.val - i.val, hllt⟩, hj1, ?_, ?_, ?_, hj3, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only [hddL]
    omega
  · rw [hkv]; omega
  · rw [hlv]; omega

/-! ## The symmetric assembly -/

/-- **Where the arm stops below `L + 9` its ceiling clause is vacuous.** -/
theorem ceil72_of_no_nine {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ∀ j, f j ≤ L + 8) :
    Ceil72 f L := fun d hd => absurd (h d) (by omega)

/-- **The symmetric assembly.** At a crossing of the trichotomy at the branch `L + 5`, if both arms
have `w72`'s deep-floor clause and its ceiling clause, both fold onto `w72`. Nothing here is asked
of which walk serves which arm: `Mid2Floor` comes from the crossing (`crossMid2`), and the rest of
`w72` comes from the trichotomy on each arm separately. -/
theorem s3_span_nine_mid5_of_cross_ceil_deep (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L)
    (hceilG : Ceil72 (armG ρ i) L) (hceilT : Ceil72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  have hG72 := leg4Land_w72_of_tri_of_mid2_of_ceil hmG (armG_isLip hlip i) h0G (fun j => hLb _)
    (fun j => hHb _) hGlow hmidG hdeepG hceilG
  have hT72 := leg4Land_w72_of_tri_of_mid2_of_ceil hmT (armT_isLip hlip i) h0T (fun j => hLb _)
    (fun j => hHb _) hTlow hmidT hdeepT hceilT
  exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
    (leg4Window_w72 L) (by omega) (by omega) hG72 hT72

/-- **The high-run crossing, with both deep-floor clauses discharged.** At a crossing whose forward
arm runs high, the two deep-floor clauses are theorems, so the pair folds as soon as both arms have
`w72`'s ceiling clause. Neither `BothNineL5` nor the partner's deep-floor clause is assumed. -/
theorem s3_span_nine_mid5_of_cross_highRun_ceil_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L)
    (hceilG : Ceil72 (armG ρ i) L) (hceilT : Ceil72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  exact s3_span_nine_mid5_of_cross_ceil_deep hcr hlip i L hp hLb hHb hGlow hTlow hcross
    (deep72_of_nineBeforeDeep_armG hcr hlip i L hp hLb hHb (nineBeforeDeep_of_highRunG hrun))
    (deep72_partner_armT_of_highRun_armG hcr hlip i L hp hLb hHb hrun hmidT) hceilG hceilT

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRun_ceil_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L)
    (hceilG : Ceil72 (armG ρ i) L) (hceilT : Ceil72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  exact s3_span_nine_mid5_of_cross_ceil_deep hcr hlip i L hp hLb hHb hGlow hTlow hcross
    (deep72_partner_armG_of_highRun_armT hcr hlip i L hp hLb hHb hrun hmidG)
    (deep72_of_nineBeforeDeep_armT hcr hlip i L hp hLb hHb (nineBeforeDeep_of_highRunT hrun))
    hceilG hceilT

/-- **The branch at `L + 5` where the forward arm runs high, reduced to one statement.** With the
distance hypothesis on the partner's side the forward arm has its ceiling clause
(`ceil72_of_nearLowT_armG`), and the backward arm has its own by one of three routes: it stops
below `L + 9`, or it is deep first at `L + 2`, or it runs high itself and the mirror distance
hypothesis holds. -/
theorem s3_span_nine_mid5_of_cross_highRun_nearLowT_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) (hnl : NearLowT ρ i L)
    (hT : (∀ j, armT ρ i j ≤ L + 8) ∨ DeepFirst2 (armT ρ i) L ∨ NearLowG ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hceilT : Ceil72 (armT ρ i) L := by
    rcases hT with h | h | h
    · exact ceil72_of_no_nine h
    · exact ceil72_of_deepFirst2_armT hcr i L hHb h
    · exact ceil72_of_nearLowG_armT hcr i L hHb h
  exact s3_span_nine_mid5_of_cross_highRun_ceil_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross
    hrun (ceil72_of_nearLowT_armG hcr i L hHb hnl) hceilT

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRun_nearLowG_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) (hnl : NearLowG ρ i L)
    (hG : (∀ j, armG ρ i j ≤ L + 8) ∨ DeepFirst2 (armG ρ i) L ∨ NearLowT ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hceilG : Ceil72 (armG ρ i) L := by
    rcases hG with h | h | h
    · exact ceil72_of_no_nine h
    · exact ceil72_of_deepFirst2_armG hcr i L hHb h
    · exact ceil72_of_nearLowT_armG hcr i L hHb h
  exact s3_span_nine_mid5_of_cross_highRun_ceil_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross
    hrun hceilG (ceil72_of_nearLowG_armT hcr i L hHb hnl)

end Pair

end HPC.Fold
