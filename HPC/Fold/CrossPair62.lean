import HPC.Fold.CrossW71
import HPC.Fold.ValleyFar

/-!
# The crossing on the boundary of the timing law: what the pairing supplies

Batch 61 left the branch `L + 5` resting on the *crossings* — the basepoints of a faithful pair
whose two arms are served by different walks of the list — and identified, for each side of a
crossing, the clause of

```
w71 : direct (P, K, M) = (L+5, L+7, L+1)     L+4 → L+7 → L+1 → L+8 → L+1
```

that the side does not already own. The `w8` side owns `w71`'s floor clause
(`leg4Land_w71_floor_of_w8`) and owes its **ceiling** clause: before an ascent to `L + 9`, a time
at `L + 6` or above and, six steps later, one at `L + 2` or below, itself `f d - L - 2` steps
before the ascent.

This file reads that clause off the *pairing*, and says exactly how far the reading gets.

## The crooked pair across the basepoint

`cross_peak_valley_core` is the whole of the input. If the sequence stands at `L + 2` or below at
an index `a` and at `L + 9` or above at a later index `b`, crookedness puts between them a peak
`r` and, after it, a valley `r'`, and the timing law spaces all four:

```
a + 70 ≤ r,   r + 29 ≤ r',   r' + 70 ≤ b,   ρ r ≥ L + 7,   ρ r' ≤ ρ a + 1.
```

Every index gap the landmark sentence asks for (`3`, `6`, `7`) is dwarfed by `70`, `29`, `70`: the
sentence's arithmetic is free here. The *level* is not: the valley the pairing supplies sits at
`ρ a + 1`, one level above the partner's own descent.

## Where the witnesses sit

At a crossing take `a = i - dT` (the partner arm's descent to `L + 2`) and `b = i + dG` (the `w8`
side's ascent to `L + 9`). `cross_peak_valley_armG` shows the peak — and hence the valley — lies
**on the `w8` side of the basepoint**: were the peak on the partner arm it would be, by the
seventy steps that separate it from `a`, exactly the landmark that `w8`'s floor clause asks for at
the partner's descent, which at a crossing the partner does not have. So both witnesses are times
of the arm that owes the clause.

## What is supplied, and what is not

* `leg4Land_w71_of_w8_of_low1` — **the `w8` side owes `w71` nothing but a valley at `L + 1`.** If
  before every ascent to `L + 9` the arm has a time at `L + 1` or below, seven steps earlier, the
  whole of `w71` follows: the peak for the ceiling clause is `w8`'s own floor landmark at that
  valley, and the index gap `6` it needs is the five the walk gives plus the one the level `L + 1`
  buys.
* `leg4Land_w71_ceil_of_cross_low1` — and at a crossing whose partner arm descends to `L + 1`, the
  pairing supplies exactly that: `ρ r' ≤ ρ a + 1 ≤ L + 2`; with `w8`'s floor landmark at `r'` the
  ceiling clause of `w71` is complete.
* `leg4Land_w72_ceil_of_cross` — when the partner descends only to `L + 2` the valley is at
  `L + 3`, and the clause that closes is the ceiling clause of the **fifth** walk
  `w72 = L+4 → L+7 → L+2 → L+8 → L+1`, whose valley level is `M + 1 = L + 3`. Its peak is the
  crooked peak `r` itself.
* `leg4Land_w72_of_cross_of_floor1` — so the `w8` side of a crossing satisfies `w72` in full as
  soon as it stays at `L + 1` or above: `w72`'s deep-floor clause triggers only at `L`.

**Where it stops.** Not at an index: every index gap is supplied with room to spare. At a level,
and at exactly one level — the crooked valley is at `ρ a + 1`, and `w71` asks for `L + 2` while
the partner's descent is only known to reach `L + 2`. One level lower on the partner arm, or one
level higher in the walk (`w72`), and the clause closes.
-/

namespace HPC.Fold

/-! ## The crooked pair across the basepoint -/

/-- **A low index and a later high index put a peak and a valley between them, far apart.**
Crookedness supplies the peak `r` at `ρ b - 1` or just below and the valley `r'` at `ρ a + 1` or
just below; the timing law (`ivSep`, through `z 6 = 71` and `z 5 = 30`) spaces the four indices. -/
theorem cross_peak_valley_core {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L + 2) (hb : L + 9 ≤ ρ b) :
    ∃ r r' : Fin n, a.val + 70 ≤ r.val ∧ r.val + 29 ≤ r'.val ∧ r'.val + 70 ≤ b.val ∧
      L + 7 ≤ ρ r ∧ ρ r' ≤ ρ a + 1 := by
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (ρ a) (ρ b)
      ⟨a, by simp, le_rfl, hcr.le a⟩ ⟨b, by simp, le_rfl, hcr.le b⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  -- the peak is seventy steps after `a`
  have h1 : a.val + 70 ≤ r.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr a r (by omega) 6 (ρ a) (ρ b - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  -- the valley is twenty-nine steps after the peak
  have h2 : r.val + 29 ≤ r'.val := by
    have hz : z 5 = 30 := by decide
    rcases ivSep hcr r' r (by omega) 5 (ρ a + 1) (ρ b - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  -- and `b` is seventy steps after the valley
  have h3 : r'.val + 70 ≤ b.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr r' b (by omega) 6 (ρ a + 1) (ρ b) (by push_cast; omega)
      hr'1 hr'2 le_rfl (hcr.le b) with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega⟩

/-- **The timing law read on one arm.** Two times of the forward arm whose levels are `D` apart
are `z D - 1` steps apart, so every index gap the landmark sentence asks for between two
landmarks of an arm is supplied with room to spare. -/
theorem armG_sep {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (p q : Fin (n - i.val)) (D : ℕ) (hpq : p.val ≤ q.val)
    (hlev : armG ρ i q + (D : ℤ) ≤ armG ρ i p) :
    p.val + z D ≤ q.val + 1 := by
  have hi := i.isLt
  have hp := p.isLt
  have hq := q.isLt
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : z 0 = 1 := rfl
    omega
  set P : Fin n := ⟨i.val + p.val, by omega⟩ with hPdef
  set Q : Fin n := ⟨i.val + q.val, by omega⟩ with hQdef
  have hPv : ρ P = armG ρ i p := rfl
  have hQv : ρ Q = armG ρ i q := rfl
  have hPval : P.val = i.val + p.val := rfl
  have hQval : Q.val = i.val + q.val := rfl
  have hDpos : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hne : Q.val ≠ P.val := by
    intro hc
    have hqp : p = q := Fin.ext (by omega)
    rw [hqp] at hlev
    omega
  rcases ivSep hcr Q P hne D (ρ Q) (ρ P) (by omega) le_rfl (hcr.le Q) le_rfl (hcr.le P) with h | h
  · have hz1 : z 1 = 2 := rfl
    have hzp := z_mono (show 1 ≤ D from hD)
    omega
  · omega

/-! ## Both witnesses lie on the side that owes the clause -/

/-- **The peak and the valley of the crossing pair are times of the `w8` arm.** The hypothesis
`hbad` is what a crossing gives on the partner arm: its descent at `dT` has no time at `L + 7` or
above before it, at index at least two. Were the crooked peak on the partner arm it would violate
that, since the timing law puts it seventy steps after the descent's own index. -/
theorem cross_peak_valley_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 2) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ R R' : Fin (n - i.val), 2 ≤ R.val ∧ R.val + 29 ≤ R'.val ∧ R'.val + 70 ≤ dG.val ∧
      L + 7 ≤ armG ρ i R ∧ armG ρ i R' ≤ armT ρ i dT + 1 := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  set a : Fin n := ⟨i.val - dT.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i dT := rfl
  have hbv : ρ b = armG ρ i dG := rfl
  have hab : a.val < b.val := by
    have : a.val ≤ i.val := by simp only [hadef]; omega
    rcases Nat.eq_zero_or_pos dG.val with h | h
    · exfalso
      have : b = i := Fin.ext (by simp only [hbdef]; omega)
      rw [this, hp] at hbv
      omega
    · simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hrlev, hr'lev⟩ :=
    cross_peak_valley_core hcr a b hab L (by omega) (by omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  have havl : a.val = i.val - dT.val := rfl
  have hbvl : b.val = i.val + dG.val := rfl
  -- the peak cannot lie on the partner arm
  have hri : i.val < r.val := by
    by_contra hc
    push_neg at hc
    have hj : i.val - r.val < i.val + 1 := by omega
    have hjv : armT ρ i ⟨i.val - r.val, hj⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    -- the peak is at least two steps from the basepoint
    have h2le : 2 ≤ i.val - r.val := by
      have := isLip_index_gap' hlip (j := r) (k := i) (by omega) 2 (by omega)
      omega
    have := hbad ⟨i.val - r.val, hj⟩ (by simpa using h2le) (by simp; omega)
    rw [hjv] at this
    omega
  have hr'i : i.val < r'.val := by omega
  refine ⟨⟨r.val - i.val, by omega⟩, ⟨r'.val - i.val, by omega⟩, ?_, by simp; omega,
    by simp; omega, ?_, ?_⟩
  · have := isLip_index_gap hlip (j := i) (k := r) (by omega) 2 (by omega)
    simp only []
    omega
  · show ρ ⟨i.val + (r.val - i.val), _⟩ ≥ L + 7
    rw [show (⟨i.val + (r.val - i.val), by omega⟩ : Fin n) = r from Fin.ext (by simp; omega)]
    exact hrlev
  · show ρ ⟨i.val + (r'.val - i.val), _⟩ ≤ armT ρ i dT + 1
    rw [show (⟨i.val + (r'.val - i.val), by omega⟩ : Fin n) = r' from Fin.ext (by simp; omega)]
    omega

/-- **What the crossing gives on the partner arm, and how far it is from `hbad`.** If the floor
clause of `w8` fails at the partner's descent `dT`, then the partner has no time at `L + 7` or
above at index at least **four** and at least seven steps before it. `cross_peak_valley_armG`
asks for the same from index **two**: the gap between the two is exactly a partner peak at
`L + 7` or above at arm index `2` or `3`. -/
theorem crossBad_of_floor_fail {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (hL : ∀ j, L ≤ f j)
    (dT : Fin m) (hT : f dT ≤ L + 2)
    (hfail : ¬ ∃ j : Fin m, 4 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (L + 7 - f dT) ≤ (dT.val : ℤ) ∧
      L + 7 ≤ f j) :
    ∀ j : Fin m, 4 ≤ j.val → j.val + 7 ≤ dT.val → f j ≤ L + 6 := by
  intro j h4 h7
  by_contra hc
  exact hfail ⟨j, by exact_mod_cast h4, by have := hL dT; omega, by omega⟩

/-! ## What the valley buys -/

/-- **The `w8` side owes `w71` nothing but a valley at `L + 1`.** Given the landmark sentence of
`w8` and, before every ascent to `L + 9`, a time at `L + 1` or below seven steps earlier, the
whole landmark sentence of `w71` follows: `w8`'s floor clause at the valley supplies the peak, and
the level `L + 1` buys the extra step of the gap `K - M = 6`. -/
theorem leg4Land_w71_of_w8_of_low1 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (h8 : Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5))
    (hval : ∀ d : Fin m, L + 9 ≤ f d →
      ∃ k : Fin m, f k ≤ L + 1 ∧ (k.val : ℤ) + 7 ≤ (d.val : ℤ)) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    have hd9 := hH d
    obtain ⟨k, hk1, hk2⟩ := hval d (by omega)
    obtain ⟨j, hj1, hj2, hj3⟩ := h8.1 k (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **At a crossing whose partner arm descends to `L + 1`, the pairing supplies the ceiling
clause of `w71`.** The crooked valley sits at `ρ a + 1 ≤ L + 2`, and `w8`'s floor landmark at it
is the peak. -/
theorem leg4Land_w71_ceil_of_cross_low1 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 1) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i dG - (L + 2)) ≤ (dG.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 2 := by
  obtain ⟨R, R', hR, hRR', hR'd, hRlev, hR'lev⟩ :=
    cross_peak_valley_armG hcr hlip i L hp dT dG (by omega) hG hbad
  have hR'2 : armG ρ i R' ≤ L + 2 := by omega
  obtain ⟨j, hj1, hj2, hj3⟩ := h8.1 R' (by omega)
  have hd9 : armG ρ i dG ≤ L + 9 :=
    hHb ⟨i.val + dG.val, by have := dG.isLt; have := i.isLt; omega⟩
  -- the index gap the walk asks for is the timing law's, not the walk's
  have hgap : j.val + z 5 ≤ R'.val + 1 :=
    armG_sep hcr i j R' 5 (by omega) (by omega)
  have hz : z 5 = 30 := by decide
  exact ⟨j, R', by omega, by omega, by omega, by omega, hR'2⟩

/-! ## The fifth walk closes on the valley the pairing gives -/

/-- **The ceiling clause of `w72` is exactly what the pairing supplies.** The walk
`w72 = L+4 → L+7 → L+2 → L+8 → L+1` asks its ceiling valley to sit at `M + 1 = L + 3`, which is
where the crooked valley is when the partner arm descends to `L + 2`; and it asks its peak to sit
at `K - 1 = L + 6`, which is where the crooked peak is. -/
theorem leg4Land_w72_ceil_of_cross {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 2) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i dG - (L + 3)) ≤ (dG.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 := by
  obtain ⟨R, R', hR, hRR', hR'd, hRlev, hR'lev⟩ :=
    cross_peak_valley_armG hcr hlip i L hp dT dG hT hG hbad
  have hd9 : armG ρ i dG ≤ L + 9 :=
    hHb ⟨i.val + dG.val, by have := dG.isLt; have := i.isLt; omega⟩
  have hlipG := armG_isLip hlip i
  have hRn := R.isLt
  have hR'n := R'.isLt
  rcases le_or_gt 3 R.val with hcase | hcase
  · exact ⟨R, R', by exact_mod_cast hcase, by omega, by omega, by omega, by omega⟩
  · -- the peak is at index two; the next step is still at `L + 6`
    have hR2 : R.val = 2 := by omega
    have h3 : (3 : ℕ) < n - i.val := by omega
    have hv3 : (⟨3, h3⟩ : Fin (n - i.val)).val = 3 := rfl
    refine ⟨⟨3, h3⟩, R', by omega, by omega, by omega, ?_, by omega⟩
    have := isLip_gap hlipG 1 R ⟨3, h3⟩ (by omega)
    omega

/-- **The `w8` side of a crossing satisfies `w72` in full as soon as it stays at `L + 1` or
above.** The floor clause is `w8`'s (one level and one index over), the deep-floor clause of `w72`
triggers only at `L`, and the ceiling clause is the pairing's. -/
theorem leg4Land_w72_of_cross_of_floor1 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 2 ∧
        (∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6)) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    have := hLb ⟨i.val + d.val, by have := d.isLt; omega⟩
    have he : armG ρ i d = ρ ⟨i.val + d.val, by have := d.isLt; omega⟩ := rfl
    omega
  · intro d hd
    obtain ⟨dT, hT, hbad⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w72_ceil_of_cross hcr hlip i L hp hHb dT d hT (by omega) hbad
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

end HPC.Fold
