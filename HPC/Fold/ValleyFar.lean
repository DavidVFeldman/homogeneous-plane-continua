import HPC.Fold.Timing
import HPC.Fold.Leg3Profile

/-!
# The far witness of the valley crossing, from the timing law

Batch 55 measured, at every pair of the valley residue, where the witness the V-criterion asks for
actually sits: always at level `L + 2` exactly, and always far — twenty-nine or thirty-one steps
from the ascent, never the time two or three steps from the basepoint that
`HPC/Fold/CrossValley.lean` looks at. This file proves that this is not an accident of the corpus
but a consequence of the crookedness clause **together with the timing law of Theorem 7**
(`minGap`, `HPC/Fold/Minimal.lean`), and with that it removes the residual configuration from the
valley crossing altogether.

## The argument

Let `X` be the arm failing `Leg3Valley`, at a descent `t` with `ρ t ≤ L + 1`, and `Y` the other
arm, at an ascent `s` with `L + 7 ≤ ρ s`. Apply the crookedness clause of the faithful model to
the pair `{s, t}` at the two levels `h = ρ s` and `k = ρ t`, which are at least six apart. It
returns two links strictly between them in chain order: one whose interval contains the level one
step inside the *far* end, and one whose interval contains the level one step inside the *near*
end. Reading it from the descent towards the ascent, the first is at `L + 6` or above and the
second at `L + 2` or below.

The point is that the two returned links are then pinned by `minGap`, which the earlier analysis
did not use:

* the high link `r` is five levels away from the descent `t` (`L + 6` against `L + 1`), so
  `z 5 - 1 = 29` steps away from it; in particular it is past the window in which the failure of
  `Leg3Valley` says nothing, so the failure applies to it and puts it within two steps of the
  basepoint;
* the low link `r'` is four levels away from `r` (`L + 2` against `L + 6`), so `z 4 - 1 = 12`
  steps away from it, hence at least ten steps past the basepoint.

Ten is more than the four the V-criterion asks for, so the witness is always there, and it is
always far: the measurements of batch 55 are exactly these two bounds.

Consequently `ValleyResidual` (`HPC/Fold/CrossValley.lean`) is not an obstruction at all:
`cross_valley_vee_pair` below proves the conclusion of the work item `cross_valley_profile`
outright, and `HPC/Fold/Mixed.lean` derives the item from it.

Both timing bounds are read off the *intervals* `[ρ, σ]` of the links, not off `ρ` alone — that is
what `minGap` needs and what the one-arm clauses `CrookUp`, `CrookDown` throw away, which is why
the earlier analysis stopped one level and one index short.
-/

namespace HPC.Fold

/-! ## The timing law between two links of the sequence -/

/-- **The timing law, between two links of a faithful crooked sequence.** If the interval of one
link contains a level `l` and the interval of another contains `l + d`, the two links are at least
`z d - 1` steps apart. This is `minGap` applied to the window between them, in the ambient index
of the sequence rather than on an arm. -/
theorem ivGap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n) (hpq : p.val < q.val)
    (d : ℕ) (l : ℤ)
    (hcov : (ρ p ≤ l ∧ l ≤ σ p ∧ ρ q ≤ l + d ∧ l + d ≤ σ q) ∨
            (ρ q ≤ l ∧ l ≤ σ q ∧ ρ p ≤ l + d ∧ l + d ≤ σ p)) :
    z d ≤ q.val - p.val + 1 := by
  have hqn := q.isLt
  have hrestr := isCrookedIvF_restrict hcr p.val q.val (le_of_lt hpq) hqn
  set m : ℕ := q.val - p.val with hm
  have hmpos : 0 < m := by omega
  have hne : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  have hP : (⟨p.val + (0 : ℕ), by omega⟩ : Fin n) = p := Fin.ext (by simp)
  have hQ : (⟨p.val + m, by omega⟩ : Fin n) = q := Fin.ext (by simp; omega)
  have key : z d ≤ m + 1 := by
    rcases hcov with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · refine minGap d hrestr ⟨0, by omega⟩ ⟨m, by omega⟩ l ?_ ?_ ?_ ?_ hne
      · simpa [hP] using h1
      · simpa [hP] using h2
      · simpa [hQ] using h3
      · simpa [hQ] using h4
    · refine minGap d hrestr ⟨m, by omega⟩ ⟨0, by omega⟩ l ?_ ?_ ?_ ?_ (Ne.symm hne)
      · simpa [hQ] using h1
      · simpa [hQ] using h2
      · simpa [hP] using h3
      · simpa [hP] using h4
  omega

/-- Four levels apart: twelve steps. -/
theorem ivGap4 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hpq : p.val < q.val) (a b : ℤ) (hab : a + 4 ≤ b)
    (hcov : (ρ p ≤ a ∧ a ≤ σ p ∧ ρ q ≤ b ∧ b ≤ σ q) ∨ (ρ q ≤ a ∧ a ≤ σ q ∧ ρ p ≤ b ∧ b ≤ σ p)) :
    p.val + 12 ≤ q.val := by
  have hd : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hz : z 4 ≤ z (b - a).toNat := z_mono (by omega)
  have hz4 : z 4 = 13 := by decide
  have := ivGap hcr p q hpq (b - a).toNat a (by
    rcases hcov with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, by omega, by omega⟩
    · exact Or.inr ⟨h1, h2, by omega, by omega⟩)
  omega

/-- Five levels apart: twenty-nine steps. -/
theorem ivGap5 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hpq : p.val < q.val) (a b : ℤ) (hab : a + 5 ≤ b)
    (hcov : (ρ p ≤ a ∧ a ≤ σ p ∧ ρ q ≤ b ∧ b ≤ σ q) ∨ (ρ q ≤ a ∧ a ≤ σ q ∧ ρ p ≤ b ∧ b ≤ σ p)) :
    p.val + 29 ≤ q.val := by
  have hd : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hz : z 5 ≤ z (b - a).toNat := z_mono (by omega)
  have hz5 : z 5 = 30 := by decide
  have := ivGap hcr p q hpq (b - a).toNat a (by
    rcases hcov with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, by omega, by omega⟩
    · exact Or.inr ⟨h1, h2, by omega, by omega⟩)
  omega

/-- **The timing law, in separation form.** Two links of a faithful crooked sequence whose
intervals contain levels `d` or more apart are at least `z d - 1` steps apart, in whichever index
order they come. -/
theorem ivSep {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hne : p.val ≠ q.val) (d : ℕ) (a b : ℤ) (hab : a + d ≤ b)
    (hpa : ρ p ≤ a) (hap : a ≤ σ p) (hqb : ρ q ≤ b) (hbq : b ≤ σ q) :
    p.val + z d ≤ q.val + 1 ∨ q.val + z d ≤ p.val + 1 := by
  have hz : z d ≤ z (b - a).toNat := z_mono (by omega)
  have hd : (((b - a).toNat : ℕ) : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  rcases Nat.lt_or_ge p.val q.val with h | h
  · have := ivGap hcr p q h (b - a).toNat a (Or.inl ⟨hpa, hap, by omega, by omega⟩)
    exact Or.inl (by omega)
  · have hq : q.val < p.val := by omega
    have := ivGap hcr q p hq (b - a).toNat a (Or.inr ⟨hpa, hap, by omega, by omega⟩)
    exact Or.inr (by omega)

/-- Three levels apart: five steps, in either order. -/
theorem ivSep3 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hne : p.val ≠ q.val) (a b : ℤ) (hab : a + 3 ≤ b)
    (hpa : ρ p ≤ a) (hap : a ≤ σ p) (hqb : ρ q ≤ b) (hbq : b ≤ σ q) :
    p.val + 5 ≤ q.val ∨ q.val + 5 ≤ p.val := by
  have hz : z 3 = 6 := by decide
  rcases ivSep hcr p q hne 3 a b (by push_cast; omega) hpa hap hqb hbq with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Four levels apart: twelve steps, in either order. -/
theorem ivSep4 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hne : p.val ≠ q.val) (a b : ℤ) (hab : a + 4 ≤ b)
    (hpa : ρ p ≤ a) (hap : a ≤ σ p) (hqb : ρ q ≤ b) (hbq : b ≤ σ q) :
    p.val + 12 ≤ q.val ∨ q.val + 12 ≤ p.val := by
  have hz : z 4 = 13 := by decide
  rcases ivSep hcr p q hne 4 a b (by push_cast; omega) hpa hap hqb hbq with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Five levels apart: twenty-nine steps, in either order. -/
theorem ivSep5 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (p q : Fin n)
    (hne : p.val ≠ q.val) (a b : ℤ) (hab : a + 5 ≤ b)
    (hpa : ρ p ≤ a) (hap : a ≤ σ p) (hqb : ρ q ≤ b) (hbq : b ≤ σ q) :
    p.val + 29 ≤ q.val ∨ q.val + 29 ≤ p.val := by
  have hz : z 5 = 30 := by decide
  rcases ivSep hcr p q hne 5 a b (by push_cast; omega) hpa hap hqb hbq with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## The crossing, with no exceptional case -/

/-- **The far witness, forward form.** The hypotheses are those of `cross_valley_low_fwd`
(`HPC/Fold/CrossValley.lean`) — an ascent `s` before the basepoint, a descent `t` after it whose
valley clause fails — and the conclusion is that one's first disjunct, with **no** residual case:
the sequence stands at `L + 2` or below strictly after `s` and at least four steps before the
basepoint.

Neither the Lipschitz hypothesis nor the value of `ρ` at the basepoint is needed: the two timing
bounds do all the work. -/
theorem cross_valley_low_fwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n)
    (hs : s.val < i.val) (hsv : L + 7 ≤ ρ s)
    (ht : i.val < t.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4) :
    ∃ v : Fin n, s.val < v.val ∧ v.val + 4 ≤ i.val ∧ ρ v ≤ L + 2 := by
  have hst : s < t := by exact Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', hsr, hrr', hr't, _hup, hdn⟩ :=
    hcr.crooked s t hst (ρ s) (ρ t) ⟨s, by simp, le_rfl, hcr.le s⟩ ⟨t, by simp, le_rfl, hcr.le t⟩
      (by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ s - ρ t)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hdn (by omega)
  -- the high link is at least five levels above the descent, hence twenty-nine steps before it
  have hwr' : σ r' ≤ ρ r' + 1 := hcr.width r'
  have hr'hi : L + 5 ≤ ρ r' := by omega
  have hgap5 : r'.val + 29 ≤ t.val :=
    ivGap5 hcr r' t (by exact_mod_cast Fin.lt_def.mp hr't) (ρ t) (ρ s - 1) (by omega)
      (Or.inr ⟨le_rfl, hcr.le t, hr'1, hr'2⟩)
  -- so the failure of the valley clause applies to it, and puts it within two steps of the base
  have hr'near : r'.val < i.val + 3 := by
    by_contra hc
    have := hfail r' (by omega) (by omega)
    omega
  -- the low link is four levels below it, hence twelve steps before it
  have hgap4 : r.val + 12 ≤ r'.val :=
    ivGap4 hcr r r' (by exact_mod_cast Fin.lt_def.mp hrr') (ρ t + 1) (ρ s - 1) (by omega)
      (Or.inl ⟨hr1, hr2, hr'1, hr'2⟩)
  exact ⟨r, by exact_mod_cast Fin.lt_def.mp hsr, by omega, by omega⟩

/-- **The far witness, backward form**, the mirror of `cross_valley_low_fwd_far`: the failing
descent `t` is before the basepoint and the ascent `s` after it. -/
theorem cross_valley_low_bwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n)
    (hs : i.val < s.val) (hsv : L + 7 ≤ ρ s)
    (ht : t.val < i.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4) :
    ∃ v : Fin n, v.val < s.val ∧ i.val + 4 ≤ v.val ∧ ρ v ≤ L + 2 := by
  have hts : t < s := by exact Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', htr, hrr', hr's, hup, _hdn⟩ :=
    hcr.crooked t s hts (ρ t) (ρ s) ⟨t, by simp, le_rfl, hcr.le t⟩ ⟨s, by simp, le_rfl, hcr.le s⟩
      (by rw [abs_of_nonpos (by omega : ρ t - ρ s ≤ 0)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hup (by omega)
  have hwr : σ r ≤ ρ r + 1 := hcr.width r
  have hrhi : L + 5 ≤ ρ r := by omega
  have hgap5 : t.val + 29 ≤ r.val :=
    ivGap5 hcr t r (by exact_mod_cast Fin.lt_def.mp htr) (ρ t) (ρ s - 1) (by omega)
      (Or.inl ⟨le_rfl, hcr.le t, hr1, hr2⟩)
  have hrnear : i.val < r.val + 3 := by
    by_contra hc
    have := hfail r (by omega) (by omega)
    omega
  have hgap4 : r.val + 12 ≤ r'.val :=
    ivGap4 hcr r r' (by exact_mod_cast Fin.lt_def.mp hrr') (ρ t + 1) (ρ s - 1) (by omega)
      (Or.inr ⟨hr'1, hr'2, hr1, hr2⟩)
  exact ⟨r', by exact_mod_cast Fin.lt_def.mp hr's, by omega, by omega⟩

/-! ## The V-criterion on the arms, unconditionally -/

/-- **The V-criterion for the backward arm**, when the forward arm fails the valley clause. This
is `critVee_armT_of_fail_armG` (`HPC/Fold/CrossValley.lean`) with the hypothesis
`¬ ValleyResidual ρ i L` removed. -/
theorem critVee_armT_of_fail_armG_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i : Fin n) (hp : ρ i = L + 4) (hfail : ¬ Leg3Valley (armG ρ i) L) :
    ∀ e : Fin (i.val + 1), L + 7 ≤ armT ρ i e →
      ∃ j : Fin (i.val + 1), j.val < e.val ∧ 4 ≤ j.val ∧ armT ρ i j ≤ L + 2 := by
  have hi := i.isLt
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  set t : Fin n := ⟨i.val + d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val + d₀.val := rfl
  have htv : ρ t ≤ L + 1 := hd₀v
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4 := by
    intro w h1 h2
    have hwn := w.isLt
    have hw : w.val - i.val < n - i.val := by omega
    have := hd₀no ⟨w.val - i.val, hw⟩ (show 3 ≤ w.val - i.val by omega)
      (show w.val - i.val + 5 ≤ d₀.val by omega)
    have heq : armG ρ i ⟨w.val - i.val, hw⟩ = ρ w := by
      show ρ ⟨i.val + (w.val - i.val), _⟩ = ρ w
      exact congrArg ρ (Fin.ext (by show i.val + (w.val - i.val) = w.val; omega))
    rw [heq] at this
    omega
  intro e he
  have hem := e.isLt
  set s : Fin n := ⟨i.val - e.val, by omega⟩ with hsdef
  have hsval : s.val = i.val - e.val := rfl
  have hsv : L + 7 ≤ ρ s := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    cross_valley_low_fwd_far hcr L i s t (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨i.val - v.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
  have heq : armT ρ i ⟨i.val - v.val, by omega⟩ = ρ v := by
    show ρ ⟨i.val - (i.val - v.val), _⟩ = ρ v
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
  rw [heq]; exact hv3

/-- **The V-criterion for the forward arm**, when the backward arm fails the valley clause. -/
theorem critVee_armG_of_fail_armT_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i : Fin n) (hp : ρ i = L + 4) (hfail : ¬ Leg3Valley (armT ρ i) L) :
    ∀ e : Fin (n - i.val), L + 7 ≤ armG ρ i e →
      ∃ j : Fin (n - i.val), j.val < e.val ∧ 4 ≤ j.val ∧ armG ρ i j ≤ L + 2 := by
  have hi := i.isLt
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  set t : Fin n := ⟨i.val - d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val - d₀.val := rfl
  have htv : ρ t ≤ L + 1 := hd₀v
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4 := by
    intro w h1 h2
    have hwn := w.isLt
    have hw : i.val - w.val < i.val + 1 := by omega
    have := hd₀no ⟨i.val - w.val, hw⟩ (show 3 ≤ i.val - w.val by omega)
      (show i.val - w.val + 5 ≤ d₀.val by omega)
    have heq : armT ρ i ⟨i.val - w.val, hw⟩ = ρ w := by
      show ρ ⟨i.val - (i.val - w.val), _⟩ = ρ w
      exact congrArg ρ (Fin.ext (by show i.val - (i.val - w.val) = w.val; omega))
    rw [heq] at this
    omega
  intro e he
  have hem := e.isLt
  set s : Fin n := ⟨i.val + e.val, by omega⟩ with hsdef
  have hsval : s.val = i.val + e.val := rfl
  have hsv : L + 7 ≤ ρ s := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    cross_valley_low_bwd_far hcr L i s t (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨v.val - i.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
  have heq : armG ρ i ⟨v.val - i.val, by omega⟩ = ρ v := by
    show ρ ⟨i.val + (v.val - i.val), _⟩ = ρ v
    exact congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
  rw [heq]; exact hv3

/-! ## The valley crossing -/

/-- **The valley crossing, with no exceptional case.** If either arm of a pair of the branch
`L + 4` fails the valley clause, then *both* arms fold onto the V-walk based at `L + 5`.

This is the conclusion of the work item `cross_valley_profile` (`HPC/Fold/Mixed.lean`), from which
the item itself follows at once; the residual configuration of `cross_valley_dichotomy`
(`HPC/Fold/CrossValley.lean`) is not an obstruction, because the timing law places the witness ten
steps past the basepoint whenever the clause has to be read near it. -/
theorem cross_valley_vee_pair {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  have hlip : IsLip ρ := hcr.isLip
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  rcases hfail with hfG | hfT
  · have hvT : FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
      refine (foldsOnto_vee_iff_profile hmT (armT ρ i) (armT_isLip hlip i) (L + 5) (L + 9) L
        (by omega) (by rw [hT0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _)).mpr ?_
      rw [critVeeProfile_iff_of_isLip (armT_isLip hlip i) (L + 5) L (by omega)]
      intro d hd
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armT_of_fail_armG_far hcr L i hp hfG d (by omega)
      exact ⟨j, hj1, by omega, hj3⟩
    refine ⟨?_, hvT⟩
    rcases leg3Valley_or_vee hmG (armG ρ i) (armG_isLip hlip i) (crookDown_armG hcr i) L hG0
      (fun j => hLb _) (fun j => hHb _) with h | h
    · exact absurd h hfG
    · exact h
  · have hvG : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
      refine (foldsOnto_vee_iff_profile hmG (armG ρ i) (armG_isLip hlip i) (L + 5) (L + 9) L
        (by omega) (by rw [hG0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _)).mpr ?_
      rw [critVeeProfile_iff_of_isLip (armG_isLip hlip i) (L + 5) L (by omega)]
      intro d hd
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armG_of_fail_armT_far hcr L i hp hfT d (by omega)
      exact ⟨j, hj1, by omega, hj3⟩
    refine ⟨hvG, ?_⟩
    rcases leg3Valley_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
      (fun j => hLb _) (fun j => hHb _) with h | h
    · exact absurd h hfT
    · exact h

end HPC.Fold
