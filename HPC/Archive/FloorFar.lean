import HPC.Fold.ValleyFar
import HPC.Fold.ArmReflect

/-!
# The crossing at the branch `L + 5`: what the timing law gives, and what it cannot give

At the branch `L + 4` the valley crossing is a theorem (`cross_valley_vee_pair`,
`HPC/Fold/ValleyFar.lean`): reading the crookedness clause between the failing arm's descent and
the other arm's ascent returns two links, and the timing law of Bing's Theorem 7 (`ivSep`) pins
them — the high link twenty-nine steps from the descent, the low link twelve steps from the high
one, so the witness the V-criterion asks for is forced ten steps past the basepoint.

This file reads the same clause at the branch `L + 5`, where the roles of the two ends are
exchanged: the failing arm has an *ascent* to `L + 8` and the other arm a *descent* to `L + 2`.
Both timing bounds survive verbatim — the clause of `IsCrookedIvF` is symmetric in its two levels,
and `ivGap4`, `ivGap5` are stated on intervals — and so the same ten steps are obtained
(`cross_high_fwd_far`, `cross_high_bwd_far`).

**What does not survive is the level.** Reading the clause downwards, the returned link `r`
satisfies `ρ r ≤ k - 1 ≤ σ r`, so `ρ r` lies in `[k - 2, k - 1]`; reading it upwards, `r` again
satisfies `ρ r ≤ k - 1 ≤ σ r`, and for an *ascent* `k = ρ t ≥ L + 8` that is a link with
`ρ r ≥ L + 6` and `σ r ≥ L + 7`, one level short of the `L + 7` the Λ-criterion of the branch
`L + 5` needs. The asymmetry is in the model, not in the reading: a link is the interval
`[ρ, ρ + 1]`, so a level read from below and a level read from above differ by one.

The two halves of the situation are therefore:

* **the interval form holds** — `cross_high_fwd_far` and `cross_high_bwd_far` below, and their
  arm-level corollaries, give a link at least ten steps from the basepoint whose interval meets
  `L + 7`;
* **the point form fails** — `not_reflValleyCrossL5` (`HPC/Fold/Audit57.lean`) exhibits a faithful
  pair at which the arm that must fold does not, precisely because every such witness has `ρ` at
  `L + 6` and only `σ` at `L + 7`.

That is the answer to question 1 of COMMISSION.md: the branch `L + 5` does not yield to the same
two bounds, and the obstruction is one level, measured here and refuted there.
-/

namespace HPC.Fold

/-! ## The far witness at the branch `L + 5`, in interval form -/

/-- **The far witness, forward form.** A descent `s` to `L + 2` before the basepoint, an ascent
`t` to `L + 8` after it, and the failure of the reflected valley clause between them: then the
sequence has a link at least ten steps before the basepoint, strictly after `s`, whose `ρ` is at
`L + 6` or above and whose interval reaches `L + 7`. -/
theorem cross_high_fwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 2)
    (ht : i.val < t.val) (htv : L + 8 ≤ ρ t)
    (hfail : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → L + 5 ≤ ρ w) :
    ∃ v : Fin n, s.val < v.val ∧ v.val + 10 ≤ i.val ∧ L + 6 ≤ ρ v ∧ L + 7 ≤ σ v := by
  have hst : s < t := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', hsr, hrr', hr't, hup, _hdn⟩ :=
    hcr.crooked s t hst (ρ s) (ρ t) ⟨s, by simp, le_rfl, hcr.le s⟩ ⟨t, by simp, le_rfl, hcr.le t⟩
      (by rw [abs_of_nonpos (by omega : ρ s - ρ t ≤ 0)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hup (by omega)
  -- the low link is five levels below the ascent, hence twenty-nine steps before it
  have hgap5 : r'.val + 29 ≤ t.val :=
    ivGap5 hcr r' t (by exact_mod_cast Fin.lt_def.mp hr't) (ρ s + 1) (ρ t) (by omega)
      (Or.inl ⟨hr'1, hr'2, le_rfl, hcr.le t⟩)
  -- so the failure of the clause applies to it, and puts it within two steps of the basepoint
  have hr'near : r'.val < i.val + 3 := by
    by_contra hc
    have := hfail r' (by omega) (by omega)
    omega
  -- the high link is four levels above it, hence twelve steps before it
  have hgap4 : r.val + 12 ≤ r'.val :=
    ivGap4 hcr r r' (by exact_mod_cast Fin.lt_def.mp hrr') (ρ s + 1) (ρ t - 1) (by omega)
      (Or.inr ⟨hr'1, hr'2, hr1, hr2⟩)
  have hwr : σ r ≤ ρ r + 1 := hcr.width r
  exact ⟨r, by exact_mod_cast Fin.lt_def.mp hsr, by omega, by omega, by omega⟩

/-- **The far witness, backward form**, the mirror of `cross_high_fwd_far`: the failing ascent `t`
is before the basepoint and the descent `s` after it. -/
theorem cross_high_bwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 2)
    (ht : t.val < i.val) (htv : L + 8 ≤ ρ t)
    (hfail : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → L + 5 ≤ ρ w) :
    ∃ v : Fin n, v.val < s.val ∧ i.val + 10 ≤ v.val ∧ L + 6 ≤ ρ v ∧ L + 7 ≤ σ v := by
  have hts : t < s := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', htr, hrr', hr's, _hup, hdn⟩ :=
    hcr.crooked t s hts (ρ t) (ρ s) ⟨t, by simp, le_rfl, hcr.le t⟩ ⟨s, by simp, le_rfl, hcr.le s⟩
      (by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ t - ρ s)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hdn (by omega)
  -- here `r` carries the low level and `r'` the high one
  have hgap5 : t.val + 29 ≤ r.val :=
    ivGap5 hcr t r (by exact_mod_cast Fin.lt_def.mp htr) (ρ s + 1) (ρ t) (by omega)
      (Or.inr ⟨hr1, hr2, le_rfl, hcr.le t⟩)
  have hrnear : i.val < r.val + 3 := by
    by_contra hc
    have := hfail r (by omega) (by omega)
    omega
  have hgap4 : r.val + 12 ≤ r'.val :=
    ivGap4 hcr r r' (by exact_mod_cast Fin.lt_def.mp hrr') (ρ s + 1) (ρ t - 1) (by omega)
      (Or.inl ⟨hr1, hr2, hr'1, hr'2⟩)
  have hwr' : σ r' ≤ ρ r' + 1 := hcr.width r'
  exact ⟨r', by exact_mod_cast Fin.lt_def.mp hr's, by omega, by omega, by omega⟩

/-! ## The criterion on the arms, in interval form

The failure read on the arm is the failure of the reflected valley clause: an ascent of the arm to
`L + 8` with no time at `L + 4` or below in the window the clause looks at. The conclusion is the
Λ-criterion of the branch `L + 5` with the level `L + 7` read on the interval instead of on the
point: before every descent of the other arm to `L + 2` there is a link at arm index ten or more
whose `ρ` is at `L + 6` and whose `σ` reaches `L + 7`. -/

/-- **The interval criterion for the backward arm**, when the forward arm's reflection fails the
valley clause. -/
theorem critLamIv_armT_of_fail_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i : Fin n) (hp : ρ i = L + 5)
    (hfail : ¬ Leg3Valley (armRefl (L + (L + 9)) (armG ρ i)) L) :
    ∀ e : Fin (i.val + 1), armT ρ i e ≤ L + 2 →
      ∃ j : Fin (i.val + 1), j.val < e.val ∧ 10 ≤ j.val ∧
        L + 6 ≤ armT ρ i j ∧ L + 7 ≤ armT σ i j := by
  have hi := i.isLt
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  simp only [armRefl_apply] at hd₀v hd₀no
  set t : Fin n := ⟨i.val + d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val + d₀.val := rfl
  have htv : L + 8 ≤ ρ t := by
    have : armG ρ i d₀ = ρ t := by
      show ρ ⟨i.val + d₀.val, _⟩ = ρ t
      rfl
    rw [this] at hd₀v; omega
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → L + 5 ≤ ρ w := by
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
  have hsv : ρ s ≤ L + 2 := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ :=
    cross_high_fwd_far hcr L i s t (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨i.val - v.val, by omega⟩, by simp; omega, by simp; omega, ?_, ?_⟩
  · have heq : armT ρ i ⟨i.val - v.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val - (i.val - v.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
    rw [heq]; exact hv3
  · have heq : armT σ i ⟨i.val - v.val, by omega⟩ = σ v := by
      show σ ⟨i.val - (i.val - v.val), _⟩ = σ v
      exact congrArg σ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
    rw [heq]; exact hv4

/-- **The interval criterion for the forward arm**, when the backward arm's reflection fails the
valley clause. -/
theorem critLamIv_armG_of_fail_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i : Fin n) (hp : ρ i = L + 5)
    (hfail : ¬ Leg3Valley (armRefl (L + (L + 9)) (armT ρ i)) L) :
    ∀ e : Fin (n - i.val), armG ρ i e ≤ L + 2 →
      ∃ j : Fin (n - i.val), j.val < e.val ∧ 10 ≤ j.val ∧
        L + 6 ≤ armG ρ i j ∧ L + 7 ≤ armG σ i j := by
  have hi := i.isLt
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  simp only [armRefl_apply] at hd₀v hd₀no
  set t : Fin n := ⟨i.val - d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val - d₀.val := rfl
  have htv : L + 8 ≤ ρ t := by
    have : armT ρ i d₀ = ρ t := by
      show ρ ⟨i.val - d₀.val, _⟩ = ρ t
      rfl
    rw [this] at hd₀v; omega
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → L + 5 ≤ ρ w := by
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
  have hsv : ρ s ≤ L + 2 := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ :=
    cross_high_bwd_far hcr L i s t (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨v.val - i.val, by omega⟩, by simp; omega, by simp; omega, ?_, ?_⟩
  · have heq : armG ρ i ⟨v.val - i.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val + (v.val - i.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
    rw [heq]; exact hv3
  · have heq : armG σ i ⟨v.val - i.val, by omega⟩ = σ v := by
      show σ ⟨i.val + (v.val - i.val), _⟩ = σ v
      exact congrArg σ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
    rw [heq]; exact hv4

end HPC.Fold
