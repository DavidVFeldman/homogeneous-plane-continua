import HPC.Fold.Agree

/-!
# Upward and symmetric crookedness

`IsCrookedSeq` (batch 7) is what `minIdx` satisfies. Because `minIdx` is a minimum, all four of
its bounds sit one unit low, and the condition is **not** preserved by negating a sequence —
so "by reflection" is unsound for any statement taking it as a hypothesis.

Two repairs, both here.

* `IsCrookedSeqUp` is what `maxIdx` satisfies: the same shape with every bound one unit
  higher. Under it the Synchronization Lemma pins the *upper* of the two witnesses exactly,
  where `IsCrookedSeq` pins the lower one.
* `IsCrookedSeqSym` has slack two on each side, is implied by both, and *is* preserved by
  negation and by reversal. It is the notion to use whenever an argument wants to treat rising
  and dropping symmetrically.

English proofs: COMMISSION-batch13.md §3.

## The correction directed by the commission

The commissioned table (§1) displaces only *two* of the four bounds upward: in the ascending
case it keeps `f r' ∈ [f s, f s + 1]`, the same interval as `IsCrookedSeq`. That literal form
is recorded verbatim below as `IsCrookedSeqUpMixed`, but it is **not** what transport through
`maxIdx` gives. Transport displaces all four bounds, for the same reason in each case: the
crooked pair `(h', k') = (maxIdx s, maxIdx t)` puts the second witness inside `D.link (h' + 1)`,
so `le_maxIdx` gives `maxIdx r' ≥ h' + 1` and adjacency only `maxIdx r' ≤ h' + 2`; the interval
is `[f s + 1, f s + 2]`, one above the commissioned one, exactly as `[f t - 1, f t]` is one
above `[f t - 2, f t - 1]` at the other end. `IsCrookedSeqUp` below therefore records the
uniformly displaced form, which is what the module docstring of the commission describes
("every bound one unit higher") and what `isCrookedSeqUp_maxIdx` proves.

The corollaries are adjusted accordingly, as §3 of batch 7's commission directs in the
analogous situation. Under the uniformly displaced form the Synchronization Lemma pins the
witness at `p + 1` exactly and leaves the other only `≤ p`; under `IsCrookedSeq` it is the
witness at `p - 1` that is pinned. Nothing is lost: the commissioned conclusion is proved
verbatim for the commissioned notion, as `sync_up_mixed` and `sync_up_mixed'`.
-/

namespace HPC.Fold

variable {n : ℕ} {f : Fin n → ℤ}

/-- Crookedness as transported through `maxIdx`: every bound one higher than `IsCrookedSeq`.

Ascending case (`f s < f t`): `f t - 1 ≤ f r ≤ f t` and `f s + 1 ≤ f r' ≤ f s + 2`.
Descending case: `f t + 1 ≤ f r ≤ f t + 2` and `f s - 1 ≤ f r' ≤ f s`. -/
def IsCrookedSeqUp (f : Fin n → ℤ) : Prop :=
  ∀ s t : Fin n, s < t → 3 ≤ |f t - f s| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (f s < f t → (f t - 1 ≤ f r ∧ f r ≤ f t) ∧ (f s + 1 ≤ f r' ∧ f r' ≤ f s + 2)) ∧
      (f t < f s → (f t + 1 ≤ f r ∧ f r ≤ f t + 2) ∧ (f s - 1 ≤ f r' ∧ f r' ≤ f s))

/-- The commissioned form of the upward condition, kept verbatim: only the witness at the far
end is displaced upward, the near one keeping the interval `IsCrookedSeq` gives it. It is a
strictly different condition from `IsCrookedSeqUp` — neither implies the other — and it is not
the one satisfied by `maxIdx` (see the module docstring), but every statement commissioned for
it is proved for it below (`IsCrookedSeqUpMixed.sym`, `sync_up_mixed`, `sync_up_mixed'`). -/
def IsCrookedSeqUpMixed (f : Fin n → ℤ) : Prop :=
  ∀ s t : Fin n, s < t → 3 ≤ |f t - f s| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (f s < f t → (f t - 1 ≤ f r ∧ f r ≤ f t) ∧ (f s ≤ f r' ∧ f r' ≤ f s + 1)) ∧
      (f t < f s → (f t ≤ f r ∧ f r ≤ f t + 1) ∧ (f s - 1 ≤ f r' ∧ f r' ≤ f s))

/-- The common weakening: slack two on each side. Negation- and reversal-symmetric. -/
def IsCrookedSeqSym (f : Fin n → ℤ) : Prop :=
  ∀ s t : Fin n, s < t → 3 ≤ |f t - f s| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (f s < f t → (f t - 2 ≤ f r ∧ f r ≤ f t) ∧ (f s ≤ f r' ∧ f r' ≤ f s + 2)) ∧
      (f t < f s → (f t ≤ f r ∧ f r ≤ f t + 2) ∧ (f s - 2 ≤ f r' ∧ f r' ≤ f s))

theorem IsCrookedSeq.sym (h : IsCrookedSeq f) : IsCrookedSeqSym f := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

theorem IsCrookedSeqUp.sym (h : IsCrookedSeqUp f) : IsCrookedSeqSym f := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- The commissioned mixed form also widens to the symmetric one. -/
theorem IsCrookedSeqUpMixed.sym (h : IsCrookedSeqUpMixed f) : IsCrookedSeqSym f := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc hlt; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- **Negation symmetry**, which `IsCrookedSeq` does not have. -/
theorem IsCrookedSeqSym.neg (h : IsCrookedSeqSym f) : IsCrookedSeqSym (fun j => - f j) := by
  intro s t hst habs
  simp only [] at habs
  have hneg : -f t - -f s = -(f t - f s) := by ring
  rw [hneg, abs_neg] at habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · simp only [] at hlt ⊢
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc (by omega)
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · simp only [] at hlt ⊢
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc (by omega)
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- Reversal symmetry, as batch 12 established for `IsCrookedSeq`. -/
theorem IsCrookedSeqSym.rev (h : IsCrookedSeqSym f) : IsCrookedSeqSym (revSeq f) := by
  intro s t hst habs
  have hs := s.isLt
  have ht := t.isLt
  have hstv : s.val < t.val := hst
  have hST : (⟨n - 1 - t.val, by omega⟩ : Fin n) < ⟨n - 1 - s.val, by omega⟩ := by
    simp only [Fin.lt_def]; omega
  have hSv : revSeq f t = f ⟨n - 1 - t.val, by omega⟩ := rfl
  have hTv : revSeq f s = f ⟨n - 1 - s.val, by omega⟩ := rfl
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    h ⟨n - 1 - t.val, by omega⟩ ⟨n - 1 - s.val, by omega⟩ hST
      (by rw [← hSv, ← hTv, abs_sub_comm]; exact habs)
  have h1v : n - 1 - t.val < r.val := h1
  have h2v : r.val < r'.val := h2
  have h3v : r'.val < n - 1 - s.val := h3
  have hr := r.isLt
  have hr' := r'.isLt
  have hRv : revSeq f ⟨n - 1 - r'.val, by omega⟩ = f r' :=
    congrArg f (Fin.ext (by simp only; omega))
  have hR'v : revSeq f ⟨n - 1 - r.val, by omega⟩ = f r :=
    congrArg f (Fin.ext (by simp only; omega))
  refine ⟨⟨n - 1 - r'.val, by omega⟩, ⟨n - 1 - r.val, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc (by omega)
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc (by omega)
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- The witness sequence for `not_isCrookedSeq_neg`: `0, 1, 1, 3`. Its only pair of levels
differing by three is the pair of endpoints, and the two middle links, both at level `1`, serve
as witnesses for it; after negation the first witness would have to sit at `-2` or `-3`, and
neither middle link does. Found by an exhaustive search over sequences of length at most seven
with values in `[0, 3]`; it is, up to reflection, the only witness of length four. -/
def negWitness : Fin 4 → ℤ := fun j => if j.val = 0 then 0 else if j.val = 3 then 3 else 1

/-- Neither displaced form is negation-symmetric: negating an `IsCrookedSeq` sequence gives
neither `IsCrookedSeq` nor `IsCrookedSeqUp` in general. Recorded as a counterexample so the
unsound step cannot be taken by accident. -/
theorem not_isCrookedSeq_neg :
    ∃ (m : ℕ) (g : Fin m → ℤ), IsCrookedSeq g ∧ ¬ IsCrookedSeq (fun j => - g j) :=
  ⟨4, negWitness, by unfold IsCrookedSeq negWitness; decide,
    by unfold IsCrookedSeq negWitness; decide⟩

/-- The same witness also fails the commissioned mixed form after negation. -/
theorem not_isCrookedSeqUpMixed_neg :
    ∃ (m : ℕ) (g : Fin m → ℤ), IsCrookedSeq g ∧ ¬ IsCrookedSeqUpMixed (fun j => - g j) :=
  ⟨4, negWitness, by unfold IsCrookedSeq negWitness; decide,
    by unfold IsCrookedSeqUpMixed negWitness; decide⟩

/-- **Negation exchanges the two displaced forms exactly.** This is the precise sense in which
the failure of negation symmetry is a one-unit displacement and nothing more: a sequence is
crooked in the `minIdx` sense exactly when its negative is crooked in the `maxIdx` sense. It
also shows the two forms are equally strong, and that the uniformly displaced `IsCrookedSeqUp`
is the right upward partner of `IsCrookedSeq` — no such equivalence holds for the mixed form,
by `not_isCrookedSeqUpMixed_neg`. -/
theorem isCrookedSeqUp_neg_iff : IsCrookedSeqUp (fun j => - f j) ↔ IsCrookedSeq f := by
  constructor
  · intro h s t hst habs
    have habs' : 3 ≤ |(fun j => - f j) t - (fun j => - f j) s| := by
      simp only []
      have hneg : -f t - -f s = -(f t - f s) := by ring
      rw [hneg, abs_neg]; exact habs
    obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs'
    simp only [] at hasc hdesc
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc (by omega)
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc (by omega)
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro h s t hst habs
    simp only [] at habs
    have hneg : -f t - -f s = -(f t - f s) := by ring
    rw [hneg, abs_neg] at habs
    obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := h s t hst habs
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · simp only [] at hlt ⊢
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hdesc (by omega)
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · simp only [] at hlt ⊢
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hasc (by omega)
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ## Transport through `maxIdx` -/

open HPC.Chain in
/-- One application of crookedness, read through `maxIdx`: the mirror of `minIdx_crooked_step`,
with each of the four bounds one unit higher, because `le_maxIdx` bounds from below where
`minIdx_le` bounds from above. -/
theorem maxIdx_crooked_step {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : HPC.Chain X m} {D : HPC.Chain X k} (h : E.IsCrookedIn' D) (i j : Fin m)
    (hij : (h.1.maxIdx i).val + 2 < (h.1.maxIdx j).val) :
    ∃ r s : Fin m, HPC.Chain.Between i r s j ∧
      (h.1.maxIdx j).val ≤ (h.1.maxIdx r).val + 1 ∧
      (h.1.maxIdx r).val ≤ (h.1.maxIdx j).val ∧
      (h.1.maxIdx i).val + 1 ≤ (h.1.maxIdx s).val ∧
      (h.1.maxIdx s).val ≤ (h.1.maxIdx i).val + 2 := by
  have hre := h.1
  have hcr := h.2
  have hmi : (E.link i ∩ D.link (hre.maxIdx i)).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty i
    exact ⟨z, hz, maxIdx_subset hre i hz⟩
  have hmj : (E.link j ∩ D.link (hre.maxIdx j)).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty j
    exact ⟨z, hz, maxIdx_subset hre j hz⟩
  obtain ⟨r, s, hbtw, hr, hs⟩ := hcr (hre.maxIdx i) (hre.maxIdx j) hij i j hmi hmj
  refine ⟨r, s, hbtw, ?_, ?_, ?_, ?_⟩
  · have h1 := le_maxIdx hre r hr
    rw [Fin.le_def] at h1
    simp only [] at h1
    omega
  · have h2 := subset_adjacent_of_subset hre r (maxIdx_subset hre r) hr
    simp only [] at h2
    omega
  · have h3 := le_maxIdx hre s hs
    rw [Fin.le_def] at h3
    simp only [] at h3
    omega
  · have h4 := subset_adjacent_of_subset hre s (maxIdx_subset hre s) hs
    simp only [] at h4
    omega

open HPC.Chain in
/-- The maximal-index sequence of a crooked refinement satisfies the upward form. -/
theorem isCrookedSeqUp_maxIdx {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : Chain X m} {D : Chain X k} (h : E.IsCrookedIn' D) :
    IsCrookedSeqUp (fun t => (h.1.maxIdx t : ℤ)) := by
  intro s t hst habs
  simp only [] at habs
  have hcase : ((h.1.maxIdx s).val + 2 < (h.1.maxIdx t).val) ∨
      ((h.1.maxIdx t).val + 2 < (h.1.maxIdx s).val) := by
    rcases abs_cases (((h.1.maxIdx t : ℕ) : ℤ) - ((h.1.maxIdx s : ℕ) : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩
    · left; omega
    · right; omega
  rcases hcase with hasc | hdesc
  · obtain ⟨r, r', hbtw, b1, b2, b3, b4⟩ := maxIdx_crooked_step h s t hasc
    have horder : s < r ∧ r < r' ∧ r' < t := by
      rcases hbtw with hb | hb
      · exact hb
      · have hts : t < r' := hb.2.2
        exact absurd hst (not_lt.mpr ((hts.trans hb.2.1).trans hb.1).le)
    refine ⟨r, r', horder.1, horder.2.1, horder.2.2, ?_, ?_⟩
    · intro _; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega
    · intro hcontra; simp only [] at hcontra; omega
  · obtain ⟨r, r', hbtw, b1, b2, b3, b4⟩ := maxIdx_crooked_step h t s hdesc
    have horder : s < r' ∧ r' < r ∧ r < t := by
      rcases hbtw with hb | hb
      · exact absurd hst (not_lt.mpr ((hb.1.trans hb.2.1).trans hb.2.2).le)
      · exact ⟨hb.2.2, hb.2.1, hb.1⟩
    refine ⟨r', r, horder.1, horder.2.1, horder.2.2, ?_, ?_⟩
    · intro hcontra; simp only [] at hcontra; omega
    · intro _; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega

/-! ## The sharpened Synchronization Lemma -/

/-- **Under the upward form, one end of `sync` becomes exact.** Where `IsCrookedSeq` gives a
link at `p − 1` followed by one only known to be `≥ p`, `IsCrookedSeqUp` gives a link `≤ p`
followed by one at exactly `p + 1`: the displacement moves the exactness from the lower witness
to the upper one.

(Commissioned conclusion: `f j = p − 1` and `f k = p + 1`. The first value is weakened to
`f j ≤ p` because the uniformly displaced form — the one `maxIdx` actually satisfies — loses
a unit upward there; with `hmid` one also has `p − 1 ≤ f j`. For the commissioned mixed form
the commissioned conclusion holds verbatim: see `sync_up_mixed`.) -/
theorem sync_up (hf : IsCrookedSeqUp f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p + 2) (hv : f v = p - 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ p - 1 ≤ f j ∧ f j ≤ p ∧ f k = p + 1 := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = -4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, -, hdesc⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hdesc (by omega)
  have hlow := (hmid r hur (lt_trans hrr' hr'v)).1
  have hhigh := (hmid r' (lt_trans hur hrr') hr'v).2
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega, by omega⟩

/-- The ascending mirror: here it is the *first* witness that is pinned, at `p + 1`. -/
theorem sync_up' (hf : IsCrookedSeqUp f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p - 2) (hv : f v = p + 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ f j = p + 1 ∧ p - 1 ≤ f k ∧ f k ≤ p := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = 4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, hasc, -⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hasc (by omega)
  have hhigh := (hmid r hur (lt_trans hrr' hr'v)).2
  have hlow := (hmid r' (lt_trans hur hrr') hr'v).1
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega, by omega⟩

/-- The commissioned statement, proved verbatim for the commissioned mixed form: both values
are pinned there, `p − 1` then `p + 1`. -/
theorem sync_up_mixed (hf : IsCrookedSeqUpMixed f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p + 2) (hv : f v = p - 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ f j = p - 1 ∧ f k = p + 1 := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = -4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, -, hdesc⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hdesc (by omega)
  have hlow := (hmid r hur (lt_trans hrr' hr'v)).1
  have hhigh := (hmid r' (lt_trans hur hrr') hr'v).2
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega⟩

/-- The ascending case of `sync_up_mixed`. -/
theorem sync_up_mixed' (hf : IsCrookedSeqUpMixed f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p - 2) (hv : f v = p + 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ f j = p + 1 ∧ f k = p - 1 := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = 4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, hasc, -⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hasc (by omega)
  have hhigh := (hmid r hur (lt_trans hrr' hr'v)).2
  have hlow := (hmid r' (lt_trans hur hrr') hr'v).1
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega⟩

/-- The symmetric form gives the weakest version, valid for both and safe under reflection.

The commissioned hypothesis that the levels in between stay inside the window is kept, but it
turns out not to be needed here: with slack two on each side the two conclusions `f j ≤ p` and
`p ≤ f k` already follow from crookedness alone. -/
theorem sync_sym (hf : IsCrookedSeqSym f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p + 2) (hv : f v = p - 2)
    (_hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ f j ≤ p ∧ p ≤ f k := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = -4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, -, hdesc⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hdesc (by omega)
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega⟩

/-! ## `MixedGap` restated over the upward form -/

/-- `MixedGap` with `IsCrookedSeqUp` in place of `IsCrookedSeq`. This is the form to attack:
the sharpened `sync_up` applies to it, and its hypothesis is what `maxIdx` supplies. -/
def MixedGapUp : Prop :=
  ∀ (m : ℕ) (ρ : Fin m → ℤ) (i : Fin m), IsLip ρ → IsCrookedSeqUp ρ →
    ¬ (hStarArm (armT ρ i) (ρ i) + 2 ≤ hStarArm (armG ρ i) (ρ i) ∧
       lStarArm (armT ρ i) (ρ i) + 2 ≤ lStarArm (armG ρ i) (ρ i))

/-- Under `MixedGapUp`, the two arms in the residual configuration both exit the window, one
upward and one downward, with everything between inside it — so `sync_up` applies with the
first drop and the first rise as witnesses. Recorded as the shape of the intended proof. -/
def MixedGapUp_witnesses : Prop :=
  ∀ (m : ℕ) (ρ : Fin m → ℤ) (i : Fin m), IsLip ρ → IsCrookedSeqUp ρ →
    hStarArm (armT ρ i) (ρ i) + 2 ≤ hStarArm (armG ρ i) (ρ i) →
    lStarArm (armT ρ i) (ρ i) + 2 ≤ lStarArm (armG ρ i) (ρ i) →
    ∃ u v : Fin m, u < v ∧ ρ u = ρ i - 2 ∧ ρ v = ρ i + 2 ∧
      ∀ w : Fin m, u < w → w < v → ρ i - 1 ≤ ρ w ∧ ρ w ≤ ρ i + 1

end HPC.Fold
