import HPC.Fold.Itinerary
import HPC.Chains.Schedule

/-!
# The Synchronization Lemma

Crookedness constrains how the two arms of a chain, read outward from a link, may first leave
the window `[p−1, p+1]` around the basepoint's level. If one arm first leaves upward and the
other first leaves downward, then strictly between the two exit links — that is, among the
pre-exit links of both arms — some link sits at `p−1` and a later one at level at least `p`, in
the order running from the upward exit to the downward exit.

This is the base case of the corrected dichotomy (F2′): the arms cannot leave in opposite
directions immediately, and more generally an arm that leaves must first wiggle toward the
other arm's side.

Stated for an abstract crooked 1-Lipschitz sequence; the chain version follows by applying it
to `minIdx`.

English proofs: COMMISSION-batch7.md §3.

## The weakening directed by the commission

The commission (§3, `isCrookedSeq_minIdx`) anticipates that the exact values of the strong
form of `IsCrookedSeq` cannot be had for `minIdx`, and directs that in that case the
definition be weakened and the corollaries adjusted. That is what happened, and the loss is
exactly one unit downward in each of the four values: crookedness of the chain puts the link
`r` inside the coarse link `k − 1`, so `minIdx r ≤ k − 1`, but `minIdx r` may be one smaller
still (if `E.link r` also lies in the coarse link `k − 2`), and the only lower bound available
is the adjacency bound `minIdx r ≥ k − 2`. The strong form is therefore *not* provable for
`minIdx`, and the definition below records what is true. See `REPORT-batch7.md`.

The strong (commissioned) form is kept below verbatim as `IsCrookedSeqStrong`, together with
the implication `IsCrookedSeqStrong.isCrookedSeq`, so that nothing is lost.
-/

namespace HPC.Fold

/-- The commissioned strong form of crookedness of a sequence, with the exact values. It is
kept verbatim under a separate name because it is **not** satisfied by the minimal-index
sequence of a crooked refinement (see the module docstring), so the weakened `IsCrookedSeq`
below is what the file's theorems assume, as §3 of the commission directs. Every strongly
crooked sequence is crooked in the weak sense (`IsCrookedSeqStrong.isCrookedSeq`), so the
theorems apply to it too. -/
def IsCrookedSeqStrong {n : ℕ} (f : Fin n → ℤ) : Prop :=
  ∀ s t : Fin n, s < t → 3 ≤ |f t - f s| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (f s < f t → f r = f t - 1 ∧ f r' = f s + 1) ∧
      (f t < f s → f r = f t + 1 ∧ f r' = f s - 1)

/-- Crookedness of an integer sequence, in the form `IsCrookedIn'` gives for `minIdx`
(batch 4, `minIdx_subset`, `minIdx_le` and `subset_adjacent_of_subset`): for `s < t` whose
levels differ by at least 3, there are `s < r < r' < t` with `f r` within one *below* the
value adjacent to `f t` on the side of `f s`, and `f r'` within one *below* the value adjacent
to `f s` on the side of `f t`.

Ascending case (`f s < f t`): `f t - 2 ≤ f r ≤ f t - 1` and `f s ≤ f r' ≤ f s + 1`.
Descending case (`f t < f s`): `f t ≤ f r ≤ f t + 1` and `f s - 2 ≤ f r' ≤ f s - 1`. -/
def IsCrookedSeq {n : ℕ} (f : Fin n → ℤ) : Prop :=
  ∀ s t : Fin n, s < t → 3 ≤ |f t - f s| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (f s < f t → (f t - 2 ≤ f r ∧ f r ≤ f t - 1) ∧ (f s ≤ f r' ∧ f r' ≤ f s + 1)) ∧
      (f t < f s → (f t ≤ f r ∧ f r ≤ f t + 1) ∧ (f s - 2 ≤ f r' ∧ f r' ≤ f s - 1))

variable {n : ℕ} {f : Fin n → ℤ}

/-- The commissioned strong form implies the weak form used throughout the file. -/
theorem IsCrookedSeqStrong.isCrookedSeq (hf : IsCrookedSeqStrong f) : IsCrookedSeq f := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ := hf s t hst habs
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · obtain ⟨e1, e2⟩ := hasc hlt; omega
  · obtain ⟨e1, e2⟩ := hdesc hlt; omega

/-- **The Synchronization Lemma.** Let `u < v` be links with `f u = p + 2` and `f v = p − 2`,
and suppose every link strictly between them has level in `[p − 1, p + 1]`. Then there are
`u < j < k < v` with `f j = p − 1` and `f k ≥ p`.

(Commissioned conclusion: `f j = p − 1` and `f k = p + 1`. The second value is weakened to
`p ≤ f k` because the available form of crookedness loses a unit downward; the first survives
exactly, because `hmid` restores it. Together with `hmid` one also has `f k ≤ p + 1`.) -/
theorem sync (hf : IsCrookedSeq f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p + 2) (hv : f v = p - 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ f j = p - 1 ∧ p ≤ f k := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = -4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, -, hdesc⟩ := hf u v huv habs
  obtain ⟨⟨h1, h2⟩, ⟨h3, -⟩⟩ := hdesc (by omega)
  have hlow := (hmid r hur (lt_trans hrr' hr'v)).1
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega⟩

/-- The mirror form, with the downward exit first: `f j ≥ p` and `f k = p − 1`. -/
theorem sync' (hf : IsCrookedSeq f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p - 2) (hv : f v = p + 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ p ≤ f j ∧ f k = p - 1 := by
  have habs : 3 ≤ |f v - f u| := by
    have hd : f v - f u = 4 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'v, hasc, -⟩ := hf u v huv habs
  obtain ⟨⟨h1, -⟩, ⟨-, h4⟩⟩ := hasc (by omega)
  have hlow := (hmid r' (lt_trans hur hrr') hr'v).1
  exact ⟨r, r', hur, hrr', hr'v, by omega, by omega⟩

/-- **Immediate exits are impossible.** If `i` is a link with `f i = p` and the links two
steps away on each side are at `p + 2` and `p − 2`, the hypotheses of `sync` are met with
only one link in between, which cannot be at level `p − 1` once the sequence is 1-Lipschitz.
So no basepoint has both arms exiting the window within two steps.

(The 1-Lipschitz hypothesis `hlip` is added as §3 of the commission directs; without it the
statement is false, since the three intermediate levels could ascend from `p − 1` to `p + 1`.) -/
theorem no_immediate_opposite_exit (hf : IsCrookedSeq f) (p : ℤ) (i : Fin n)
    (a b : Fin n) (ha : a.val + 2 = i.val) (hb : i.val + 2 = b.val)
    (hlip : ∀ s t : Fin n, t.val = s.val + 1 → |f t - f s| ≤ 1)
    (hfi : f i = p) (hfa : f a = p + 2) (hfb : f b = p - 2)
    (hmid : ∀ w : Fin n, a < w → w < b → p - 1 ≤ f w ∧ f w ≤ p + 1) : False := by
  have hab : a < b := by rw [Fin.lt_def]; omega
  obtain ⟨j, k, haj, hjk, hkb, hfj, -⟩ := sync hf p a b hab hfa hfb hmid
  rw [Fin.lt_def] at haj hjk hkb
  -- `j` is either `a + 1` or `i`
  have hjval : j.val = a.val + 1 ∨ j.val = i.val := by omega
  rcases hjval with hj1 | hj2
  · have hstep := hlip a j hj1
    rw [abs_le] at hstep
    omega
  · have : j = i := Fin.ext hj2
    rw [this, hfi] at hfj
    omega

/-- **The wiggle corollary.** Under the hypotheses of `sync`, the sequence takes the value
`p − 1` strictly between the two exits and reaches level at least `p` again after that. In
particular the arm containing the upward exit dips to `p − 1` before that exit, or the other
arm dips to `p − 1` before its own exit. -/
theorem sync_dip (hf : IsCrookedSeq f) (p : ℤ) (u v : Fin n) (huv : u < v)
    (hu : f u = p + 2) (hv : f v = p - 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ f w ∧ f w ≤ p + 1) :
    ∃ j : Fin n, u < j ∧ j < v ∧ f j = p - 1 ∧
      ∃ k : Fin n, j < k ∧ k < v ∧ p ≤ f k := by
  obtain ⟨j, k, huj, hjk, hkv, hfj, hfk⟩ := sync hf p u v huv hu hv hmid
  exact ⟨j, huj, lt_trans hjk hkv, hfj, k, hjk, hkv, hfk⟩

/-! ## The chain form -/

open HPC.Chain in
/-- One application of crookedness, read through `minIdx`: if the minimal index of `E.link j`
exceeds that of `E.link i` by more than two, there are two links between them, in the order
running from `i` to `j`, the first within one below the coarse link just before `minIdx j`,
the second within one below the coarse link just after `minIdx i`. -/
theorem minIdx_crooked_step {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : HPC.Chain X m} {D : HPC.Chain X k} (h : E.IsCrookedIn' D) (i j : Fin m)
    (hij : (h.1.minIdx i).val + 2 < (h.1.minIdx j).val) :
    ∃ r s : Fin m, HPC.Chain.Between i r s j ∧
      (h.1.minIdx j).val ≤ (h.1.minIdx r).val + 2 ∧
      (h.1.minIdx r).val + 1 ≤ (h.1.minIdx j).val ∧
      (h.1.minIdx i).val ≤ (h.1.minIdx s).val ∧
      (h.1.minIdx s).val ≤ (h.1.minIdx i).val + 1 := by
  have hre := h.1
  have hcr := h.2
  have hmi : (E.link i ∩ D.link (hre.minIdx i)).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty i
    exact ⟨z, hz, minIdx_subset hre i hz⟩
  have hmj : (E.link j ∩ D.link (hre.minIdx j)).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty j
    exact ⟨z, hz, minIdx_subset hre j hz⟩
  obtain ⟨r, s, hbtw, hr, hs⟩ := hcr (hre.minIdx i) (hre.minIdx j) hij i j hmi hmj
  refine ⟨r, s, hbtw, ?_, ?_, ?_, ?_⟩
  · have h1 := subset_adjacent_of_subset hre r (minIdx_subset hre r) hr
    simp only [] at h1
    omega
  · have h2 := minIdx_le hre r hr
    rw [Fin.le_def] at h2
    simp only [] at h2
    omega
  · have h3 := subset_adjacent_of_subset hre s (minIdx_subset hre s) hs
    simp only [] at h3
    omega
  · have h4 := minIdx_le hre s hs
    rw [Fin.le_def] at h4
    simp only [] at h4
    omega

open HPC.Chain in
/-- The minimal-index sequence of a crooked refinement is a crooked sequence, in the weakened
sense of `IsCrookedSeq`. -/
theorem isCrookedSeq_minIdx {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : HPC.Chain X m} {D : HPC.Chain X k} (h : E.IsCrookedIn' D) :
    IsCrookedSeq (fun t => (h.1.minIdx t : ℤ)) := by
  intro s t hst habs
  simp only [] at habs
  have hcase : ((h.1.minIdx s).val + 2 < (h.1.minIdx t).val) ∨
      ((h.1.minIdx t).val + 2 < (h.1.minIdx s).val) := by
    rcases abs_cases (((h.1.minIdx t : ℕ) : ℤ) - ((h.1.minIdx s : ℕ) : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩
    · left; omega
    · right; omega
  rcases hcase with hasc | hdesc
  · obtain ⟨r, r', hbtw, b1, b2, b3, b4⟩ := minIdx_crooked_step h s t hasc
    have horder : s < r ∧ r < r' ∧ r' < t := by
      rcases hbtw with hb | hb
      · exact hb
      · have hts : t < r' := hb.2.2
        exact absurd hst (not_lt.mpr ((hts.trans hb.2.1).trans hb.1).le)
    refine ⟨r, r', horder.1, horder.2.1, horder.2.2, ?_, ?_⟩
    · intro _; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega
    · intro hcontra; simp only [] at hcontra; omega
  · obtain ⟨r, r', hbtw, b1, b2, b3, b4⟩ := minIdx_crooked_step h t s hdesc
    -- here the crossing runs from `t` down to `s`, so `s < r' < r < t`
    have horder : s < r' ∧ r' < r ∧ r < t := by
      rcases hbtw with hb | hb
      · exact absurd hst (not_lt.mpr ((hb.1.trans hb.2.1).trans hb.2.2).le)
      · exact ⟨hb.2.2, hb.2.1, hb.1⟩
    refine ⟨r', r, horder.1, horder.2.1, horder.2.2, ?_, ?_⟩
    · intro hcontra; simp only [] at hcontra; omega
    · intro _; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega

end HPC.Fold
