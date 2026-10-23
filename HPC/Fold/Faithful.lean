import HPC.Fold.IntervalWitness

/-!
# The faithful model, with a realization theorem

`IsCrookedIv` (batch 20) is necessary but not sufficient, for two reasons the geometry
dictates and the definition omitted:

* **Adjacency.** Two overlapping links lie in the intersection of all their containing coarse
  links, so the union of their two index-intervals must fit in two consecutive indices. A
  width-2 link at `{a, a+1}` cannot neighbour a link touching `a + 2`, since
  `d_a ∩ d_{a+1} ∩ d_{a+2} = ∅`. Both batch-20 witnesses violate this at several places.
* **Forced meetings.** A link overlaps each neighbour and therefore meets every coarse link
  its neighbour lies in. Those meetings fire crookedness hypotheses.

`IsCrookedIvF` imposes both. Two theorems close the model question: a crooked chain lands in
it (necessity), and every sequence in it is the `(minIdx, maxIdx)` pair of an explicit crooked
chain of open rectangles in `ℝ × ℝ` (sufficiency). After this batch a counterexample in the
model *is* a chain, by construction.

English proofs: COMMISSION-batch22.md §3; the endpoint table actually used is in
REPORT-batch22.md. Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

open Set

/-- The faithful model. -/
structure IsCrookedIvF {n : ℕ} (ρ σ : Fin n → ℤ) : Prop where
  le : ∀ t, ρ t ≤ σ t
  width : ∀ t, σ t ≤ ρ t + 1
  /-- geometric adjacency: the two intervals of neighbours fit in two consecutive indices -/
  adj : ∀ t t' : Fin n, t'.val = t.val + 1 → max (σ t) (σ t') ≤ min (ρ t) (ρ t') + 1
  /-- crookedness, with hypotheses on forced meetings -/
  crooked : ∀ s t : Fin n, s < t → ∀ h k : ℤ,
    (∃ u : Fin n, ((u : ℤ) - s).natAbs ≤ 1 ∧ ρ u ≤ h ∧ h ≤ σ u) →
    (∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ k ∧ k ≤ σ u) →
    3 ≤ |h - k| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (h < k → (ρ r ≤ k - 1 ∧ k - 1 ≤ σ r) ∧ (ρ r' ≤ h + 1 ∧ h + 1 ≤ σ r')) ∧
      (k < h → (ρ r ≤ k + 1 ∧ k + 1 ≤ σ r) ∧ (ρ r' ≤ h - 1 ∧ h - 1 ≤ σ r'))

theorem IsCrookedIvF.isCrookedIv {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ) :
    IsCrookedIv ρ σ := by
  refine ⟨h.le, h.width, ?_, ?_⟩
  · intro t t' htt'
    have hadj := h.adj t t' htt'
    rw [max_le_iff] at hadj
    have := h.le t
    have := h.le t'
    constructor <;> omega
  · intro s t hst hh kk h1 h2 h3 h4 habs
    exact h.crooked s t hst hh kk ⟨s, by simp, h1, h2⟩ ⟨t, by simp, h3, h4⟩ habs

/-- Both members of a neighbouring pair are pinned by the adjacency condition, in the
symmetric form used throughout: this also covers `u = t`, where it is `width`. -/
theorem IsCrookedIvF.near {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) {t u : Fin n}
    (h : ((u : ℤ) - t).natAbs ≤ 1) : σ t ≤ ρ u + 1 ∧ σ u ≤ ρ t + 1 := by
  have hwt := hf.width t
  have hwu := hf.width u
  have hlt := hf.le t
  have hlu := hf.le u
  rcases eq_or_ne u t with rfl | hne
  · exact ⟨by omega, by omega⟩
  · have hval : u.val = t.val + 1 ∨ t.val = u.val + 1 := by
      have : (u : ℤ) ≠ (t : ℤ) := by
        simpa [Fin.ext_iff] using fun hh => hne (Fin.ext (by exact_mod_cast hh))
      omega
    rcases hval with h1 | h1
    · have := hf.adj t u h1
      rw [max_le_iff] at this
      omega
    · have := hf.adj u t h1
      rw [max_le_iff] at this
      omega

/-! ## A decidable criterion for the faithful model

The crookedness clause quantifies over integers `h` and `k`; the width clause pins each of
them to one of the two ends of the interval of the witnessing neighbour, so the clause is
equivalent to a statement quantified over two indices and two Booleans, which `decide` can
check on concrete data. -/

/-- The finite (decidable) form of `IsCrookedIvF`. -/
def IsCrookedIvFCheck {n : ℕ} (ρ σ : Fin n → ℤ) : Prop :=
  (∀ t, ρ t ≤ σ t) ∧ (∀ t, σ t ≤ ρ t + 1) ∧
  (∀ t t' : Fin n, t'.val = t.val + 1 → max (σ t) (σ t') ≤ min (ρ t) (ρ t') + 1) ∧
  (∀ s t : Fin n, s < t → ∀ u v : Fin n, ((u : ℤ) - s).natAbs ≤ 1 → ((v : ℤ) - t).natAbs ≤ 1 →
    ∀ b b' : Bool, 3 ≤ |ivEnd ρ σ b u - ivEnd ρ σ b' v| →
      ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
        (ivEnd ρ σ b u < ivEnd ρ σ b' v →
          (ρ r ≤ ivEnd ρ σ b' v - 1 ∧ ivEnd ρ σ b' v - 1 ≤ σ r) ∧
          (ρ r' ≤ ivEnd ρ σ b u + 1 ∧ ivEnd ρ σ b u + 1 ≤ σ r')) ∧
        (ivEnd ρ σ b' v < ivEnd ρ σ b u →
          (ρ r ≤ ivEnd ρ σ b' v + 1 ∧ ivEnd ρ σ b' v + 1 ≤ σ r) ∧
          (ρ r' ≤ ivEnd ρ σ b u - 1 ∧ ivEnd ρ σ b u - 1 ≤ σ r')))

/-- The finite criterion suffices. -/
theorem isCrookedIvF_of_check {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvFCheck ρ σ) :
    IsCrookedIvF ρ σ := by
  obtain ⟨hle, hw, hadj, hcr⟩ := h
  have hf0 : ∀ w : Fin n, ivEnd ρ σ false w = ρ w := fun _ => rfl
  have hf1 : ∀ w : Fin n, ivEnd ρ σ true w = σ w := fun _ => rfl
  refine ⟨hle, hw, hadj, ?_⟩
  rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  have hbu : hh = ivEnd ρ σ false u ∨ hh = ivEnd ρ σ true u := by
    rw [hf0, hf1]; have := hw u; omega
  have hbv : kk = ivEnd ρ σ false v ∨ kk = ivEnd ρ σ true v := by
    rw [hf0, hf1]; have := hw v; omega
  rcases hbu with e | e <;> rcases hbv with e' | e' <;> subst e <;> subst e'
  · exact hcr s t hst u v hu hv false false habs
  · exact hcr s t hst u v hu hv false true habs
  · exact hcr s t hst u v hu hv true false habs
  · exact hcr s t hst u v hu hv true true habs

open HPC.Chain in
/-- One application of 1948 crookedness, from meeting hypotheses: the `crookedIv_step` of
batch 20 with `meets` in place of `lies in`. -/
theorem crookedIvF_step {X : Type*} [MetricSpace X] {m c : ℕ}
    {E : Chain X m} {D : Chain X c} (hcr : E.IsCrookedIn' D) {s t : Fin m} (hst : s < t)
    (a b : Fin c) (ha : (E.link s ∩ D.link a).Nonempty) (hb : (E.link t ∩ D.link b).Nonempty)
    (hab : 3 ≤ |(a : ℤ) - (b : ℤ)|) :
    ∃ r r' : Fin m, s < r ∧ r < r' ∧ r' < t ∧
      ((a : ℤ) < (b : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) - 1 ∧ (b : ℤ) - 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) + 1 ∧
          (a : ℤ) + 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) ∧
      ((b : ℤ) < (a : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) - 1 ∧
          (a : ℤ) - 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) := by
  have href := hcr.1
  rcases lt_or_gt_of_ne (fun (hab' : (a : ℤ) = (b : ℤ)) => by
      rw [hab'] at hab; simp at hab) with hlt | hgt
  · have hidx : a.val + 2 < b.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 a b hidx s t ha hb
    have horder : s < r ∧ r < r' ∧ r' < t := by
      rcases hbtw with hb' | hb'
      · exact hb'
      · exact absurd hst (not_lt.mpr ((hb'.2.2.trans hb'.2.1).trans hb'.1).le)
    refine ⟨r, r', horder.1, horder.2.1, horder.2.2, fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      fun hcon => absurd hcon (by omega)⟩
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
  · have hidx : b.val + 2 < a.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 b a hidx t s hb ha
    have horder : s < r' ∧ r' < r ∧ r < t := by
      rcases hbtw with hb' | hb'
      · exact absurd hst (not_lt.mpr ((hb'.1.trans hb'.2.1).trans hb'.2.2).le)
      · exact ⟨hb'.2.2, hb'.2.1, hb'.1⟩
    refine ⟨r', r, horder.1, horder.2.1, horder.2.2, fun hcon => absurd hcon (by omega),
      fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega

open HPC.Chain in
/-- **Necessity.** A crooked chain lands in the faithful model. -/
theorem isCrookedIvF_minIdx_maxIdx {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : Chain X m} {D : Chain X k} (h : E.IsCrookedIn' D) :
    IsCrookedIvF (fun t => (h.1.minIdx t : ℤ)) (fun t => (h.1.maxIdx t : ℤ)) := by
  have href := h.1
  have hle : ∀ t, ((href.minIdx t : ℕ) : ℤ) ≤ ((href.maxIdx t : ℕ) : ℤ) := by
    intro t
    have := Fin.le_def.mp (minIdx_le href t (maxIdx_subset href t))
    exact_mod_cast this
  have hwidth : ∀ t, ((href.maxIdx t : ℕ) : ℤ) ≤ ((href.minIdx t : ℕ) : ℤ) + 1 := by
    intro t
    have hadj := subset_adjacent_of_subset href t (minIdx_subset href t) (maxIdx_subset href t)
    have := hle t
    omega
  -- a link whose interval contains `j` lies in the coarse link with index `j`
  have hpin : ∀ (t : Fin m) (j : ℤ), ((href.minIdx t : ℕ) : ℤ) ≤ j →
      j ≤ ((href.maxIdx t : ℕ) : ℤ) → ∃ a : Fin k, E.link t ⊆ D.link a ∧ ((a : ℕ) : ℤ) = j := by
    intro t j h1 h2
    have := hwidth t
    rcases (by omega : j = ((href.minIdx t : ℕ) : ℤ) ∨ j = ((href.maxIdx t : ℕ) : ℤ)) with e | e
    · exact ⟨href.minIdx t, minIdx_subset href t, e.symm⟩
    · exact ⟨href.maxIdx t, maxIdx_subset href t, e.symm⟩
  refine ⟨hle, hwidth, ?_, ?_⟩
  · intro t t' htt'
    have h1 := hle t
    have h2 := hle t'
    have h3 := hwidth t
    have h4 := hwidth t'
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t t').mpr (by omega)
    have hA : ((href.maxIdx t : ℤ) - (href.minIdx t' : ℤ)).natAbs ≤ 1 :=
      (D.adjacent _ _).mp ⟨z, maxIdx_subset href t hz1, minIdx_subset href t' hz2⟩
    have hB : ((href.maxIdx t' : ℤ) - (href.minIdx t : ℤ)).natAbs ≤ 1 :=
      (D.adjacent _ _).mp ⟨z, maxIdx_subset href t' hz2, minIdx_subset href t hz1⟩
    rw [max_le_iff]
    simp only [] at *
    omega
  · rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    obtain ⟨a, ha, hav⟩ := hpin u hh hu1 hu2
    obtain ⟨b, hb, hbv⟩ := hpin v kk hv1 hv2
    have hmeet_s : (E.link s ∩ D.link a).Nonempty := by
      obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff s u).mpr (by
        have : ((u : ℤ) - (s : ℤ)).natAbs ≤ 1 := hu
        omega)
      exact ⟨z, hz1, ha hz2⟩
    have hmeet_t : (E.link t ∩ D.link b).Nonempty := by
      obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t v).mpr (by
        have : ((v : ℤ) - (t : ℤ)).natAbs ≤ 1 := hv
        omega)
      exact ⟨z, hz1, hb hz2⟩
    obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
      crookedIvF_step h hst a b hmeet_s hmeet_t (by rw [hav, hbv]; exact habs)
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by omega)
      omega
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by omega)
      omega

/-! ## Sufficiency: the realization -/

/-- Coarse strip `j`: `(j, j + 3/2) × ℝ`. Consecutive strips overlap in `(j + 1, j + 3/2)`;
strips two apart are disjoint. -/
def strip (j : ℤ) : Set (ℝ × ℝ) := Set.Ioo (j : ℝ) (j + 3/2) ×ˢ Set.univ

section Endpoints

variable {n : ℕ}

/-- The left neighbour test: some neighbour of `t` reaches the index `ρ t − 1`. -/
def ExtL (ρ : Fin n → ℤ) (t : Fin n) : Prop :=
  ∃ u : Fin n, ((u : ℤ) - t).natAbs = 1 ∧ ρ u ≤ ρ t - 1

/-- The right neighbour test: some neighbour of `t` reaches the index `σ t + 1`. -/
def ExtR (σ : Fin n → ℤ) (t : Fin n) : Prop :=
  ∃ u : Fin n, ((u : ℤ) - t).natAbs = 1 ∧ σ t + 1 ≤ σ u

instance decidableExtL (ρ : Fin n → ℤ) (t : Fin n) : Decidable (ExtL ρ t) := by
  unfold ExtL; infer_instance

instance decidableExtR (σ : Fin n → ℤ) (t : Fin n) : Decidable (ExtR σ t) := by
  unfold ExtR; infer_instance

/-- The left endpoint of the `x`-range of link `t`, in eighths: `8ρ + 9` for a width-2 link
(which sits in the overlap `(ρ + 1, ρ + 3/2)`), `8ρ + 2` for a width-1 link extended left,
`8ρ + 4` otherwise. -/
def lxN (ρ σ : Fin n → ℤ) (t : Fin n) : ℤ :=
  if σ t = ρ t + 1 then 8 * ρ t + 9 else if ExtL ρ t then 8 * ρ t + 2 else 8 * ρ t + 4

/-- The right endpoint of the `x`-range of link `t`, in eighths: `8ρ + 11` for a width-2 link
or a width-1 link extended right, `8ρ + 8` otherwise. -/
def rxN (ρ σ : Fin n → ℤ) (t : Fin n) : ℤ :=
  if σ t = ρ t + 1 then 8 * ρ t + 11 else if ExtR σ t then 8 * ρ t + 11 else 8 * ρ t + 8

variable {ρ σ : Fin n → ℤ}

/-- A width-2 link has no left extension: its neighbours lie inside its own interval. -/
theorem not_extL_of_width_two (hf : IsCrookedIvF ρ σ) {t : Fin n} (h2 : σ t = ρ t + 1) :
    ¬ ExtL ρ t := by
  rintro ⟨u, hu, h⟩
  have := (hf.near (t := t) (u := u) (by omega)).1
  omega

/-- A width-2 link has no right extension. -/
theorem not_extR_of_width_two (hf : IsCrookedIvF ρ σ) {t : Fin n} (h2 : σ t = ρ t + 1) :
    ¬ ExtR σ t := by
  rintro ⟨u, hu, h⟩
  have := (hf.near (t := t) (u := u) (by omega)).2
  omega

/-- The `x`-range of a link is a nonempty interval. -/
theorem lxN_lt_rxN (hf : IsCrookedIvF ρ σ) (t : Fin n) : lxN ρ σ t < rxN ρ σ t := by
  have hw := hf.width t
  have hl := hf.le t
  by_cases h2 : σ t = ρ t + 1
  · simp only [lxN, rxN, if_pos h2]; omega
  · by_cases hL : ExtL ρ t <;> by_cases hR : ExtR σ t <;>
      simp only [lxN, rxN, h2, hL, hR, if_true, if_neg, not_false_iff] <;> omega

/-- Every right endpoint is at least `ρ + 1`. -/
theorem rxN_ge (ρ σ : Fin n → ℤ) (t : Fin n) : 8 * ρ t + 8 ≤ rxN ρ σ t := by
  unfold rxN; split_ifs <;> omega

/-- **The containment table.** The `x`-range of link `t` lies inside the `x`-range of strip `j`
exactly for the indices `j` of the interval of `t`. -/
theorem strip_table (hf : IsCrookedIvF ρ σ) (t : Fin n) (j : ℤ) :
    (8 * j ≤ lxN ρ σ t ∧ rxN ρ σ t ≤ 8 * j + 12) ↔ (ρ t ≤ j ∧ j ≤ σ t) := by
  have hw := hf.width t
  have hl := hf.le t
  by_cases h2 : σ t = ρ t + 1
  · simp only [lxN, rxN, if_pos h2]
    omega
  · have hs : σ t = ρ t := by omega
    by_cases hL : ExtL ρ t <;> by_cases hR : ExtR σ t <;>
      simp only [lxN, rxN, h2, hL, hR, if_true, if_neg, not_false_iff] <;> omega

/-- **The meeting table, in terms of the extension flags.** -/
theorem meet_range (hf : IsCrookedIvF ρ σ) (t : Fin n) (j : ℤ) :
    (8 * j < rxN ρ σ t ∧ lxN ρ σ t < 8 * j + 12) ↔
      ((if ExtL ρ t then ρ t - 1 else ρ t) ≤ j ∧ j ≤ (if ExtR σ t then σ t + 1 else σ t)) := by
  have hw := hf.width t
  have hl := hf.le t
  by_cases h2 : σ t = ρ t + 1
  · have hL := not_extL_of_width_two hf h2
    have hR := not_extR_of_width_two hf h2
    simp only [lxN, rxN, if_pos h2, hL, hR, if_false]
    omega
  · have hs : σ t = ρ t := by omega
    by_cases hL : ExtL ρ t <;> by_cases hR : ExtR σ t <;>
      simp only [lxN, rxN, h2, hL, hR, if_true, if_neg, not_false_iff] <;> omega

/-- **The meeting table.** The `x`-range of link `t` meets the `x`-range of strip `j` exactly
for the indices `j` belonging to the interval of `t` or of one of its neighbours. -/
theorem meet_table (hf : IsCrookedIvF ρ σ) (t : Fin n) (j : ℤ) :
    (8 * j < rxN ρ σ t ∧ lxN ρ σ t < 8 * j + 12) ↔
      ∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ j ∧ j ≤ σ u := by
  rw [meet_range hf t j]
  have hw := hf.width t
  have hl := hf.le t
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hin : ρ t ≤ j ∧ j ≤ σ t
    · exact ⟨t, by simp, hin.1, hin.2⟩
    · by_cases hlt : j < ρ t
      · have hL : ExtL ρ t := by by_contra hL; simp only [if_neg hL] at h1; omega
        obtain ⟨u, hu, hu1⟩ := id hL
        have hn := hf.near (t := t) (u := u) (by omega)
        have hlu := hf.le u
        simp only [if_pos hL] at h1
        exact ⟨u, by omega, by omega, by omega⟩
      · have hgt : σ t < j := by
          by_contra hc
          exact hin ⟨by omega, by omega⟩
        have hR : ExtR σ t := by by_contra hR; simp only [if_neg hR] at h2; omega
        obtain ⟨u, hu, hu1⟩ := id hR
        have hn := hf.near (t := t) (u := u) (by omega)
        have hlu := hf.le u
        simp only [if_pos hR] at h2
        exact ⟨u, by omega, by omega, by omega⟩
  · rintro ⟨u, hu, hu1, hu2⟩
    have hn := hf.near (t := t) (u := u) hu
    have hlu := hf.le u
    constructor
    · by_cases hL : ExtL ρ t
      · simp only [if_pos hL]; omega
      · simp only [if_neg hL]
        rcases (by omega : (u : ℤ) = (t : ℤ) ∨ ((u : ℤ) - t).natAbs = 1) with he | he
        · have : u = t := Fin.ext (by exact_mod_cast he)
          subst this; omega
        · have : ¬ (ρ u ≤ ρ t - 1) := fun hc => hL ⟨u, he, hc⟩
          omega
    · by_cases hR : ExtR σ t
      · simp only [if_pos hR]; omega
      · simp only [if_neg hR]
        rcases (by omega : (u : ℤ) = (t : ℤ) ∨ ((u : ℤ) - t).natAbs = 1) with he | he
        · have : u = t := Fin.ext (by exact_mod_cast he)
          subst this; omega
        · have : ¬ (σ t + 1 ≤ σ u) := fun hc => hR ⟨u, he, hc⟩
          omega

/-- **The overlap of neighbours.** The `x`-ranges of two neighbouring links meet: the
extension rule puts both into a common overlap zone when their intervals differ, and their
cores share a strip when they agree. -/
theorem lxN_lt_rxN_adj (hf : IsCrookedIvF ρ σ) {t u : Fin n} (h : ((u : ℤ) - t).natAbs = 1) :
    lxN ρ σ t < rxN ρ σ u := by
  have hn := hf.near (t := t) (u := u) (by omega)
  have hlt := hf.le t
  have hlu := hf.le u
  have hwt' := hf.width t
  have hwu' := hf.width u
  have hsym : ((t : ℤ) - u).natAbs = 1 := by omega
  by_cases hwt : σ t = ρ t + 1
  · have hlx : lxN ρ σ t = 8 * ρ t + 9 := by simp only [lxN, if_pos hwt]
    by_cases hwu : σ u = ρ u + 1
    · have : rxN ρ σ u = 8 * ρ u + 11 := by simp only [rxN, if_pos hwu]
      omega
    · by_cases hR : ExtR σ u
      · have : rxN ρ σ u = 8 * ρ u + 11 := by simp only [rxN, if_neg hwu, if_pos hR]
        omega
      · have hst : ¬ (σ u + 1 ≤ σ t) := fun hc => hR ⟨t, hsym, hc⟩
        have : rxN ρ σ u = 8 * ρ u + 8 := by simp only [rxN, if_neg hwu, if_neg hR]
        omega
  · have hst : σ t = ρ t := by omega
    have hle4 : lxN ρ σ t ≤ 8 * ρ t + 4 := by
      unfold lxN; rw [if_neg hwt]; split_ifs <;> omega
    by_cases hlow : ρ u ≤ ρ t - 1
    · have hL : ExtL ρ t := ⟨u, h, by omega⟩
      have hlx : lxN ρ σ t = 8 * ρ t + 2 := by simp only [lxN, if_neg hwt, if_pos hL]
      by_cases hwu : σ u = ρ u + 1
      · have : rxN ρ σ u = 8 * ρ u + 11 := by simp only [rxN, if_pos hwu]
        omega
      · have hR : ExtR σ u := ⟨t, hsym, by omega⟩
        have : rxN ρ σ u = 8 * ρ u + 11 := by simp only [rxN, if_neg hwu, if_pos hR]
        omega
    · have := rxN_ge ρ σ u
      omega

end Endpoints

/-- The `x`-range of link `t`, the open interval with endpoints `lxN/8` and `rxN/8`. -/
noncomputable def linkX {n : ℕ} (ρ σ : Fin n → ℤ) (t : Fin n) : Set ℝ :=
  Set.Ioo ((lxN ρ σ t : ℝ) / 8) ((rxN ρ σ t : ℝ) / 8)

/-- Link `t` occupies its `x`-range at height lane `t`: `(t, t + 3/2)`. Consecutive lanes
overlap; lanes two apart are disjoint. -/
noncomputable def linkRect {n : ℕ} (ρ σ : Fin n → ℤ) (t : Fin n) : Set (ℝ × ℝ) :=
  linkX ρ σ t ×ˢ Set.Ioo (t : ℝ) (t + 3/2)

/-! ### Intervals with endpoints in eighths -/

/-- Containment of two intervals with endpoints in eighths. -/
theorem ioo8_subset_iff {p q u v : ℤ} (hpq : p < q) :
    Set.Ioo ((p : ℝ)/8) ((q : ℝ)/8) ⊆ Set.Ioo ((u : ℝ)/8) ((v : ℝ)/8) ↔ u ≤ p ∧ q ≤ v := by
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  rw [Set.Ioo_subset_Ioo_iff (by linarith)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast (by linarith : (u : ℝ) ≤ p),
      by exact_mod_cast (by linarith : (q : ℝ) ≤ v)⟩
  · rintro ⟨h1, h2⟩
    have h1' : (u : ℝ) ≤ p := by exact_mod_cast h1
    have h2' : (q : ℝ) ≤ v := by exact_mod_cast h2
    constructor <;> linarith

/-- Overlap of two intervals with endpoints in eighths. -/
theorem ioo8_inter_nonempty_iff {p q u v : ℤ} (hpq : p < q) (huv : u < v) :
    (Set.Ioo ((p : ℝ)/8) ((q : ℝ)/8) ∩ Set.Ioo ((u : ℝ)/8) ((v : ℝ)/8)).Nonempty ↔
      p < v ∧ u < q := by
  rw [Set.Ioo_inter_Ioo, Set.nonempty_Ioo, max_lt_iff, lt_min_iff, lt_min_iff]
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have huv' : (u : ℝ) < v := by exact_mod_cast huv
  constructor
  · rintro ⟨⟨-, h1⟩, h2, -⟩
    exact ⟨by exact_mod_cast (by linarith : (p : ℝ) < v),
      by exact_mod_cast (by linarith : (u : ℝ) < q)⟩
  · rintro ⟨h1, h2⟩
    have h1' : (p : ℝ) < v := by exact_mod_cast h1
    have h2' : (u : ℝ) < q := by exact_mod_cast h2
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- A strip, with its `x`-range written in eighths. -/
theorem strip_eq (j : ℤ) : strip j =
    Set.Ioo (((8 * j : ℤ) : ℝ)/8) (((8 * j + 12 : ℤ) : ℝ)/8) ×ˢ (Set.univ : Set ℝ) := by
  unfold strip; push_cast; ring_nf

/-- A lane, in eighths. -/
theorem lane_eq {n : ℕ} (t : Fin n) : Set.Ioo ((t : ℝ)) ((t : ℝ) + 3/2) =
    Set.Ioo (((8 * (t.val : ℤ) : ℤ) : ℝ)/8) (((8 * (t.val : ℤ) + 12 : ℤ) : ℝ)/8) := by
  push_cast; ring_nf

theorem lane_nonempty {n : ℕ} (t : Fin n) : (Set.Ioo ((t : ℝ)) ((t : ℝ) + 3/2)).Nonempty := by
  rw [Set.nonempty_Ioo]; linarith

/-- **Refinement, read off the endpoint table.** Link `t` lies in strip `j` exactly when `j`
belongs to the interval of `t`. -/
theorem linkRect_subset_strip_iff {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (t : Fin n)
    (j : ℤ) : linkRect ρ σ t ⊆ strip j ↔ (ρ t ≤ j ∧ j ≤ σ t) := by
  rw [← strip_table hf t j, strip_eq]
  constructor
  · intro hsub
    obtain ⟨y, hy⟩ := lane_nonempty (n := n) t
    have hx : linkX ρ σ t ⊆ Set.Ioo (((8 * j : ℤ) : ℝ)/8) (((8 * j + 12 : ℤ) : ℝ)/8) := by
      intro x hxm
      exact (hsub (Set.mk_mem_prod hxm hy)).1
    have := (ioo8_subset_iff (u := 8 * j) (v := 8 * j + 12) (lxN_lt_rxN hf t)).mp hx
    omega
  · intro hj
    have hx : linkX ρ σ t ⊆ Set.Ioo (((8 * j : ℤ) : ℝ)/8) (((8 * j + 12 : ℤ) : ℝ)/8) :=
      (ioo8_subset_iff (u := 8 * j) (v := 8 * j + 12) (lxN_lt_rxN hf t)).mpr (by omega)
    exact Set.prod_mono hx (Set.subset_univ _)

/-- **Forced meetings, read off the endpoint table.** Link `t` meets strip `j` exactly when `j`
belongs to the interval of `t` or of one of its neighbours. -/
theorem linkRect_meet_strip_iff {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (t : Fin n)
    (j : ℤ) : (linkRect ρ σ t ∩ strip j).Nonempty ↔
      ∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ j ∧ j ≤ σ u := by
  rw [← meet_table hf t j, strip_eq, linkRect, Set.prod_inter_prod, Set.prod_nonempty_iff,
    linkX, ioo8_inter_nonempty_iff (lxN_lt_rxN hf t) (by omega)]
  have hlane : (Set.Ioo ((t : ℝ)) ((t : ℝ) + 3/2) ∩ Set.univ).Nonempty := by
    rw [Set.inter_univ]; exact lane_nonempty t
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, hlane⟩

/-- The coarse chain of strips `0, …, M − 1`. -/
def stripChain (M : ℕ) : Chain (ℝ × ℝ) M where
  link j := strip (j.val : ℤ)
  isOpen _ := isOpen_Ioo.prod isOpen_univ
  adjacent i j := by
    rw [strip_eq, strip_eq, Set.prod_inter_prod, Set.prod_nonempty_iff,
      ioo8_inter_nonempty_iff (by omega) (by omega), Set.inter_univ]
    simp only [Set.univ_nonempty, and_true]
    omega

/-- The fine chain of link rectangles. -/
noncomputable def linkChain {n : ℕ} (ρ σ : Fin n → ℤ) (hf : IsCrookedIvF ρ σ) :
    Chain (ℝ × ℝ) n where
  link := linkRect ρ σ
  isOpen _ := by
    rw [linkRect, linkX]
    exact isOpen_Ioo.prod isOpen_Ioo
  adjacent t u := by
    rw [linkRect, linkRect, Set.prod_inter_prod, Set.prod_nonempty_iff, linkX, linkX,
      ioo8_inter_nonempty_iff (lxN_lt_rxN hf t) (lxN_lt_rxN hf u), lane_eq, lane_eq,
      ioo8_inter_nonempty_iff (by omega) (by omega)]
    constructor
    · rintro ⟨-, h1, h2⟩
      omega
    · intro h
      rcases (by omega : t = u ∨ ((u : ℤ) - t).natAbs = 1) with rfl | he
      · exact ⟨⟨lxN_lt_rxN hf t, lxN_lt_rxN hf t⟩, by omega, by omega⟩
      · exact ⟨⟨lxN_lt_rxN_adj hf he, lxN_lt_rxN_adj hf (by omega : ((t : ℤ) - u).natAbs = 1)⟩,
          by omega, by omega⟩

open HPC.Chain in
/-- **Sufficiency.** Every sequence in the faithful model is realized: the link chain refines
the strip chain, is crooked in it in the 1948 sense, and has exactly the given minimal and
maximal indices. -/
theorem realization {n M : ℕ} (ρ σ : Fin n → ℤ) (hf : IsCrookedIvF ρ σ)
    (hlo : ∀ t, 0 ≤ ρ t) (hhi : ∀ t, σ t < M) :
    ∃ h : (linkChain ρ σ hf).IsCrookedIn' (stripChain M),
      (∀ t, (h.1.minIdx t : ℤ) = ρ t) ∧ (∀ t, (h.1.maxIdx t : ℤ) = σ t) := by
  have hlink : ∀ (t : Fin n) (j : Fin M),
      (linkChain ρ σ hf).link t ⊆ (stripChain M).link j ↔
        (ρ t ≤ (j.val : ℤ) ∧ (j.val : ℤ) ≤ σ t) :=
    fun t j => linkRect_subset_strip_iff hf t (j.val : ℤ)
  have hmeet : ∀ (t : Fin n) (j : Fin M),
      ((linkChain ρ σ hf).link t ∩ (stripChain M).link j).Nonempty ↔
        ∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ (j.val : ℤ) ∧ (j.val : ℤ) ≤ σ u :=
    fun t j => linkRect_meet_strip_iff hf t (j.val : ℤ)
  -- the index of an admissible integer level
  have hidx : ∀ j : ℤ, 0 ≤ j → j < M → ∃ i : Fin M, (i.val : ℤ) = j := by
    intro j h1 h2
    exact ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
  have href : (linkChain ρ σ hf).Refines (stripChain M) := by
    intro t
    have h1 := hlo t
    have h2 := hhi t
    have h3 := hf.le t
    obtain ⟨i, hi⟩ := hidx (ρ t) (by omega) (by omega)
    exact ⟨i, (hlink t i).mpr ⟨by omega, by omega⟩⟩
  refine ⟨⟨href, ?_⟩, ?_, ?_⟩
  · intro hh kk hk i j hi hj
    rw [hmeet] at hi hj
    have habs : 3 ≤ |((hh : ℕ) : ℤ) - ((kk : ℕ) : ℤ)| := by
      rw [abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ ((kk : ℕ) : ℤ) - ((hh : ℕ) : ℤ))]
      omega
    have hhlt := hh.isLt
    have hklt := kk.isLt
    have hk1 : ((hh : ℕ) : ℤ) + 1 < M := by omega
    obtain ⟨p, hp⟩ := hidx (((kk : ℕ) : ℤ) - 1) (by omega) (by omega)
    obtain ⟨q, hq⟩ := hidx (((hh : ℕ) : ℤ) + 1) (by omega) (by omega)
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨r, r', h1, h2, h3, hasc, -⟩ :=
        hf.crooked i j hij ((hh : ℕ) : ℤ) ((kk : ℕ) : ℤ) hi hj habs
      obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by omega)
      refine ⟨r, r', Or.inl ⟨h1, h2, h3⟩, ?_, ?_⟩
      · have hsub := (hlink r p).mpr ⟨by omega, by omega⟩
        have hpe : p = ⟨kk.val - 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rwa [hpe] at hsub
      · have hsub := (hlink r' q).mpr ⟨by omega, by omega⟩
        have hqe : q = ⟨hh.val + 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rwa [hqe] at hsub
    · -- a single link meets only three consecutive strips, so this case is vacuous
      exfalso
      obtain ⟨u, hu, hu1, hu2⟩ := hi
      obtain ⟨v, hv, hv1, hv2⟩ := hj
      have hnu := hf.near (t := i) (u := u) hu
      have hnv := hf.near (t := i) (u := v) hv
      have := hf.le i
      have := hf.width i
      omega
    · obtain ⟨r, r', h1, h2, h3, -, hdesc⟩ :=
        hf.crooked j i hij ((kk : ℕ) : ℤ) ((hh : ℕ) : ℤ) hj hi (by rw [abs_sub_comm]; exact habs)
      obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by omega)
      refine ⟨r', r, Or.inr ⟨h3, h2, h1⟩, ?_, ?_⟩
      · have hsub := (hlink r' p).mpr ⟨by omega, by omega⟩
        have hpe : p = ⟨kk.val - 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rwa [hpe] at hsub
      · have hsub := (hlink r q).mpr ⟨by omega, by omega⟩
        have hqe : q = ⟨hh.val + 1, by omega⟩ := Fin.ext (by simp only []; omega)
        rwa [hqe] at hsub
  · intro t
    have h1 := hlo t
    have h2 := hhi t
    have h3 := hf.le t
    obtain ⟨i, hi⟩ := hidx (ρ t) (by omega) (by omega)
    have hle := Fin.le_def.mp (minIdx_le href t ((hlink t i).mpr ⟨by omega, by omega⟩))
    have hge := ((hlink t (href.minIdx t)).mp (minIdx_subset href t)).1
    omega
  · intro t
    have h1 := hlo t
    have h2 := hhi t
    have h3 := hf.le t
    obtain ⟨i, hi⟩ := hidx (σ t) (by omega) (by omega)
    have hle := Fin.le_def.mp (le_maxIdx href t ((hlink t i).mpr ⟨by omega, by omega⟩))
    have hge := ((hlink t (href.maxIdx t)).mp (maxIdx_subset href t)).2
    omega

/-! ## A realized example

The realization theorem is not vacuous: here is a six-term member of the faithful model whose
crookedness clause genuinely fires — at `s = 0`, `t = 4`, with meeting indices `0` and `3` —
together with the chain of open rectangles that realizes it. -/

/-- A six-term sequence in the faithful model. -/
def demoRho : Fin 6 → ℤ := ![0, 1, 1, 1, 2, 2]

/-- Its upper ends. -/
def demoSig : Fin 6 → ℤ := ![0, 1, 2, 1, 2, 3]

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem demo_isCrookedIvF : IsCrookedIvF demoRho demoSig :=
  isCrookedIvF_of_check (by unfold IsCrookedIvFCheck ivEnd; decide)

open HPC.Chain in
/-- The example is realized by an explicit crooked chain of open rectangles on four strips. -/
theorem demo_realized :
    ∃ h : (linkChain demoRho demoSig demo_isCrookedIvF).IsCrookedIn' (stripChain 4),
      (∀ t, (h.1.minIdx t : ℤ) = demoRho t) ∧ (∀ t, (h.1.maxIdx t : ℤ) = demoSig t) :=
  realization demoRho demoSig demo_isCrookedIvF (by decide) (by decide)

/-! ## The batch-20 witnesses are not chains -/

/-- The 22-term batch-20 witness violates geometric adjacency at `t = 5`: the intervals are
`(6, 6)` and `(7, 8)`, and `max 6 8 = 8 > min 6 7 + 1 = 7`. -/
theorem ivSeq_not_faithful : ¬ IsCrookedIvF ivSeq ivSig := by
  intro h
  have hadj := h.adj 5 6 (by decide)
  rw [max_le_iff] at hadj
  have h1 : ivSig 6 = 8 := by decide
  have h2 : ivSeq 6 = 7 := by decide
  have h3 : ivSeq 5 = 6 := by decide
  omega

/-- The 24-term batch-20 witness violates geometric adjacency at `t = 0`: the intervals are
`(5, 5)` and `(6, 7)`, and `max 5 7 = 7 > min 5 6 + 1 = 6`. -/
theorem lpivSeq_not_faithful : ¬ IsCrookedIvF lpivSeq lpivSig := by
  intro h
  have hadj := h.adj 0 1 (by decide)
  rw [max_le_iff] at hadj
  have h1 : lpivSig 1 = 7 := by decide
  have h2 : lpivSeq 1 = 6 := by decide
  have h3 : lpivSeq 0 = 5 := by decide
  omega

/-! ## The route, over the faithful model -/

def F2PrimeF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (SegLam (armG ρ i) (ρ i) H L (hStar ρ i H L) ∧
       SegLam (armT ρ i) (ρ i) H L (hStar ρ i H L)) ∨
      (SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L) ∧
       SegVee (armT ρ i) (ρ i) H L (lStar ρ i H L))

open HPC.Chain in
theorem theorem3_of_F2PrimeF (hF2 : F2PrimeF) {X : Type*} [MetricSpace X] {n k : ℕ}
    (hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
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
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    have hLi : L ≤ ρ i := hLf i
    have hiH : ρ i ≤ H := hHf i
    rcases hF2 n ρ σ i H L hlip hcrook hLf hHf hcase ⟨tL, hL.symm⟩ ⟨tH, hH.symm⟩ with
      ⟨hG, hT⟩ | ⟨hG, hT⟩
    · exact exists_blocks_first_of_segLam href i (ρ i) H L (hStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [hStar]; omega) (by simp only [hStar]; omega) hLi
        (by simp only [hStar]; omega)
    · exact exists_blocks_first_of_segVee href i (ρ i) H L (lStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [lStar]; omega) (by simp only [lStar]; omega) hiH
        (by simp only [lStar]; omega)

end HPC.Fold
