import HPC.Fold.CoverL5Land

/-!
# What the branch hypothesis supplies to the exact criterion

`CoverL5Low.lean` records the batch-58 identification: the branch hypothesis `LowAt (L+1) (L+8)`
*is* the descent announcement of the walk `L+6 → L+3 → L+7 → L+1 → L+8` — the engine's criterion at
the reflected parameter set `(P, K, M) = (L+4, L+6, L+2)` — so at the branch that walk's engine
criterion asks for two announcements about ascents and nothing else.

With the exact criterion of `HPC/Fold/Leg4Land.lean` the same walk asks for *less*, and this file
measures how much less. The landmark sentence names its landmarks one level nearer the middle
(`K - 1` and `M + 1` where the engine asks for `K` and `M - 1`) but imposes index gaps; and for a
1-Lipschitz arm based at `L + 5` **the index gaps are free**: a time at `L + 2` is at index at
least three because the arm starts at `L + 5`, a later time at `L + 6` is at least four steps after
it, and a descent to `L + 1` is at least `L + 6 - f d` steps after that. That is `isLip_gap`, and
it turns the second disjunct of the branch hypothesis into the whole descent clause of the exact
criterion (`land_down1_of_lowAt_low`).

So the branch's obligation at this walk, in exact form, is:

* the second disjunct of `LowAt` at every descent to `L + 1` — the first disjunct (a prior time at
  `L + 8`) does not by itself give the descent clause of this walk, since an arm that rises to
  `L + 8` before it ever falls to `L + 4` does not fold onto it at all; that is where the walks
  with valley `L + 1` take over (`HPC/Fold/Audit59.lean`);
* the two ascent clauses, in their landmark form, which are weaker than the engine's announcements
  of `s3_span_nine_mid5_of_ascents` by one level at each landmark.
-/

namespace HPC.Fold

/-! ## The index gaps are free -/

/-- **A 1-Lipschitz arm moves by at most one level per step**, so a level gap is an index gap. -/
theorem isLip_gap {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) :
    ∀ (n : ℕ) (j k : Fin m), k.val = j.val + n → f k - f j ≤ (n : ℤ) ∧ f j - f k ≤ (n : ℤ) := by
  intro n
  induction n with
  | zero =>
      intro j k hk
      have : k = j := Fin.ext (by omega)
      subst this
      simp
  | succ n ih =>
      intro j k hk
      have hkm := k.isLt
      have hnm : j.val + n < m := by omega
      obtain ⟨h1, h2⟩ := ih j ⟨j.val + n, hnm⟩ rfl
      have hstep := hf ⟨j.val + n, hnm⟩ k (by show k.val = j.val + n + 1; omega)
      rw [abs_le] at hstep
      push_cast
      omega

/-- The same, stated as an index bound from a level bound. -/
theorem isLip_index_gap {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) {j k : Fin m} (hjk : j.val ≤ k.val)
    (n : ℤ) (h : f j + n ≤ f k) : (j.val : ℤ) + n ≤ (k.val : ℤ) := by
  obtain ⟨h1, -⟩ := isLip_gap hf (k.val - j.val) j k (by omega)
  have : ((k.val - j.val : ℕ) : ℤ) = (k.val : ℤ) - (j.val : ℤ) := by
    push_cast [Nat.cast_sub hjk]; ring
  omega

/-- The same downwards. -/
theorem isLip_index_gap' {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) {j k : Fin m} (hjk : j.val ≤ k.val)
    (n : ℤ) (h : f k + n ≤ f j) : (j.val : ℤ) + n ≤ (k.val : ℤ) := by
  obtain ⟨-, h2⟩ := isLip_gap hf (k.val - j.val) j k (by omega)
  have : ((k.val - j.val : ℕ) : ℤ) = (k.val : ℤ) - (j.val : ℤ) := by
    push_cast [Nat.cast_sub hjk]; ring
  omega

/-! ## The descent clause of the walk `L+6 → L+3 → L+7 → L+1 → L+8` -/

/-- **The second disjunct of the branch hypothesis is the whole descent clause of the exact
criterion.** For a 1-Lipschitz arm based at `L + 5`, if before every descent to `L + 1` there is a
time at `L + 2` or below followed by one at `L + 6` or above, then the ceiling clause of
`Leg4Land` for the reflected parameter set `(P, K, M) = (L + 4, L + 6, L + 2)` holds — index
bounds included, which the Lipschitz condition supplies for nothing. -/
theorem land_down1_of_lowAt_low {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f) {L : ℤ}
    (h0 : f ⟨0, hm⟩ = L + 5)
    (hlow : ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, j.val < k.val ∧ k.val < d.val ∧
      f j ≤ L + 2 ∧ L + 6 ≤ f k) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 4 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧
      f j ≤ L + 4 ∧ L + 6 ≤ f k := by
  intro d hd
  obtain ⟨j, k, hjk, hkd, hj, hk⟩ := hlow d hd
  refine ⟨j, k, ?_, ?_, ?_, by omega, hk⟩
  · have := isLip_index_gap' hf (j := ⟨0, hm⟩) (k := j) (Nat.zero_le _) 3 (by omega)
    simpa using this
  · exact isLip_index_gap hf (le_of_lt hjk) 4 (by omega)
  · exact isLip_index_gap' hf (le_of_lt hkd) (L + 6 - f d) (by omega)

/-- **The exact criterion of the walk `L+6 → L+3 → L+7 → L+1 → L+8`, assembled.** The reflected
arm satisfies the landmark sentence of `(P, K, M) = (L + 4, L + 6, L + 2)` as soon as the branch
hypothesis is met in its second disjunct and the two ascent clauses hold in landmark form. -/
theorem leg4Land_walk63718_of_lowAt_low {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f)
    {L : ℤ} (h0 : f ⟨0, hm⟩ = L + 5)
    (hlow : ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, j.val < k.val ∧ k.val < d.val ∧
      f j ≤ L + 2 ∧ L + 6 ≤ f k)
    (hup8 : ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (f d - (L + 4)) ≤ (d.val : ℤ) ∧ f j ≤ L + 4)
    (hup9 : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k l : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 4 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧
      (l.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      f j ≤ L + 4 ∧ L + 6 ≤ f k ∧ f l ≤ L + 2) :
    Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    obtain ⟨j, hj1, hj2, hj3⟩ := hup8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hup9 d (by omega)
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := land_down1_of_lowAt_low hm hf h0 hlow d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The fold onto `L+6 → L+3 → L+7 → L+1 → L+8`, from the exact criterion.** -/
theorem foldsOnto_walk63718_of_land {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f) {L : ℤ}
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, j.val < k.val ∧ k.val < d.val ∧
      f j ≤ L + 2 ∧ L + 6 ≤ f k)
    (hup8 : ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (f d - (L + 4)) ≤ (d.val : ℤ) ∧ f j ≤ L + 4)
    (hup9 : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k l : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 4 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧
      (l.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      f j ≤ L + 4 ∧ L + 6 ≤ f k ∧ f l ≤ L + 2) :
    FoldsOnto f (leg4Len L (L + 9) (L + 6) (L + 2) (L + 4))
      (leg4Walk' L (L + 9) (L + 6) (L + 2) (L + 4)) := by
  refine foldsOnto_leg4W_refl f L (L + 9) (L + 6) (L + 2) (L + 4) ?_
  exact foldsOnto_leg4_of_leg4Land hm (armRefl (L + (L + 9)) f) (armRefl_isLip hf _)
    L (L + 9) (L + 6) (L + 2) (L + 4) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by simp only [armRefl_apply]; rw [h0]; omega)
    (by simp only [armRefl_apply]; rw [h0]; omega)
    (fun j => by simp only [armRefl_apply]; have := hH j; omega)
    (fun j => by simp only [armRefl_apply]; have := hL j; omega)
    (leg4Land_walk63718_of_lowAt_low hm hf h0 hlow hup8 hup9)

end HPC.Fold
