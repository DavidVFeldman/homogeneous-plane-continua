import HPC.Fold.Pair

/-!
# The outside-in induction step

Batch 33 proved the append lemma (`isZigFree_append_outer`), censused the trimming — the span
drops by exactly one at every step and never stalls — and found the defect in the sketch: the
maximal stretch is **not unique**, so the induction must choose one, and the basepoint does not
stay interior to the inner band.

This batch runs COMMISSION.md §1, and the answer splits in two.

**The gate as stated passes.** For every interior basepoint of `bing 0 n`, `n = 6 … 12` — 13 635
of them at span twelve — the greedy trims of span `H − L − 1` admit an inner walk, and *every*
walk serving the inner stretch's two arms extends, by appending `[L+1, H−1]` or `[H−1, L+1]`, to
a walk serving the whole arms. 0 failures at spans 9, 10, 11 and 12, in the strong ("every")
form and in the weak ("some") form alike.

**But the extension is then not a member of the family**, so the gate as stated cannot close the
induction. That is a theorem here, not an observation: `zigFree_append_forces_inner` says that
if `ts` is a member of the free family of `[L', H']` and `ts ++ [x, y]` — with `(x, y)` either
pair of outer legs — is a member of the free family of `[L, H]`, then `L + 1 ≤ L'` and
`H' ≤ H − 1`. A trim of span `H − L − 1` keeps one of the two extreme levels, so no extension of
any of its members is a member of the outer family, and `S3ZigFreeInterior` — whose conclusion
demands a member of the outer family — does not follow. The trim must strip *both* extremes,
and then the append does go through at any width: `isZigFree_append_outer'` generalises batch
33's lemma from the band `[L+1, H−1]` to every band strictly inside `[L, H]`.

**With the trim so corrected, the strong form of the step is false.** The census decides it
exactly at every interior basepoint of `bing 0 n`, `n = 6 … 12`, over every band inside
`[L+1, H−1]` and its maximal stretches: the "every" form fails at 10 of the 25 interior
basepoints at span six already, and at 2 406 of the 13 635 at span twelve. The first witness is
basepoint 5 of `bing 0 6`, at level 3: on the band `[1, 5]`, whose maximal stretch is the whole
of `[1, 69]`, the member `[2, 4, 2]` folds both inner arms, but its extension `[2, 4, 2, 5, 1]`
— a member of the free family of `[0, 6]` — does not fold the backward arm `3, 2, 1, 2, 1, 0`.
The weak ("some") form, by contrast, holds at every one of those basepoints at every span.

The reason is timing, and it too is a theorem: every target of an inner member is at least
`L + 2`, so the extension's centres stay at least `L + 2` for the whole of the inner walk
(`zigWalk_prefix`), and an arm that reaches level `L` at index `d` cannot be folded unless `d` is
at least the inner walk's length (`no_fold_of_early_low`). In the witness it is sharper still:
the extension runs `2 3 4 3 2 3 4 5 4 3 2 1` and comes near the bottom only at time eleven, while
the backward arm is at level `0` at index five. `bing6_arm_not_folded` is that instance, by the
engine `no_fold_of_low_early`.

What is delivered: the generalised append lemma; `zigFree_append_forces_inner`; the corrected
step `ExtendStepZF` and the induction it carries, `s3ZigFreeInterior_of_extendStepZF`, with the
case split on interiority discharged by `s3ZigFree_near_extreme`; the weak form `ExtendStepSome`
and its (immediate) implication; and the timing obstruction with its instance. The commissioned
`ExtendStep` is kept, and `extendStep` is kept commented out at the end with the census verdict.

English proofs: COMMISSION.md §2–§3, and REPORT-batch34.md.
-/

namespace HPC.Fold

/-! ## Trims -/

/-- A contiguous stretch of `ρ` containing `i`, with its own attained extremes and span one less
than the ambient. This is the commissioned notion; `IsInnerTrim` is the corrected one. -/
def IsTrim {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (a b : ℕ) (L' H' : ℤ) : Prop :=
  a ≤ i.val ∧ i.val ≤ b ∧ b < n ∧
  (∀ j : Fin n, a ≤ j.val → j.val ≤ b → L' ≤ ρ j ∧ ρ j ≤ H') ∧
  (∃ j : Fin n, a ≤ j.val ∧ j.val ≤ b ∧ ρ j = L') ∧
  (∃ j : Fin n, a ≤ j.val ∧ j.val ≤ b ∧ ρ j = H') ∧
  H' - L' ≤ H - L - 1

/-- **The corrected trim.** A contiguous stretch of `ρ` containing `i`, with its own attained
extremes, whose band is strictly inside `[L, H]` and still wide enough to carry the family.
`zigFree_append_forces_inner` shows that only such a trim can be appended to. -/
def IsInnerTrim {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ) (a b : ℕ) (L' H' : ℤ) : Prop :=
  a ≤ i.val ∧ i.val ≤ b ∧ b < n ∧
  (∀ j : Fin n, a ≤ j.val → j.val ≤ b → L' ≤ ρ j ∧ ρ j ≤ H') ∧
  (∃ j : Fin n, a ≤ j.val ∧ j.val ≤ b ∧ ρ j = L') ∧
  (∃ j : Fin n, a ≤ j.val ∧ j.val ≤ b ∧ ρ j = H') ∧
  L + 1 ≤ L' ∧ H' ≤ H - 1 ∧ L' + 3 ≤ H'

/-! ## The append lemma at any width -/

/-- Appending the legs `L + 1`, `H − 1` to a member of a band strictly inside `[L, H]` whose last
two targets are `p, q` with `q` its high extreme. The generalisation of batch 33's
`isZigFree_append_two` from the band `[L+1, H−1]` to any inner band. -/
theorem isZigFree_append_two_inner {L H L' H' x y : ℤ} {ts : List ℤ}
    (hL : L + 1 ≤ L') (hH : H' ≤ H - 1) (h3 : L' + 3 ≤ H')
    (hb : ∀ t ∈ ts, L' + 1 ≤ t ∧ t ≤ H' - 1)
    (hlen : 3 ≤ ts.length)
    (halt : ∀ j, j + 2 < ts.length → (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0)
    (hamp : ∀ j, 1 ≤ j → j + 2 < ts.length → |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|)
    (hp : ts[ts.length - 2]! = L' + 1) (hq : ts[ts.length - 1]! = H' - 1)
    (hx : x = L + 1) (hy : y = H - 1) :
    IsZigFree L H (ts ++ [x, y]) := by
  have hlenA : (ts ++ [x, y]).length = ts.length + 2 := by simp
  subst hx; subst hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have := hb t ht; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> omega
  · omega
  · intro j hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact halt j hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = L' + 1 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = H' - 1 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        exact mul_neg_of_pos_of_neg (by omega) (by omega)
      · have e2 : ts[j]! = H' - 1 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        exact mul_neg_of_neg_of_pos (by omega) (by omega)
  · intro j hj1 hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact hamp j hj1 hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = L' + 1 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = H' - 1 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
        omega
      · have e2 : ts[j]! = H' - 1 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
        omega
  · left
    rw [hlenA, show ts.length + 2 - 2 = ts.length by omega,
      show ts.length + 2 - 1 = ts.length + 1 by omega, getElem!_append2_fst,
      getElem!_append2_snd]

/-- The mirror of `isZigFree_append_two_inner`. -/
theorem isZigFree_append_two_inner' {L H L' H' x y : ℤ} {ts : List ℤ}
    (hL : L + 1 ≤ L') (hH : H' ≤ H - 1) (h3 : L' + 3 ≤ H')
    (hb : ∀ t ∈ ts, L' + 1 ≤ t ∧ t ≤ H' - 1)
    (hlen : 3 ≤ ts.length)
    (halt : ∀ j, j + 2 < ts.length → (ts[j+1]! - ts[j]!) * (ts[j+2]! - ts[j+1]!) < 0)
    (hamp : ∀ j, 1 ≤ j → j + 2 < ts.length → |ts[j+1]! - ts[j]!| < |ts[j+2]! - ts[j+1]!|)
    (hp : ts[ts.length - 2]! = H' - 1) (hq : ts[ts.length - 1]! = L' + 1)
    (hx : x = H - 1) (hy : y = L + 1) :
    IsZigFree L H (ts ++ [x, y]) := by
  have hlenA : (ts ++ [x, y]).length = ts.length + 2 := by simp
  subst hx; subst hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have := hb t ht; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> omega
  · omega
  · intro j hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact halt j hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = H' - 1 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = L' + 1 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        exact mul_neg_of_neg_of_pos (by omega) (by omega)
      · have e2 : ts[j]! = L' + 1 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        exact mul_neg_of_pos_of_neg (by omega) (by omega)
  · intro j hj1 hj
    rw [hlenA] at hj
    rcases Nat.lt_or_ge (j + 2) ts.length with hc | hc
    · rw [getElem!_append2_left (j := j) (by omega),
        getElem!_append2_left (j := j + 1) (by omega),
        getElem!_append2_left (j := j + 2) (by omega)]
      exact hamp j hj1 hc
    · rcases Nat.lt_or_ge (j + 1) ts.length with hc2 | hc2
      · have e1 : ts[j]! = H' - 1 := by rw [show j = ts.length - 2 by omega]; exact hp
        have e2 : ts[j + 1]! = L' + 1 := by rw [show j + 1 = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega),
          getElem!_append2_left (j := j + 1) (by omega), e1, e2,
          show j + 2 = ts.length by omega, getElem!_append2_fst]
        rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
        omega
      · have e2 : ts[j]! = L' + 1 := by rw [show j = ts.length - 1 by omega]; exact hq
        rw [getElem!_append2_left (j := j) (by omega), e2,
          show j + 2 = ts.length + 1 by omega, show j + 1 = ts.length by omega,
          getElem!_append2_fst, getElem!_append2_snd]
        rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
        omega
  · right
    rw [hlenA, show ts.length + 2 - 2 = ts.length by omega,
      show ts.length + 2 - 1 = ts.length + 1 by omega, getElem!_append2_fst,
      getElem!_append2_snd]

/-- **The append lemma at any width.** A member of the free family of a band strictly inside
`[L, H]` becomes a member of the free family of `[L, H]` when the two outer legs are appended;
which pair is appended is decided by the orientation of the inner member's end. -/
theorem isZigFree_append_outer' {L H L' H' : ℤ} {ts : List ℤ}
    (hL : L + 1 ≤ L') (hH : H' ≤ H - 1) (h3 : L' + 3 ≤ H')
    (h : IsZigFree L' H' ts) :
    IsZigFree L H (ts ++ [L + 1, H - 1]) ∨ IsZigFree L H (ts ++ [H - 1, L + 1]) := by
  rcases h.ends with he | he
  · have h1 : ts[ts.length - 2]! = L' + 1 := by
      have := congrArg Prod.fst he; simp only at this; omega
    have h2 : ts[ts.length - 1]! = H' - 1 := by
      have := congrArg Prod.snd he; simp only at this; omega
    exact Or.inl (isZigFree_append_two_inner hL hH h3 h.bounds h.len h.alt h.amp h1 h2 rfl rfl)
  · have h1 : ts[ts.length - 2]! = H' - 1 := by
      have := congrArg Prod.fst he; simp only at this; omega
    have h2 : ts[ts.length - 1]! = L' + 1 := by
      have := congrArg Prod.snd he; simp only at this; omega
    exact Or.inr (isZigFree_append_two_inner' hL hH h3 h.bounds h.len h.alt h.amp h1 h2 rfl rfl)

/-! ## Only a strictly inner trim can be appended to -/

/-- **The trim must strip both extremes.** If a member of the free family of `[L', H']` becomes a
member of the free family of `[L, H]` when the two outer legs are appended, then its band lies
strictly inside: `L + 1 ≤ L'` and `H' ≤ H − 1`. So a trim that keeps either extreme level — in
particular any trim of span `H − L − 1`, the one the sketch takes — is useless to the induction,
however well its walks fold. -/
theorem zigFree_append_forces_inner {L H L' H' x y : ℤ} {ts : List ℤ}
    (h : IsZigFree L' H' ts) (h3 : L' + 3 ≤ H')
    (hxy : (x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1))
    (hA : IsZigFree L H (ts ++ [x, y])) :
    L + 1 ≤ L' ∧ H' ≤ H - 1 := by
  have hm : 3 ≤ ts.length := h.len
  have hmem : ∀ k, k < ts.length → ts[k]! ∈ ts := by
    intro k hk
    rw [getElem!_pos ts k hk]
    exact List.getElem_mem _
  have hlenA : (ts ++ [x, y]).length = ts.length + 2 := by simp
  have e1 : ts.length - 2 + 1 = ts.length - 1 := by omega
  have e2 : ts.length - 2 + 2 = ts.length := by omega
  have e3 : ts.length - 1 + 1 = ts.length := by omega
  have e4 : ts.length - 1 + 2 = ts.length + 1 := by omega
  -- the two alternation and the two amplitude clauses at the join
  have halt1 := hA.alt (ts.length - 2) (by rw [hlenA]; omega)
  have hamp1 := hA.amp (ts.length - 2) (by omega) (by rw [hlenA]; omega)
  have halt2 := hA.alt (ts.length - 1) (by rw [hlenA]; omega)
  have hamp2 := hA.amp (ts.length - 1) (by omega) (by rw [hlenA]; omega)
  rw [e1, e2, getElem!_append2_left (by omega : ts.length - 2 < ts.length),
      getElem!_append2_left (by omega : ts.length - 1 < ts.length),
      getElem!_append2_fst] at halt1
  rw [e1, e2, getElem!_append2_left (by omega : ts.length - 2 < ts.length),
      getElem!_append2_left (by omega : ts.length - 1 < ts.length),
      getElem!_append2_fst] at hamp1
  rw [e3, e4, getElem!_append2_left (by omega : ts.length - 1 < ts.length),
    getElem!_append2_fst, getElem!_append2_snd] at halt2 hamp2
  -- the inner band lies weakly inside the outer one
  have hlow : L + 1 ≤ ts[ts.length - 2]! :=
    (hA.bounds _ (List.mem_append_left _ (hmem _ (by omega)))).1
  have hhigh : ts[ts.length - 2]! ≤ H - 1 :=
    (hA.bounds _ (List.mem_append_left _ (hmem _ (by omega)))).2
  have hlow' : L + 1 ≤ ts[ts.length - 1]! :=
    (hA.bounds _ (List.mem_append_left _ (hmem _ (by omega)))).1
  have hhigh' : ts[ts.length - 1]! ≤ H - 1 :=
    (hA.bounds _ (List.mem_append_left _ (hmem _ (by omega)))).2
  have hends := h.ends
  simp only [Prod.mk.injEq] at hends hxy
  set A := ts[ts.length - 2]! with hAdef
  set B := ts[ts.length - 1]! with hBdef
  rcases hends with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rcases hxy with ⟨hxv, hyv⟩ | ⟨hxv, hyv⟩ <;>
    subst hxv <;> subst hyv <;> rw [hp] at hlow hhigh <;> rw [hq] at hlow' hhigh' <;>
    rw [hp, hq] at halt1 hamp1 <;> rw [hq] at halt2 hamp2
  · -- ends low-high, legs (L+1, H-1)
    rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)] at hamp1
    rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)] at hamp2
    omega
  · -- ends low-high, legs (H-1, L+1): the alternation fails
    exfalso
    nlinarith [halt1]
  · -- ends high-low, legs (L+1, H-1): the alternation fails
    exfalso
    nlinarith [halt1]
  · -- ends high-low, legs (H-1, L+1)
    rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)] at hamp1
    rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)] at hamp2
    omega

/-- **A trim whose span is only one less is useless.** With the two outer legs appended, a member
of the free family of `[L', H']` can be a member of the free family of `[L, H]` only if the trim
stripped both extremes, so the span must drop by at least two. This is why the gate of
COMMISSION.md §1 — which passes, at every interior basepoint of `bing 0 n` for `n = 6 … 12` —
does not close the induction. -/
theorem no_outer_member_of_span_one_trim {L H L' H' x y : ℤ} {ts : List ℤ}
    (h : IsZigFree L' H' ts) (h3 : L' + 3 ≤ H')
    (hxy : (x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1))
    (hspan : H - L ≤ H' - L' + 1) :
    ¬ IsZigFree L H (ts ++ [x, y]) := by
  intro hA
  obtain ⟨h1, h2⟩ := zigFree_append_forces_inner h h3 hxy hA
  omega

/-! ## The step -/

/-- **`ExtendStep`.** The commissioned statement: some trim admits an inner walk, and every walk
serving the inner stretch's arms extends by the two outer legs to one serving the whole arms. -/
def ExtendStep : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 4 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∃ (a b : ℕ) (_hai : a ≤ i.val) (_hib : i.val ≤ b) (_hbn : b < n) (L' H' : ℤ),
      IsTrim ρ i L H a b L' H' ∧
      (∃ ts : List ℤ, IsZigFree L' H' ts ∧
        FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2) ∧
      ∀ ts : List ℤ, IsZigFree L' H' ts →
        FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2 →
        FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2 →
        ∃ x y : ℤ, ((x, y) = (L + 1, H - 1) ∨ (x, y) = (H - 1, L + 1)) ∧
          FoldsOnto (armG ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2 ∧
          FoldsOnto (armT ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2

/-- **`ExtendStepZF`.** The corrected step: the trim strips both extremes, the existence clause is
dropped — the induction hypothesis supplies the inner walk — and the extension is required to be
a member of the free family of the outer band, which is what `S3ZigFreeInterior` asks for and
what `zigFree_append_forces_inner` shows the commissioned trim cannot deliver. -/
def ExtendStepZF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 6 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∃ (a b : ℕ) (_hai : a ≤ i.val) (_hib : i.val ≤ b) (_hbn : b < n) (L' H' : ℤ),
      IsInnerTrim ρ i L H a b L' H' ∧
      ∀ ts : List ℤ, IsZigFree L' H' ts →
        FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2 →
        FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩) ⟨i.val - a, by omega⟩)
          (zigWalk ts).1 (zigWalk ts).2 →
        ∃ x y : ℤ, IsZigFree L H (ts ++ [x, y]) ∧
          FoldsOnto (armG ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2 ∧
          FoldsOnto (armT ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2

/-- **The induction the step carries.** Strong induction on the span: the trim's stretch is
faithful and crooked (`isCrookedIvF_restrict`), its extremes are attained and its span is at
least two smaller, so either the induction hypothesis (if the basepoint is still interior to the
inner band) or `s3ZigFree_near_extreme` (if it is not) supplies a walk serving the inner arms,
and `ExtendStepZF` extends it. -/
theorem s3ZigFreeInterior_of_extendStepZF (h : ExtendStepZF) : S3ZigFreeInterior := by
  have key : ∀ d : ℕ, ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      (H - L).toNat ≤ d → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
      ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
    intro d
    induction d with
    | zero =>
        intro n ρ σ i H L hd _ _ _ hLH _ _ _ _
        exact absurd hd (by omega)
    | succ d ih =>
        intro n ρ σ i H L hd hcr hLb hHb _ heL heH hlo hhi
        have hi0 := hLb i
        have h6 : L + 6 ≤ H := by omega
        obtain ⟨a, b, hai, hib, hbn, L', H', htrim, hevery⟩ :=
          h n ρ σ i H L hcr hLb hHb h6 heL heH hlo hhi
        obtain ⟨-, -, -, hband, ⟨jL, hjL1, hjL2, hjL3⟩, ⟨jH, hjH1, hjH2, hjH3⟩, hLL, hHH, h3⟩ :=
          htrim
        -- the stretch, its faithfulness, its band and its basepoint
        have hcr' : IsCrookedIvF (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
            (fun j : Fin (b - a + 1) => σ ⟨a + j.val, by omega⟩) :=
          isCrookedIvF_restrict hcr a b (by omega) hbn
        have hLb' : ∀ t : Fin (b - a + 1), L' ≤ ρ ⟨a + t.val, by omega⟩ := by
          intro t
          have ht := t.isLt
          exact (hband _ (by simp) (by simp; omega)).1
        have hHb' : ∀ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) ≤ H' := by
          intro t
          have ht := t.isLt
          exact (hband _ (by simp) (by simp; omega)).2
        have heL' : ∃ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) = L' := by
          refine ⟨⟨jL.val - a, by omega⟩, ?_⟩
          rw [show (⟨a + (jL.val - a), by omega⟩ : Fin n) = jL from Fin.ext (by simp; omega)]
          exact hjL3
        have heH' : ∃ t : Fin (b - a + 1), ρ (⟨a + t.val, by omega⟩ : Fin n) = H' := by
          refine ⟨⟨jH.val - a, by omega⟩, ?_⟩
          rw [show (⟨a + (jH.val - a), by omega⟩ : Fin n) = jH from Fin.ext (by simp; omega)]
          exact hjH3
        have hbase : ρ (⟨a + (i.val - a), by omega⟩ : Fin n) = ρ i := by
          rw [show (⟨a + (i.val - a), by omega⟩ : Fin n) = i from Fin.ext (by simp; omega)]
        -- an inner walk: by the induction hypothesis if the basepoint is still interior,
        -- and by `s3ZigFree_near_extreme` if it is not
        have hinner : ∃ ts : List ℤ, IsZigFree L' H' ts ∧
            FoldsOnto (armG (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 ∧
            FoldsOnto (armT (fun j : Fin (b - a + 1) => ρ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩) (zigWalk ts).1 (zigWalk ts).2 := by
          by_cases hint : L' + 3 ≤ ρ i ∧ ρ i ≤ H' - 3
          · refine ih (b - a + 1) _ (fun j : Fin (b - a + 1) => σ ⟨a + j.val, by omega⟩)
              ⟨i.val - a, by omega⟩ H' L' (by omega) hcr' hLb' hHb' (by omega) heL' heH'
              ?_ ?_
            · show L' + 3 ≤ ρ ⟨a + (i.val - a), _⟩
              rw [hbase]; exact hint.1
            · show ρ (⟨a + (i.val - a), _⟩ : Fin n) ≤ H' - 3
              rw [hbase]; exact hint.2
          · refine s3ZigFree_near_extreme _ ⟨i.val - a, by omega⟩ H' L' hcr'.isLip hLb' hHb'
              (by omega) ?_
            have h1 : L' ≤ ρ i := by
              have := hLb' ⟨i.val - a, by omega⟩
              rwa [hbase] at this
            have h2 : ρ i ≤ H' := by
              have := hHb' ⟨i.val - a, by omega⟩
              rwa [hbase] at this
            show ρ (⟨a + (i.val - a), _⟩ : Fin n) ≤ L' + 2 ∨
              H' - 2 ≤ ρ (⟨a + (i.val - a), _⟩ : Fin n)
            rw [hbase]
            omega
        obtain ⟨ts, hzf, hG, hT⟩ := hinner
        obtain ⟨x, y, hmem, hfG, hfT⟩ := hevery ts hzf hG hT
        exact ⟨ts ++ [x, y], hmem, hfG, hfT⟩
  intro n ρ σ i H L hcr hLb hHb hLH heL heH hlo hhi
  exact key (H - L).toNat n ρ σ i H L le_rfl hcr hLb hHb hLH heL heH hlo hhi

/-- **`ExtendStepSome`.** The weak form, which the census does support at every interior
basepoint of `bing 0 n` for `n = 6 … 12`: *some* member of some inner band's family folds both
inner arms and extends to a member of the outer family folding both whole arms. It implies
`S3ZigFreeInterior` outright, but it carries no induction: an induction hypothesis returns a
walk and gives no control over which, which is why the commission states the "every" form. -/
def ExtendStepSome : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 6 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∃ (a b : ℕ) (_hai : a ≤ i.val) (_hib : i.val ≤ b) (_hbn : b < n) (L' H' : ℤ)
      (ts : List ℤ) (x y : ℤ),
      IsInnerTrim ρ i L H a b L' H' ∧ IsZigFree L' H' ts ∧
        IsZigFree L H (ts ++ [x, y]) ∧
        FoldsOnto (armG ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2 ∧
        FoldsOnto (armT ρ i) (zigWalk (ts ++ [x, y])).1 (zigWalk (ts ++ [x, y])).2

theorem s3ZigFreeInterior_of_extendStepSome (h : ExtendStepSome) : S3ZigFreeInterior := by
  intro n ρ σ i H L hcr hLb hHb _ heL heH hlo hhi
  have h6 : L + 6 ≤ H := by omega
  obtain ⟨a, b, -, -, -, L', H', ts, x, y, -, -, hmem, hfG, hfT⟩ :=
    h n ρ σ i H L hcr hLb hHb h6 heL heH hlo hhi
  exact ⟨ts ++ [x, y], hmem, hfG, hfT⟩

/-! ## The timing obstruction

Why the strong form fails. The walk through `ts ++ l` runs through the targets of `ts` first,
and if those are all at least `L + 2` its centres stay at least `L + 2` for the whole of that
prefix. A fold pins the token to time `0` and moves it by at most one time per link, so an arm
that is at level `L` at index `d` cannot be folded unless `d` is at least the length of the
prefix. The witness of the census is sharper still: the extension `[2, 4, 2, 5, 1]` reaches a
centre `≤ 1` only at its last time, eleven, while the backward arm at basepoint 5 of `bing 0 6`
is at level `0` at index five.
-/

/-- **A fold cannot reach a level the walk has not come near.** If the arm is at level `≤ v` at
index `d` while every centre up to time `d` is at least `v + 2`, there is no fold: the token
stands at a time at most `d`, and no such time is near enough. -/
theorem no_fold_of_low_early {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ} {v : ℤ} {d : Fin m}
    (hd : f d ≤ v) (hc : ∀ u, u ≤ d.val → v + 2 ≤ c u) :
    ¬ FoldsOnto f len c := by
  rintro ⟨β, -, hlip, hz, hcl⟩
  have hβ : ∀ (k : ℕ) (hk : k < m), β ⟨k, hk⟩ ≤ k := by
    intro k
    induction k with
    | zero => intro hk; rw [hz ⟨0, hk⟩ rfl]
    | succ k ih =>
        intro hk
        have hk' : k < m := by omega
        have hstep := hlip ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl
        rw [abs_le] at hstep
        have := ih hk'
        omega
  have h1 : β d ≤ d.val := by
    have := hβ d.val d.isLt
    simpa using this
  have h2 := hcl d
  have h3 := hc (β d) h1
  rw [abs_le] at h2
  omega

private theorem lastD_cons : ∀ (rest : List ℤ) (t a : ℤ),
    (t :: rest).getLast?.getD a = rest.getLast?.getD t
  | [], _, _ => by simp
  | u :: us, t, a => by
      rw [List.getLast?_cons_cons, lastD_cons us u a, lastD_cons us u t]

/-- Walking through `r ++ l` is walking through `r` and then, from where that left off,
through `l`. -/
theorem zigTail_append (a : ℤ) (r l : List ℤ) :
    zigTail a (r ++ l) = zigTail a r ++ zigTail (r.getLastD a) l := by
  induction r generalizing a with
  | nil => simp [zigTail]
  | cons t rest ih => simp [zigTail, ih, lastD_cons]

/-- The levels of the walk through `ts ++ l` begin with the levels of the walk through `ts`. -/
theorem zigLevels_append (ts l : List ℤ) (hne : ts ≠ []) :
    zigLevels (ts ++ l) = zigLevels ts ++ zigTail (ts.getLastD 0) l := by
  cases ts with
  | nil => simp at hne
  | cons t rest => simp [zigLevels, zigTail_append, lastD_cons]

/-- **The extension does not disturb the walk it extends**: at every time of the inner walk the
extended walk has the same centre. -/
theorem zigWalk_prefix (ts l : List ℤ) (u : ℕ) (hu : u < (zigWalk ts).1) :
    (zigWalk (ts ++ l)).2 u = (zigWalk ts).2 u := by
  cases ts with
  | nil => simp [zigWalk, zigLevels] at hu
  | cons t rest =>
      have hne : (t :: rest) ≠ [] := by simp
      simp only [zigWalk] at hu ⊢
      rw [zigLevels_append _ _ hne, List.getD_append _ _ _ u hu]

/-- **No fold of an arm that dives early.** If every target of `ts` is at least `L + 2`, an arm
that is at level `≤ L` at index `d` cannot fold onto the walk through `ts ++ l` unless `d` is at
least the length of the walk through `ts`. The inner member of a trim whose band lies inside
`[L+1, H−1]` has all its targets at least `L + 2`, so this is exactly the obstruction the
appended legs must overcome. -/
theorem no_fold_of_early_low {L H : ℤ} {ts l : List ℤ} {m : ℕ} {f : Fin m → ℤ}
    (hb : ∀ t ∈ ts, L + 2 ≤ t ∧ t ≤ H) {d : Fin m} (hd : f d ≤ L)
    (hfold : FoldsOnto f (zigWalk (ts ++ l)).1 (zigWalk (ts ++ l)).2) :
    (zigWalk ts).1 ≤ d.val := by
  by_contra hcon
  refine no_fold_of_low_early (v := L) hd (fun u hu => ?_) hfold
  have hlt : u < (zigWalk ts).1 := by omega
  rw [zigWalk_prefix ts l u hlt]
  have hval : (zigWalk ts).2 u = (zigLevels ts)[u]'hlt := by
    simp [zigWalk, List.getElem?_eq_getElem hlt]
  rw [hval]
  exact (zigLevels_bounds hb _ (List.getElem_mem _)).1

/-- The backward arm of `bing 0 6` at basepoint 5: five links down to the bottom level. -/
def arm5 : Fin 6 → ℤ := ![3, 2, 1, 2, 1, 0]

/-- **The witness of the census, in Lean.** The census finds that the member `[2, 4, 2]` of the
free family of the band `[1, 5]` folds both arms of the stretch `[1, 69]` of `bing 0 6` at
basepoint 5, while its extension `[2, 4, 2, 5, 1]` does not fold both whole arms there. This is
the half that is a theorem: the extension does not fold the backward arm, which is at level `0`
at index five while the extension's centres are at least `2` up to time five — it reaches a
centre near the bottom only at its last time, eleven. -/
theorem bing6_arm_not_folded :
    ¬ FoldsOnto arm5 (zigWalk [2, 4, 2, 5, 1]).1 (zigWalk [2, 4, 2, 5, 1]).2 := by
  have hlev : zigLevels [2, 4, 2, 5, 1] = [2, 3, 4, 3, 2, 3, 4, 5, 4, 3, 2, 1] := by
    simp [zigLevels, zigTail, stepRun]
  refine no_fold_of_low_early (v := 0) (d := ⟨5, by omega⟩) (by decide) ?_
  intro u hu
  simp only [zigWalk, hlev]
  simp only at hu
  interval_cases u <;> decide

/-- `[2, 4, 2, 5, 1]` is a member of the free family of `[0, 6]`, as
`isZigFree_append_outer'` promises: it is the fold, and not the family, that fails. -/
theorem isZigFree_2425_1 : IsZigFree 0 6 [2, 4, 2, 5, 1] := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · intro j hj
    have h3 : j < 3 := by simp at hj; omega
    interval_cases j <;> decide
  · intro j _ hj
    have h3 : j < 3 := by simp at hj; omega
    interval_cases j <;> decide

-- Commented-out statement `extendStep` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
