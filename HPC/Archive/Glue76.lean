import HPC.Fold.Target76

/-!
# Gluing through the extension law, and a decision procedure for its failure

Batch 76 §2.2 asks, at a witness `(L', H', w', e)` of `ExtendsSubBand` (`HPC/Fold/Target76.lean`),
whether each arm's fold onto the extended walk `w` can be *glued* from a fold of the arm truncated
at its first exit from `[L', H']` onto `w'` and a fold of the rest of the arm onto `w` — the step
`foldsFrom_split` (`HPC/Fold/Span.lean`) performs. This file states that question exactly and
decides its failure.

* `SuffixGlues f s len' c' len c` — the arm's first `s + 1` entries fold onto `(len', c')`,
  arriving at some time `u` at the index `s`, and the arm from the index `s` on folds onto
  `(len, c)` from `u` (`FoldsFrom`). Any fold of the prefix, any arrival time.
* `GluesAtFirstExit f L' H' s e ts` — `SuffixGlues` at the last index inside `[L', H']`, with
  `w' = walkList s ts` and `w = walkList s (ts ++ [e])`: §2.2's question on one arm.
* `CappedFold f len c cap s` — a fold of the whole arm onto `(len, c)` whose itinerary stays below
  the time `cap` at the indices `0 … s`; `cappedB` is its dynamic program (`reachCap`).
* `cappedFold_of_suffixGlues` — if `(len, c)` extends `(len', c')`, a gluing is a capped fold,
  with the cap `len'` — and so `not_gluesAtFirstExit_of_cappedB`: a *false* verdict of `cappedB`
  refutes the gluing, for every fold of the truncated arm and every arrival time at once.
* `walkList_append_of_lt`, `walkLen_le_append` — `w` extends `w'`.
* `foldsOnto_of_gluesAtFirstExit` — a gluing is a fold of the whole arm onto `w` (sanity: the
  notion glues what it claims to).

Only the soundness direction of `cappedB` is proved: it is all a refutation needs.
-/

namespace HPC.Fold

/-! ## `w` extends `w'` -/

/-- **Appending a target does not move the earlier times of the walk.** -/
theorem walkList_append_of_lt (e : ℤ) :
    ∀ (s : ℤ) (ts : List ℤ) (p : ℕ), p < walkLen s ts →
      walkList s (ts ++ [e]) p = walkList s ts p := by
  intro s ts
  induction ts generalizing s with
  | nil =>
    intro p hp
    simp only [walkLen] at hp
    have hp0 : p = 0 := by omega
    subst hp0
    rw [List.nil_append, walkList, walkList, walkList]
    split_ifs <;> push_cast <;> omega
  | cons t ts ih =>
    intro p hp
    simp only [walkLen] at hp
    rw [List.cons_append, walkList, walkList]
    by_cases h : p < (t - s).natAbs
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact ih t _ (by omega)

/-- **Appending a target does not shorten the walk.** -/
theorem walkLen_le_append (e : ℤ) :
    ∀ (s : ℤ) (ts : List ℤ), walkLen s ts ≤ walkLen s (ts ++ [e]) := by
  intro s ts
  induction ts generalizing s with
  | nil => simp [walkLen]
  | cons t ts ih => simp only [List.cons_append, walkLen]; have := ih t; omega

/-! ## Gluing -/

/-- **`SuffixGlues f s len' c' len c`** — the arm `f` is glued at the index `s`: its entries
`0 … s` fold onto `(len', c')` (from time `0`), arriving at a time `u` at the index `s`, and the arm
from the index `s` on folds onto `(len, c)` from `u`. These are the two hypotheses of
`foldsFrom_split`, the prefix read on `(len', c')`. -/
def SuffixGlues {m : ℕ} (f : Fin m → ℤ) (s : ℕ) (len' : ℕ) (c' : ℕ → ℤ) (len : ℕ)
    (c : ℕ → ℤ) : Prop :=
  ∃ (hs : s < m) (u : ℕ),
    (∃ β : Fin (s + 1) → ℕ, (∀ j, β j < len') ∧
      (∀ j j' : Fin (s + 1), j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
      (∀ j : Fin (s + 1), j.val = 0 → β j = 0) ∧
      (∀ j : Fin (s + 1), j.val = s → β j = u) ∧
      ∀ j : Fin (s + 1), |f ⟨j.val, by omega⟩ - c' (β j)| ≤ 1) ∧
    FoldsFrom (fun j : Fin (m - s) => f ⟨s + j.val, by omega⟩) len c u

/-- **`GluesAtFirstExit f L' H' s e ts`** — batch 76 §2.2's question on one arm: the arm is glued
at the last index inside `[L', H']` (one before `bandPrefixLen`, the first exit), the prefix — the
truncated arm `truncArm f L' H'` — folded onto `w' = walkList s ts`, the rest onto
`w = walkList s (ts ++ [e])` from the prefix's arrival time. When the arm never leaves the band the
index is the arm's last, and the rest is the last entry alone. -/
def GluesAtFirstExit {m : ℕ} (f : Fin m → ℤ) (L' H' s e : ℤ) (ts : List ℤ) : Prop :=
  SuffixGlues f (bandPrefixLen (armSeq f) m L' H' - 1) (walkLen s ts) (walkList s ts)
    (walkLen s (ts ++ [e])) (walkList s (ts ++ [e]))

/-- **`CappedFold f len c cap s`** — a fold of the whole arm onto `(len, c)` whose itinerary is
below the time `cap` at every index `j ≤ s`. -/
def CappedFold {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (cap s : ℕ) : Prop :=
  ∃ β : Fin m → ℕ, (∀ j, β j < len) ∧
    (∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
    (∀ j : Fin m, j.val = 0 → β j = 0) ∧
    (∀ j, |f j - c (β j)| ≤ 1) ∧
    ∀ j : Fin m, j.val ≤ s → β j < cap

/-- **A gluing is a capped fold.** If `(len, c)` extends `(len', c')`, the two halves of a gluing
at the index `s` combine into one fold of the arm onto `(len, c)` that stays below `len'` up to
the index `s`. -/
theorem cappedFold_of_suffixGlues {m : ℕ} (f : Fin m → ℤ) (s len' : ℕ) (c' : ℕ → ℤ) (len : ℕ)
    (c : ℕ → ℤ) (hle : len' ≤ len) (hagree : ∀ p, p < len' → c p = c' p)
    (h : SuffixGlues f s len' c' len c) : CappedFold f len c len' s := by
  classical
  obtain ⟨hs, u, ⟨βp, hplt, hplip, hp0, hps, hpw⟩, ⟨βs, hslt, hslip, hs0, hsw⟩⟩ := h
  have hz : βs ⟨0, by omega⟩ = u := hs0 _ rfl
  refine ⟨fun j => if h : j.val ≤ s then βp ⟨j.val, by omega⟩
      else βs ⟨j.val - s, by have := j.isLt; omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val ≤ s
    · simp only [dif_pos hj]; exact lt_of_lt_of_le (hplt _) hle
    · simp only [dif_neg hj]; exact hslt _
  · intro j j' hjj'
    have hjm := j.isLt
    have hj'm := j'.isLt
    by_cases hj' : j'.val ≤ s
    · have hj : j.val ≤ s := by omega
      simp only [dif_pos hj, dif_pos hj']
      exact hplip ⟨j.val, by omega⟩ ⟨j'.val, by omega⟩ (by simpa using hjj')
    · by_cases hj : j.val ≤ s
      · simp only [dif_pos hj, dif_neg hj', hps ⟨j.val, by omega⟩ (show j.val = s by omega)]
        have := hslip ⟨0, by omega⟩ ⟨j'.val - s, by omega⟩ (by simp; omega)
        rw [hz] at this
        simpa using this
      · simp only [dif_neg hj, dif_neg hj']
        exact hslip ⟨j.val - s, by omega⟩ ⟨j'.val - s, by omega⟩ (by simp; omega)
  · intro j hj
    simp only [dif_pos (show j.val ≤ s by omega)]
    exact hp0 _ hj
  · intro j
    have hjm := j.isLt
    by_cases hj : j.val ≤ s
    · simp only [dif_pos hj]
      have := hpw ⟨j.val, by omega⟩
      rw [hagree _ (hplt _)]
      simpa using this
    · simp only [dif_neg hj]
      have := hsw ⟨j.val - s, by omega⟩
      simp only at this
      have he : (⟨s + (j.val - s), by omega⟩ : Fin m) = j := Fin.ext (by simp; omega)
      rw [he] at this
      exact this
  · intro j hj
    simp only [dif_pos hj]
    exact hplt _

/-- A capped fold is a fold. -/
theorem foldsOnto_of_cappedFold {m : ℕ} {f : Fin m → ℤ} {len : ℕ} {c : ℕ → ℤ} {cap s : ℕ}
    (h : CappedFold f len c cap s) : FoldsOnto f len c := by
  obtain ⟨β, h1, h2, h3, h4, -⟩ := h
  exact ⟨β, h1, h2, h3, h4⟩

/-- **A gluing at the first exit is a fold of the whole arm onto `w`.** -/
theorem foldsOnto_of_gluesAtFirstExit {m : ℕ} {f : Fin m → ℤ} {L' H' s e : ℤ} {ts : List ℤ}
    (h : GluesAtFirstExit f L' H' s e ts) :
    FoldsOnto f (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) :=
  foldsOnto_of_cappedFold (cappedFold_of_suffixGlues f _ _ _ _ _ (walkLen_le_append e s ts)
    (fun p hp => walkList_append_of_lt e s ts p hp) h)

/-! ## The capped dynamic program -/

/-- The walk positions a capped partial itinerary can occupy at the step `k`: `foldReach` with
positions at or above `cap` forbidden at the steps `0 … s`. -/
def reachCap (g : ℕ → ℤ) (len : ℕ) (c : ℕ → ℤ) (cap s : ℕ) : ℕ → List ℕ
  | 0 => if 0 < len ∧ 0 < cap ∧ |g 0 - c 0| ≤ 1 then [0] else []
  | (k + 1) =>
      (List.range len).filter fun p =>
        decide (|g (k + 1) - c p| ≤ 1) && decide (s < k + 1 ∨ p < cap) &&
          (reachCap g len c cap s k).any fun q => decide (p ≤ q + 1 ∧ q ≤ p + 1)

/-- **Soundness of the capped program.** A partial itinerary over `0 … k` that respects the cap
ends at a position the program lists. -/
theorem mem_reachCap_of_partItin (g : ℕ → ℤ) (len : ℕ) (c : ℕ → ℤ) (cap s : ℕ) :
    ∀ (k : ℕ) (b : ℕ → ℕ), PartItin g len c k b → (∀ j, j ≤ k → j ≤ s → b j < cap) →
      b k ∈ reachCap g len c cap s k := by
  intro k
  induction k with
  | zero =>
    rintro b ⟨hb0, hblt, -, hbval⟩ hcap
    have h1 : 0 < len := by have := hblt 0 le_rfl; omega
    have h2 : 0 < cap := by have := hcap 0 le_rfl (Nat.zero_le _); omega
    have h3 : |g 0 - c 0| ≤ 1 := by have := hbval 0 le_rfl; rwa [hb0] at this
    rw [reachCap, if_pos ⟨h1, h2, h3⟩, hb0]
    exact List.mem_singleton_self 0
  | succ k ih =>
    rintro b ⟨hb0, hblt, hbst, hbval⟩ hcap
    rw [reachCap, List.mem_filter]
    refine ⟨List.mem_range.2 (hblt (k + 1) le_rfl), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨⟨hbval (k + 1) le_rfl, ?_⟩, b k,
      ih b ⟨hb0, fun j hj => hblt j (by omega), fun j hj => hbst j (by omega),
        fun j hj => hbval j (by omega)⟩ (fun j hj hjs => hcap j (by omega) hjs), ?_⟩
    · by_cases hks : s < k + 1
      · exact Or.inl hks
      · exact Or.inr (hcap (k + 1) le_rfl (by omega))
    · have hstep := hbst k (by omega)
      rw [abs_le] at hstep
      refine ⟨?_, ?_⟩ <;> omega

/-- **The verdict of the capped program.** -/
def cappedB {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (cap s : ℕ) : Bool :=
  match m with
  | 0 => true
  | (k + 1) => decide (reachCap (armSeq f) len c cap s k ≠ [])

/-- **A capped fold has a true verdict.** -/
theorem cappedB_of_cappedFold {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (cap s : ℕ)
    (h : CappedFold f len c cap s) : cappedB f len c cap s = true := by
  cases m with
  | zero => rfl
  | succ k =>
    obtain ⟨β, hlt, hlip, h0, hval, hcap⟩ := h
    simp only [cappedB, decide_eq_true_eq]
    let b : ℕ → ℕ := fun j => if hj : j < k + 1 then β ⟨j, hj⟩ else 0
    have hbv : ∀ j (hj : j < k + 1), b j = β ⟨j, hj⟩ := fun j hj => dif_pos hj
    refine List.ne_nil_of_mem (a := b k) (mem_reachCap_of_partItin (armSeq f) len c cap s k b
      ⟨?_, ?_, ?_, ?_⟩ ?_)
    · rw [hbv 0 (by omega)]
      exact h0 ⟨0, by omega⟩ rfl
    · intro j hj
      rw [hbv j (by omega)]
      exact hlt _
    · intro j hj
      rw [hbv j (by omega), hbv (j + 1) (by omega)]
      exact hlip ⟨j, by omega⟩ ⟨j + 1, by omega⟩ rfl
    · intro j hj
      rw [hbv j (by omega)]
      have := hval ⟨j, by omega⟩
      simpa [armSeq, show j < k + 1 by omega] using this
    · intro j hj hjs
      rw [hbv j (by omega)]
      exact hcap ⟨j, by omega⟩ hjs

/-- **A capped fold is refuted by an empty step of the capped program.** If the capped program has
no position left at some step `q` inside the arm, the arm has no capped fold: an itinerary of the
whole arm would be one of its first `q + 1` entries. -/
theorem not_cappedFold_of_reachCap_nil {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ)
    (cap s q : ℕ) (hq : q < m) (h : reachCap (armSeq f) len c cap s q = []) :
    ¬ CappedFold f len c cap s := by
  rintro ⟨β, hlt, hlip, h0, hval, hcap⟩
  let b : ℕ → ℕ := fun j => if hj : j < m then β ⟨j, hj⟩ else 0
  have hbv : ∀ j (hj : j < m), b j = β ⟨j, hj⟩ := fun j hj => dif_pos hj
  have hmem := mem_reachCap_of_partItin (armSeq f) len c cap s q b ⟨?_, ?_, ?_, ?_⟩ ?_
  · rw [h] at hmem
    exact List.not_mem_nil hmem
  · rw [hbv 0 (by omega)]
    exact h0 ⟨0, by omega⟩ rfl
  · intro j hj
    rw [hbv j (by omega)]
    exact hlt _
  · intro j hj
    rw [hbv j (by omega), hbv (j + 1) (by omega)]
    exact hlip ⟨j, by omega⟩ ⟨j + 1, by omega⟩ rfl
  · intro j hj
    rw [hbv j (by omega)]
    have := hval ⟨j, by omega⟩
    simpa [armSeq, show j < m by omega] using this
  · intro j hj hjs
    rw [hbv j (by omega)]
    exact hcap ⟨j, by omega⟩ hjs

/-- **Refuting a gluing by an empty step of the capped program**, run on the arm and `w` with the
cap `len w'` up to the last index inside the band: no fold of the truncated arm onto `w'`, with any
arrival time, glues to a fold of the rest onto `w`. Only the first `q + 1` entries of the arm are
read. -/
theorem not_gluesAtFirstExit_of_reachCap_nil {m : ℕ} (f : Fin m → ℤ) (L' H' s e : ℤ)
    (ts : List ℤ) (q : ℕ) (hq : q < m)
    (h : reachCap (armSeq f) (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) (walkLen s ts)
      (bandPrefixLen (armSeq f) m L' H' - 1) q = []) :
    ¬ GluesAtFirstExit f L' H' s e ts := fun hg =>
  not_cappedFold_of_reachCap_nil f _ _ _ _ q hq h (cappedFold_of_suffixGlues f _ _ _ _ _
    (walkLen_le_append e s ts) (fun p hp => walkList_append_of_lt e s ts p hp) hg)

/-- **Refuting a gluing by the capped program.** If the capped program, run on the whole arm and
`w` with the cap `len w'` up to the last index inside the band, finds no itinerary, then no fold of
the truncated arm onto `w'`, with any arrival time, glues to a fold of the rest onto `w`. -/
theorem not_gluesAtFirstExit_of_cappedB {m : ℕ} (f : Fin m → ℤ) (L' H' s e : ℤ) (ts : List ℤ)
    (h : cappedB f (walkLen s (ts ++ [e])) (walkList s (ts ++ [e])) (walkLen s ts)
      (bandPrefixLen (armSeq f) m L' H' - 1) = false) :
    ¬ GluesAtFirstExit f L' H' s e ts := by
  intro hg
  have := cappedB_of_cappedFold _ _ _ _ _ (cappedFold_of_suffixGlues f _ _ _ _ _
    (walkLen_le_append e s ts) (fun p hp => walkList_append_of_lt e s ts p hp) hg)
  rw [h] at this
  exact Bool.false_ne_true this

end HPC.Fold
