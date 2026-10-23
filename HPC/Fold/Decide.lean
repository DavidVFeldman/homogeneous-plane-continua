import HPC.Fold.Itinerary

/-!
# `FoldsOnto` is decidable, and the decision is the census's dynamic program

Every census of this development decides a fold by the same dynamic program: keep the set of walk
positions an itinerary could occupy at the current step, and advance it one step at a time. Every
witness file of this development, on the other hand, exhibits an itinerary as a base-sixteen
numeral and lets the kernel check the three conditions of `FoldsOnto`. The two are not the same
instrument: the first can say *no* and the second cannot, and nothing so far connects them.

This file closes the gap. `foldReach` is the dynamic program, `foldsB` is its verdict, and

> **`foldsB_iff`.** `foldsB f len c = true ↔ FoldsOnto f len c`,

so the verdict is exactly the definition — in both directions, on any arm and any walk. Three
things follow.

* `FoldsOnto` is a **decidable** predicate of a concrete arm and walk (`decidableFoldsOnto`), so a
  fold, or the absence of one, can be settled by the kernel with no itinerary supplied by hand.
* A census verdict is auditable: the program the census runs is this one, and where the census says
  a pair folds or does not fold, the same question can be put to the kernel on the same object.
* Refutations no longer need a criterion. Before this file an arm could be shown *not* to fold only
  through a necessary condition (`HPC/Fold/Landmark.lean`); now `decide` does it.

The dynamic program is the standard one. `foldReach g len c k` is the list of positions `p` such
that some itinerary over the steps `0 … k` of the sequence `g` ends at `p`; the step from `k` to
`k+1` keeps the positions of the walk that serve `g (k+1)` and are within one of a position already
reachable. `PartItin` is the predicate it is proved to describe (`mem_foldReach`).
-/

namespace HPC.Fold

/-! ## The arm read as a `ℕ`-indexed sequence -/

/-- The arm as a sequence indexed by `ℕ`, zero outside its range. Only the values at indices
below `m` are ever used. -/
def armSeq {m : ℕ} (f : Fin m → ℤ) (j : ℕ) : ℤ := if h : j < m then f ⟨j, h⟩ else 0

@[simp] theorem armSeq_val {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : armSeq f j.val = f j := by
  simp [armSeq, j.isLt]

/-! ## The dynamic program -/

/-- The walk positions an itinerary can occupy at the step `k`. -/
def foldReach (g : ℕ → ℤ) (len : ℕ) (c : ℕ → ℤ) : ℕ → List ℕ
  | 0 => if 0 < len ∧ |g 0 - c 0| ≤ 1 then [0] else []
  | (k + 1) =>
      (List.range len).filter fun p =>
        decide (|g (k + 1) - c p| ≤ 1) &&
          (foldReach g len c k).any fun q => decide (p ≤ q + 1 ∧ q ≤ p + 1)

/-- **A partial itinerary** over the steps `0 … k`: it starts at the walk's first position, stays
inside the walk, moves by at most one position per step, and serves the sequence at every step. -/
def PartItin (g : ℕ → ℤ) (len : ℕ) (c : ℕ → ℤ) (k : ℕ) (b : ℕ → ℕ) : Prop :=
  b 0 = 0 ∧ (∀ j, j ≤ k → b j < len) ∧
    (∀ j, j < k → |(b (j + 1) : ℤ) - (b j : ℤ)| ≤ 1) ∧
    (∀ j, j ≤ k → |g j - c (b j)| ≤ 1)

/-- **What the dynamic program computes.** A position is in the list at the step `k` exactly when
some partial itinerary over `0 … k` ends there. -/
theorem mem_foldReach (g : ℕ → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    ∀ (k p : ℕ), p ∈ foldReach g len c k ↔ ∃ b : ℕ → ℕ, PartItin g len c k b ∧ b k = p := by
  intro k
  induction k with
  | zero =>
      intro p
      constructor
      · intro hp
        by_cases hc : 0 < len ∧ |g 0 - c 0| ≤ 1
        · rw [foldReach, if_pos hc] at hp
          have hp0 : p = 0 := by simpa using hp
          subst hp0
          refine ⟨fun _ => 0, ⟨rfl, fun j hj => hc.1, fun j hj => absurd hj (by omega),
            fun j hj => ?_⟩, rfl⟩
          have hj0 : j = 0 := Nat.le_zero.1 hj
          subst hj0
          exact hc.2
        · rw [foldReach, if_neg hc] at hp
          simp at hp
      · rintro ⟨b, ⟨hb0, hblt, -, hbval⟩, hbk⟩
        have h1 : 0 < len := by have := hblt 0 le_rfl; omega
        have h2 : |g 0 - c 0| ≤ 1 := by have := hbval 0 le_rfl; rwa [hb0] at this
        rw [foldReach, if_pos ⟨h1, h2⟩]
        simp [← hbk, hb0]
  | succ k ih =>
      intro p
      constructor
      · intro hp
        rw [foldReach, List.mem_filter] at hp
        obtain ⟨hpr, hcond⟩ := hp
        rw [List.mem_range] at hpr
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hcond
        obtain ⟨hval, q, hq, hstep⟩ := hcond
        obtain ⟨b, ⟨hb0, hblt, hbst, hbval⟩, hbk⟩ := (ih q).1 hq
        refine ⟨fun j => if j ≤ k then b j else p, ⟨by simp [hb0], ?_, ?_, ?_⟩, by simp⟩
        · intro j hj
          by_cases hjk : j ≤ k
          · simpa [hjk] using hblt j hjk
          · simpa [hjk] using hpr
        · intro j hj
          by_cases hjk : j + 1 ≤ k
          · have hjk' : j ≤ k := by omega
            simpa [hjk, hjk'] using hbst j (by omega)
          · have hje : j = k := by omega
            subst hje
            simp only [if_neg hjk, if_pos (le_refl j), hbk]
            rw [abs_le]
            omega
        · intro j hj
          by_cases hjk : j ≤ k
          · simpa [hjk] using hbval j hjk
          · have hje : j = k + 1 := by omega
            subst hje
            simpa [hjk] using hval
      · rintro ⟨b, ⟨hb0, hblt, hbst, hbval⟩, hbk⟩
        rw [foldReach, List.mem_filter]
        refine ⟨List.mem_range.2 (by simpa [hbk] using hblt (k + 1) le_rfl), ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        refine ⟨by simpa [hbk] using hbval (k + 1) le_rfl, b k,
          (ih (b k)).2 ⟨b, ⟨hb0, fun j hj => hblt j (by omega), fun j hj => hbst j (by omega),
            fun j hj => hbval j (by omega)⟩, rfl⟩, ?_⟩
        have hstep := hbst k (by omega)
        rw [abs_le] at hstep
        refine ⟨?_, ?_⟩ <;> omega

/-! ## The verdict -/

/-- **The census's verdict.** The arm folds onto the walk iff the dynamic program still has a
position at the last step. -/
def foldsB {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) : Bool :=
  match m with
  | 0 => true
  | (k + 1) => decide (foldReach (armSeq f) len c k ≠ [])

/-- **The verdict is the definition.** -/
theorem foldsB_iff {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    foldsB f len c = true ↔ FoldsOnto f len c := by
  cases m with
  | zero =>
      simp only [foldsB]
      exact ⟨fun _ => ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
        fun j => j.elim0⟩, fun _ => trivial⟩
  | succ k =>
      simp only [foldsB, decide_eq_true_eq]
      constructor
      · intro h
        obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
        obtain ⟨b, ⟨hb0, hblt, hbst, hbval⟩, -⟩ := (mem_foldReach (armSeq f) len c k p).1 hp
        refine ⟨fun j => b j.val, fun j => hblt j.val (by omega), ?_, ?_, ?_⟩
        · intro j j' hjj'
          show |((b j'.val : ℤ)) - ((b j.val : ℤ))| ≤ 1
          have hj' := j'.isLt
          rw [hjj']
          exact hbst j.val (by omega)
        · intro j hj
          show b j.val = 0
          rw [hj]
          exact hb0
        · intro j
          have := hbval j.val (by omega)
          rwa [armSeq_val] at this
      · rintro ⟨β, hlt, hst, hz, hval⟩
        set b : ℕ → ℕ := fun j => if h : j < k + 1 then β ⟨j, h⟩ else 0 with hb
        have hbv : ∀ (j : ℕ) (h : j < k + 1), b j = β ⟨j, h⟩ := by
          intro j h
          show (if h' : j < k + 1 then β ⟨j, h'⟩ else 0) = β ⟨j, h⟩
          rw [dif_pos h]
        refine List.ne_nil_of_mem (a := b k) ((mem_foldReach (armSeq f) len c k (b k)).2
          ⟨b, ⟨?_, ?_, ?_, ?_⟩, rfl⟩)
        · rw [hbv 0 (by omega)]
          exact hz ⟨0, by omega⟩ rfl
        · intro j hj
          rw [hbv j (by omega)]
          exact hlt ⟨j, by omega⟩
        · intro j hj
          rw [hbv j (by omega), hbv (j + 1) (by omega)]
          exact hst ⟨j, by omega⟩ ⟨j + 1, by omega⟩ rfl
        · intro j hj
          rw [hbv j (by omega)]
          have := hval ⟨j, by omega⟩
          rwa [← armSeq_val f ⟨j, by omega⟩] at this

/-- **`FoldsOnto` is decidable** on a concrete arm and walk. -/
instance decidableFoldsOnto {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    Decidable (FoldsOnto f len c) :=
  decidable_of_iff (foldsB f len c = true) (foldsB_iff f len c)

/-- A fold, from the verdict. -/
theorem foldsOnto_of_foldsB {m : ℕ} {f : Fin m → ℤ} {len : ℕ} {c : ℕ → ℤ}
    (h : foldsB f len c = true) : FoldsOnto f len c := (foldsB_iff f len c).1 h

/-- No fold, from the verdict. -/
theorem not_foldsOnto_of_foldsB {m : ℕ} {f : Fin m → ℤ} {len : ℕ} {c : ℕ → ℤ}
    (h : foldsB f len c = false) : ¬ FoldsOnto f len c := by
  rw [← foldsB_iff]
  simp [h]

end HPC.Fold
