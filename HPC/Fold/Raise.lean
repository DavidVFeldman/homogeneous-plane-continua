import HPC.Fold.Shave

/-!
# Raising a link: not every faithful pair is a shaving of a thin one

`HPC/Fold/Shave.lean` lowers `ρ` at a strict peak and keeps the pair faithful, so the general
model is strictly wider than its thin form. This file asks the converse question: is every
faithful pair obtained that way — is the **raise** `(σ, σ)`, in which every link is lifted to the
greatest level it meets, again a faithful pair?

**It is not.** The six-term pair

```
ρ = 0 1 1 1 2 2
σ = 0 1 2 2 2 3
```

is faithful (`raise_faithful`), and its raise `σ = 0 1 2 2 2 3`, read as a thin pair, is not
(`not_isCrookedIvF_raise`): the clause fires between the link `0`, which meets the level `0`, and
the link `5`, which meets the level `3`, and asks for a time at `2` followed by a later time at
`1`; the sequence `σ` stands at `2` at the indices `2, 3, 4` and never returns to `1`. In the
original pair the clause is satisfied because the links `2` and `3` both meet `1` as well as `2` —
*meeting* a level and *standing* at it are the two readings whose difference is the whole of the
one-level gap of the general model.

Since shaving leaves `σ` alone, a pair that is a shaving of a thin sequence has that thin sequence
for its `σ`; so the pair above is not a shaving of any thin one (`not_isShavingOfThin_example`),
and no route through the thin results of `HPC/Fold/ThinSpan9.lean` can reach the general model by
raising.

This is the answer to the first question of the batch-47 commission, and it is a negative one:
it is not merely that the raise-then-fold route loses the fold, but that the raise leaves the
model. (That the *fold* does not transfer either is the separate observation of
`HPC/Fold/LinkFold.lean`.)

The counterexample is the least one there is: an exhaustive enumeration of the general model
(`census-batch47.c`) finds none of length five or less in the band `[0, 4]`, and 20 of length six,
of which this is one.
-/

namespace HPC.Fold

/-- The point sequence of a six-term faithful pair whose raise is not faithful. -/
def raiseRho : Fin 6 → ℤ := ![0, 1, 1, 1, 2, 2]

/-- Its upper ends: the links are `[0,0]`, `[1,1]`, `[1,2]`, `[1,2]`, `[2,2]`, `[2,3]`. -/
def raiseSig : Fin 6 → ℤ := ![0, 1, 2, 2, 2, 3]

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The pair is faithful. -/
theorem raise_faithful : IsCrookedIvF raiseRho raiseSig :=
  isCrookedIvF_of_check (by unfold IsCrookedIvFCheck ivEnd raiseRho raiseSig; decide)

/-- It is not thin: the links `2`, `3` and `5` are two levels wide. -/
theorem raise_not_thin : ¬ ∀ t, raiseSig t = raiseRho t := by
  intro h
  have := h 2
  simp [raiseRho, raiseSig] at this

/-- **The raise is not faithful.** Reading every link at the greatest level it meets turns the
faithful pair above into a thin sequence that fails the crookedness clause: between the index `0`,
which stands at `0`, and the index `5`, which stands at `3`, the clause asks for a time at `2`
followed by a later time at `1`, and after its first `2` the sequence never returns to `1`. -/
theorem not_isCrookedIvF_raise : ¬ IsCrookedIvF raiseSig raiseSig := by
  intro h
  obtain ⟨r, r', h1, h2, h3, hup, -⟩ :=
    h.crooked 0 5 (by decide) 0 3 ⟨0, by decide⟩ ⟨5, by decide⟩ (by decide)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hup (by decide)
  -- `σ r = 2` and `σ r' = 1` with `0 < r < r' < 5` is impossible
  have hrv : raiseSig r = 2 := le_antisymm hr1 hr2
  have hr'v : raiseSig r' = 1 := le_antisymm hr'1 hr'2
  have h2' : r.val < r'.val := h2
  fin_cases r <;> fin_cases r' <;> simp_all [raiseSig]

/-- **Being a shaving of a thin sequence.** Shaving lowers `ρ` at a strict peak and leaves `σ`
alone, so a pair that arises from a thin faithful sequence by any number of shavings has that
sequence for its `σ`, and its `ρ` is `σ` lowered by at most one at each link. This is the weakest
form of the property, and it is already too strong. -/
def IsShavingOfThin {n : ℕ} (ρ σ : Fin n → ℤ) : Prop :=
  IsCrookedIvF σ σ ∧ ∀ t, ρ t = σ t ∨ ρ t = σ t - 1

/-- A shaved pair, in the sense of `isCrookedIvF_shave`, is a shaving of a thin sequence when the
sequence it was shaved from was thin. -/
theorem isShavingOfThin_shave {n : ℕ} {τ ρ : Fin n → ℤ} (hcr : IsCrookedIvF τ τ) (j : Fin n)
    (hj : ρ j = τ j - 1) (hoth : ∀ u : Fin n, u ≠ j → ρ u = τ u) :
    IsShavingOfThin ρ τ :=
  ⟨hcr, fun t => by
    rcases eq_or_ne t j with rfl | ht
    · exact Or.inr hj
    · exact Or.inl (hoth t ht)⟩

/-- **The example is not a shaving of a thin sequence.** -/
theorem not_isShavingOfThin_example : ¬ IsShavingOfThin raiseRho raiseSig := fun h =>
  not_isCrookedIvF_raise h.1

/-- **Not every faithful pair is a shaving of a thin one.** The answer to the first question of
the batch-47 commission. -/
theorem exists_faithful_not_isShavingOfThin :
    ∃ (n : ℕ) (ρ σ : Fin n → ℤ), IsCrookedIvF ρ σ ∧ ¬ IsShavingOfThin ρ σ :=
  ⟨6, raiseRho, raiseSig, raise_faithful, not_isShavingOfThin_example⟩

end HPC.Fold
