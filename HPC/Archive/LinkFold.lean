import HPC.Fold.Faithful

/-!
# Folding the upper ends instead of the point sequence

`exists_blocks_first_of_folds` (`HPC/Fold/Itinerary.lean`) is the bridge from a fold to Bing 1948
Theorem 3: both arms of the **point** sequence `ρ = minIdx` folding onto one walk give a block
consolidation with every block inside **three** consecutive links of the coarse chain. The
batch-47 commission asks whether the fold may instead be read on `σ = maxIdx`, or on the whole
link `[ρ t, σ t]`.

**It may, and it costs one link.** A walk that stays within one of `σ` at each time stays within
*two* of `ρ`, so the minimal indices inside one block of the consolidation can spread over four
consecutive links, not three: `exists_blocks_first_of_folds_max` below is the four-link form, and
it is proved from the same schedule machinery, with the window `4` in place of `3`. The same
bound, and no better, is what a fold reading the whole link gives, since a walk within one of some
level of `[ρ t, σ t]` is within two of `ρ t`.

Three consecutive links is the conclusion of Theorem 3, so the extra link is not free: the route
through `σ` proves a weaker statement. Where the pair is thin the two readings coincide
(`foldsOnto_of_thin`), which is another way of saying that the one-level gap between `ρ` and `σ`
is exactly the gap between the two conclusions.

Together with `HPC/Fold/Raise.lean` this answers the first two questions of the batch-47
commission: the raise of a faithful pair need not be faithful, and even where it is, the fold it
carries lands one link short.
-/

namespace HPC.Fold

open HPC.Chain

/-- A thin pair folds the same way whichever end is read. -/
theorem foldsOnto_of_thin {m : ℕ} {f g : Fin m → ℤ} (h : ∀ t, f t = g t) (len : ℕ) (c : ℕ → ℤ)
    (hf : FoldsOnto f len c) : FoldsOnto g len c := by
  have : f = g := funext h
  rwa [this] at hf

/-- **Theorem 3 from a fold of the upper ends, in four-link form.** If both arms of the sequence
of *greatest* indices `σ = maxIdx` fold onto one walk, and each link's two indices differ by at
most one — which is what the faithful model asks of a link — then `E` has a block consolidation
with `d_i` in the first block and every block inside **four** consecutive links of `D`.

This is `exists_blocks_first_of_folds` with `σ` in place of `ρ` and one more link in the window:
a walk within one of `σ t` is within two of `ρ t`, so two links of one block have minimal indices
at most three apart. -/
theorem exists_blocks_first_of_folds_max {X : Type*} [MetricSpace X] {n m : ℕ}
    {E : Chain X m} {D : Chain X n} (h : E.Refines D)
    (hwidth : ∀ t, (h.maxIdx t : ℤ) ≤ (h.minIdx t : ℤ) + 1)
    (i : Fin m) (len : ℕ) (c : ℕ → ℤ)
    (hG : FoldsOnto (armG (fun t => (h.maxIdx t : ℤ)) i) len c)
    (hT : FoldsOnto (armT (fun t => (h.maxIdx t : ℤ)) i) len c) :
    ∃ (p : ℕ) (β' : Fin m → Fin p) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 4 := by
  obtain ⟨β, hβlt, hβlip, hβi, hβw⟩ :=
    exists_schedule_of_folds (fun t => (h.maxIdx t : ℤ)) i len c hG hT
  have hsched : IsSchedule β :=
    ⟨fun t t' htt' => by have := hβlip t t' htt'; rw [abs_le] at this; omega, ⟨i, hβi⟩⟩
  have hmin_le_max : ∀ t, (h.minIdx t : ℤ) ≤ (h.maxIdx t : ℤ) := by
    intro t
    exact_mod_cast Fin.le_def.mp (minIdx_le h t (maxIdx_subset h t))
  obtain ⟨p, β', hβ', hval, hblk⟩ :=
    exists_blocks_of_schedule h hsched 4 (by norm_num) (fun t t' hββ => by
      have h1 := hβw t
      have h2 := hβw t'
      rw [abs_le] at h1 h2
      rw [hββ] at h1
      have h3 := hwidth t
      have h4 := hwidth t'
      have h5 := hmin_le_max t
      have h6 := hmin_le_max t'
      omega)
  exact ⟨p, β', hβ', by rw [hval i, hβi], hblk⟩

end HPC.Fold
