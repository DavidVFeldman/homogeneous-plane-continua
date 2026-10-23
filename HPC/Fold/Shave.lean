import HPC.Fold.Faithful

/-!
# Shaving a peak: the general model is strictly wider than its thin form

A faithful pair `(ρ, σ)` records, for each link, the least and the greatest level it meets:
`ρ t ≤ σ t ≤ ρ t + 1`. The **thin** form of the model is `σ = ρ`, every link a single level, and
`HPC/Fold/ThinSpan9.lean` proves the whole of span nine there. This file answers the standing
question of batches 44 and 45 — *does the thin form lose pairs?* — in the affirmative, and by an
operation that changes only one link.

**Shaving.** Let `ρ` be a faithful sequence and let `j` be a strict local maximum: both its
neighbours stand at `ρ j - 1`. Lower `ρ` at `j` by one and leave `σ` where it was. The link at `j`
now runs from `ρ j - 1` to `ρ j`: it still *meets* the peak level, but the point sequence `ρ` no
longer stands there. `isCrookedIvF_shave` proves that the result is again a faithful crooked pair.

The two hypotheses are exactly what is needed and no more: the link being shaved must itself be
thin (`σ j = ρ j`, else the shaved link would be two levels wide), and both its neighbours must
lie strictly below it (else adjacency would fail). Nothing else about the sequence is used.

**Why it matters.** Every walk criterion of this development reads the *point* sequence `ρ`, while
every application of the crookedness clause returns a *link* meeting a level. On a thin sequence
the two agree; shaving is precisely the operation that separates them, and it separates them at
the one level at which the span-nine argument of `HPC/Fold/MixedThin.lean` works. Applied to
Bing's chain `bing 0 9` it refutes both work items of `HPC/Fold/Mixed.lean`
(`HPC/Fold/Bing9Shave.lean`, `HPC/Fold/Bing9ShaveWitness.lean`).
-/

namespace HPC.Fold

/-- A neighbour of `j`, when the sequence has at least two links. -/
private def nbr {n : ℕ} (j : Fin n) (h : 1 < n) : Fin n :=
  if hj : j.val + 1 < n then ⟨j.val + 1, hj⟩ else ⟨j.val - 1, by omega⟩

private theorem nbr_dist {n : ℕ} (j : Fin n) (h : 1 < n) :
    ((nbr j h : ℤ) - (j : ℤ)).natAbs = 1 := by
  have hj := j.isLt
  unfold nbr
  split_ifs with hc
  · simp
  · simp
    omega

/-- **Shaving a peak keeps the pair faithful.** If `(ρ, σ)` is faithful crooked, the link `j` is
thin, and both neighbours of `j` stand at `ρ j - 1` or below, then lowering `ρ` at `j` by one —
leaving `σ` alone, so that the link still meets the level `ρ j` — gives a faithful crooked pair
again.

The clause transfers because a level met by the shaved link near an index `s` is met, in the
original pair, by a link near `s` as well: the new level `ρ j - 1` is the level of the neighbours
of `j`. In the other direction the conclusion only gets easier: the shaved link meets everything
it met before. -/
theorem isCrookedIvF_shave {n : ℕ} {ρ σ ρ' : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (j : Fin n)
    (hσj : σ j = ρ j)
    (hnb : ∀ u : Fin n, ((u : ℤ) - (j : ℤ)).natAbs = 1 → ρ u ≤ ρ j - 1)
    (hj : ρ' j = ρ j - 1) (hoth : ∀ u : Fin n, u ≠ j → ρ' u = ρ u) :
    IsCrookedIvF ρ' σ := by
  -- `ρ'` is `ρ` except at `j`, where it is one lower
  have hle' : ∀ u, ρ' u ≤ ρ u := by
    intro u
    rcases eq_or_ne u j with rfl | hu
    · omega
    · rw [hoth u hu]
  -- a neighbour of `j` stands exactly at `ρ j - 1`
  have hnbeq : ∀ u : Fin n, ((u : ℤ) - (j : ℤ)).natAbs = 1 → ρ u = ρ j - 1 ∧ ρ j - 1 ≤ σ u := by
    intro u hu
    have h1 := hnb u hu
    have hadj : max (σ j) (σ u) ≤ min (ρ j) (ρ u) + 1 := by
      have huj : u.val = j.val + 1 ∨ j.val = u.val + 1 := by
        have := u.isLt; have := j.isLt; omega
      rcases huj with h | h
      · have := hcr.adj j u h
        omega
      · have := hcr.adj u j h
        have : max (σ u) (σ j) ≤ min (ρ u) (ρ j) + 1 := this
        omega
    have hle := hcr.le u
    constructor <;> omega
  refine ⟨fun t => ?_, fun t => ?_, fun t t' htt' => ?_, ?_⟩
  · -- le
    rcases eq_or_ne t j with rfl | ht
    · omega
    · rw [hoth t ht]; exact hcr.le t
  · -- width
    rcases eq_or_ne t j with rfl | ht
    · omega
    · rw [hoth t ht]; exact hcr.width t
  · -- adj
    have hadj := hcr.adj t t' htt'
    rcases eq_or_ne t j with rfl | ht
    · have hnb' : ρ t' = ρ t - 1 ∧ ρ t - 1 ≤ σ t' := by
        refine hnbeq t' ?_
        have : (t' : ℤ) = (t : ℤ) + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) htt'
        omega
      have ht' : t' ≠ t := by
        intro h; rw [h] at htt'; omega
      rw [hoth t' ht']
      have := hcr.le t'
      have := hcr.width t'
      omega
    · rcases eq_or_ne t' j with rfl | ht'
      · have hnb' : ρ t = ρ t' - 1 ∧ ρ t' - 1 ≤ σ t := by
          refine hnbeq t ?_
          have : (t' : ℤ) = (t : ℤ) + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) htt'
          omega
        rw [hoth t ht]
        have := hcr.le t
        have := hcr.width t
        omega
      · rw [hoth t ht, hoth t' ht']
        exact hadj
  · -- the crookedness clause
    rintro s t hst h k ⟨u, hu1, hu2, hu3⟩ ⟨v, hv1, hv2, hv3⟩ habs
    have hn : 1 < n := by
      have := s.isLt; have := t.isLt
      have : s.val < t.val := hst
      omega
    -- a witness for the original pair, near the same index
    have key : ∀ (l : ℤ) (w x : Fin n), ((w : ℤ) - (x : ℤ)).natAbs ≤ 1 → ρ' w ≤ l → l ≤ σ w →
        ∃ y : Fin n, ((y : ℤ) - (x : ℤ)).natAbs ≤ 1 ∧ ρ y ≤ l ∧ l ≤ σ y := by
      intro l w x hwx hw1 hw2
      rcases eq_or_ne w j with rfl | hw
      · -- the shaved link: either the level is the old one, or it is the neighbours' level
        by_cases hcase : ρ w ≤ l
        · exact ⟨w, hwx, hcase, hw2⟩
        · -- `l = ρ j - 1`, met by any neighbour of `j`
          have hh : l = ρ w - 1 := by omega
          rcases eq_or_ne x w with rfl | hxw
          · refine ⟨nbr x hn, ?_, ?_, ?_⟩
            · rw [nbr_dist x hn]
            · exact le_of_eq (by rw [(hnbeq _ (nbr_dist x hn)).1, hh])
            · rw [hh]; exact (hnbeq _ (nbr_dist x hn)).2
          · have hx1 : ((x : ℤ) - (w : ℤ)).natAbs = 1 := by
              have : (x : ℤ) ≠ (w : ℤ) := by
                intro hc
                exact hxw (Fin.ext (by exact_mod_cast hc))
              omega
            refine ⟨x, by simp, ?_, ?_⟩
            · exact le_of_eq (by rw [(hnbeq _ hx1).1, hh])
            · rw [hh]; exact (hnbeq _ hx1).2
      · exact ⟨w, hwx, by rw [← hoth w hw]; exact hw1, hw2⟩
    obtain ⟨u', hu1', hu2', hu3'⟩ := key h u s hu1 hu2 hu3
    obtain ⟨v', hv1', hv2', hv3'⟩ := key k v t hv1 hv2 hv3
    obtain ⟨r, r', h1, h2, h3, hup, hdn⟩ :=
      hcr.crooked s t hst h k ⟨u', hu1', hu2', hu3'⟩ ⟨v', hv1', hv2', hv3'⟩ habs
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hup hlt
      exact ⟨⟨le_trans (hle' r) p1, p2⟩, le_trans (hle' r') q1, q2⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hdn hlt
      exact ⟨⟨le_trans (hle' r) p1, p2⟩, le_trans (hle' r') q1, q2⟩

/-- **The shaved sequence is Lipschitz.** Lowering a strict local maximum by one keeps every step
of size at most one: the peak's neighbours stand exactly one below it. -/
theorem isLip_shave {n : ℕ} {ρ ρ' : Fin n → ℤ} (hlip : IsLip ρ) (j : Fin n)
    (hnb : ∀ u : Fin n, ((u : ℤ) - (j : ℤ)).natAbs = 1 → ρ u = ρ j - 1)
    (hj : ρ' j = ρ j - 1) (hoth : ∀ u : Fin n, u ≠ j → ρ' u = ρ u) :
    IsLip ρ' := by
  intro a b hab
  have hcast : (b : ℤ) = (a : ℤ) + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hab
  rcases eq_or_ne a j with rfl | ha
  · have := hnb b (by omega)
    have hb : b ≠ a := by intro hc; rw [hc] at hab; omega
    rw [hoth b hb, hj, abs_le]
    omega
  · rcases eq_or_ne b j with rfl | hb
    · have := hnb a (by omega)
      rw [hoth a ha, hj, abs_le]
      omega
    · rw [hoth a ha, hoth b hb]
      exact hlip a b hab

end HPC.Fold
