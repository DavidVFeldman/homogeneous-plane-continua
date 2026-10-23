import HPC.Fold.Shave

/-!
# The general model is reflection-symmetric, and valleys can be filled

`isCrookedIvF_reflect` (`HPC/Fold/ThinSpan9.lean`) reflects a **thin** faithful sequence. The
general model is symmetric too, but the reflection exchanges the two ends of each link: the
reflection of `(ρ, σ)` in a level `a` is `(a - σ, a - ρ)`, whose point sequence is `a - σ` and not
`a - ρ`. That is `isCrookedIvF_reflect_general` below, and it is what the thin statement is the
diagonal of.

Two things follow.

* **`σ` is 1-Lipschitz** (`isCrookedIvF_sig_isLip`): geometric adjacency bounds the upper ends of
  two neighbouring links as tightly as it bounds their lower ends. So the reflected pair is again
  a Lipschitz point sequence with links of width at most one, and every statement of the
  development applies to it.
* **Filling a valley** (`isCrookedIvF_fill`): the reflection of shaving a peak. Let `j` be a thin
  link whose two neighbours have their upper ends strictly above it. Raise `σ` at `j` by one and
  leave `ρ` alone: the pair stays faithful. Where shaving keeps `σ` and lowers `ρ`, filling keeps
  `ρ` and raises `σ`, so it is a generator of non-thin pairs that changes no walk criterion at
  all — every criterion of the development reads `ρ` — while making the crookedness clause fire
  from more levels.

Filling is what makes the batch-47 counterexample of `HPC/Fold/Raise.lean` typical rather than
accidental: a filled valley is a link that meets a level at which the point sequence never stands,
and the raise of such a pair moves its point sequence to a place the clause never certified.
-/

namespace HPC.Fold

/-- **The upper ends are 1-Lipschitz.** Geometric adjacency gives `σ t ≤ ρ t' + 1 ≤ σ t' + 1` for
neighbours, and symmetrically. -/
theorem isCrookedIvF_sig_isLip {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ) : IsLip σ := by
  intro t t' htt'
  have hadj := h.adj t t' htt'
  rw [max_le_iff] at hadj
  have h1 := h.le t
  have h2 := h.le t'
  rw [abs_le]
  omega

/-- **The general model is symmetric under reflection of the levels.** Reflecting a faithful
crooked pair in a level `a` gives the faithful crooked pair `(a - σ, a - ρ)`: the lower end of
each link becomes its upper end. A level is met by a link of the reflected pair exactly when its
reflection is met by the same link of the original, and the two branches of the crookedness
clause exchange. -/
theorem isCrookedIvF_reflect_general {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (a : ℤ) :
    IsCrookedIvF (fun u => a - σ u) (fun u => a - ρ u) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t t' htt' => ?_, ?_⟩
  · have := hcr.le t; show a - σ t ≤ a - ρ t; omega
  · have := hcr.width t; show a - ρ t ≤ a - σ t + 1; omega
  · have hadj := hcr.adj t t' htt'
    have h1 := hcr.le t
    have h2 := hcr.le t'
    show max (a - ρ t) (a - ρ t') ≤ min (a - σ t) (a - σ t') + 1
    omega
  · rintro s t hst h k ⟨u, hu1, hu2, hu3⟩ ⟨v, hv1, hv2, hv3⟩ habs
    -- a level `l` is met by the reflected link `w` exactly when `a - l` is met by `w`
    obtain ⟨r, r', h1, h2, h3, hup, hdn⟩ :=
      hcr.crooked s t hst (a - h) (a - k)
        ⟨u, hu1, by omega, by omega⟩ ⟨v, hv1, by omega, by omega⟩
        (by rw [show a - h - (a - k) = -(h - k) from by ring, abs_neg]; exact habs)
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hdn (by omega)
      exact ⟨⟨by show a - σ r ≤ k - 1; omega, by show k - 1 ≤ a - ρ r; omega⟩,
        by show a - σ r' ≤ h + 1; omega, by show h + 1 ≤ a - ρ r'; omega⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hup (by omega)
      exact ⟨⟨by show a - σ r ≤ k + 1; omega, by show k + 1 ≤ a - ρ r; omega⟩,
        by show a - σ r' ≤ h - 1; omega, by show h - 1 ≤ a - ρ r'; omega⟩

/-- **Filling a valley keeps the pair faithful.** The reflection of `isCrookedIvF_shave`: if
`(ρ, σ)` is faithful, the link `j` is thin and both its neighbours have their upper ends strictly
above it, then raising `σ` at `j` by one — leaving `ρ` alone, so that the point sequence does not
move — gives a faithful crooked pair again.

Only the two hypotheses of shaving are used, read on the other end of the link. -/
theorem isCrookedIvF_fill {n : ℕ} {ρ σ σ' : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (j : Fin n)
    (hσj : σ j = ρ j)
    (hnb : ∀ u : Fin n, ((u : ℤ) - (j : ℤ)).natAbs = 1 → σ j + 1 ≤ σ u)
    (hj : σ' j = σ j + 1) (hoth : ∀ u : Fin n, u ≠ j → σ' u = σ u) :
    IsCrookedIvF ρ σ' := by
  -- reflect, shave the peak that `j` has become, and reflect back
  have hrefl := isCrookedIvF_reflect_general hcr 0
  have hshave :=
    isCrookedIvF_shave (ρ := fun u => -σ u) (σ := fun u => -ρ u) (ρ' := fun u => -σ' u)
      (by simpa using hrefl) j (by show -ρ j = -σ j; omega)
      (fun u hu => by
        have := hnb u hu
        show -σ u ≤ -σ j - 1
        omega)
      (by show -σ' j = -σ j - 1; omega)
      (fun u hu => by show -σ' u = -σ u; rw [hoth u hu])
  have hback := isCrookedIvF_reflect_general hshave 0
  have h1 : (fun u => 0 - -ρ u) = ρ := by funext u; omega
  have h2 : (fun u => 0 - -σ' u) = σ' := by funext u; omega
  rw [h1, h2] at hback
  exact hback

end HPC.Fold
