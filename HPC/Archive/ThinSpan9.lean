import HPC.Archive.MixedThin

/-!
# Span nine, complete, on a thin sequence

The thin form of the faithful model — `σ = ρ`, every link a point — is **symmetric under
reflection of the levels**: if `ρ` is thin faithful crooked, so is `a - ρ` for any `a`. The
general model is not symmetric in this way in its own terms, because reflecting the pair
`(ρ, σ)` gives the pair `(-σ, -ρ)`, and the two branches of the crookedness clause exchange; on a
thin sequence the two coincide (`isCrookedIvF_reflect`).

That is enough to carry the whole branch `L + 4` of `HPC/Fold/MixedThin.lean` to the branch
`L + 5`: reflecting in `a = 2L + 9` fixes the band `[L, L + 9]` and exchanges the two
basepoints. So, for a thin sequence, `s3_span_nine` is a theorem
(`s3_span_nine_mid5_thin`, `s3_span_nine_thin`).

**This is not the answer to the standing question** of whether the thin form loses pairs. What
it shows is where the thin form is doing work, and how much: at span nine, everything that is
left.

Note that the reflection is available only because the branch `L + 5` is reached through the
*proved* branch `L + 4` and not through its commissioned statement: the two branch hypotheses
`HighAt (L + 1) (L + 8)` and `LowAt (L + 1) (L + 8)` are **not** reflections of one another —
`HighAt` has one clause and `LowAt` two — and `s3_span_nine_mid4_thin` needs neither.
-/

namespace HPC.Fold

/-! ## Reflection of the levels -/

/-- The reflected arm is Lipschitz. -/
theorem isLip_reflect {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (a : ℤ) :
    IsLip (fun u => a - ρ u) := by
  intro j j' hjj'
  have := hlip j j' hjj'
  simp only [abs_le] at this ⊢
  omega

/-- **The thin model is symmetric under reflection of the levels.** Reflecting a thin faithful
crooked sequence in any level gives a thin faithful crooked sequence: the reflection exchanges
the two branches of the crookedness clause, and on a thin sequence each branch pins its two
links exactly, so the exchange is an equality. -/
theorem isCrookedIvF_reflect {n : ℕ} {ρ : Fin n → ℤ} (hcr : IsCrookedIvF ρ ρ) (a : ℤ) :
    IsCrookedIvF (fun u => a - ρ u) (fun u => a - ρ u) := by
  refine ⟨fun t => le_rfl, fun t => by omega, fun t t' htt' => ?_, ?_⟩
  · have h := hcr.adj t t' htt'
    show max (a - ρ t) (a - ρ t') ≤ min (a - ρ t) (a - ρ t') + 1
    omega
  · rintro s t hst h k ⟨u, hu1, hu2, hu3⟩ ⟨v, hv1, hv2, hv3⟩ habs
    obtain ⟨r, r', h1, h2, h3, hup, hdn⟩ :=
      hcr.crooked s t hst (a - h) (a - k)
        ⟨u, hu1, by omega, by omega⟩ ⟨v, hv1, by omega, by omega⟩
        (by rw [show a - h - (a - k) = -(h - k) from by ring, abs_neg]; exact habs)
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hdn (by omega)
      exact ⟨⟨by show a - ρ r ≤ k - 1; omega, by show k - 1 ≤ a - ρ r; omega⟩,
        by show a - ρ r' ≤ h + 1; omega, by show h + 1 ≤ a - ρ r'; omega⟩
    · obtain ⟨⟨p1, p2⟩, q1, q2⟩ := hup (by omega)
      exact ⟨⟨by show a - ρ r ≤ k + 1; omega, by show k + 1 ≤ a - ρ r; omega⟩,
        by show a - ρ r' ≤ h - 1; omega, by show h - 1 ≤ a - ρ r'; omega⟩

/-- A fold of the reflected arm is a fold of the arm, onto the reflected walk. -/
theorem foldsOnto_of_reflect {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (a : ℤ)
    (h : FoldsOnto (fun j => a - f j) len c) : FoldsOnto f len (fun u => a - c u) := by
  obtain ⟨β, h1, h2, h3, h4⟩ := h
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [abs_le] at this ⊢
  omega

/-! ## The branch `L + 5`, and span nine -/

/-- **The branch `L + 5`, on a thin sequence.** The reflection of `s3_span_nine_mid4_thin` in the
middle of the band: `a = 2L + 9` fixes `[L, L + 9]` and carries `L + 5` to `L + 4`. -/
theorem s3_span_nine_mid5_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hcr' : IsCrookedIvF ρ ρ := by
    have : σ = ρ := funext hthin
    rwa [this] at hcr
  set a : ℤ := 2 * L + 9 with ha
  obtain ⟨len, c, hG, hT⟩ :=
    s3_span_nine_mid4_thin (fun u => a - ρ u) (fun u => a - ρ u) i L (isLip_reflect hlip a)
      (isCrookedIvF_reflect hcr' a) (fun _ => rfl)
      (fun t => by show L ≤ a - ρ t; have := hHb t; omega)
      (fun t => by show a - ρ t ≤ L + 9; have := hLb t; omega)
      (by show a - ρ i = L + 4; omega)
  exact ⟨len, fun u => a - c u, foldsOnto_of_reflect (armG ρ i) len c a hG,
    foldsOnto_of_reflect (armT ρ i) len c a hT⟩

/-- **Span nine, complete, on a thin sequence.** Every basepoint of a thin faithful crooked
sequence of span at most nine has both its arms folding onto one walk. This is the commissioned
`s3_span_nine` with the thin hypothesis added; in the general model both of its two branches are
still open. -/
theorem s3_span_nine_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h8 : H ≤ L + 8
  · exact s3_span_eight ρ σ i H L hlip hcr hLb hHb hLH h8
  · have hH9 : H = L + 9 := by omega
    subst hH9
    by_cases hp4 : ρ i = L + 4
    · exact s3_span_nine_mid4_thin ρ σ i L hlip hcr hthin hLb hHb hp4
    · by_cases hp5 : ρ i = L + 5
      · exact s3_span_nine_mid5_thin ρ σ i L hlip hcr hthin hLb hHb hp5
      · exact s3_span_nine_off_center ρ σ i (L + 9) L hlip hcr hLb hHb hLH hspan
          (Or.inr ⟨hp4, hp5⟩)

end HPC.Fold
