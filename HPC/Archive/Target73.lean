import HPC.Archive.Descent73

/-!
# The branch `L + 5`, and span nine

This file carries the two standing targets that the import order keeps out of the files where they
were stated. `s3_span_nine_mid5` is the statement of `HPC/Fold/Mixed.lean` verbatim, and
`s3_span_nine` that of `HPC/Fold/General.lean` verbatim; both are kept there, commented out, with a
pointer here.

The proof of the branch is the trichotomy reduction plus the crossing theorem of
`HPC/Fold/Descent73.lean`:

* `leg4Land_tri` (`HPC/Fold/LandTri.lean`) serves each arm of the branch with one of three walks,
  so `s3_span_nine_mid5_of_leg4TriCrossL5` reduces the branch to the **crossings** — the basepoints
  no one walk of the three serves on both arms;
* at a crossing, either both arms are deep first at `L + 2`, and `w71` serves both
  (`s3_span_nine_mid5_of_cross_deepFirst2`, `HPC/Fold/Ceil68.lean`), or one of them is not, and
  then it runs high; the two cases are exhaustive by `highRunG_of_not_deepFirst2`;
* a high-run crossing has its partner's ceiling clause free (`ceil72_partner_of_cross_highRunG`,
  batch 72) and its running arm's ceiling clause from the `w8`-failing descent
  (`ceil72_run_of_cross_highRunG`, batch 73), and folds.

Span nine is then `s3_span_nine_of_mid` (`HPC/Fold/CrossArm.lean`) applied to `s3_span_nine_mid4`
and the branch, which is exactly `s3_span_nine'` of `HPC/Fold/Mixed.lean`.

`s3_general` — every span, not only spans at most nine — remains open, and so does `theorem3`
through it.
-/

namespace HPC.Fold

/-- **The branch `L + 5`, ends attained.** `key5` of `s3_span_nine_of_mid`, and the statement of
`HPC/Fold/Mixed.lean`.

The two attainment hypotheses `hLat`, `hHat` are part of the commissioned statement and are kept,
but the proof does not use them: the branch closes from the band, the branch level and the two
`LowAt` announcements alone. -/
theorem s3_span_nine_mid5 {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (_hLat : ∃ t, ρ t = L) (_hHat : ∃ t, ρ t = L + 9)
    (hp : ρ i = L + 5) (hG : LowAt (armG ρ i) (L + 1) (L + 8))
    (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4TriCrossL5 leg4TriCrossL5_holds ρ σ i L hlip hcr hLb hHb hp hG hT

/-- **Span nine, complete.** The statement of `s3_span_nine'` (`HPC/Fold/Mixed.lean`). -/
theorem s3_span_nine' {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_of_mid (fun ρ' σ' i' L' a b c d e f g h k =>
      s3_span_nine_mid4 ρ' σ' i' L' a b c d e f g h k)
    (fun ρ' σ' i' L' a b c d e f g h k => s3_span_nine_mid5 ρ' σ' i' L' a b c d e f g h k)
    ρ σ i H L hlip hcr hLb hHb hLH hspan

/-- **Span nine, complete.** The statement of `HPC/Fold/General.lean`. -/
theorem s3_span_nine {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine' ρ σ i H L hlip hcr hLb hHb hLH hspan

end HPC.Fold
