import HPC.Archive.Target74

/-!
# The extreme levels, parametrically in the band

The census of batch 74 records that, at every span swept, the three levels at each end of the
band — `L`, `L + 1`, `L + 2` and `H - 2`, `H - 1`, `H` — are *single-walk*: one walk serves every
basepoint of the level. The commission of batch 75 §2.4 asks whether that is a theorem at every
span: does the repository's argument at those levels use the span, or only the distance to the
nearer end?

**It uses only the distance to the nearer end, and this file says so in Lean.** Nothing here
carries a bound on `H - L`.

What is proved is in fact stronger than "one walk per level" in three ways, and all three fall out
of the existing argument without change:

* the walk depends only on the band, not on the sequence `ρ`, not on the basepoint `i`, and not
  even on the basepoint's level — **one** walk serves all three levels at the bottom end
  (`lowEndWalk`) and one serves all three at the top end (`highEndWalk`);
* no crookedness is used: `IsCrookedIvF` does not appear in any hypothesis, only `IsLip` and the
  band bounds;
* the extremes need not be attained.

The walks are the self-ladders of `HPC/Fold/OffCenter.lean` at the centre pinned to the end of the
band: `lowEndWalk L H = offVee (L+1) (L+1) L H` and `highEndWalk L H = offLam (H-1) (H-1) L H`.
The chain of lemmas behind them — `offDichotomyAt_near_extreme`, `topOnTime_of_ge` /
`bottomOnTime_of_le`, `foldsOnto_offVee_self` / `foldsOnto_offLam_self` — is already stated for an
arbitrary band, so the restatement is proved by instantiating it, with no step re-proved and no
step lost.

`s3_general` — every span, every level — remains open; this file is about the six extreme levels
only.
-/

namespace HPC.Fold

/-- **The walk of the bottom end of the band.** The V-ladder centred at `L + 1`:
down to `L + 1`, up to `H - 1`, down to `L + 1` again. It depends on `L` and `H` only. -/
def lowEndWalk (L H : ℤ) : ℕ × (ℕ → ℤ) := offVee (L + 1) (L + 1) L H

/-- **The walk of the top end of the band.** The Λ-ladder centred at `H - 1`. It depends on `L`
and `H` only. -/
def highEndWalk (L H : ℤ) : ℕ × (ℕ → ℤ) := offLam (H - 1) (H - 1) L H

/-- **The bottom end, at any span.** At a basepoint whose level is at most `L + 2`, both arms fold
onto `lowEndWalk L H`. There is no bound on `H - L`, no crookedness hypothesis, and the walk is
independent of `ρ`, of `i` and of the basepoint's level. -/
theorem foldsOnto_lowEndWalk {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hlow : ρ i ≤ L + 2) :
    FoldsOnto (armG ρ i) (lowEndWalk L H).1 (lowEndWalk L H).2 ∧
      FoldsOnto (armT ρ i) (lowEndWalk L H).1 (lowEndWalk L H).2 := by
  have hi := hLb i
  refine ⟨?_, ?_⟩
  · exact foldsOnto_offVee_self _ (armG_isLip hlip i) (L + 1) L H (by omega) (by omega) hLH
      (fun k => hLb _) (fun k => hHb _)
      (fun k hk => by rw [armG_zero ρ i k hk, abs_le]; omega)
      (topOnTime_of_ge fun k => by have : L ≤ armG ρ i k := hLb _; omega)
  · exact foldsOnto_offVee_self _ (armT_isLip hlip i) (L + 1) L H (by omega) (by omega) hLH
      (fun k => hLb _) (fun k => hHb _)
      (fun k hk => by rw [armT_zero ρ i k hk, abs_le]; omega)
      (topOnTime_of_ge fun k => by have : L ≤ armT ρ i k := hLb _; omega)

/-- **The top end, at any span.** At a basepoint whose level is at least `H - 2`, both arms fold
onto `highEndWalk L H`. As above: no span bound, no crookedness, one walk for the three levels. -/
theorem foldsOnto_highEndWalk {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hhigh : H - 2 ≤ ρ i) :
    FoldsOnto (armG ρ i) (highEndWalk L H).1 (highEndWalk L H).2 ∧
      FoldsOnto (armT ρ i) (highEndWalk L H).1 (highEndWalk L H).2 := by
  have hi := hHb i
  refine ⟨?_, ?_⟩
  · exact foldsOnto_offLam_self _ (armG_isLip hlip i) (H - 1) L H (by omega) (by omega) hLH
      (fun k => hLb _) (fun k => hHb _)
      (fun k hk => by rw [armG_zero ρ i k hk, abs_le]; omega)
      (bottomOnTime_of_le fun k => by have : armG ρ i k ≤ H := hHb _; omega)
  · exact foldsOnto_offLam_self _ (armT_isLip hlip i) (H - 1) L H (by omega) (by omega) hLH
      (fun k => hLb _) (fun k => hHb _)
      (fun k hk => by rw [armT_zero ρ i k hk, abs_le]; omega)
      (bottomOnTime_of_le fun k => by have : armT ρ i k ≤ H := hHb _; omega)

/-- **The six extreme levels of any band are served by two walks.** For every band `[L, H]` with
`L + 3 ≤ H` — and with no upper bound on `H - L` — there are two walks such that, in *every*
Lipschitz sequence with values in the band, every basepoint at a level within two of the bottom
has both arms folding onto the first, and every basepoint at a level within two of the top has
both arms folding onto the second.

This is the parametric form of the census's observation that the extreme three levels at each end
are single-walk at every span: the quantifier `∃ len c` stands *outside* `∀ n ρ i`. -/
theorem extreme_levels_two_walks (L H : ℤ) (hLH : L + 3 ≤ H) :
    ∃ (lenLo : ℕ) (cLo : ℕ → ℤ) (lenHi : ℕ) (cHi : ℕ → ℤ),
      ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) →
        (ρ i ≤ L + 2 → FoldsOnto (armG ρ i) lenLo cLo ∧ FoldsOnto (armT ρ i) lenLo cLo) ∧
        (H - 2 ≤ ρ i → FoldsOnto (armG ρ i) lenHi cHi ∧ FoldsOnto (armT ρ i) lenHi cHi) :=
  ⟨(lowEndWalk L H).1, (lowEndWalk L H).2, (highEndWalk L H).1, (highEndWalk L H).2,
    fun _ ρ i hlip hLb hHb =>
      ⟨fun hlow => foldsOnto_lowEndWalk ρ i L H hlip hLb hHb hLH hlow,
       fun hhigh => foldsOnto_highEndWalk ρ i L H hlip hLb hHb hLH hhigh⟩⟩

/-- **`S3` at the extreme levels of any band**, with the walk named. This is `s3_near_extreme`
(`HPC/Fold/Span.lean`) with the existential walk replaced by the explicit one, which is what makes
the "single walk" reading true: the same `len, c` serves every basepoint of the three levels at
that end, in every sequence. -/
theorem s3_near_extreme_named {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L H : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i) :
    (FoldsOnto (armG ρ i) (lowEndWalk L H).1 (lowEndWalk L H).2 ∧
        FoldsOnto (armT ρ i) (lowEndWalk L H).1 (lowEndWalk L H).2) ∨
      (FoldsOnto (armG ρ i) (highEndWalk L H).1 (highEndWalk L H).2 ∧
        FoldsOnto (armT ρ i) (highEndWalk L H).1 (highEndWalk L H).2) := by
  rcases hnear with hlow | hhigh
  · exact Or.inl (foldsOnto_lowEndWalk ρ i L H hlip hLb hHb hLH hlow)
  · exact Or.inr (foldsOnto_highEndWalk ρ i L H hlip hLb hHb hLH hhigh)

/-- **The length of the two walks grows linearly in the span.** Both have
`1 + 2 * ((H - L - 3) + 1)` times, so the parametric statement is not vacuous for large spans: the
walk is a genuine V (resp. Λ) across the whole band, and its length is determined by the band
alone. -/
theorem lowEndWalk_len (L H : ℤ) :
    (lowEndWalk L H).1 = 1 + ((H - L - 3).toNat + 1) + ((H - L - 3).toNat + 1) := by
  have h1 : ((L + 1) - (L + 1) : ℤ).toNat = 0 := by simp
  have h2 : (H - 1 - ((L + 1) + 1) : ℤ).toNat = (H - L - 3).toNat := by congr 1; ring
  have h3 : (H - 2 - (L + 1) : ℤ).toNat = (H - L - 3).toNat := by congr 1; ring
  simp only [lowEndWalk, offVee, h1, h2, h3]

theorem highEndWalk_len (L H : ℤ) :
    (highEndWalk L H).1 = 1 + ((H - L - 3).toNat + 1) + ((H - L - 3).toNat + 1) := by
  have h1 : ((H - 1) - (H - 1) : ℤ).toNat = 0 := by simp
  have h2 : (H - 1 - 1 - (L + 1) : ℤ).toNat = (H - L - 3).toNat := by congr 1; ring
  have h3 : (H - 1 - (L + 2) : ℤ).toNat = (H - L - 3).toNat := by congr 1; ring
  simp only [highEndWalk, offLam, h1, h2, h3]

end HPC.Fold
