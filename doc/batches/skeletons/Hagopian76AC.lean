import HPC.Hagopian.Hagopian84A

/-!
# Batch 185 skeleton: Hagopian 1976, Theorem 1 — Lemma 7 of 1984; saturation; the case split

Save as `HPC/Hagopian/Hagopian76AC.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76AC` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before. Every theorem
with a named `Prop` among its hypotheses gets a non-vacuity note.

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–348; Hagopian 1984
(`doc/sources/hagopian1984.pdf`), pp. 336–337. Route: commission 185.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §0. `W(x, ε)` -/

/-- **§0**: the 1984 `W(x, ε)` (`Wset84`) is the 1976 `Wₓ` (`Wset`). -/
theorem wset84_eq_wset {M : Set Pt} (x : M) (ε : ℝ) : Wset84 x ε = Wset M ε x := by
  sorry

section Rigidity

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The two-sided extension -/

/-- **§1** (Hagopian 1984, p. 336, in the proof of Lemma 7: "By Lemma 4, there is a continuum `H` of
type λ in `M` such that (1) `E` is an essential subcontinuum of `H` that misses both end sets of
`H`"). Shape: report 184 §11. -/
theorem hagopian84_two_sided (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (H : Set M) (d : H → unitInterval), IsMinimalAdmissible H d ∧ IsEssential84 d E ∧
      Disjoint E (layer d 0) ∧ Disjoint E (layer d 1) := by
  sorry

/-! ## §2. Lemma 7 of 1984 -/

/-- **§2, Lemma 7** (p. 336): "Suppose `F` is a continuum of type λ in `M` such that
`E∖F ≠ ∅ ≠ F∖E`. Suppose `F ∩ k⁻¹(r) ≠ ∅` for some number `r` (`0 ≤ r ≤ 1`). Then `k⁻¹(r)` is an
element of the decomposition of `F`." Shape: the commented-out block of `Hagopian84A.lean`. -/
theorem hagopian84_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : (E \ F).Nonempty) (hFE : (F \ E).Nonempty)
    {r : unitInterval} (hr : (F ∩ layer k r).Nonempty) : ∃ u, layer k r = layer d u := by
  sorry

end Rigidity

/-- **§2, Lemma 7 as a named `Prop`**, for the conditional forms of §4 if §2 resists. -/
def Hagopian84Lemma7 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    ∀ (E F : Set M) (k : E → unitInterval) (d : F → unitInterval), IsMinimalAdmissible E k →
      IsMinimalAdmissible F d → (E \ F).Nonempty → (F \ E).Nonempty →
        ∀ r : unitInterval, (F ∩ layer k r).Nonempty → ∃ u, layer k r = layer d u

section Runs

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §3. Rigidity and translate runs -/

/-- **§3.1, rigidity**: on the intersection of two type λ continua that meets two layers of one of
them, the decompositions agree. *Shape left to you.* -/
theorem layers_agree : True := by
  sorry

/-- **§3.2, runs**: each end of the common segment `G ∩ h[E]` is an end of the translate or an end
layer of `G` (atriodicity). *Shape left to you.* -/
theorem translate_run : True := by
  sorry

/-- **§3.3**: for a crossing component `C` of `F ∩ π⁻¹[D]`, `F` runs along the translate of
`strand_lemma` from `C` to within `2/n` of a translate end, or to `d⁻¹(1)`. *Shape left to you.* -/
theorem crossing_component_run : True := by
  sorry

end Runs

section Sat

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §4. Saturation (2e) -/

/-- **§4.1, steps 4–5 of `noncrossing_half_in_O`**: if neither `K⁻` nor `K⁺` lies in `π⁻¹[D]`, the
component of `y = h(e)` in `F ∩ π⁻¹[D]` is a crossing piece. *Shape left to you.* -/
theorem noncrossing_half_in_O_steps45 : True := by
  sorry

/-- **§4.2, the tip by Lemma 7**: `K⁻ ⊆ π⁻¹[D]` (or `K⁺ ⊆ π⁻¹[D]`) is impossible.
*Shape left to you.* -/
theorem half_in_O_false : True := by
  sorry

/-- **§4.3, saturation from the named `Prop`** (2e for Hagopian's `F` on
`(3/22 + 8/n, 19/22 − 8/n)`). -/
theorem innerComponentsCross_hagopian_of_lemma7 (h7 : Hagopian84Lemma7) (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

/-- **§4.3, saturation**, if §2 is proved. -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

/-! ## §5. The case split for `i ≥ 3` -/

/-- **§5** (p. 348: "The proof now breaks down into two cases"): for tight blocks and `3 ≤ i ≤ m`,
`d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` each meet a closed side segment. -/
theorem blockLayersMeetSides3 (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) : BlockLayersMeetSides3 S x m := by
  sorry

/-! ## §6. "Between" with runs -/

/-- **§6** (p. 348: "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is
between `d⁻¹[I]` and `d⁻¹[J]`"), with §3.3. *Shape left to you.* -/
theorem case1_between_runs : True := by
  sorry

end Sat

/-- **§7, Theorem 1, the strongest conditional form of this batch**
(`hagopian76_theorem1_of_cases4`): from `StepFrame`, `LastStepClaims`, `Case1ClaimsE24`, `Case2ClaimsE24` (and `Hagopian84Lemma7` if
§2 is open), with saturation and the case split discharged. *Shape left to you.* -/
theorem hagopian76_theorem1_of_cases4 : True := by
  sorry

end HPC.Hagopian
