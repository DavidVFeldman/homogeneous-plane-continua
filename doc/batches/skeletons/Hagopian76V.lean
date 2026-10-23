import HPC.Hagopian.Hagopian76U

/-!
# Batch 177 skeleton: Hagopian 1976, Theorem 1 — the strand lemma, and the endgame rebuilt on it

Save as `HPC/Hagopian/Hagopian76V.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76V` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 177 §2–§3.
The constants are chosen in the order `n → θ(n) → δ′ (Effros) → η → c(n) → D → ε₂ → ε₃`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **θ(n)**: points of `E` whose parameters differ by at least `1/n` are at least `θ` apart. -/
theorem exists_param_sep {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (n : ℕ) (hn : 0 < n) :
    ∃ θ > 0, ∀ a b : E, 1 / (n : ℝ) ≤ |(k a : ℝ) - (k b : ℝ)| →
      θ ≤ dist ((a : M) : Pt) ((b : M) : Pt) := by
  sorry

/-- **S0–S1** (commission 177 §2): fine monotonicity of small translates, and every point of `M`
over a thin enough strip is `h(e)` for a `θ/4`-homeomorphism `h` with `k(e)` within `1/n` of its
abscissa. *Shape left to you.* -/
theorem strand_fine_translate : True := by
  sorry

/-- **S2–S3, the strand lemma**: for `D` of height `≤ c(n)`, the component of `M ∩ π⁻¹[D]` through
a point over the inner middle `[3/22 + 3/n, 19/22 − 3/n]` is crossing, and its closure lies in a
`θ/4`-translate `h[E]` and contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`. *Shape left to you.* -/
theorem strand_lemma : True := by
  sorry

/-- **S4**: the strands are linearly ordered; pockets contain no point of `M` over the inner
middle. *Shape left to you.* -/
theorem strand_order : True := by
  sorry

/-- **S5**: a type A′ continuum meets the inner middle in whole strands, except at its end sets.
*Shape left to you.* -/
theorem typeA'_inner_strands : True := by
  sorry

/-- **A.** `T12Data` exists. *Shape left to you.* -/
theorem exists_T12Data : True := by
  sorry

/-- **B.** `π⁻¹[Fr D]` is compact and connected. *Shape left to you.* -/
theorem pi_preimage_frontier_D : True := by
  sorry

/-- **C.** The blocks of `St J`. *Shape left to you.* -/
theorem exists_blocks : True := by
  sorry

/-- **D.** `SepByCrossing` for Hagopian's `F`, `p`, `f(p)`, by the ladder. *Shape left to you.* -/
theorem sep_by_crossing : True := by
  sorry

/-- **E.** `Property4Step` (Cases 1–2), on strands. *Shape left to you.* -/
theorem hagopian76_property4_step : True := by
  sorry

end Thm1

/-- **F. Theorem 1** (p. 345), or the strongest conditional form. *Shape left to you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
