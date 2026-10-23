import HPC.Census.Census87

/-!
# Batch 87: the finite census checks, run in Lean

The checks of `HPC.Fold.Census87` over `gen 4 n` for `n ≤ 7`, decided by `native_decide`, and
their consequences: the model statement `ModelT3End` and the three-link fold under `S2` hold for
every crooked sequence of at most seven links over four coarse links.
-/

namespace HPC.Fold.Census87

theorem checkT3_4_1 : (gen 4 1).all (checkT3 4 1) = true := by native_decide
theorem checkT3_4_2 : (gen 4 2).all (checkT3 4 2) = true := by native_decide
theorem checkT3_4_3 : (gen 4 3).all (checkT3 4 3) = true := by native_decide
theorem checkT3_4_4 : (gen 4 4).all (checkT3 4 4) = true := by native_decide
theorem checkT3_4_5 : (gen 4 5).all (checkT3 4 5) = true := by native_decide
theorem checkT3_4_6 : (gen 4 6).all (checkT3 4 6) = true := by native_decide
theorem checkT3_4_7 : (gen 4 7).all (checkT3 4 7) = true := by native_decide

theorem checkF3_4_1 : (gen 4 1).all (checkF3 1) = true := by native_decide
theorem checkF3_4_2 : (gen 4 2).all (checkF3 2) = true := by native_decide
theorem checkF3_4_3 : (gen 4 3).all (checkF3 3) = true := by native_decide
theorem checkF3_4_4 : (gen 4 4).all (checkF3 4) = true := by native_decide
theorem checkF3_4_5 : (gen 4 5).all (checkF3 5) = true := by native_decide
theorem checkF3_4_6 : (gen 4 6).all (checkF3 6) = true := by native_decide
theorem checkF3_4_7 : (gen 4 7).all (checkF3 7) = true := by native_decide

theorem checkT3_4_le7 : ∀ n, 1 ≤ n → n ≤ 7 → (gen 4 n).all (checkT3 4 n) = true := by
  intro n h1 h2
  interval_cases n
  exacts [checkT3_4_1, checkT3_4_2, checkT3_4_3, checkT3_4_4, checkT3_4_5, checkT3_4_6,
    checkT3_4_7]

theorem checkF3_4_le7 : ∀ n, 1 ≤ n → n ≤ 7 → (gen 4 n).all (checkF3 n) = true := by
  intro n h1 h2
  interval_cases n
  exacts [checkF3_4_1, checkF3_4_2, checkF3_4_3, checkF3_4_4, checkF3_4_5, checkF3_4_6,
    checkF3_4_7]

/-- **Census `T3END`, Lean-checked (`K = 4`, `n ≤ 7`).** Every crooked sequence of at most seven
links over four coarse links satisfies the model reading of `theorem3_end` at every basepoint. -/
theorem modelT3End_census_K4 {n : ℕ} (hn : n ≤ 7) {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ)
    (h0 : ∀ t, 0 ≤ ρ t) (hK : ∀ t, σ t < 4) (i : Fin n) : ModelT3End ρ σ 4 i :=
  modelT3End_of_check (K := 4) (checkT3_4_le7 n (Fin.pos i) hn) hf h0 hK i

/-- **Census `FOLD3` under `S2`, Lean-checked (`K = 4`, `n ≤ 7`).** For every crooked sequence of at
most seven links over four coarse links, every window `[lo, hi]` containing distinct links `a`, `c`
and satisfying the window property relative to `[min a c, max a c]`, and every link `q` outside the
window at coarse gap `≥ 3` from it, the three-link covering fold exists. -/
theorem fold3_census_K4 {n : ℕ} (hn : n ≤ 7) {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ)
    (h0 : ∀ t, 0 ≤ ρ t) (hK : ∀ t, σ t < 4)
    {a c q lo hi : Fin n} (hac : a ≠ c) (ha : lo ≤ a ∧ a ≤ hi) (hc : lo ≤ c ∧ c ≤ hi)
    (hq : ¬ (lo ≤ q ∧ q ≤ hi))
    (hw : ModelWindow ρ σ (min a c) (max a c) (Finset.Icc lo hi))
    (hfar : ModelFar ρ σ q (Finset.Icc lo hi)) :
    ModelCoveringFold₃ ρ σ {a} {c} {q} (Finset.Icc lo hi) :=
  fold3_of_check (K := 4) (checkF3_4_le7 n (Fin.pos a) hn) hf h0 hK hac ha hc hq hw hfar

end HPC.Fold.Census87
