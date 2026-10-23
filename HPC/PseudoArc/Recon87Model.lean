import HPC.PseudoArc.Recon86Model

/-!
# Batch 87, item 2: the time-ordering fold with three-link blocks, in the faithful model

`ModelCoveringFold₃ ρ σ A T Qs I` is `ModelCoveringFold` (`HPC/PseudoArc/Recon86Model.lean`) with
the one-link block clause replaced by the three-link clause `∃ j, ∀ t, β t = u → j ≤ σ t ∧
ρ t ≤ j + 2` (the coarse intervals of the members of each block meet a common window
`[j, j + 2]`); it is the model reading of `Description.IsCoveringFold₃`
(`HPC/PseudoArc/Recon87.lean`).

* `model_covering_fold₃_recon86`: the batch-86 witness is **not** a counterexample to the
  three-link reading (commission §0.1): `β = (0, 1, 2, 3, 3, 4)`.
* `model_covering_fold₃_refuted`: the three-link statement is still **false** under crookedness,
  the window property and the separation `S1` of the links of `P'` and `R` (coarse gap `≥ 3`)
  together — a seven-link witness. The link of `Q'` in it is adjacent to the link of `P'`.
* `ModelFar`: the separation `S2` of the link of `Q'` from every `W`-link (coarse gap `≥ 3`),
  which holds at deep levels because `Q' ∉ W`. The census `census-batch87-model.c` found no
  failure of the three-link statement under crookedness, the window property and `S2`
  (ranges and counts in `REPORT-batch87.md`); that statement is recorded below as a conjecture.
-/

namespace HPC.Fold

/-- The time-ordering fold in the faithful model, with three-link blocks. -/
def ModelCoveringFold₃ {n : ℕ} (ρ σ : Fin n → ℤ) (A T Qs I : Finset (Fin n)) : Prop :=
  ∃ q, ∃ β : Fin n → Fin q, ∃ b : Fin q, Chain.IsBlockMap β ∧
    (∀ u, ∃ j : ℤ, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2) ∧
    (∀ t ∈ A, (β t).val = 0) ∧ (∀ t ∈ Qs, (β t).val = q - 1) ∧
    (∀ t ∈ T, β t = b) ∧ (∀ t ∈ I, β t ≤ b)

/-- The coarse gap between the intervals of two links (`≤ 0` when they share a coarse level). -/
def levelGap {n : ℕ} (ρ σ : Fin n → ℤ) (u v : Fin n) : ℤ := max (ρ v - σ u) (ρ u - σ v)

/-- Separation `S2`: the link `q` (of `Q'`) is at coarse gap `≥ 3` from every link of `I`. -/
def ModelFar {n : ℕ} (ρ σ : Fin n → ℤ) (q : Fin n) (I : Finset (Fin n)) : Prop :=
  ∀ t ∈ I, 3 ≤ levelGap ρ σ t q

/-- Two links whose coarse intervals are more than two levels apart are never in the same
three-link block. -/
theorem block₃_val_ne {n q : ℕ} {ρ σ : Fin n → ℤ} {β : Fin n → Fin q}
    (hsm : ∀ u, ∃ j : ℤ, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2) {t t' : Fin n}
    (h : σ t + 2 < ρ t' ∨ σ t' + 2 < ρ t) : (β t).val ≠ (β t').val := by
  intro he
  obtain ⟨j, hj⟩ := hsm (β t)
  have h1 := hj t rfl
  have h2 := hj t' (Fin.ext he.symm)
  omega

/-- **The batch-86 witness has a three-link fold** (commission §0.1): `β = (0, 1, 2, 3, 3, 4)`,
`R`'s block `3 = {3, 4}`, every block inside the window `[0, 2]`. -/
theorem model_covering_fold₃_recon86 :
    ModelCoveringFold₃ recon86Rho recon86Rho {0} {3} {5} (Finset.Icc 0 4) := by
  refine ⟨5, ![0, 1, 2, 3, 3, 4], 3, ⟨by decide, by decide⟩, fun _ => ⟨0, ?_⟩, by decide,
    by decide, by decide, by decide⟩
  intro t _
  fin_cases t <;> simp [recon86Rho]

/-- The seven-link witness: coarse intervals `[0,0], [0,0], [1,1], [1,2], [1,1], [2,2], [3,3]`.
`P'` in link `1`, `R` in link `6`, `Q'` in link `0`, `W` meets links `1 … 6`. -/
def recon87Rho : Fin 7 → ℤ := ![0, 0, 1, 1, 1, 2, 3]
/-- Upper ends of the seven-link witness. -/
def recon87Sig : Fin 7 → ℤ := ![0, 0, 1, 2, 1, 2, 3]

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem recon87_isCrookedIvF : IsCrookedIvF recon87Rho recon87Sig :=
  isCrookedIvF_of_check (by unfold IsCrookedIvFCheck ivEnd; decide)

theorem recon87_window : ModelWindow recon87Rho recon87Sig 1 6 (Finset.Icc 1 6) := by
  intro u hu
  refine ⟨u, (Finset.mem_Icc.mp hu).1, (Finset.mem_Icc.mp hu).2, recon87Rho u, le_rfl, ?_,
    le_rfl, ?_⟩ <;> fin_cases u <;> simp [recon87Rho, recon87Sig]

/-- **The three-link time-ordering fold fails in the model**, although the pattern is crooked,
the `W`-links form an interval containing the links of `P'` and `R`, the link of `Q'` lies
outside it, the window property holds, and the links of `P'` and `R` are three coarse levels
apart (`S1`). The link of `Q'` is adjacent to that of `P'`, so `S2` fails. -/
theorem model_covering_fold₃_refuted :
    IsCrookedIvF recon87Rho recon87Sig ∧
    ModelWindow recon87Rho recon87Sig 1 6 (Finset.Icc 1 6) ∧
    3 ≤ levelGap recon87Rho recon87Sig 1 6 ∧
    ¬ ModelFar recon87Rho recon87Sig 0 (Finset.Icc 1 6) ∧
    ¬ ModelCoveringFold₃ recon87Rho recon87Sig {1} {6} {0} (Finset.Icc 1 6) := by
  refine ⟨recon87_isCrookedIvF, recon87_window, by decide, fun h => ?_, ?_⟩
  · have := h 1 (by decide)
    revert this; decide
  rintro ⟨q, β, b, hβ, hsm, hA, hQ, -, -⟩
  have n16 : (β 1).val ≠ (β 6).val := block₃_val_ne hsm (by decide)
  have n06 : (β 0).val ≠ (β 6).val := block₃_val_ne hsm (by decide)
  have l0 := hβ.lip 0 1 rfl
  have v1 : (β 1).val = 0 := hA 1 (by decide)
  have v0 : (β 0).val = q - 1 := hQ 0 (by decide)
  have h6 := (β 6).isLt
  omega

/-! ### The conjecture suggested by the census (not proved)

```
∀ n (ρ σ : Fin n → ℤ) (a c q : Fin n) (I : Finset (Fin n)),
  IsCrookedIvF ρ σ → a ≠ c →
  I is an index interval containing a and c, q ∉ I →
  ModelWindow ρ σ (min a c) (max a c) I → ModelFar ρ σ q I →
  ModelCoveringFold₃ ρ σ {a} {c} {q} I
```

Census (`census-batch87-model.c`, class `FOLD3[S2]`, largest admissible `I`): no failure over
all faithful sequences spanning exactly four coarse links of lengths `6 … 13` and exactly five
coarse links of lengths `13 … 16`, and over the subchains of Bing's chains for `K = 5, 6, 7`
(some cases at `K = 7` left undecided by the node limit); the counts are in `REPORT-batch87.md`.
At four and five coarse links `S2` forces every link of `I` into one three-link window, so those
instances test only the part of the chain outside `I`. With `S1` added as well the hypotheses need
at least seven coarse levels, which only the Bing chains reach.
-/

end HPC.Fold
