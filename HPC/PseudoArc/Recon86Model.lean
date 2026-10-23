import HPC.Fold.Faithful
import HPC.Chains.Consolidation

/-!
# Batch 86: the time-ordering fold in the faithful model (commission §1.3 Q2)

`ModelCoveringFold ρ σ A T Qs I` is the combinatorial statement behind
`Description.IsCoveringFold` (`HPC/PseudoArc/Recon86.lean`), read in the faithful model: fine
links `t` with coarse interval `[ρ t, σ t]`; a block map `β` onto `q` blocks, each block inside one
coarse link; the links `A` (through `P'`) in block `0`, the links `Qs` (through `Q'`) in the last
block, the links `T` (through `R`) in one block `b`, the links `I` (meeting `W`) in blocks `≤ b`.

`model_covering_fold_refuted`: the statement is **false** under crookedness (`IsCrookedIvF`) and
the window property of `Description.window_of_irreducible` together — a six-link witness. So a proof
of `covering_step` through time-ordering folds must use more of `W` than crookedness of the levels
and the window property.
-/

namespace HPC.Fold

/-- The time-ordering fold in the faithful model. -/
def ModelCoveringFold {n : ℕ} (ρ σ : Fin n → ℤ) (A T Qs I : Finset (Fin n)) : Prop :=
  ∃ q, ∃ β : Fin n → Fin q, ∃ b : Fin q, Chain.IsBlockMap β ∧
    (∀ u, ∃ s : ℤ, ∀ t, β t = u → ρ t ≤ s ∧ s ≤ σ t) ∧
    (∀ t ∈ A, (β t).val = 0) ∧ (∀ t ∈ Qs, (β t).val = q - 1) ∧
    (∀ t ∈ T, β t = b) ∧ (∀ t ∈ I, β t ≤ b)

/-- The window property in the model: every link of `I` shares a coarse link with some link of
the index interval `[a, c]`. -/
def ModelWindow {n : ℕ} (ρ σ : Fin n → ℤ) (a c : Fin n) (I : Finset (Fin n)) : Prop :=
  ∀ u ∈ I, ∃ v : Fin n, a ≤ v ∧ v ≤ c ∧ ∃ s : ℤ, ρ u ≤ s ∧ s ≤ σ u ∧ ρ v ≤ s ∧ s ≤ σ v

/-- The witness: coarse levels `0, 1, 2, 1, 0, 1`. `P'` in link `0`, `R` in link `3`, `W` meets
links `0 … 4`, `Q'` in link `5`. -/
def recon86Rho : Fin 6 → ℤ := ![0, 1, 2, 1, 0, 1]

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem recon86_isCrookedIvF : IsCrookedIvF recon86Rho recon86Rho :=
  isCrookedIvF_of_check (by unfold IsCrookedIvFCheck ivEnd; decide)

theorem recon86_window : ModelWindow recon86Rho recon86Rho 0 3 (Finset.Icc 0 4) := by
  have h : ∀ u : Fin 6, ∃ v : Fin 6, v ≤ 3 ∧ recon86Rho v = recon86Rho u := by decide
  intro u _
  obtain ⟨v, hv, hvu⟩ := h u
  exact ⟨v, Fin.zero_le v, hv, recon86Rho u, le_rfl, le_rfl, hvu.le, hvu.ge⟩

/-- **The time-ordering fold fails in the model**, although the pattern is crooked, the
`W`-links form an interval containing the `P'`- and `R`-links, the `Q'`-link lies outside it, and
the window property holds. -/
theorem model_covering_fold_refuted :
    IsCrookedIvF recon86Rho recon86Rho ∧
    ModelWindow recon86Rho recon86Rho 0 3 (Finset.Icc 0 4) ∧
    ¬ ModelCoveringFold recon86Rho recon86Rho {0} {3} {5} (Finset.Icc 0 4) := by
  refine ⟨recon86_isCrookedIvF, recon86_window, ?_⟩
  rintro ⟨q, β, b, hβ, hsm, hA, -, hT, hI⟩
  have same : ∀ t t' : Fin 6, (β t).val = (β t').val → recon86Rho t = recon86Rho t' := by
    intro t t' h
    obtain ⟨s, hs⟩ := hsm (β t)
    have h1 := hs t rfl
    have h2 := hs t' (Fin.ext h.symm)
    omega
  have n01 : (β 0).val ≠ (β 1).val := fun h => by
    have := same 0 1 h; simp [recon86Rho] at this
  have n02 : (β 0).val ≠ (β 2).val := fun h => by
    have := same 0 2 h; simp [recon86Rho] at this
  have n12 : (β 1).val ≠ (β 2).val := fun h => by
    have := same 1 2 h; simp [recon86Rho] at this
  have n23 : (β 2).val ≠ (β 3).val := fun h => by
    have := same 2 3 h; simp [recon86Rho] at this
  have n24 : (β 2).val ≠ (β 4).val := fun h => by
    have := same 2 4 h; simp [recon86Rho] at this
  have n34 : (β 3).val ≠ (β 4).val := fun h => by
    have := same 3 4 h; simp [recon86Rho] at this
  have l0 := hβ.lip 0 1 rfl
  have l1 := hβ.lip 1 2 rfl
  have l2 := hβ.lip 2 3 rfl
  have l3 := hβ.lip 3 4 rfl
  have v0 : (β 0).val = 0 := hA 0 (by decide)
  have v3 : β 3 = b := hT 3 (by decide)
  have i2 : (β 2).val ≤ b.val := Fin.le_def.mp (hI 2 (by decide))
  have i4 : (β 4).val ≤ b.val := Fin.le_def.mp (hI 4 (by decide))
  rw [← v3] at i2 i4
  omega

end HPC.Fold
