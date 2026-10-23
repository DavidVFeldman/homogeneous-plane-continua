import HPC.PseudoArc.Recon87Model
import HPC.Fold.ClosureF

/-!
# Batch 87, item 3: the end-time control lemma, stated in the faithful model, and refuted

Setting (commission item 3): in a description of `M` from `R` to `Q'`, the links of a deep level
that meet `W` form an initial segment `[0, c]`, `R` is in link `0`, `P'` in a link `p` with
`0 < p < c`. Wanted: a three-link fold of `[0, c]` from the basepoint `p` in which the two arm
ends `0` and `c` are both placed at the maximal time.

`ModelEndTime ρ σ p` states this in the faithful model for a sequence on `Fin (c + 1)`.

`model_end_time_refuted`: it is **false** under crookedness, the window property of
`Description.window_of_irreducible` (every link shares a coarse level with a link of the arm
`[0, p]` from `R` to `P'`) and the separation of the links of `R` and `P'` (coarse gap `≥ 3`)
together — a seven-link witness. The obstruction is structural: both arm ends are at the
maximal time, hence in the *same* block, so their coarse intervals must meet a common three-link
window (`ModelEndTime.ends_close`); nothing in the hypotheses places the last `W`-link `c` near
the link of `R`.

`model_end_time_refuted'`: the lemma is **still false** with that necessary condition (`C`)
added — a fifteen-link witness, crooked across five coarse links. There the arm `[p, c]` is a
single step, so the maximal time is at most `1` (the block map is `1`-Lipschitz), and two blocks
cannot hold the link `1` (level `0`) beside the links `p` (level `4`) and `c` (level `3`). In the
ranges searched, every census failure under `C` also violates the condition `X` of the last
section (an arm that misses an extreme coarse level); see `REPORT-batch87.md`.
-/

namespace HPC.Fold

/-- **The end-time property** in the faithful model: a block map of `[0, c]`, every block inside
three consecutive coarse links, with the basepoint `p` at time `0` and both arm ends `0` and `c`
at the maximal time. -/
def ModelEndTime {c : ℕ} (ρ σ : Fin (c + 1) → ℤ) (p : Fin (c + 1)) : Prop :=
  ∃ q, ∃ β : Fin (c + 1) → Fin q, Chain.IsBlockMap β ∧
    (∀ u, ∃ j : ℤ, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2) ∧
    (β p).val = 0 ∧ (β 0).val = q - 1 ∧ (β (Fin.last c)).val = q - 1

/-- **Both arm ends share the last block**, so their coarse intervals meet a common window
`[j, j + 2]`. This necessary condition is what the witness below violates. -/
theorem ModelEndTime.ends_close {c : ℕ} {ρ σ : Fin (c + 1) → ℤ} {p : Fin (c + 1)}
    (h : ModelEndTime ρ σ p) :
    ∃ j : ℤ, j ≤ σ 0 ∧ ρ 0 ≤ j + 2 ∧ j ≤ σ (Fin.last c) ∧ ρ (Fin.last c) ≤ j + 2 := by
  obtain ⟨q, β, -, hsm, -, h0, hc⟩ := h
  obtain ⟨j, hj⟩ := hsm (β 0)
  have e : β (Fin.last c) = β 0 := Fin.ext (hc.trans h0.symm)
  exact ⟨j, (hj 0 rfl).1, (hj 0 rfl).2, (hj _ e).1, (hj _ e).2⟩

/-- The witness: coarse levels `0, 1, 2, 1, 2, 3, 3` (`ρ = σ`), `R` in link `0`, `P'` in link
`5`, `c = 6`. -/
def endRho : Fin 7 → ℤ := ![0, 1, 2, 1, 2, 3, 3]

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem endRho_isCrookedIvF : IsCrookedIvF endRho endRho :=
  isCrookedIvF_of_check (by unfold IsCrookedIvFCheck ivEnd; decide)

theorem endRho_window : ModelWindow endRho endRho 0 5 Finset.univ := by
  have h : ∀ u : Fin 7, ∃ v : Fin 7, v ≤ 5 ∧ endRho v = endRho u := by decide
  intro u _
  obtain ⟨v, hv, hvu⟩ := h u
  exact ⟨v, Fin.zero_le v, hv, endRho u, le_rfl, le_rfl, hvu.le, hvu.ge⟩

/-- **The end-time lemma fails in the model**, under crookedness, the window property and the
separation of the links of `R` and `P'`. -/
theorem model_end_time_refuted :
    IsCrookedIvF endRho endRho ∧ ModelWindow endRho endRho 0 5 Finset.univ ∧
    3 ≤ levelGap endRho endRho 0 5 ∧ ¬ ModelEndTime (c := 6) endRho endRho 5 := by
  refine ⟨endRho_isCrookedIvF, endRho_window, by decide, ?_⟩
  intro h
  obtain ⟨j, h1, -, -, h2⟩ := h.ends_close
  simp [endRho] at h1 h2
  omega

/-- The fifteen-link witness, lower ends. `R` in link `0`, `P'` in link `13`, `c = 14`. -/
def end15Rho : Fin 15 → ℤ := ![0, 0, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4, 3]
/-- Upper ends of the fifteen-link witness. -/
def end15Sig : Fin 15 → ℤ := ![1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3]

set_option maxRecDepth 40000000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 20000000 in
set_option maxHeartbeats 20000000 in
theorem end15_isCrookedIvF : IsCrookedIvF end15Rho end15Sig :=
  isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

theorem end15_window : ModelWindow end15Rho end15Sig 0 13 Finset.univ := by
  have h : ∀ u : Fin 15, ∃ v : Fin 15, v ≤ 13 ∧ ∃ s : Fin 5,
      end15Rho u ≤ (s : ℤ) ∧ (s : ℤ) ≤ end15Sig u ∧ end15Rho v ≤ (s : ℤ) ∧
        (s : ℤ) ≤ end15Sig v := by decide
  intro u _
  obtain ⟨v, hv, s, hs⟩ := h u
  exact ⟨v, Fin.zero_le v, hv, s, hs⟩

/-- **The end-time lemma fails even with both ends in one three-link window** (condition `C`),
together with crookedness, the window property and the separation of the links of `R` and `P'`. -/
theorem model_end_time_refuted' :
    IsCrookedIvF end15Rho end15Sig ∧ ModelWindow end15Rho end15Sig 0 13 Finset.univ ∧
    3 ≤ levelGap end15Rho end15Sig 0 13 ∧
    (∃ j : ℤ, j ≤ end15Sig 0 ∧ end15Rho 0 ≤ j + 2 ∧ j ≤ end15Sig (Fin.last 14) ∧
      end15Rho (Fin.last 14) ≤ j + 2) ∧
    ¬ ModelEndTime (c := 14) end15Rho end15Sig 13 := by
  refine ⟨end15_isCrookedIvF, end15_window, by decide, ⟨1, by decide, by decide, by decide,
    by decide⟩, ?_⟩
  rintro ⟨q, β, hβ, hsm, hp, h0, hc⟩
  have hc' : (β 14).val = q - 1 := hc
  have n0p : (β 0).val ≠ (β 13).val := block₃_val_ne hsm (by decide)
  have n1p : (β 1).val ≠ (β 13).val := block₃_val_ne hsm (by decide)
  have n1c : (β 1).val ≠ (β 14).val := block₃_val_ne hsm (by decide)
  have l13 := hβ.lip 13 14 rfl
  have h1 := (β 1).isLt
  omega

/-! ### What the census leaves (not proved)

Both refutations have a cause visible in the data: `C` fails (the ends are too far apart to share
a block), or the arm `[p, c]` is too short for the number of blocks the arm `[0, p]` needs. The
condition `X` — each arm `[0, p]` and `[p, c]` has a link at coarse level `0` and a link at
coarse level `K - 1` (the hypothesis of Theorem 4, on each arm) — excludes the second kind. The
census found no failure of

```
IsCrookedIvF ρ σ → 0 < p.val → p.val < c → C → X → ModelEndTime ρ σ p
```

(class `END[C+X]` of `census-batch87-model.c`; ranges and counts in `REPORT-batch87.md`). Neither
`C` nor `X` is known to follow from the hypotheses of `covering_step`.
-/

end HPC.Fold
