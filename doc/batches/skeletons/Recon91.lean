import HPC.Plane.Most51

/-!
# Batch 91: Bing's windows for Pacific Theorem 3; reconnaissance on Duke 1951 Theorem 10

Skeleton (save as `HPC/Plane/Recon91.lean`; add `import HPC.Plane.Recon91` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. `theorem10_1951` itself lives in `HPC/Plane/EndPoints51.lean` and is the target of §2 of
the commission; its strongest proved form goes here under a new name if the statement there is
not reached.
-/

namespace HPC.Plane

open Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **Bing's windows** (Pacific J. Math. Theorem 3, Nadler 12.13): for a monotone map `f` of a
chainable continuum `M` onto `M'`, with `δ` from uniform continuity for `ε/5`, a `δ`-chain `C`
covering `M` with every link meeting `M`, the indices `n₁ = 0 < n₂ < ⋯` defined by
`n_{i+1} = max {j : some fibre meets c(n_i) and c(j)}`, and the windows
`D(a, b) = {y ∈ M' : fibre y ⊆ c(a) ∪ ⋯ ∪ c(b)}` taken as `D(n_{3k+1}, n_{3k+5})` (last one to the end),
form an `ε`-chain of `M'` covering `M'`. Stated through its conclusion; the report records the
exact form of the chain it proves (COMMISSION-batch91.md §1). -/
theorem theorem3_HIC_windows {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsSnakeLike M)
    (hf : IsMonotoneMap f M M') {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (E : Chain Y n), IsEpsChain E ε ∧ M' ⊆ E.union ∧
      -- each link of `E` is a window of Bing's form: the points of `M'` whose fibre lies in the
      -- union of a run of consecutive links of a chain covering `M`
      ∃ (m : ℕ) (C : Chain X m), M ⊆ C.union ∧ ∀ u : Fin n, ∃ a b : ℕ, a ≤ b ∧ b < m ∧
        E.link u ∩ M' = {y | y ∈ M' ∧ M ∩ f ⁻¹' {y} ⊆ ⋃ (i : Fin m) (_ : a ≤ i.val ∧ i.val ≤ b), C.link i} := by
  sorry

/-- **The step of Bing's proof of Duke 1951 Theorem 10** (p. 659): "`M` contains a proper
subcontinuum `M''` that contains `p` and intersects each element of `D`". Prove, or refute by
the `sin(1/x)` continuum with `p` the free end of the curve and a chain whose last link meets
`M` only inside the limit bar (COMMISSION-batch91.md §2.2, Q1). -/
theorem exists_proper_meeting_all_links {M : Set X} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) {p : X} (hp : CondA M p) {m : ℕ} (D : Chain X m) (hD : M ⊆ D.union)
    (hmeet : ∀ i, (D.link i ∩ M).Nonempty) :
    ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧ ∀ i, (D.link i ∩ K).Nonempty := by
  sorry

/-- **Theorem 10 with the step as a hypothesis** (Q4, one of the candidate forms): if for the
given `D` some proper subcontinuum through `p` meets every link, the conclusion of Theorem 10
holds. To be replaced by the strongest form proved. -/
theorem theorem10_1951_of_step {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hp : CondA M p)
    (hstep : ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧
      ∀ i, (D.link i ∩ K).Nonempty) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  sorry

end HPC.Plane
