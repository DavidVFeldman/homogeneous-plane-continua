import HPC.Fold.Theorem3Pair

/-!
# Batch 124, item 1 (Q3): the only-clauses of Bing's Theorem 4 as printed

COMMISSION-batch124.md, Q3, second half. `Theorem4LiteralND` (Theorem 4 as printed, outside the
degenerate case of batch 123) is **false**: with three coarse links and `r < s` the only-clause at
`d_r` can fail (`not_theorem4LiteralND`). The example lives in `ℕ` (a discrete metric space, so
every set is open): five fine links, `d₀ ⊆ d₁`, `r = 0`, `s = 1`. Any consolidation with `d₁` in the
last block and `d₀` only in the first has a single block, and the union of all of `E` lies in no two
adjacent links of `D`.
-/

namespace HPC.Fold

open HPC HPC.Chain

/-- The coarse links of the example. -/
def onlyCoarseF : Fin 3 → Finset ℕ := ![{0, 1, 5}, {1, 2, 4, 5}, {2, 3, 4}]

/-- The fine links of the example: `d₀ ⊆ d₁`. -/
def onlyFineF : Fin 5 → Finset ℕ := ![{5}, {4, 5}, {2, 3, 4}, {1, 2}, {0, 1}]

theorem coe_inter_nonempty_iff (A B : Finset ℕ) :
    ((A : Set ℕ) ∩ (B : Set ℕ)).Nonempty ↔ (A ∩ B).Nonempty := by
  rw [← Finset.coe_inter, Finset.coe_nonempty]

/-- The coarse chain of the example. -/
def onlyCoarse : Chain ℕ 3 where
  link t := (onlyCoarseF t : Set ℕ)
  isOpen _ := isOpen_discrete _
  adjacent s t := by
    rw [coe_inter_nonempty_iff]
    revert s t; decide

/-- The fine chain of the example. -/
def onlyFine : Chain ℕ 5 where
  link t := (onlyFineF t : Set ℕ)
  isOpen _ := isOpen_discrete _
  adjacent s t := by
    rw [coe_inter_nonempty_iff]
    revert s t; decide

theorem onlyFine_crooked : onlyFine.IsCrookedIn' onlyCoarse := by
  refine ⟨fun t => ?_, fun h k hk => absurd hk (by omega)⟩
  refine ⟨![0, 1, 2, 1, 0] t, ?_⟩
  show (onlyFineF t : Set ℕ) ⊆ (onlyCoarseF (![0, 1, 2, 1, 0] t) : Set ℕ)
  rw [Finset.coe_subset]
  revert t; decide

/-- **Bing's Theorem 4 as printed is false with three coarse links, also for `r < s`**: the
only-clause at `d_r` fails in the example (`d₀ ⊆ d₁`, `r = 0`, `s = 1`). -/
theorem not_theorem4LiteralND : ¬ Theorem4LiteralND := by
  intro h
  obtain ⟨q, β, hβ, h0, hq, honly, -, hblk⟩ :=
    h ℕ 5 3 (by norm_num) onlyFine onlyCoarse onlyFine_crooked 0 1 (by decide)
      ⟨0, le_rfl, by decide, ⟨5, Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide)⟩⟩
      ⟨1, by decide, le_rfl, ⟨4, Finset.mem_coe.mpr (by decide), Finset.mem_coe.mpr (by decide)⟩⟩
      (Or.inl (by decide))
  by_cases hne : β 1 = β 0
  · -- a single block
    have hq1 : q = 1 := by
      have := congrArg Fin.val hne; omega
    subst hq1
    obtain ⟨j, hj⟩ := hblk 0
    have hmem : ∀ (t : Fin 5) (x : ℕ), x ∈ onlyFineF t → x ∈ onlyCoarse.unionRange j 2 := by
      intro t x hx
      apply hj
      rw [ofBlocks_link]
      exact Set.mem_biUnion (show t ∈ {t | β t = 0} from Subsingleton.elim _ _)
        (show x ∈ (onlyFineF t : Set ℕ) from hx)
    obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (hmem 4 0 (by decide))
    obtain ⟨b, hb1, hb2, hb3, hb4⟩ := mem_unionRange.mp (hmem 2 3 (by decide))
    have ha : a = 0 := by
      interval_cases a
      · rfl
      · simp [onlyCoarse, onlyCoarseF] at ha4
      · simp [onlyCoarse, onlyCoarseF] at ha4
    subst ha
    have hj0 : j = 0 := by omega
    subst hj0
    interval_cases b
    · simp [onlyCoarse, onlyCoarseF] at hb4
    · simp [onlyCoarse, onlyCoarseF] at hb4
  · -- `d₀ ⊆ d₁` lies in the last block too
    refine honly (β 1) hne ?_
    intro x hx
    rw [ofBlocks_link]
    have hx' : x ∈ (onlyFineF 1 : Set ℕ) := by
      have : (onlyFineF 0 : Set ℕ) ⊆ (onlyFineF 1 : Set ℕ) := by
        rw [Finset.coe_subset]; decide
      exact this hx
    exact Set.mem_biUnion (show (1 : Fin 5) ∈ {t | β t = β 1} from rfl) hx'

/-- **Theorem 4 as printed, with at least four coarse links** (open). `not_theorem4LiteralND`
refutes the only-clauses with three coarse links; the model census of batch 124 found no failure
with four or five (REPORT-batch124 §Q3, which also states the obstruction). -/
def Theorem4LiteralGe4 : Prop :=
  ∀ (X : Type) [MetricSpace X] (n k : ℕ) (hk : 4 ≤ k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ r s : Fin n, r ≤ s →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty) →
    (∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2

end HPC.Fold
