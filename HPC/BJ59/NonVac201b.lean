import HPC.BJ59.NonVac200b
import HPC.BJ59.NonVac201
import HPC.BJ59.Thm10Pattern

/-!
# Batch 201, §7: non-vacuity of the tools of §3

* `nonvac_point_only`, `nonvac_adjacent`: the hypotheses of `exists_point_only_of_minimal` and of
  `adjacent_of_properCover` on `[0, 1]` with the three-link chain `nvChain 0` (centres
  `0, 1/2, 1`).
* `nonvac_fibreFine`: the hypotheses of `isFibreFine_of_isEpsChain` on `[0, 1]²` with the first
  projection (`κ = 1`) and a chain of small open rectangles along one fibre.
* `nonvac_pattern`: the hypotheses of `exists_pattern` on a plane pseudo-arc `Q`, `φ` the inclusion,
  `D` the chain of `nonvac_bj_chains` shrunk to private points.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-- `0` lies in no link of `nvChain i` but the first. -/
theorem zero_notMem_nvLink (i k : ℕ) (hk : 1 ≤ k) : (0 : unitInterval) ∉ nvLink i k := by
  have hN := nvN_pos i
  simp only [nvLink, mem_setOf_eq, Set.Icc.coe_zero, zero_sub, abs_neg, not_lt]
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hN]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- `1` lies in no link of `nvChain i` but the last. -/
theorem one_notMem_nvLink (i k : ℕ) (hk : k + 1 ≤ nvN i) : (1 : unitInterval) ∉ nvLink i k := by
  have hN := nvN_pos i
  simp only [nvLink, mem_setOf_eq, Set.Icc.coe_one, not_lt]
  have hk' : (k : ℝ) + 1 ≤ nvN i := by exact_mod_cast hk
  have h1 : (k : ℝ) / nvN i ≤ 1 := (div_le_one hN).2 (by linarith)
  rw [abs_of_nonneg (by linarith), show (1 : ℝ) - k / nvN i = (nvN i - k) / nvN i by
    field_simp, div_le_div_iff₀ (by positivity) hN]
  nlinarith

/-- **Non-vacuity of `exists_point_only_of_minimal`**: on `[0, 1]`, the three-link chain `nvChain 0`,
`C = [0, 1]`, the whole run `0..2`: `C` is covered by the run and by neither shorter run. -/
theorem nonvac_point_only :
    IsPreconnected (univ : Set unitInterval) ∧
    (univ : Set unitInterval) ⊆ ⋃ (j : Fin (nvN 0 + 1)) (_ : 0 ≤ j.val ∧ j.val ≤ nvN 0),
      (nvChain 0).link j ∧
    ¬ (univ : Set unitInterval) ⊆ ⋃ (j : Fin (nvN 0 + 1)) (_ : 0 + 1 ≤ j.val ∧ j.val ≤ nvN 0),
      (nvChain 0).link j ∧
    ¬ (univ : Set unitInterval) ⊆ ⋃ (j : Fin (nvN 0 + 1)) (_ : 0 ≤ j.val ∧ j.val + 1 ≤ nvN 0),
      (nvChain 0).link j := by
  refine ⟨isPreconnected_univ, fun x hx => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (nvChain_cover 0 hx)
    exact mem_iUnion₂.2 ⟨j, ⟨Nat.zero_le _, by omega⟩, hj⟩
  · obtain ⟨j, hj, hx⟩ := mem_iUnion₂.1 (h (mem_univ 0))
    exact zero_notMem_nvLink 0 j.val hj.1 hx
  · obtain ⟨j, hj, hx⟩ := mem_iUnion₂.1 (h (mem_univ 1))
    exact one_notMem_nvLink 0 j.val hj.2 hx

/-- **Non-vacuity of `adjacent_of_properCover`**: on `[0, 1]`, the three-link chain `nvChain 0`,
`C = [0, 1]`, and `R = R' = id` on the run `0..2`. -/
theorem nonvac_adjacent :
    IsChainMap (id : Fin (nvN 0 + 1) → Fin (nvN 0 + 1)) ∧
    (∀ a : Fin (nvN 0 + 1), 0 ≤ a.val → a.val ≤ nvN 0 →
      ((nvChain 0).link (id a) ∩ (univ : Set unitInterval)).Nonempty) ∧
    (univ : Set unitInterval) ⊆ ⋃ (a : Fin (nvN 0 + 1)) (_ : 0 ≤ a.val ∧ a.val ≤ nvN 0),
      (nvChain 0).link (id a) := by
  refine ⟨fun _ _ h => h, fun a _ _ => ?_, fun x hx => ?_⟩
  · obtain ⟨p, hp⟩ := nvChain_nonempty 0 a
    exact ⟨p, hp, mem_univ _⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (nvChain_cover 0 hx)
    exact mem_iUnion₂.2 ⟨j, ⟨Nat.zero_le _, by omega⟩, hj⟩

/-- Small open rectangles along the fibre over `0` of `[0, 1]²`: the links `L₀ × L_k` of
`nvChain 2` (`19` links). -/
def nvSquareChain : Chain (unitInterval × unitInterval) (nvN 2 + 1) where
  link k := nvLink 2 0 ×ˢ nvLink 2 k
  isOpen k := (nvLink_isOpen 2 0).prod (nvLink_isOpen 2 k)
  adjacent k l := by
    rw [Set.prod_inter_prod, Set.prod_nonempty_iff, inter_self]
    have h0 : (nvLink 2 0).Nonempty := ⟨_, nvLink_mem 2 0 (Nat.zero_le _)⟩
    rw [← nvLink_inter_iff 2 k l (by omega) (by omega)]
    exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩

/-- **Non-vacuity of `isFibreFine_of_isEpsChain`**: on `[0, 1]²` with the first projection, every
fibre has two points at distance `1`, and the chain `nvSquareChain` of `19` small rectangles along
the fibre over `0` is a `1/3`-chain; hence it is fibre-fine. -/
theorem nonvac_fibreFine :
    (∀ t, ∃ p ∈ (Prod.fst : unitInterval × unitInterval → unitInterval) ⁻¹' {t},
      ∃ q ∈ (Prod.fst : unitInterval × unitInterval → unitInterval) ⁻¹' {t}, (1 : ℝ) ≤ dist p q) ∧
    IsEpsChain nvSquareChain (1 / 3) ∧ 3 ≤ nvN 2 + 1 ∧ IsFibreFine Prod.fst nvSquareChain := by
  have hfib : ∀ t, ∃ p ∈ (Prod.fst : unitInterval × unitInterval → unitInterval) ⁻¹' {t},
      ∃ q ∈ (Prod.fst : unitInterval × unitInterval → unitInterval) ⁻¹' {t},
        (1 : ℝ) ≤ dist p q := by
    intro t
    refine ⟨(t, 0), rfl, (t, 1), rfl, ?_⟩
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq]
    simp
  have heps : IsEpsChain nvSquareChain (1 / 3) := by
    intro k
    have hA := nvChain_eps 2 ⟨0, by omega⟩
    have hB := nvChain_eps 2 k
    change Bornology.IsBounded (nvLink 2 0) ∧ diam (nvLink 2 0) < 1 / 2 ^ 2 at hA
    change Bornology.IsBounded (nvLink 2 k) ∧ diam (nvLink 2 k) < 1 / 2 ^ 2 at hB
    refine ⟨hA.1.prod hB.1, lt_of_le_of_lt (b := 1 / 4) ?_ (by norm_num)⟩
    refine diam_le_of_forall_dist_le (by norm_num) fun x hx y hy => ?_
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · have := dist_le_diam_of_mem hA.1 hx.1 hy.1
      norm_num at hA; linarith
    · have := dist_le_diam_of_mem hB.1 hx.2 hy.2
      norm_num at hB; linarith
  refine ⟨hfib, heps, by simp, isFibreFine_of_isEpsChain hfib _ ?_⟩
  simpa using heps

/-- **Non-vacuity of `exists_pattern`**: a plane pseudo-arc `Q`, `φ` the inclusion, `D` a chain of
at least three links (from `nonvac_bj_chains`, shrunk to private points), and the whole run: all
hypotheses hold. -/
theorem nonvac_pattern : ∃ Q : Set Pt, IsPseudoArc Q ∧ ∃ n, 3 ≤ n ∧ ∃ D : Chain Pt n,
    IsCompact Q ∧ IsPreconnected Q ∧ Q.Nontrivial ∧
    Continuous (Subtype.val : Q → Pt) ∧ 0 ≤ n - 1 ∧ n - 1 < n ∧
    (∀ z : Q, (z : Pt) ∈ ⋃ (j : Fin n) (_ : 0 ≤ j.val ∧ j.val ≤ n - 1), D.link j) ∧
    (∀ j : Fin n, 0 ≤ j.val → j.val ≤ n - 1 → ∃ z : Q, (z : Pt) ∈ D.link j ∧
      ∀ j' : Fin n, 0 ≤ j'.val → j'.val ≤ n - 1 → j' ≠ j → (z : Pt) ∉ D.link j') := by
  obtain ⟨Q, hQ, n, hn, D, -, hQD, -, hpr⟩ := nonvac_privatePoint_shrink
  refine ⟨Q, hQ, n, hn, D, hQ.1.1.1, hQ.1.1.2.isPreconnected, hQ.2.2, continuous_subtype_val,
    Nat.zero_le _, by omega, fun z => ?_, fun j _ _ => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 (hQD z.2)
    exact mem_iUnion₂.2 ⟨j, ⟨Nat.zero_le _, by omega⟩, hj⟩
  · obtain ⟨p, ⟨hpQ, hpj⟩, hp⟩ := hpr j
    exact ⟨⟨p, hpQ⟩, hpj, fun j' _ _ hj' h => hp j' hj' (subset_closure h)⟩

end HPC.BJ59
