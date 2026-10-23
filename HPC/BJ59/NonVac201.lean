import HPC.BJ59.NonVac200
import HPC.BJ59.NonVac200b
import HPC.BJ59.Thm10Defs

/-!
# Batch 201, §7: non-vacuity of the conditions of §2

`nonvac_conditions` (statement as in the skeleton): on `[0, 1]` with the identity, the three-link
chain `nvChain 0` (centres `0, 1/2, 1`, radius `3/8`, from batch 200) is a chain in Bing–Jones's
sense with private points (the centres), and the identity is a fibre chain map of it onto itself.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-- The closure of a triadic link lies in the closed band. -/
theorem closure_nvLink_subset (i k : ℕ) :
    closure (nvLink i k) ⊆ {x : unitInterval | |(x : ℝ) - k / nvN i| ≤ 3 / (4 * nvN i)} := by
  refine closure_minimal (fun x hx => ?_)
    (isClosed_le ((continuous_subtype_val.sub continuous_const).abs) continuous_const)
  simp only [nvLink, mem_setOf_eq] at hx ⊢
  exact hx.le

/-- The centres are private points of the triadic chains. -/
theorem nvChain_private (i : ℕ) : HasPrivatePoints (nvChain i) := by
  intro j
  have hN := nvN_pos i
  refine ⟨_, nvLink_mem i j.val (by omega), fun j' hj' hcl => ?_⟩
  have h := closure_nvLink_subset i j'.val hcl
  simp only [mem_setOf_eq] at h
  rw [← sub_div, abs_div, abs_of_pos hN, div_le_div_iff₀ hN (by positivity)] at h
  have hne : (j.val : ℤ) ≠ j'.val := fun h' => hj' (Fin.ext (by omega))
  have h1 : (1 : ℝ) ≤ |(j.val : ℝ) - j'.val| := by
    rcases lt_or_gt_of_ne hne with h2 | h2
    · have : (j.val : ℝ) + 1 ≤ j'.val := by exact_mod_cast (show (j.val : ℤ) + 1 ≤ j'.val by omega)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (j'.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show (j'.val : ℤ) + 1 ≤ j.val by omega)
      rw [abs_of_nonneg (by linarith)]; linarith
  nlinarith

/-- The conditions of §2 on a non-degenerate input: `[0, 1]` with the identity, a chain of at
least three links in Bing–Jones's sense with private points, and the identity chain map. -/
theorem nonvac_conditions : ∃ (n : ℕ) (D : Chain unitInterval n), 3 ≤ n ∧ univ ⊆ D.union ∧
    IsBJChain D ∧ HasPrivatePoints D ∧ IsFibreChainMap id id D D id :=
  ⟨nvN 0 + 1, nvChain 0, by simp, nvChain_cover 0, nvChain_bj 0, nvChain_private 0,
    fun _ _ h => h, Function.surjective_id, fun _ _ h => h, fun _ _ _ _ h => h⟩

/-! ### Degenerate inputs -/

/-- One-link chains (degenerate input): on `[0, 1]` with the identity, the one-link chain has
private points and is fibre-fine, and the identity chain map satisfies Conditions A and C. -/
theorem nonvac_conditions_one :
    HasPrivatePoints (oneChain unitInterval) ∧ IsFibreFine id (oneChain unitInterval) ∧
      IsFibreChainMap id id (oneChain unitInterval) (oneChain unitInterval) id ∧
      EndCompat id id (Homeomorph.refl _) (Homeomorph.refl _) (oneChain unitInterval)
        (oneChain unitInterval) id :=
  ⟨fun j => ⟨0, mem_univ _, fun j' hj' => absurd (Subsingleton.elim j' j) hj'⟩, Or.inl rfl,
    ⟨fun _ _ h => h, Function.surjective_id, fun _ _ h => h, fun _ _ _ _ h => h⟩,
    fun _ _ h => h, fun _ _ h => h⟩

/-- Chains with no link (degenerate input): private points hold vacuously; a fibre chain map from
an empty chain forces the target to be empty (the onto clause); an empty chain is fibre-fine for
any map onto `[0, 1]` (no run covers a fibre). -/
theorem nonvac_conditions_zero {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → unitInterval) (g : Y → unitInterval) :
    (∀ D : Chain X 0, HasPrivatePoints D) ∧
      (∀ {m : ℕ} (D : Chain X 0) (E : Chain Y m) (H : Fin 0 → Fin m),
        IsFibreChainMap f g D E H → m = 0) ∧
      (Function.Surjective g → ∀ E : Chain Y 0, IsFibreFine g E) := by
  refine ⟨fun D j => j.elim0, fun {m} D E H hH => ?_, fun hg E => Or.inr ?_⟩
  · by_contra hm
    obtain ⟨j, -⟩ := hH.2.1 ⟨0, Nat.pos_of_ne_zero hm⟩
    exact j.elim0
  · intro t u v hcov
    exfalso
    obtain ⟨y, hy⟩ := hg t
    obtain ⟨j, -⟩ := mem_iUnion₂.1 (hcov (show y ∈ g ⁻¹' {t} from hy))
    exact j.elim0

end HPC.BJ59
