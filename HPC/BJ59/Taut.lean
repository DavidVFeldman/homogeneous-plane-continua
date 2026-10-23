import HPC.BJ59.BJChains
import HPC.Plane.Fugate66

/-!
# Batch 199 (optional item of commission 199 §7): `IsBJChain D ↔ IsTaut D`

Bing–Jones's chains (nonadjacent links at positive distance, `IsBJChain`) are exactly Fugate's
taut chains (`HPC.Plane.IsTaut`, positive infimum distance between nonadjacent links). The
commission asks for this in a compact space; compactness is not needed, since the links of a chain
are nonempty (`Chain.link_nonempty`), so the equivalence is stated in every metric space.
-/

namespace HPC.BJ59

open Set

variable {X : Type*} [MetricSpace X]

/-- For nonempty `U`, `V`, the infimum distance `IsTaut.infDist' U V` is positive iff some `δ > 0`
bounds `dist x y` below for all `x ∈ U`, `y ∈ V`. -/
theorem infDist'_pos_iff {U V : Set X} (hU : U.Nonempty) (hV : V.Nonempty) :
    0 < HPC.Plane.IsTaut.infDist' U V ↔ ∃ δ > 0, ∀ x ∈ U, ∀ y ∈ V, δ ≤ dist x y := by
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty V := hV.to_subtype
  unfold HPC.Plane.IsTaut.infDist'
  have hbdd : ∀ x : U, BddBelow (range fun y : V => dist x.1 y.1) :=
    fun x => ⟨0, by rintro _ ⟨y, rfl⟩; exact dist_nonneg⟩
  have hbdd' : BddBelow (range fun x : U => ⨅ y : V, dist x.1 y.1) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact le_ciInf fun y => dist_nonneg⟩
  constructor
  · intro h
    refine ⟨_, h, fun x hx y hy => ?_⟩
    exact (ciInf_le hbdd' ⟨x, hx⟩).trans (ciInf_le (hbdd ⟨x, hx⟩) ⟨y, hy⟩)
  · rintro ⟨δ, hδ, h⟩
    exact hδ.trans_le (le_ciInf fun x => le_ciInf fun y => h x.1 x.2 y.1 y.2)

/-- **Bing–Jones chains are Fugate's taut chains** (commission 199 §7, optional), in any metric
space. -/
theorem isBJChain_iff_isTaut {n : ℕ} (D : Chain X n) : IsBJChain D ↔ HPC.Plane.IsTaut D := by
  have key : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs ↔
      (1 < (i.val : ℤ) - j.val ∨ 1 < (j.val : ℤ) - i.val) := fun i j => by omega
  unfold IsBJChain HPC.Plane.IsTaut
  refine forall₂_congr fun i j => ?_
  rw [key, infDist'_pos_iff (D.link_nonempty i) (D.link_nonempty j)]

end HPC.BJ59
