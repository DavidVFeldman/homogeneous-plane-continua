import HPC.BJ59.Thm3
import HPC.BJ59.Defs
import HPC.BJ59.Transfer

/-!
# Batch 198, library: helpers for Theorems 5 and 6 (commission 198, §6)

* `sign_persist`: two chain maps whose values are never within `1` keep the sign of their
  difference (it changes by at most `2` per step);
* `isIndecomposable_singleton`, `isArcOfContinua_id`, `isSnakeLike_univ_unitInterval`,
  `oneLinkChain`: the ingredients of the degenerate counterexample to Theorem 5 as printed.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

/-- **Sign persistence for chain maps.** If `H₁ i` and `H₂ i` are never within `1` of each other,
then `H₁ - H₂ > 1` at one index implies it at every index. -/
theorem sign_persist {n m : ℕ} {H₁ H₂ : Fin n → Fin m} (h₁ : IsChainMap H₁)
    (h₂ : IsChainMap H₂) (hne : ∀ i, 1 < ((H₁ i : ℤ) - H₂ i).natAbs) (i j : Fin n)
    (hij : 1 < (H₁ i : ℤ) - H₂ i) : 1 < (H₁ j : ℤ) - H₂ j := by
  have key : ∀ k : ℕ, ∀ hk : k < n, ∀ hi0 : 0 < n, 1 < (H₁ ⟨0, hi0⟩ : ℤ) - H₂ ⟨0, hi0⟩ →
      1 < (H₁ ⟨k, hk⟩ : ℤ) - H₂ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk hi0 h; exact h
    | succ k ih =>
      intro hk hi0 h
      have := ih (by omega) hi0 h
      have a := h₁ ⟨k+1, hk⟩ ⟨k, by omega⟩ (by simp)
      have b := h₂ ⟨k+1, hk⟩ ⟨k, by omega⟩ (by simp)
      have c := hne ⟨k+1, hk⟩
      omega
  have key' : ∀ k : ℕ, ∀ hk : k < n, ∀ hi0 : 0 < n, 1 < (H₁ ⟨k, hk⟩ : ℤ) - H₂ ⟨k, hk⟩ →
      1 < (H₁ ⟨0, hi0⟩ : ℤ) - H₂ ⟨0, hi0⟩ := by
    intro k
    induction k with
    | zero => intro hk hi0 h; exact h
    | succ k ih =>
      intro hk hi0 h
      apply ih (by omega) hi0
      have a := h₁ ⟨k+1, hk⟩ ⟨k, by omega⟩ (by simp)
      have b := h₂ ⟨k+1, hk⟩ ⟨k, by omega⟩ (by simp)
      have c := hne ⟨k, by omega⟩
      omega
  exact key j j.2 i.pos (key' i i.2 i.pos hij)

/-- A point is an indecomposable continuum (in the library's sense). -/
theorem isIndecomposable_singleton {X : Type*} [MetricSpace X] (x : X) :
    Fold.Q78.IsIndecomposable ({x} : Set X) := by
  refine ⟨⟨isCompact_singleton, isConnected_singleton⟩, fun A B hA _ hAx _ _ => Or.inl ?_⟩
  exact (Set.Nonempty.subset_singleton_iff hA.2.nonempty).1 hAx

/-- The identity of `[0, 1]` is an arc of continua (of points). -/
theorem isArcOfContinua_id : IsArcOfContinua (id : unitInterval → unitInterval) :=
  ⟨continuous_id, Function.surjective_id, fun _ => ⟨isCompact_singleton, isConnected_singleton⟩⟩

/-- `[0, 1]` is snake-like. -/
theorem isSnakeLike_univ_unitInterval : IsSnakeLike (univ : Set unitInterval) :=
  isSnakeLike_univ_of_epsMap fun ε hε => ⟨Subtype.val, continuous_subtype_val,
    fun x y h => by rw [Subtype.ext h, dist_self]; exact hε⟩

/-- The chain with one link, the whole space. -/
def oneLinkChain (X : Type*) [MetricSpace X] [Nonempty X] : Chain X 1 where
  link := fun _ => univ
  isOpen := fun _ => isOpen_univ
  adjacent := fun i j => by
    have : i = j := Subsingleton.elim _ _
    subst this
    simp only [sub_self, Int.natAbs_zero, zero_le_one, iff_true, inter_self]
    exact univ_nonempty

/-- `exp π = -1 ≠ 1` on the circle. -/
theorem circle_exp_pi_ne_one : Circle.exp Real.pi ≠ 1 := by
  intro h
  have := congrArg (fun z : Circle => (z : ℂ).re) h
  simp [Circle.coe_exp] at this
  norm_num at this

end HPC.BJ59
