import HPC.Hagopian.H76Defs

/-!
# Batch 156, item B: Lemma 2 of Hagopian 1976 and the end sets

* `lemma2_aux`: the set of points to which an `ε`-homeomorphism takes `x` is open and contains `x`.
  If `h x = y` with `h` an `ε`-homeomorphism, the displacement `v ↦ ρ(v, h(v))` attains its maximum
  `m < ε` on the compact `M`; by `hagopian75_lemma4` (Effros) every `y'` in a neighbourhood `W` of `y`
  is `g(y)` for an `(ε − m)`-homeomorphism `g`, and `g ∘ h` is an `ε`-homeomorphism taking `x` to `y'`.
* `end_sets_aux`: `admissible_end_sets'` (batch 155) in the setting of §2.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

/-- **Lemma 2**, for a homogeneous compact metric space. -/
theorem lemma2_aux {Y : Type*} [MetricSpace Y] [CompactSpace Y] (hX : IsHomogeneous Y) {ε : ℝ}
    (hε : 0 < ε) (x : Y) :
    IsOpen {y : Y | ∃ h : Y ≃ₜ Y, h x = y ∧ ∀ v, dist v (h v) < ε} ∧
      x ∈ {y : Y | ∃ h : Y ≃ₜ Y, h x = y ∧ ∀ v, dist v (h v) < ε} := by
  refine ⟨isOpen_iff_forall_mem_open.2 fun y ⟨h, hxy, hh⟩ => ?_,
    ⟨Homeomorph.refl Y, rfl, fun v => by simpa using hε⟩⟩
  -- the largest displacement of `h`
  have hcont : Continuous fun v => dist v (h v) := continuous_id.dist h.continuous
  obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hcont.continuousOn
  set m := dist v₀ (h v₀)
  have hm : m < ε := hh v₀
  obtain ⟨W, hWo, hyW, hW⟩ := hagopian75_lemma4 hX (sub_pos.2 hm) y
  refine ⟨W, fun y' hy' => ?_, hWo, hyW⟩
  obtain ⟨g, hgy, hg⟩ := hW y hyW y' hy'
  refine ⟨h.trans g, by simp [hxy, hgy], fun v => ?_⟩
  have h1 : dist v (h v) ≤ m := hv₀ (mem_univ v)
  have h2 := hg (h v)
  calc dist v ((h.trans g) v) ≤ dist v (h v) + dist (h v) (g (h v)) := dist_triangle _ _ _
    _ < m + (ε - m) := add_lt_add_of_le_of_lt h1 h2
    _ = ε := by ring

/-- **End sets** (Thomas Theorem 8): a subcontinuum of `E` meeting both end sets is `E`. -/
theorem end_sets_aux {X : Type*} [MetricSpace X] {E : Set X} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {K : Set X} (hKE : K ⊆ E) (hK : Fold.Q78.IsContinuum K)
    (h0 : (K ∩ layer k 0).Nonempty) (h1 : (K ∩ layer k 1).Nonempty) : K = E := by
  obtain ⟨⟨a, b, hab⟩, hk, hk0⟩ := hE
  exact (admissible_end_sets' hab hk hk0).2 K hKE hK h0 h1

end HPC.Hagopian
