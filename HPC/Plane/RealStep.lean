import HPC.Plane.StdStep

/-!
# The planar step for tame chains

Batch 84. Transport of `std_step` through a plane homeomorphism `Φ`: the coarse chain is the tame
chain `Φ(stdRect j)`, the fine chain is `Φ(Ψ(stdRect t))`. Uniform continuity of `Φ` on the
compact region of the coarse chain turns "small in standard coordinates" into "diameter at most
`ε`".
-/

namespace HPC.Plane

open Set Metric

theorem isCompact_zone (j : ℕ) : IsCompact (zone j) := isCompact_Icc.prod isCompact_Icc

theorem isCompact_closure_stdRect (j : ℕ) : IsCompact (closure (stdRect j)) := by
  rw [closure_stdRect]; exact isCompact_Icc.prod isCompact_Icc

theorem tameChain_link_bounded (Φ : Pt ≃ₜ Pt) (m : ℕ) (j : Fin m) :
    Bornology.IsBounded ((tameChain Φ m).link j) := by
  rw [tameChain_link]
  exact ((isCompact_closure_stdRect j).image Φ.continuous).isBounded.subset
    (image_mono subset_closure)

theorem trans_image (Ψ Φ : Pt ≃ₜ Pt) (S : Set Pt) : (Ψ.trans Φ) '' S = Φ '' (Ψ '' S) := by
  rw [image_image]; rfl

/-- **The planar step for tame chains.** -/
theorem real_step (Φ : Pt ≃ₜ Pt) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 12 ≤ N ∧ ∀ (n : ℕ) (x : Fin n → Fin m), 0 < n → Joints.UnitSteps x →
      Joints.Slow x N → ∃ Ψ : Pt ≃ₜ Pt,
        (∀ t : Fin n, closure ((tameChain (Ψ.trans Φ) n).link t) ⊆ (tameChain Φ m).link (x t)) ∧
        (∀ (t : Fin n) (l : Fin m),
          ((tameChain (Ψ.trans Φ) n).link t ∩ (tameChain Φ m).link l).Nonempty →
          ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t') ∧
        (∀ t : Fin n, diam ((tameChain (Ψ.trans Φ) n).link t) ≤ ε ∨
          ∃ k : ℕ, k < m ∧ (tameChain (Ψ.trans Φ) n).link t ⊆ Φ '' zone k) ∧
        (∀ t : ℕ, t < n → Bornology.IsBounded ((Ψ.trans Φ) '' zone t) ∧
          diam ((Ψ.trans Φ) '' zone t) ≤ ε) ∧
        (∀ (h2 : 2 ≤ n), (x ⟨0, by omega⟩ : ℕ) = 0 → (x ⟨1, by omega⟩ : ℕ) = 0 →
          (Ψ.trans Φ) '' boxA ⊆ Φ '' boxA) ∧
        (∀ (h2 : 2 ≤ n), (x ⟨n - 1, by omega⟩ : ℕ) = m - 1 → (x ⟨n - 2, by omega⟩ : ℕ) = m - 1 →
          (Ψ.trans Φ) '' boxB n ⊆ Φ '' boxB m) := by
  have huc : UniformContinuousOn Φ (region m) :=
    (isCompact_region m).uniformContinuousOn_of_continuous Φ.continuous.continuousOn
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨N, hN, hstep⟩ := std_step hm (half_pos hδ)
  refine ⟨N, hN, fun n x hn hx hs => ?_⟩
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6⟩ := hstep n x hn hx hs
  -- images of small subsets of the region are small
  have small : ∀ S : Set Pt, S ⊆ region m → (∀ p ∈ S, ∀ q ∈ S, dist p q ≤ δ / 2) →
      diam (Φ '' S) ≤ ε := by
    intro S hS hd
    refine diam_le_of_forall_dist_le hε.le ?_
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact (hδε p (hS hp) q (hS hq) (lt_of_le_of_lt (hd p hp q hq) (half_lt_self hδ))).le
  have inreg : ∀ t : Fin n, Ψ '' closure (stdRect t) ⊆ region m := fun t =>
    (h1 t).trans (subset_closure.trans (closure_stdRect_subset_region (x t)))
  refine ⟨Ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [tameChain_link, tameChain_link, trans_image, ← Φ.image_closure, ← Ψ.image_closure]
    exact image_mono (h1 t)
  · intro t l h
    rw [tameChain_link, tameChain_link, trans_image, ← image_inter Φ.injective,
      image_nonempty] at h
    exact h2 t l h
  · intro t
    rw [tameChain_link, trans_image]
    rcases h3 t with h | ⟨k, hk, hz⟩
    · left
      refine (diam_mono (image_mono (image_mono subset_closure)) ?_).trans
        (small _ (inreg t) h)
      exact ((isCompact_closure_stdRect t).image Ψ.continuous |>.image Φ.continuous).isBounded
    · right
      exact ⟨k, hk, image_mono ((image_mono subset_closure).trans hz)⟩
  · intro t ht
    rw [trans_image]
    exact ⟨((isCompact_zone t).image Ψ.continuous |>.image Φ.continuous).isBounded,
      small _ (h4 t ht).1 (h4 t ht).2⟩
  · intro h2' a b
    rw [trans_image]; exact image_mono (h5 h2' a b)
  · intro h2' a b
    rw [trans_image]; exact image_mono (h6 h2' a b)

end HPC.Plane
