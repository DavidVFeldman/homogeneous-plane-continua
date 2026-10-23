import HPC.Moore.M25BRefute

/-!
# Batch 146: Mullikin 1922, Theorem 4, at `M₁ ∩ M₂ = ∅`

Mullikin's Theorem 4 (p. 154): "If `M₁` and `M₂` are two closed, connected, bounded point sets,
neither of which disconnects a plane `S`, a necessary and sufficient condition that their sum, `M`,
shall disconnect `S` is that `M̄`, the set of points common to `M₁` and `M₂`, be not connected."

Her definition of "connected" (p. 144): "A point set `M` is said to be connected if it cannot be
expressed as the sum of two mutually exclusive point sets neither of which contains a limit point of
the other." The two summands must be read as nonempty (otherwise `M = M + ∅` and no set would be
connected), and so read the empty set is connected. At `M₁ ∩ M₂ = ∅` Theorem 4 therefore says that
`M₁ + M₂` does not disconnect `S`, and this is true (`mullikin_theorem4_disjoint`, from Janiszewski's
theorem with empty intersection, `janiszewski_compact`). Under Mathlib's convention (the empty set is
not connected) the same sentence would claim that `M₁ + M₂` does disconnect `S`, which is false
(`not_mullikin_theorem4_disjoint_mathlib`: two distinct points).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

/-- **Mullikin 1922, Theorem 4, at `M₁ ∩ M₂ = ∅`** (her convention: the empty set is connected):
two disjoint compact sets neither of which separates the plane have a union that does not separate
the plane. -/
theorem mullikin_theorem4_disjoint {M₁ M₂ : Set Pt} (hM₁ : IsCompact M₁) (hM₂ : IsCompact M₂)
    (hs₁ : ¬ SeparatesPlane M₁) (hs₂ : ¬ SeparatesPlane M₂) (hd : M₁ ∩ M₂ = ∅) :
    ¬ SeparatesPlane (M₁ ∪ M₂) := by
  unfold SeparatesPlane at *
  push_neg at *
  refine ⟨nonempty_compl.2 (hM₁.union hM₂).ne_univ, ?_⟩
  refine isPreconnected_of_forall_pair fun x hx y hy => ⟨connectedComponentIn (M₁ ∪ M₂)ᶜ x,
    connectedComponentIn_subset _ _, mem_connectedComponentIn hx, ?_,
    isPreconnected_connectedComponentIn⟩
  have hx' : x ∉ M₁ ∪ M₂ := hx
  have hy' : y ∉ M₁ ∪ M₂ := hy
  have key := janiszewski_compact hM₁ hM₂ (Or.inr hd) (x := x) (y := y)
    (fun h => h.2.2 (by
      rw [hs₁.isPreconnected.connectedComponentIn (fun h' => hx' (Or.inl h'))]
      exact fun h' => hy' (Or.inl h')))
    (fun h => h.2.2 (by
      rw [hs₂.isPreconnected.connectedComponentIn (fun h' => hx' (Or.inr h'))]
      exact fun h' => hy' (Or.inr h')))
  by_contra hc
  exact key ⟨hx', hy', hc⟩

/-- Under Mathlib's convention (the empty set is not connected), Mullikin's Theorem 4 at
`M₁ ∩ M₂ = ∅` would say that the union *does* separate the plane; this is false (two distinct
points). -/
theorem not_mullikin_theorem4_disjoint_mathlib :
    ¬ ∀ M₁ M₂ : Set Pt, IsCompact M₁ → IsConnected M₁ → IsCompact M₂ → IsConnected M₂ →
      ¬ SeparatesPlane M₁ → ¬ SeparatesPlane M₂ → M₁ ∩ M₂ = ∅ → SeparatesPlane (M₁ ∪ M₂) := by
  intro h
  have hpt : ∀ p : Pt, ¬ SeparatesPlane {p} := fun p => by
    unfold SeparatesPlane
    push_neg
    exact isConnected_compl_singleton_of_one_lt_rank (by simp; norm_num) p
  have hd : ({((0 : ℝ), (0 : ℝ))} : Set Pt) ∩ {((1 : ℝ), (0 : ℝ))} = ∅ := by simp
  exact mullikin_theorem4_disjoint isCompact_singleton isCompact_singleton (hpt _) (hpt _) hd
    (h {((0 : ℝ), (0 : ℝ))} {((1 : ℝ), (0 : ℝ))} isCompact_singleton isConnected_singleton
      isCompact_singleton isConnected_singleton (hpt _) (hpt _) hd)

end HPC.Moore
