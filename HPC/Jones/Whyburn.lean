import HPC.Jones.Jones48

/-!
# Batch 136, item B: Jones 1941 Theorem 4; Whyburn 1939 (6.1), (6.2), (6.21)

§3 of the batch-136 skeleton. Whyburn's standing hypothesis (*Semi-locally connected sets*,
Amer. J. Math. 61 (1939), §II, p. 737): `M` metric, connected, semi-locally-connected. Here `M` is
the whole compact space `X`.

**The proofs are not Whyburn's.** Whyburn proves (6.2) with the components `Rᵢ` of `M − V_{δᵢ}(x)`
and the finiteness given by semi-local connectedness. Here everything goes through Theorem 0 of
Jones 1948 (`theorem0`, batch 135): in a compact continuum, semi-local connectedness at `x` is
aposyndesis at every other point with respect to `x`. Hence in a semi-locally-connected continuum
the points `y` that lie with `a` in a continuum missing `x` form a set that is open and closed in
`X − x` (`whyburn_6_2`); (6.1) and (6.21) follow.
-/

namespace HPC.Jones

open Set Topology Filter Metric

section Whyburn

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Jones 1941, Theorem 4 (compact case).** An aposyndetic compact continuum is
semi-locally-connected. (In a compact space "locally peripherally bicompact" holds; also immediate
from `theorem0`.) -/
theorem semiLocConn_of_isAposyndetic (h : IsAposyndetic X) (x : X) : SemiLocConnAt x :=
  (theorem0 x).mpr fun y hy => h y x hy

/-- A semi-locally-connected continuum is aposyndetic (the converse of Jones 1941 Theorem 4, again
from `theorem0`). -/
theorem isAposyndetic_of_semiLocConn (h : ∀ z : X, SemiLocConnAt z) : IsAposyndetic X :=
  fun y x hyx => (theorem0 x).mp (h x) y hyx

/-- **Whyburn (6.1).** In a semi-locally-connected continuum, each component of `X − x` is open.

*Shape change:* the skeleton's `ha : a ≠ x` is dropped (for `a = x` the set is empty). -/
theorem whyburn_6_1 (h : ∀ z : X, SemiLocConnAt z) (x a : X) :
    IsOpen (connectedComponentIn {x}ᶜ a) := by
  refine isOpen_iff_forall_mem_open.mpr fun b hb => ?_
  have hbx : b ≠ x := connectedComponentIn_subset _ _ hb
  obtain ⟨K, V, hK, hV, hbV, hVK, hxK⟩ := isAposyndetic_of_semiLocConn h b x hbx
  refine ⟨V, ?_, hV, hbV⟩
  rw [connectedComponentIn_eq hb]
  exact hVK.trans (hK.2.isPreconnected.subset_connectedComponentIn (hVK hbV)
    (fun z hz hzx => hxK (hzx ▸ hz)))

/-- **Whyburn (6.2).** If `x` does not separate `a` and `b` (they lie in one component of
`X − x`), then some continuum contains `a` and `b` and misses `x`. -/
theorem whyburn_6_2 (h : ∀ z : X, SemiLocConnAt z) {x a b : X} (ha : a ≠ x)
    (hb : b ∈ connectedComponentIn {x}ᶜ a) :
    ∃ N : Set X, Fold.Q78.IsContinuum N ∧ a ∈ N ∧ b ∈ N ∧ x ∉ N := by
  have hap := isAposyndetic_of_semiLocConn h
  set W : Set X := {y | ∃ N : Set X, Fold.Q78.IsContinuum N ∧ a ∈ N ∧ y ∈ N ∧ x ∉ N}
  -- `W` is open
  have hWo : IsOpen W := by
    refine isOpen_iff_forall_mem_open.mpr fun y ⟨N, hN, haN, hyN, hxN⟩ => ?_
    have hyx : y ≠ x := fun hyx => hxN (hyx ▸ hyN)
    obtain ⟨K, V, hK, hV, hyV, hVK, hxK⟩ := hap y x hyx
    refine ⟨V, fun z hz => ⟨N ∪ K, ⟨hN.1.union hK.1, IsConnected.union ⟨y, hyN, hVK hyV⟩ hN.2 hK.2⟩,
      Or.inl haN, Or.inr (hVK hz), ?_⟩, hV, hyV⟩
    rintro (h1 | h1)
    · exact hxN h1
    · exact hxK h1
  -- `X − x − W` is open
  have hW'o : IsOpen ({x}ᶜ \ W) := by
    refine isOpen_iff_forall_mem_open.mpr fun y ⟨hyx, hyW⟩ => ?_
    obtain ⟨K, V, hK, hV, hyV, hVK, hxK⟩ := hap y x hyx
    refine ⟨V, fun z hz => ⟨fun hzx => hxK (hzx ▸ hVK hz), fun ⟨N, hN, haN, hzN, hxN⟩ => ?_⟩,
      hV, hyV⟩
    refine hyW ⟨N ∪ K, ⟨hN.1.union hK.1, IsConnected.union ⟨z, hzN, hVK hz⟩ hN.2 hK.2⟩, Or.inl haN,
      Or.inr (hVK hyV), ?_⟩
    rintro (h1 | h1)
    · exact hxN h1
    · exact hxK h1
  have haW : a ∈ W := ⟨{a}, ⟨isCompact_singleton, isConnected_singleton⟩, rfl, rfl,
    fun h1 => ha (mem_singleton_iff.mp h1).symm⟩
  have hsub : connectedComponentIn {x}ᶜ a ⊆ W := by
    refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union hWo hW'o
      disjoint_sdiff_right ?_ ⟨a, mem_connectedComponentIn ha, haW⟩
    intro z hz
    by_cases hzW : z ∈ W
    · exact Or.inl hzW
    · exact Or.inr ⟨connectedComponentIn_subset _ _ hz, hzW⟩
  exact hsub hb

/-- **Whyburn (6.21)**, in the form Jones 1951 uses: in a semi-locally-connected continuum, if `p`
cuts `a` from `b` (every continuum through both contains `p`), then `p` separates `a` from `b`. -/
theorem whyburn_6_21 (h : ∀ z : X, SemiLocConnAt z) {p a b : X} (hc : CutsPts p a b) :
    b ∉ connectedComponentIn {p}ᶜ a := by
  intro hb
  obtain ⟨N, hN, haN, hbN, hpN⟩ := whyburn_6_2 h hc.1 hb
  exact hpN (hc.2.2.2 N hN haN hbN)

end Whyburn

end HPC.Jones
