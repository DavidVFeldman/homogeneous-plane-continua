import HPC.Jones.Jones55T2

/-!
# Batch 149, item A: order of a point (Menger–Urysohn)

The two definitions of the batch-149 skeleton (`OrderLE`, `HasOrder`, verbatim), the invariance of
order under homeomorphisms (`hasOrder_homeomorph`), and three general facts used for Menger's
theorem (`Jones49Menger.lean`):

* `orderLE_subtype`: order does not increase on passing to a subspace;
* `not_orderLE_two_of_triod`: three connected sets through `p`, pairwise meeting only in `p`, each
  with a point other than `p`, make the order of `p` at least 3 (in a `T₁` space);
* `locallyConnectedSpace_of_orderLE`: a compact metric continuum each of whose points has finite
  order is locally connected (boundary bumping: each component of `V̄` meets the finite frontier of
  `V`, so `V̄` has finitely many components and the one containing `p` is a neighbourhood of `p`).
-/

namespace HPC.Jones

open Set Topology Metric

section Order

variable {X : Type*} [TopologicalSpace X]

/-- **Menger–Urysohn order `≤ n`**: `p` has arbitrarily small open neighbourhoods whose frontier has
at most `n` points. Check against Menger (*Kurventheorie*, Ch. IV) and Whyburn (Ch. III §2, p. 48)
and record any difference. -/
def OrderLE (p : X) (n : ℕ) : Prop :=
  ∀ U ∈ 𝓝 p, ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ (frontier V).Finite ∧ (frontier V).ncard ≤ n

/-- `p` is a point **of order `n`**: order `≤ n` and not `≤ n − 1`. -/
def HasOrder (p : X) (n : ℕ) : Prop := OrderLE p n ∧ ∀ m < n, ¬ OrderLE p m

/-- One direction of the invariance of `OrderLE`. -/
theorem OrderLE.homeomorph {Y : Type*} [TopologicalSpace Y] (h : X ≃ₜ Y) {p : X} {n : ℕ}
    (hp : OrderLE p n) : OrderLE (h p) n := by
  intro U hU
  have hU' : h ⁻¹' U ∈ 𝓝 p := h.continuous.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVo, hpV, hVU, hfin, hcard⟩ := hp _ hU'
  refine ⟨h '' V, h.isOpenMap V hVo, mem_image_of_mem _ hpV, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact hVU hv
  · rw [← h.image_frontier]; exact hfin.image _
  · rw [← h.image_frontier, ncard_image_of_injective _ h.injective]; exact hcard

theorem orderLE_homeomorph {Y : Type*} [TopologicalSpace Y] (h : X ≃ₜ Y) {p : X} {n : ℕ} :
    OrderLE p n ↔ OrderLE (h p) n :=
  ⟨fun hp => hp.homeomorph h, fun hp => by simpa using hp.homeomorph h.symm⟩

/-- Order is a topological invariant. -/
theorem hasOrder_homeomorph {Y : Type*} [TopologicalSpace Y] (h : X ≃ₜ Y) {p : X} {n : ℕ} :
    HasOrder p n ↔ HasOrder (h p) n := by
  unfold HasOrder
  simp only [← orderLE_homeomorph h]

/-- Order does not increase on passing to a subspace. -/
theorem orderLE_subtype {W : Set X} {p : X} (hp : p ∈ W) {n : ℕ} (h : OrderLE p n) :
    OrderLE (⟨p, hp⟩ : W) n := by
  intro U hU
  rw [nhds_subtype, Filter.mem_comap] at hU
  obtain ⟨U', hU', hU'U⟩ := hU
  obtain ⟨V, hVo, hpV, hVU, hfin, hcard⟩ := h U' hU'
  have hsub : frontier ((↑) ⁻¹' V : Set W) ⊆ (↑) ⁻¹' frontier V := by
    rw [frontier, frontier, (hVo.preimage continuous_subtype_val).interior_eq, hVo.interior_eq]
    exact diff_subset_diff_left (closure_subset_preimage_closure_image continuous_subtype_val
      |>.trans (preimage_mono (image_preimage_subset _ _ |> closure_mono)))
  have hfin' : ((↑) ⁻¹' frontier V : Set W).Finite := hfin.preimage Subtype.val_injective.injOn
  refine ⟨((↑) : W → X) ⁻¹' V, hVo.preimage continuous_subtype_val, show p ∈ V from hpV,
    fun x hx => hU'U (show (x : X) ∈ U' from hVU hx), hfin'.subset hsub, ?_⟩
  calc (frontier ((↑) ⁻¹' V : Set W)).ncard ≤ ((↑) ⁻¹' frontier V : Set W).ncard :=
        ncard_le_ncard hsub hfin'
    _ ≤ (frontier V).ncard :=
        ncard_le_ncard_of_injOn (↑) (fun a ha => ha) Subtype.val_injective.injOn hfin
    _ ≤ n := hcard

/-- A preconnected set through a point of an open set `V`, with a point outside `V`, meets the
frontier of `V`. -/
theorem meets_frontier_of_isPreconnected {T V : Set X} (hT : IsPreconnected T) {p x : X}
    (hpT : p ∈ T) (hpV : p ∈ V) (hxT : x ∈ T) (hxV : x ∉ V) : (T ∩ frontier V).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
  exact hxV (HPC.Moore.Gen.conn_sub_of_frontier hT h ⟨p, hpT, hpV⟩ hxT)

/-- **Triods raise the order.** Three preconnected sets through `p`, pairwise meeting only in `p`,
each containing a point other than `p`: then `p` is not of order `≤ 2`. -/
theorem not_orderLE_two_of_triod [T1Space X] {p : X} {T₁ T₂ T₃ : Set X}
    (h₁ : IsPreconnected T₁) (h₂ : IsPreconnected T₂) (h₃ : IsPreconnected T₃)
    (hp₁ : p ∈ T₁) (hp₂ : p ∈ T₂) (hp₃ : p ∈ T₃)
    (hn₁ : ∃ x ∈ T₁, x ≠ p) (hn₂ : ∃ x ∈ T₂, x ≠ p) (hn₃ : ∃ x ∈ T₃, x ≠ p)
    (h12 : T₁ ∩ T₂ ⊆ {p}) (h13 : T₁ ∩ T₃ ⊆ {p}) (h23 : T₂ ∩ T₃ ⊆ {p}) : ¬ OrderLE p 2 := by
  intro hp
  obtain ⟨x₁, hx₁, hx₁p⟩ := hn₁
  obtain ⟨x₂, hx₂, hx₂p⟩ := hn₂
  obtain ⟨x₃, hx₃, hx₃p⟩ := hn₃
  have hU : ({x₁, x₂, x₃}ᶜ : Set X) ∈ 𝓝 p := by
    refine (Set.toFinite _).isClosed.isOpen_compl.mem_nhds ?_
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hx₁p.symm, hx₂p.symm, hx₃p.symm⟩
  obtain ⟨V, hVo, hpV, hVU, hfin, hcard⟩ := hp _ hU
  have hout : ∀ {x}, x = x₁ ∨ x = x₂ ∨ x = x₃ → x ∉ V := by
    intro x hx hxV
    have := hVU hxV
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at this
    rcases hx with rfl | rfl | rfl
    · exact this.1 rfl
    · exact this.2.1 rfl
    · exact this.2.2 rfl
  obtain ⟨y₁, hy₁T, hy₁F⟩ := meets_frontier_of_isPreconnected h₁ hp₁ hpV hx₁ (hout (Or.inl rfl))
  obtain ⟨y₂, hy₂T, hy₂F⟩ :=
    meets_frontier_of_isPreconnected h₂ hp₂ hpV hx₂ (hout (Or.inr (Or.inl rfl)))
  obtain ⟨y₃, hy₃T, hy₃F⟩ :=
    meets_frontier_of_isPreconnected h₃ hp₃ hpV hx₃ (hout (Or.inr (Or.inr rfl)))
  have hyp : ∀ {y}, y ∈ frontier V → y ≠ p := by
    rintro y hy rfl
    exact (disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hVo.inter_frontier_eq)) hpV hy
  have hne : ∀ {S T : Set X} {y z : X}, S ∩ T ⊆ {p} → y ∈ S → z ∈ T → y ∈ frontier V → y ≠ z := by
    rintro S T y z hST hy hz hyF rfl
    exact hyp hyF (hST ⟨hy, hz⟩)
  have h3 : ({y₁, y₂, y₃} : Set X).ncard = 3 := by
    rw [ncard_insert_of_notMem, ncard_pair (hne h23 hy₂T hy₃T hy₂F)]
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne h12 hy₁T hy₂T hy₁F, hne h13 hy₁T hy₃T hy₁F⟩
  have : ({y₁, y₂, y₃} : Set X).ncard ≤ (frontier V).ncard := by
    refine ncard_le_ncard ?_ hfin
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  omega

/-- The connected component of a point in a closed set is closed. -/
theorem isClosed_connectedComponentIn_of_isClosed {F : Set X} (hF : IsClosed F) (x : X) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.1 ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset _ _) hF)
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

end Order

section LocConn

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- **Local connectedness from finite order.** A compact metric continuum each of whose points has
finite order is locally connected. -/
theorem locallyConnectedSpace_of_orderLE (h : ∀ p : Y, ∃ n, OrderLE p n) :
    LocallyConnectedSpace Y := by
  classical
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro p U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨n, hn⟩ := h p
  obtain ⟨V, hVo, hpV, hVU, hfin, -⟩ := hn _ (closedBall_mem_nhds p (half_pos hε))
  have hVcl : closure V ⊆ U := (closure_minimal hVU isClosed_closedBall).trans
    ((closedBall_subset_ball (half_lt_self hε)).trans hεU)
  by_cases hfull : closure V = univ
  · exact ⟨univ, Filter.univ_mem, isPreconnected_univ, fun z _ => hVcl (hfull ▸ mem_univ z)⟩
  set F := closure V
  have hcov : ∀ z ∈ F, ∃ f ∈ frontier V, z ∈ connectedComponentIn F f := by
    intro z hz
    obtain ⟨K, hK, hKF, hzK, w, hwK, hw⟩ := HPC.Plane.exists_continuum_bump_closed
      (M := univ) ⟨isCompact_univ, isConnected_univ⟩ isClosed_closure (subset_univ _) hfull hz
    have hwV : w ∉ V := by
      intro hwV
      rw [← compl_eq_univ_diff, closure_compl] at hw
      exact hw (interior_maximal subset_closure hVo hwV)
    have hwF : w ∈ frontier V := by
      rw [hVo.frontier_eq]; exact ⟨hKF hwK, hwV⟩
    refine ⟨w, hwF, ?_⟩
    exact hK.2.isPreconnected.subset_connectedComponentIn hwK hKF hzK
  set D : Set Y := ⋃ f ∈ {f ∈ frontier V | p ∉ connectedComponentIn F f}, connectedComponentIn F f
  have hDcl : IsClosed D :=
    (hfin.subset (sep_subset _ _)).isClosed_biUnion fun f _ =>
      isClosed_connectedComponentIn_of_isClosed isClosed_closure f
  have hpD : p ∉ D := by
    intro hpD
    obtain ⟨f, ⟨-, hpf⟩, hpf'⟩ := mem_iUnion₂.1 hpD
    exact hpf hpf'
  refine ⟨connectedComponentIn F p, ?_, isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset _ _).trans hVcl⟩
  refine Filter.mem_of_superset ((hVo.sdiff hDcl).mem_nhds ⟨hpV, hpD⟩) ?_
  rintro z ⟨hzV, hzD⟩
  obtain ⟨f, hf, hzf⟩ := hcov z (subset_closure hzV)
  by_cases hpf : p ∈ connectedComponentIn F f
  · rw [← connectedComponentIn_eq hpf]; exact hzf
  · exact absurd (mem_iUnion₂.2 ⟨f, ⟨hf, hpf⟩, hzf⟩) hzD

end LocConn

end HPC.Jones
