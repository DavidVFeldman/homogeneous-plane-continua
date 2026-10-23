import HPC.Jones.Jones49C

/-!
# Batch 152, items A and C: joining points of a complementary domain near a non-cut point

Whyburn's step 3 (*Semi-locally-connected sets*, 1939, pp. 747–748) uses a θ-curve separation and
"a theorem of R. L. Moore" (a simple closed curve `C ⊂ J + C_ε` bounding a region `E ∋ 0` inside
`I·V_ε(p)`). Here both are replaced by one application of Janiszewski's theorem for plane
compacta (`HPC.Moore.janiszewski_compact`):

* `join_in_domain`: let `N ⊆ M` be a continuum containing `M − V_ε(p)`, and let `W` be the component
  of `V_ε(p) − N` containing `p`. Then any two points of a complementary domain `R` of `M` that lie
  in `W` lie in one component of `W − M`. (With `K = (M ∩ W̄) ∪ N` and `L = Wᶜ ∩ B̄(p, ρ)`,
  `K ∩ L = N` is connected; `K ⊆ M` does not separate points of `R`, and `L` does not separate
  points of `W`; so `K ∪ L` does not separate them, and the joining component lies in `W − M`.)
* `local_join_of_noncut`: with (6.22) (`whyburn39_6_22_sec14`), near a non-cut point `p` of a compact
  semi-locally-connected plane continuum, any two points of `R` close to `p` lie in a connected
  subset of `R` close to `p`.
-/

namespace HPC.Jones.Sec14

open Set Topology Metric Filter HPC.Plane

/-- **The joining lemma** (replaces Whyburn's θ-curve step and Moore's curve `C`). `M` compact, `N`
a closed connected subset of `M` containing every point of `M` at distance `≥ ε` from `p`, and `W`
the component of `(N ∪ V_ε(p)ᶜ)ᶜ` containing `p`. Two points `a`, `b` of a complementary domain of
`M` which lie in `W` lie in the same component of `W − M`. -/
theorem join_in_domain {M N : Set Pt} (hM : IsCompact M) (hN : IsClosed N) (hNc : IsConnected N)
    (hNM : N ⊆ M) {p : Pt} {ε : ℝ} (hout : M \ ball p ε ⊆ N) {x a b : Pt}
    (ha : a ∈ connectedComponentIn Mᶜ x) (hb : b ∈ connectedComponentIn Mᶜ x)
    (haW : a ∈ connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p)
    (hbW : b ∈ connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p) :
    b ∈ connectedComponentIn (connectedComponentIn (N ∪ (ball p ε)ᶜ)ᶜ p ∩ Mᶜ) a := by
  set Q := N ∪ (ball p ε)ᶜ with hQdef
  set W := connectedComponentIn Qᶜ p with hWdef
  set R := connectedComponentIn Mᶜ x
  have hQcl : IsClosed Q := hN.union isOpen_ball.isClosed_compl
  have hWo : IsOpen W := hQcl.isOpen_compl.connectedComponentIn
  have hWQ : W ⊆ Qᶜ := connectedComponentIn_subset _ _
  have hWball : W ⊆ ball p ε := fun z hz => by
    have := hWQ hz
    simp only [hQdef, mem_compl_iff, mem_union, not_or, not_not] at this
    exact this.2
  have hfr : frontier W ⊆ Q := by
    have := HPC.Moore.frontier_connectedComponentIn_subset hQcl.isOpen_compl p
    rwa [compl_compl] at this
  have hRM : R ⊆ Mᶜ := connectedComponentIn_subset _ _
  have hNc' : IsCompact N := hM.of_isClosed_subset hN hNM
  obtain ⟨r, hr⟩ := hM.isBounded.subset_closedBall p
  set ρ := max r ε + 1
  have hrρ : r < ρ := by simp only [ρ]; linarith [le_max_left r ε]
  have hερ : ε < ρ := by simp only [ρ]; linarith [le_max_right r ε]
  set K := (M ∩ closure W) ∪ N
  set L := Wᶜ ∩ closedBall p ρ
  have hKM : K ⊆ M := union_subset inter_subset_left hNM
  have hKc : IsCompact K := (hM.inter_right isClosed_closure).union hNc'
  have hLc : IsCompact L := (isCompact_closedBall p ρ).inter_left hWo.isClosed_compl
  have hNW : N ∩ W = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzN hzW
    exact hWQ hzW (Or.inl hzN)
  have hKL : K ∩ L = N := by
    apply Subset.antisymm
    · rintro z ⟨hzK, hzW, -⟩
      rcases hzK with ⟨hzM, hzcl⟩ | hzN
      · have hzfr : z ∈ frontier W := by
          rw [hWo.frontier_eq]; exact ⟨hzcl, hzW⟩
        rcases hfr hzfr with h | h
        · exact h
        · exact hout ⟨hzM, h⟩
      · exact hzN
    · intro z hzN
      refine ⟨Or.inr hzN, fun hzW => ?_, ?_⟩
      · have : z ∈ N ∩ W := ⟨hzN, hzW⟩
        rw [hNW] at this; exact this
      · exact closedBall_subset_closedBall hrρ.le (hr (hNM hzN))
  have haM : a ∉ M := hRM ha
  have hbM : b ∉ M := hRM hb
  have hnK : ¬ SeparatesPts K a b := by
    rintro ⟨-, -, h⟩
    exact h ((isPreconnected_connectedComponentIn).subset_connectedComponentIn ha
      (hRM.trans (compl_subset_compl.2 hKM)) hb)
  have hnL : ¬ SeparatesPts L a b := by
    rintro ⟨-, -, h⟩
    have hWL : W ⊆ Lᶜ := fun z hz hzL => hzL.1 hz
    exact h ((isPreconnected_connectedComponentIn).subset_connectedComponentIn haW hWL hbW)
  have hint : IsConnected (K ∩ L) ∨ K ∩ L = ∅ := Or.inl (hKL ▸ hNc)
  have hJ := HPC.Moore.janiszewski_compact hKc hLc hint hnK hnL
  have haKL : a ∉ K ∪ L := by
    rintro (h | h)
    · exact haM (hKM h)
    · exact h.1 haW
  have hbKL : b ∉ K ∪ L := by
    rintro (h | h)
    · exact hbM (hKM h)
    · exact h.1 hbW
  have hbC : b ∈ connectedComponentIn (K ∪ L)ᶜ a := by
    by_contra h
    exact hJ ⟨haKL, hbKL, h⟩
  set C := connectedComponentIn (K ∪ L)ᶜ a
  have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCKL : C ⊆ (K ∪ L)ᶜ := connectedComponentIn_subset _ _
  have haC : a ∈ C := mem_connectedComponentIn haKL
  -- `C` stays inside `B(p, ρ)`: the square of radius `ρ` lies in `L`
  have hCin : C ⊆ {z | dist z p < ρ} := by
    have hsub : C ⊆ {z | dist z p < ρ} ∪ {z | ρ < dist z p} := by
      intro z hz
      rcases lt_trichotomy (dist z p) ρ with h | h | h
      · exact Or.inl h
      · exfalso
        refine hCKL hz (Or.inr ⟨fun hzW => ?_, mem_closedBall.2 h.le⟩)
        have := mem_ball.1 (hWball hzW)
        linarith
      · exact Or.inr h
    refine hCc.subset_left_of_subset_union (isOpen_lt (continuous_id.dist continuous_const)
      continuous_const) (isOpen_lt continuous_const (continuous_id.dist continuous_const)) ?_
      hsub ⟨a, haC, ?_⟩
    · rw [Set.disjoint_left]
      intro z h1 h2
      have h1' : dist z p < ρ := h1
      have h2' : ρ < dist z p := h2
      linarith
    · show dist a p < ρ
      have := mem_ball.1 (hWball haW)
      linarith
  have hCWM : C ⊆ W ∩ Mᶜ := by
    intro z hz
    have hzKL := hCKL hz
    have hzρ : dist z p < ρ := hCin hz
    have hzW : z ∈ W := by
      by_contra h
      exact hzKL (Or.inr ⟨h, mem_closedBall.2 hzρ.le⟩)
    refine ⟨hzW, fun hzM => hzKL (Or.inl (Or.inl ⟨hzM, subset_closure hzW⟩))⟩
  exact hCc.subset_connectedComponentIn haC hCWM hbC

/-- **Step 3 of Whyburn's proof, in joining form.** Near a non-cut point `p` of a compact
semi-locally-connected plane continuum `M`, a complementary domain `R` of `M` is locally connected
in the following uniform sense: for every `ε > 0` there is `δ > 0` such that any two points of `R`
within `δ` of `p` lie in a connected subset of `R` within `ε` of `p`. From (6.22)
(`whyburn39_6_22_sec14`): `N` is the closure of the component of `M − V_δ(p)` containing
`M − V_ε(p)`, and `join_in_domain` applies, since `V_δ(p)` lies in the component `W` of `p`. -/
theorem local_join_of_noncut {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {p : M} (hpc : IsConnected ({p}ᶜ : Set M)) {ε : ℝ}
    (hε : 0 < ε) (x : Pt) :
    ∃ δ > 0, ∀ a ∈ connectedComponentIn Mᶜ x, ∀ b ∈ connectedComponentIn Mᶜ x,
      a ∈ ball (p : Pt) δ → b ∈ ball (p : Pt) δ →
      ∃ C ⊆ connectedComponentIn Mᶜ x, IsPreconnected C ∧ a ∈ C ∧ b ∈ C ∧
        C ⊆ ball (p : Pt) ε := by
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hM
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.1 hMc
  obtain ⟨δ, hδ, hδε, c, hc, hsub⟩ := whyburn39_6_22_sec14 hS hpc hε
  set N₀ : Set Pt := Subtype.val '' connectedComponentIn (ball p δ)ᶜ c
  set N := closure N₀
  have hMcl := hM.isClosed
  have hN₀M : N₀ ⊆ M \ ball (p : Pt) δ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, fun h => ?_⟩
    have := connectedComponentIn_subset _ _ hz
    exact this (by rw [mem_ball, Subtype.dist_eq]; exact mem_ball.1 h)
  have hNM' : N ⊆ M \ ball (p : Pt) δ := closure_minimal hN₀M (hMcl.sdiff isOpen_ball)
  have hNc : IsConnected N :=
    ((isConnected_connectedComponentIn_iff.2 hc).image _
      continuous_subtype_val.continuousOn).closure
  have hout : M \ ball (p : Pt) ε ⊆ N := by
    rintro z ⟨hzM, hzb⟩
    apply subset_closure
    refine ⟨⟨z, hzM⟩, hsub ?_, rfl⟩
    intro h
    apply hzb
    rw [mem_ball, Subtype.dist_eq] at h
    exact mem_ball.2 h
  set W := connectedComponentIn (N ∪ (ball (p : Pt) ε)ᶜ)ᶜ (p : Pt)
  have hballW : ball (p : Pt) δ ⊆ W := by
    refine (convex_ball _ _).isPreconnected.subset_connectedComponentIn (mem_ball_self hδ) ?_
    intro z hz hzQ
    rcases hzQ with h | h
    · exact (hNM' h).2 hz
    · exact h (ball_subset_ball hδε.le hz)
  have hWball : W ⊆ ball (p : Pt) ε := fun z hz => by
    have := (connectedComponentIn_subset _ _ hz : z ∈ (N ∪ (ball (p : Pt) ε)ᶜ)ᶜ)
    simp only [mem_compl_iff, mem_union, not_or, not_not] at this
    exact this.2
  refine ⟨δ, hδ, fun a ha b hb haδ hbδ => ?_⟩
  have hj := join_in_domain hM isClosed_closure hNc (fun z hz => (hNM' hz).1) hout ha hb
    (hballW haδ) (hballW hbδ)
  set C := connectedComponentIn (W ∩ Mᶜ) a
  have hCsub : C ⊆ W ∩ Mᶜ := connectedComponentIn_subset _ _
  have haM : a ∉ M := (connectedComponentIn_subset _ _ ha : a ∈ Mᶜ)
  have haC : a ∈ C := mem_connectedComponentIn ⟨hballW haδ, haM⟩
  refine ⟨C, ?_, isPreconnected_connectedComponentIn, haC, hj,
    hCsub.trans (inter_subset_left.trans hWball)⟩
  rw [connectedComponentIn_eq ha]
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn haC
    (hCsub.trans inter_subset_right)

end HPC.Jones.Sec14
