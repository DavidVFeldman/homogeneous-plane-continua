import HPC.Jones.Jones49Circle
import HPC.Moore.CutArc
import HPC.PseudoArc.Theorem14

/-!
# Batch 149, item C: Menger's theorem on curves of order 2

`menger_order_two`: a nondegenerate compact metric continuum all of whose points have order 2 is
homeomorphic to `Circle`; `jones49_order_two`: for a homogeneous continuum one point of order 2
suffices.

The route is neither Menger's (pp. 262–267: the `n`-Beinsatz and the classification of ordinary
curves) nor the one through `circle_char`, but Menger's own *second* argument (p. 267, the lemma for
arcs: the first point of an arc from outside on a curve is a branch point), applied twice:

1. `locallyConnectedSpace_of_orderLE`: every subcontinuum of `X` is locally connected (its points
   have order `≤ 2` in it, `orderLE_subtype`).
2. `exists_tarc_of_orderLE`: hence any two points of a subcontinuum `K` are joined by an arc in
   `K`: a subcontinuum irreducible between them (batch 83's `exists_irreducible`) is locally
   connected, so each of its other points cuts it (`exists_continuum_of_isOpen`), and it is an arc
   (batch 146's `IsCutArc.exists_embedding`).
3. `arc_eq_of_legs`: an arc `B ⊆ K` from `a` to `b`, with connected "legs" at `a` and `b` meeting
   `K` only there, is all of `K`: else an arc from a point of `K − B` to `B` produces a triod
   (`not_orderLE_two_of_triod`).
4. Main proof: take a non-cut point `u` (batch 94's `exists_two_nonCutPoints`) and a small open
   connected `V ∋ u` with frontier `{a, b}` (exactly two points since `u` is not of order `≤ 1`).
   Step 3 for `K = V̄` (legs: the parts outside `V` of connected neighbourhoods of `a`, `b`) shows
   that `V̄` is an arc; since `u` does not cut `X`, `X − V` is connected; step 3 again for
   `K = X − V` (legs: the two halves of `V̄` at `u`) shows that `X − V` is an arc. So `X` is a
   topological simple closed curve, and `tscc_homeomorph_circle` applies.
-/

namespace HPC.Jones

open Set Topology Metric unitInterval
open HPC.Moore.Gen (TArc TSCC)

section General

variable {Y : Type*} [TopologicalSpace Y]

/-- The frontier of a component of an open set (in a locally connected space) lies in the frontier
of the set. -/
theorem frontier_connectedComponentIn_subset [LocallyConnectedSpace Y] {V : Set Y} (hV : IsOpen V)
    (x : Y) : frontier (connectedComponentIn V x) ⊆ frontier V := by
  intro z hz
  rw [hV.connectedComponentIn.frontier_eq] at hz
  obtain ⟨hzcl, hzC⟩ := hz
  rw [hV.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset _ _) hzcl, fun hzV => hzC ?_⟩
  have hO := (hV.connectedComponentIn (x := z)).mem_nhds (mem_connectedComponentIn hzV)
  obtain ⟨w, hwz, hwC⟩ := mem_closure_iff_nhds.1 hzcl _ hO
  rw [connectedComponentIn_eq hwC, ← connectedComponentIn_eq hwz]
  exact mem_connectedComponentIn hzV

/-- The part outside an open set `V` of a preconnected set `N` meeting the frontier of `V` in one
point `a` only is preconnected. -/
theorem isPreconnected_diff_of_frontier {N V : Set Y} (hN : IsPreconnected N) (hV : IsOpen V)
    {a : Y} (haN : a ∈ N) (haF : a ∈ frontier V) (hfr : N ∩ frontier V ⊆ {a}) :
    IsPreconnected (N \ V) := by
  have haV : a ∉ V := fun h => (disjoint_left.1
    (disjoint_iff_inter_eq_empty.2 hV.inter_frontier_eq)) h haF
  have main : ∀ {u v : Set Y}, IsOpen u → IsOpen v → N \ V ⊆ u ∪ v → N \ V ∩ (u ∩ v) = ∅ →
      a ∈ u → N \ V ⊆ u := by
    intro u v hu hv hcov hdisj hau
    have hcov' : N ⊆ (u ∪ V) ∪ (v ∩ (closure V)ᶜ) := by
      intro z hz
      by_cases hzV : z ∈ V
      · exact Or.inl (Or.inr hzV)
      by_cases hzcl : z ∈ closure V
      · have : z = a := hfr ⟨hz, hzcl, by rwa [hV.interior_eq]⟩
        exact Or.inl (Or.inl (this ▸ hau))
      rcases hcov ⟨hz, hzV⟩ with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨h, hzcl⟩
    have hdisj' : N ∩ ((u ∪ V) ∩ (v ∩ (closure V)ᶜ)) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z ⟨hzN, hzuV, hzv, hzcl⟩ => ?_
      have hzV : z ∉ V := fun h => hzcl (subset_closure h)
      exact (eq_empty_iff_forall_notMem.1 hdisj) z ⟨⟨hzN, hzV⟩, hzuV.resolve_right hzV, hzv⟩
    rcases isPreconnected_iff_subset_of_disjoint.1 hN _ _ (hu.union hV)
      (hv.inter isClosed_closure.isOpen_compl) hcov' hdisj' with h | h
    · intro z ⟨hzN, hzV⟩; exact (h hzN).resolve_right hzV
    · exact absurd (frontier_subset_closure haF) (h haN).2
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  rcases hcov ⟨haN, haV⟩ with hau | hav
  · exact Or.inl (main hu hv hcov hdisj hau)
  · refine Or.inr (main hv hu (by rwa [union_comm]) (by rwa [inter_comm v]) hav)

variable [CompactSpace Y] [T2Space Y] [LocallyConnectedSpace Y]

theorem exists_conn_nhds_closure_subset {O : Set Y} {z : Y} (hO : O ∈ 𝓝 z) :
    ∃ N, IsOpen N ∧ IsPreconnected N ∧ z ∈ N ∧ closure N ⊆ O := by
  obtain ⟨C, hC, hCcl, hCO⟩ := exists_mem_nhds_isClosed_subset hO
  refine ⟨connectedComponentIn (interior C) z, isOpen_interior.connectedComponentIn,
    isPreconnected_connectedComponentIn,
    mem_connectedComponentIn (mem_interior_iff_mem_nhds.2 hC), ?_⟩
  exact (closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) hCcl).trans hCO

/-- In a compact locally connected Hausdorff space, two points of a connected open set lie in a
continuum inside it. -/
theorem exists_continuum_of_isOpen {O : Set Y} (hO : IsOpen O) (hOc : IsPreconnected O)
    {x y : Y} (hx : x ∈ O) (hy : y ∈ O) :
    ∃ K ⊆ O, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K := by
  set S := {z | ∃ K ⊆ O, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ z ∈ K}
  have hext : ∀ z ∈ O, ∃ N, IsOpen N ∧ z ∈ N ∧ N ⊆ O ∧ ∀ w ∈ N, (z ∈ S ↔ w ∈ S) := by
    intro z hz
    obtain ⟨N, hNo, hNc, hzN, hNO⟩ := exists_conn_nhds_closure_subset (hO.mem_nhds hz)
    have hcl : IsConnected (closure N) := ⟨⟨z, subset_closure hzN⟩, hNc.closure⟩
    have key : ∀ {z' w : Y}, z' ∈ closure N → w ∈ closure N → z' ∈ S → w ∈ S := by
      rintro z' w hz' hw ⟨K, hKO, hKc, hKconn, hxK, hzK⟩
      exact ⟨K ∪ closure N, union_subset hKO hNO, hKc.union isClosed_closure.isCompact,
        IsConnected.union ⟨z', hzK, hz'⟩ hKconn hcl, Or.inl hxK, Or.inr hw⟩
    exact ⟨N, hNo, hzN, subset_closure.trans hNO, fun w hw =>
      ⟨key (subset_closure hzN) (subset_closure hw), key (subset_closure hw) (subset_closure hzN)⟩⟩
  have hSo : IsOpen (O ∩ S) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzO, hzS⟩
    obtain ⟨N, hNo, hzN, hNO, hN⟩ := hext z hzO
    exact Filter.mem_of_superset (hNo.mem_nhds hzN) fun w hw => ⟨hNO hw, (hN w hw).1 hzS⟩
  have hTo : IsOpen (O \ S) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzO, hzS⟩
    obtain ⟨N, hNo, hzN, hNO, hN⟩ := hext z hzO
    exact Filter.mem_of_superset (hNo.mem_nhds hzN)
      fun w hw => ⟨hNO hw, fun h => hzS ((hN w hw).2 h)⟩
  have hxS : x ∈ S :=
    ⟨{x}, singleton_subset_iff.2 hx, isCompact_singleton, isConnected_singleton, rfl, rfl⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hOc _ _ hSo hTo
    (fun z hz => by
      by_cases h : z ∈ S
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩)
    (eq_empty_iff_forall_notMem.2 fun z hz => hz.2.2.2 hz.2.1.2) with h | h
  · exact (h hy).2
  · exact absurd hxS (h hx).2

end General

section Arcs

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Arcs in a curve of finite order.** If every point of the compact metric space `X` has finite
order, any two points of a subcontinuum `K` are joined by an arc in `K`. -/
theorem exists_tarc_of_orderLE (hreg : ∀ p : X, ∃ n, OrderLE p n) {K : Set X} (hK : IsCompact K)
    (hKc : IsConnected K) {a b : X} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) :
    ∃ B ⊆ K, TArc a b B := by
  obtain ⟨W, hWK, ⟨hWc, hWconn⟩, haW, hbW, hirr⟩ := HPC.exists_irreducible ⟨hK, hKc⟩ ha hb
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hWc
  haveI : ConnectedSpace W := Subtype.connectedSpace hWconn
  haveI : LocallyConnectedSpace W := locallyConnectedSpace_of_orderLE fun q => by
    obtain ⟨n, hn⟩ := hreg q; exact ⟨n, orderLE_subtype q.2 hn⟩
  have hcut : HPC.Moore.IsCutArc a b W := by
    refine ⟨hab, hWc, hWconn, haW, hbW, fun x hxW hxa hxb hconn => ?_⟩
    set O : Set W := {⟨x, hxW⟩}ᶜ
    have himg : ((↑) : W → X) '' O = W \ {x} := by
      ext z
      simp only [O, mem_image, mem_compl_iff, mem_singleton_iff, mem_diff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, fun e => hw (Subtype.ext e)⟩
      · rintro ⟨hz, hzx⟩
        exact ⟨⟨z, hz⟩, fun e => hzx (congrArg Subtype.val e), rfl⟩
    have hOc : IsPreconnected O := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, himg]; exact hconn.isPreconnected
    obtain ⟨K', hK'O, hK'c, hK'conn, haK', hbK'⟩ := exists_continuum_of_isOpen
      isOpen_compl_singleton hOc (x := ⟨a, haW⟩) (y := ⟨b, hbW⟩)
      (fun e => hxa (congrArg Subtype.val e).symm) (fun e => hxb (congrArg Subtype.val e).symm)
    have heq := hirr ((↑) '' K') ⟨hK'c.image continuous_subtype_val,
      hK'conn.image _ continuous_subtype_val.continuousOn⟩
      (by rintro _ ⟨w, -, rfl⟩; exact w.2) ⟨_, haK', rfl⟩ ⟨_, hbK', rfl⟩
    have hx : x ∈ ((↑) '' K' : Set X) := by rw [heq]; exact hxW
    obtain ⟨w, hw, hwx⟩ := hx
    exact hK'O hw (Subtype.ext hwx)
  obtain ⟨f, hf, hfW, hf0, hf1⟩ := hcut.exists_embedding
  exact ⟨W, hWK, hab, f, hf, hfW, hf0, hf1⟩

/-- The two halves of an arc at an interior point. -/
theorem tarc_halves {Z : Type*} [TopologicalSpace Z] {a b P : Z} {B : Set Z} (hB : TArc a b B)
    (hP : P ∈ B) : ∃ T₁ T₂ : Set Z, T₁ ⊆ B ∧ T₂ ⊆ B ∧ IsPreconnected T₁ ∧ IsPreconnected T₂ ∧
      P ∈ T₁ ∧ P ∈ T₂ ∧ a ∈ T₁ ∧ b ∈ T₂ ∧ T₁ ∩ T₂ ⊆ {P} ∧ T₁ ∪ T₂ = B ∧
      (P ≠ b → b ∉ T₁) ∧ (P ≠ a → a ∉ T₂) ∧ IsCompact T₁ ∧ IsCompact T₂ := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hB
  obtain ⟨t, rfl⟩ := hP
  refine ⟨f '' Icc 0 t, f '' Icc t 1, image_subset_range _ _, image_subset_range _ _,
    isPreconnected_Icc.image _ hf.continuous.continuousOn,
    isPreconnected_Icc.image _ hf.continuous.continuousOn,
    ⟨t, ⟨nonneg', le_rfl⟩, rfl⟩, ⟨t, ⟨le_rfl, le_one'⟩, rfl⟩,
    ⟨0, ⟨le_rfl, nonneg'⟩, rfl⟩, ⟨1, ⟨le_one', le_rfl⟩, rfl⟩, ?_, ?_, ?_, ?_,
    isCompact_Icc.image hf.continuous, isCompact_Icc.image hf.continuous⟩
  · rintro _ ⟨⟨s, hs, rfl⟩, ⟨s', hs', he⟩⟩
    have := hf.injective he
    subst this
    rw [mem_singleton_iff]
    exact congrArg f (le_antisymm hs.2 hs'.1)
  · rw [← image_union, Icc_union_Icc_eq_Icc (nonneg') (le_one')]
    ext z; simp only [mem_image, mem_range]
    exact ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, ⟨nonneg', le_one'⟩, h⟩⟩
  · rintro hPa ⟨s, hs, he⟩
    have := hf.injective he
    subst this
    exact hPa (congrArg f (le_antisymm (le_one') hs.2))
  · rintro hPb ⟨s, hs, he⟩
    have := hf.injective he
    subst this
    exact hPb (congrArg f (le_antisymm hs.1 (nonneg')))

/-- **An arc with legs at both ends fills the continuum.** In a compact metric space all of whose
points have order `≤ 2`: an arc `B ⊆ K` from `a` to `b` (`K` a continuum), together with
preconnected nondegenerate sets `Ta ∋ a`, `Tb ∋ b` meeting `K` only in `a`, respectively `b`, is all
of `K`. -/
theorem arc_eq_of_legs (hreg : ∀ p : X, OrderLE p 2) {K B Ta Tb : Set X} (hK : IsCompact K)
    (hKc : IsConnected K) {a b : X} (hB : TArc a b B) (hBK : B ⊆ K)
    (hTa : IsPreconnected Ta) (haTa : a ∈ Ta) (hTan : ∃ x ∈ Ta, x ≠ a) (hTaK : Ta ∩ K ⊆ {a})
    (hTb : IsPreconnected Tb) (hbTb : b ∈ Tb) (hTbn : ∃ x ∈ Tb, x ≠ b) (hTbK : Tb ∩ K ⊆ {b}) :
    K = B := by
  refine Subset.antisymm (fun q hqK => by_contra fun hqB => ?_) hBK
  have hqa : q ≠ a := fun h => hqB (h ▸ hB.left_mem)
  obtain ⟨C, hCK, hC⟩ := exists_tarc_of_orderLE (fun p => ⟨2, hreg p⟩) hK hKc hqK
    (hBK hB.left_mem) hqa
  obtain ⟨P, hPB, C', hC'C, hC', hC'B⟩ :=
    hC.first_point hB.isClosed ⟨a, hC.right_mem, hB.left_mem⟩ hqB
  have hC'K := hC'C.trans hCK
  have hqP : q ≠ P := fun h => hqB (h ▸ hPB)
  have hC'B' : C' ∩ B ⊆ {P} := hC'B.subset
  by_cases hPa : P = a
  · subst hPa
    exact not_orderLE_two_of_triod hC'.isPreconnected hB.isPreconnected hTa hC'.right_mem
      hB.left_mem haTa ⟨q, hC'.left_mem, hqP⟩ ⟨b, hB.right_mem, hB.ne.symm⟩ hTan hC'B'
      (fun z hz => hTaK ⟨hz.2, hC'K hz.1⟩) (fun z hz => hTaK ⟨hz.2, hBK hz.1⟩) (hreg _)
  by_cases hPb : P = b
  · subst hPb
    exact not_orderLE_two_of_triod hC'.isPreconnected hB.isPreconnected hTb hC'.right_mem
      hB.right_mem hbTb ⟨q, hC'.left_mem, hqP⟩ ⟨a, hB.left_mem, hB.ne⟩ hTbn hC'B'
      (fun z hz => hTbK ⟨hz.2, hC'K hz.1⟩) (fun z hz => hTbK ⟨hz.2, hBK hz.1⟩) (hreg _)
  obtain ⟨T₁, T₂, hT₁B, hT₂B, hT₁, hT₂, hPT₁, hPT₂, haT₁, hbT₂, h12, -⟩ := tarc_halves hB hPB
  exact not_orderLE_two_of_triod hT₁ hT₂ hC'.isPreconnected hPT₁ hPT₂ hC'.right_mem
    ⟨a, haT₁, Ne.symm hPa⟩ ⟨b, hbT₂, Ne.symm hPb⟩ ⟨q, hC'.left_mem, hqP⟩ h12
    (fun z hz => hC'B' ⟨hz.2, hT₁B hz.1⟩) (fun z hz => hC'B' ⟨hz.2, hT₂B hz.1⟩) (hreg _)

end Arcs

/-- **Menger, p. 267 (the circle half):** a nondegenerate compact metric continuum all of whose
points are of order 2 is homeomorphic to a circle. -/
theorem menger_order_two {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (h : ∀ p : X, HasOrder p 2) : Nonempty (X ≃ₜ Circle) := by
  classical
  have hreg : ∀ p : X, OrderLE p 2 := fun p => (h p).1
  have hnot1 : ∀ p : X, ¬ OrderLE p 1 := fun p => (h p).2 1 (by norm_num)
  haveI : LocallyConnectedSpace X := locallyConnectedSpace_of_orderLE fun p => ⟨2, hreg p⟩
  obtain ⟨u, -, -, hu, -⟩ := HPC.Plane.exists_two_nonCutPoints (X := X)
  have hu' : IsConnected ({u}ᶜ : Set X) := not_not.1 hu
  obtain ⟨U₀, hU₀, hU₀'⟩ : ∃ U₀ ∈ 𝓝 u, ∀ V, IsOpen V → u ∈ V → V ⊆ U₀ →
      (frontier V).Finite → ¬ (frontier V).ncard ≤ 1 := by
    have := hnot1 u
    simp only [OrderLE, not_forall, not_exists, not_and] at this
    obtain ⟨U₀, hU₀, h'⟩ := this
    exact ⟨U₀, hU₀, fun V hVo huV hVU hfin => h' V hVo huV hVU hfin⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU₀
  obtain ⟨V₀, hV₀o, huV₀, hV₀U, hV₀fin, hV₀card⟩ := hreg u _ (ball_mem_nhds u (half_pos hε))
  set V := connectedComponentIn V₀ u with hVdef
  have hVo : IsOpen V := hV₀o.connectedComponentIn
  have huV : u ∈ V := mem_connectedComponentIn huV₀
  have hVc : IsConnected V := ⟨⟨u, huV⟩, isPreconnected_connectedComponentIn⟩
  have hfrV : frontier V ⊆ frontier V₀ := frontier_connectedComponentIn_subset hV₀o u
  have hVfin : (frontier V).Finite := hV₀fin.subset hfrV
  have hclV : closure V ⊆ U₀ :=
    (closure_mono ((connectedComponentIn_subset _ _).trans hV₀U)).trans
      (closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (half_lt_self hε)).trans hεU))
  have hcard : (frontier V).ncard = 2 := by
    have h1 := ncard_le_ncard hfrV hV₀fin
    have h2 := hU₀' V hVo huV (subset_closure.trans hclV) hVfin
    omega
  obtain ⟨a, b, hab, hfr⟩ := ncard_eq_two.1 hcard
  have hVF : ∀ {z}, z ∈ frontier V → z ∉ V := fun hz hzV =>
    (disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hVo.inter_frontier_eq)) hzV hz
  have haFr : a ∈ frontier V := by rw [hfr]; exact Or.inl rfl
  have hbFr : b ∈ frontier V := by rw [hfr]; exact Or.inr rfl
  have hclVeq : closure V = V ∪ {a, b} := by rw [closure_eq_self_union_frontier, hfr]
  have hcapV : closure V ∩ Vᶜ = {a, b} := by rw [← hfr, hVo.frontier_eq, diff_eq]
  -- the frontier points are limit points of the outside of `V̄`
  have side : ∀ c d : X, frontier V = {c, d} → c ≠ d → c ∈ closure (closure V)ᶜ := by
    intro c d hcd hne
    by_contra hcn
    have hcF : c ∈ frontier V := by rw [hcd]; exact Or.inl rfl
    set V' := V ∪ {c}
    have hV'o : IsOpen V' := by
      have : V' = V ∪ ((closure (closure V)ᶜ)ᶜ \ {d}) := by
        ext z
        constructor
        · rintro (hz | hz)
          · exact Or.inl hz
          · rw [mem_singleton_iff] at hz; subst hz
            exact Or.inr ⟨hcn, fun e => hne (mem_singleton_iff.1 e)⟩
        · rintro (hz | ⟨hz1, hz2⟩)
          · exact Or.inl hz
          have hz' : z ∈ closure V := by
            by_contra hz'; exact hz1 (subset_closure hz')
          rw [closure_eq_self_union_frontier, hcd] at hz'
          rcases hz' with hz' | hz' | hz'
          · exact Or.inl hz'
          · exact Or.inr hz'
          · exact absurd hz' hz2
      rw [this]; exact hVo.union (isClosed_closure.isOpen_compl.sdiff isClosed_singleton)
    have hfrV' : frontier V' ⊆ {d} := by
      rw [hV'o.frontier_eq]
      rintro z ⟨hzcl, hzV'⟩
      have hsub : closure V' ⊆ closure V := closure_minimal
        (union_subset subset_closure (singleton_subset_iff.2 (frontier_subset_closure hcF)))
        isClosed_closure
      have hz := hsub hzcl
      rw [closure_eq_self_union_frontier, hcd] at hz
      rcases hz with hz | hz | hz
      · exact absurd (Or.inl hz) hzV'
      · exact absurd (Or.inr hz) hzV'
      · exact hz
    have := hU₀' V' hV'o (Or.inl huV)
      (union_subset (subset_closure.trans hclV)
        (singleton_subset_iff.2 (hclV (frontier_subset_closure hcF))))
      ((finite_singleton d).subset hfrV')
    exact this ((ncard_le_ncard hfrV' (finite_singleton d)).trans (ncard_singleton d).le)
  -- legs at `a` and `b` outside `V`
  have leg_out : ∀ c d : X, frontier V = {c, d} → c ≠ d → ∃ T : Set X, IsPreconnected T ∧
      c ∈ T ∧ (∃ x ∈ T, x ≠ c) ∧ T ∩ closure V ⊆ {c} := by
    intro c d hcd hne
    set N := connectedComponentIn ({d}ᶜ) c
    have hNo : IsOpen N := isOpen_compl_singleton.connectedComponentIn
    have hcN : c ∈ N := mem_connectedComponentIn hne
    have hcF : c ∈ frontier V := by rw [hcd]; exact Or.inl rfl
    have hdN : d ∉ N := fun h => connectedComponentIn_subset _ _ h rfl
    have hNF : N ∩ frontier V ⊆ {c} := by
      rintro z ⟨hzN, hzF⟩
      rw [hcd] at hzF
      rcases hzF with hz | hz
      · exact hz
      · rw [mem_singleton_iff] at hz; subst hz; exact absurd hzN hdN
    refine ⟨N \ V, isPreconnected_diff_of_frontier isPreconnected_connectedComponentIn hVo hcN
      hcF hNF, ⟨hcN, hVF hcF⟩, ?_, ?_⟩
    · obtain ⟨z, hzN, hz⟩ := mem_closure_iff_nhds.1 (side c d hcd hne) N (hNo.mem_nhds hcN)
      exact ⟨z, ⟨hzN, fun h => hz (subset_closure h)⟩,
        fun h => hz (h ▸ frontier_subset_closure hcF)⟩
    · rintro z ⟨⟨hzN, hzV⟩, hzcl⟩
      have : z ∈ frontier V := by rw [hVo.frontier_eq]; exact ⟨hzcl, hzV⟩
      exact hNF ⟨hzN, this⟩
  -- `V̄` is an arc from `a` to `b`
  have hKcl : IsCompact (closure V) := isClosed_closure.isCompact
  have hKclc : IsConnected (closure V) := hVc.closure
  obtain ⟨B₀, hB₀K, hB₀⟩ := exists_tarc_of_orderLE (fun p => ⟨2, hreg p⟩) hKcl hKclc
    (frontier_subset_closure haFr) (frontier_subset_closure hbFr) hab
  obtain ⟨Ta, hTa, haTa, hTan, hTaK⟩ := leg_out a b hfr hab
  obtain ⟨Tb, hTb, hbTb, hTbn, hTbK⟩ := leg_out b a (hfr.trans (pair_comm a b)) hab.symm
  have hB₀eq : closure V = B₀ :=
    arc_eq_of_legs hreg hKcl hKclc hB₀ hB₀K hTa haTa hTan hTaK hTb hbTb hTbn hTbK
  -- its halves at `u`
  have huB₀ : u ∈ B₀ := hB₀eq ▸ subset_closure huV
  obtain ⟨T₁, T₂, -, -, hT₁, hT₂, huT₁, huT₂, haT₁, hbT₂, h12, h1u2, hbT₁, haT₂, hT₁k, hT₂k⟩ :=
    tarc_halves hB₀ huB₀
  have hua : u ≠ a := fun e => hVF haFr (e ▸ huV)
  have hub : u ≠ b := fun e => hVF hbFr (e ▸ huV)
  have hbT₁ := hbT₁ hub
  have haT₂ := haT₂ hua
  have hT₁c : IsClosed T₁ := hT₁k.isClosed
  have hT₂c : IsClosed T₂ := hT₂k.isClosed
  have hT12 : closure V = T₁ ∪ T₂ := hB₀eq.trans h1u2.symm
  have hVcl : IsClosed Vᶜ := hVo.isClosed_compl
  have hab' : ∀ {w}, w ∈ Vᶜ → w ∈ T₁ ∪ T₂ → w = a ∨ w = b := fun {w} hw hw' => by
    have : w ∈ ({a, b} : Set X) := by rw [← hcapV]; exact ⟨hT12 ▸ hw', hw⟩
    simpa using this
  -- `X − V` is connected, since `u` does not cut `X`
  have claimA : ∀ E F : Set X, IsClosed E → IsClosed F → Vᶜ ⊆ E ∪ F → Vᶜ ∩ (E ∩ F) = ∅ →
      a ∈ E → b ∈ E → Vᶜ ⊆ E := by
    intro E F hE hF hcov hdisj haE hbE
    have hdisj' := eq_empty_iff_forall_notMem.1 hdisj
    have hG : IsClopen (Vᶜ ∩ F) := by
      refine ⟨hVcl.inter hF, ?_⟩
      have : Vᶜ ∩ F = Eᶜ ∩ (closure V)ᶜ := by
        ext z
        constructor
        · rintro ⟨hzV, hzF⟩
          refine ⟨fun hzE => hdisj' z ⟨hzV, hzE, hzF⟩, fun hzcl => ?_⟩
          have : z ∈ ({a, b} : Set X) := by rw [← hcapV]; exact ⟨hzcl, hzV⟩
          rcases this with rfl | rfl
          · exact hdisj' _ ⟨hzV, haE, hzF⟩
          · exact hdisj' _ ⟨hzV, hbE, hzF⟩
        · rintro ⟨hzE, hzcl⟩
          have hzV : z ∈ Vᶜ := fun h => hzcl (subset_closure h)
          exact ⟨hzV, (hcov hzV).resolve_left hzE⟩
      rw [this]; exact hE.isOpen_compl.inter isClosed_closure.isOpen_compl
    rcases isClopen_iff.1 hG with h | h
    · intro z hz
      exact (hcov hz).resolve_right fun hzF => (eq_empty_iff_forall_notMem.1 h) z ⟨hz, hzF⟩
    · have hu2 : u ∈ Vᶜ ∩ F := by rw [h]; exact mem_univ u
      exact absurd huV hu2.1
  have claimB : ∀ E F : Set X, IsClosed E → IsClosed F → Vᶜ ⊆ E ∪ F → Vᶜ ∩ (E ∩ F) = ∅ →
      a ∈ E → b ∈ F → False := by
    intro E F hE hF hcov hdisj haE hbF'
    have hdisj' := eq_empty_iff_forall_notMem.1 hdisj
    have haV : a ∈ Vᶜ := hVF haFr
    have hbV : b ∈ Vᶜ := hVF hbFr
    have hc1 : ({u}ᶜ : Set X) ⊆ ((Vᶜ ∩ E) ∪ T₁) ∪ ((Vᶜ ∩ F) ∪ T₂) := by
      intro z _
      by_cases hzV : z ∈ V
      · have : z ∈ T₁ ∪ T₂ := hT12 ▸ subset_closure hzV
        rcases this with h1 | h2
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inr h2)
      · rcases hcov hzV with h1 | h2
        · exact Or.inl (Or.inl ⟨hzV, h1⟩)
        · exact Or.inr (Or.inl ⟨hzV, h2⟩)
    have hc2 : ({u}ᶜ : Set X) ∩ (((Vᶜ ∩ E) ∪ T₁) ∩ ((Vᶜ ∩ F) ∪ T₂)) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z ⟨hzu, hz1, hz2⟩ => ?_
      rcases hz1 with ⟨hzV, hzE⟩ | hzT₁ <;> rcases hz2 with ⟨hzV', hzF⟩ | hzT₂
      · exact hdisj' z ⟨hzV, hzE, hzF⟩
      · rcases hab' hzV (Or.inr hzT₂) with rfl | rfl
        · exact haT₂ hzT₂
        · exact hdisj' _ ⟨hzV, hzE, hbF'⟩
      · rcases hab' hzV' (Or.inl hzT₁) with rfl | rfl
        · exact hdisj' _ ⟨hzV', haE, hzF⟩
        · exact hbT₁ hzT₁
      · exact hzu (h12 ⟨hzT₁, hzT₂⟩)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hu'.isPreconnected
      ((Vᶜ ∩ E) ∪ T₁) ((Vᶜ ∩ F) ∪ T₂) ((hVcl.inter hE).union hT₁c)
      ((hVcl.inter hF).union hT₂c) hc1 hc2 with h | h
    · rcases h (show b ∈ ({u}ᶜ : Set X) from hub.symm) with ⟨-, hbE⟩ | hb1
      · exact hdisj' b ⟨hbV, hbE, hbF'⟩
      · exact hbT₁ hb1
    · rcases h (show a ∈ ({u}ᶜ : Set X) from hua.symm) with ⟨-, haF'⟩ | ha2
      · exact hdisj' a ⟨haV, haE, haF'⟩
      · exact haT₂ ha2
  have hVcc : IsConnected Vᶜ := by
    refine ⟨⟨a, hVF haFr⟩, ?_⟩
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro E F hE hF hcov hdisj
    have hdisj2 : Vᶜ ∩ (F ∩ E) = ∅ := by rwa [inter_comm F E]
    have hcov2 : Vᶜ ⊆ F ∪ E := by rwa [union_comm]
    rcases hcov (hVF haFr) with haE | haE <;> rcases hcov (hVF hbFr) with hbE | hbE
    · exact Or.inl (claimA E F hE hF hcov hdisj haE hbE)
    · exact (claimB E F hE hF hcov hdisj haE hbE).elim
    · exact (claimB F E hF hE hcov2 hdisj2 haE hbE).elim
    · exact Or.inr (claimA F E hF hE hcov2 hdisj2 haE hbE)
  -- `X − V` is an arc from `a` to `b`
  obtain ⟨B₂, hB₂K, hB₂⟩ := exists_tarc_of_orderLE (fun p => ⟨2, hreg p⟩) hVcl.isCompact hVcc
    (hVF haFr) (hVF hbFr) hab
  have hT₁V : T₁ ∩ Vᶜ ⊆ {a} := by
    rintro z ⟨hz1, hzV⟩
    rcases hab' hzV (Or.inl hz1) with rfl | rfl
    · rfl
    · exact absurd hz1 hbT₁
  have hT₂V : T₂ ∩ Vᶜ ⊆ {b} := by
    rintro z ⟨hz2, hzV⟩
    rcases hab' hzV (Or.inr hz2) with rfl | rfl
    · exact absurd hz2 haT₂
    · rfl
  have hB₂eq : Vᶜ = B₂ := arc_eq_of_legs hreg hVcl.isCompact hVcc hB₂ hB₂K hT₁ haT₁
    ⟨u, huT₁, hua⟩ hT₁V hT₂ hbT₂ ⟨u, huT₂, hub⟩ hT₂V
  -- so `X` is a simple closed curve
  have hT : TSCC (univ : Set X) := by
    refine ⟨a, b, B₀, B₂, hB₀, hB₂, by rw [← hB₀eq, ← hB₂eq, hcapV], ?_⟩
    rw [← hB₀eq, ← hB₂eq]
    exact (eq_univ_of_forall fun z => by
      by_cases hz : z ∈ V
      · exact Or.inl (subset_closure hz)
      · exact Or.inr hz).symm
  obtain ⟨e⟩ := tscc_homeomorph_circle hT
  exact ⟨(Homeomorph.Set.univ X).symm.trans e⟩

/-- **Jones 1949, p. 113, first sentence of the proof:** "If a point of `M` is of order 2 in `M`,
then `M` is a simple closed curve [4]" — with `M` homogeneous (the hypothesis of Theorem 1 that makes
Menger's "all points" follow from "a point"). -/
theorem jones49_order_two {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (hX : IsHomogeneous X) {p : X} (hp : HasOrder p 2) :
    Nonempty (X ≃ₜ Circle) := by
  refine menger_order_two fun q => ?_
  obtain ⟨g, hg⟩ := hX p q
  exact hg ▸ (hasOrder_homeomorph g).1 hp

end HPC.Jones
