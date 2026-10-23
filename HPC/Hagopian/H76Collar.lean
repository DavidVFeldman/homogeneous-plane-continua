import HPC.Hagopian.H76Invert

/-!
# Batch 159, item C: a two-sided collar of an arc in the plane

* `accessible_of_noncut`: batch 153's accessibility theorem (`accessible_of_cyclic'`) needs only
  that the point `p` is not a cut point of `M`; the proof is that of batch 153 verbatim, with the
  hypothesis weakened (it is used once, for `local_join_of_noncut` at `p`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Moore HPC.Moore.Gen HPC.Jones

/-- **Accessibility at a non-cut point.** As `accessible_of_cyclic'`, for a point `p` which does not
cut `M`. -/
theorem accessible_of_noncut {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) {x : Pt}
    (hx : x ∉ M) {p : Pt} (hp : p ∈ frontier (connectedComponentIn Mᶜ x))
    (hcyc : ∀ hpM : p ∈ M, IsConnected ({⟨p, hpM⟩}ᶜ : Set M)) {y : Pt}
    (hy : y ∈ connectedComponentIn Mᶜ x) (hyp : y ≠ p) :
    ∃ C : Set Pt, TArc y p C ∧ C \ {p} ⊆ connectedComponentIn Mᶜ x := by
  set R := connectedComponentIn Mᶜ x with hRdef
  have hRo : IsOpen R := hM.isClosed.isOpen_compl.connectedComponentIn
  have hRc : IsConnected R := isConnected_connectedComponentIn_iff.2 hx
  have hpM : p ∈ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hM.isClosed x hp
  have hpR : p ∉ R := fun h => connectedComponentIn_subset _ _ h hpM
  have hpcl : p ∈ closure R := frontier_subset_closure hp
  have hLJ := fun (ε : ℝ) (hε : 0 < ε) =>
    Sec14.local_join_of_noncut hM hMc hS (p := ⟨p, hpM⟩) (hcyc hpM) hε x
  choose! δ hδpos hδ using hLJ
  -- points of `R` near `p`, other than a given point
  have hnear : ∀ r > 0, ∀ w : Pt, ∃ z ∈ R, z ∈ ball p r ∧ z ≠ w := by
    intro r hr w
    by_cases hw : w = p
    · obtain ⟨z, hzb, hzR⟩ := mem_closure_iff.1 hpcl (ball p r) isOpen_ball (mem_ball_self hr)
      exact ⟨z, hzR, hzb, fun e => hpR (by rw [← hw, ← e]; exact hzR)⟩
    · obtain ⟨z, ⟨hzb, hzw⟩, hzR⟩ := mem_closure_iff.1 hpcl (ball p r ∩ {w}ᶜ)
        (isOpen_ball.inter isOpen_compl_singleton) ⟨mem_ball_self hr, Ne.symm hw⟩
      exact ⟨z, hzR, hzb, hzw⟩
  -- the step
  have step : ∀ (x₀ : Pt) (ρ ρ' : ℝ), 0 < ρ → 0 < ρ' → x₀ ∈ R → x₀ ∈ ball p (δ ρ) →
      ∃ x₁ : Pt, ∃ β : Set Pt, x₁ ∈ R ∧ x₁ ∈ ball p (δ ρ') ∧ TArc x₀ x₁ β ∧ β ⊆ R ∧
        β ⊆ ball p ρ := by
    intro x₀ ρ ρ' hρ hρ' hx₀R hx₀b
    obtain ⟨x₁, hx₁R, hx₁b, hx₁x₀⟩ := hnear (min (δ ρ) (δ ρ'))
      (lt_min (hδpos ρ hρ) (hδpos ρ' hρ')) x₀
    obtain ⟨C, hCR, hCc, hx₀C, hx₁C, hCb⟩ := hδ ρ hρ x₀ hx₀R x₁ hx₁R hx₀b
      (ball_subset_ball (min_le_left _ _) hx₁b)
    set W := connectedComponentIn (R ∩ ball p ρ) x₀
    have hWo : IsOpen W := (hRo.inter isOpen_ball).connectedComponentIn
    have hWc : IsConnected W := isConnected_connectedComponentIn_iff.2 ⟨hx₀R, hCb hx₀C⟩
    have hCW : C ⊆ W := hCc.subset_connectedComponentIn hx₀C (subset_inter hCR hCb)
    obtain ⟨β, hβW, hβ⟩ := exists_tarc_of_isOpen_plane hWo hWc (hCW hx₀C) (hCW hx₁C)
      (Ne.symm hx₁x₀)
    have hWsub : W ⊆ R ∩ ball p ρ := connectedComponentIn_subset _ _
    exact ⟨x₁, β, hx₁R, ball_subset_ball (min_le_right _ _) hx₁b, hβ,
      hβW.trans (hWsub.trans inter_subset_left), hβW.trans (hWsub.trans inter_subset_right)⟩
  choose! X1 B1 hX1R hX1b hB1arc hB1R hB1b using step
  -- the initial point and radii
  obtain ⟨x₀, hx₀R, hx₀b, -⟩ := hnear (δ 1) (hδpos 1 one_pos) p
  have hx₀p : x₀ ≠ p := fun e => hpR (e ▸ hx₀R)
  have hdx₀ : 0 < dist x₀ p := dist_pos.2 hx₀p
  set ρ₁ : ℝ := min (1 / 2) (dist x₀ p) with hρ₁
  have hρ₁pos : 0 < ρ₁ := lt_min (by norm_num) hdx₀
  let nxt : Pt × ℝ × ℝ → Pt × ℝ × ℝ := fun s =>
    (X1 s.1 s.2.1 s.2.2, s.2.2, min (s.2.2 / 2) (infDist p (B1 s.1 s.2.1 s.2.2)))
  let st : ℕ → Pt × ℝ × ℝ := fun n => Nat.rec (x₀, 1, ρ₁) (fun _ s => nxt s) n
  have hst : ∀ n, st (n + 1) = nxt (st n) := fun n => rfl
  -- invariants
  have hinv : ∀ n, 0 < (st n).2.1 ∧ 0 < (st n).2.2 ∧ (st n).1 ∈ R ∧
      (st n).1 ∈ ball p (δ (st n).2.1) ∧ (st n).2.2 ≤ (st n).2.1 / 2 := by
    intro n
    induction n with
    | zero =>
      refine ⟨one_pos, hρ₁pos, hx₀R, hx₀b, ?_⟩
      show ρ₁ ≤ 1 / 2
      exact min_le_left _ _
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4, -⟩ := ih
      rw [hst]
      have hβR := hB1R _ _ _ h1 h2 h3 h4
      have hβarc := hB1arc _ _ _ h1 h2 h3 h4
      have hpβ : p ∉ B1 (st n).1 (st n).2.1 (st n).2.2 := fun h => hpR (hβR h)
      have hinf : 0 < infDist p (B1 (st n).1 (st n).2.1 (st n).2.2) :=
        (hβarc.isClosed.notMem_iff_infDist_pos ⟨_, hβarc.left_mem⟩).1 hpβ
      refine ⟨h2, lt_min (by linarith) hinf, hX1R _ _ _ h1 h2 h3 h4,
        hX1b _ _ _ h1 h2 h3 h4, min_le_left _ _⟩
  set xs : ℕ → Pt := fun n => (st n).1 with hxs
  set ρ : ℕ → ℝ := fun n => (st n).2.1 with hρ
  set β : ℕ → Set Pt := fun n => B1 (st n).1 (st n).2.1 (st n).2.2 with hβ
  have harc : ∀ n, TArc (xs n) (xs (n + 1)) (β n) := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1arc _ _ _ h1 h2 h3 h4
  have hβR : ∀ n, β n ⊆ R := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1R _ _ _ h1 h2 h3 h4
  have hβb : ∀ n, β n ⊆ ball p (ρ n) := fun n => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv n
    exact hB1b _ _ _ h1 h2 h3 h4
  have hρsucc : ∀ n, ρ (n + 1) ≤ ρ n / 2 := fun n => by
    show (st (n + 1)).2.1 ≤ _
    rw [hst]; exact (hinv n).2.2.2.2
  have hρpos : ∀ n, 0 < ρ n := fun n => (hinv n).1
  have hρanti : Antitone ρ := antitone_nat_of_succ_le fun n => by
    have := hρsucc n; have := hρpos n; linarith
  have hρ2 : ∀ n, ρ (n + 2) ≤ infDist p (β n) := fun n => by
    exact min_le_right _ _
  have hρpow : ∀ n, ρ n ≤ 1 / 2 ^ n := by
    intro n
    induction n with
    | zero => show (1 : ℝ) ≤ 1 / 2 ^ 0; norm_num
    | succ n ih =>
      calc ρ (n + 1) ≤ ρ n / 2 := hρsucc n
        _ ≤ (1 / 2 ^ n) / 2 := by linarith
        _ = 1 / 2 ^ (n + 1) := by rw [pow_succ]; field_simp
  obtain ⟨τ, hτsub, hτ⟩ := exists_tarc_of_seq (x := xs) (β := β) (B := p) harc
    (fun n m hnm => by
      refine disjoint_left.mpr fun z hzn hzm => ?_
      have h1 : dist z p < ρ m := mem_ball.1 (hβb m hzm)
      have h2 : ρ m ≤ ρ (n + 2) := hρanti hnm
      have h3 := hρ2 n
      have h4 : infDist p (β n) ≤ dist p z := infDist_le_dist_of_mem hzn
      rw [dist_comm] at h1
      linarith)
    (fun h => by
      have h1 : dist (xs 0) p < ρ 1 := mem_ball.1 (hβb 1 h)
      have h2 : ρ 1 = ρ₁ := rfl
      have h3 : ρ₁ ≤ dist x₀ p := min_le_right _ _
      have h4 : xs 0 = x₀ := rfl
      rw [h4, h2] at h1
      linarith)
    (fun n h => hpR (hβR n h))
    (fun U hU => by
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
      refine eventually_atTop.2 ⟨N, fun n hn => (hβb n).trans ((ball_subset_ball ?_).trans hεU)⟩
      calc ρ n ≤ 1 / 2 ^ n := hρpow n
        _ = (1 / 2) ^ n := by rw [one_div_pow]
        _ ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ ≤ ε := hN.le)
  have hτR : τ \ {p} ⊆ R := by
    rintro z ⟨hz, hzp⟩
    rcases hτsub hz with h | h
    · exact absurd h hzp
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      exact hβR n hn
  have hxs0 : xs 0 = x₀ := rfl
  rw [hxs0] at hτ
  by_cases hyx : y = x₀
  · subst hyx; exact ⟨τ, hτ, hτR⟩
  obtain ⟨α, hαR, hα⟩ := exists_tarc_of_isOpen_plane hRo hRc hy hx₀R hyx
  obtain ⟨γ, hγ, hγarc⟩ := hα.join hτ.symm ⟨x₀, hα.right_mem, hτ.left_mem⟩ hyp
  refine ⟨γ, hγarc, ?_⟩
  rintro z ⟨hz, hzp⟩
  rcases hγ hz with h | h
  · exact hαR h
  · exact hτR ⟨h, hzp⟩

/-- A compact locally connected metric space is semi-locally connected at each point. -/
theorem semiLocConnAt_of_locallyConnected {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] (x : X) : SemiLocConnAt x := by
  intro U hU hxU
  obtain ⟨V, hVn, hVc, hVU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hVn, interior_subset.trans hVU,
    ?_⟩
  have hcpt : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hW : ∀ y ∈ Uᶜ, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ IsConnected W ∧ W ⊆ Vᶜ := by
    intro y hy
    have : Vᶜ ∈ 𝓝 y := hVc.isOpen_compl.mem_nhds fun h => hy (hVU h)
    obtain ⟨W, hWV, hWo, hyW, hWc⟩ := (locallyConnectedSpace_iff_subsets_isOpen_isConnected.1
      inferInstance) y _ this
    exact ⟨W, hWo, hyW, hWc, hWV⟩
  choose! W hWo hyW hWc hWV using hW
  obtain ⟨F, hFU, hFcov⟩ := hcpt.elim_nhds_subcover W fun y hy => (hWo y hy).mem_nhds (hyW y hy)
  refine ⟨F, fun y hy => ?_, fun z hz => ?_⟩
  · exact fun h => hFU y hy (hVU (interior_subset h))
  · obtain ⟨y, hyF, hzy⟩ := mem_iUnion₂.1 (hFcov hz)
    refine mem_iUnion₂.2 ⟨y, hyF, ?_⟩
    exact (hWc y (hFU y hyF)).isPreconnected.subset_connectedComponentIn (hyW y (hFU y hyF))
      ((hWV y (hFU y hyF)).trans (compl_subset_compl.2 interior_subset)) hzy

/-- `[0, 1]` is locally connected. -/
theorem locallyConnectedSpace_unitInterval : LocallyConnectedSpace unitInterval := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨ball x ε, hεU, isOpen_ball, mem_ball_self hε, ⟨x, mem_ball_self hε⟩, ?_⟩
  rw [← IsInducing.subtypeVal.isPreconnected_image]
  have : Subtype.val '' ball x ε = Icc (0 : ℝ) 1 ∩ ball (x : ℝ) ε := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩
    · rintro ⟨hy, hyb⟩; exact ⟨⟨y, hy⟩, hyb, rfl⟩
  rw [this, Real.ball_eq_Ioo]
  exact (ordConnected_Icc.inter ordConnected_Ioo).isPreconnected

/-- An arc is semi-locally connected at each of its points. -/
theorem TArc.semiLocConnAt {a b : Pt} {C : Set Pt} (h : TArc a b C) (z : C) : SemiLocConnAt z := by
  obtain ⟨-, f, hf, rfl, -, -⟩ := h
  have e : unitInterval ≃ₜ range f := hf.toHomeomorph
  haveI : CompactSpace (range f) := e.compactSpace
  haveI := locallyConnectedSpace_unitInterval
  haveI : LocallyConnectedSpace (range f) := e.symm.isOpenEmbedding.locallyConnectedSpace
  exact semiLocConnAt_of_locallyConnected z

/-- The complement of an arc in the plane is connected (Moore 1925, Theorem 9, for the
decomposition into points). -/
theorem TArc.isConnected_compl {a b : Pt} {C : Set Pt} (h : TArc a b C) : IsConnected Cᶜ := by
  have hG := mooreDecomp_ptSetoid
  have h' : IsArcElt (ptHomeo a) (ptHomeo b) (ptHomeo '' C) :=
    (isArcElt_iff_tarc hG).2 (tarc_image_embedding ptHomeo.isEmbedding h)
  have := m25_theorem9 hG h'
  rw [← image_compl_eq ptHomeo.bijective] at this
  exact (ptHomeo.isConnected_image).1 this

/-- An arc in the plane has empty interior. -/
theorem TArc.interior_eq_empty {a b : Pt} {C : Set Pt} (h : TArc a b C) : interior C = ∅ := by
  by_contra hne
  obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.2 hne
  -- a point of the open arc in the interior
  have hcl : C ⊆ closure (C \ {a, b}) := h.subset_closure_diff
  obtain ⟨z, hzi, hzC, hzab⟩ : ∃ z, z ∈ interior C ∧ z ∈ C ∧ z ∉ ({a, b} : Set Pt) := by
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 (hcl (interior_subset hw)) _ isOpen_interior hw
    exact ⟨z, hz1, hz2.1, hz2.2⟩
  have hza : z ≠ a := fun e => hzab (Or.inl e)
  have hzb : z ≠ b := fun e => hzab (Or.inr e)
  obtain ⟨C₁, C₂, h₁, h₂, h12, h12i⟩ := h.split hzC hza hzb
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.1 isOpen_interior z hzi
  -- the punctured ball is connected and lies in `C − z`
  have hpc : IsPreconnected (ball z r \ {z}) :=
    (isConnected_diff_singleton_of_isOpen isOpen_ball (isConnected_ball hr) z).isPreconnected
  have hsub : ball z r \ {z} ⊆ (C₁ \ {z}) ∪ (C₂ \ {z}) := by
    rintro y ⟨hy, hyz⟩
    have : y ∈ C₁ ∪ C₂ := h12 ▸ interior_subset (hrC hy)
    rcases this with h | h
    · exact Or.inl ⟨h, hyz⟩
    · exact Or.inr ⟨h, hyz⟩
  have hnear : ∀ {D : Set Pt} {u : Pt}, TArc z u D → ∃ y ∈ D, y ∈ ball z r ∧ y ≠ z := by
    intro D u hD
    have hzcl : z ∈ closure (D \ {z, u}) := hD.subset_closure_diff hD.left_mem
    obtain ⟨y, hyb, hyD⟩ := mem_closure_iff.1 hzcl _ isOpen_ball (mem_ball_self hr)
    exact ⟨y, hyD.1, hyb, fun e => hyD.2 (Or.inl e)⟩
  obtain ⟨y₁, hy₁C, hy₁b, hy₁z⟩ := hnear h₁.symm
  obtain ⟨y₂, hy₂C, hy₂b, hy₂z⟩ := hnear h₂
  have hy₁n : y₁ ∉ C₂ := fun h => hy₁z (by
    have : y₁ ∈ C₁ ∩ C₂ := ⟨hy₁C, h⟩
    rwa [h12i] at this)
  have hy₂n : y₂ ∉ C₁ := fun h => hy₂z (by
    have : y₂ ∈ C₁ ∩ C₂ := ⟨h, hy₂C⟩
    rwa [h12i] at this)
  have hcov : ball z r \ {z} ⊆ C₂ᶜ ∪ C₁ᶜ := by
    rintro y hy
    rcases hsub hy with h | h
    · by_cases hy2 : y ∈ C₂
      · exact absurd (by
          have : y ∈ C₁ ∩ C₂ := ⟨h.1, hy2⟩
          rwa [h12i] at this) h.2
      · exact Or.inl hy2
    · by_cases hy1 : y ∈ C₁
      · exact absurd (by
          have : y ∈ C₁ ∩ C₂ := ⟨hy1, h.1⟩
          rwa [h12i] at this) h.2
      · exact Or.inr hy1
  rcases isPreconnected_iff_subset_of_disjoint.1 hpc _ _ h₂.isClosed.isOpen_compl
      h₁.isClosed.isOpen_compl hcov (by
        ext y
        simp only [mem_inter_iff, mem_diff, mem_compl_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨hy, -⟩, hy2, hy1⟩
        have : y ∈ C₁ ∪ C₂ := h12 ▸ interior_subset (hrC hy)
        exact this.elim hy1 hy2) with h | h
  · exact h ⟨hy₂b, hy₂z⟩ hy₂C
  · exact h ⟨hy₁b, hy₁z⟩ hy₁C

/-- An end point of an arc does not cut it. -/
theorem TArc.isConnected_compl_end {a b : Pt} {C : Set Pt} (h : TArc a b C) (ha : a ∈ C) :
    IsConnected ({⟨a, ha⟩}ᶜ : Set C) := by
  have : Subtype.val '' ({⟨a, ha⟩}ᶜ : Set C) = C \ {a} := by
    ext z
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, mem_diff]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, fun e => hw (Subtype.ext e)⟩
    · rintro ⟨hz, hza⟩; exact ⟨⟨z, hz⟩, fun e => hza (congrArg Subtype.val e), rfl⟩
  refine ⟨⟨⟨b, h.right_mem⟩, fun e => h.ne (congrArg Subtype.val e).symm⟩, ?_⟩
  rw [← IsInducing.subtypeVal.isPreconnected_image, this]
  exact h.symm.isPreconnected_diff_right

/-- **Every arc of the plane lies on a simple closed curve**: its end points are joined by an arc
meeting it only in them. Both ends are accessible from the (connected) complement of the arc
(`accessible_of_noncut`). -/
theorem TArc.exists_closing_arc {a b : Pt} {C : Set Pt} (h : TArc a b C) :
    ∃ β, TArc a b β ∧ β ∩ C = {a, b} := by
  have hint := TArc.interior_eq_empty h
  have hfr : frontier Cᶜ = C := by
    rw [frontier_compl, frontier, h.isClosed.closure_eq, hint, diff_empty]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ C := by
    by_contra hall
    push_neg at hall
    have : interior C = univ := by
      rw [eq_univ_iff_forall]; intro z
      exact mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset Filter.univ_mem fun w _ => hall w)
    rw [hint] at this
    exact empty_ne_univ this
  have hR : connectedComponentIn Cᶜ x = Cᶜ := (TArc.isConnected_compl h).isPreconnected.connectedComponentIn hx
  have hS := TArc.semiLocConnAt h
  have acc : ∀ {p : Pt}, p ∈ C → TArc a b C → (∀ hp : p ∈ C, IsConnected ({⟨p, hp⟩}ᶜ : Set C)) →
      ∃ τ, TArc x p τ ∧ τ \ {p} ⊆ Cᶜ := by
    intro p hp _ hcut
    have hpx : x ≠ p := fun e => hx (e ▸ hp)
    obtain ⟨τ, hτ, hτR⟩ := accessible_of_noncut h.isCompact ⟨⟨a, h.left_mem⟩, h.isPreconnected⟩ hS hx
      (by rw [hR, hfr]; exact hp) hcut (by rw [hR]; exact hx) hpx
    exact ⟨τ, hτ, hR ▸ hτR⟩
  obtain ⟨τa, hτa, hτaC⟩ := acc h.left_mem h (fun hp => TArc.isConnected_compl_end h hp)
  obtain ⟨τb, hτb, hτbC⟩ := acc h.right_mem h (fun hp => TArc.isConnected_compl_end h.symm hp)
  obtain ⟨β, hβsub, hβ⟩ := hτa.symm.join hτb.symm ⟨x, hτa.left_mem, hτb.left_mem⟩ h.ne
  refine ⟨β, hβ, Subset.antisymm ?_ ?_⟩
  · rintro z ⟨hzβ, hzC⟩
    rcases hβsub hzβ with hz | hz
    · by_cases hza : z = a
      · exact Or.inl hza
      · exact absurd hzC (hτaC ⟨hz, hza⟩)
    · by_cases hzb : z = b
      · exact Or.inr hzb
      · exact absurd hzC (hτbC ⟨hz, hzb⟩)
  · rintro z (rfl | rfl)
    · exact ⟨hβ.left_mem, h.left_mem⟩
    · exact ⟨hβ.right_mem, h.right_mem⟩

/-- A **two-sided collar** of the arc `γ`: an embedding `F` of `[0, 1] × [−1, 1]` into the plane with
`F(t, 0) = γ t` and `F` of the open rectangle open. In its coordinates `γ` is the horizontal segment
of Hagopian's "we assume without loss of generality that `π[E]` is lying on a horizontal line"
(pp. 345, 346). (Moved here unchanged from the batch-159 skeleton.) -/
def IsCollar (γ : unitInterval → Pt) (F : ℝ × ℝ → Pt) : Prop :=
  IsEmbedding ((Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1).restrict F) ∧
    (∀ t : unitInterval, F ((t : ℝ), 0) = γ t) ∧ IsOpen (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))

/-- **Every arc in the plane has a two-sided collar.** -/
theorem exists_collar_aux {γ : unitInterval → Pt} (hγ : IsEmbedding γ) : ∃ F, IsCollar γ F := by
  set Γ := range γ
  set a := γ 0
  set b := γ 1
  have hab : a ≠ b := fun e => zero_ne_one (hγ.injective e)
  have hΓ : TArc a b Γ := ⟨hab, γ, hγ, rfl, rfl, rfl⟩
  obtain ⟨β, hβ, hβΓ⟩ := TArc.exists_closing_arc hΓ
  set J₁ := Γ ∪ β
  have hΓβ : Γ ∩ β = {a, b} := by rw [inter_comm]; exact hβΓ
  have hJ₁ : TSCC J₁ := ⟨a, b, Γ, β, hΓ, hβ, hΓβ, rfl⟩
  obtain ⟨I₁, E₁, hIo, hIc, hEo, hEc, hIE, hU, hIb, hEb, hIf, hEf⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ₁)
  have hIJ : Disjoint I₁ J₁ := disjoint_left.2 fun z hz hzJ =>
    (hU.symm ▸ (Or.inl hz : z ∈ I₁ ∪ E₁) : z ∈ J₁ᶜ) hzJ
  have hEJ : Disjoint E₁ J₁ := disjoint_left.2 fun z hz hzJ =>
    (hU.symm ▸ (Or.inr hz : z ∈ I₁ ∪ E₁) : z ∈ J₁ᶜ) hzJ
  have haJ : a ∈ J₁ := Or.inl hΓ.left_mem
  have hbJ : b ∈ J₁ := Or.inl hΓ.right_mem
  obtain ⟨β₂, hβ₂, hβ₂I⟩ := exists_side_arc hJ₁ hIc hIJ hIf haJ hbJ hab
  obtain ⟨R₁, R₂, ⟨o₁, c₁, b₁, f₁⟩, ⟨o₂, c₂, b₂, f₂⟩, hsplit, hR12⟩ :=
    plane_split hJ₁ hIo hIc hIb hIf hΓ hβ hΓβ rfl hβ₂ hβ₂I
  have hβ₂Γ : β₂ ∩ Γ = {a, b} := by
    apply Subset.antisymm
    · rintro z ⟨hz2, hzΓ⟩
      by_contra hz
      exact disjoint_left.1 hIJ (hβ₂I ⟨hz2, hz⟩) (Or.inl hzΓ)
    · rintro z (rfl | rfl)
      · exact ⟨hβ₂.left_mem, hΓ.left_mem⟩
      · exact ⟨hβ₂.right_mem, hΓ.right_mem⟩
  have hβ₂β : β₂ ∩ β ⊆ Γ := by
    rintro z ⟨hz2, hzβ⟩
    by_contra hz
    have hzab : z ∉ ({a, b} : Set Pt) := fun h => hz (by
      rcases h with rfl | rfl
      · exact hΓ.left_mem
      · exact hΓ.right_mem)
    exact disjoint_left.1 hIJ (hβ₂I ⟨hz2, hzab⟩) (Or.inr hzβ)
  set J₂ := β₂ ∪ Γ
  have hJ₂ : TSCC J₂ := ⟨a, b, β₂, Γ, hβ₂, hΓ, hβ₂Γ, rfl⟩
  obtain ⟨g₁, hg₁, hg₁0, hg₁r, hg₁Γ, hg₁S, W₁, hW₁o, hW₁⟩ :=
    isHalfCollar_bounded hJ₂ o₁ c₁ b₁ f₁ hγ (subset_union_right)
  obtain ⟨g₂, hg₂, hg₂0, hg₂r, hg₂Γ, hg₂S, W₂, hW₂o, hW₂⟩ :=
    isHalfCollar_unbounded hJ₁ hIo hIc.nonempty hIb hEo hEc hEf hIE hU hγ subset_union_left
  have hR₁I : R₁ ⊆ I₁ := fun z hz => ((hsplit.symm ▸ (Or.inl hz : z ∈ R₁ ∪ R₂)) :
    z ∈ I₁ \ β₂).1
  have hR₂I : R₂ ⊆ I₁ := fun z hz => ((hsplit.symm ▸ (Or.inr hz : z ∈ R₁ ∪ R₂)) :
    z ∈ I₁ \ β₂).1
  -- (S1) the two sides meet only in `Γ`
  have S1 : ∀ z, z ∈ R₁ ∪ J₂ → z ∈ E₁ ∪ J₁ → z ∈ Γ := by
    intro z h1 h2
    have notI : z ∉ I₁ := fun hzI => h2.elim (disjoint_left.1 hIE hzI)
      (disjoint_left.1 hIJ hzI)
    rcases h1 with h1 | h1 | h1
    · exact absurd (hR₁I h1) notI
    · by_contra hz
      have hzab : z ∉ ({a, b} : Set Pt) := fun h => hz (by
        rcases h with rfl | rfl
        · exact hΓ.left_mem
        · exact hΓ.right_mem)
      exact notI (hβ₂I ⟨h1, hzab⟩)
    · exact h1
  -- (S2) near the open arc, the two closed sides fill a neighbourhood
  have S2a : (closure R₂)ᶜ ⊆ (R₁ ∪ J₂) ∪ (E₁ ∪ J₁) := by
    intro w hw
    by_cases hwJ : w ∈ J₁
    · exact Or.inr (Or.inr hwJ)
    have : w ∈ I₁ ∪ E₁ := hU ▸ hwJ
    rcases this with hwI | hwE
    · by_cases hwβ : w ∈ β₂
      · exact Or.inl (Or.inr (Or.inl hwβ))
      have : w ∈ R₁ ∪ R₂ := hsplit ▸ ⟨hwI, hwβ⟩
      rcases this with h | h
      · exact Or.inl (Or.inl h)
      · exact absurd (subset_closure h) hw
    · exact Or.inr (Or.inl hwE)
  have S2b : ∀ t : unitInterval, 0 < t → t < 1 → γ t ∉ closure R₂ := by
    intro t ht0 ht1 h
    rw [closure_eq_self_union_frontier, f₂] at h
    have hta : γ t ≠ a := fun e => ht0.ne' (hγ.injective e)
    have htb : γ t ≠ b := fun e => ht1.ne (hγ.injective e)
    have hnab : γ t ∉ ({a, b} : Set Pt) := by
      rintro (e | e)
      · exact hta e
      · exact htb e
    rcases h with h | h | h
    · exact disjoint_left.1 hIJ (hR₂I h) (Or.inl (mem_range_self t))
    · exact hnab (hβ₂Γ ▸ ⟨h, mem_range_self t⟩)
    · exact hnab (hΓβ ▸ ⟨mem_range_self t, h⟩)
  -- the collar
  set P := projIcc (0 : ℝ) 1 zero_le_one
  have hP : ∀ t : unitInterval, P (t : ℝ) = t := fun t => projIcc_val zero_le_one t
  have hP0 : P 0 = 0 := by simpa using hP 0
  have hPv : ∀ x, x ∈ Icc (0 : ℝ) 1 → (P x : ℝ) = x := fun x hx =>
    congrArg Subtype.val (projIcc_of_mem zero_le_one hx)
  set F : ℝ × ℝ → Pt := fun q =>
    if 0 ≤ q.2 then g₁ (P q.1, P q.2) else g₂ (P q.1, P (-q.2)) with hFdef
  have hcont : Continuous F := by
    refine Continuous.if_le ?_ ?_ continuous_const continuous_snd ?_
    · exact hg₁.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
        (continuous_projIcc.comp continuous_snd))
    · exact hg₂.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
        (continuous_projIcc.comp continuous_snd.neg))
    · intro q hq
      simp only [← hq, neg_zero, hP0, hg₁0, hg₂0]
  have hF0 : ∀ t : unitInterval, F ((t : ℝ), 0) = γ t := fun t => by
    simp [hFdef, hP, hP0, hg₁0]
  have hPinj : ∀ {x y : ℝ}, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 → P x = P y → x = y :=
    fun hx hy e => by
      have := congrArg Subtype.val e
      rwa [hPv _ hx, hPv _ hy] at this
  have hP2 : ∀ {x : ℝ}, 0 < x → x ≤ 1 → P x ≠ 0 := fun hx0 hx1 e => by
    have := congrArg Subtype.val e
    rw [hPv _ ⟨hx0.le, hx1⟩] at this
    exact hx0.ne' this
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hinj : InjOn F K := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨x', y'⟩ ⟨hx', hy'⟩ e
    simp only [mem_Icc] at hx hy hx' hy'
    simp only [hFdef] at e
    have cross : ∀ {x y x' y' : ℝ}, 0 ≤ y → y' < 0 → -1 ≤ y' →
        g₁ (P x, P y) = g₂ (P x', P (-y')) → False := by
      intro x y x' y' hy hy' hy1 e
      have hz : g₁ (P x, P y) ∈ Γ :=
        S1 _ (hg₁r (mem_range_self _)) (e ▸ hg₂r (mem_range_self _))
      have := hg₂Γ (P x', P (-y')) (e ▸ hz)
      exact hP2 (by linarith) (by linarith) this
    split_ifs at e with h1 h2 h2
    · have := hg₁.injective e
      simp only [Prod.mk.injEq] at this
      rw [hPinj ⟨hx.1, hx.2⟩ ⟨hx'.1, hx'.2⟩ this.1, hPinj ⟨h1, by linarith⟩ ⟨h2, by linarith⟩ this.2]
    · exact (cross h1 (lt_of_not_ge h2) hy'.1 e).elim
    · exact (cross h2 (lt_of_not_ge h1) hy.1 e.symm).elim
    · have := hg₂.injective e
      simp only [Prod.mk.injEq] at this
      have h3 := hPinj ⟨by linarith [lt_of_not_ge h1], by linarith⟩
        ⟨by linarith [lt_of_not_ge h2], by linarith⟩ this.2
      rw [hPinj ⟨hx.1, hx.2⟩ ⟨hx'.1, hx'.2⟩ this.1, neg_inj.1 h3]
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hemb : IsEmbedding (K.restrict F) := by
    refine (Continuous.isClosedEmbedding (hcont.comp continuous_subtype_val) ?_).isEmbedding
    rintro ⟨p, hp⟩ ⟨q, hq⟩ e
    exact Subtype.ext (hinj hp hq e)
  refine ⟨F, hemb, hF0, ?_⟩
  -- the image of the open rectangle
  set O := {p : unitInterval × unitInterval | 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 1}
  have himg : F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) = g₁ '' O ∪ g₂ '' O := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
      have hPx0 : 0 < P x := by
        show (0 : ℝ) < (P x : ℝ); rw [hPv _ ⟨hx0.le, hx1.le⟩]; exact hx0
      have hPx1 : P x < 1 := by
        show (P x : ℝ) < 1; rw [hPv _ ⟨hx0.le, hx1.le⟩]; exact hx1
      by_cases hy : 0 ≤ y
      · left
        refine ⟨(P x, P y), ⟨hPx0, hPx1, ?_⟩, by simp [hFdef, hy]⟩
        show (P y : ℝ) < 1; rw [hPv _ ⟨hy, hy1.le⟩]; exact hy1
      · right
        push_neg at hy
        refine ⟨(P x, P (-y)), ⟨hPx0, hPx1, ?_⟩, by simp [hFdef, not_le.2 hy]⟩
        show (P (-y) : ℝ) < 1; rw [hPv _ ⟨by linarith, by linarith⟩]; linarith
    · rintro _ (⟨p, ⟨h1, h2, h3⟩, rfl⟩ | ⟨p, ⟨h1, h2, h3⟩, rfl⟩)
      · refine ⟨((p.1 : ℝ), (p.2 : ℝ)), ⟨⟨h1, h2⟩, ⟨by linarith [p.2.2.1], h3⟩⟩, ?_⟩
        simp [hFdef, p.2.2.1, hP]
      · by_cases hp2 : (p.2 : ℝ) = 0
        · refine ⟨((p.1 : ℝ), 0), ⟨⟨h1, h2⟩, ⟨by norm_num, by norm_num⟩⟩, ?_⟩
          have : p = (p.1, 0) := Prod.ext rfl (Subtype.ext hp2)
          rw [this, hF0, hg₂0]
        · have hp2' : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.2.1 (Ne.symm hp2)
          refine ⟨((p.1 : ℝ), -(p.2 : ℝ)), ⟨⟨h1, h2⟩, ⟨by
            have : (p.2 : ℝ) < 1 := h3
            linarith, by linarith⟩⟩, ?_⟩
          simp [hFdef, hp2', hP]
  rw [himg, isOpen_iff_mem_nhds]
  -- points on the bottom side
  have bottom : ∀ t : unitInterval, 0 < t → t < 1 →
      g₁ '' O ∪ g₂ '' O ∈ 𝓝 (γ t) := by
    intro t ht0 ht1
    have hm₁ : γ t ∈ W₁ := by
      have : γ t ∈ g₁ '' O := ⟨(t, 0), ⟨ht0, ht1, by simp⟩, hg₁0 t⟩
      rw [← hW₁] at this; exact this.1
    have hm₂ : γ t ∈ W₂ := by
      have : γ t ∈ g₂ '' O := ⟨(t, 0), ⟨ht0, ht1, by simp⟩, hg₂0 t⟩
      rw [← hW₂] at this; exact this.1
    refine Filter.mem_of_superset (inter_mem (inter_mem (hW₁o.mem_nhds hm₁)
      (hW₂o.mem_nhds hm₂)) (isClosed_closure.isOpen_compl.mem_nhds (S2b t ht0 ht1))) ?_
    rintro w ⟨⟨hw1, hw2⟩, hw3⟩
    rcases S2a hw3 with h | h
    · exact Or.inl (hW₁ ▸ ⟨hw1, h⟩)
    · exact Or.inr (hW₂ ▸ ⟨hw2, h⟩)
  rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · by_cases hp2 : p.2 = 0
    · have : p = (p.1, 0) := Prod.ext rfl hp2
      rw [this, hg₁0]; exact bottom p.1 hp.1 hp.2.1
    · have hp2' : 0 < p.2 := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hp2)
      have hin := hg₁S p hp.1 hp.2.1 hp2' hp.2.2
      have hW : g₁ p ∈ W₁ := by
        have : g₁ p ∈ g₁ '' O := ⟨p, hp, rfl⟩
        rw [← hW₁] at this; exact this.1
      refine Filter.mem_of_superset (inter_mem (o₁.mem_nhds hin) (hW₁o.mem_nhds hW)) ?_
      rintro w ⟨hw1, hw2⟩
      exact Or.inl (hW₁ ▸ ⟨hw2, Or.inl hw1⟩)
  · by_cases hp2 : p.2 = 0
    · have : p = (p.1, 0) := Prod.ext rfl hp2
      rw [this, hg₂0]; exact bottom p.1 hp.1 hp.2.1
    · have hp2' : 0 < p.2 := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hp2)
      have hin := hg₂S p hp.1 hp.2.1 hp2' hp.2.2
      have hW : g₂ p ∈ W₂ := by
        have : g₂ p ∈ g₂ '' O := ⟨p, hp, rfl⟩
        rw [← hW₂] at this; exact this.1
      refine Filter.mem_of_superset (inter_mem (hEo.mem_nhds hin) (hW₂o.mem_nhds hW)) ?_
      rintro w ⟨hw1, hw2⟩
      exact Or.inr (hW₂ ▸ ⟨hw2, Or.inl hw1⟩)

end HPC.Hagopian
