import HPC.Moore.M43Dual

/-!
# Theorem 43: the component of an intersection adjacent to a point (batch 140, item B)

See `HPC/Moore/M43Dual.lean` for the plan. `dual_component` is the main step.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

section Comp

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The component of `U ∩ I'` adjacent to `O`** is the interior of a closed curve on `J + J'`
through `O` (`J ∩ J'` having two points). *Axioms used: 1–8.* -/
theorem dual_component {J I J' I' U : Set S} (hI : σ.IsInteriorOf J I)
    (hI' : σ.IsInteriorOf J' I')
    (hU : U = I ∨ (U = (@closure S σ.topology I)ᶜ ∧ ¬ I ⊆ I')) {O : S} (hO : O ∈ J)
    (hOI' : O ∈ I') {y y' : S} (hy : y ∈ J ∩ J') (hy' : y' ∈ J ∩ J') (hyy : y ≠ y') :
    ∃ J'' I'', σ.IsInteriorOf J'' I'' ∧ O ∈ J'' ∧ J'' ⊆ J ∪ J' ∧ I'' ⊆ U ∩ I' := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, hIc, -, hfr, hEo, -, -, hfrE, hcl, hdisIJ, hdisEJ, hcompl, hJcpt, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨hI'o, hI'c, -, hfr', hE'o, -, -, -, hcl', hdisI'J', -, hcompl', hJ'cpt, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI'
  have hJc : IsClosed J := hJcpt.isClosed
  have hJ'c : IsClosed J' := hJ'cpt.isClosed
  have hJcl : J ⊆ closure I := hfr ▸ frontier_subset_closure
  have hJ'cl : J' ⊆ closure I' := hfr' ▸ frontier_subset_closure
  have hOJ' : O ∉ J' := fun h => disjoint_left.mp hdisI'J' hOI' h
  -- the side `U` of `J` and the other side `U'`
  obtain ⟨U', hUo, hU'o, hUU', hsplit, hclU⟩ : ∃ U', IsOpen U ∧ IsOpen U' ∧ Disjoint U U' ∧
      Jᶜ = U ∪ U' ∧ closure U ⊆ U ∪ J := by
    rcases hU with hU | ⟨hU, -⟩
    · subst U
      exact ⟨(closure I)ᶜ, hIo, hEo, disjoint_compl_right.mono_left subset_closure, hcompl,
        hcl.subset⟩
    · subst U
      refine ⟨I, hEo, hIo, (disjoint_compl_right.mono_left subset_closure).symm,
        by rw [hcompl, union_comm], ?_⟩
      rw [closure_eq_union_frontier hEo, hfrE]
  have hUJ : Disjoint U J := by
    rw [disjoint_left]
    intro x hxU hxJ
    have : x ∈ Jᶜ := by rw [hsplit]; exact Or.inl hxU
    exact this hxJ
  -- the component `W`
  obtain ⟨P, hPo, hPc, hPsub, hOP⟩ := adjacent_piece h1 h2 h3 h4 h5 h6 h7 h8 hI hI' hU hO hOI'
  obtain ⟨x₀, hx₀⟩ : P.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hOP
    exact hOP
  set W := connectedComponentIn (U ∩ I') x₀ with hWdef
  have hWo : IsOpen W := (hUo.inter hI'o).connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hPW : P ⊆ W := hPc.subset_connectedComponentIn hx₀ hPsub
  have hOW : O ∈ closure W := closure_mono hPW hOP
  have hx₀W : x₀ ∈ W := hPW hx₀
  have hWsub : W ⊆ U ∩ I' := connectedComponentIn_subset _ _
  have hWJ : Disjoint W J := disjoint_left.mpr fun x hx hxJ =>
    disjoint_left.mp hUJ (hWsub hx).1 hxJ
  have hWJ' : Disjoint W J' := disjoint_left.mpr fun x hx hxJ =>
    disjoint_left.mp hdisI'J' (hWsub hx).2 hxJ
  have hclW : ∀ z ∈ closure W, z ∈ U ∩ I' → z ∈ W := fun z hz hzU =>
    mem_connectedComponentIn_of_mem_closure hz hzU
  have hWU : closure W ⊆ U ∪ J := (closure_mono fun x hx => (hWsub hx).1).trans hclU
  have hWI' : closure W ⊆ I' ∪ J' := by
    rw [← hcl']; exact closure_mono fun x hx => (hWsub hx).2
  have hfrW' : ∀ z ∈ closure W, z ∉ W → z ∈ J ∨ z ∈ J' := by
    intro z hz hzW
    rcases hWU hz with h | h
    · rcases hWI' hz with h' | h'
      · exact absurd (hclW z hz ⟨h, h'⟩) hzW
      · exact Or.inr h'
    · exact Or.inl h
  have hcl₁V : closure W ∩ (I' \ J) ⊆ W := by
    rintro z ⟨hz, hzI, hzJ⟩
    exact hclW z hz ⟨(hWU hz).resolve_right hzJ, hzI⟩
  have hcl₂V : closure W ∩ (U \ J') ⊆ W := by
    rintro z ⟨hz, hzU, hzJ⟩
    exact hclW z hz ⟨hzU, (hWI' hz).resolve_right hzJ⟩
  have hWsub₁ : W ⊆ I' \ J := fun x hx => ⟨(hWsub hx).2, fun h => disjoint_left.mp hWJ hx h⟩
  have hWsub₂ : W ⊆ U \ J' := fun x hx => ⟨(hWsub hx).1, fun h => disjoint_left.mp hWJ' hx h⟩
  -- the chord of `J` through `O`, and `O'`
  obtain ⟨p, q, d, hd, hdJ, hp, hq, hOd, hdJ'⟩ :=
    chord_through h1 h3 h4 h51 hI.1 hJ'c hO hOJ' hy hy' hyy
  have hdI' : d \ {p, q} ⊆ I' := by
    have hsub : d \ {p, q} ⊆ I' ∪ (closure I')ᶜ := fun z hz => by
      have : z ∈ J'ᶜ := fun h => disjoint_left.mp hdJ' hz h
      rwa [hcompl'] at this
    rcases hd.isPreconnected_diff.subset_or_subset hI'o hE'o
      (disjoint_compl_right.mono_left subset_closure) hsub with h | h
    · exact h
    · exact absurd (subset_closure hOI') (h hOd)
  have hdW : d ⊆ closure W := chord_side h1 h2 h3 h4 h5 h6 h7 h8 hI.1 hI'o hd hdJ hdI' hWo hWc
    hWsub₁ hcl₁V ⟨O, hOd, hOW⟩
  obtain ⟨O', hO'd, hO'O⟩ : ∃ O' ∈ d \ {p, q}, O' ≠ O := by
    obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓu, hΓi⟩ :=
      hd.split hOd.1 (fun e => hOJ' (e ▸ hp)) (fun e => hOJ' (e ▸ hq))
    obtain ⟨z, hz, hzpO⟩ := hΓ₁.nonempty_diff
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzpO
    refine ⟨z, ⟨hΓu ▸ Or.inl hz, ?_⟩, hzpO.2⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨hzpO.1, fun hzq => ?_⟩
    have : z ∈ Γ₁ ∩ Γ₂ := ⟨hz, hzq ▸ hΓ₂.right_mem⟩
    rw [hΓi] at this
    exact hzpO.2 this
  have hO'J' : O' ∉ J' := fun h => disjoint_left.mp hdJ' hO'd h
  have hO'J : O' ∈ J := hdJ hO'd.1
  have hO'W : O' ∈ closure W := hdW hO'd.1
  -- the two arcs of `J` from `O` to `O'`
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ :=
    exists_two_arcs_of_isSCC h1 h3 h4 h51 hI.1 hO hO'J hO'O.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  have hJ'W : ¬ J' ⊆ closure W := by
    intro h
    rcases hU with hU | ⟨hU, hnot⟩
    · subst U
      have hI'I : I' ⊆ I := th21Prop h1 h3 h4 h5 h7 I hI.2.1 I' hI'.2.1
        (by rw [hfr']; exact h.trans (closure_mono fun x hx => (hWsub hx).1))
      exact disjoint_left.mp hdisIJ (hI'I hOI') hO
    · apply hnot
      have hJ'I : Disjoint I J' := by
        rw [disjoint_left]
        intro x hxI hxJ
        rcases hWU (h hxJ) with h' | h'
        · rw [hU] at h'; exact h' (subset_closure hxI)
        · exact disjoint_left.mp hdisIJ hxI h'
      obtain ⟨w, hwI', hwI⟩ := mem_closure_iff_nhds.mp (hJcl hO) I' (hI'o.mem_nhds hOI')
      exact conn_sub_of_frontier hIc (by rw [hfr']; exact hJ'I) ⟨w, hwI, hwI'⟩
  -- the pocket property on an arc of `J` from `O`
  have hpockU : ∀ {f : unitInterval → S}, IsEmbedding f → range f ⊆ J → f 0 = O →
      ∀ u v Z, u < v → TArc (f u) (f v) Z → Z ⊆ J' → Z ⊆ closure W → Z \ {f u, f v} ⊆ U →
      Disjoint (f '' Ioo u v) (closure W) := by
    intro f hf hfJ hf0 u v Z huv hZ hZJ hZW hZU
    have hu0 : 0 < u := lt_of_le_of_ne nonneg' fun e => hOJ' (hf0 ▸ e ▸ hZJ hZ.left_mem)
    have hOC : O ∉ f '' Icc u v := by
      rintro ⟨t, ht, e⟩
      rw [← hf0] at e
      have := hf.injective e
      subst this
      exact absurd ht.1 (not_le.mpr hu0)
    have hC := TArc.image_Icc hf huv
    have hCJ : f '' Icc u v ⊆ J := (image_subset_range _ _).trans hfJ
    rw [← image_Icc_diff_ends hf.injective]
    rcases hU with hU | ⟨hU, -⟩
    · subst U
      exact pocket_int h1 h2 h3 h4 h5 h7 h8 hI hZ hZU hC hCJ hO hOC hWc
        (fun x hx => (hWsub hx).1) (hWJ'.mono_right hZJ) hOW
    · subst U
      exact pocket_ext h1 h2 h3 h4 h5 h7 h8 hI hZ hZU hC hCJ hO hOC hWc
        (fun x hx => (hWsub hx).1) (hWJ'.mono_right hZJ) hOW
  -- the replacement on one arc
  have half : ∀ D, TArc O O' D → D ⊆ J → ∃ D', TArc O O' D' ∧
      (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧ b ∈ D ∧ Z ⊆ J' ∧
        Z \ {a, b} ⊆ U ∧ x ∈ Z ∧ Z ⊆ D') ∧
      (∀ Z a b, TArc a b Z → a ∈ D → b ∈ D → Z ⊆ J' → Z ⊆ closure W →
        Z \ {a, b} ⊆ U → Z ⊆ D') ∧
      closure W ∩ D ⊆ D' := by
    rintro D ⟨-, f, hf, rfl, hf0, hf1⟩ hDJ
    obtain ⟨D', hD', hD'sub, hD'Z, hD'V⟩ := half_replace_gen h1 h3 h4 h51 hI'.1 hUJ.symm hf hDJ
      hJ'W (hpockU hf hDJ hf0)
    rw [hf0, hf1] at hD'
    refine ⟨D', hD', fun x hx => ?_, fun Z a b hZ ha hb hZJ hZV hZE => ?_, hD'V⟩
    · rcases hD'sub hx with h | ⟨Z, ⟨u, v, huv, hZ, hZJ, hZV, hZE⟩, hxZ⟩
      · exact Or.inl h
      · exact Or.inr ⟨Z, f u, f v, hZ, mem_range_self _, mem_range_self _, hZJ, hZE, hxZ,
          hD'Z Z u v huv hZ hZJ hZV hZE⟩
    · obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      rcases lt_trichotomy u v with huv | huv | huv
      · exact hD'Z Z u v huv hZ hZJ hZV hZE
      · exact absurd (congrArg f huv) hZ.ne
      · exact hD'Z Z v u huv hZ.symm hZJ hZV (by rwa [pair_comm])
  have hD₁J : D₁ ⊆ J := hDu ▸ subset_union_left
  have hD₂J : D₂ ⊆ J := hDu ▸ subset_union_right
  obtain ⟨D₁', hD₁', hD₁'sub, hD₁'Z, hD₁'V⟩ := half D₁ hD₁ hD₁J
  obtain ⟨D₂', hD₂', hD₂'sub, hD₂'Z, hD₂'V⟩ := half D₂ hD₂ hD₂J
  have onJ : ∀ {D D' : Set S}, (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧ b ∈ D ∧
      Z ⊆ J' ∧ Z \ {a, b} ⊆ U ∧ x ∈ Z ∧ Z ⊆ D') → ∀ x ∈ D', x ∈ J → x ∈ D := by
    intro D D' hsub x hx hxJ
    rcases hsub x hx with h | ⟨Z, a, b, -, ha, hb, -, hZE, hxZ, -⟩
    · exact h
    · by_contra hxD
      have hxab : x ∉ ({a, b} : Set S) := by
        rintro (h | h)
        · exact hxD (h ▸ ha)
        · exact hxD ((mem_singleton_iff.mp h) ▸ hb)
      exact disjoint_left.mp hUJ (hZE ⟨hxZ, hxab⟩) hxJ
  have hOOJ : ∀ x ∈ D₁ ∩ D₂, x ∉ J' := by
    intro x hx hxJ
    rw [hDi] at hx
    rcases hx with h | h
    · exact hOJ' (h ▸ hxJ)
    · exact hO'J' ((mem_singleton_iff.mp h) ▸ hxJ)
  have hint : D₁' ∩ D₂' = {O, O'} := by
    have hgen : ∀ x ∈ D₁' ∩ D₂', x ∈ J → x ∈ ({O, O'} : Set S) := fun x hx hxJ => by
      rw [← hDi]
      exact ⟨onJ hD₁'sub x hx.1 hxJ, onJ hD₂'sub x hx.2 hxJ⟩
    apply subset_antisymm
    · intro x hx
      by_cases hxJ : x ∈ J
      · exact hgen x hx hxJ
      exfalso
      rcases hD₁'sub x hx.1 with h | ⟨Z₁, a₁, b₁, hZ₁, ha₁, hb₁, hZ₁J, hZ₁E, hxZ₁, hZ₁D⟩
      · exact hxJ (hD₁J h)
      rcases hD₂'sub x hx.2 with h | ⟨Z₂, a₂, b₂, hZ₂, ha₂, hb₂, hZ₂J, hZ₂E, hxZ₂, hZ₂D⟩
      · exact hxJ (hD₂J h)
      have hx₁ : x ∈ Z₁ \ {a₁, b₁} := ⟨hxZ₁, by
        rintro (h | h)
        · exact hxJ (h ▸ hD₁J ha₁)
        · exact hxJ ((mem_singleton_iff.mp h) ▸ hD₁J hb₁)⟩
      have hx₂ : x ∈ Z₂ \ {a₂, b₂} := ⟨hxZ₂, by
        rintro (h | h)
        · exact hxJ (h ▸ hD₂J ha₂)
        · exact hxJ ((mem_singleton_iff.mp h) ▸ hD₂J hb₂)⟩
      have s1 := chord_subset h1 h3 h4 h51 hI'.1 hZ₁ hZ₂ hZ₁J hZ₂J (hD₁J ha₁) (hD₁J hb₁)
        (hUJ.mono_left hZ₂E) ⟨x, hx₁, hx₂⟩
      have ha₂D : a₂ ∈ D₁' ∩ D₂' := ⟨hZ₁D (s1 hZ₂.left_mem), hZ₂D hZ₂.left_mem⟩
      have := hgen a₂ ha₂D (hD₂J ha₂)
      rw [← hDi] at this
      exact hOOJ a₂ this (hZ₂J hZ₂.left_mem)
    · rintro x (rfl | h)
      · exact ⟨hD₁'.left_mem, hD₂'.left_mem⟩
      · rw [mem_singleton_iff.mp h]; exact ⟨hD₁'.right_mem, hD₂'.right_mem⟩
  have hsubJ : ∀ {D D' : Set S}, D ⊆ J → (∀ x ∈ D', x ∈ D ∨ ∃ Z a b, TArc a b Z ∧ a ∈ D ∧
      b ∈ D ∧ Z ⊆ J' ∧ Z \ {a, b} ⊆ U ∧ x ∈ Z ∧ Z ⊆ D') → D' ⊆ J ∪ J' := by
    intro D D' hDJ hsub x hx
    rcases hsub x hx with h | ⟨Z, a, b, -, -, -, hZJ, -, hxZ, -⟩
    · exact Or.inl (hDJ h)
    · exact Or.inr (hZJ hxZ)
  have hfrJ : frontier W ⊆ D₁' ∪ D₂' := by
    intro z hz
    have hzc : z ∈ closure W := hz.1
    have hzW : z ∉ W := by have := hz.2; rwa [hWo.interior_eq] at this
    by_cases hzJ : z ∈ J
    · rw [← hDu] at hzJ
      rcases hzJ with h | h
      · exact Or.inl (hD₁'V ⟨hzc, h⟩)
      · exact Or.inr (hD₂'V ⟨hzc, h⟩)
    have hzJ' : z ∈ J' := (hfrW' z hzc hzW).resolve_left hzJ
    have hzU : z ∈ U := (hWU hzc).resolve_right hzJ
    obtain ⟨a, b, Z, hZ, hZJ, ha, hb, hzZ, hZJJ⟩ :=
      chord_through h1 h3 h4 h51 hI'.1 hJc hzJ' hzJ ⟨hy.2, hy.1⟩ ⟨hy'.2, hy'.1⟩ hyy
    have hZU : Z \ {a, b} ⊆ U := by
      have hsub : Z \ {a, b} ⊆ U ∪ U' := fun w hw => by
        have : w ∈ Jᶜ := fun h => disjoint_left.mp hZJJ hw h
        rwa [hsplit] at this
      rcases hZ.isPreconnected_diff.subset_or_subset hUo hU'o hUU' hsub with h | h
      · exact h
      · exact absurd (h hzZ) (disjoint_left.mp hUU' hzU)
    have hZW : Z ⊆ closure W := chord_side h1 h2 h3 h4 h5 h6 h7 h8 hI'.1 hUo hZ hZJ hZU hWo hWc
      hWsub₂ hcl₂V ⟨z, hzZ, hzc⟩
    have haJ' : a ∈ J' := hZJ hZ.left_mem
    have hbJ' : b ∈ J' := hZJ hZ.right_mem
    obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu⟩ :=
      exists_two_arcs_of_isSCC h1 h3 h4 h51 hI.1 ha hb hZ.ne
    rw [isArc_iff_tarc h1 h3 h4 h51] at hC₁ hC₂
    obtain ⟨C, hC, hCJ, hOC⟩ : ∃ C, TArc a b C ∧ C ⊆ J ∧ O ∉ C := by
      by_cases hO1 : O ∈ C₁
      · refine ⟨C₂, hC₂, hCu ▸ subset_union_right, fun hO2 => ?_⟩
        have : O ∈ C₁ ∩ C₂ := ⟨hO1, hO2⟩
        rw [hCi] at this
        rcases this with h | h
        · exact hOJ' (h ▸ haJ')
        · exact hOJ' ((mem_singleton_iff.mp h) ▸ hbJ')
      · exact ⟨C₁, hC₁, hCu ▸ subset_union_left, hO1⟩
    have hpk : Disjoint (C \ {a, b}) (closure W) := by
      rcases hU with hU | ⟨hU, -⟩
      · subst U
        exact pocket_int h1 h2 h3 h4 h5 h7 h8 hI hZ hZU hC hCJ hO hOC hWc
          (fun x hx => (hWsub hx).1) (hWJ'.mono_right hZJ) hOW
      · subst U
        exact pocket_ext h1 h2 h3 h4 h5 h7 h8 hI hZ hZU hC hCJ hO hOC hWc
          (fun x hx => (hWsub hx).1) (hWJ'.mono_right hZJ) hOW
    have hO'C : O' ∉ C := by
      intro h
      refine disjoint_left.mp hpk ⟨h, ?_⟩ hO'W
      rintro (e | e)
      · exact hO'J' (e ▸ haJ')
      · exact hO'J' ((mem_singleton_iff.mp e) ▸ hbJ')
    have hCsub : C ⊆ D₂ᶜ ∪ D₁ᶜ := by
      intro w hw
      by_contra hc
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
      have : w ∈ D₁ ∩ D₂ := ⟨hc.2, hc.1⟩
      rw [hDi] at this
      rcases this with h | h
      · exact hOC (h ▸ hw)
      · exact hO'C ((mem_singleton_iff.mp h) ▸ hw)
    have hCe : C ∩ (D₂ᶜ ∩ D₁ᶜ) = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hw hw2 hw1
      have : w ∈ J := hCJ hw
      rw [← hDu] at this
      rcases this with h | h
      exacts [hw1 h, hw2 h]
    rcases (isPreconnected_iff_subset_of_disjoint.mp hC.isPreconnected) _ _
      hD₂.isClosed.isOpen_compl hD₁.isClosed.isOpen_compl hCsub hCe with h | h
    · have hCD : C ⊆ D₁ := fun w hw => by
        have : w ∈ J := hCJ hw
        rw [← hDu] at this
        exact this.resolve_right (h hw)
      exact Or.inl (hD₁'Z Z a b hZ (hCD hC.left_mem) (hCD hC.right_mem) hZJ hZW hZU hzZ.1)
    · have hCD : C ⊆ D₂ := fun w hw => by
        have : w ∈ J := hCJ hw
        rw [← hDu] at this
        exact this.resolve_left (h hw)
      exact Or.inr (hD₂'Z Z a b hZ (hCD hC.left_mem) (hCD hC.right_mem) hZJ hZW hZU hzZ.1)
  -- the curve, and `W` is its interior
  set Jn := D₁' ∪ D₂' with hJn
  have hJt : TSCC Jn := ⟨O, O', D₁', D₂', hD₁', hD₂', hint, rfl⟩
  have hJsub : Jn ⊆ J ∪ J' := union_subset (hsubJ hD₁J hD₁'sub) (hsubJ hD₂J hD₂'sub)
  have hJs : σ.IsSCC Jn := (isSCC_iff_tscc h1 h3 h4 h51).mpr hJt
  obtain ⟨In, hIn, -⟩ := existsUnique_interior h1 h3 h4 h5 h7 h8 hJs
  obtain ⟨hIno, hInc, -, -, hEno, hEnc, -, -, -, hdisIn, hdisEn, hcomplN, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hIn
  have hWJn : Disjoint W Jn := by
    refine disjoint_left.mpr fun x hx hxJ => ?_
    rcases hJsub hxJ with h | h
    · exact disjoint_left.mp hWJ hx h
    · exact disjoint_left.mp hWJ' hx h
  have hWsplit : W ⊆ In ∪ (closure In)ᶜ := fun x hx => by
    have : x ∈ Jnᶜ := fun h => disjoint_left.mp hWJn hx h
    rwa [hcomplN] at this
  -- a connected set missing `Jn` and meeting `W` lies in `W`
  have absorb : ∀ T, IsPreconnected T → Disjoint T Jn → (T ∩ W).Nonempty → T ⊆ W := by
    intro T hT hTJ hTW
    have hsub : T ⊆ W ∪ (closure W)ᶜ := fun x hx => by
      by_cases hxc : x ∈ closure W
      · left
        by_contra hxW
        exact disjoint_left.mp hTJ hx (hfrJ ⟨hxc, by rwa [hWo.interior_eq]⟩)
      · exact Or.inr hxc
    exact hT.subset_left_of_subset_union hWo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub hTW
  have hWIn : W ⊆ In := by
    rcases hWc.subset_or_subset hIno hEno (disjoint_compl_right.mono_left subset_closure)
      hWsplit with h | h
    · exact h
    · exfalso
      have hEW : (closure In)ᶜ ⊆ W := absorb _ hEnc hdisEn ⟨x₀, h hx₀W, hx₀W⟩
      have hEc : IsCompact (closure (closure In)ᶜ) :=
        (isCompact_closure_region h1 h4 hI'.2.1).of_isClosed_subset isClosed_closure
          (closure_mono (hEW.trans fun x hx => (hWsub hx).2))
      exact not_isCompact_univ h1 h5 (((isCompact_closure_region h1 h4 hIn.2.1).union
        hEc).of_isClosed_subset isClosed_univ fun x _ => by
          by_cases hx : x ∈ closure In
          · exact Or.inl hx
          · exact Or.inr (subset_closure hx))
  have hInW : In ⊆ W := absorb _ hInc hdisIn ⟨x₀, hWIn hx₀W, hx₀W⟩
  have hWeq : W = In := subset_antisymm hWIn hInW
  refine ⟨Jn, In, hIn, ?_, hJsub, hWeq ▸ hWsub⟩
  exact hfrJ ⟨hOW, by rw [hWo.interior_eq]; exact fun h => disjoint_left.mp hWJ h hO⟩

end Comp

end HPC.Moore
