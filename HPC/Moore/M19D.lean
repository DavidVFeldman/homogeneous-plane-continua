import HPC.Moore.M19B

/-!
# Moore 1919: the arc of footnote * of p. 174, used in Theorem D (batch 140, item B)

Theorem D (p. 173) uses: "Within `g₁` (and within `J` except for the point `A₁`) there is* an arc
`A₁E′₁` that has in common with `E₁E′₁` only the point `E′₁`", with footnote *: "Make use of
Theorems 43 and 40 and the existence of the curve `ABTNA` described on page 149 of *Foundations*".
`m19_D_arc` states it in the form Theorem D needs and proves it without Theorem 43: the component
`Q` of `I_g − J` containing `E₁E′₁ − E₁` stays connected when the arc `E₁E′₁` is removed
(`hair_isPreconnected`, Kline's proof of Theorem 33 for any connected open set: this is the role of
the curve `ABTNA`), it has the points of the interval `E₁A₁` of `J` as limit points
(`side_propagate`), and batch 138's `accessible` reaches `A₁` and `E′₁` from it.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **Theorem 33 for any connected open set** (Kline's proof, as in `fa_theorem33`, which uses only
that the region is open and connected): if `A ∉ R`, `B ∈ R` and the arc `AB` has `AB − A ⊆ R`, then
`R − AB` is connected. *Axioms used: 1–8.* -/
theorem hair_isPreconnected (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {R : Set S}
    (hRo : @IsOpen S σ.topology R) (hRc : @IsPreconnected S σ.topology R) {A B : S} (hAR : A ∉ R)
    (hB : B ∈ R) {K : Set S} (hK : @TArc S σ.topology A B K) (hKR : K \ {A} ⊆ R) :
    @IsPreconnected S σ.topology (R \ K) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  obtain ⟨hAB, g, hg, rfl, rfl, rfl⟩ := hK
  have hKarc : TArc (g 0) (g 1) (range g) := ⟨hAB, g, hg, rfl, rfl, rfl⟩
  have hgO : ∀ u ∈ Ioo 0 1, g u ∈ R := fun u hu =>
    hKR ⟨mem_range_self u, fun e => hu.1.ne' (hg.injective e)⟩
  have step1 : ∀ P ∈ R \ range g, ∃ Γ, TArc P (g 1) Γ ∧ Γ ⊆ R ∧ Γ ∩ range g = {g 1} := by
    intro P hP
    obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P hP.1 (g 1) hB
      (fun e => hP.2 (e ▸ mem_range_self 1))
    exact reach_end h1 h2 h3 h4 h5 h6 h7 h8 hg hRo hgO hB hP hΓ₀ hΓ₀R (mem_range_self 1)
      (fun h => hAR (hΓ₀R h))
  refine isPreconnected_of_forall_pair fun P hP P' hP' => ?_
  obtain ⟨Γ, hΓ, hΓR, hΓK⟩ := step1 P hP
  have hPB : P ≠ g 1 := fun e => hP.2 (e ▸ mem_range_self 1)
  by_cases hP'Γ : P' ∈ Γ
  · refine ⟨Γ \ {g 1}, fun x hx => ⟨hΓR hx.1, fun h => hx.2 ?_⟩, ⟨hΓ.left_mem, hPB⟩,
      ⟨hP'Γ, fun e => hP'.2 (e ▸ mem_range_self 1)⟩, hΓ.isPreconnected_diff_right⟩
    have : x ∈ Γ ∩ range g := ⟨hx.1, h⟩
    rwa [hΓK] at this
  have hK'' : TArc P (g 0) (Γ ∪ range g) := hΓ.union hKarc.symm hΓK
  obtain ⟨-, φ, hφ, hφr, hφ0, hφ1⟩ := hK''.symm
  have hφO : ∀ u ∈ Ioo 0 1, φ u ∈ R := by
    intro u hu
    have hu' : φ u ∈ Γ ∪ range g := hφr ▸ mem_range_self u
    have hne : φ u ≠ g 0 := fun e => hu.1.ne' (hφ.injective (e.trans hφ0.symm))
    rcases hu' with h | h
    · exact hΓR h
    · exact hKR ⟨h, hne⟩
  have hP'φ : P' ∈ R \ range φ := ⟨hP'.1, by rw [hφr]; rintro (h | h); exacts [hP'Γ h, hP'.2 h]⟩
  have hPP' : P' ≠ P := fun e => hP'Γ (e ▸ hΓ.left_mem)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P' hP'.1 P hP.1 hPP'
  obtain ⟨τ, hτ, hτR, hτK⟩ := reach_end h1 h2 h3 h4 h5 h6 h7 h8 hφ hRo hφO (hφ1 ▸ hP.1) hP'φ
    hΓ₀ hΓ₀R (hφ1 ▸ mem_range_self 1) (by rw [hφ0]; exact fun h => hAR (hΓ₀R h))
  rw [hφ1] at hτ hτK
  refine ⟨τ, fun x hx => ⟨hτR hx, fun h => hP.2 ?_⟩, hτ.right_mem, hτ.left_mem, hτ.isPreconnected⟩
  have : x ∈ τ ∩ range φ := ⟨hx, hφr ▸ Or.inr h⟩
  rw [hτK] at this
  exact this ▸ h

/-- **The arc of footnote * of p. 174** (Theorem D: "Within `g₁` (and within `J` except for the point
`A₁`) there is an arc `A₁E′₁` that has in common with `E₁E′₁` only the point `E′₁`"), in the form
Theorem D needs. `J` (interior `I`) and `g` (interior `I_g`) are closed curves; `K` is an interval
`A₁B₁` of `J` whose segment lies within `g`; `E₁` is a point of that segment; `E₁E′₁` is an arc
within `g` lying, except for `E₁`, within `J`. Then there is an arc from `A₁` to `E′₁` lying, except
for `A₁`, within `g` and within `J`, and meeting `E₁E′₁` only in `E′₁`. *Axioms used: 1–8.*
**Proof replaced** (Theorem 43 is not used; see the module docstring). -/
theorem m19_D_arc (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    {J I g Ig : Set S} (hJ : σ.IsInteriorOf J I) (hg : σ.IsInteriorOf g Ig)
    {A₁ B₁ E₁ E₁' : S} {K β : Set S} (hK : σ.IsArc A₁ B₁ K) (hKJ : K ⊆ J)
    (hKg : openArc A₁ B₁ K ⊆ Ig) (hE₁ : E₁ ∈ openArc A₁ B₁ K) (hβ : σ.IsArc E₁ E₁' β)
    (hβg : β ⊆ Ig) (hβI : β \ {E₁} ⊆ I) :
    ∃ γ, σ.IsArc A₁ E₁' γ ∧ γ \ {A₁} ⊆ Ig ∩ I ∧ γ ∩ β = {E₁'} := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, -, -, hEo, -, -, -, -, hdisIJ, -, hcompl, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJ
  obtain ⟨hIgo, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hg
  -- the other interval `K₂` of `J` from `A₁` to `B₁`
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ.1 (hKJ hK.left_mem) (hKJ hK.right_mem) hK.1
  obtain ⟨K₂, hK₂, hKK₂, hKK₂u⟩ : ∃ K₂, σ.IsArc A₁ B₁ K₂ ∧ K ∩ K₂ = {A₁, B₁} ∧ K ∪ K₂ = J := by
    rcases huniq K hKJ hK with rfl | rfl
    · exact ⟨C₂, hC₂, hCi, hCu⟩
    · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
  have hK₂c : IsClosed K₂ := ((isArc_iff_tarc h1 h3 h4 h51).mp hK₂).isClosed
  have hβt := (isArc_iff_tarc h1 h3 h4 h51).mp hβ
  have hβc : IsClosed β := hβt.isClosed
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp hK).symm
  have hinj := hf.injective
  have hJI : ∀ x ∈ J, x ∉ I := fun x hx hxI => disjoint_left.mp hdisIJ hxI hx
  -- `E₁ = f e`
  obtain ⟨e, he, rfl⟩ : ∃ e ∈ Ioo (0 : unitInterval) 1, f e = E₁ := by
    obtain ⟨hE₁K, hE₁AB⟩ := hE₁
    rw [← hfr] at hE₁K
    obtain ⟨e, rfl⟩ := hE₁K
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hE₁AB
    refine ⟨e, ⟨lt_of_le_of_ne nonneg' fun h => ?_, lt_of_le_of_ne le_one' fun h => ?_⟩, rfl⟩
    · exact hE₁AB.2 (by rw [← h, hf0])
    · exact hE₁AB.1 (by rw [h, hf1])
  have hfK₂ : ∀ u ∈ Ioo (0 : unitInterval) 1, f u ∉ K₂ := by
    intro u hu h
    have : f u ∈ K ∩ K₂ := ⟨hfr ▸ mem_range_self u, h⟩
    rw [hKK₂, ← hf0, ← hf1] at this
    rcases this with h' | h'
    · exact hu.2.ne (hinj h')
    · exact hu.1.ne' (hinj h')
  have hfg : ∀ u ∈ Ioo (0 : unitInterval) 1, f u ∈ Ig := by
    intro u hu
    refine hKg ⟨hfr ▸ mem_range_self u, ?_⟩
    rintro (h | h)
    · exact hu.2.ne (hinj (h.trans hf1.symm))
    · exact hu.1.ne' (hinj ((mem_singleton_iff.mp h).trans hf0.symm))
  have hfβ : ∀ u, u ≠ e → f u ∉ β := by
    intro u hue h
    by_cases hE : f u = f e
    · exact hue (hinj hE)
    · exact hJI _ (hKJ (hfr ▸ mem_range_self u)) (hβI ⟨h, hE⟩)
  -- the component `Q` of `I_g − J` containing `E₁E′₁ − E₁`
  set O := Ig \ K₂ with hOdef
  have hOo : IsOpen O := hIgo.sdiff hK₂c
  have hOK : O \ range f = Ig \ J := by
    rw [hfr, ← hKK₂u]
    ext x; simp only [hOdef, mem_diff, mem_union, not_or]; tauto
  have hβ' : β \ {f e} ⊆ O \ range f := by
    rw [hOK]; exact fun x hx => ⟨hβg hx.1, fun h => hJI x h (hβI hx)⟩
  set Q := connectedComponentIn (O \ range f) E₁' with hQdef
  have hQo : IsOpen Q := (hOo.sdiff (isCompact_range hf.continuous).isClosed).connectedComponentIn
  have hQc : IsPreconnected Q := isPreconnected_connectedComponentIn
  have hβQ : β \ {f e} ⊆ Q :=
    hβt.symm.isPreconnected_diff_right.subset_connectedComponentIn
      ⟨hβt.right_mem, hβt.ne.symm⟩ hβ'
  have hQsub : Q ⊆ Ig \ J := hOK ▸ connectedComponentIn_subset _ _
  have hQI : Q ⊆ I := by
    have hQL : Q ⊆ I ∪ (closure I)ᶜ := fun x hx => hcompl ▸ (hQsub hx).2
    rcases hQc.subset_or_subset hIo hEo (disjoint_compl_right.mono_left subset_closure) hQL
      with h | h
    · exact h
    · exfalso
      have hE' : E₁' ∈ I := hβI ⟨hβt.right_mem, hβt.ne.symm⟩
      exact h (hβQ ⟨hβt.right_mem, hβt.ne.symm⟩) (subset_closure hE')
  -- the points of the open interval `B₁A₁` are limit points of `Q`
  have hE₁cl : f e ∈ closure Q :=
    closure_mono hβQ hβt.symm.mem_closure_diff_right
  have hprop := side_propagate h1 h2 h3 h4 h5 h6 h7 h8 hf hOo (x₀ := E₁') isPreconnected_Ioo
    subset_rfl (fun u hu => ⟨hfg u hu, hfK₂ u hu⟩) he hE₁cl
  -- `Q − E₁E′₁` is connected
  have hE₁Q : f e ∉ Q := fun h => hJI _ (hKJ (hfr ▸ mem_range_self e)) (hQI h)
  have hQβc := hair_isPreconnected h1 h2 h3 h4 h5 h6 h7 h8 hQo hQc hE₁Q
    (hβQ ⟨hβt.right_mem, hβt.ne.symm⟩) hβt hβQ
  -- a point `x₀` of `Q − E₁E′₁` near the middle of `E₁E′₁`
  have hE'β : E₁' ∈ β \ {f e} := ⟨hβt.right_mem, hβt.ne.symm⟩
  obtain ⟨-, b, hb, hbr, hb0, hb1⟩ := hβt
  set m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩ with hm
  have hm0 : (0 : unitInterval) < m := by rw [hm]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have hm1 : m < 1 := by rw [hm]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have hbQ : ∀ u ∈ Ioo (0 : unitInterval) 1, b u ∈ Q := by
    intro u hu
    refine hβQ ⟨hbr ▸ mem_range_self u, fun h => hu.1.ne' (hb.injective ?_)⟩
    rw [mem_singleton_iff.mp h, hb0]
  obtain ⟨e', s', he', hs', N, I₁, I₂, -, hNQ, -, -, hI₁N, -, -, -, hI₁c, -, hI₁β, hI₂β, hcl⟩ :=
    sides h1 h2 h3 h4 h5 h6 h7 h8 hb hm0 hm1 hQo (hbQ m ⟨hm0, hm1⟩)
  have hbm : b m ∈ closure I₁ := (hcl m ⟨he'.le, hs'.le⟩).1
  obtain ⟨x₀, hx₀⟩ : I₁.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hbm
    exact hbm
  have hI₁Qβ : I₁ ⊆ Q \ range b := fun x hx =>
    ⟨hNQ (hI₁N hx), fun h => disjoint_left.mp hI₁β hx h⟩
  have hx₀Q : x₀ ∈ Q \ β := hbr ▸ hI₁Qβ hx₀
  -- `E′₁` from `x₀`
  obtain ⟨τ₂, hτ₂, hτ₂Q⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hb hQo (t₀ := 0)
    (zero_lt_one' unitInterval) hbQ (hI₁Qβ hx₀)
    ⟨m, ⟨hm0, hm1⟩, closure_mono (hI₁c.subset_connectedComponentIn hx₀ hI₁Qβ) hbm⟩
  rw [hb1] at hτ₂ hτ₂Q
  -- `A₁` from `x₀`
  set O₁ := Ig \ (K₂ ∪ β) with hO₁def
  have hO₁o : IsOpen O₁ := hIgo.sdiff (hK₂c.union hβc)
  have hQβO₁ : Q \ β ⊆ O₁ \ range f := by
    intro x hx
    have := hQsub hx.1
    refine ⟨⟨this.1, ?_⟩, fun h => this.2 (hKJ (hfr ▸ h))⟩
    rintro (h | h)
    · exact this.2 (hKK₂u ▸ Or.inr h)
    · exact hx.2 h
  obtain ⟨u, heu, hu1⟩ := exists_between he.2
  have hfu : f u ∈ closure (Q \ β) := by
    have hfuQ := hprop u ⟨he.1.trans heu, hu1⟩
    rw [mem_closure_iff_nhds] at hfuQ ⊢
    intro t ht
    obtain ⟨y, hyt, hyQ⟩ := hfuQ (t ∩ βᶜ)
      (Filter.inter_mem ht (hβc.isOpen_compl.mem_nhds (hfβ u heu.ne')))
    exact ⟨y, hyt.1, hyQ, hyt.2⟩
  obtain ⟨τ₁, hτ₁, hτ₁Q⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hf hO₁o (t₀ := e) he.2
    (fun v hv => ⟨hfg v ⟨he.1.trans hv.1, hv.2⟩, by
      rintro (h | h)
      · exact hfK₂ v ⟨he.1.trans hv.1, hv.2⟩ h
      · exact hfβ v hv.1.ne' h⟩)
    (hQβO₁ hx₀Q) ⟨u, ⟨heu, hu1⟩, closure_mono
      (hQβc.subset_connectedComponentIn hx₀Q hQβO₁) hfu⟩
  rw [hf1] at hτ₁ hτ₁Q
  set C₁' := connectedComponentIn (O₁ \ range f) x₀ with hC₁'
  have hC₁sub : C₁' ⊆ (Ig \ J) \ β := by
    intro x hx
    have h := connectedComponentIn_subset _ _ hx
    refine ⟨⟨h.1.1, ?_⟩, fun hb' => h.1.2 (Or.inr hb')⟩
    rw [← hKK₂u]
    rintro (h' | h')
    · exact h.2 (hfr ▸ h')
    · exact h.1.2 (Or.inl h')
  have hC₁I : C₁' ⊆ I := by
    have hC : IsPreconnected C₁' := isPreconnected_connectedComponentIn
    have hQL : C₁' ⊆ I ∪ (closure I)ᶜ := fun x hx => hcompl ▸ (hC₁sub hx).1.2
    rcases hC.subset_or_subset hIo hEo (disjoint_compl_right.mono_left subset_closure) hQL
      with h | h
    · exact h
    · exact absurd (subset_closure (hQI hx₀Q.1))
        (h (mem_connectedComponentIn (hQβO₁ hx₀Q)))
  set C₂' := connectedComponentIn (Q \ range b) x₀ with hC₂'
  have hC₂sub : C₂' ⊆ Q \ β := hbr ▸ connectedComponentIn_subset _ _
  -- join
  have hA₁E : A₁ ≠ E₁' := fun h => hJI _ (hKJ hK.left_mem) (by rw [h]; exact hβI hE'β)
  obtain ⟨γ, hγsub, hγ⟩ := hτ₁.symm.join hτ₂.symm ⟨x₀, hτ₁.left_mem, hτ₂.left_mem⟩ hA₁E
  have hE'I : E₁' ∈ Ig ∩ I := ⟨hβg hE'β.1, hβI hE'β⟩
  refine ⟨γ, (isArc_iff_tarc h1 h3 h4 h51).mpr hγ, ?_, ?_⟩
  · rintro x ⟨hx, hxA⟩
    rcases hγsub hx with h | h
    · rcases hτ₁Q h with rfl | h
      · exact absurd rfl hxA
      · exact ⟨(hC₁sub h).1.1, hC₁I h⟩
    · rcases hτ₂Q h with rfl | h
      · exact hE'I
      · exact ⟨(hQsub (hC₂sub h).1).1, hQI (hC₂sub h).1⟩
  · ext x
    constructor
    · rintro ⟨hx, hxβ⟩
      rcases hγsub hx with h | h
      · rcases hτ₁Q h with hx1 | h
        · exfalso
          rw [hx1] at hxβ
          by_cases hA : A₁ = f e
          · exact he.2.ne (hinj (hA.symm.trans hf1.symm))
          · exact hJI _ (hKJ hK.left_mem) (hβI ⟨hxβ, hA⟩)
        · exact absurd hxβ (hC₁sub h).2
      · rcases hτ₂Q h with rfl | h
        · rfl
        · exact absurd hxβ (hC₂sub h).2
    · rintro rfl
      exact ⟨hγ.right_mem, hE'β.1⟩

end HPC.Moore
