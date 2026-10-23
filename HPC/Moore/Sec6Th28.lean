import HPC.Moore.Sec6B

/-!
# Moore, F.A. (1916), §6: Theorem 28 (batch 138, item B)

**Theorem 28.** If `O` is on the closed curve `J`, `R̄` is a region about `O`, and `M` is the
interior or the exterior of `J`, there is an arc `AXB` with `A`, `B` on `J`, the open arc `AXB`
in `M ∩ R̄`, and, of the two arcs into which `A`, `B` divide `J`, the one containing `O` in `R̄`.

Moore's proof (p. 145): Axioms 6 and 7 give regions `L ⊆ M ∩ R̄` and `L̄ ⊆ R̄` about `O` with every
point of `J` in `L̄` a boundary point of `L`; an arc `A₁OB₁` of `J` in `L̄`; points `A₂`, `B₂` in
the order `A₁A₂OB₂B₁`; regions `R_A`, `R_B` about them meeting `J` only in `A₁O`, `OB₁`; points
`C`, `D` of `L` in `R_A`, `R_B`; arcs `PC`, `PD` in `L` and `CA₂`, `DB₂` in `R_A`, `R_B`; and \"the
point-set `A₂C + CP + PD + DB₂` contains as a subset an arc `AXB` satisfying conditions (1), (2),
and (3)\". That last step needs care: the arc `CA₂` runs in `R_A`, which straddles `J`, so its part
before `J` need not lie in `M`. Here `A` is taken as the **first point of `CA₂` outside `M`**; it
is a boundary point of `M`, hence on `J`, hence on the open arc `A₁O`. The point `P` is not
needed.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **Theorem 28.** *Axioms used: 1, 2, 3, 4, 5₁, and 6 (for `M` the interior) or 7 (for `M` the
exterior).* **Shape change:** the axioms are made explicit (both 6 and 7 are assumed, since `M`
may be either), with Axiom 5₁ for Axiom 5; the conclusion `O ∈ C₁` is strengthened to `O` in the
open arc `C₁ − A − B` (Moore's proof gives this, and Theorem 31 uses it). -/
theorem fa_theorem28 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h6 : σ.Axiom6) (h7 : σ.Axiom7) {J R : Set S}
    (hR : σ.IsInteriorOf J R) {O : S} (hO : O ∈ J) {R' : Set S} (hR' : R' ∈ σ.region)
    (hOR' : O ∈ R') {M : Set S} (hM : M = R ∨ M = σ.ext R) :
    ∃ A B : S, ∃ X C₁ C₂ : Set S, σ.IsArc A B X ∧ openArc A B X ⊆ M ∩ R' ∧
      σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧ O ∈ openArc A B C₁ ∧ C₁ ⊆ R' := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have harc := arcConn h1 h3 h4 h51 h2
  have hJ := hR.1
  have hRreg := hR.2.1
  have hRJ : frontier R = J := by rw [← bdry_eq_frontier h1]; exact hR.2.2
  have hRo : IsOpen R := isOpen_region hRreg
  -- Axioms 6, 7: the regions `L ⊆ M ∩ R̄` and `L̄ ∋ O`
  obtain ⟨L, hL, Lb, hLb, hLR', hLbR', hOLb, hLM, hJLb⟩ : ∃ L ∈ σ.region, ∃ Lb ∈ σ.region,
      L ⊆ R' ∧ Lb ⊆ R' ∧ O ∈ Lb ∧ L ⊆ M ∧ J ∩ Lb ⊆ closure L := by
    have hObd : O ∈ σ.bdry R := hR.2.2 ▸ hO
    rcases hM with hM | hM <;> rw [hM]
    · obtain ⟨K, hK, Kb, hKb, hKR', hKbR', hOKb, hKR, hbd⟩ := h6 R hRreg R' hR' O hOR' hObd
      refine ⟨K, hK, Kb, hKb, hKR', hKbR', hOKb, hKR, fun x hx => ?_⟩
      have := hbd ⟨hR.2.2 ▸ hx.1, hx.2⟩
      rw [bdry_eq_frontier h1] at this
      exact frontier_subset_closure this
    · obtain ⟨K, hK, Kb, hKb, hKR', hKbR', hOKb, hKR, hbd⟩ := h7 R hRreg R' hR' O hOR' hObd
      refine ⟨K, hK, Kb, hKb, hKR', hKbR', hOKb, hKR, fun x hx => ?_⟩
      have := hbd ⟨hR.2.2 ▸ hx.1, hx.2⟩
      rw [bdry_eq_frontier h1] at this
      exact frontier_subset_closure this
  have hLo : IsOpen L := isOpen_region hL
  have hLbo : IsOpen Lb := isOpen_region hLb
  -- `M` is open, misses `J`, and its boundary lies on `J`
  have hMo : IsOpen M ∧ Disjoint M J ∧ frontier M ⊆ J := by
    rcases hM with rfl | rfl
    · exact ⟨hRo, hRJ ▸ disjoint_frontier hRo, hRJ.le⟩
    · rw [ext_eq_compl_closure h1]
      refine ⟨isClosed_closure.isOpen_compl, disjoint_left.mpr fun x hx hxJ =>
        hx (frontier_subset_closure (hRJ ▸ hxJ)), ?_⟩
      rw [frontier_compl]; exact frontier_closure_subset.trans hRJ.le
  obtain ⟨hMo, hMJ, hMfr⟩ := hMo
  -- two points `P ≠ Q` of `J` other than `O`, and the arcs `PQ` of `J`
  obtain ⟨P, Q, hPJ, hQJ, hPQ, hPO, hQO⟩ : ∃ P Q : S, P ∈ J ∧ Q ∈ J ∧ P ≠ Q ∧ P ≠ O ∧ Q ≠ O := by
    obtain ⟨A₀, B₀, E₁, E₂, hE₁, hE₂, -, rfl⟩ := hJ
    rw [isArc_iff_tarc h1 h3 h4 h51] at hE₁
    obtain ⟨Z, hZ⟩ := hE₁.nonempty_diff
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at hZ
    by_cases hOA : O = A₀
    · subst hOA
      exact ⟨B₀, Z, Or.inl hE₁.right_mem, Or.inl hZ.1, fun h => hZ.2.2 h.symm,
        hE₁.ne.symm, hZ.2.1⟩
    by_cases hOB : O = B₀
    · subst hOB
      exact ⟨A₀, Z, Or.inl hE₁.left_mem, Or.inl hZ.1, fun h => hZ.2.1 h.symm, hE₁.ne, hZ.2.2⟩
    exact ⟨A₀, B₀, Or.inl hE₁.left_mem, Or.inl hE₁.right_mem, hE₁.ne, Ne.symm hOA, Ne.symm hOB⟩
  obtain ⟨D₁, D₂, hD₁, hD₂, hD12, hDJ⟩ :
      ∃ D₁ D₂, σ.IsArc P Q D₁ ∧ σ.IsArc P Q D₂ ∧ D₁ ∩ D₂ = {P, Q} ∧ D₁ ∪ D₂ = J ∧ O ∈ D₁ := by
    obtain ⟨D₁, D₂, hD₁, hD₂, hD12, hDJ⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ hPJ hQJ hPQ
    rcases (hDJ ▸ hO : O ∈ D₁ ∪ D₂) with h | h
    · exact ⟨D₁, D₂, hD₁, hD₂, hD12, hDJ, h⟩
    · exact ⟨D₂, D₁, hD₂, hD₁, by rw [inter_comm]; exact hD12, by rw [union_comm]; exact hDJ, h⟩
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  obtain ⟨g, hg, hgr, hg0, hg1⟩ := hD₁.2
  have hinj := hg.injective
  obtain ⟨o, rfl⟩ : ∃ o, g o = O := by rw [← hgr] at hDJ; exact hDJ.2
  have ho0 : 0 < o := lt_of_le_of_ne nonneg' fun e => hPO (by rw [← hg0, e])
  have ho1 : o < 1 := lt_of_le_of_ne le_one' fun e => hQO (by rw [← hg1, e])
  have hJD : J = range g ∪ D₂ := by rw [hgr]; exact hDJ.1.symm
  -- an arc `A₁OB₁` of `J` in `L̄`
  obtain ⟨l, u, ⟨hlo, hou⟩, hlu⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨0, ho0⟩ ⟨1, ho1⟩).mp
    ((hLbo.preimage hg.continuous).mem_nhds hOLb)
  obtain ⟨a₁, hla₁, ha₁o⟩ := exists_between hlo
  obtain ⟨b₁, hob₁, hb₁u⟩ := exists_between hou
  have hab₁ : g '' Icc a₁ b₁ ⊆ Lb := by
    rintro _ ⟨v, hv, rfl⟩
    exact hlu ⟨hla₁.trans_le hv.1, hv.2.trans_lt hb₁u⟩
  obtain ⟨a₂, ha₁a₂, ha₂o⟩ := exists_between ha₁o
  obtain ⟨b₂, hob₂, hb₂b₁⟩ := exists_between hob₁
  -- the regions `R_A`, `R_B` (connected open sets)
  obtain ⟨UA, UB, hUA, hUB, hA₂UA, hB₂UB, hUAB⟩ :=
    t2_separation (fun e => (ha₂o.trans hob₂).ne (hinj e))
  have hcl : ∀ s t : unitInterval, IsClosed (g '' Icc s t) := fun s t =>
    (isCompact_Icc.image hg.continuous).isClosed
  have hD₂c : IsClosed D₂ := hD₂.isClosed
  obtain ⟨WA, hWAsub, hWAo, hA₂WA, hWAc⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
    ‹_› (g a₂) (Lb ∩ (D₂ ∪ g '' Icc 0 a₁ ∪ g '' Icc o 1)ᶜ ∩ UA)
    (((hLbo.inter ((hD₂c.union (hcl 0 a₁)).union (hcl o 1)).isOpen_compl).inter hUA).mem_nhds
      ⟨⟨hab₁ (mem_image_of_mem g ⟨ha₁a₂.le, (ha₂o.trans hob₁).le⟩), by
        rintro ((h | ⟨v, hv, e⟩) | ⟨v, hv, e⟩)
        · have : g a₂ ∈ range g ∩ D₂ := ⟨mem_range_self _, h⟩
          rw [hgr, hD12] at this
          rcases this with e | e
          · exact (ha₁a₂.trans_le' nonneg').ne' (hinj (e.trans hg0.symm))
          · exact (ha₂o.trans ho1).ne (hinj (e.trans hg1.symm))
        · exact absurd (hinj e ▸ hv.2) (not_le.mpr ha₁a₂)
        · exact absurd (hinj e ▸ hv.1) (not_le.mpr ha₂o)⟩, hA₂UA⟩)
  obtain ⟨WB, hWBsub, hWBo, hB₂WB, hWBc⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
    ‹_› (g b₂) (Lb ∩ (D₂ ∪ g '' Icc 0 o ∪ g '' Icc b₁ 1)ᶜ ∩ UB)
    (((hLbo.inter ((hD₂c.union (hcl 0 o)).union (hcl b₁ 1)).isOpen_compl).inter hUB).mem_nhds
      ⟨⟨hab₁ (mem_image_of_mem g ⟨(ha₁o.trans hob₂).le, hb₂b₁.le⟩), by
        rintro ((h | ⟨v, hv, e⟩) | ⟨v, hv, e⟩)
        · have : g b₂ ∈ range g ∩ D₂ := ⟨mem_range_self _, h⟩
          rw [hgr, hD12] at this
          rcases this with e | e
          · exact (ho0.trans hob₂).ne' (hinj (e.trans hg0.symm))
          · exact (hb₂b₁.trans_le le_one').ne (hinj (e.trans hg1.symm))
        · exact absurd (hinj e ▸ hv.2) (not_le.mpr hob₂)
        · exact absurd (hinj e ▸ hv.1) (not_le.mpr hb₂b₁)⟩, hB₂UB⟩)
  -- points of `J` in `R_A`, `R_B` lie on `A₁O`, `OB₁`
  have hWAJ : ∀ x ∈ WA, x ∈ J → ∃ v, a₁ < v ∧ v < o ∧ g v = x := by
    intro x hx hxJ
    have hx' := hWAsub hx
    simp only [mem_inter_iff, mem_compl_iff, mem_union, not_or] at hx'
    obtain ⟨⟨-, ⟨hxD₂, hx1⟩, hx2⟩, -⟩ := hx'
    rw [hJD] at hxJ
    rcases hxJ with ⟨v, rfl⟩ | h
    · exact ⟨v, not_le.mp fun h => hx1 (mem_image_of_mem g ⟨nonneg', h⟩),
        not_le.mp fun h => hx2 (mem_image_of_mem g ⟨h, le_one'⟩), rfl⟩
    · exact absurd h hxD₂
  have hWBJ : ∀ x ∈ WB, x ∈ J → ∃ v, o < v ∧ v < b₁ ∧ g v = x := by
    intro x hx hxJ
    have hx' := hWBsub hx
    simp only [mem_inter_iff, mem_compl_iff, mem_union, not_or] at hx'
    obtain ⟨⟨-, ⟨hxD₂, hx1⟩, hx2⟩, -⟩ := hx'
    rw [hJD] at hxJ
    rcases hxJ with ⟨v, rfl⟩ | h
    · exact ⟨v, not_le.mp fun h => hx1 (mem_image_of_mem g ⟨nonneg', h⟩),
        not_le.mp fun h => hx2 (mem_image_of_mem g ⟨h, le_one'⟩), rfl⟩
    · exact absurd h hxD₂
  have hWALb : WA ⊆ Lb := fun x hx => (hWAsub hx).1.1
  have hWBLb : WB ⊆ Lb := fun x hx => (hWBsub hx).1.1
  have hWAB : Disjoint WA WB := hUAB.mono (fun x hx => (hWAsub hx).2) (fun x hx => (hWBsub hx).2)
  -- points `C`, `D` of `L` in `R_A`, `R_B`
  have hA₂J : g a₂ ∈ J := hJD ▸ Or.inl (mem_range_self _)
  have hB₂J : g b₂ ∈ J := hJD ▸ Or.inl (mem_range_self _)
  obtain ⟨C, hCWA, hCL⟩ := mem_closure_iff_nhds.mp
    (hJLb ⟨hA₂J, hWALb hA₂WA⟩) WA (hWAo.mem_nhds hA₂WA)
  obtain ⟨D, hDWB, hDL⟩ := mem_closure_iff_nhds.mp
    (hJLb ⟨hB₂J, hWBLb hB₂WB⟩) WB (hWBo.mem_nhds hB₂WB)
  have hCD : C ≠ D := fun e => disjoint_left.mp hWAB hCWA (e ▸ hDWB)
  have hCM : C ∈ M := hLM hCL
  have hDM : D ∈ M := hLM hDL
  -- the arc `CD` in `L`; the arcs from `C`, `D` to their first points `A`, `B` outside `M`
  obtain ⟨γ, hγL, hγ⟩ := harc L hLo ((isConn_iff h1).mp (h2 L hL)) C hCL D hDL hCD
  have hfirst : ∀ (W : Set S), IsOpen W → IsConnected W → ∀ Z ∈ W, Z ∈ M → ∀ Y ∈ W, Y ∈ J →
      ∃ E ∈ W, E ∈ J ∧ ∃ σE, TArc Z E σE ∧ σE ⊆ W ∧ σE \ {E} ⊆ M := by
    intro W hWo hWc Z hZW hZM Y hYW hYJ
    have hZY : Z ≠ Y := fun e => disjoint_left.mp hMJ hZM (e ▸ hYJ)
    obtain ⟨ζ, hζW, hζ⟩ := harc W hWo hWc.isPreconnected Z hZW Y hYW hZY
    obtain ⟨E, hEM, σE, hσEζ, hσE, hσEM⟩ := hζ.first_point hMo.isClosed_compl
      ⟨Y, hζ.right_mem, fun h => disjoint_left.mp hMJ h hYJ⟩ (fun h => h hZM)
    have hsub : σE \ {E} ⊆ M := by
      intro x ⟨hx, hxE⟩
      by_contra hxM
      exact hxE (by rw [← hσEM]; exact ⟨hx, hxM⟩)
    have hEJ : E ∈ J :=
      hMfr (mem_frontier_of_mem_closure hMo (closure_mono hsub hσE.mem_closure_diff_right) hEM)
    exact ⟨E, hζW (hσEζ hσE.right_mem), hEJ, σE, hσE, hσEζ.trans hζW, hsub⟩
  obtain ⟨A, hAWA, hAJ, σA, hσA, hσAW, hσAM⟩ :=
    hfirst WA hWAo hWAc C hCWA hCM (g a₂) hA₂WA hA₂J
  obtain ⟨B, hBWB, hBJ, σB, hσB, hσBW, hσBM⟩ :=
    hfirst WB hWBo hWBc D hDWB hDM (g b₂) hB₂WB hB₂J
  obtain ⟨a, ha₁a, hao, rfl⟩ := hWAJ A hAWA hAJ
  obtain ⟨b, hob, hbb₁, rfl⟩ := hWBJ B hBWB hBJ
  have hAM : g a ∉ M := fun h => disjoint_left.mp hMJ h hAJ
  have hBM : g b ∉ M := fun h => disjoint_left.mp hMJ h hBJ
  have hab : a < b := hao.trans hob
  -- the arc `AXB`
  obtain ⟨δ, hδ, hδa⟩ := hσA.symm.join hγ.symm ⟨C, hσA.left_mem, hγ.left_mem⟩
    (fun e => hAM (e ▸ hDM))
  obtain ⟨Xa, hXa, hXaa⟩ := hδa.join hσB.symm ⟨D, hδa.right_mem, hσB.left_mem⟩
    (fun e => hab.ne (hinj e))
  -- the arc of `J` from `A` to `B` through `O`, and the other one
  have hC₁ : TArc (g a) (g b) (g '' Icc a b) := TArc.image_Icc hg hab
  have hC₁J : g '' Icc a b ⊆ J := fun x hx => hJD ▸ Or.inl (image_subset_range _ _ hx)
  have hAJ' : g a ∈ J := hC₁J (mem_image_of_mem g ⟨le_rfl, hab.le⟩)
  have hBJ' : g b ∈ J := hC₁J (mem_image_of_mem g ⟨hab.le, le_rfl⟩)
  obtain ⟨E₁, E₂, hE₁, hE₂, hE12, hEJ, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ hAJ' hBJ' (fun e => hab.ne (hinj e))
  have hC₁σ : σ.IsArc (g a) (g b) (g '' Icc a b) := (isArc_iff_tarc h1 h3 h4 h51).mpr hC₁
  obtain ⟨C₂, hC₂, hC12, hCJ⟩ : ∃ C₂, σ.IsArc (g a) (g b) C₂ ∧ g '' Icc a b ∩ C₂ = {g a, g b} ∧
      g '' Icc a b ∪ C₂ = J := by
    rcases huniq _ hC₁J hC₁σ with e | e
    · exact ⟨E₂, hE₂, e ▸ hE12, e ▸ hEJ⟩
    · exact ⟨E₁, hE₁, by rw [e, inter_comm]; exact hE12, by rw [e, union_comm]; exact hEJ⟩
  refine ⟨g a, g b, Xa, g '' Icc a b, C₂, (isArc_iff_tarc h1 h3 h4 h51).mpr hXaa, ?_, hC₁σ, hC₂,
    hC12, hCJ, ⟨mem_image_of_mem g ⟨hao.le, hob.le⟩, by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => hao.ne' (hinj e), fun e => hob.ne (hinj e)⟩⟩, ?_⟩
  · rintro x ⟨hx, hxAB⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxAB
    rcases hXa hx with hx | hx
    · rcases hδ hx with hx | hx
      · exact ⟨hσAM ⟨hx, hxAB.1⟩, hLbR' (hWALb (hσAW hx))⟩
      · exact ⟨hLM (hγL hx), hLR' (hγL hx)⟩
    · exact ⟨hσBM ⟨hx, hxAB.2⟩, hLbR' (hWBLb (hσBW hx))⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hLbR' (hab₁ (mem_image_of_mem g ⟨ha₁a.le.trans hv.1, hv.2.trans hbb₁.le⟩))

end HPC.Moore
