import HPC.Moore.M43Comp

/-!
# Moore, F.A. (1916), Theorem 43, corrected (batch 140, item B)

**Theorem 43** (p. 156, with `G` nonempty: the printed form is refuted for `G = ∅`,
`not_fa_theorem43_printed`). If `J` is a closed curve with interior `I`, `O` a point of `J`, and `G`
a finite nonempty set of closed curves whose interiors contain `O` and none of which contains `I`,
there are closed curves `J₁`, `J₂` through `O`, lying on `J` and the curves of `G`, with the interior
of `J₁` without `J`, that of `J₂` within `J`, and both inside every curve of `G`.

Moore gives no proof. Here: `dual_step` (the intersection analogue of Theorem 41, from
`dual_component` and a degenerate case), iterated over `G` (`iterate_inner`), starting from `J`
for `J₂`, and from the exterior side of `J` for `J₁`.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A closed curve minus a set with at most one point is connected. *Axioms used: 1, 3, 4, 5₁.* -/
theorem isPreconnected_scc_diff (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J T : Set S} (hJ : σ.IsSCC J) (hT : T.Subsingleton) :
    @IsPreconnected S σ.topology (J \ T) := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨A, B, C₁, C₂, hC₁, hC₂, hC12, hJeq⟩ := (isSCC_iff_tscc h1 h3 h4 h51).mp hJ
  by_cases hTJ : (J ∩ T).Nonempty
  · obtain ⟨c, hcJ, hcT⟩ := hTJ
    have hdiff : J \ T = J \ {c} := by
      ext x
      simp only [mem_diff, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hxT⟩; exact ⟨hx, fun e => hxT (e ▸ hcT)⟩
      · rintro ⟨hx, hxc⟩; exact ⟨hx, fun hxT => hxc (hT hxT hcT)⟩
    rw [hdiff]
    obtain ⟨d, hdJ, hdc⟩ : ∃ d ∈ J, d ≠ c := by
      by_cases hAc : A = c
      · exact ⟨B, hJeq ▸ Or.inl hC₁.right_mem, fun e => hC₁.ne (hAc.trans e.symm)⟩
      · exact ⟨A, hJeq ▸ Or.inl hC₁.left_mem, hAc⟩
    obtain ⟨D₁, D₂, hD₁, hD₂, -, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ hcJ hdJ hdc.symm
    rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
    have e : J \ {c} = (D₁ \ {c}) ∪ (D₂ \ {c}) := by rw [← hDu, union_diff_distrib]
    rw [e]
    exact hD₁.symm.isPreconnected_diff_right.union d ⟨hD₁.right_mem, hdc⟩
      ⟨hD₂.right_mem, hdc⟩ hD₂.symm.isPreconnected_diff_right
  · rw [not_nonempty_iff_eq_empty] at hTJ
    have : J \ T = J := by
      ext x; simp only [mem_diff, and_iff_left_iff_imp]
      intro hx hxT; exact (hTJ ▸ (⟨hx, hxT⟩ : x ∈ J ∩ T) : x ∈ (∅ : Set S))
    rw [this, hJeq]
    exact hC₁.isPreconnected.union A hC₁.left_mem hC₂.left_mem hC₂.isPreconnected

section Th43

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The intersection analogue of Theorem 41.** If `O` is a point of the closed curve `J` within
the closed curve `J'`, and `U` is the interior of `J`, or its exterior provided `I ⊄ I'`, there is
a closed curve through `O` on `J + J'` whose interior lies in `U ∩ I'`. *Axioms used: 1–8.* -/
theorem dual_step {J I J' I' U : Set S} (hI : σ.IsInteriorOf J I) (hI' : σ.IsInteriorOf J' I')
    (hU : U = I ∨ (U = (@closure S σ.topology I)ᶜ ∧ ¬ I ⊆ I')) {O : S} (hO : O ∈ J)
    (hOI' : O ∈ I') :
    ∃ J'' I'', σ.IsInteriorOf J'' I'' ∧ O ∈ J'' ∧ J'' ⊆ J ∪ J' ∧ I'' ⊆ U ∩ I' := by
  by_cases hsing : (J ∩ J').Subsingleton
  swap
  · obtain ⟨y, hy, y', hy', hyy⟩ := Set.not_subsingleton_iff.mp hsing
    exact dual_component h1 h2 h3 h4 h5 h6 h7 h8 hI hI' hU hO hOI' hy hy' hyy
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, hIc, -, hfr, hEo, hEc, -, hfrE, hcl, hdisIJ, hdisEJ, hcompl, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨hI'o, -, -, hfr', hE'o, -, -, -, hcl', hdisI'J', -, hcompl', -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI'
  have hJcl : J ⊆ closure I := hfr ▸ frontier_subset_closure
  -- the side `U`: connected, open, with `O` as a limit point, and the other side `U'`
  obtain ⟨U', hUo, hUc, hU'o, hUU', hsplit, hOU⟩ : ∃ U', IsOpen U ∧ IsPreconnected U ∧
      IsOpen U' ∧ Disjoint U U' ∧ Jᶜ = U ∪ U' ∧ O ∈ closure U := by
    rcases hU with hU | ⟨hU, -⟩
    · rw [hU]
      exact ⟨(closure I)ᶜ, hIo, hIc, hEo, disjoint_compl_right.mono_left subset_closure, hcompl,
        hJcl hO⟩
    · rw [hU]
      exact ⟨I, hEo, hEc, hIo, (disjoint_compl_right.mono_left subset_closure).symm,
        by rw [hcompl, union_comm], frontier_subset_closure (hfrE.symm ▸ hO)⟩
  have hUJ : Disjoint U J := by
    rw [disjoint_left]
    intro x hxU hxJ
    have : x ∈ Jᶜ := by rw [hsplit]; exact Or.inl hxU
    exact this hxJ
  have hUI' : (U ∩ I').Nonempty := by
    obtain ⟨w, hwI', hwU⟩ := mem_closure_iff_nhds.mp hOU I' (hI'o.mem_nhds hOI')
    exact ⟨w, hwU, hwI'⟩
  by_cases hJ'U : (J' ∩ U).Nonempty
  · exfalso
    obtain ⟨z, hzJ', hzU⟩ := hJ'U
    have hpc := isPreconnected_scc_diff h1 h3 h4 h51 hI'.1 hsing
    have hsub : J' \ (J ∩ J') ⊆ U ∪ U' := fun x hx => by
      have : x ∈ Jᶜ := fun h => hx.2 ⟨h, hx.1⟩
      rwa [hsplit] at this
    have hJ'Usub : J' \ (J ∩ J') ⊆ U := by
      rcases hpc.subset_or_subset hUo hU'o hUU' hsub with h | h
      · exact h
      · exact absurd (h ⟨hzJ', fun h' => disjoint_left.mp hUJ hzU h'.1⟩)
          (disjoint_left.mp hUU' hzU)
    have hJ'cl : J' ⊆ U ∪ J := fun x hx => by
      by_cases hxJ : x ∈ J
      · exact Or.inr hxJ
      · exact Or.inl (hJ'Usub ⟨hx, fun h => hxJ h.1⟩)
    rcases hU with hU | ⟨hU, hnot⟩
    · rw [hU] at hJ'cl
      have hI'I : I' ⊆ I := th21Prop h1 h3 h4 h5 h7 I hI.2.1 I' hI'.2.1
        (by rw [hfr', hcl]; exact hJ'cl)
      exact disjoint_left.mp hdisIJ (hI'I hOI') hO
    · apply hnot
      have hJ'I : Disjoint I J' := by
        rw [disjoint_left]
        intro x hxI hxJ
        rcases hJ'cl hxJ with h | h
        · rw [hU] at h; exact h (subset_closure hxI)
        · exact disjoint_left.mp hdisIJ hxI h
      obtain ⟨w, hwI', hwI⟩ := mem_closure_iff_nhds.mp (hJcl hO) I' (hI'o.mem_nhds hOI')
      exact conn_sub_of_frontier hIc (by rw [hfr']; exact hJ'I) ⟨w, hwI, hwI'⟩
  · rw [not_nonempty_iff_eq_empty] at hJ'U
    have hUsplit : U ⊆ I' ∪ (closure I')ᶜ := fun x hx => by
      have : x ∈ J'ᶜ := fun h => (hJ'U ▸ (⟨h, hx⟩ : x ∈ J' ∩ U) : x ∈ (∅ : Set S))
      rwa [hcompl'] at this
    have hUsubI' : U ⊆ I' := by
      rcases hUc.subset_or_subset hI'o hE'o (disjoint_compl_right.mono_left subset_closure)
        hUsplit with h | h
      · exact h
      · obtain ⟨w, hwU, hwI'⟩ := hUI'
        exact absurd (subset_closure hwI') (h hwU)
    rcases hU with hU | ⟨hU, -⟩
    · exact ⟨J, I, hI, hO, subset_union_left, fun x hx => ⟨hU ▸ hx, hUsubI' (hU ▸ hx)⟩⟩
    · exfalso
      rw [hU] at hUsubI'
      have hEc' : IsCompact (closure (closure I)ᶜ) :=
        (isCompact_closure_region h1 h4 hI'.2.1).of_isClosed_subset isClosed_closure
          (closure_mono hUsubI')
      exact not_isCompact_univ h1 h5 (((isCompact_closure_region h1 h4 hI.2.1).union
        hEc').of_isClosed_subset isClosed_univ fun x _ => by
          by_cases hx : x ∈ closure I
          · exact Or.inl hx
          · exact Or.inr (subset_closure hx))

/-- `dual_step` within the interior, iterated over a finite set of closed curves whose interiors
contain `O`. *Axioms used: 1–8.* -/
theorem iterate_inner {J₀ I₀ : Set S} (hI₀ : σ.IsInteriorOf J₀ I₀) {O : S} (hO : O ∈ J₀)
    (H : Finset (Set S × Set S)) (hH : ∀ p ∈ H, σ.IsInteriorOf p.1 p.2)
    (hOH : ∀ p ∈ H, O ∈ p.2) :
    ∃ J' I', σ.IsInteriorOf J' I' ∧ O ∈ J' ∧ J' ⊆ J₀ ∪ ⋃ p ∈ H, p.1 ∧ I' ⊆ I₀ ∧
      ∀ p ∈ H, I' ⊆ p.2 := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨J₀, I₀, hI₀, hO, subset_union_left, subset_rfl, fun p hp => absurd hp
      (Finset.notMem_empty p)⟩
  | insert a H haH ih =>
    obtain ⟨J', I', hI', hOJ', hJ'sub, hI'sub, hI'H⟩ :=
      ih (fun p hp => hH p (Finset.mem_insert_of_mem hp))
        (fun p hp => hOH p (Finset.mem_insert_of_mem hp))
    obtain ⟨J'', I'', hI'', hOJ'', hJ''sub, hI''sub⟩ :=
      dual_step h1 h2 h3 h4 h5 h6 h7 h8 hI' (hH a (Finset.mem_insert_self a H)) (Or.inl rfl) hOJ'
        (hOH a (Finset.mem_insert_self a H))
    refine ⟨J'', I'', hI'', hOJ'', fun x hx => ?_, fun x hx => hI'sub (hI''sub hx).1,
      fun p hp => ?_⟩
    · rcases hJ''sub hx with h | h
      · rcases hJ'sub h with h' | h'
        · exact Or.inl h'
        · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp h'
          exact Or.inr (mem_iUnion₂.mpr ⟨p, Finset.mem_insert_of_mem hp, hxp⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a H, h⟩)
    · rcases Finset.mem_insert.mp hp with rfl | hp
      · exact fun x hx => (hI''sub hx).2
      · exact fun x hx => hI'H p hp (hI''sub hx).1

/-- **Theorem 43**, corrected (`G` nonempty). *Axioms used: 1–8.*
**Shape changes:** `G` nonempty (`hGne`; the printed form is refuted for `G = ∅`,
`not_fa_theorem43_printed`); the axioms are made explicit. -/
theorem fa_theorem43 {J I : Set S} (hJ : σ.IsInteriorOf J I) {O : S} (hO : O ∈ J)
    (G : Finset (Set S × Set S)) (hGne : G.Nonempty) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hOG : ∀ p ∈ G, O ∈ p.2) (hnot : ∀ p ∈ G, ¬ I ⊆ p.2) :
    ∃ J₁ I₁ J₂ I₂, σ.IsInteriorOf J₁ I₁ ∧ σ.IsInteriorOf J₂ I₂ ∧ O ∈ J₁ ∧ O ∈ J₂ ∧
      J₁ ∪ J₂ ⊆ J ∪ ⋃ p ∈ G, p.1 ∧ I₁ ⊆ σ.ext I ∧ I₂ ⊆ I ∧
      ∀ p ∈ G, I₁ ∪ I₂ ⊆ p.2 := by
  obtain ⟨p₀, hp₀⟩ := hGne
  obtain ⟨J₂, I₂, hI₂, hOJ₂, hJ₂sub, hI₂I, hI₂G⟩ :=
    iterate_inner h1 h2 h3 h4 h5 h6 h7 h8 hJ hO G hG hOG
  obtain ⟨K, IK, hIK, hOK, hKsub, hIKsub⟩ := dual_step h1 h2 h3 h4 h5 h6 h7 h8 hJ (hG p₀ hp₀)
    (Or.inr ⟨rfl, hnot p₀ hp₀⟩) hO (hOG p₀ hp₀)
  obtain ⟨J₁, I₁, hI₁, hOJ₁, hJ₁sub, hI₁K, hI₁G⟩ :=
    iterate_inner h1 h2 h3 h4 h5 h6 h7 h8 hIK hOK G hG hOG
  refine ⟨J₁, I₁, J₂, I₂, hI₁, hI₂, hOJ₁, hOJ₂, union_subset ?_ hJ₂sub, ?_, hI₂I,
    fun p hp => union_subset (hI₁G p hp) (hI₂G p hp)⟩
  · intro x hx
    rcases hJ₁sub hx with h | h
    · rcases hKsub h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (mem_iUnion₂.mpr ⟨p₀, hp₀, h'⟩)
    · exact Or.inr h
  · rw [ext_eq_compl_closure h1]
    exact fun x hx => (hIKsub (hI₁K hx)).1

end Th43

end HPC.Moore
