import HPC.Moore.M19DNice

/-!
# Moore 1919, Theorem D

**Theorem D** (`m19_theoremD`, p. 173). If each point on or within `ABCDA` is within some curve of a
set `G` of closed curves, the interior of `ABCDA` can be divided by a double ruling into
subdivisions each within some curve of `G`.

The proof replaces Moore's (see the batch-142 report). By compactness `G` may be taken finite
(`rulable_of_cover`, induction on the number of curves). For the step, `F`, the part of `J + I`
not within the other curves, is compact and lies within the first curve `g₁`; about `F` there is a
closed curve `h` with interior `W ⊇ F`, `h + W` within `g₁`, meeting `J` in finitely many points,
none of them `A, B, C, D`, and crossing `J` at each of them (`exists_nice_curve`). By the
corrected Theorem C (`curve_rulable`) there is a ruling whose subdivisions miss `h`; each
subdivision is then within `W ⊆ g₁` or without `W`, and a subdivision without `W` is, with its
boundary, covered by the other curves, so the induction hypothesis applies to it. The rulings of the
subdivisions are combined by the refinement lemma (`Space.ArcRuling.refine`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem C, corrected** (ruling form): a closed curve meeting `ABCDA` in finitely many points,
none of them `A, B, C, D`, and touching `ABCDA` from within at none of them (no common point is a
common end of two arcs of the curve lying, except for that point, within `ABCDA`). There is a ruling
none of whose subdivisions meets the curve. -/
theorem curve_rulable (q : σ.Quad J I A B C D sAB sBC sCD sDA) {h W : Set S}
    (hW : σ.IsInteriorOf h W) (hfin : (h ∩ J).Finite) (hcor : Disjoint h {A, B, C, D})
    (hnt : ∀ p ∈ h ∩ J, ∀ (m₁ m₂ : S) (M₁ M₂ : Set S), @TArc S σ.topology p m₁ M₁ →
      @TArc S σ.topology p m₂ M₂ → M₁ ∩ M₂ = {p} → M₁ ∪ M₂ ⊆ h → M₁ \ {p} ⊆ I →
        M₂ \ {p} ⊆ I → False) :
    σ.Rulable (fun U => Disjoint U h) I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, hclI, hIJ, -, hJc, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  rcases (h ∩ J).eq_empty_or_nonempty with he | hne
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hht⟩ := jordan h1 h2 h3 h4 h51 h7 hW
    have hhc : IsPreconnected h := by
      obtain ⟨a, b, C₁, C₂, hC₁, hC₂, hab, rfl⟩ := hht
      exact hC₁.isPreconnected.union a hC₁.left_mem hC₂.left_mem hC₂.isPreconnected
    have hsub : h ⊆ I ∪ (closure I)ᶜ := by
      rw [← hJc]; intro z hz hzJ; exact (he ▸ (⟨hz, hzJ⟩ : z ∈ h ∩ J) : z ∈ (∅ : Set S))
    obtain ⟨hIo, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
    rcases hhc.subset_or_subset hIo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub with hI | hE
    · exact inside_rulable h1 h2 h3 h4 h5 h6 h7 h8 q hW hI
    · refine q.rulable_of_good h1 h2 h3 h4 h5 h7 ?_
      exact disjoint_left.mpr fun z hzI hzh => hE hzh (subset_closure hzI)
  · obtain ⟨T, hTf, hTc, hTd, hcov⟩ := extract_chords h1 h2 h3 h4 h5 h7 q hW hne hfin hcor hnt
    exact (chords_rulable h1 h2 h3 h4 h5 h6 h7 h8 q hTf hTc hTd).mono fun U hUI hU =>
      disjoint_left.mpr fun z hzU hzh => disjoint_left.mp hU hzU (hcov ⟨hzh, hUI hzU⟩)

/-- **Theorem D for a finite cover**, by induction on the number of curves. -/
theorem rulable_of_cover (G : Set (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (Fs : Finset (Set S × Set S)) (hFs : ↑Fs ⊆ G) :
    ∀ {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S},
      σ.Quad J I A B C D sAB sBC sCD sDA → J ∪ I ⊆ ⋃ p ∈ Fs, p.2 →
      σ.Rulable (fun U => ∃ p ∈ G, U ⊆ p.2) I sAB sBC sCD sDA A B C D := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  induction Fs using Finset.induction_on with
  | empty =>
    intro J I A B C D sAB sBC sCD sDA q hcov
    obtain ⟨-, -, ⟨z, hz⟩, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
    have := hcov (Or.inr hz)
    simp at this
  | insert p₁ Fs hp ih =>
    intro J I A B C D sAB sBC sCD sDA q hcov
    have hp₁G : p₁ ∈ G := hFs (Finset.mem_insert_self _ _)
    have hFsG : ↑Fs ⊆ G := fun p hp => hFs (Finset.mem_insert_of_mem hp)
    obtain ⟨hIo, -, -, -, -, -, -, -, hclI, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
    have hcpt : IsCompact (J ∪ I) := by
      rw [union_comm, ← hclI]; exact isCompact_closure_region h1 h4 q.interior.2.1
    set F := (J ∪ I) \ ⋃ p ∈ Fs, p.2 with hF
    have hFc : IsCompact F := hcpt.diff (isOpen_biUnion fun p hp =>
      isOpen_region (hG p (hFsG hp)).2.1)
    have hFV : F ⊆ p₁.2 := by
      rintro z ⟨hz, hz'⟩
      obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hcov hz)
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hzp
      · exact absurd (mem_iUnion₂.mpr ⟨p, hp, hzp⟩) hz'
    obtain ⟨h, W, hW, hFW, hhWV, hfin, hcor, hcr⟩ :=
      exists_nice_curve h1 h2 h3 h4 h5 h6 h7 h8 q (hG p₁ hp₁G) hFc hFV
    obtain ⟨𝒳, 𝒴, R, hR⟩ := curve_rulable h1 h2 h3 h4 h5 h6 h7 h8 q hW hfin hcor
      fun p hp _ _ _ _ a b c d e f => (hcr p hp).no_fork h1 a b c d (Or.inl ⟨e, f⟩)
    have hGood : ∀ U V : Set S, U ⊆ V → (∃ p ∈ G, V ⊆ p.2) → ∃ p ∈ G, U ⊆ p.2 :=
      fun U V hUV ⟨p, hp, hVp⟩ => ⟨p, hp, hUV.trans hVp⟩
    suffices H : σ.CellsRulable (fun U => ∃ p ∈ G, U ⊆ p.2) I (⋃₀ 𝒳 ∪ ⋃₀ 𝒴) by
      obtain ⟨𝒳', 𝒴', -, -, R', hP⟩ := R.refine h1 h2 h3 h4 h5 h6 h7 h8 hGood q H
      exact ⟨𝒳', 𝒴', R', fun U hU => (hP U hU).1⟩
    intro J' I' A' B' C' D' s₁ s₂ s₃ s₄ q' hI'
    have hdis : Disjoint I' h := hR I' hI'
    have hI'I : I' ⊆ I := Space.cellsOf_subset hI'
    obtain ⟨-, hI'c, -, -, -, -, -, -, hclI', -⟩ := jordan h1 h2 h3 h4 h51 h7 q'.interior
    obtain ⟨hWo, -, -, -, -, -, -, -, -, -, -, hJW, -⟩ := jordan h1 h2 h3 h4 h51 h7 hW
    have hsub : I' ⊆ W ∪ (closure W)ᶜ := by
      rw [← hJW]; exact fun z hz hzh => disjoint_left.mp hdis hz hzh
    rcases hI'c.subset_or_subset hWo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub with hIW | hIE
    · exact q'.rulable_of_good h1 h2 h3 h4 h5 h7
        ⟨p₁, hp₁G, hIW.trans (subset_union_right.trans hhWV)⟩
    · refine ih hFsG q' ?_
      intro z hz
      have hzcl : z ∈ closure I' := by rw [hclI', union_comm]; exact hz
      have hzI : z ∈ J ∪ I := by
        rw [union_comm, ← hclI]; exact closure_mono hI'I hzcl
      have hzW : z ∉ W := fun hzW => by
        obtain ⟨y, hyW, hyI'⟩ := mem_closure_iff.mp hzcl W hWo hzW
        exact hIE hyI' (subset_closure hyW)
      by_contra hzF
      exact hzW (hFW ⟨hzI, hzF⟩)

end Ax

section Final

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Moore 1919, Theorem D** (p. 173). If each point on or within the closed curve `ABCDA` is
within some curve of a set `G` of closed curves, the interior of `ABCDA` can be divided by a double
ruling into subdivisions each within some curve of `G`. *Axioms used: 1–8.* -/
theorem m19_theoremD (q : σ.Quad J I A B C D sAB sBC sCD sDA) (G : Set (Set S × Set S))
    (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2) (hcov : ∀ P ∈ J ∪ I, ∃ p ∈ G, P ∈ p.2) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ p ∈ G, U ⊆ p.2 := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, hclI, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have hcpt : IsCompact (J ∪ I) := by
    rw [union_comm, ← hclI]; exact isCompact_closure_region h1 h4 q.interior.2.1
  obtain ⟨b, hbG, hbf, hcovb⟩ := hcpt.elim_finite_subcover_image (b := G) (c := fun p => p.2)
    (fun p hp => isOpen_region (hG p hp).2.1)
    (fun P hP => by obtain ⟨p, hp, hPp⟩ := hcov P hP; exact mem_iUnion₂.mpr ⟨p, hp, hPp⟩)
  obtain ⟨𝒳, 𝒴, R, hR⟩ := rulable_of_cover h1 h2 h3 h4 h5 h6 h7 h8 G hG hbf.toFinset
    (by simpa using hbG) q (by simpa using hcovb)
  obtain ⟨R', hr₁, hr₂⟩ := R.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  refine ⟨_, _, R', fun U hU => ?_⟩
  rw [R'.cells_eq_cellsOf, R'.carrier_eq, hr₁, hr₂] at hU
  exact hR U hU

end Final

end HPC.Moore
