import HPC.Moore.M19DPocket

/-!
# Moore 1919, Theorem D: the outer tile of a system of chords

If `M` is a finite set of chords of `J` whose pockets `P m` are mutually exclusive, then
`I − ⋃ (P m)′` is the interior of a closed curve (`outer_tile`): remove the pockets one at a time,
each chord being a cross-cut of the region left (`split_interior`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

theorem mem_closure_diff_of_notMem [TopologicalSpace S] {Y F : Set S} {z : S}
    (hz : z ∈ closure Y) (hF : IsClosed F) (hzF : z ∉ F) : z ∈ closure (Y \ F) := by
  rw [mem_closure_iff_nhds] at hz ⊢
  intro N hN
  obtain ⟨y, ⟨hyN, hyF⟩, hyY⟩ := hz (N ∩ Fᶜ) (Filter.inter_mem hN (hF.isOpen_compl.mem_nhds hzF))
  exact ⟨y, hyN, hyY, hyF⟩

/-- A data package for a chord with a pocket. -/
def Space.ChordPocket (σ : Space S) (J I m : Set S) (a b : S) (C C' P Q : Set S) : Prop :=
  a ∈ J ∧ b ∈ J ∧ @TArc S σ.topology a b m ∧ m \ {a, b} ⊆ I ∧ σ.Pocket J I m a b C C' P Q

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

variable {J I : Set S}

omit h8 in
/-- The open arc of a chord misses the closed pocket of another chord, when the pockets are
exclusive. -/
theorem ChordPocket.diff_disj_closure (hJI : σ.IsInteriorOf J I) {m m' : Set S} {a b a' b' : S}
    {C C' P Q Cm Cm' Pm Qm : Set S} (hm : σ.ChordPocket J I m a b C C' P Q)
    (hm' : σ.ChordPocket J I m' a' b' Cm Cm' Pm Qm) (hd : Disjoint m' m) (hP : Disjoint Pm P) :
    Disjoint (m \ {a, b}) (@closure S σ.topology Pm) ∧ a ∉ @closure S σ.topology Pm ∧
      b ∉ @closure S σ.topology Pm ∧ Disjoint P (@closure S σ.topology Pm) := by
  letI := σ.topology
  obtain ⟨ha, hb, hmt, hmI, hp⟩ := hm
  obtain ⟨ha', hb', hmt', hmI', hp'⟩ := hm'
  have hIJ := (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hJI).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hQ, -, haP, hbP⟩ := hp'.disj_facts h1 h2 h3 h4 h5 h7 hp hJI ha' hb' ha hb hmt' hmI'
    hmt hmI hd hP
  obtain ⟨-, hdc, -, -⟩ := hp.disj_facts h1 h2 h3 h4 h5 h7 hp' hJI ha hb ha' hb' hmt hmI
    hmt' hmI' hd.symm hP.symm
  refine ⟨?_, haP, hbP, hdc⟩
  rw [disjoint_left]
  intro z hz hzc
  rw [hp'.closure_P h1 h2 h3 h4 h5 h7] at hzc
  rcases hzc with hzP | hzm | hzC
  · exact disjoint_left.mp hp'.dis hzP (hQ hz)
  · exact disjoint_left.mp hd hzm hz.1
  · exact disjoint_left.mp hIJ (hmI hz) (hp'.C_sub hzC)

/-- **The outer tile.** For a finite set of chords with mutually exclusive pockets,
`I − ⋃ (P m)′` is the interior of a closed curve. -/
theorem outer_tile (hJI : σ.IsInteriorOf J I) {a b : Set S → S} {C C' P Q : Set S → Set S}
    (M : Finset (Set S))
    (hM : ∀ m ∈ M, σ.ChordPocket J I m (a m) (b m) (C m) (C' m) (P m) (Q m))
    (hdis : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint m m' ∧ Disjoint (P m) (P m')) :
    ∃ K₀, σ.IsInteriorOf K₀ (I \ ⋃ m ∈ M, @closure S σ.topology (P m)) := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, hclI, hIJ, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJI
  induction M using Finset.induction_on with
  | empty => exact ⟨J, by simpa using hJI⟩
  | insert m M hmM ih =>
    obtain ⟨K, hK⟩ := ih (fun m' hm' => hM m' (Finset.mem_insert_of_mem hm'))
      (fun m' hm' m'' hm'' hne => hdis m' (Finset.mem_insert_of_mem hm') m''
        (Finset.mem_insert_of_mem hm'') hne)
    set W := I \ ⋃ m' ∈ M, closure (P m') with hW
    have hmm := hM m (Finset.mem_insert_self _ _)
    obtain ⟨ha, hb, hmt, hmI, hp⟩ := hmm
    have facts : ∀ m' ∈ M, Disjoint (m \ {a m, b m}) (closure (P m')) ∧ a m ∉ closure (P m') ∧
        b m ∉ closure (P m') ∧ Disjoint (P m) (closure (P m')) := fun m' hm' => by
      have hne : m ≠ m' := fun h => hmM (h ▸ hm')
      obtain ⟨hd, hP⟩ := hdis m (Finset.mem_insert_self _ _) m' (Finset.mem_insert_of_mem hm') hne
      exact ChordPocket.diff_disj_closure h1 h2 h3 h4 h5 h7 hJI (hM m (Finset.mem_insert_self _ _))
        (hM m' (Finset.mem_insert_of_mem hm')) hd.symm hP.symm
    have hUc : IsClosed (⋃ m' ∈ M, closure (P m')) :=
      M.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
    obtain ⟨hWo, -, -, hWfr, -⟩ := jordan h1 h2 h3 h4 h51 h7 hK
    have hend : ∀ {e : S}, e ∈ J → (∀ m' ∈ M, e ∉ closure (P m')) → e ∈ K := by
      intro e heJ hen
      rw [← hWfr]
      refine ⟨mem_closure_diff_of_notMem (hclI ▸ Or.inr heJ) hUc ?_, ?_⟩
      · simp only [mem_iUnion, not_exists]; exact hen
      · rw [hWo.interior_eq]; exact fun h => disjoint_left.mp hIJ h.1 heJ
    have hmW : m \ {a m, b m} ⊆ W := fun z hz => ⟨hmI hz, by
      simp only [mem_iUnion, not_exists]
      exact fun m' hm' hzc => disjoint_left.mp (facts m' hm').1 hz hzc⟩
    obtain ⟨K₁, R₁, K₂, R₂, hR₁, hR₂, -, -, hsplit, hdis12, -, -⟩ :=
      split_interior h1 h2 h3 h4 h5 h7 h8 hK (hend ha fun m' hm' => (facts m' hm').2.1)
        (hend hb fun m' hm' => (facts m' hm').2.2.1) hmt hmW
    have hPW : P m ⊆ W \ m := fun z hz => ⟨⟨hp.P_sub hz, by
      simp only [mem_iUnion, not_exists]
      exact fun m' hm' hzc => disjoint_left.mp (facts m' hm').2.2.2 hz hzc⟩,
      fun hzm => disjoint_left.mp hp.P_disj_t hz hzm⟩
    have hPne : (P m).Nonempty := (jordan h1 h2 h3 h4 h51 h7 hp.hP).2.2.1
    -- the region of `W − m` containing the pocket is the pocket
    have key : ∀ {R R' K' : Set S}, σ.IsInteriorOf K' R → W \ m = R ∪ R' → Disjoint R R' →
        P m ⊆ R → R' = I \ ⋃ m' ∈ insert m M, closure (P m') := by
      intro R R' K' hR hsp hRR' hPR
      have hRP : R ⊆ P m := by
        obtain ⟨-, hRc, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR
        have hRsub : R ⊆ I \ m := fun z hz => by
          have : z ∈ W \ m := hsp ▸ Or.inl hz
          exact ⟨this.1.1, this.2⟩
        rcases hp.conn h1 h2 h3 h4 h5 h7 hRc hRsub with h | h
        · exact h
        · obtain ⟨z, hz⟩ := hPne
          exact absurd (h (hPR hz)) (disjoint_left.mp hp.dis hz)
      have hRe : R = P m := subset_antisymm hRP hPR
      ext z
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_diff, mem_union, not_or]
      constructor
      · intro hz
        have hzW : z ∈ W \ m := hsp ▸ Or.inr hz
        refine ⟨hzW.1.1, ?_, hzW.1.2⟩
        rw [hp.closure_P h1 h2 h3 h4 h5 h7]
        rintro (hzP | hzm | hzC)
        · exact disjoint_left.mp hRR' (hRe ▸ hzP) hz
        · exact hzW.2 hzm
        · exact disjoint_left.mp hIJ hzW.1.1 (hp.C_sub hzC)
      · rintro ⟨hzI, hzc, hzU⟩
        have hzW : z ∈ W \ m := ⟨⟨hzI, hzU⟩, fun hzm => hzc (hp.t_sub_closure_P h1 h2 h3 h4 h5 h7 hzm)⟩
        rw [hsp] at hzW
        rcases hzW with h | h
        · exact absurd (subset_closure (hRe ▸ h)) hzc
        · exact h
    obtain ⟨-, hPc, -⟩ := jordan h1 h2 h3 h4 h51 h7 hp.hP
    rcases hPc.subset_or_subset (jordan h1 h2 h3 h4 h51 h7 hR₁).1 (jordan h1 h2 h3 h4 h51 h7 hR₂).1
      hdis12 (hsplit ▸ hPW) with h | h
    · exact ⟨K₂, key hR₁ hsplit hdis12 h ▸ hR₂⟩
    · exact ⟨K₁, key hR₂ (by rw [union_comm]; exact hsplit) hdis12.symm h ▸ hR₁⟩

end Ax

section Arc

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S}

/-- **An arc through the outer tile** from a point of the open arc of one of the chords to a point
of `J` outside all the closed pockets. -/
theorem outer_arc (hJI : σ.IsInteriorOf J I) {a b : Set S → S} {C C' P Q : Set S → Set S}
    (M : Finset (Set S))
    (hM : ∀ m ∈ M, σ.ChordPocket J I m (a m) (b m) (C m) (C' m) (P m) (Q m))
    (hdis : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint m m' ∧ Disjoint (P m) (P m'))
    {t : Set S} (ht : t ∈ M) {c : S} (hc : c ∈ t \ {a t, b t}) {d : S} (hdJ : d ∈ J)
    (hd : ∀ m ∈ M, d ∉ @closure S σ.topology (P m)) :
    ∃ u, @TArc S σ.topology c d u ∧ u \ {c, d} ⊆ I \ ⋃ m ∈ M, @closure S σ.topology (P m) := by
  classical
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, hclI, hIJ, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJI
  obtain ⟨K₀, hK₀⟩ := outer_tile h1 h2 h3 h4 h5 h7 h8 hJI M hM hdis
  obtain ⟨hWo, -, -, hWfr, -⟩ := jordan h1 h2 h3 h4 h51 h7 hK₀
  have hUc : ∀ M' : Finset (Set S), IsClosed (⋃ m' ∈ M', closure (P m')) := fun M' =>
    M'.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨hta, htb, htt, htI, hp⟩ := hM t ht
  have hcI : c ∈ I := htI hc
  have hdK : d ∈ K₀ := by
    rw [← hWfr]
    refine ⟨mem_closure_diff_of_notMem (hclI ▸ Or.inr hdJ) (hUc M) ?_, ?_⟩
    · simp only [mem_iUnion, not_exists]; exact hd
    · rw [hWo.interior_eq]; exact fun h => disjoint_left.mp hIJ h.1 hdJ
  have hcK : c ∈ K₀ := by
    rw [← hWfr]
    refine ⟨?_, ?_⟩
    · have hsub : Q t \ ⋃ m' ∈ M.erase t, closure (P m') ⊆ I \ ⋃ m ∈ M, closure (P m) := by
        rintro z ⟨hzQ, hzU⟩
        refine ⟨hp.Q_sub hzQ, ?_⟩
        simp only [mem_iUnion, not_exists] at hzU ⊢
        intro m hm hzc
        by_cases hmt : m = t
        · subst hmt
          rw [hp.closure_P h1 h2 h3 h4 h5 h7] at hzc
          rcases hzc with hzP | hzm | hzC
          · exact disjoint_left.mp hp.dis hzP hzQ
          · exact disjoint_left.mp hp.swap.P_disj_t hzQ hzm
          · exact disjoint_left.mp hIJ (hp.Q_sub hzQ) (hp.C_sub hzC)
        · exact hzU m (Finset.mem_erase.mpr ⟨hmt, hm⟩) hzc
      refine closure_mono hsub (mem_closure_diff_of_notMem
        (hp.swap.t_sub_closure_P h1 h2 h3 h4 h5 h7 hc.1) (hUc _) ?_)
      simp only [mem_iUnion, not_exists]
      intro m hm hcm
      obtain ⟨hmt, hm⟩ := Finset.mem_erase.mp hm
      obtain ⟨hd', hP'⟩ := hdis t ht m hm (Ne.symm hmt)
      exact disjoint_left.mp (ChordPocket.diff_disj_closure h1 h2 h3 h4 h5 h7 hJI (hM t ht)
        (hM m hm) hd'.symm hP'.symm).1 hc hcm
    · rw [hWo.interior_eq]
      rintro ⟨-, hc'⟩
      simp only [mem_iUnion, not_exists] at hc'
      exact hc' t ht (hp.t_sub_closure_P h1 h2 h3 h4 h5 h7 hc.1)
  have hcd : c ≠ d := fun h => disjoint_left.mp hIJ hcI (h ▸ hdJ)
  exact exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hK₀ (Or.inl rfl) hcK hdK hcd

end Arc

end HPC.Moore
