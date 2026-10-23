import HPC.Moore.M19DOuter

/-!
# Moore 1919, Theorem D: chords in the two halves of a cut, and their weights

The *weight* of a chord of `ABCDA` is `1` if it joins opposite sides, `3` if it meets only one side,
and `2` otherwise (`chordWeight`). A chord missing the arc `x` of a cut is a chord of one of the two
halves, with the same weight (`Space.Quad.Cut.chord_half`, `Space.Quad.Cut.weight_A`,
`Space.Quad.Cut.weight_B`). Rulings of the two halves missing the chords of each half glue to a ruling
of `ABCDA` missing all the chords (`Space.Quad.Cut.glue_chords`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- The weight of a chord meeting the sides as recorded by the four propositions. -/
noncomputable def chordWt (mAB mBC mCD mDA : Prop) : ℕ := by
  classical
  exact if (mAB ∧ mCD) ∨ (mBC ∧ mDA) then 1 else
    if (¬mBC ∧ ¬mCD ∧ ¬mDA) ∨ (¬mAB ∧ ¬mCD ∧ ¬mDA) ∨ (¬mAB ∧ ¬mBC ∧ ¬mDA) ∨
      (¬mAB ∧ ¬mBC ∧ ¬mCD) then 3 else 2

/-- The weight of a chord `t` of the quadrilateral with sides `sAB, sBC, sCD, sDA`. -/
noncomputable def chordWeight (sAB sBC sCD sDA t : Set S) : ℕ :=
  chordWt (t ∩ sAB).Nonempty (t ∩ sBC).Nonempty (t ∩ sCD).Nonempty (t ∩ sDA).Nonempty

theorem chordWt_rot (a b c d : Prop) : chordWt b c d a = chordWt a b c d := by
  unfold chordWt
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;> simp [*]

theorem one_le_chordWt (a b c d : Prop) : 1 ≤ chordWt a b c d := by
  unfold chordWt; split_ifs <;> omega

theorem chordWeight_rot (sAB sBC sCD sDA t : Set S) :
    chordWeight sBC sCD sDA sAB t = chordWeight sAB sBC sCD sDA t :=
  chordWt_rot _ _ _ _

theorem Space.IsChord.rot {J I : Set S} {A B C D : S} {t : Set S}
    (h : σ.IsChord J I A B C D t) : σ.IsChord J I B C D A t := by
  obtain ⟨a, b, ha, hb, ht, htI⟩ := h
  have e : ({B, C, D, A} : Set S) = {A, B, C, D} := by
    ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  exact ⟨a, b, e ▸ ha, e ▸ hb, ht, htI⟩

theorem Space.IsChord.unrot {J I : Set S} {A B C D : S} {t : Set S}
    (h : σ.IsChord J I B C D A t) : σ.IsChord J I A B C D t :=
  h.rot.rot.rot

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S}

/-- **A chord missing the cut lies in one half**, and is a chord of that half. -/
theorem Space.Quad.Cut.chord_half (c : q.Cut x) {s : Set S} {e₁ e₂ : S}
    (hs : @TArc S σ.topology e₁ e₂ s) (hsI : s \ {e₁, e₂} ⊆ I \ x)
    (he₁ : e₁ ∈ J ∪ x) (he₂ : e₂ ∈ J ∪ x)
    (hn₁ : e₁ ∉ ({A, B, C, D, c.X, c.X'} : Set S)) (hn₂ : e₂ ∉ ({A, B, C, D, c.X, c.X'} : Set S)) :
    (s ⊆ c.clA ∧ σ.IsChord (c.s₁ ∪ x ∪ c.t₁ ∪ sDA) c.IA A c.X c.X' D s) ∨
    (s ⊆ c.clB ∧ σ.IsChord (c.s₂ ∪ sBC ∪ c.t₂ ∪ x) c.IB c.X B C c.X' s) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  have hsplit : s \ {e₁, e₂} ⊆ c.IA ∪ c.IB := c.split ▸ hsI
  have notI : ∀ {e : S}, e ∈ J ∪ x → e ∉ I \ x := by
    rintro e (he | he) ⟨heI, hex⟩
    · exact disjoint_left.mp hIJ heI he
    · exact hex he
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hn₁ hn₂
  rcases hs.isPreconnected_diff.subset_or_subset (c.IA_open h1 h2 h3 h4 h51 h7)
    (c.IB_open h1 h2 h3 h4 h51 h7) c.dis hsplit with hA | hB
  · left
    have hcl : s ⊆ c.clA := by
      rw [← c.closure_IA h1 h2 h3 h4 h51 h7]
      exact hs.subset_closure_diff.trans (closure_mono hA)
    have hend : ∀ {e : S}, e ∈ s → e ∈ J ∪ x → e ∈ c.s₁ ∪ x ∪ c.t₁ ∪ sDA := by
      intro e hes he
      rcases hcl hes with h | h
      · exact absurd (c.IA_sub h) (notI he)
      · exact h
    refine ⟨hcl, e₁, e₂, ⟨hend hs.left_mem he₁, ?_⟩, ⟨hend hs.right_mem he₂, ?_⟩, hs, hA⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]; tauto
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]; tauto
  · right
    have hcl : s ⊆ c.clB := by
      rw [← c.closure_IB h1 h2 h3 h4 h51 h7]
      exact hs.subset_closure_diff.trans (closure_mono hB)
    have hend : ∀ {e : S}, e ∈ s → e ∈ J ∪ x → e ∈ c.s₂ ∪ sBC ∪ c.t₂ ∪ x := by
      intro e hes he
      rcases hcl hes with h | h
      · exact absurd (c.IB_sub h) (notI he)
      · exact h
    refine ⟨hcl, e₁, e₂, ⟨hend hs.left_mem he₁, ?_⟩, ⟨hend hs.right_mem he₂, ?_⟩, hs, hB⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]; tauto
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]; tauto

/-- A chord of the half `AXX′DA` missing `x` has the same weight there as in `ABCDA`. -/
theorem Space.Quad.Cut.weight_A (c : q.Cut x) {s : Set S} (hs : s ⊆ c.clA) (hsx : Disjoint s x) :
    chordWeight c.s₁ x c.t₁ sDA s = chordWeight sAB sBC sCD sDA s := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have e1 : (s ∩ c.s₁).Nonempty ↔ (s ∩ sAB).Nonempty := by
    refine ⟨fun ⟨z, hz⟩ => ⟨z, hz.1, c.s₁_sub hz.2⟩, fun ⟨z, hzs, hz⟩ => ?_⟩
    rw [← c.hs] at hz
    rcases hz with hz | hz
    · exact ⟨z, hzs, hz⟩
    · exact absurd (icl ⟨hs hzs, Or.inr (Or.inl (Or.inl (Or.inl hz)))⟩) (disjoint_left.mp hsx hzs)
  have e3 : (s ∩ c.t₁).Nonempty ↔ (s ∩ sCD).Nonempty := by
    refine ⟨fun ⟨z, hz⟩ => ⟨z, hz.1, c.t₁_sub hz.2⟩, fun ⟨z, hzs, hz⟩ => ?_⟩
    rw [← c.ht] at hz
    rcases hz with hz | hz
    · exact ⟨z, hzs, hz⟩
    · exact absurd (icl ⟨hs hzs, Or.inr (Or.inl (Or.inr hz))⟩) (disjoint_left.mp hsx hzs)
  have e2 : (s ∩ x).Nonempty ↔ False :=
    ⟨fun ⟨z, hzs, hzx⟩ => disjoint_left.mp hsx hzs hzx, False.elim⟩
  have e4 : (s ∩ sBC).Nonempty ↔ False := by
    refine ⟨fun ⟨z, hzs, hz⟩ => ?_, False.elim⟩
    have := c.closure_IA_disjoint_BC h1 h2 h3 h4 h51 h7
    rw [c.closure_IA h1 h2 h3 h4 h51 h7] at this
    exact disjoint_left.mp this (hs hzs) hz
  simp only [chordWeight, e1, e2, e3, e4]

/-- A chord of the half `XBCX′X` missing `x` has the same weight there as in `ABCDA`. -/
theorem Space.Quad.Cut.weight_B (c : q.Cut x) {s : Set S} (hs : s ⊆ c.clB) (hsx : Disjoint s x) :
    chordWeight c.s₂ sBC c.t₂ x s = chordWeight sAB sBC sCD sDA s := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have icl := c.inter_cl h1 h2 h3 h4 h51 h7
  have e1 : (s ∩ c.s₂).Nonempty ↔ (s ∩ sAB).Nonempty := by
    refine ⟨fun ⟨z, hz⟩ => ⟨z, hz.1, c.s₂_sub hz.2⟩, fun ⟨z, hzs, hz⟩ => ?_⟩
    rw [← c.hs] at hz
    rcases hz with hz | hz
    · exact absurd (icl ⟨Or.inr (Or.inl (Or.inl (Or.inl hz))), hs hzs⟩) (disjoint_left.mp hsx hzs)
    · exact ⟨z, hzs, hz⟩
  have e3 : (s ∩ c.t₂).Nonempty ↔ (s ∩ sCD).Nonempty := by
    refine ⟨fun ⟨z, hz⟩ => ⟨z, hz.1, c.t₂_sub hz.2⟩, fun ⟨z, hzs, hz⟩ => ?_⟩
    rw [← c.ht] at hz
    rcases hz with hz | hz
    · exact absurd (icl ⟨Or.inr (Or.inl (Or.inr hz)), hs hzs⟩) (disjoint_left.mp hsx hzs)
    · exact ⟨z, hzs, hz⟩
  have e2 : (s ∩ x).Nonempty ↔ False :=
    ⟨fun ⟨z, hzs, hzx⟩ => disjoint_left.mp hsx hzs hzx, False.elim⟩
  have e4 : (s ∩ sDA).Nonempty ↔ False := by
    refine ⟨fun ⟨z, hzs, hz⟩ => ?_, False.elim⟩
    have := c.closure_IB_disjoint_DA h1 h2 h3 h4 h51 h7
    rw [c.closure_IB h1 h2 h3 h4 h51 h7] at this
    exact disjoint_left.mp this (hs hzs) hz
  simp only [chordWeight, e1, e2, e3, e4]

end Ax

section Glue

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S}

/-- **Gluing rulings missing chords.** -/
theorem Space.Quad.Cut.glue_chords (c : q.Cut x) (hxq : σ.XArc I sAB sCD A B C D x)
    {T TA TB : Set (Set S)}
    (HA : σ.Rulable (fun U => Disjoint U (⋃₀ TA)) c.IA c.s₁ x c.t₁ sDA A c.X c.X' D)
    (HB : σ.Rulable (fun U => Disjoint U (⋃₀ TB)) c.IB c.s₂ sBC c.t₂ x c.X B C c.X')
    (covA : ⋃₀ T ∩ c.IA ⊆ ⋃₀ TA) (covB : ⋃₀ T ∩ c.IB ⊆ ⋃₀ TB) :
    σ.Rulable (fun U => Disjoint U (⋃₀ T)) I sAB sBC sCD sDA A B C D := by
  refine c.rulable h1 h2 h3 h4 h5 h6 h7 h8 (fun U V hUV hV => hV.mono_left hUV) hxq
    (HA.mono fun U hU hd => ?_) (HB.mono fun U hU hd => ?_)
  · exact disjoint_left.mpr fun z hzU hzT => disjoint_left.mp hd hzU (covA ⟨hzT, hU hzU⟩)
  · exact disjoint_left.mpr fun z hzU hzT => disjoint_left.mp hd hzU (covB ⟨hzT, hU hzU⟩)

end Glue

end HPC.Moore
