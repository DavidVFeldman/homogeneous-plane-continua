import HPC.Moore.M19DCorner

/-!
# Moore 1919, Theorem D: a ruling missing finitely many chords

**Theorem.** For a finite set `T` of mutually exclusive chords of `ABCDA` (ends on the open sides),
there is a ruling of `ABCDA` none of whose subdivisions meets a chord of `T` (`chords_rulable`).

Induction on the total weight (`weightSum`). A chord joining opposite sides is an arc of a cut.
Otherwise take a chord `t` whose pocket is maximal, with an end `a` on `AB` (after rotating), a point
`d` of the open side `CD` on no base of a maximal pocket (`exists_gap`) and an arc `u` from a point
`c` of `t` to `d` through the outer tile (`outer_arc`); cut along `x = ac + u`. The remaining piece
`cb` of `t` is a chord of one half, of smaller weight.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

attribute [local instance] Classical.propDecidable

/-- The total weight of a finite set of chords. -/
noncomputable def weightSum (sAB sBC sCD sDA : Set S) (T : Finset (Set S)) : ℕ :=
  ∑ t ∈ T, chordWeight sAB sBC sCD sDA t

theorem weightSum_rot (sAB sBC sCD sDA : Set S) (T : Finset (Set S)) :
    weightSum sBC sCD sDA sAB T = weightSum sAB sBC sCD sDA T :=
  Finset.sum_congr rfl fun _ _ => chordWeight_rot _ _ _ _ _

theorem chordWt_le_two_ab {a b c d : Prop} (ha : a) (hb : b) : chordWt a b c d ≤ 2 := by
  unfold chordWt; split_ifs <;> simp_all

theorem chordWt_le_two_ad {a b c d : Prop} (ha : a) (hd : d) : chordWt a b c d ≤ 2 := by
  unfold chordWt; split_ifs <;> simp_all

theorem chordWt_ge_two {a b c d : Prop} (h : ¬ ((a ∧ c) ∨ (b ∧ d))) : 2 ≤ chordWt a b c d := by
  unfold chordWt; split_ifs <;> simp_all

theorem chordWt_eq_one {a b c d : Prop} (h : (a ∧ c) ∨ (b ∧ d)) : chordWt a b c d = 1 := by
  unfold chordWt; rw [if_pos h]

theorem chordWt_eq_three {a : Prop} : chordWt a False False False = 3 := by
  unfold chordWt; simp

/-- The statement of the theorem for total weights below `n`. -/
def ChordsBelow (σ : Space S) (n : ℕ) : Prop :=
  ∀ {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S},
    σ.Quad J I A B C D sAB sBC sCD sDA → ∀ T : Finset (Set S),
      (∀ t ∈ T, σ.IsChord J I A B C D t) → (T : Set (Set S)).Pairwise Disjoint →
      weightSum sAB sBC sCD sDA T < n →
      σ.Rulable (fun U => Disjoint U (⋃₀ (T : Set (Set S)))) I sAB sBC sCD sDA A B C D

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
  {q : σ.Quad J I A B C D sAB sBC sCD sDA} {x : Set S}

/-- A chord of `ABCDA` missing the arc of a cut is a chord of one half. -/
theorem Space.Quad.Cut.chord_half' (c : q.Cut x) {s : Set S} (hs : σ.IsChord J I A B C D s)
    (hsx : Disjoint s x) :
    (s ⊆ c.clA ∧ σ.IsChord (c.s₁ ∪ x ∪ c.t₁ ∪ sDA) c.IA A c.X c.X' D s) ∨
    (s ⊆ c.clB ∧ σ.IsChord (c.s₂ ∪ sBC ∪ c.t₂ ∪ x) c.IB c.X B C c.X' s) := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨a, b, ⟨haJ, haK⟩, ⟨hbJ, hbK⟩, hst, hsI⟩ := hs
  have hX : c.X ∈ x := c.qA.bc.left_mem
  have hX' : c.X' ∈ x := c.qA.bc.right_mem
  have hn : ∀ {e : S}, e ∈ s → e ∉ ({A, B, C, D} : Set S) →
      e ∉ ({A, B, C, D, c.X, c.X'} : Set S) := by
    intro e hes heK
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at heK ⊢
    refine ⟨heK.1, heK.2.1, heK.2.2.1, heK.2.2.2, ?_, ?_⟩
    · rintro rfl; exact disjoint_left.mp hsx hes hX
    · rintro rfl; exact disjoint_left.mp hsx hes hX'
  exact c.chord_half h1 h2 h3 h4 h5 h7 hst
    (fun z hz => ⟨hsI hz, fun hzx => disjoint_left.mp hsx hz.1 hzx⟩) (Or.inl haJ) (Or.inl hbJ)
    (hn hst.left_mem haK) (hn hst.right_mem hbK)

/-- A chord in the closure of the half `B` misses the half `A`. -/
theorem Space.Quad.Cut.clB_disj_IA (c : q.Cut x) {s : Set S} (hs : s ⊆ c.clB) :
    Disjoint s c.IA := by
  have h51 := axiom5₁_of_axiom5 h5
  rw [disjoint_left]
  intro z hzs hzA
  exact (c.IA_sub hzA).2 (c.inter_cl h1 h2 h3 h4 h51 h7 ⟨Or.inl hzA, hs hzs⟩)

theorem Space.Quad.Cut.clA_disj_IB (c : q.Cut x) {s : Set S} (hs : s ⊆ c.clA) :
    Disjoint s c.IB := by
  have h51 := axiom5₁_of_axiom5 h5
  rw [disjoint_left]
  intro z hzs hzB
  exact (c.IB_sub hzB).2 (c.inter_cl h1 h2 h3 h4 h51 h7 ⟨hs hzs, Or.inl hzB⟩)

/-- **Distributing chords to the two halves.** -/
theorem Space.Quad.Cut.halves (c : q.Cut x) (T' : Finset (Set S))
    (hT : ∀ s ∈ T', σ.IsChord J I A B C D s) (hx : ∀ s ∈ T', Disjoint s x) :
    (∀ s ∈ T'.filter (· ⊆ c.clA), σ.IsChord (c.s₁ ∪ x ∪ c.t₁ ∪ sDA) c.IA A c.X c.X' D s) ∧
    (∀ s ∈ T'.filter (fun s => ¬ s ⊆ c.clA),
      s ⊆ c.clB ∧ σ.IsChord (c.s₂ ∪ sBC ∪ c.t₂ ∪ x) c.IB c.X B C c.X' s) ∧
    weightSum c.s₁ x c.t₁ sDA (T'.filter (· ⊆ c.clA)) =
      ∑ s ∈ T'.filter (· ⊆ c.clA), chordWeight sAB sBC sCD sDA s ∧
    weightSum c.s₂ sBC c.t₂ x (T'.filter (fun s => ¬ s ⊆ c.clA)) =
      ∑ s ∈ T'.filter (fun s => ¬ s ⊆ c.clA), chordWeight sAB sBC sCD sDA s ∧
    ⋃₀ (T' : Set (Set S)) ∩ c.IA ⊆ ⋃₀ ↑(T'.filter (· ⊆ c.clA)) ∧
    ⋃₀ (T' : Set (Set S)) ∩ c.IB ⊆ ⋃₀ ↑(T'.filter (fun s => ¬ s ⊆ c.clA)) := by
  have hB : ∀ s ∈ T', ¬ s ⊆ c.clA →
      s ⊆ c.clB ∧ σ.IsChord (c.s₂ ∪ sBC ∪ c.t₂ ∪ x) c.IB c.X B C c.X' s := fun s hs hsA =>
    ((c.chord_half' h1 h2 h3 h4 h5 h7 (hT s hs) (hx s hs)).resolve_left fun h => hsA h.1)
  refine ⟨fun s hs => ?_, fun s hs => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hs, hsA⟩ := Finset.mem_filter.mp hs
    rcases c.chord_half' h1 h2 h3 h4 h5 h7 (hT s hs) (hx s hs) with h | h
    · exact h.2
    · exfalso
      obtain ⟨a, b, -, -, hst, hsI⟩ := h.2
      letI := σ.topology
      obtain ⟨z, hz⟩ := hst.nonempty_diff
      exact disjoint_left.mp (c.clA_disj_IB h1 h2 h3 h4 h5 h7 hsA) hz.1 (hsI hz)
  · obtain ⟨hs, hsA⟩ := Finset.mem_filter.mp hs
    exact hB s hs hsA
  · refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hs, hsA⟩ := Finset.mem_filter.mp hs
    exact c.weight_A h1 h2 h3 h4 h5 h7 hsA (hx s hs)
  · refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hs, hsA⟩ := Finset.mem_filter.mp hs
    exact c.weight_B h1 h2 h3 h4 h5 h7 (hB s hs hsA).1 (hx s hs)
  · rintro z ⟨⟨s, hs, hzs⟩, hzA⟩
    by_cases hsA : s ⊆ c.clA
    · exact ⟨s, Finset.mem_filter.mpr ⟨hs, hsA⟩, hzs⟩
    · exact absurd hzA (disjoint_left.mp (c.clB_disj_IA h1 h2 h3 h4 h5 h7 (hB s hs hsA).1) hzs)
  · rintro z ⟨⟨s, hs, hzs⟩, hzB⟩
    by_cases hsA : s ⊆ c.clA
    · exact absurd hzB (disjoint_left.mp (c.clA_disj_IB h1 h2 h3 h4 h5 h7 hsA) hzs)
    · exact ⟨s, Finset.mem_filter.mpr ⟨hs, hsA⟩, hzs⟩

end Ax

theorem weightSum_sub_le {sAB sBC sCD sDA : Set S} {T U : Finset (Set S)} {t : Set S} (ht : t ∈ T)
    (hU : U ⊆ T.erase t) :
    ∑ s ∈ U, chordWeight sAB sBC sCD sDA s + chordWeight sAB sBC sCD sDA t ≤
      weightSum sAB sBC sCD sDA T := by
  rw [weightSum, ← Finset.sum_erase_add _ _ ht]
  exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset hU) _

section Step

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **A chord joining `AB` and `CD`** is the arc of a cut. -/
theorem opp_step {n : ℕ} (ih : ChordsBelow σ n) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (T : Finset (Set S)) (hT : ∀ t ∈ T, σ.IsChord J I A B C D t)
    (hTd : (T : Set (Set S)).Pairwise Disjoint) (hW : weightSum sAB sBC sCD sDA T < n + 1)
    {t : Set S} (ht : t ∈ T) (hab : (t ∩ sAB).Nonempty) (hcd : (t ∩ sCD).Nonempty) :
    σ.Rulable (fun U => Disjoint U (⋃₀ (T : Set (Set S)))) I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨a, b, ⟨haJ, haK⟩, ⟨hbJ, hbK⟩, htt, htI⟩ := hT t ht
  obtain ⟨z, hzt, hzAB⟩ := hab
  obtain ⟨w, hwt, hwCD⟩ := hcd
  have hzw : z ≠ w := fun h => disjoint_left.mp q.ab_cd hzAB (h ▸ hwCD)
  have hzK : z ∉ ({A, B} : Set S) := by
    rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior htI hzt (q.sAB_sub hzAB) with rfl | rfl <;>
      exact fun h => by simp only [mem_insert_iff, mem_singleton_iff] at h haK hbK; tauto
  have hwK : w ∉ ({C, D} : Set S) := by
    rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior htI hwt (q.sCD_sub hwCD) with rfl | rfl <;>
      exact fun h => by simp only [mem_insert_iff, mem_singleton_iff] at h haK hbK; tauto
  have hxq : σ.XArc I sAB sCD A B C D t := by
    refine ⟨z, w, ⟨hzAB, hzK⟩, ⟨hwCD, hwK⟩, ?_⟩
    rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior htI hzt (q.sAB_sub hzAB) with rfl | rfl <;>
      rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior htI hwt (q.sCD_sub hwCD) with rfl | rfl
    · exact absurd rfl hzw
    · exact ⟨htt, htI⟩
    · exact ⟨htt.symm, by rw [pair_comm]; exact htI⟩
    · exact absurd rfl hzw
  obtain ⟨c⟩ := q.exists_cut h1 h2 h3 h4 h5 h7 h8 hxq
  have hx : ∀ s ∈ T.erase t, Disjoint s t := fun s hs =>
    hTd (Finset.mem_erase.mp hs).2 ht (Finset.mem_erase.mp hs).1
  obtain ⟨hA, hB, hwA, hwB, covA, covB⟩ :=
    c.halves h1 h2 h3 h4 h5 h7 (T.erase t) (fun s hs => hT s (Finset.mem_of_mem_erase hs)) hx
  have hwt : 1 ≤ chordWeight sAB sBC sCD sDA t := one_le_chordWt _ _ _ _
  have hdA := weightSum_sub_le ht (Finset.filter_subset (· ⊆ c.clA) (T.erase t))
    (sAB := sAB) (sBC := sBC) (sCD := sCD) (sDA := sDA)
  have hdB := weightSum_sub_le ht (Finset.filter_subset (fun s => ¬ s ⊆ c.clA) (T.erase t))
    (sAB := sAB) (sBC := sBC) (sCD := sCD) (sDA := sDA)
  have pd : ∀ U : Finset (Set S), U ⊆ T → (U : Set (Set S)).Pairwise Disjoint := fun U hU =>
    hTd.mono (Finset.coe_subset.mpr hU)
  have RA := ih c.qA _ hA (pd _ ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)))
    (by rw [hwA]; omega)
  have RB := ih c.qB _ (fun s hs => (hB s hs).2)
    (pd _ ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))) (by rw [hwB]; omega)
  refine c.glue_chords h1 h2 h3 h4 h5 h6 h7 h8 hxq RA RB ?_ ?_
  · rintro y ⟨⟨s, hs, hys⟩, hyA⟩
    by_cases hst : s = t
    · subst hst; exact absurd hys (c.IA_sub hyA).2
    · exact covA ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyA⟩
  · rintro y ⟨⟨s, hs, hys⟩, hyB⟩
    by_cases hst : s = t
    · subst hst; exact absurd hys (c.IB_sub hyB).2
    · exact covB ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyB⟩

end Step

section Corners

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

theorem Space.Quad.corners_sub (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    ({A, B, C, D} : Set S) ⊆ J := by
  intro z hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact q.sAB_sub q.ab.2.2.2.2.1
  · exact q.sAB_sub q.ab.2.2.2.2.2.1
  · exact q.sCD_sub q.cd.2.2.2.2.1
  · exact q.sCD_sub q.cd.2.2.2.2.2.1

theorem Space.Quad.corners_not_two (q : σ.Quad J I A B C D sAB sBC sCD sDA) (x y : S) :
    ¬ ({A, B, C, D} : Set S) ⊆ {x, y} := by
  intro h
  have hA := h (by simp : A ∈ ({A, B, C, D} : Set S))
  have hB := h (by simp : B ∈ ({A, B, C, D} : Set S))
  have hC := h (by simp : C ∈ ({A, B, C, D} : Set S))
  have hAB : A ≠ B := q.ab.1
  have hBC : B ≠ C := q.bc.1
  have hAC : A ≠ C := fun e => disjoint_left.mp q.ab_cd q.ab.2.2.2.2.1 (e ▸ q.cd.2.2.2.2.1)
  simp only [mem_insert_iff, mem_singleton_iff] at hA hB hC
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> rcases hC with rfl | rfl <;> simp_all

end Corners

section Absorb

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Absorbing a chord with maximal pocket and an end on `AB`.** -/
theorem absorb_step {n : ℕ} (ih : ChordsBelow σ n) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (T : Finset (Set S)) (hT : ∀ t ∈ T, σ.IsChord J I A B C D t)
    (hTd : (T : Set (Set S)).Pairwise Disjoint) (hW : weightSum sAB sBC sCD sDA T < n + 1)
    (hno : ∀ t ∈ T, ¬ (((t ∩ sAB).Nonempty ∧ (t ∩ sCD).Nonempty) ∨
      ((t ∩ sBC).Nonempty ∧ (t ∩ sDA).Nonempty)))
    {a b : Set S → S} {Cb C' P Q : Set S → Set S}
    (hp : ∀ t ∈ T, σ.ChordPocket J I t (a t) (b t) (Cb t) (C' t) (P t) (Q t))
    (hK : ∀ t ∈ T, (({A, B, C, D} : Set S) ∩ Cb t).Subsingleton)
    {t : Set S} (ht : t ∈ T) (hmax : ∀ s ∈ T, P t ⊆ P s → s = t) (hat : a t ∈ sAB) :
    σ.Rulable (fun U => Disjoint U (⋃₀ (T : Set (Set S)))) I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  have hKJ := q.corners_sub
  have hK2 := q.corners_not_two
  have hend : ∀ s ∈ T, ∀ e ∈ s, e ∈ J → e ∉ ({A, B, C, D} : Set S) := by
    intro s hs e hes heJ
    obtain ⟨a', b', ⟨-, ha'⟩, ⟨-, hb'⟩, -, hsI⟩ := hT s hs
    rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior hsI hes heJ with rfl | rfl
    exacts [ha', hb']
  -- distinct chords have distinct pockets
  have hinj : ∀ s ∈ T, ∀ s' ∈ T, P s = P s' → s = s' := by
    intro s hs s' hs' he
    by_contra hne
    obtain ⟨-, -, hst, hsI, hps⟩ := hp s hs
    obtain ⟨-, -, -, -, hps'⟩ := hp s' hs'
    obtain ⟨y, hy⟩ := hst.nonempty_diff
    have hy' : y ∈ s' ∪ Cb s' := by
      rw [← hps'.frontier_P h1 h2 h3 h4 h5 h7, ← he, hps.frontier_P h1 h2 h3 h4 h5 h7]
      exact Or.inl hy.1
    rcases hy' with h | h
    · exact disjoint_left.mp (hTd hs hs' hne) hy.1 h
    · exact disjoint_left.mp hIJ (hsI hy) (hps'.C_sub h)
  have hnest : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' →
      Disjoint (P s) (P s') ∨ P s ⊆ P s' ∨ P s' ⊆ P s := by
    intro s hs s' hs' hne
    obtain ⟨has, hbs, hst, hsI, hps⟩ := hp s hs
    obtain ⟨has', hbs', hst', hsI', hps'⟩ := hp s' hs'
    exact hps.nest h1 h2 h3 h4 h5 h7 hps' q.interior has' hbs' hst hsI hst' hsI' (hTd hs hs' hne)
      hKJ hK2 (hK s hs) (hK s' hs')
  set M := T.filter (fun m => ∀ s ∈ T, P m ⊆ P s → s = m) with hM
  have hMT : ∀ m ∈ M, m ∈ T := fun m hm => (Finset.mem_filter.mp hm).1
  have htM : t ∈ M := Finset.mem_filter.mpr ⟨ht, hmax⟩
  have hMdis : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint m m' ∧ Disjoint (P m) (P m') := by
    intro m hm m' hm' hne
    obtain ⟨hmT, hmm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmT', hmm'⟩ := Finset.mem_filter.mp hm'
    refine ⟨hTd hmT hmT' hne, ?_⟩
    rcases hnest m hmT m' hmT' hne with h | h | h
    · exact h
    · exact absurd (hmm m' hmT' h) (Ne.symm hne)
    · exact absurd (hmm' m hmT h) hne
  have hcl : ∀ s ∈ T, ∃ m ∈ M, s ⊆ closure (P m) := by
    intro s hs
    obtain ⟨B₀, hsB, hmx⟩ := Finset.exists_le_maximal (T.image P) (Finset.mem_image_of_mem P hs)
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmx.prop
    refine ⟨m, Finset.mem_filter.mpr ⟨hm, fun s' hs' hle => ?_⟩, ?_⟩
    · exact hinj s' hs' m hm (hmx.eq_of_le (Finset.mem_image_of_mem P hs') hle).symm
    · exact ((hp s hs).2.2.2.2.t_sub_closure_P h1 h2 h3 h4 h5 h7).trans (closure_mono hsB)
  -- the gap point `d`
  obtain ⟨d, ⟨hdCD, hdK⟩, hdM⟩ := exists_gap h1 h3 h4 h5 q M (F := Cb)
    (fun m hm => (hp m (hMT m hm)).2.2.2.2.hC.isClosed)
    (fun m hm m' hm' hne => by
      obtain ⟨has, hbs, hst, hsI, hps⟩ := hp m (hMT m hm)
      obtain ⟨has', hbs', hst', hsI', hps'⟩ := hp m' (hMT m' hm')
      exact hps.disj_C h1 h2 h3 h4 h5 h7 hps' q.interior has hbs has' hbs' hst hsI hst' hsI'
        (hMdis m hm m' hm' hne).1 (hMdis m hm m' hm' hne).2)
    (fun m hm => hK m (hMT m hm))
  have hdJ : d ∈ J := q.sCD_sub hdCD
  have hdP : ∀ m ∈ M, d ∉ closure (P m) := by
    intro m hm h
    obtain ⟨-, -, hmt, hmI, hpm⟩ := hp m (hMT m hm)
    rw [hpm.closure_P h1 h2 h3 h4 h5 h7] at h
    rcases h with h | h | h
    · exact disjoint_left.mp hIJ (hpm.P_sub h) hdJ
    · rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior hmI h hdJ with e | e
      · exact hdM m hm (e ▸ hpm.hC.left_mem)
      · exact hdM m hm (e ▸ hpm.hC.right_mem)
    · exact hdM m hm h
  -- the point `c` and the arc `u`
  obtain ⟨hta, htb, htt, htI, hpt⟩ := hp t ht
  obtain ⟨c, hc⟩ := htt.nonempty_diff
  have hcI : c ∈ I := htI hc
  have hca : c ≠ a t := fun e => hc.2 (Or.inl e)
  have hcb : c ≠ b t := fun e => hc.2 (Or.inr e)
  obtain ⟨u, hu, huW⟩ := outer_arc h1 h2 h3 h4 h5 h6 h7 h8 q.interior M
    (fun m hm => hp m (hMT m hm)) hMdis htM hc hdJ hdP
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓu, hΓi⟩ := htt.split hc.1 hca hcb
  have hΓ₁t : Γ₁ ⊆ t := hΓu ▸ subset_union_left
  have hΓ₂t : Γ₂ ⊆ t := hΓu ▸ subset_union_right
  have hut : ∀ z ∈ u, z ∈ t → z = c := by
    intro z hzu hzt
    by_contra hzc
    by_cases hzd : z = d
    · subst hzd; exact hdP t htM (hpt.t_sub_closure_P h1 h2 h3 h4 h5 h7 hzt)
    · have hz := huW ⟨hzu, by simp [hzc, hzd]⟩
      exact hz.2 (mem_iUnion₂.mpr ⟨t, htM, hpt.t_sub_closure_P h1 h2 h3 h4 h5 h7 hzt⟩)
  have hΓ₁u : Γ₁ ∩ u = {c} := subset_antisymm (fun z hz => hut z hz.2 (hΓ₁t hz.1))
    (by rintro z rfl; exact ⟨hΓ₁.right_mem, hu.left_mem⟩)
  have hx : TArc (a t) d (Γ₁ ∪ u) := hΓ₁.union hu hΓ₁u
  have hbΓ₁ : b t ∉ Γ₁ := fun h => hcb (Space.Quad.Cut.single h hΓ₂.right_mem hΓi).symm
  have haΓ₂ : a t ∉ Γ₂ := fun h => hca (Space.Quad.Cut.single hΓ₁.left_mem h hΓi).symm
  have hxI : (Γ₁ ∪ u) \ {a t, d} ⊆ I := by
    rintro z ⟨hz | hz, hzn⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzn
      exact htI ⟨hΓ₁t hz, by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨hzn.1, fun e => hbΓ₁ (e ▸ hz)⟩⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzn
      by_cases hzc : z = c
      · exact hzc ▸ hcI
      · exact (huW ⟨hz, by simp [hzc, hzn.2]⟩).1
  have hatK := hend t ht (a t) htt.left_mem hta
  have hbtK := hend t ht (b t) htt.right_mem htb
  have hxJ : ∀ z ∈ Γ₁ ∪ u, z ∈ J → z = a t ∨ z = d := by
    intro z hz hzJ
    by_contra hne
    simp only [not_or] at hne
    exact disjoint_left.mp hIJ (hxI ⟨hz, by simp [hne.1, hne.2]⟩) hzJ
  have hxq : σ.XArc I sAB sCD A B C D (Γ₁ ∪ u) := by
    refine ⟨a t, d, ⟨hat, ?_⟩, ⟨hdCD, hdK⟩, hx, hxI⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hatK ⊢
    exact ⟨hatK.1, hatK.2.1⟩
  obtain ⟨c0⟩ := q.exists_cut h1 h2 h3 h4 h5 h7 h8 hxq
  have hX : c0.X = a t := by
    have hXs : c0.X ∈ sAB := c0.s₁_sub (c0.hsi ▸ mem_singleton _ : c0.X ∈ c0.s₁ ∩ c0.s₂).1
    rcases hxJ _ c0.qA.bc.2.2.2.2.1 (q.sAB_sub hXs) with h | h
    · exact h
    · exact absurd (h ▸ hXs) (disjoint_right.mp q.ab_cd hdCD)
  have hX' : c0.X' = d := by
    have hXs : c0.X' ∈ sCD := c0.t₁_sub (c0.hti ▸ mem_singleton _ : c0.X' ∈ c0.t₁ ∩ c0.t₂).1
    rcases hxJ _ c0.qA.bc.2.2.2.2.2.1 (q.sCD_sub hXs) with h | h
    · exact absurd (h ▸ hXs) (disjoint_left.mp q.ab_cd hat)
    · exact h
  have hcx : c ∈ Γ₁ ∪ u := Or.inl hΓ₁.right_mem
  -- the other chords miss `x`
  have hdx : ∀ s ∈ T.erase t, Disjoint s (Γ₁ ∪ u) := by
    intro s hs
    obtain ⟨hst, hs⟩ := Finset.mem_erase.mp hs
    rw [disjoint_left]
    rintro z hzs (hz | hz)
    · exact disjoint_left.mp (hTd hs ht hst) hzs (hΓ₁t hz)
    · obtain ⟨m, hm, hsm⟩ := hcl s hs
      by_cases hzc : z = c
      · subst hzc; exact disjoint_left.mp (hTd hs ht hst) hzs hc.1
      by_cases hzd : z = d
      · subst hzd; exact hdP m hm (hsm hzs)
      · exact (huW ⟨hz, by simp [hzc, hzd]⟩).2 (mem_iUnion₂.mpr ⟨m, hm, hsm hzs⟩)
  -- the remaining piece `Γ₂` of `t`
  have hΓ₂I : Γ₂ \ {c, b t} ⊆ I \ (Γ₁ ∪ u) := by
    rintro z ⟨hz, hzn⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzn
    refine ⟨htI ⟨hΓ₂t hz, ?_⟩, ?_⟩
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => haΓ₂ (e ▸ hz), hzn.2⟩
    · rintro (hz' | hz')
      · exact hzn.1 (Space.Quad.Cut.single hz' hz hΓi)
      · exact hzn.1 (hut z hz' (hΓ₂t hz))
  have hbd : b t ≠ d := fun e => hdM t htM (e ▸ hpt.hC.right_mem)
  have hpiece := c0.chord_half h1 h2 h3 h4 h5 h7 hΓ₂ hΓ₂I (Or.inr hcx) (Or.inl htb)
    (by
      rw [hX, hX']
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨?_, ?_, ?_, ?_, hca, fun e => disjoint_left.mp hIJ hcI (e ▸ hdJ)⟩ <;>
        rintro rfl <;> exact disjoint_left.mp hIJ hcI (hKJ (by simp)))
    (by
      rw [hX, hX']
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hbtK ⊢
      exact ⟨hbtK.1, hbtK.2.1, hbtK.2.2.1, hbtK.2.2.2, htt.ne.symm, hbd⟩)
  obtain ⟨hA, hB, hwA, hwB, covA, covB⟩ :=
    c0.halves h1 h2 h3 h4 h5 h7 (T.erase t) (fun s hs => hT s (Finset.mem_of_mem_erase hs)) hdx
  have hΓ₂s : ∀ s ∈ T.erase t, Disjoint Γ₂ s := fun s hs =>
    (hTd ht (Finset.mem_of_mem_erase hs) (Finset.mem_erase.mp hs).1.symm).mono_left hΓ₂t
  have hΓ₂ne : ∀ s ∈ T.erase t, Γ₂ ≠ s := fun s hs e =>
    disjoint_left.mp (hΓ₂s s hs) hΓ₂.left_mem (e ▸ hΓ₂.left_mem)
  -- weights
  have hbx : b t ∉ Γ₁ ∪ u := fun h => by
    rcases hxJ _ h htb with e | e
    · exact htt.ne e.symm
    · exact hbd e
  have hΓ₂x : (Γ₂ ∩ (Γ₁ ∪ u)).Nonempty := ⟨c, hΓ₂.left_mem, hcx⟩
  have hbsides : b t ∈ sAB ∨ b t ∈ sBC ∨ b t ∈ sDA := by
    have := htb; rw [← q.union] at this
    rcases this with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (Or.inl ⟨⟨a t, htt.left_mem, hat⟩, ⟨b t, htt.right_mem, h⟩⟩) (hno t ht)
    · exact Or.inr (Or.inr h)
  have hw2 : 2 ≤ chordWeight sAB sBC sCD sDA t := chordWt_ge_two (hno t ht)
  have hw3 : b t ∈ sAB → chordWeight sAB sBC sCD sDA t = 3 := by
    intro hbAB
    have hmiss : ∀ {s : Set S}, s ⊆ J → (∀ z ∈ sAB, z ∈ s → z ∈ ({A, B, C, D} : Set S)) →
        ¬ (t ∩ s).Nonempty := by
      rintro s hsJ hs ⟨z, hzt, hzs⟩
      rcases chord_inter_J h1 h2 h3 h4 h5 h7 q.interior htI hzt (hsJ hzs) with rfl | rfl
      · exact hatK (hs _ hat hzs)
      · exact hbtK (hs _ hbAB hzs)
    have e1 := hmiss q.sBC_sub fun z hz hz' => by
      have : z ∈ sAB ∩ sBC := ⟨hz, hz'⟩
      rw [q.ab_bc] at this; rw [mem_singleton_iff.mp this]; simp
    have e2 := hmiss q.sCD_sub fun z hz hz' => absurd hz' (disjoint_left.mp q.ab_cd hz)
    have e3 := hmiss q.sDA_sub fun z hz hz' => by
      have : z ∈ sDA ∩ sAB := ⟨hz', hz⟩
      rw [q.da_ab] at this; rw [mem_singleton_iff.mp this]; simp
    simp only [chordWeight, eq_false e1, eq_false e2, eq_false e3]
    exact chordWt_eq_three
  have hltA : Γ₂ ⊆ c0.clA →
      chordWeight c0.s₁ (Γ₁ ∪ u) c0.t₁ sDA Γ₂ < chordWeight sAB sBC sCD sDA t := by
    intro hsub
    rcases hbsides with h | h | h
    · have hbs₁ : b t ∈ c0.s₁ := by
        rw [← c0.hs] at h
        rcases h with h | h
        · exact h
        · exact absurd (c0.inter_cl h1 h2 h3 h4 h51 h7 ⟨hsub hΓ₂.right_mem,
            Or.inr (Or.inl (Or.inl (Or.inl h)))⟩) hbx
      have := chordWt_le_two_ab (a := (Γ₂ ∩ c0.s₁).Nonempty) (b := (Γ₂ ∩ (Γ₁ ∪ u)).Nonempty)
        (c := (Γ₂ ∩ c0.t₁).Nonempty) (d := (Γ₂ ∩ sDA).Nonempty) ⟨b t, hΓ₂.right_mem, hbs₁⟩ hΓ₂x
      rw [hw3 h]; unfold chordWeight; omega
    · exfalso
      have := c0.closure_IA_disjoint_BC h1 h2 h3 h4 h51 h7
      rw [c0.closure_IA h1 h2 h3 h4 h51 h7] at this
      exact disjoint_left.mp this (hsub hΓ₂.right_mem) h
    · have := chordWt_eq_one (a := (Γ₂ ∩ c0.s₁).Nonempty) (b := (Γ₂ ∩ (Γ₁ ∪ u)).Nonempty)
        (c := (Γ₂ ∩ c0.t₁).Nonempty) (d := (Γ₂ ∩ sDA).Nonempty)
        (Or.inr ⟨hΓ₂x, ⟨b t, hΓ₂.right_mem, h⟩⟩)
      unfold chordWeight at hw2 ⊢; omega
  have hltB : Γ₂ ⊆ c0.clB →
      chordWeight c0.s₂ sBC c0.t₂ (Γ₁ ∪ u) Γ₂ < chordWeight sAB sBC sCD sDA t := by
    intro hsub
    rcases hbsides with h | h | h
    · have hbs₂ : b t ∈ c0.s₂ := by
        rw [← c0.hs] at h
        rcases h with h | h
        · exact absurd (c0.inter_cl h1 h2 h3 h4 h51 h7 ⟨Or.inr (Or.inl (Or.inl (Or.inl h))),
            hsub hΓ₂.right_mem⟩) hbx
        · exact h
      have := chordWt_le_two_ad (a := (Γ₂ ∩ c0.s₂).Nonempty) (b := (Γ₂ ∩ sBC).Nonempty)
        (c := (Γ₂ ∩ c0.t₂).Nonempty) (d := (Γ₂ ∩ (Γ₁ ∪ u)).Nonempty) ⟨b t, hΓ₂.right_mem, hbs₂⟩ hΓ₂x
      rw [hw3 h]; unfold chordWeight; omega
    · have := chordWt_eq_one (a := (Γ₂ ∩ c0.s₂).Nonempty) (b := (Γ₂ ∩ sBC).Nonempty)
        (c := (Γ₂ ∩ c0.t₂).Nonempty) (d := (Γ₂ ∩ (Γ₁ ∪ u)).Nonempty)
        (Or.inr ⟨⟨b t, hΓ₂.right_mem, h⟩, hΓ₂x⟩)
      unfold chordWeight at hw2 ⊢; omega
    · exfalso
      have := c0.closure_IB_disjoint_DA h1 h2 h3 h4 h51 h7
      rw [c0.closure_IB h1 h2 h3 h4 h51 h7] at this
      exact disjoint_left.mp this (hsub hΓ₂.right_mem) h
  have hdA := weightSum_sub_le ht (Finset.filter_subset (· ⊆ c0.clA) (T.erase t))
    (sAB := sAB) (sBC := sBC) (sCD := sCD) (sDA := sDA)
  have hdB := weightSum_sub_le ht (Finset.filter_subset (fun s => ¬ s ⊆ c0.clA) (T.erase t))
    (sAB := sAB) (sBC := sBC) (sCD := sCD) (sDA := sDA)
  have hwt : 1 ≤ chordWeight sAB sBC sCD sDA t := one_le_chordWt _ _ _ _
  have pd : ∀ U : Finset (Set S), U ⊆ T.erase t → (U : Set (Set S)).Pairwise Disjoint := fun U hU =>
    hTd.mono (Finset.coe_subset.mpr (hU.trans (Finset.erase_subset _ _)))
  have pdi : ∀ U : Finset (Set S), U ⊆ T.erase t →
      ((insert Γ₂ U : Finset (Set S)) : Set (Set S)).Pairwise Disjoint := fun U hU => by
    rw [Finset.coe_insert]
    exact (pd U hU).insert fun s hs _ => ⟨hΓ₂s s (hU hs), (hΓ₂s s (hU hs)).symm⟩
  have hnotin : ∀ U : Finset (Set S), U ⊆ T.erase t → Γ₂ ∉ U := fun U hU h => hΓ₂ne Γ₂ (hU h) rfl
  have tcov : ∀ {z : S}, z ∈ t → z ∉ Γ₁ ∪ u → z ∈ Γ₂ := fun {z} hzt hzx => by
    rw [← hΓu] at hzt
    exact hzt.resolve_left fun h => hzx (Or.inl h)
  rcases hpiece with ⟨hsubA, hchA⟩ | ⟨hsubB, hchB⟩
  · -- the piece is in the half `A`
    have RA := ih c0.qA (insert Γ₂ ((T.erase t).filter (· ⊆ c0.clA)))
      (fun s hs => by
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hchA
        · exact hA s hs)
      (pdi _ (Finset.filter_subset _ _)) (by
        rw [weightSum, Finset.sum_insert (hnotin _ (Finset.filter_subset _ _))]
        rw [weightSum] at hwA
        have := hltA hsubA
        omega)
    have RB := ih c0.qB _ (fun s hs => (hB s hs).2) (pd _ (Finset.filter_subset _ _))
      (by rw [hwB]; omega)
    refine c0.glue_chords h1 h2 h3 h4 h5 h6 h7 h8 hxq RA RB ?_ ?_
    · rintro y ⟨⟨s, hs, hys⟩, hyA⟩
      by_cases hst : s = t
      · subst hst
        exact ⟨Γ₂, Finset.mem_insert_self _ _, tcov hys (c0.IA_sub hyA).2⟩
      · obtain ⟨s', hs', hys'⟩ := covA ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyA⟩
        exact ⟨s', Finset.mem_insert_of_mem hs', hys'⟩
    · rintro y ⟨⟨s, hs, hys⟩, hyB⟩
      by_cases hst : s = t
      · subst hst
        exact absurd hyB (disjoint_left.mp (c0.clA_disj_IB h1 h2 h3 h4 h5 h7 hsubA)
          (tcov hys (c0.IB_sub hyB).2))
      · exact covB ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyB⟩
  · -- the piece is in the half `B`
    have RA := ih c0.qA _ hA (pd _ (Finset.filter_subset _ _)) (by rw [hwA]; omega)
    have RB := ih c0.qB (insert Γ₂ ((T.erase t).filter (fun s => ¬ s ⊆ c0.clA)))
      (fun s hs => by
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hchB
        · exact (hB s hs).2)
      (pdi _ (Finset.filter_subset _ _)) (by
        rw [weightSum, Finset.sum_insert (hnotin _ (Finset.filter_subset _ _))]
        rw [weightSum] at hwB
        have := hltB hsubB
        omega)
    refine c0.glue_chords h1 h2 h3 h4 h5 h6 h7 h8 hxq RA RB ?_ ?_
    · rintro y ⟨⟨s, hs, hys⟩, hyA⟩
      by_cases hst : s = t
      · subst hst
        exact absurd hyA (disjoint_left.mp (c0.clB_disj_IA h1 h2 h3 h4 h5 h7 hsubB)
          (tcov hys (c0.IA_sub hyA).2))
      · exact covA ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyA⟩
    · rintro y ⟨⟨s, hs, hys⟩, hyB⟩
      by_cases hst : s = t
      · subst hst
        exact ⟨Γ₂, Finset.mem_insert_self _ _, tcov hys (c0.IB_sub hyB).2⟩
      · obtain ⟨s', hs', hys'⟩ := covB ⟨⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hys⟩, hyB⟩
        exact ⟨s', Finset.mem_insert_of_mem hs', hys'⟩

end Absorb

section Main

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

theorem chordsBelow (n : ℕ) : ChordsBelow σ n := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro J I A B C D sAB sBC sCD sDA q T hT hTd hW
    letI := σ.topology
    have h51 := axiom5₁_of_axiom5 h5
    have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
    have e1 : ({B, C, D, A} : Set S) = {A, B, C, D} := by
      ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    have e2 : ({C, D, A, B} : Set S) = {A, B, C, D} := by
      ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    have e3 : ({D, A, B, C} : Set S) = {A, B, C, D} := by
      ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    rcases T.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
    · exact q.rulable_of_good h1 h2 h3 h4 h5 h7 (by simp)
    by_cases hopp : ∃ t ∈ T, ((t ∩ sAB).Nonempty ∧ (t ∩ sCD).Nonempty) ∨
        ((t ∩ sBC).Nonempty ∧ (t ∩ sDA).Nonempty)
    · obtain ⟨t, ht, h | h⟩ := hopp
      · exact opp_step h1 h2 h3 h4 h5 h6 h7 h8 ih q T hT hTd hW ht h.1 h.2
      · exact Space.Rulable.of_rot h1 (opp_step h1 h2 h3 h4 h5 h6 h7 h8 ih q.rot T
          (fun t ht => (hT t ht).rot) hTd (by rw [weightSum_rot]; exact hW) ht h.1 h.2)
    have hno : ∀ t ∈ T, ¬ (((t ∩ sAB).Nonempty ∧ (t ∩ sCD).Nonempty) ∨
        ((t ∩ sBC).Nonempty ∧ (t ∩ sDA).Nonempty)) := fun t ht h => hopp ⟨t, ht, h⟩
    obtain ⟨p₀, -⟩ := hT t₀ ht₀
    have hch : ∀ t : Set S, ∃ a b : S, ∃ C₀ C' P Q : Set S, t ∈ T →
        σ.ChordPocket J I t a b C₀ C' P Q ∧ (({A, B, C, D} : Set S) ∩ C₀).Subsingleton := by
      intro t
      by_cases ht : t ∈ T
      · obtain ⟨a, b, C₀, C', P, Q, h, hK⟩ :=
          pocket_of_not_opp h1 h2 h3 h4 h5 h7 h8 q (hT t ht) (hno t ht)
        exact ⟨a, b, C₀, C', P, Q, fun _ => ⟨h, hK⟩⟩
      · exact ⟨p₀, p₀, ∅, ∅, ∅, ∅, fun h => absurd h ht⟩
    choose a b Cb C' P Q hpq using hch
    have hp := fun t ht => (hpq t ht).1
    have hK := fun t ht => (hpq t ht).2
    -- a chord with a maximal pocket
    have hinj : ∀ s ∈ T, ∀ s' ∈ T, P s = P s' → s = s' := by
      intro s hs s' hs' he
      by_contra hne
      obtain ⟨-, -, hst, hsI, hps⟩ := hp s hs
      obtain ⟨-, -, -, -, hps'⟩ := hp s' hs'
      obtain ⟨y, hy⟩ := hst.nonempty_diff
      have hy' : y ∈ s' ∪ Cb s' := by
        rw [← hps'.frontier_P h1 h2 h3 h4 h5 h7, ← he, hps.frontier_P h1 h2 h3 h4 h5 h7]
        exact Or.inl hy.1
      rcases hy' with h | h
      · exact disjoint_left.mp (hTd hs hs' hne) hy.1 h
      · exact disjoint_left.mp hIJ (hsI hy) (hps'.C_sub h)
    obtain ⟨B₀, -, hmx⟩ := Finset.exists_le_maximal (T.image P) (Finset.mem_image_of_mem P ht₀)
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmx.prop
    have hmax : ∀ s ∈ T, P t ⊆ P s → s = t := fun s hs hle =>
      hinj s hs t ht (hmx.eq_of_le (Finset.mem_image_of_mem P hs) hle).symm
    have hat : a t ∈ J := (hp t ht).1
    rw [← q.union] at hat
    rcases hat with ((h | h) | h) | h
    · exact absorb_step h1 h2 h3 h4 h5 h6 h7 h8 ih q T hT hTd hW hno hp hK ht hmax h
    · refine Space.Rulable.of_rot h1 (absorb_step h1 h2 h3 h4 h5 h6 h7 h8 ih q.rot T
        (fun t ht => (hT t ht).rot) hTd (by rw [weightSum_rot]; exact hW) (fun t ht h' => ?_) hp
        (fun t ht => by rw [e1]; exact hK t ht) ht hmax h)
      exact hno t ht (by tauto)
    · refine Space.Rulable.of_rot h1 (Space.Rulable.of_rot h1 (absorb_step h1 h2 h3 h4 h5 h6 h7 h8
        ih q.rot.rot T (fun t ht => (hT t ht).rot.rot) hTd
        (by rw [weightSum_rot, weightSum_rot]; exact hW) (fun t ht h' => ?_) hp
        (fun t ht => by rw [e2]; exact hK t ht) ht hmax h))
      exact hno t ht (by tauto)
    · refine Space.Rulable.of_rot h1 (Space.Rulable.of_rot h1 (Space.Rulable.of_rot h1
        (absorb_step h1 h2 h3 h4 h5 h6 h7 h8 ih q.rot.rot.rot T (fun t ht => (hT t ht).rot.rot.rot)
        hTd (by rw [weightSum_rot, weightSum_rot, weightSum_rot]; exact hW) (fun t ht h' => ?_) hp
        (fun t ht => by rw [e3]; exact hK t ht) ht hmax h)))
      exact hno t ht (by tauto)

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Chords in the carrier.** For a finite set of mutually exclusive chords of `ABCDA` there is a
ruling none of whose subdivisions meets any of the chords. -/
theorem chords_rulable (q : σ.Quad J I A B C D sAB sBC sCD sDA) {T : Set (Set S)}
    (hT : T.Finite) (hc : ∀ t ∈ T, σ.IsChord J I A B C D t) (hd : T.Pairwise Disjoint) :
    σ.Rulable (fun U => Disjoint U (⋃₀ T)) I sAB sBC sCD sDA A B C D := by
  have := chordsBelow h1 h2 h3 h4 h5 h6 h7 h8 _ q hT.toFinset (fun t ht => hc t (by simpa using ht))
    (by simpa using hd) (Nat.lt_succ_self _)
  simpa using this

end Main

end HPC.Moore
