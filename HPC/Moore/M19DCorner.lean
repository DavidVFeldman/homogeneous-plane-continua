import HPC.Moore.M19DWeight

/-!
# Moore 1919, Theorem D: the base of a chord not joining opposite sides

A chord of `ABCDA` whose ends are not on opposite sides has a pocket whose base (an arc of `ABCDA`)
contains at most one of the vertices `A, B, C, D` (`pocket_of_not_opp`). If finitely many such bases
are mutually exclusive, some point of the open side `CD` lies on none of them (`exists_gap`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A preconnected set covered by finitely many mutually exclusive closed sets lies in one. -/
theorem IsPreconnected.subset_of_finite_closed [TopologicalSpace S] {O : Set S}
    (hO : IsPreconnected O) (hne : O.Nonempty) {ι : Type*} (M : Finset ι) {F : ι → Set S}
    (hF : ∀ m ∈ M, IsClosed (F m)) (hdis : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint (F m) (F m'))
    (hsub : O ⊆ ⋃ m ∈ M, F m) : ∃ m ∈ M, O ⊆ F m := by
  classical
  induction M using Finset.induction_on with
  | empty => obtain ⟨z, hz⟩ := hne; simpa using hsub hz
  | insert m₀ M hm₀ ih =>
    have hsub' : O ⊆ F m₀ ∪ ⋃ m ∈ M, F m := by
      intro z hz; have := hsub hz
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at this; exact this
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hO _ _ (hF m₀ (Finset.mem_insert_self _ _))
      (M.finite_toSet.isClosed_biUnion fun m hm => hF m (Finset.mem_insert_of_mem hm)) hsub' (by
        rw [eq_empty_iff_forall_notMem]
        rintro z ⟨-, hz₀, hz⟩
        obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
        exact disjoint_left.mp (hdis m₀ (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm)
          (fun h => hm₀ (h ▸ hm))) hz₀ hzm) with h | h
    · exact ⟨m₀, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨m, hm, hOm⟩ := ih (fun m hm => hF m (Finset.mem_insert_of_mem hm))
        (fun m hm m' hm' => hdis m (Finset.mem_insert_of_mem hm) m' (Finset.mem_insert_of_mem hm')) h
      exact ⟨m, Finset.mem_insert_of_mem hm, hOm⟩

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

omit h2 h7 h8 in
/-- **A gap on the side `CD`**: if the bases are mutually exclusive closed sets each containing at
most one vertex, some point of the open side `CD` lies on none of them. -/
theorem exists_gap (q : σ.Quad J I A B C D sAB sBC sCD sDA) {ι : Type*} (M : Finset ι)
    {F : ι → Set S} (hF : ∀ m ∈ M, @IsClosed S σ.topology (F m))
    (hdis : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint (F m) (F m'))
    (hK : ∀ m ∈ M, (({A, B, C, D} : Set S) ∩ F m).Subsingleton) :
    ∃ d ∈ sCD \ {C, D}, ∀ m ∈ M, d ∉ F m := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have hcd := (isArc_iff_tarc h1 h3 h4 h51).mp q.cd
  by_contra hno
  push_neg at hno
  obtain ⟨m, hm, hsub⟩ := IsPreconnected.subset_of_finite_closed hcd.isPreconnected_diff hcd.nonempty_diff M hF hdis
    fun d hd => by obtain ⟨m, hm, h⟩ := hno d hd; exact mem_iUnion₂.mpr ⟨m, hm, h⟩
  have hcl : sCD ⊆ F m := hcd.subset_closure_diff.trans (closure_minimal hsub (hF m hm))
  exact hcd.ne (hK m hm ⟨by simp, hcl hcd.left_mem⟩ ⟨by simp, hcl hcd.right_mem⟩)

omit h8 in
/-- A pocket with a prescribed base. -/
theorem exists_pocket_of_base (hJI : σ.IsInteriorOf J I) {a b : S} {t L : Set S} (ha : a ∈ J)
    (hb : b ∈ J) (ht : @TArc S σ.topology a b t) (htI : t \ {a, b} ⊆ I)
    (hL : @TArc S σ.topology a b L) (hLJ : L ⊆ J) (h8 : σ.Axiom8) :
    ∃ C' P Q, σ.Pocket J I t a b L C' P Q := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJI.1 ha hb ht.ne
  have hLa := (isArc_iff_tarc h1 h3 h4 h51).mpr hL
  rcases arc_eq_of_subset_union h1 h3 h4 h51 hC₁ hC₂ hCi (hCu ▸ hLJ) hLa with rfl | rfl
  · rw [isArc_iff_tarc h1 h3 h4 h51] at hC₁ hC₂
    obtain ⟨P, Q, hP, hQ, hsplit, hdis⟩ :=
      split_interior_of h1 h2 h3 h4 h5 h7 h8 hJI hC₁ hC₂ hCi hCu ht htI
    exact ⟨C₂, P, Q, hC₁, hC₂, hCi, hCu, hP, hQ, hsplit, hdis⟩
  · rw [isArc_iff_tarc h1 h3 h4 h51] at hC₁ hC₂
    obtain ⟨P, Q, hP, hQ, hsplit, hdis⟩ :=
      split_interior_of h1 h2 h3 h4 h5 h7 h8 hJI hC₂ hC₁ (by rw [inter_comm]; exact hCi)
        (by rw [union_comm]; exact hCu) ht htI
    exact ⟨C₁, P, Q, hC₂, hC₁, by rw [inter_comm]; exact hCi, by rw [union_comm]; exact hCu, hP, hQ,
      hsplit, hdis⟩

/-- A chord with both ends on the sides `AB`, `BC` has a pocket whose base contains no vertex but
`B`. -/
theorem pocket_adjacent (q : σ.Quad J I A B C D sAB sBC sCD sDA) {a b : S} {t : Set S}
    (ha : a ∈ sAB ∪ sBC) (hb : b ∈ sAB ∪ sBC) (haK : a ∉ ({A, B, C, D} : Set S))
    (hbK : b ∉ ({A, B, C, D} : Set S)) (ht : @TArc S σ.topology a b t) (htI : t \ {a, b} ⊆ I) :
    ∃ C₀ C' P Q, σ.Pocket J I t a b C₀ C' P Q ∧ (({A, B, C, D} : Set S) ∩ C₀).Subsingleton := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have hab := (isArc_iff_tarc h1 h3 h4 h51).mp q.ab
  have hbc := (isArc_iff_tarc h1 h3 h4 h51).mp q.bc
  have hL : TArc A C (sAB ∪ sBC) := hab.union hbc q.ab_bc
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at haK hbK
  obtain ⟨L, hLsub, hLt, hAL, hCL⟩ := hL.sub_avoid ha hb haK.1 haK.2.2.1 hbK.1 hbK.2.2.1 ht.ne
  have hLJ : L ⊆ J := hLsub.trans (union_subset q.sAB_sub q.sBC_sub)
  obtain ⟨C', P, Q, hp⟩ := exists_pocket_of_base h1 h2 h3 h4 h5 h7 q.interior
    (hLJ hLt.left_mem) (hLJ hLt.right_mem) ht htI hLt hLJ h8
  refine ⟨L, C', P, Q, hp, ?_⟩
  have hsub : ({A, B, C, D} : Set S) ∩ L ⊆ {B} := by
    rintro z ⟨hz, hzL⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact absurd hzL hAL
    · rfl
    · exact absurd hzL hCL
    · exfalso
      rcases hLsub hzL with h | h
      · exact disjoint_left.mp q.ab_cd h ((isArc_iff_tarc h1 h3 h4 h51).mp q.cd).right_mem
      · exact disjoint_left.mp q.bc_da h ((isArc_iff_tarc h1 h3 h4 h51).mp q.da).left_mem
  exact subsingleton_singleton.anti hsub

/-- **A chord not joining opposite sides** has a pocket whose base contains at most one vertex. -/
theorem pocket_of_not_opp (q : σ.Quad J I A B C D sAB sBC sCD sDA) {t : Set S}
    (ht : σ.IsChord J I A B C D t)
    (hno : ¬ (((t ∩ sAB).Nonempty ∧ (t ∩ sCD).Nonempty) ∨
      ((t ∩ sBC).Nonempty ∧ (t ∩ sDA).Nonempty))) :
    ∃ a b C₀ C' P Q, σ.ChordPocket J I t a b C₀ C' P Q ∧
      (({A, B, C, D} : Set S) ∩ C₀).Subsingleton := by
  letI := σ.topology
  obtain ⟨a, b, ⟨haJ, haK⟩, ⟨hbJ, hbK⟩, htt, htI⟩ := ht
  have e1 : ({B, C, D, A} : Set S) = {A, B, C, D} := by
    ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have e2 : ({C, D, A, B} : Set S) = {A, B, C, D} := by
    ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have e3 : ({D, A, B, C} : Set S) = {A, B, C, D} := by
    ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  suffices H : ∃ C₀ C' P Q, σ.Pocket J I t a b C₀ C' P Q ∧
      (({A, B, C, D} : Set S) ∩ C₀).Subsingleton by
    obtain ⟨C₀, C', P, Q, hp, hK⟩ := H
    exact ⟨a, b, C₀, C', P, Q, ⟨haJ, hbJ, htt, htI, hp⟩, hK⟩
  have hsides : ∀ {z : S}, z ∈ J → z ∈ sAB ∨ z ∈ sBC ∨ z ∈ sCD ∨ z ∈ sDA := by
    intro z hz; rw [← q.union] at hz
    rcases hz with ((h | h) | h) | h <;> tauto
  have hat : a ∈ t := htt.left_mem
  have hbt : b ∈ t := htt.right_mem
  have P0 := fun ha hb => pocket_adjacent h1 h2 h3 h4 h5 h7 h8 q ha hb haK hbK htt htI
  have P1 := fun ha hb => pocket_adjacent h1 h2 h3 h4 h5 h7 h8 q.rot ha hb (e1 ▸ haK) (e1 ▸ hbK)
    htt htI
  have P2 := fun ha hb => pocket_adjacent h1 h2 h3 h4 h5 h7 h8 q.rot.rot ha hb (e2 ▸ haK)
    (e2 ▸ hbK) htt htI
  have P3 := fun ha hb => pocket_adjacent h1 h2 h3 h4 h5 h7 h8 q.rot.rot.rot ha hb (e3 ▸ haK)
    (e3 ▸ hbK) htt htI
  rw [e1] at P1; rw [e2] at P2; rw [e3] at P3
  rcases hsides haJ with ha | ha | ha | ha <;> rcases hsides hbJ with hb | hb | hb | hb
  · exact P0 (Or.inl ha) (Or.inl hb)
  · exact P0 (Or.inl ha) (Or.inr hb)
  · exact absurd (Or.inl ⟨⟨a, hat, ha⟩, ⟨b, hbt, hb⟩⟩) hno
  · exact P3 (Or.inr ha) (Or.inl hb)
  · exact P0 (Or.inr ha) (Or.inl hb)
  · exact P1 (Or.inl ha) (Or.inl hb)
  · exact P1 (Or.inl ha) (Or.inr hb)
  · exact absurd (Or.inr ⟨⟨a, hat, ha⟩, ⟨b, hbt, hb⟩⟩) hno
  · exact absurd (Or.inl ⟨⟨b, hbt, hb⟩, ⟨a, hat, ha⟩⟩) hno
  · exact P1 (Or.inr ha) (Or.inl hb)
  · exact P2 (Or.inl ha) (Or.inl hb)
  · exact P2 (Or.inl ha) (Or.inr hb)
  · exact P3 (Or.inl ha) (Or.inr hb)
  · exact absurd (Or.inr ⟨⟨b, hbt, hb⟩, ⟨a, hat, ha⟩⟩) hno
  · exact P2 (Or.inr ha) (Or.inl hb)
  · exact P3 (Or.inl ha) (Or.inl hb)

end Ax

end HPC.Moore
