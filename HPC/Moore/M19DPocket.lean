import HPC.Moore.M19DDefs

/-!
# Moore 1919, Theorem D: pockets of chords

A chord `t` (ends `a`, `b`) of the closed curve `J` with interior `I` divides `I` into the interiors
`P` and `Q` of `t + C` and `t + C′`, where `C`, `C′` are the two arcs of `J` from `a` to `b`
(`Space.Pocket`, `exists_pocket`). Near a point of `C` other than `a`, `b`, the points of `I` are in
`P` (`Space.Pocket.local_P`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- The chord `t` from `a` to `b` of `J` divides `I` into the interior `P` of `t + C` and the interior
`Q` of `t + C′`, where `C`, `C′` are the arcs of `J` from `a` to `b`. -/
structure Space.Pocket (σ : Space S) (J I t : Set S) (a b : S) (C C' P Q : Set S) : Prop where
  hC : @TArc S σ.topology a b C
  hC' : @TArc S σ.topology a b C'
  hCi : C ∩ C' = {a, b}
  hCu : C ∪ C' = J
  hP : σ.IsInteriorOf (t ∪ C) P
  hQ : σ.IsInteriorOf (t ∪ C') Q
  split : I \ t = P ∪ Q
  dis : Disjoint P Q

namespace Space.Pocket

variable {J I t : Set S} {a b : S} {C C' P Q : Set S}

theorem swap (h : σ.Pocket J I t a b C C' P Q) : σ.Pocket J I t a b C' C Q P where
  hC := h.hC'
  hC' := h.hC
  hCi := by rw [inter_comm]; exact h.hCi
  hCu := by rw [union_comm]; exact h.hCu
  hP := h.hQ
  hQ := h.hP
  split := by rw [union_comm]; exact h.split
  dis := h.dis.symm

theorem P_sub (h : σ.Pocket J I t a b C C' P Q) : P ⊆ I :=
  fun _ hz => (h.split.symm ▸ (Or.inl hz : _ ∈ P ∪ Q) : _ ∈ I \ t).1

theorem Q_sub (h : σ.Pocket J I t a b C C' P Q) : Q ⊆ I := h.swap.P_sub

theorem P_disj_t (h : σ.Pocket J I t a b C C' P Q) : Disjoint P t :=
  disjoint_left.mpr fun _ hz => (h.split.symm ▸ (Or.inl hz : _ ∈ P ∪ Q) : _ ∈ I \ t).2

theorem C_sub (h : σ.Pocket J I t a b C C' P Q) : C ⊆ J := h.hCu ▸ subset_union_left

theorem C'_sub (h : σ.Pocket J I t a b C C' P Q) : C' ⊆ J := h.hCu ▸ subset_union_right

end Space.Pocket

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I t : Set S} {a b : S}

omit h6 in
/-- Every chord divides the interior into two pockets. -/
theorem exists_pocket (hJI : σ.IsInteriorOf J I) (ha : a ∈ J) (hb : b ∈ J)
    (ht : @TArc S σ.topology a b t) (htI : t \ {a, b} ⊆ I) :
    ∃ C C' P Q, σ.Pocket J I t a b C C' P Q := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨C, C', hC, hC', hCi, hCu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJI.1 ha hb ht.ne
  rw [isArc_iff_tarc h1 h3 h4 h51] at hC hC'
  obtain ⟨P, Q, hP, hQ, hsplit, hdis⟩ :=
    split_interior_of h1 h2 h3 h4 h5 h7 h8 hJI hC hC' hCi hCu ht htI
  exact ⟨C, C', P, Q, hC, hC', hCi, hCu, hP, hQ, hsplit, hdis⟩

omit h6 h8 in
theorem chord_inter_J (hJI : σ.IsInteriorOf J I) (htI : t \ {a, b} ⊆ I) {z : S} (hzt : z ∈ t)
    (hzJ : z ∈ J) : z = a ∨ z = b := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ, -⟩ := jordan h1 h2 h3 h4 h51 h7 hJI
  by_contra hne
  simp only [not_or] at hne
  exact disjoint_left.mp hIJ (htI ⟨hzt, by simp [hne.1, hne.2]⟩) hzJ

namespace Space.Pocket

variable {C C' P Q : Set S}

omit h6 h8 in
theorem closure_P (h : σ.Pocket J I t a b C C' P Q) :
    @closure S σ.topology P = P ∪ (t ∪ C) :=
  (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 h.hP).2.2.2.2.2.2.2.2.1

omit h6 h8 in
theorem frontier_P (h : σ.Pocket J I t a b C C' P Q) :
    @frontier S σ.topology P = t ∪ C :=
  (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 h.hP).2.2.2.1

omit h6 h8 in
theorem isOpen_P (h : σ.Pocket J I t a b C C' P Q) : @IsOpen S σ.topology P :=
  (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 h.hP).1

omit h6 h8 in
theorem isPreconnected_P (h : σ.Pocket J I t a b C C' P Q) : @IsPreconnected S σ.topology P :=
  (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 h.hP).2.1

omit h6 h8 in
theorem t_sub_closure_P (h : σ.Pocket J I t a b C C' P Q) : t ⊆ @closure S σ.topology P := by
  rw [h.closure_P h1 h2 h3 h4 h5 h7]; exact fun z hz => Or.inr (Or.inl hz)

omit h6 h8 in
theorem C_sub_closure_P (h : σ.Pocket J I t a b C C' P Q) : C ⊆ @closure S σ.topology P := by
  rw [h.closure_P h1 h2 h3 h4 h5 h7]; exact fun z hz => Or.inr (Or.inr hz)

omit h6 h8 in
/-- A connected subset of `I − t` lies in one pocket. -/
theorem conn (h : σ.Pocket J I t a b C C' P Q) {Z : Set S} (hZ : @IsPreconnected S σ.topology Z)
    (hZI : Z ⊆ I \ t) : Z ⊆ P ∨ Z ⊆ Q := by
  letI := σ.topology
  rw [h.split] at hZI
  exact hZ.subset_or_subset (h.isOpen_P h1 h2 h3 h4 h5 h7) (h.swap.isOpen_P h1 h2 h3 h4 h5 h7)
    h.dis hZI

omit h6 h8 in
/-- Near a point of `C` other than its ends, the points of `I` are in `P`. -/
theorem local_P (h : σ.Pocket J I t a b C C' P Q) (hJI : σ.IsInteriorOf J I)
    (htI : t \ {a, b} ⊆ I) {z : S} (hz : z ∈ C \ {a, b}) :
    ∃ N ∈ @nhds S σ.topology z, N ∩ I ⊆ P := by
  letI := σ.topology
  have hzQ : z ∉ closure Q := by
    rw [h.swap.closure_P h1 h2 h3 h4 h5 h7]
    rintro (hzQ | hzt | hzC')
    · exact disjoint_left.mp (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hJI).2.2.2.2.2.2.2.2.2.1
        (h.Q_sub hzQ) (h.C_sub hz.1)
    · exact hz.2 (by rcases chord_inter_J h1 h2 h3 h4 h5 h7 hJI htI hzt (h.C_sub hz.1) with e | e
                     <;> simp [e])
    · exact hz.2 (h.hCi ▸ ⟨hz.1, hzC'⟩)
  refine ⟨(closure Q)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hzQ, ?_⟩
  rintro y ⟨hyQ, hyI⟩
  by_cases hyt : y ∈ t
  · exact absurd (h.swap.t_sub_closure_P h1 h2 h3 h4 h5 h7 hyt) hyQ
  · have : y ∈ P ∪ Q := h.split ▸ ⟨hyI, hyt⟩
    rcases this with hy | hy
    · exact hy
    · exact absurd (subset_closure hy) hyQ

end Space.Pocket

end Ax

theorem nonempty_inter_of_mem_closure [TopologicalSpace S] {U V : Set S} (hU : IsOpen U) {y : S}
    (hyU : y ∈ U) (hyV : y ∈ closure V) : (U ∩ V).Nonempty :=
  mem_closure_iff.mp hyV U hU hyU

section Two

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {J I s t : Set S} {a b a' b' : S} {Cs Cs' Ps Qs Ct Ct' Pt Qt : Set S}

/-- The open arc of a chord `t` disjoint from the chord `s` lies in one pocket of `s`. -/
theorem Space.Pocket.side (hs : σ.Pocket J I s a b Cs Cs' Ps Qs)
    (ht : @TArc S σ.topology a' b' t) (htI : t \ {a', b'} ⊆ I) (hst : Disjoint s t) :
    t \ {a', b'} ⊆ Ps ∨ t \ {a', b'} ⊆ Qs := by
  letI := σ.topology
  exact hs.conn h1 h2 h3 h4 h5 h7 ht.isPreconnected_diff fun z hz =>
    ⟨htI hz, fun hzs => disjoint_left.mp hst hzs hz.1⟩

theorem Space.Pocket.diff_sub_closure (ht : σ.Pocket J I t a' b' Ct Ct' Pt Qt) :
    t \ {a', b'} ⊆ @closure S σ.topology Pt :=
  fun _ hz => ht.t_sub_closure_P h1 h2 h3 h4 h5 h7 hz.1

/-- **Two pockets with no common point.** -/
theorem Space.Pocket.disj_facts (hs : σ.Pocket J I s a b Cs Cs' Ps Qs)
    (ht : σ.Pocket J I t a' b' Ct Ct' Pt Qt) (hJI : σ.IsInteriorOf J I) (ha : a ∈ J) (hb : b ∈ J)
    (ha' : a' ∈ J) (hb' : b' ∈ J) (hss : @TArc S σ.topology a b s) (hsI : s \ {a, b} ⊆ I)
    (htt : @TArc S σ.topology a' b' t) (htI : t \ {a', b'} ⊆ I) (hst : Disjoint s t)
    (hPP : Disjoint Ps Pt) :
    t \ {a', b'} ⊆ Qs ∧ Disjoint Ps (@closure S σ.topology Pt) ∧
      a' ∉ @closure S σ.topology Ps ∧ b' ∉ @closure S σ.topology Ps := by
  letI := σ.topology
  have hIJ := (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hJI).2.2.2.2.2.2.2.2.2.1
  have hi : t \ {a', b'} ⊆ Qs := by
    rcases hs.side h1 h2 h3 h4 h5 h7 htt htI hst with h | h
    · obtain ⟨y, hy⟩ := htt.nonempty_diff
      obtain ⟨z, hzs, hzt⟩ := nonempty_inter_of_mem_closure (hs.isOpen_P h1 h2 h3 h4 h5 h7) (h hy)
        (ht.diff_sub_closure h1 h2 h3 h4 h5 h7 hy)
      exact absurd hzt (disjoint_left.mp hPP hzs)
    · exact h
  have hend : ∀ {e : S}, e ∈ t → e ∈ J → e ∉ closure Ps := by
    intro e het heJ he
    rw [hs.closure_P h1 h2 h3 h4 h5 h7] at he
    rcases he with heP | hes | heC
    · exact disjoint_left.mp hIJ (hs.P_sub heP) heJ
    · exact disjoint_left.mp hst hes het
    · have hne : e ∉ ({a, b} : Set S) := by
        rintro (rfl | rfl)
        · exact disjoint_left.mp hst hss.left_mem het
        · exact disjoint_left.mp hst hss.right_mem het
      obtain ⟨N, hN, hNP⟩ := hs.local_P h1 h2 h3 h4 h5 h7 hJI hsI ⟨heC, hne⟩
      obtain ⟨y, hyN, hyP⟩ := mem_closure_iff_nhds.mp (ht.t_sub_closure_P h1 h2 h3 h4 h5 h7 het) N hN
      exact disjoint_left.mp hPP (hNP ⟨hyN, ht.P_sub hyP⟩) hyP
  refine ⟨hi, ?_, hend htt.left_mem ha', hend htt.right_mem hb'⟩
  rw [disjoint_left]
  intro z hzP hz
  rw [ht.closure_P h1 h2 h3 h4 h5 h7] at hz
  rcases hz with hzP' | hzt | hzC
  · exact disjoint_left.mp hPP hzP hzP'
  · have hzI := hs.P_sub hzP
    have hz' : z ∈ t \ {a', b'} := ⟨hzt, by
      rintro (rfl | rfl)
      · exact disjoint_left.mp hIJ hzI ha'
      · exact disjoint_left.mp hIJ hzI hb'⟩
    exact disjoint_left.mp hs.dis hzP (hi hz')
  · exact disjoint_left.mp hIJ (hs.P_sub hzP) (ht.C_sub hzC)

/-- Two pockets with no common point have mutually exclusive bases. -/
theorem Space.Pocket.disj_C (hs : σ.Pocket J I s a b Cs Cs' Ps Qs)
    (ht : σ.Pocket J I t a' b' Ct Ct' Pt Qt) (hJI : σ.IsInteriorOf J I) (ha : a ∈ J) (hb : b ∈ J)
    (ha' : a' ∈ J) (hb' : b' ∈ J) (hss : @TArc S σ.topology a b s) (hsI : s \ {a, b} ⊆ I)
    (htt : @TArc S σ.topology a' b' t) (htI : t \ {a', b'} ⊆ I) (hst : Disjoint s t)
    (hPP : Disjoint Ps Pt) : Disjoint Cs Ct := by
  letI := σ.topology
  obtain ⟨-, -, ha'P, hb'P⟩ := hs.disj_facts h1 h2 h3 h4 h5 h7 ht hJI ha hb ha' hb' hss hsI htt htI
    hst hPP
  obtain ⟨-, -, haP, hbP⟩ := ht.disj_facts h1 h2 h3 h4 h5 h7 hs hJI ha' hb' ha hb htt htI hss hsI
    hst.symm hPP.symm
  rw [disjoint_left]
  intro z hzs hzt
  have hzs' : z ∉ ({a, b} : Set S) := by
    rintro (rfl | rfl)
    · exact haP (ht.C_sub_closure_P h1 h2 h3 h4 h5 h7 hzt)
    · exact hbP (ht.C_sub_closure_P h1 h2 h3 h4 h5 h7 hzt)
  have hzt' : z ∉ ({a', b'} : Set S) := by
    rintro (rfl | rfl)
    · exact ha'P (hs.C_sub_closure_P h1 h2 h3 h4 h5 h7 hzs)
    · exact hb'P (hs.C_sub_closure_P h1 h2 h3 h4 h5 h7 hzs)
  obtain ⟨N₁, hN₁, hP₁⟩ := hs.local_P h1 h2 h3 h4 h5 h7 hJI hsI ⟨hzs, hzs'⟩
  obtain ⟨N₂, hN₂, hP₂⟩ := ht.local_P h1 h2 h3 h4 h5 h7 hJI htI ⟨hzt, hzt'⟩
  have hzcl : z ∈ closure I := by
    rw [(jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hJI).2.2.2.2.2.2.2.2.1]
    exact Or.inr (hs.C_sub hzs)
  obtain ⟨y, hyN, hyI⟩ := mem_closure_iff_nhds.mp hzcl (N₁ ∩ N₂) (Filter.inter_mem hN₁ hN₂)
  exact disjoint_left.mp hPP (hP₁ ⟨hyN.1, hyI⟩) (hP₂ ⟨hyN.2, hyI⟩)

/-- **Pockets are nested or exclusive**, when each base contains at most one point of a set `K` of
at least three points of `J` (the corners). -/
theorem Space.Pocket.nest (hs : σ.Pocket J I s a b Cs Cs' Ps Qs)
    (ht : σ.Pocket J I t a' b' Ct Ct' Pt Qt) (hJI : σ.IsInteriorOf J I)
    (ha' : a' ∈ J) (hb' : b' ∈ J) (hss : @TArc S σ.topology a b s) (hsI : s \ {a, b} ⊆ I)
    (htt : @TArc S σ.topology a' b' t) (htI : t \ {a', b'} ⊆ I) (hst : Disjoint s t)
    {K : Set S} (hKJ : K ⊆ J) (hK : ∀ x y : S, ¬ K ⊆ {x, y}) (hsK : (K ∩ Cs).Subsingleton)
    (htK : (K ∩ Ct).Subsingleton) : Disjoint Ps Pt ∨ Ps ⊆ Pt ∨ Pt ⊆ Ps := by
  classical
  letI := σ.topology
  have hIJ := (jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hJI).2.2.2.2.2.2.2.2.2.1
  -- the pocket `Pt` misses `s` when `s°` is in `Qt`, etc.
  have miss : ∀ {s : Set S} {a b : S} {Ps Qs Pt Qt Cs Cs' : Set S},
      σ.Pocket J I s a b Cs Cs' Ps Qs → @TArc S σ.topology a b s → s \ {a, b} ⊆ I →
      s \ {a, b} ⊆ Qt → Disjoint Pt Qt → Pt ⊆ I → Disjoint Pt s := by
    intro s a b Ps Qs Pt Qt Cs Cs' hs hss hsI hsQ hdis hPI
    rw [disjoint_left]
    intro z hzP hzs
    have hzI := hPI hzP
    have : z ∈ s \ {a, b} := ⟨hzs, by
      rintro (rfl | rfl)
      · exact disjoint_left.mp hIJ hzI (hs.C_sub hs.hC.left_mem)
      · exact disjoint_left.mp hIJ hzI (hs.C_sub hs.hC.right_mem)⟩
    exact disjoint_left.mp hdis hzP (hsQ this)
  rcases hs.side h1 h2 h3 h4 h5 h7 htt htI hst with htP | htQ <;>
    rcases ht.side h1 h2 h3 h4 h5 h7 hss hsI hst.symm with hsP | hsQ
  · -- each chord in the other's pocket: impossible
    exfalso
    have hQsPt : Qs ⊆ Pt := by
      have hd : Disjoint Qs t := miss ht htt htI htP hs.dis.symm hs.Q_sub
      rcases ht.conn h1 h2 h3 h4 h5 h7 (hs.swap.isPreconnected_P h1 h2 h3 h4 h5 h7)
        (fun z hz => ⟨hs.Q_sub hz, fun h => disjoint_left.mp hd hz h⟩) with h | h
      · exact h
      · obtain ⟨y, hy⟩ := hss.nonempty_diff
        obtain ⟨z, hzP, hzQ⟩ := nonempty_inter_of_mem_closure (ht.isOpen_P h1 h2 h3 h4 h5 h7)
          (hsP hy) (hs.swap.diff_sub_closure h1 h2 h3 h4 h5 h7 hy)
        exact absurd (h hzQ) (disjoint_left.mp ht.dis hzP)
    have hJ : J ⊆ Cs ∪ Ct := by
      intro z hzJ
      by_cases hzC : z ∈ Cs
      · exact Or.inl hzC
      right
      have hzC' : z ∈ Cs' := by rw [← hs.hCu] at hzJ; exact hzJ.resolve_left hzC
      have hzcl : z ∈ closure Pt :=
        closure_mono hQsPt (hs.swap.C_sub_closure_P h1 h2 h3 h4 h5 h7 hzC')
      rw [ht.closure_P h1 h2 h3 h4 h5 h7] at hzcl
      rcases hzcl with hzP | hzt | hzC
      · exact absurd hzJ (disjoint_left.mp hIJ (ht.P_sub hzP))
      · rcases chord_inter_J h1 h2 h3 h4 h5 h7 hJI htI hzt hzJ with rfl | rfl
        · exact ht.hC.left_mem
        · exact ht.hC.right_mem
      · exact hzC
    apply hK (if h : (K ∩ Cs).Nonempty then h.some else a) (if h : (K ∩ Ct).Nonempty then h.some else a)
    intro z hzK
    rcases hJ (hKJ hzK) with hz | hz
    · have hne : (K ∩ Cs).Nonempty := ⟨z, hzK, hz⟩
      left; rw [dif_pos hne]; exact hsK ⟨hzK, hz⟩ hne.some_mem
    · have hne : (K ∩ Ct).Nonempty := ⟨z, hzK, hz⟩
      right; rw [mem_singleton_iff, dif_pos hne]; exact htK ⟨hzK, hz⟩ hne.some_mem
  · -- `t` in the pocket of `s`, `s` not in the pocket of `t`: `Pt ⊆ Ps`
    right; right
    have hd : Disjoint Pt s := miss hs hss hsI hsQ ht.dis ht.P_sub
    rcases hs.conn h1 h2 h3 h4 h5 h7 (ht.isPreconnected_P h1 h2 h3 h4 h5 h7)
      (fun z hz => ⟨ht.P_sub hz, fun h => disjoint_left.mp hd hz h⟩) with h | h
    · exact h
    · obtain ⟨y, hy⟩ := htt.nonempty_diff
      obtain ⟨z, hzP, hzQ⟩ := nonempty_inter_of_mem_closure (hs.isOpen_P h1 h2 h3 h4 h5 h7)
        (htP hy) (ht.diff_sub_closure h1 h2 h3 h4 h5 h7 hy)
      exact absurd (h hzQ) (disjoint_left.mp hs.dis hzP)
  · -- symmetric: `Ps ⊆ Pt`
    right; left
    have hd : Disjoint Ps t := miss ht htt htI htQ hs.dis hs.P_sub
    rcases ht.conn h1 h2 h3 h4 h5 h7 (hs.isPreconnected_P h1 h2 h3 h4 h5 h7)
      (fun z hz => ⟨hs.P_sub hz, fun h => disjoint_left.mp hd hz h⟩) with h | h
    · exact h
    · obtain ⟨y, hy⟩ := hss.nonempty_diff
      obtain ⟨z, hzP, hzQ⟩ := nonempty_inter_of_mem_closure (ht.isOpen_P h1 h2 h3 h4 h5 h7)
        (hsP hy) (hs.diff_sub_closure h1 h2 h3 h4 h5 h7 hy)
      exact absurd (h hzQ) (disjoint_left.mp ht.dis hzP)
  · -- neither in the other's pocket: exclusive
    left
    have hd : Disjoint Ps t := miss ht htt htI htQ hs.dis hs.P_sub
    rcases ht.conn h1 h2 h3 h4 h5 h7 (hs.isPreconnected_P h1 h2 h3 h4 h5 h7)
      (fun z hz => ⟨hs.P_sub hz, fun h => disjoint_left.mp hd hz h⟩) with h | h
    · exfalso
      obtain ⟨y, hy⟩ := hss.nonempty_diff
      obtain ⟨z, hzQ, hzP⟩ := nonempty_inter_of_mem_closure (ht.swap.isOpen_P h1 h2 h3 h4 h5 h7)
        (hsQ hy) (closure_mono h (hs.diff_sub_closure h1 h2 h3 h4 h5 h7 hy))
      exact disjoint_left.mp ht.dis hzP hzQ
    · exact ht.dis.symm.mono_left h

end Two

end HPC.Moore
