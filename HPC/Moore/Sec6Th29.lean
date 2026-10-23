import HPC.Moore.Sec6Th28

/-!
# Moore, F.A. (1916), §6: Theorems 29 and 30 (batch 138, item B)

**Theorem 29.** If `A`, `B` separate `C`, `D` on `J`, and the open arcs `AXB`, `CYD` are both
within or both without `J`, then they meet.

**Theorem 30.** Under the same hypothesis, the interiors of `AXBDA` and `CYDBC` meet. (No proof
printed.)

Moore's proof of Theorem 29 (pp. 145–146): Case I (both within) by Theorem 25; Case II (both
without) by Theorem 27. In Case I Moore argues with a point `P` of `CYD` near `C`; here the same
argument is phrased with Axiom 2: the connected open arc `CYD` lies in `R₁ + R₂` (Theorem 25)
and so in one of them, but `D` is without `R₁` and `C` without `R₂` (Theorem 24).

The proof of Theorem 30 supplied here (`Gen.th30`) uses a point `Q` of `J`, on the open arc `ADB`
and on the open arc `DBC`, near `D`. Case I: near `Q`, the points of `R` lie in `R₁` (Theorems
24, 25 for `AXB`) and in `R₂` (Theorems 24, 25 for `CYD`). Case II: Theorem 27 for `AXB` and for
`CYD` gives two alternatives each; in the four combinations a common point is found in `R`, near
`C`, near a point of the other arc `DAC` of `J`, or near `Q` outside `J` (Theorem 20).
-/

namespace HPC.Moore

open Set Topology

namespace Gen

variable {T : Type*} [TopologicalSpace T] [T2Space T] {reg : Set (Set T)}

omit [T2Space T] in
/-- An arc `AXB` whose open part misses `J`, together with an arc `ACB` of `J`, forms a closed
curve. -/
theorem tscc_of_open_disjoint {J : Set T} {A B : T} {Ci Xa : Set T} (hCi : TArc A B Ci)
    (hX : TArc A B Xa) (hCiJ : Ci ⊆ J) (hXJ : ∀ x ∈ Xa \ {A, B}, x ∉ J) : TSCC (Xa ∪ Ci) := by
  refine ⟨A, B, Xa, Ci, hX, hCi, ?_, rfl⟩
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    by_contra h
    exact hXJ x ⟨hx, h⟩ (hCiJ hxC)
  · rintro (rfl | rfl)
    · exact ⟨hX.left_mem, hCi.left_mem⟩
    · exact ⟨hX.right_mem, hCi.right_mem⟩

/-- Theorem 27, both alternatives: if the open arc `AXB` is without `J`, then the interior of
`AXBDA` is `ACB (open) + R + R₁`, or the interior of `AXBCA` is `ADB (open) + R + R₂`. -/
theorem th27_dich [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    {J R : Set T} (hR : TInt reg J R) {A B C D : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    (hC : C ∈ C₁ \ {A, B}) (hD : D ∈ C₂ \ {A, B})
    {Xa : Set T} (hX : TArc A B Xa) (hXR : Xa \ {A, B} ⊆ (closure R)ᶜ) {R₁ R₂ : Set T}
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₂ : TInt reg (Xa ∪ C₂) R₂) :
    R₂ = C₁ \ {A, B} ∪ R ∪ R₁ ∨ R₁ = C₂ \ {A, B} ∪ R ∪ R₂ := by
  have h := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₁ hC₂ hC12 hCJ hC hD hX hXR hR₁ hR₂
  have h' := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₂ hC₁
    (by rw [inter_comm]; exact hC12) (by rw [union_comm]; exact hCJ) hD hC hX hXR hR₂ hR₁
  rcases h.1 with h1 | h1
  · exact Or.inl (h.2 h1).2
  · exact Or.inr (h'.2 h1).2

/-- **Theorem 29**, topologically. -/
theorem th29 [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    {J R : Set T} (hR : TInt reg J R) {A B C D : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    (hC : C ∈ C₁ \ {A, B}) (hD : D ∈ C₂ \ {A, B}) {Xa Y : Set T} (hX : TArc A B Xa)
    (hY : TArc C D Y)
    (hin : (Xa \ {A, B} ⊆ R ∧ Y \ {C, D} ⊆ R) ∨
      (Xa \ {A, B} ⊆ (closure R)ᶜ ∧ Y \ {C, D} ⊆ (closure R)ᶜ)) :
    (Xa \ {A, B} ∩ (Y \ {C, D})).Nonempty := by
  have hRo := hopen R hR.2.1
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  have hC₂J : C₂ ⊆ J := hCJ ▸ subset_union_right
  have hAJ : A ∈ J := hC₁J hC₁.left_mem
  have hBJ : B ∈ J := hC₁J hC₁.right_mem
  have hJcl : J ⊆ closure R := hR.2.2 ▸ frontier_subset_closure
  have hRJ : ∀ x ∈ R, x ∉ J := fun x hx hxJ => notMem_of_mem_frontier hRo (hR.2.2 ▸ hxJ) hx
  have hXJ : ∀ x ∈ Xa \ {A, B}, x ∉ J := by
    intro x hx hxJ
    rcases hin with h | h
    · exact hRJ x (h.1 hx) hxJ
    · exact h.1 hx (hJcl hxJ)
  obtain ⟨R₁, hR₁reg, hR₁fr⟩ := h8 _ (tscc_of_open_disjoint hC₁ hX hC₁J hXJ)
  obtain ⟨R₂, hR₂reg, hR₂fr⟩ := h8 _ (tscc_of_open_disjoint hC₂ hX hC₂J hXJ)
  have hR₁ : TInt reg (Xa ∪ C₁) R₁ := ⟨tscc_of_open_disjoint hC₁ hX hC₁J hXJ, hR₁reg, hR₁fr⟩
  have hR₂ : TInt reg (Xa ∪ C₂) R₂ := ⟨tscc_of_open_disjoint hC₂ hX hC₂J hXJ, hR₂reg, hR₂fr⟩
  have hR₁o := hopen R₁ hR₁reg
  have hR₂o := hopen R₂ hR₂reg
  have hCcl : C ∈ closure (Y \ {C, D}) := hY.subset_closure_diff hY.left_mem
  have hDcl : D ∈ closure (Y \ {C, D}) := hY.subset_closure_diff hY.right_mem
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hYX : ∀ y ∈ Y \ {C, D}, y ∉ Xa \ {A, B} := fun y hy hyX =>
    (eq_empty_iff_forall_notMem.mp hne) y ⟨hyX, hy⟩
  rcases hin with ⟨hXR, hYR⟩ | ⟨hXR, hYR⟩
  · -- Case I: both within `J`
    have hR₁R := th24_sub h21 hR hAJ hBJ hC₁J hXR hR₁
    have hR₂R := th24_sub h21 hR hAJ hBJ hC₂J hXR hR₂
    have hC₂ext := th24_ext hopen hR hC₂J hC12 hXR hR₁ hR₁R
    have hC₁ext := th24_ext hopen hR hC₁J (by rw [inter_comm]; exact hC12) hXR hR₂ hR₂R
    have hdis := th24_disj hopen hpc hR hC₁J hR₁ hR₂ hR₂R hC₂ext hC₂.nonempty_diff
    have hdec := th25 hopen hpc h21 harc h8 hext hR hC₁ hC₂ hC12 hCJ hX hXR hR₁ hR₂
    have hsub : Y \ {C, D} ⊆ R₁ ∪ R₂ := by
      intro y hy
      have := hYR hy
      rw [hdec] at this
      rcases this with (h | h) | h
      · exact absurd h (hYX y hy)
      · exact Or.inl h
      · exact Or.inr h
    rcases hY.isPreconnected_diff.subset_or_subset hR₁o hR₂o hdis hsub with h | h
    · exact hC₂ext hD (closure_mono h hDcl)
    · exact hC₁ext hC (closure_mono h hCcl)
  · -- Case II: both without `J`
    have hYXJ : Disjoint (Y \ {C, D}) (Xa ∪ J) := by
      rw [disjoint_left]
      rintro y hy (hyX | hyJ)
      · by_cases hyAB : y ∈ ({A, B} : Set T)
        · rcases hyAB with h | h
          · exact hYR hy (h ▸ hJcl hAJ)
          · exact hYR hy (h ▸ hJcl hBJ)
        · exact hYX y hy ⟨hyX, hyAB⟩
      · exact hYR hy (hJcl hyJ)
    have key : ∀ {P Q : T} {Ci Ri Rj : Set T}, IsOpen Rj → frontier Rj ⊆ Xa ∪ J → Ci ⊆ J →
        P ∈ Rj → Q ∈ (closure Ri)ᶜ → Rj = Ci \ {A, B} ∪ R ∪ Ri →
        P ∈ closure (Y \ {C, D}) → Q ∈ closure (Y \ {C, D}) → False := by
      intro P Q Ci Ri Rj hRjo hfr hCiJ hP hQ hRj hPcl hQcl
      have hsub : Y \ {C, D} ⊆ Rj := conn_sub_of_frontier hY.isPreconnected_diff
        (hYXJ.mono_right hfr) (by
          obtain ⟨y, hyRj, hy⟩ := mem_closure_iff_nhds.mp hPcl Rj (hRjo.mem_nhds hP)
          exact ⟨y, hy, hyRj⟩)
      have hsub' : Y \ {C, D} ⊆ Ri := by
        intro y hy
        have := hsub hy
        rw [hRj] at this
        rcases this with (h | h) | h
        · exact absurd (hJcl (hCiJ h.1)) (hYR hy)
        · exact absurd (subset_closure h) (hYR hy)
        · exact h
      exact hQ (closure_mono hsub' hQcl)
    have h27 := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₁ hC₂ hC12 hCJ hC hD hX hXR hR₁ hR₂
    have h27' := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₂ hC₁
      (by rw [inter_comm]; exact hC12) (by rw [union_comm]; exact hCJ) hD hC hX hXR hR₂ hR₁
    rcases h27.1 with h | h
    · obtain ⟨hCR₂, hR₂eq⟩ := h27.2 h
      exact key hR₂o (by rw [hR₂fr]; exact union_subset_union_right _ hC₂J) hC₁J hCR₂ h hR₂eq
        hCcl hDcl
    · obtain ⟨hDR₁, hR₁eq⟩ := h27'.2 h
      exact key hR₁o (by rw [hR₁fr]; exact union_subset_union_right _ hC₁J) hC₂J hDR₁ h hR₁eq
        hDcl hCcl

/-- **Theorem 30**, topologically. `F` is the arc of `J` from `C` to `D` that is used (Moore's
`DBC`), `E` the other one. -/
theorem th30 [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    (h20 : ∀ R ∈ reg, frontier R ⊆ closure (closure R)ᶜ)
    {J R : Set T} (hR : TInt reg J R) {A B C D : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    (hC : C ∈ C₁ \ {A, B}) (hD : D ∈ C₂ \ {A, B}) {Xa Y : Set T} (hX : TArc A B Xa)
    (hY : TArc C D Y)
    (hin : (Xa \ {A, B} ⊆ R ∧ Y \ {C, D} ⊆ R) ∨
      (Xa \ {A, B} ⊆ (closure R)ᶜ ∧ Y \ {C, D} ⊆ (closure R)ᶜ))
    {E F : Set T} (hE : TArc C D E) (hF : TArc C D F) (hEF : E ∩ F = {C, D}) (hEFJ : E ∪ F = J)
    {R₁ R₂ : Set T} (hR₁ : TInt reg (Xa ∪ C₂) R₁) (hR₂ : TInt reg (Y ∪ F) R₂) :
    (R₁ ∩ R₂).Nonempty := by
  have hRo := hopen R hR.2.1
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  have hC₂J : C₂ ⊆ J := hCJ ▸ subset_union_right
  have hAJ : A ∈ J := hC₁J hC₁.left_mem
  have hBJ : B ∈ J := hC₁J hC₁.right_mem
  have hEJ : E ⊆ J := hEFJ ▸ subset_union_left
  have hFJ : F ⊆ J := hEFJ ▸ subset_union_right
  have hCJ' : C ∈ J := hEJ hE.left_mem
  have hDJ : D ∈ J := hEJ hE.right_mem
  have hJcl : J ⊆ closure R := hR.2.2 ▸ frontier_subset_closure
  have hRJ : ∀ x ∈ R, x ∉ J := fun x hx hxJ => notMem_of_mem_frontier hRo (hR.2.2 ▸ hxJ) hx
  have hXJ : ∀ x ∈ Xa \ {A, B}, x ∉ J := by
    intro x hx hxJ
    rcases hin with h | h
    · exact hRJ x (h.1 hx) hxJ
    · exact h.1 hx (hJcl hxJ)
  have hYJ : ∀ y ∈ Y \ {C, D}, y ∉ J := by
    intro y hy hyJ
    rcases hin with h | h
    · exact hRJ y (h.2 hy) hyJ
    · exact h.2 hy (hJcl hyJ)
  obtain ⟨R₁', hR₁'reg, hR₁'fr⟩ := h8 _ (tscc_of_open_disjoint hC₁ hX hC₁J hXJ)
  have hR₁' : TInt reg (Xa ∪ C₁) R₁' := ⟨tscc_of_open_disjoint hC₁ hX hC₁J hXJ, hR₁'reg, hR₁'fr⟩
  obtain ⟨R₂', hR₂'reg, hR₂'fr⟩ := h8 _ (tscc_of_open_disjoint hE hY hEJ hYJ)
  have hR₂' : TInt reg (Y ∪ E) R₂' := ⟨tscc_of_open_disjoint hE hY hEJ hYJ, hR₂'reg, hR₂'fr⟩
  have hR₁o := hopen R₁ hR₁.2.1
  have hR₂o := hopen R₂ hR₂.2.1
  have hR₁'o := hopen R₁' hR₁'reg
  have hR₂'o := hopen R₂' hR₂'reg
  have hDC₁ : D ∉ C₁ := fun h => hD.2 (hC12 ▸ ⟨h, hD.1⟩)
  -- the point `Q`, on the open arcs `ADB` and `DBC`, and `Q'`, on the open arcs `ADB` and `DAC`
  obtain ⟨Q, hQC₁, hQF⟩ : ∃ Q, Q ∉ C₁ ∧ Q ∈ F \ {C, D} :=
    mem_closure_iff_nhds.mp (hF.subset_closure_diff hF.right_mem) C₁ᶜ
      (hC₁.isClosed.isOpen_compl.mem_nhds hDC₁)
  obtain ⟨Q', hQ'C₁, hQ'E⟩ : ∃ Q', Q' ∉ C₁ ∧ Q' ∈ E \ {C, D} :=
    mem_closure_iff_nhds.mp (hE.subset_closure_diff hE.right_mem) C₁ᶜ
      (hC₁.isClosed.isOpen_compl.mem_nhds hDC₁)
  have hQJ : Q ∈ J := hFJ hQF.1
  have hQC₂ : Q ∈ C₂ \ {A, B} := ⟨(hCJ ▸ hQJ : Q ∈ C₁ ∪ C₂).resolve_left hQC₁, fun h => hQC₁ (by
    rcases h with h | h
    · exact h ▸ hC₁.left_mem
    · exact h ▸ hC₁.right_mem)⟩
  have hQ'C₂ : Q' ∈ C₂ := (hCJ ▸ hEJ hQ'E.1 : Q' ∈ C₁ ∪ C₂).resolve_left hQ'C₁
  have hQX : Q ∉ Xa := fun h => hXJ Q ⟨h, hQC₂.2⟩ hQJ
  have hQY : Q ∉ Y := fun h => hYJ Q ⟨h, hQF.2⟩ hQJ
  have hQfr : Q ∈ frontier R := hR.2.2 ▸ hQJ
  rcases hin with ⟨hXR, hYR⟩ | ⟨hXR, hYR⟩
  · -- Case I: near `Q`, the points of `R` are in `R₁` and in `R₂`
    have hR₁'R := th24_sub h21 hR hAJ hBJ hC₁J hXR hR₁'
    have hR₂'R := th24_sub h21 hR hCJ' hDJ hEJ hYR hR₂'
    have hC₂ext := th24_ext hopen hR hC₂J hC12 hXR hR₁' hR₁'R
    have hFext := th24_ext hopen hR hFJ hEF hYR hR₂' hR₂'R
    have hdecX := th25 hopen hpc h21 harc h8 hext hR hC₁ hC₂ hC12 hCJ hX hXR hR₁' hR₁
    have hdecY := th25 hopen hpc h21 harc h8 hext hR hE hF hEF hEFJ hY hYR hR₂' hR₂
    obtain ⟨z, hzN, hzR⟩ := mem_closure_iff_nhds.mp hQfr.1
      ((closure R₁')ᶜ ∩ Xaᶜ ∩ ((closure R₂')ᶜ ∩ Yᶜ))
      (IsOpen.mem_nhds ((isClosed_closure.isOpen_compl.inter hX.isClosed.isOpen_compl).inter
        (isClosed_closure.isOpen_compl.inter hY.isClosed.isOpen_compl))
        ⟨⟨hC₂ext hQC₂, hQX⟩, hFext hQF, hQY⟩)
    refine ⟨z, ?_, ?_⟩
    · have := hzR; rw [hdecX] at this
      rcases this with (h | h) | h
      · exact absurd h.1 hzN.1.2
      · exact absurd (subset_closure h) hzN.1.1
      · exact h
    · have := hzR; rw [hdecY] at this
      rcases this with (h | h) | h
      · exact absurd h.1 hzN.2.2
      · exact absurd (subset_closure h) hzN.2.1
      · exact h
  · -- Case II: Theorem 27 for `AXB` and for `CYD`
    have dX := th27_dich hopen hpc h21 harc h8 hext hcpt hnc hR hC₁ hC₂ hC12 hCJ hC hD hX hXR
      hR₁' hR₁
    have dY := th27_dich hopen hpc h21 harc h8 hext hcpt hnc hR hE hF hEF hEFJ hQ'E hQF hY hYR
      hR₂' hR₂
    rcases dX with hX1 | hX1 <;> rcases dY with hY1 | hY1
    · obtain ⟨z, hz⟩ := nonempty_of_mem_frontier hQfr
      refine ⟨z, ?_, ?_⟩
      · rw [hX1]; exact Or.inl (Or.inr hz)
      · rw [hY1]; exact Or.inl (Or.inr hz)
    · have hCR₁ : C ∈ R₁ := by rw [hX1]; exact Or.inl (Or.inl hC)
      have hCcl : C ∈ closure R₂ :=
        frontier_subset_closure (hR₂.2.2 ▸ Or.inl hY.left_mem : C ∈ frontier R₂)
      exact mem_closure_iff_nhds.mp hCcl R₁ (hR₁o.mem_nhds hCR₁)
    · have hQ'R₂ : Q' ∈ R₂ := by rw [hY1]; exact Or.inl (Or.inl hQ'E)
      have hQ'cl : Q' ∈ closure R₁ :=
        frontier_subset_closure (hR₁.2.2 ▸ Or.inr hQ'C₂ : Q' ∈ frontier R₁)
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.mp hQ'cl R₂ (hR₂o.mem_nhds hQ'R₂)
      exact ⟨z, hz2, hz1⟩
    · have hQR₁' : Q ∈ R₁' := by rw [hX1]; exact Or.inl (Or.inl hQC₂)
      have hQR₂' : Q ∈ R₂' := by rw [hY1]; exact Or.inl (Or.inl hQF)
      obtain ⟨z, hzN, hz⟩ := mem_closure_iff_nhds.mp (h20 R hR.2.1 hQfr) (R₁' ∩ R₂')
        ((hR₁'o.inter hR₂'o).mem_nhds ⟨hQR₁', hQR₂'⟩)
      have h1 := hzN.1
      rw [hX1] at h1
      have h2 := hzN.2
      rw [hY1] at h2
      refine ⟨z, ?_, ?_⟩
      · rcases h1 with (h | h) | h
        · exact absurd (hJcl (hC₂J h.1)) hz
        · exact absurd (subset_closure h) hz
        · exact h
      · rcases h2 with (h | h) | h
        · exact absurd (hJcl (hFJ h.1)) hz
        · exact absurd (subset_closure h) hz
        · exact h

end Gen

variable {S : Type*} {σ : Space S}

/-- **Theorem 29.** If `A`, `B` separate `C`, `D` on `J`, and the open arcs `AXB`, `CYD` are both
within or both without `J`, then they meet. *Axioms used: 1, 2, 3, 4, 5, 7, 8.* Moore's proof
(Theorems 24, 25 in Case I; Theorem 27 in Case II), see `Gen.th29`.
**Shape change:** the axioms are made explicit (Axiom 6 is not used). -/
theorem fa_theorem29 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J R : Set S} (hR : σ.IsInteriorOf J R)
    {A B C D : S} {C₁ C₂ : Set S} (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X Y : Set S}
    (hX : σ.IsArc A B X) (hY : σ.IsArc C D Y)
    (hin : (openArc A B X ⊆ R ∧ openArc C D Y ⊆ R) ∨
      (openArc A B X ⊆ σ.ext R ∧ openArc C D Y ⊆ σ.ext R)) :
    (openArc A B X ∩ openArc C D Y).Nonempty := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX hY
  rw [ext_eq_compl_closure h1] at hin
  obtain ⟨hC₁, hC₂, hC12, hCJ, hC, hD⟩ := (separatesOn_iff h1 h3 h4 h51).mp hsep
  exact Gen.th29 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7)
    (arcConn h1 h3 h4 h51 h2) (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3)
    (fun R hR => isCompact_closure_region h1 h4 hR) (not_isCompact_univ h1 h5) hR hC₁ hC₂ hC12
    hCJ hC hD hX hY hin

/-- **Theorem 30.** Under the hypothesis of Theorem 29, the interiors of `AXBDA` and `CYDBC` meet.
(No proof printed.) *Axioms used: 1, 2, 3, 4, 5, 7, 8.* Proof supplied (`Gen.th30`): Theorems 24,
25 in Case I; Theorems 20, 24–27 in Case II.
**Shape change:** the axioms are made explicit (Axiom 6 is not used). The datum `DBC` is an arc of
`J` from `D` to `C`; the skeleton's further condition `B ∈ DBC` is dropped, since the proof does
not use it: the conclusion holds for *either* arc of `J` from `D` to `C` (the proof works near a
point of `ADB` on the chosen arc, next to `D`). -/
theorem fa_theorem30 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J R : Set S} (hR : σ.IsInteriorOf J R)
    {A B C D : S} {C₁ C₂ : Set S} (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X Y : Set S}
    (hX : σ.IsArc A B X) (hY : σ.IsArc C D Y)
    (hin : (openArc A B X ⊆ R ∧ openArc C D Y ⊆ R) ∨
      (openArc A B X ⊆ σ.ext R ∧ openArc C D Y ⊆ σ.ext R))
    {DBC : Set S} (hDBC : σ.IsArc D C DBC ∧ DBC ⊆ J)
    {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₂) R₁) (hR₂ : σ.IsInteriorOf (Y ∪ DBC) R₂) :
    (R₁ ∩ R₂).Nonempty := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have hJ := hR.1
  obtain ⟨hDBCa, hDBCJ⟩ := hDBC
  obtain ⟨-, -, -, hCJ0, hC0, hD0⟩ := id hsep
  have hCJ' : C ∈ J := hCJ0 ▸ Or.inl hC0.1
  have hDJ' : D ∈ J := hCJ0 ▸ Or.inr hD0.1
  rw [isArc_iff_tarc h1 h3 h4 h51] at hDBCa
  have hF := hDBCa.symm
  obtain ⟨E₁, E₂, hE₁, hE₂, hE12, hEJ, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ hCJ' hDJ' hDBCa.ne.symm
  obtain ⟨E, hE, hEF, hEFJ⟩ : ∃ E, σ.IsArc C D E ∧ E ∩ DBC = {C, D} ∧ E ∪ DBC = J := by
    rcases huniq DBC hDBCJ ((isArc_iff_tarc h1 h3 h4 h51).mpr hF) with e | e
    · exact ⟨E₂, hE₂, by rw [e, inter_comm]; exact hE12, by rw [e, union_comm]; exact hEJ⟩
    · exact ⟨E₁, hE₁, by rw [e]; exact hE12, by rw [e]; exact hEJ⟩
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR hR₁ hR₂
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX hY hE
  rw [ext_eq_compl_closure h1] at hin
  obtain ⟨hC₁, hC₂, hC12, hCJ, hC, hD⟩ := (separatesOn_iff h1 h3 h4 h51).mp hsep
  exact Gen.th30 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7)
    (arcConn h1 h3 h4 h51 h2) (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3)
    (fun R hR => isCompact_closure_region h1 h4 hR) (not_isCompact_univ h1 h5)
    (fun R hR => frontier_subset_closure_ext h1 h7 hR) hR hC₁ hC₂ hC12 hCJ hC hD hX hY hin
    hE hF hEF hEFJ hR₁ hR₂

end HPC.Moore
