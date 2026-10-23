import HPC.Jones.Jones49ETheta
import HPC.Jones.Jones49D
import HPC.Jones.Jones55T2A
import HPC.Jones.Jones49Circle
import HPC.Moore.M25Plane
import HPC.Moore.M41Geom
import HPC.Moore.CutArc

/-!
# Batch 153: plane lemmas for Whyburn 1939, Corollary 1 (items D and F)

* `frontier_cyclic'` (item D): a cut point `z` of the boundary `B` of a complementary domain `R` of
  a compact plane set `M` is a cut point of `M`. If `B − z = U ∪ V` is a separation, put
  `P = U + z`, `Q = V + z` (compact, `P · Q = z`), and let `R_P`, `R_Q` be the components of
  `P ᶜ`, `Q ᶜ` containing `R`. Janiszewski's theorem (`janiszewski_compact`; `P · Q` is connected)
  gives `R_P · R_Q = R`; `V ⊆ R_P` and `U ⊆ R_Q`; and `M · R_Q` is open and closed in `M − z`,
  contains `U` and misses `V`. Neither accessibility nor the Jordan curve theorem is needed.
* `jordan_side`, `theta_not_subset_closure` (the θ-curve lemma used in item F): if three arcs with
  common ends and pairwise only the ends in common lie in the closure of a connected set `D` missing
  them, contradiction. Each of the three curves `Kᵢ + Kⱼ` is a Jordan curve; `D` lies on the side
  containing the third open arc; the other side of `K₁ + K₂` lies on those same sides of the other
  two curves; and Janiszewski's theorem applied to `K₁ + K₃`, `K₂ + K₃` (common part `K₃`,
  connected) contradicts the separation by `K₁ + K₂`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-- The closure of a component of the complement of a closed plane set `K` lies in the component
together with `K`. -/
theorem closure_ccIn_subset {K : Set Pt} (hK : IsClosed K) (x : Pt) :
    closure (connectedComponentIn Kᶜ x) ⊆ connectedComponentIn Kᶜ x ∪ K := by
  rw [closure_eq_self_union_frontier]
  exact union_subset_union_right _ (HPC.Moore.Gen.frontier_connectedComponentIn_subset hK x)

/-! ### Item D -/

/-- The boundary of a complementary domain of a cyclic compact plane set has a point other than
any given point `z` of it: if `frontier R ⊆ {z}` then `{z}ᶜ ⊆ R`, so `M ⊆ {z}`, against
cyclicity. -/
theorem frontier_diff_nonempty {M : Set Pt} (hM : IsCompact M)
    (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt} (hx : x ∉ M) {z : Pt}
    (hz : z ∈ frontier (connectedComponentIn Mᶜ x)) :
    (frontier (connectedComponentIn Mᶜ x) \ {z}).Nonempty := by
  set R := connectedComponentIn Mᶜ x with hRdef
  have hBM : frontier R ⊆ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hM.isClosed x
  have hzM : z ∈ M := hBM hz
  by_contra hne
  rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
  have hxR : x ∈ R := mem_connectedComponentIn hx
  have hsub : ({z}ᶜ : Set Pt) ⊆ R := by
    refine conn_sub_of_frontier (isConnected_compl_singleton_of_one_lt_rank (by norm_num) z).2
      (disjoint_left.mpr fun y hy hyB => hy (hne hyB)) ⟨x, fun e => hx (e ▸ hzM), hxR⟩
  obtain ⟨⟨m, hm⟩, hmz⟩ := (hcyc ⟨z, hzM⟩).nonempty
  have hmz' : m ≠ z := fun e => hmz (Subtype.ext e)
  exact (connectedComponentIn_subset _ _ (hsub hmz')) hm

/-- **Item D: the boundary is cyclic.** Every cut point of the boundary `B` of a complementary
domain of a compact plane set `M` is a cut point of `M` (Janiszewski's theorem; see the module
docstring). Only the compactness of `M` and its cyclicity are used. -/
theorem frontier_cyclic' {M : Set Pt} (hM : IsCompact M)
    (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt} (hx : x ∉ M) :
    ∀ z : frontier (connectedComponentIn Mᶜ x),
      IsConnected ({z}ᶜ : Set (frontier (connectedComponentIn Mᶜ x))) := by
  rintro ⟨z, hz⟩
  set R := connectedComponentIn Mᶜ x with hRdef
  set B := frontier R with hBdef
  rw [HPC.Moore.isConnected_compl_singleton_subtype_iff]
  refine ⟨frontier_diff_nonempty hM hcyc hx hz, ?_⟩
  intro u v hu hv hsuv hSu hSv
  by_contra hSuv
  have hBM : B ⊆ M := HPC.Moore.Gen.frontier_connectedComponentIn_subset hM.isClosed x
  have hzM : z ∈ M := hBM hz
  have hBc : IsCompact B := hM.of_isClosed_subset isClosed_frontier hBM
  have hxR : x ∈ R := mem_connectedComponentIn hx
  have hRM : R ⊆ Mᶜ := connectedComponentIn_subset _ _
  have huv : ∀ y ∈ B, y ≠ z → y ∈ u → y ∈ v → False := fun y hy hyz h1 h2 =>
    hSuv ⟨y, ⟨hy, hyz⟩, h1, h2⟩
  have hcov : ∀ y ∈ B, y ≠ z → y ∈ u ∨ y ∈ v := fun y hy hyz => hsuv ⟨hy, hyz⟩
  set P : Set Pt := (B ∩ vᶜ) ∪ {z} with hPdef
  set Q : Set Pt := (B ∩ uᶜ) ∪ {z} with hQdef
  have hP : IsCompact P := (hBc.inter_right hv.isClosed_compl).union isCompact_singleton
  have hQ : IsCompact Q := (hBc.inter_right hu.isClosed_compl).union isCompact_singleton
  have hPM : P ⊆ M := union_subset (inter_subset_left.trans hBM) (singleton_subset_iff.2 hzM)
  have hQM : Q ⊆ M := union_subset (inter_subset_left.trans hBM) (singleton_subset_iff.2 hzM)
  have hPQ : P ∩ Q = {z} := by
    apply subset_antisymm
    · rintro y ⟨hyP | hyP, hyQ | hyQ⟩
      · by_contra hyz
        rcases hcov y hyP.1 hyz with h | h
        exacts [hyQ.2 h, hyP.2 h]
      all_goals first | exact hyP | exact hyQ
    · rintro y rfl; exact ⟨Or.inr rfl, Or.inr rfl⟩
  have hPQB : P ∪ Q = B := by
    apply subset_antisymm
    · refine union_subset (union_subset inter_subset_left (singleton_subset_iff.2 hz))
        (union_subset inter_subset_left (singleton_subset_iff.2 hz))
    · intro y hy
      by_cases hyz : y = z
      · exact Or.inl (Or.inr hyz)
      by_cases hyv : y ∈ v
      · by_cases hyu : y ∈ u
        · exact (huv y hy hyz hyu hyv).elim
        · exact Or.inr (Or.inl ⟨hy, hyu⟩)
      · exact Or.inl (Or.inl ⟨hy, hyv⟩)
  set RP := connectedComponentIn Pᶜ x with hRPdef
  set RQ := connectedComponentIn Qᶜ x with hRQdef
  have hRPo : IsOpen RP := hP.isClosed.isOpen_compl.connectedComponentIn
  have hRQo : IsOpen RQ := hQ.isClosed.isOpen_compl.connectedComponentIn
  have hRRP : R ⊆ RP := isPreconnected_connectedComponentIn.subset_connectedComponentIn hxR
    (hRM.trans (compl_subset_compl.2 hPM))
  have hRRQ : R ⊆ RQ := isPreconnected_connectedComponentIn.subset_connectedComponentIn hxR
    (hRM.trans (compl_subset_compl.2 hQM))
  have hxB : x ∉ B := fun h => hx (hBM h)
  -- Janiszewski: `RP ∩ RQ ⊆ R`
  have hjan : ∀ y, y ∈ RP → y ∈ RQ → y ∈ R := by
    intro y hyP hyQ
    have hns := HPC.Moore.janiszewski_compact hP hQ
      (Or.inl (by rw [hPQ]; exact isConnected_singleton))
      (x := x) (y := y) (fun h => h.2.2 hyP) (fun h => h.2.2 hyQ)
    rw [hPQB] at hns
    have hyB : y ∉ B := by
      rw [← hPQB]
      rintro (h | h)
      · exact connectedComponentIn_subset _ _ hyP h
      · exact connectedComponentIn_subset _ _ hyQ h
    have hy : y ∈ connectedComponentIn Bᶜ x := by
      by_contra h; exact hns ⟨hxB, hyB, h⟩
    exact conn_sub_of_frontier isPreconnected_connectedComponentIn
      (disjoint_left.mpr fun w hw hwB => (connectedComponentIn_subset _ _ hw : w ∈ Bᶜ) hwB)
      ⟨x, mem_connectedComponentIn hxB, hxR⟩ hy
  have hMRR : ∀ m ∈ M, m ∈ RP → m ∈ RQ → False := fun m hm h1 h2 => hRM (hjan m h1 h2) hm
  have hBcl : B ⊆ closure R := frontier_subset_closure
  have hVRP : ∀ y ∈ B, y ≠ z → y ∈ v → y ∈ RP := by
    intro y hy hyz hyv
    rcases closure_ccIn_subset hP.isClosed x (closure_mono hRRP (hBcl hy)) with h | h
    · exact h
    · rcases h with h | h
      exacts [(h.2 hyv).elim, (hyz h).elim]
  have hURQ : ∀ y ∈ B, y ≠ z → y ∈ u → y ∈ RQ := by
    intro y hy hyz hyu
    rcases closure_ccIn_subset hQ.isClosed x (closure_mono hRRQ (hBcl hy)) with h | h
    · exact h
    · rcases h with h | h
      exacts [(h.2 hyu).elim, (hyz h).elim]
  have hnotcl : ∀ y ∈ RP, y ∉ closure (M ∩ RQ) := by
    intro y hy hcl
    obtain ⟨m, hmP, hmM, hmQ⟩ := mem_closure_iff.1 hcl RP hRPo hy
    exact hMRR m hmM hmP hmQ
  obtain ⟨u₀, ⟨hu₀B, hu₀z⟩, hu₀u⟩ := hSu
  obtain ⟨v₀, ⟨hv₀B, hv₀z⟩, hv₀v⟩ := hSv
  have hMc := (hcyc ⟨z, hzM⟩)
  rw [HPC.Moore.isConnected_compl_singleton_subtype_iff] at hMc
  obtain ⟨m, ⟨hmM, hmz⟩, hmQ, hmW⟩ := hMc.2 RQ (closure (M ∩ RQ))ᶜ hRQo
    isClosed_closure.isOpen_compl
    (by
      rintro m ⟨hmM, hmz⟩
      by_cases hmQ : m ∈ RQ
      · exact Or.inl hmQ
      · right
        intro hcl
        rcases closure_ccIn_subset hQ.isClosed x (closure_mono inter_subset_right hcl) with
          h | h
        · exact hmQ h
        · rcases h with h | h
          · rcases hcov m h.1 hmz with h' | h'
            · exact h.2 h'
            · exact hnotcl m (hVRP m h.1 hmz h') hcl
          · exact hmz h)
    ⟨u₀, ⟨hBM hu₀B, hu₀z⟩, hURQ u₀ hu₀B hu₀z hu₀u⟩
    ⟨v₀, ⟨hBM hv₀B, hv₀z⟩, hnotcl v₀ (hVRP v₀ hv₀B hv₀z hv₀v)⟩
  exact hmW (subset_closure ⟨hmM, hmQ⟩)

/-! ### The θ-curve lemma -/

/-- The two sides of a Jordan curve, named so that a given connected set missing the curve lies in
the first. -/
theorem jordan_side {J : Set Pt} (hJ : TSCC J) {A : Set Pt} (hA : IsPreconnected A)
    (hAJ : Disjoint A J) :
    ∃ S T : Set Pt, IsOpen S ∧ IsPreconnected S ∧ IsOpen T ∧ IsPreconnected T ∧ Disjoint S T ∧
      S ∪ T = Jᶜ ∧ frontier S = J ∧ frontier T = J ∧ A ⊆ S := by
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hIE, hU, -, -, hfI, hfE⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hsub : A ⊆ I ∪ E := hU ▸ fun y hy hyJ => disjoint_left.mp hAJ hy hyJ
  rcases hA.subset_or_subset hIo hEo hIE hsub with h | h
  · exact ⟨I, E, hIo, hIc.2, hEo, hEc.2, hIE, hU, hfI, hfE, h⟩
  · exact ⟨E, I, hEo, hEc.2, hIo, hIc.2, hIE.symm, by rw [union_comm, hU], hfE, hfI, h⟩

/-- A connected set missing a Jordan curve, whose closure meets the side `S`'s part `A`, lies in
`S`. -/
theorem sub_side_of_closure {J S T A D : Set Pt} (hSo : IsOpen S) (hTo : IsOpen T)
    (hST : Disjoint S T) (hU : S ∪ T = Jᶜ) (hfT : frontier T = J) (hAS : A ⊆ S)
    (hD : IsPreconnected D) (hDJ : Disjoint D J) (hAne : A.Nonempty) (hAD : A ⊆ closure D) :
    D ⊆ S := by
  have hsub : D ⊆ S ∪ T := hU ▸ fun y hy hyJ => disjoint_left.mp hDJ hy hyJ
  rcases hD.subset_or_subset hSo hTo hST hsub with h | h
  · exact h
  · obtain ⟨a, ha⟩ := hAne
    have hcl := closure_mono h (hAD ha)
    rw [closure_eq_self_union_frontier, hfT] at hcl
    rcases hcl with h' | h'
    · exact (disjoint_left.mp hST (hAS ha) h').elim
    · have hSJ : a ∈ Jᶜ := by rw [← hU]; exact Or.inl (hAS ha)
      exact (hSJ h').elim

/-- **The θ-curve lemma.** Three arcs with common ends `a ≠ b`, any two meeting only in `a` and
`b`, cannot all lie in the closure of a connected set `D` that misses them. -/
theorem theta_not_subset_closure {a b : Pt} {K₁ K₂ K₃ : Set Pt} (h₁ : TArc a b K₁)
    (h₂ : TArc a b K₂) (h₃ : TArc a b K₃) (h12 : K₁ ∩ K₂ = {a, b}) (h13 : K₁ ∩ K₃ = {a, b})
    (h23 : K₂ ∩ K₃ = {a, b}) {D : Set Pt} (hD : IsPreconnected D)
    (hDθ : Disjoint D (K₁ ∪ K₂ ∪ K₃)) : ¬ (K₁ ∪ K₂ ∪ K₃ ⊆ closure D) := by
  intro hcl
  have mem2 : ∀ {Ki Kk : Set Pt}, Ki ∩ Kk = {a, b} → ∀ y ∈ Kk \ {a, b}, y ∉ Ki :=
    fun hik y hy hyi => hy.2 (hik ▸ ⟨hyi, hy.1⟩)
  have h21 : K₂ ∩ K₁ = {a, b} := by rw [inter_comm]; exact h12
  have h31 : K₃ ∩ K₁ = {a, b} := by rw [inter_comm]; exact h13
  have h32 : K₃ ∩ K₂ = {a, b} := by rw [inter_comm]; exact h23
  have d3 : Disjoint (K₃ \ {a, b}) (K₁ ∪ K₂) := disjoint_left.mpr fun y hy h =>
    h.elim (mem2 h13 y hy) (mem2 h23 y hy)
  have d2 : Disjoint (K₂ \ {a, b}) (K₁ ∪ K₃) := disjoint_left.mpr fun y hy h =>
    h.elim (mem2 h12 y hy) (mem2 h32 y hy)
  have d1 : Disjoint (K₁ \ {a, b}) (K₂ ∪ K₃) := disjoint_left.mpr fun y hy h =>
    h.elim (mem2 h21 y hy) (mem2 h31 y hy)
  obtain ⟨S₃, T₃, hS₃o, hS₃c, hT₃o, hT₃c, hST₃, hU₃, hfS₃, hfT₃, hA₃⟩ :=
    jordan_side ⟨a, b, K₁, K₂, h₁, h₂, h12, rfl⟩ h₃.isPreconnected_diff d3
  obtain ⟨S₂, T₂, hS₂o, hS₂c, hT₂o, hT₂c, hST₂, hU₂, hfS₂, hfT₂, hA₂⟩ :=
    jordan_side ⟨a, b, K₁, K₃, h₁, h₃, h13, rfl⟩ h₂.isPreconnected_diff d2
  obtain ⟨S₁, T₁, hS₁o, hS₁c, hT₁o, hT₁c, hST₁, hU₁, hfS₁, hfT₁, hA₁⟩ :=
    jordan_side ⟨a, b, K₂, K₃, h₂, h₃, h23, rfl⟩ h₁.isPreconnected_diff d1
  have s12 : K₁ ∪ K₂ ⊆ K₁ ∪ K₂ ∪ K₃ := subset_union_left
  have s13 : K₁ ∪ K₃ ⊆ K₁ ∪ K₂ ∪ K₃ := union_subset_union_left _ subset_union_left
  have s23 : K₂ ∪ K₃ ⊆ K₁ ∪ K₂ ∪ K₃ := union_subset_union_left _ subset_union_right
  have k1 : K₁ ⊆ K₁ ∪ K₂ ∪ K₃ := subset_union_left.trans subset_union_left
  have k2 : K₂ ⊆ K₁ ∪ K₂ ∪ K₃ := subset_union_right.trans subset_union_left
  have k3 : K₃ ⊆ K₁ ∪ K₂ ∪ K₃ := subset_union_right
  have hDS₃ : D ⊆ S₃ := sub_side_of_closure hS₃o hT₃o hST₃ hU₃ hfT₃ hA₃ hD (hDθ.mono_right s12)
    h₃.nonempty_diff ((diff_subset.trans k3).trans hcl)
  have hDS₂ : D ⊆ S₂ := sub_side_of_closure hS₂o hT₂o hST₂ hU₂ hfT₂ hA₂ hD (hDθ.mono_right s13)
    h₂.nonempty_diff ((diff_subset.trans k2).trans hcl)
  have hDS₁ : D ⊆ S₁ := sub_side_of_closure hS₁o hT₁o hST₁ hU₁ hfT₁ hA₁ hD (hDθ.mono_right s23)
    h₁.nonempty_diff ((diff_subset.trans k1).trans hcl)
  obtain ⟨z, hz⟩ : D.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simpa using hcl (k1 h₁.left_mem)
  obtain ⟨u, hu⟩ : T₃.Nonempty :=
    nonempty_of_mem_frontier (by rw [hfT₃]; exact Or.inl h₁.left_mem)
  have hT₃J : ∀ y ∈ T₃, y ∉ K₁ ∪ K₂ := fun y hy hyJ => by
    have : y ∈ (K₁ ∪ K₂)ᶜ := hU₃ ▸ Or.inr hy
    exact this hyJ
  have hT₃θ : Disjoint T₃ (K₁ ∪ K₂ ∪ K₃) := by
    refine disjoint_left.mpr fun y hy hyθ => ?_
    rcases hyθ with h | h
    · exact hT₃J y hy h
    · by_cases hyab : y ∈ ({a, b} : Set Pt)
      · rcases hyab with rfl | rfl
        · exact hT₃J _ hy (Or.inl h₁.left_mem)
        · exact hT₃J _ hy (Or.inl h₁.right_mem)
      · exact disjoint_left.mp hST₃ (hA₃ ⟨h, hyab⟩) hy
  have hclT₃ : K₁ ∪ K₂ ⊆ closure T₃ := hfT₃ ▸ frontier_subset_closure
  have hT₃S₂ : T₃ ⊆ S₂ := sub_side_of_closure hS₂o hT₂o hST₂ hU₂ hfT₂ hA₂ hT₃c
    (hT₃θ.mono_right s13) h₂.nonempty_diff
    ((diff_subset.trans subset_union_right).trans hclT₃)
  have hT₃S₁ : T₃ ⊆ S₁ := sub_side_of_closure hS₁o hT₁o hST₁ hU₁ hfT₁ hA₁ hT₃c
    (hT₃θ.mono_right s23) h₁.nonempty_diff
    ((diff_subset.trans subset_union_left).trans hclT₃)
  have hS₂J : S₂ ⊆ (K₁ ∪ K₃)ᶜ := hU₂ ▸ subset_union_left
  have hS₁J : S₁ ⊆ (K₂ ∪ K₃)ᶜ := hU₁ ▸ subset_union_left
  have hns₂ : ¬ SeparatesPts (K₁ ∪ K₃) z u := fun h =>
    h.2.2 (hS₂c.subset_connectedComponentIn (hDS₂ hz) hS₂J (hT₃S₂ hu))
  have hns₁ : ¬ SeparatesPts (K₂ ∪ K₃) z u := fun h =>
    h.2.2 (hS₁c.subset_connectedComponentIn (hDS₁ hz) hS₁J (hT₃S₁ hu))
  have hinter : (K₁ ∪ K₃) ∩ (K₂ ∪ K₃) = K₃ := by
    apply subset_antisymm
    · rintro y ⟨h1 | h1, h2 | h2⟩
      · have : y ∈ K₁ ∩ K₂ := ⟨h1, h2⟩
        rw [h12] at this
        rcases this with rfl | rfl
        exacts [h₃.left_mem, h₃.right_mem]
      all_goals assumption
    · intro y hy; exact ⟨Or.inr hy, Or.inr hy⟩
  have hjan := HPC.Moore.janiszewski_compact (h₁.isCompact.union h₃.isCompact)
    (h₂.isCompact.union h₃.isCompact)
    (Or.inl (by rw [hinter]; exact ⟨⟨a, h₃.left_mem⟩, h₃.isPreconnected⟩)) hns₂ hns₁
  have hθeq : K₁ ∪ K₃ ∪ (K₂ ∪ K₃) = K₁ ∪ K₂ ∪ K₃ := by
    ext y; simp only [mem_union]; tauto
  rw [hθeq] at hjan
  have hzθ : z ∉ K₁ ∪ K₂ ∪ K₃ := disjoint_left.mp hDθ hz
  refine hjan ⟨hzθ, disjoint_left.mp hT₃θ hu, fun hmem => ?_⟩
  have hCsub : connectedComponentIn (K₁ ∪ K₂ ∪ K₃)ᶜ z ⊆ S₃ ∪ T₃ := by
    rw [hU₃]
    exact (connectedComponentIn_subset _ _).trans (compl_subset_compl.2 s12)
  rcases isPreconnected_connectedComponentIn.subset_or_subset hS₃o hT₃o hST₃ hCsub with h | h
  · exact disjoint_left.mp hST₃ (h hmem) hu
  · exact disjoint_left.mp hST₃ (hDS₃ hz) (h (mem_connectedComponentIn hzθ))

end HPC.Jones
