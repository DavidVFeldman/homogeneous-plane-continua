import HPC.Jones.Jones49E

/-!
# Batch 154: plane lemmas for Jones 1949 Theorem 1 (θ-curves)

* `mem_cc_of_not_mem_domain` — two points off a Jordan curve and off one of its complementary
  domains lie in the same component of the complement of the curve.
* `theta_no_common_side` — for a θ-curve `K₁ + K₂ + K₃` no point lies, for each `i`, on the side of
  `Kⱼ + Kₖ` containing the open arc `Kᵢ` (Jordan curve theorem and Janiszewski's theorem).
* `theta_separation` — the separation of `M − (A + B)` in Case 2 (item C, step 5).
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-- A preconnected set missing a closed set `F`, with a point `k ∉ F` in its closure, lies in the
component of `Fᶜ` containing `k`. -/
theorem sub_cc_of_mem_closure {F T : Set Pt} (hF : IsClosed F) (hT : IsPreconnected T)
    (hTF : Disjoint T F) {k : Pt} (hk : k ∉ F) (hkT : k ∈ closure T) :
    T ⊆ connectedComponentIn Fᶜ k := by
  have hO : IsOpen (connectedComponentIn Fᶜ k) := hF.isOpen_compl.connectedComponentIn
  obtain ⟨t, htO, htT⟩ := mem_closure_iff.mp hkT _ hO (mem_connectedComponentIn hk)
  rw [connectedComponentIn_eq htO]
  exact hT.subset_connectedComponentIn htT fun z hz hzF => disjoint_left.mp hTF hz hzF

/-- A component of `Fᶜ` meeting a preconnected set `S` whose frontier lies in `F` is contained in
`S`. -/
theorem cc_sub_of_frontier {F S : Set Pt} (hSF : frontier S ⊆ F) {k : Pt} (hk : k ∈ S) :
    connectedComponentIn Fᶜ k ⊆ S := by
  by_cases hkF : k ∈ F
  · rw [connectedComponentIn_eq_empty (by simpa using hkF)]; exact empty_subset _
  refine conn_sub_of_frontier isPreconnected_connectedComponentIn ?_
    ⟨k, mem_connectedComponentIn hkF, hk⟩
  exact disjoint_left.mpr fun z hz hzf => connectedComponentIn_subset _ _ hz (hSF hzf)

/-- Two points off a Jordan curve `Γ` and off a complementary domain `D` of `Γ` (open, connected,
with frontier `Γ`) lie in the same component of `Γᶜ`. -/
theorem mem_cc_of_not_mem_domain {Γ D : Set Pt} (hΓ : TSCC Γ) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDne : D.Nonempty) (hDf : frontier D = Γ) {m l : Pt} (hm : m ∉ D)
    (hmΓ : m ∉ Γ) (hl : l ∉ D) (hlΓ : l ∉ Γ) : m ∈ connectedComponentIn Γᶜ l := by
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hIE, hU, -, -, hfI, hfE⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hΓ)
  have hDΓ : D ⊆ Γᶜ := fun z hz hzΓ => by
    have : z ∈ D ∩ frontier D := ⟨hz, hDf ▸ hzΓ⟩
    rw [hDo.inter_frontier_eq] at this; exact this
  have hDIE : D ⊆ I ∪ E := hU ▸ hDΓ
  have key : ∀ {P Q : Set Pt}, IsPreconnected P → IsPreconnected Q → P ∪ Q = Γᶜ →
      Disjoint P Q → D ⊆ P → m ∈ connectedComponentIn Γᶜ l := by
    intro P Q hP hQ hPQ hdisj hDP
    have hPD : P ⊆ D := by
      refine conn_sub_of_frontier hP ?_ ?_
      · rw [hDf]; exact disjoint_left.mpr fun z hz hzΓ => (hPQ ▸ Or.inl hz : z ∈ Γᶜ) hzΓ
      · obtain ⟨d, hd⟩ := hDne; exact ⟨d, hDP hd, hd⟩
    have hmQ : m ∈ Q := by
      have : m ∈ P ∪ Q := hPQ ▸ hmΓ
      exact this.resolve_left fun h => hm (hPD h)
    have hlQ : l ∈ Q := by
      have : l ∈ P ∪ Q := hPQ ▸ hlΓ
      exact this.resolve_left fun h => hl (hPD h)
    exact hQ.subset_connectedComponentIn hlQ (fun z hz => hPQ ▸ Or.inr hz) hmQ
  rcases hDc.subset_or_subset hIo hEo hIE hDIE with h | h
  · exact key hIc.2 hEc.2 hU hIE h
  · exact key hEc.2 hIc.2 (by rw [union_comm, hU]) hIE.symm h

/-- The side of a Jordan curve containing a given connected set, as a component. -/
theorem side_eq_cc {Γ S : Set Pt} (hSc : IsPreconnected S) (hSf : frontier S = Γ)
    (hSΓ : Disjoint S Γ) {k : Pt} (hk : k ∈ S) : connectedComponentIn Γᶜ k = S := by
  refine subset_antisymm (cc_sub_of_frontier hSf.le hk) ?_
  exact hSc.subset_connectedComponentIn hk fun z hz hzΓ => disjoint_left.mp hSΓ hz hzΓ

/-- **No common side.** For a θ-curve `K₁ + K₂ + K₃` (arcs from `a` to `b` meeting pairwise in
`a`, `b`) and points `kᵢ ∈ Kᵢ − {a, b}`, no point off the θ-curve lies in the component of
`(Kⱼ + Kₖ)ᶜ` containing `kᵢ` for all three `i`. Proof: a point `w` of the other side of `K₁ + K₂`
lies on the `k₁`-side of `K₂ + K₃` and on the `k₂`-side of `K₁ + K₃`, as `m` does; by
Janiszewski's theorem (`janiszewski_compact`, with common part `K₃`) `m`, `w` lie in one component
of the complement of the θ-curve, hence on one side of `K₁ + K₂`. -/
theorem theta_no_common_side {a b : Pt} {K₁ K₂ K₃ : Set Pt} (h₁ : TArc a b K₁) (h₂ : TArc a b K₂)
    (h₃ : TArc a b K₃) (h12 : K₁ ∩ K₂ = {a, b}) (h13 : K₁ ∩ K₃ = {a, b})
    (h23 : K₂ ∩ K₃ = {a, b}) {k₁ k₂ k₃ m : Pt} (hk₁ : k₁ ∈ K₁ \ {a, b}) (hk₂ : k₂ ∈ K₂ \ {a, b})
    (hk₃ : k₃ ∈ K₃ \ {a, b}) (hm : m ∉ K₁ ∪ K₂ ∪ K₃)
    (hm12 : m ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ k₃)
    (hm23 : m ∈ connectedComponentIn (K₂ ∪ K₃)ᶜ k₁)
    (hm13 : m ∈ connectedComponentIn (K₁ ∪ K₃)ᶜ k₂) : False := by
  have mem2 : ∀ {Ki Kk : Set Pt}, Ki ∩ Kk = {a, b} → ∀ y ∈ Kk \ {a, b}, y ∉ Ki :=
    fun hik y hy hyi => hy.2 (hik ▸ ⟨hyi, hy.1⟩)
  have d3 : Disjoint (K₃ \ {a, b}) (K₁ ∪ K₂) := disjoint_left.mpr fun y hy h =>
    h.elim (mem2 h13 y hy) (mem2 h23 y hy)
  obtain ⟨S, T, hSo, hSc, hTo, hTc, hST, hU, hfS, hfT, hAS⟩ :=
    jordan_side ⟨a, b, K₁, K₂, h₁, h₂, h12, rfl⟩ h₃.isPreconnected_diff d3
  have hTΓ : Disjoint T (K₁ ∪ K₂) := by
    refine disjoint_left.mpr fun z hz hzΓ => ?_
    have : z ∈ T ∩ frontier T := ⟨hz, hfT ▸ hzΓ⟩
    rw [hTo.inter_frontier_eq] at this; exact this
  have hT3 : Disjoint T K₃ := by
    refine disjoint_left.mpr fun z hz hz3 => ?_
    by_cases hzab : z ∈ ({a, b} : Set Pt)
    · have : z ∈ K₁ := by
        rcases hzab with rfl | rfl
        · exact h₁.left_mem
        · exact h₁.right_mem
      exact disjoint_left.mp hTΓ hz (Or.inl this)
    · exact disjoint_left.mp hST (hAS ⟨hz3, hzab⟩) hz
  obtain ⟨w, hw⟩ : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, frontier_empty] at hfT
    exact (hfT ▸ (Or.inl h₁.left_mem : a ∈ K₁ ∪ K₂) : a ∈ (∅ : Set Pt))
  have hK1T : K₁ ⊆ closure T := fun z hz => frontier_subset_closure (hfT ▸ Or.inl hz)
  have hK2T : K₂ ⊆ closure T := fun z hz => frontier_subset_closure (hfT ▸ Or.inr hz)
  have hcl23 : IsClosed (K₂ ∪ K₃) := h₂.isClosed.union h₃.isClosed
  have hcl13 : IsClosed (K₁ ∪ K₃) := h₁.isClosed.union h₃.isClosed
  have n12 : k₁ ∉ K₂ := mem2 (by rw [inter_comm]; exact h12) k₁ hk₁
  have n13 : k₁ ∉ K₃ := mem2 (by rw [inter_comm]; exact h13) k₁ hk₁
  have n21 : k₂ ∉ K₁ := mem2 h12 k₂ hk₂
  have n23 : k₂ ∉ K₃ := mem2 (by rw [inter_comm]; exact h23) k₂ hk₂
  have hT23 : T ⊆ connectedComponentIn (K₂ ∪ K₃)ᶜ k₁ :=
    sub_cc_of_mem_closure hcl23 hTc (disjoint_union_right.mpr ⟨hTΓ.mono_right subset_union_right,
      hT3⟩) (fun h => h.elim n12 n13) (hK1T hk₁.1)
  have hT13 : T ⊆ connectedComponentIn (K₁ ∪ K₃)ᶜ k₂ :=
    sub_cc_of_mem_closure hcl13 hTc (disjoint_union_right.mpr ⟨hTΓ.mono_right subset_union_left,
      hT3⟩) (fun h => h.elim n21 n23) (hK2T hk₂.1)
  have hns13 : ¬ SeparatesPts (K₁ ∪ K₃) m w := by
    rintro ⟨-, -, h⟩; apply h; rw [← connectedComponentIn_eq hm13]; exact hT13 hw
  have hns23 : ¬ SeparatesPts (K₂ ∪ K₃) m w := by
    rintro ⟨-, -, h⟩; apply h; rw [← connectedComponentIn_eq hm23]; exact hT23 hw
  have hint : (K₁ ∪ K₃) ∩ (K₂ ∪ K₃) = K₃ := by
    ext z
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · have : z ∈ K₁ ∩ K₂ := ⟨h1, h2⟩
        rw [h12] at this
        rcases this with rfl | rfl
        · exact h₃.left_mem
        · exact h₃.right_mem
      all_goals assumption
    · intro hz; exact ⟨Or.inr hz, Or.inr hz⟩
  have hJ := HPC.Moore.janiszewski_compact (h₁.isCompact.union h₃.isCompact)
    (h₂.isCompact.union h₃.isCompact)
    (Or.inl (by rw [hint]; exact ⟨⟨a, h₃.left_mem⟩, h₃.isPreconnected⟩)) hns13 hns23
  apply hJ
  refine ⟨fun h => hm (by rcases h with (h | h) | (h | h) <;> simp_all), fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h) | (h | h)
    · exact disjoint_left.mp hTΓ hw (Or.inl h)
    · exact disjoint_left.mp hT3 hw h
    · exact disjoint_left.mp hTΓ hw (Or.inr h)
    · exact disjoint_left.mp hT3 hw h
  · have hsub : ((K₁ ∪ K₃) ∪ (K₂ ∪ K₃))ᶜ ⊆ (K₁ ∪ K₂)ᶜ := by
      refine compl_subset_compl.mpr fun z hz => ?_
      rcases hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · exact Or.inr (Or.inl hz)
    have h1 := connectedComponentIn_mono m hsub h
    rw [← connectedComponentIn_eq hm12] at h1
    exact disjoint_left.mp hST (cc_sub_of_frontier hfS.le (hAS hk₃) h1) hw

/-- An open set whose frontier is nonempty is nonempty. -/
theorem nonempty_of_frontier {T : Set Pt} {z : Pt} (hz : z ∈ frontier T) : T.Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  rw [h, frontier_empty] at hz
  exact hz

/-- An open set misses its frontier. -/
theorem disjoint_frontier_of_isOpen {T Γ : Set Pt} (hTo : IsOpen T) (hf : frontier T = Γ) :
    Disjoint T Γ := by
  refine disjoint_left.mpr fun z hz hzΓ => ?_
  have : z ∈ T ∩ frontier T := ⟨hz, hf ▸ hzΓ⟩
  rw [hTo.inter_frontier_eq] at this; exact this

/-- A point of `K − {a, b}` is not in an arc meeting `K` only in `a`, `b`. -/
theorem not_mem_of_inter {a b y : Pt} {K K' : Set Pt} (h : K' ∩ K = {a, b})
    (hy : y ∈ K \ {a, b}) : y ∉ K' := fun hy' => hy.2 (h ▸ ⟨hy', hy.1⟩)

/-- **Item C, step 5: the separation of `M − (A + B)`.** `J₁`, `J₂`, `L` are arcs from `A` to `B`
meeting pairwise only in `A`, `B`, lying in `M`; `D` is a complementary domain of `J₁ + J₂` missing
`M`; `U` is a domain missing `M` with boundary the simple closed curve `L + L'`, lying on the side
of `J₁ + L` away from `J₂` (`hUside`). Then `M − {A, B}` is the union of the separated sets
`X₁ = M · (E₁ + J₁°)` and `X₂ = M · (E₂ + J₂° + L°)`, where `E₁` (`E₂`) is the side of `J₁ + L`
(`J₂ + L`) not containing `J₂°` (`J₁°`).

*The difficulty of the commission (§2 C) is that `L°` lies in the closure of both `E₁` and `E₂`.*
It is met by `theta_no_common_side` applied to the θ-curve `L' + L + J₂`: a point of `M · E₁` not
on `L'` is outside `U` and outside `E₂`, so it is not on the side of `L' + J₂` that contains `L°`;
hence `M · E₁` does not accumulate at `L°`. -/
theorem theta_separation_core {M : Set Pt} {A B : Pt} {J₁ J₂ L L' D U : Set Pt}
    (hJ₁ : TArc A B J₁) (hJ₂ : TArc A B J₂) (hL : TArc A B L) (hL' : TArc A B L')
    (h12 : J₁ ∩ J₂ = {A, B}) (h1L : J₁ ∩ L = {A, B}) (h2L : J₂ ∩ L = {A, B})
    (hLL' : L ∩ L' = {A, B}) (hθM : J₁ ∪ J₂ ∪ L ⊆ M)
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hDne : D.Nonempty) (hDf : frontier D = J₁ ∪ J₂)
    (hDM : Disjoint D M) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUf : frontier U = L ∪ L')
    (hUM : Disjoint U M) {j₂ : Pt} (hj₂ : j₂ ∈ J₂ \ {A, B})
    (hUside : Disjoint U (connectedComponentIn (J₁ ∪ L)ᶜ j₂)) :
    ∃ X₁ X₂ : Set Pt, X₁ ∪ X₂ = M \ {A, B} ∧ X₁.Nonempty ∧ X₂.Nonempty ∧
      Disjoint (closure X₁) X₂ ∧ Disjoint X₁ (closure X₂) := by
  have h21 : J₂ ∩ J₁ = {A, B} := by rw [inter_comm]; exact h12
  have hL1 : L ∩ J₁ = {A, B} := by rw [inter_comm]; exact h1L
  have hL2 : L ∩ J₂ = {A, B} := by rw [inter_comm]; exact h2L
  have hL'L : L' ∩ L = {A, B} := by rw [inter_comm]; exact hLL'
  have hAB1 : ({A, B} : Set Pt) ⊆ J₁ := by
    rintro z (rfl | rfl); exacts [hJ₁.left_mem, hJ₁.right_mem]
  have hABL : ({A, B} : Set Pt) ⊆ L := by
    rintro z (rfl | rfl); exacts [hL.left_mem, hL.right_mem]
  have hABL' : ({A, B} : Set Pt) ⊆ L' := by
    rintro z (rfl | rfl); exacts [hL'.left_mem, hL'.right_mem]
  have hAB2 : ({A, B} : Set Pt) ⊆ J₂ := by
    rintro z (rfl | rfl); exacts [hJ₂.left_mem, hJ₂.right_mem]
  obtain ⟨j₁, hj₁⟩ := hJ₁.nonempty_diff
  obtain ⟨l, hl⟩ := hL.nonempty_diff
  obtain ⟨l', hl'⟩ := hL'.nonempty_diff
  have hj₁M : j₁ ∈ M := hθM (Or.inl (Or.inl hj₁.1))
  have hj₂M : j₂ ∈ M := hθM (Or.inl (Or.inr hj₂.1))
  have hlM : l ∈ M := hθM (Or.inr hl.1)
  -- the sides `E₁`, `E₂`
  obtain ⟨S₁, E₁, hS₁o, hS₁c, hE₁o, hE₁c, hSE₁, hU₁, hfS₁, hfE₁, hJ₂S₁⟩ :=
    jordan_side ⟨A, B, J₁, L, hJ₁, hL, h1L, rfl⟩ hJ₂.isPreconnected_diff
      (disjoint_left.mpr fun y hy h => h.elim (not_mem_of_inter h12 hy) (not_mem_of_inter hL2 hy))
  obtain ⟨S₂, E₂, hS₂o, hS₂c, hE₂o, hE₂c, hSE₂, hU₂, hfS₂, hfE₂, hJ₁S₂⟩ :=
    jordan_side ⟨A, B, J₂, L, hJ₂, hL, h2L, rfl⟩ hJ₁.isPreconnected_diff
      (disjoint_left.mpr fun y hy h => h.elim (not_mem_of_inter h21 hy) (not_mem_of_inter hL1 hy))
  have hE₁Γ := disjoint_frontier_of_isOpen hE₁o hfE₁
  have hE₂Γ := disjoint_frontier_of_isOpen hE₂o hfE₂
  have hS₁Γ := disjoint_frontier_of_isOpen hS₁o hfS₁
  have hS₂Γ := disjoint_frontier_of_isOpen hS₂o hfS₂
  have hE₁J₂ : Disjoint E₁ J₂ := by
    refine disjoint_left.mpr fun z hz hz2 => ?_
    by_cases hzab : z ∈ ({A, B} : Set Pt)
    · exact disjoint_left.mp hE₁Γ hz (Or.inl (hAB1 hzab))
    · exact disjoint_left.mp hSE₁ (hJ₂S₁ ⟨hz2, hzab⟩) hz
  have hE₂J₁ : Disjoint E₂ J₁ := by
    refine disjoint_left.mpr fun z hz hz1 => ?_
    by_cases hzab : z ∈ ({A, B} : Set Pt)
    · exact disjoint_left.mp hE₂Γ hz (Or.inl (hAB2 hzab))
    · exact disjoint_left.mp hSE₂ (hJ₁S₂ ⟨hz1, hzab⟩) hz
  have hE₁S₂ : E₁ ⊆ S₂ := sub_side_of_closure hS₂o hE₂o hSE₂ hU₂ hfE₂ hJ₁S₂ hE₁c
    (disjoint_union_right.mpr ⟨hE₁J₂, hE₁Γ.mono_right subset_union_right⟩) hJ₁.nonempty_diff
    fun z hz => frontier_subset_closure (hfE₁ ▸ Or.inl hz.1)
  have hE₁E₂ : Disjoint E₁ E₂ := disjoint_left.mpr fun z hz hz' =>
    disjoint_left.mp hSE₂ (hE₁S₂ hz) hz'
  have hS₁eq : connectedComponentIn (J₁ ∪ L)ᶜ j₂ = S₁ := side_eq_cc hS₁c hfS₁ hS₁Γ (hJ₂S₁ hj₂)
  have hS₂eq : connectedComponentIn (J₂ ∪ L)ᶜ j₁ = S₂ := side_eq_cc hS₂c hfS₂ hS₂Γ (hJ₁S₂ hj₁)
  -- `U` lies in `E₁`
  have hUE₁ : U ⊆ E₁ := by
    intro u hu
    have hu' : u ∈ (J₁ ∪ L)ᶜ := fun h => disjoint_left.mp hUM hu
      (h.elim (fun h => hθM (Or.inl (Or.inl h))) fun h => hθM (Or.inr h))
    rw [← hU₁] at hu'
    exact hu'.resolve_left fun h => disjoint_left.mp hUside hu (hS₁eq ▸ h)
  have hL'sub : L' ⊆ E₁ ∪ (J₁ ∪ L) := by
    intro z hz
    have : z ∈ closure U := frontier_subset_closure (hUf ▸ Or.inr hz)
    have := closure_mono hUE₁ this
    rwa [closure_eq_self_union_frontier, hfE₁] at this
  have hL'J₂ : L' ∩ J₂ = {A, B} := by
    apply subset_antisymm
    · rintro z ⟨hz, hz2⟩
      rcases hL'sub hz with h | h | h
      · exact (disjoint_left.mp hE₁J₂ h hz2).elim
      · exact h12 ▸ ⟨h, hz2⟩
      · exact h2L ▸ ⟨hz2, h⟩
    · exact fun z hz => ⟨hABL' hz, hAB2 hz⟩
  -- every point of `M` off the θ-curve lies in `E₁ ∪ E₂`
  have hcover : ∀ m ∈ M, m ∉ J₁ ∪ J₂ ∪ L → m ∈ E₁ ∪ E₂ := by
    intro m hmM hmθ
    by_contra hne
    simp only [mem_union, not_or] at hne hmθ
    have hm1 : m ∈ S₁ := by
      have : m ∈ S₁ ∪ E₁ := hU₁ ▸ fun h => h.elim hmθ.1.1 hmθ.2
      exact this.resolve_right hne.1
    have hm2 : m ∈ S₂ := by
      have : m ∈ S₂ ∪ E₂ := hU₂ ▸ fun h => h.elim hmθ.1.2 hmθ.2
      exact this.resolve_right hne.2
    refine theta_no_common_side hJ₁ hJ₂ hL h12 h1L h2L hj₁ hj₂ hl
      (by simp only [mem_union, not_or]; exact ⟨⟨hmθ.1.1, hmθ.1.2⟩, hmθ.2⟩) ?_
      (hS₂eq ▸ hm2) (hS₁eq ▸ hm1)
    exact mem_cc_of_not_mem_domain ⟨A, B, J₁, J₂, hJ₁, hJ₂, h12, rfl⟩ hDo hDc hDne hDf
      (fun h => disjoint_left.mp hDM h hmM) (fun h => h.elim hmθ.1.1 hmθ.1.2)
      (fun h => disjoint_left.mp hDM h hlM)
      (fun h => h.elim (not_mem_of_inter h1L hl) (not_mem_of_inter h2L hl))
  -- the side `S'` of `L' + J₂` containing `L°`
  set S' := connectedComponentIn (L' ∪ J₂)ᶜ l with hS'def
  have hS'o : IsOpen S' := (hL'.isClosed.union hJ₂.isClosed).isOpen_compl.connectedComponentIn
  have hLS' : L \ {A, B} ⊆ S' :=
    hL.isPreconnected_diff.subset_connectedComponentIn hl fun z hz h =>
      h.elim (not_mem_of_inter hL'L hz) (not_mem_of_inter h2L hz)
  have hE₂ne : E₂.Nonempty := nonempty_of_frontier (hfE₂ ▸ Or.inl hJ₂.left_mem : A ∈ frontier E₂)
  have hME₁ : M ∩ E₁ ⊆ S'ᶜ ∪ L' := by
    rintro m ⟨hmM, hmE₁⟩
    by_cases hmL' : m ∈ L'
    · exact Or.inr hmL'
    left
    intro hmS'
    have hmL : m ∉ L := fun h => disjoint_left.mp hE₁Γ hmE₁ (Or.inr h)
    have hm2 : m ∉ J₂ := fun h => disjoint_left.mp hE₁J₂ hmE₁ h
    have hl'L : l' ∉ L := not_mem_of_inter hLL' hl'
    have hl'2 : l' ∉ J₂ := not_mem_of_inter (by rw [inter_comm]; exact hL'J₂) hl'
    have hl'E₂ : l' ∉ E₂ := by
      intro h
      rcases hL'sub hl'.1 with h' | h' | h'
      · exact disjoint_left.mp hE₁E₂ h' h
      · exact disjoint_left.mp hE₂J₁ h h'
      · exact disjoint_left.mp hE₂Γ h (Or.inr h')
    have hj₂L' : j₂ ∉ L' := not_mem_of_inter hL'J₂ hj₂
    have hj₂L : j₂ ∉ L := not_mem_of_inter hL2 hj₂
    refine theta_no_common_side hL' hL hJ₂ hL'L hL'J₂ hL2 hl' hl hj₂
      (by simp only [mem_union, not_or]; exact ⟨⟨hmL', hmL⟩, hm2⟩) ?_ ?_ hmS'
    · exact mem_cc_of_not_mem_domain ⟨A, B, L', L, hL', hL, hL'L, rfl⟩ hUo hUc
        (nonempty_of_frontier (hUf ▸ Or.inl hL.left_mem : A ∈ frontier U))
        (by rw [hUf, union_comm])
        (fun h => disjoint_left.mp hUM h hmM) (fun h => h.elim hmL' hmL)
        (fun h => disjoint_left.mp hE₁J₂ (hUE₁ h) hj₂.1) (fun h => h.elim hj₂L' hj₂L)
    · exact mem_cc_of_not_mem_domain ⟨A, B, L, J₂, hL, hJ₂, hL2, rfl⟩ hE₂o hE₂c hE₂ne
        (by rw [hfE₂, union_comm]) (fun h => disjoint_left.mp hE₁E₂ hmE₁ h)
        (fun h => h.elim hmL hm2) hl'E₂ (fun h => h.elim hl'L hl'2)
  -- the separation
  refine ⟨M ∩ (E₁ ∪ J₁ \ {A, B}), M ∩ (E₂ ∪ J₂ \ {A, B} ∪ L \ {A, B}), ?_,
    ⟨j₁, hj₁M, Or.inr hj₁⟩, ⟨j₂, hj₂M, Or.inl (Or.inr hj₂)⟩, ?_, ?_⟩
  · ext m
    simp only [mem_union, mem_inter_iff, mem_diff]
    constructor
    · rintro (⟨hm, h | h⟩ | ⟨hm, (h | h) | h⟩)
      · exact ⟨hm, fun hab => disjoint_left.mp hE₁Γ h (Or.inl (hAB1 hab))⟩
      · exact ⟨hm, h.2⟩
      · exact ⟨hm, fun hab => disjoint_left.mp hE₂Γ h (Or.inl (hAB2 hab))⟩
      · exact ⟨hm, h.2⟩
      · exact ⟨hm, h.2⟩
    · rintro ⟨hm, hab⟩
      by_cases h1 : m ∈ J₁
      · exact Or.inl ⟨hm, Or.inr ⟨h1, hab⟩⟩
      by_cases h2 : m ∈ J₂
      · exact Or.inr ⟨hm, Or.inl (Or.inr ⟨h2, hab⟩)⟩
      by_cases hl' : m ∈ L
      · exact Or.inr ⟨hm, Or.inr ⟨hl', hab⟩⟩
      rcases hcover m hm (by simp only [mem_union, not_or]; exact ⟨⟨h1, h2⟩, hl'⟩) with h | h
      · exact Or.inl ⟨hm, Or.inl h⟩
      · exact Or.inr ⟨hm, Or.inl (Or.inl h)⟩
  · have hcl : closure (M ∩ (E₁ ∪ J₁ \ {A, B})) ⊆ ((E₁ ∪ (J₁ ∪ L)) ∩ (S'ᶜ ∪ L')) ∪ J₁ := by
      rw [inter_union_distrib_left, closure_union]
      refine union_subset_union (subset_inter ?_ ?_) ?_
      · rw [← hfE₁, ← closure_eq_self_union_frontier]; exact closure_mono inter_subset_right
      · exact closure_minimal hME₁ (hS'o.isClosed_compl.union hL'.isClosed)
      · exact closure_minimal (inter_subset_right.trans diff_subset) hJ₁.isClosed
    refine disjoint_left.mpr fun z hz hz2 => ?_
    rcases hcl hz with ⟨h | h | h, h'⟩ | h
    · -- `z ∈ E₁`
      rcases hz2.2 with (h2 | h2) | h2
      · exact disjoint_left.mp hE₁E₂ h h2
      · exact disjoint_left.mp hE₁J₂ h h2.1
      · exact disjoint_left.mp hE₁Γ h (Or.inr h2.1)
    · rcases hz2.2 with (h2 | h2) | h2
      · exact disjoint_left.mp hE₂J₁ h2 h
      · exact not_mem_of_inter h12 h2 h
      · exact not_mem_of_inter h1L h2 h
    · rcases hz2.2 with (h2 | h2) | h2
      · exact disjoint_left.mp hE₂Γ h2 (Or.inr h)
      · exact not_mem_of_inter hL2 h2 h
      · rcases h' with h' | h'
        · exact h' (hLS' h2)
        · exact not_mem_of_inter hL'L h2 h'
    · rcases hz2.2 with (h2 | h2) | h2
      · exact disjoint_left.mp hE₂J₁ h2 h
      · exact not_mem_of_inter h12 h2 h
      · exact not_mem_of_inter h1L h2 h
  · have hEcl : IsClosed (E₂ ∪ (J₂ ∪ L)) := by
      rw [← hfE₂, ← closure_eq_self_union_frontier]; exact isClosed_closure
    have hcl : closure (M ∩ (E₂ ∪ J₂ \ {A, B} ∪ L \ {A, B})) ⊆ E₂ ∪ (J₂ ∪ L) := by
      refine closure_minimal (inter_subset_right.trans ?_) hEcl
      rintro z ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.1)
      · exact Or.inr (Or.inr h.1)
    refine disjoint_left.mpr fun z hz hz2 => ?_
    rcases hcl hz2 with h2 | h2 | h2
    · rcases hz.2 with h | h
      · exact disjoint_left.mp hE₁E₂ h h2
      · exact disjoint_left.mp hE₂J₁ h2 h.1
    · rcases hz.2 with h | h
      · exact disjoint_left.mp hE₁J₂ h h2
      · exact not_mem_of_inter h21 h h2
    · rcases hz.2 with h | h
      · exact disjoint_left.mp hE₁Γ h (Or.inr h2)
      · exact not_mem_of_inter hL1 h h2

/-- **Item C, step 5** (both orientations): as `theta_separation_core`, with the side of `U`
determined. `U` is a domain missing `M` and `D`; it lies on the side of `J₁ + L` away from `J₂` or
on the side of `J₂ + L` away from `J₁`, since otherwise a point of `U` would be on the common side
excluded by `theta_no_common_side`. -/
theorem theta_separation {M : Set Pt} {A B : Pt} {J₁ J₂ L L' D U : Set Pt}
    (hJ₁ : TArc A B J₁) (hJ₂ : TArc A B J₂) (hL : TArc A B L) (hL' : TArc A B L')
    (h12 : J₁ ∩ J₂ = {A, B}) (h1L : J₁ ∩ L = {A, B}) (h2L : J₂ ∩ L = {A, B})
    (hLL' : L ∩ L' = {A, B}) (hθM : J₁ ∪ J₂ ∪ L ⊆ M)
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hDne : D.Nonempty) (hDf : frontier D = J₁ ∪ J₂)
    (hDM : Disjoint D M) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUf : frontier U = L ∪ L') (hUM : Disjoint U M) (hUD : Disjoint U D) :
    ∃ X₁ X₂ : Set Pt, X₁ ∪ X₂ = M \ {A, B} ∧ X₁.Nonempty ∧ X₂.Nonempty ∧
      Disjoint (closure X₁) X₂ ∧ Disjoint X₁ (closure X₂) := by
  obtain ⟨j₁, hj₁⟩ := hJ₁.nonempty_diff
  obtain ⟨j₂, hj₂⟩ := hJ₂.nonempty_diff
  obtain ⟨l, hl⟩ := hL.nonempty_diff
  have hUθ : ∀ u ∈ U, u ∉ J₁ ∪ J₂ ∪ L := fun u hu h => disjoint_left.mp hUM hu (hθM h)
  have absorb : ∀ {F : Set Pt} {k : Pt}, (∀ u ∈ U, u ∉ F) →
      (U ∩ connectedComponentIn Fᶜ k).Nonempty → U ⊆ connectedComponentIn Fᶜ k := by
    rintro F k hUF ⟨u, hu, huk⟩
    rw [connectedComponentIn_eq huk]
    exact hUc.subset_connectedComponentIn hu hUF
  by_cases h1 : (U ∩ connectedComponentIn (J₁ ∪ L)ᶜ j₂).Nonempty
  · by_cases h2 : (U ∩ connectedComponentIn (J₂ ∪ L)ᶜ j₁).Nonempty
    · exfalso
      obtain ⟨u, hu⟩ := hUne
      have hu1 := absorb (fun u hu h => hUθ u hu (h.elim (fun h => Or.inl (Or.inl h))
        fun h => Or.inr h)) h1 hu
      have hu2 := absorb (fun u hu h => hUθ u hu (h.elim (fun h => Or.inl (Or.inr h))
        fun h => Or.inr h)) h2 hu
      have huθ := hUθ u hu
      simp only [mem_union, not_or] at huθ
      refine theta_no_common_side hJ₁ hJ₂ hL h12 h1L h2L hj₁ hj₂ hl
        (by simp only [mem_union, not_or]; exact huθ) ?_ hu2 hu1
      exact mem_cc_of_not_mem_domain ⟨A, B, J₁, J₂, hJ₁, hJ₂, h12, rfl⟩ hDo hDc hDne hDf
        (fun h => disjoint_left.mp hUD hu h) (fun h => h.elim huθ.1.1 huθ.1.2)
        (fun h => disjoint_left.mp hDM h (hθM (Or.inr hl.1)))
        (fun h => h.elim (not_mem_of_inter h1L hl) (not_mem_of_inter h2L hl))
    · rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h2
      have h21 : J₂ ∩ J₁ = {A, B} := by rw [inter_comm]; exact h12
      exact theta_separation_core hJ₂ hJ₁ hL hL' h21 h2L h1L hLL'
        (by rw [union_comm J₂ J₁]; exact hθM) hDo hDc hDne (by rw [hDf, union_comm]) hDM hUo hUc
        hUf hUM hj₁ h2
  · rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h1
    exact theta_separation_core hJ₁ hJ₂ hL hL' h12 h1L h2L hLL' hθM hDo hDc hDne hDf hDM hUo hUc
      hUf hUM hj₂ h1

end HPC.Jones
