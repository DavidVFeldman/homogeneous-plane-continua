import HPC.Plane.Enc2
import HPC.Moore.M25Plane

/-!
# Bing 1951 (Duke), Theorem 6, by the compact form of Janiszewski's theorem

The repository proves Theorem 6 (`theorem6_1951`, `Enc2.lean`) as a corollary of Theorem 7: the
`janiszewski` field of `PlaneFacts` is only asserted for polygonal sets, so the circular-chain
argument needs the links to be polygon interiors, which forces the general-position cover of
Theorem 7. Janiszewski's theorem for *compact* sets is also proved in the repository, by logarithms
(`HPC.Moore.janiszewski_compact`, `HPC/Moore/M25Plane.lean`). With it the batch-118 proof goes
through for an arbitrary open cover with no triple points, and Theorem 6 follows directly from the
notched-square cover, with no general position, no cross-cuts and no polygonality lemma. This is
the route followed by the lecture notes, Volume 4 (`doc/lecture-notes/vol4/`).

* `janiszewski_polygonal_of_compact`: the polygonal form is a special case of the compact one.
* `exists_theta_point_open`: Bing's point `q` for arbitrary open `h₁`, `h₂` (the proof of
  `PlaneFacts.exists_theta_point`, with `A := frontier h₁ ∩ closure (U ∩ h₁ ∩ h₂)`, which is compact,
  in place of the polygonal `Γ₁ ∩ closure (U ∩ h₁ ∩ h₂)`).
* `compFamily_no_circular_open`, `treeChain_of_cover_open`: `compFamily_no_circular` and
  `treeChain_of_cover` without the hypothesis that the components are polygon interiors.
* `theorem6_direct`: Theorem 6 from `exists_notched_cover_bdd`, `enclose_holds` and
  `treeChain_of_cover_open`.
-/

namespace HPC.Plane

open Set Topology Metric

open scoped Classical

/-- **Janiszewski for polygonal sets, from the compact form** (polygonal sets are compact). -/
theorem janiszewski_polygonal_of_compact {A B : Set Pt} (hA : IsPolygonal A)
    (hB : IsPolygonal B) (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) {x y : Pt}
    (hx : ¬ SeparatesPts A x y) (hy : ¬ SeparatesPts B x y) : ¬ SeparatesPts (A ∪ B) x y :=
  HPC.Moore.janiszewski_compact hA.isCompact hB.isCompact hAB hx hy

/-- **Bing's point `q`, for arbitrary open sets.** Let `Γ` be a simple closed polygon decomposed
into three connected sets `α₁` (containing `p₁`, `p₂`), `α₂` (containing `p₂`, `p₃`) and `β`
(containing `p₃`, `p₁`). Let `h₁ ⊇ α₁`, `h₂ ⊇ α₂`, `V ⊇ β` be open with `V ∩ h₁ ∩ h₂ = ∅`. Then some
point `q` of the interior of `Γ` is a frontier point of `h₁` and of `h₂` and lies in the closure of
`h₁ ∩ h₂`. -/
theorem exists_theta_point_open (hPF : PlaneFacts) {Γ α₁ α₂ β : Set Pt} {p₁ p₂ p₃ : Pt}
    (hΓ : IsSimpleClosedPolygon Γ) (hdec : α₁ ∪ α₂ ∪ β = Γ)
    (h₁c : IsConnected α₁) (h₂c : IsConnected α₂) (hβc : IsConnected β)
    (hp₂ : p₂ ∈ α₁ ∩ α₂) (hp₃ : p₃ ∈ α₂ ∩ β) (hp₁ : p₁ ∈ β ∩ α₁)
    {h₁ h₂ V : Set Pt} (ho₁ : IsOpen h₁) (ho₂ : IsOpen h₂) (hoV : IsOpen V)
    (hα₁ : α₁ ⊆ h₁) (hα₂ : α₂ ⊆ h₂) (hβ : β ⊆ V) (hV : V ∩ h₁ ∩ h₂ = ∅) :
    ∃ q ∈ polyInterior Γ, q ∈ frontier h₁ ∧ q ∈ frontier h₂ ∧ q ∈ closure (h₁ ∩ h₂) := by
  obtain ⟨E, hU, hE, hJ, hd, hUb, hfr, hfU, hfE, -⟩ := hPF.split hΓ
  set U := polyInterior Γ with hUdef
  have hsub₁ : α₁ ⊆ Γ := hdec ▸ subset_union_left.trans subset_union_left
  have hsub₂ : α₂ ⊆ Γ := hdec ▸ subset_union_right.trans subset_union_left
  have hsubβ : β ⊆ Γ := hdec ▸ subset_union_right
  obtain ⟨S₁, hS₁c, hS₁, hl₁⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsub₁ h₁c.isPreconnected ho₁ hα₁
  obtain ⟨S₂, hS₂c, hS₂, hl₂⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsub₂ h₂c.isPreconnected ho₂ hα₂
  obtain ⟨S₃, hS₃c, hS₃, hl₃⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsubβ hβc.isPreconnected hoV hβ
  have hmeet : ∀ {S S' : Set Pt} {w : Pt}, w ∈ Γ → (∃ r > 0, U ∩ ball w r ⊆ S) →
      (∃ r > 0, U ∩ ball w r ⊆ S') → (S ∩ S').Nonempty := by
    rintro S S' w hw ⟨r, hr, hrS⟩ ⟨r', hr', hrS'⟩
    obtain ⟨y, hyU, hy⟩ := Metric.mem_closure_iff.1 (hfU w hw) _ (lt_min hr hr')
    rw [dist_comm] at hy
    exact ⟨y, hrS ⟨hyU, (lt_min_iff.1 hy).1⟩, hrS' ⟨hyU, (lt_min_iff.1 hy).2⟩⟩
  obtain ⟨x, hx₁, hx₂⟩ := hmeet (hsub₁ hp₂.1) (hl₁ p₂ hp₂.1) (hl₂ p₂ hp₂.2)
  obtain ⟨y, hy₂, hy₃⟩ := hmeet (hsub₂ hp₃.1) (hl₂ p₃ hp₃.1) (hl₃ p₃ hp₃.2)
  obtain ⟨z, hz₁, hz₃⟩ := hmeet (hsub₁ hp₁.2) (hl₁ p₁ hp₁.2) (hl₃ p₁ hp₁.1)
  by_contra hno
  push_neg at hno
  -- basic facts
  have hUΓ : Disjoint U Γ := by
    rw [Set.disjoint_left]; intro u hu huΓ
    have : u ∈ U ∪ E := Or.inl hu
    rw [← hJ] at this; exact this huΓ
  have hVcl : Disjoint V (closure (h₁ ∩ h₂)) := by
    refine Disjoint.closure_right ?_ hoV
    rw [Set.disjoint_left]; intro u hu hu'
    have : u ∈ V ∩ h₁ ∩ h₂ := ⟨⟨hu, hu'.1⟩, hu'.2⟩
    rw [hV] at this; exact this
  have hfr₁ : Disjoint h₁ (frontier h₁) := by
    rw [ho₁.frontier_eq]; exact disjoint_sdiff_right
  have hfr₂ : Disjoint h₂ (frontier h₂) := by
    rw [ho₂.frontier_eq]; exact disjoint_sdiff_right
  have hO : IsOpen (U ∩ h₁ ∩ h₂) := (hU.inter ho₁).inter ho₂
  have hxO : x ∈ U ∩ h₁ ∩ h₂ := ⟨⟨(hS₁ hx₁).1, (hS₁ hx₁).2⟩, (hS₂ hx₂).2⟩
  set C := connectedComponentIn (U ∩ h₁ ∩ h₂) x with hC
  have hCO : C ⊆ U ∩ h₁ ∩ h₂ := connectedComponentIn_subset _ _
  have hCo : IsOpen C := hO.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hxO
  have hclO : closure (U ∩ h₁ ∩ h₂) ⊆ closure (h₁ ∩ h₂) :=
    closure_mono fun u hu => ⟨hu.1.2, hu.2⟩
  have hclOU : closure (U ∩ h₁ ∩ h₂) ⊆ U ∪ Γ := by
    refine (closure_mono fun u hu => hu.1.1).trans ?_
    rw [closure_eq_self_union_frontier, hfr]
  set A := frontier h₁ ∩ closure (U ∩ h₁ ∩ h₂) with hA
  set B := frontier h₂ ∩ closure (U ∩ h₁ ∩ h₂) with hB
  have hclK : IsCompact (closure (U ∩ h₁ ∩ h₂)) :=
    (hUb.subset fun u hu => hu.1.1).isCompact_closure
  have hAp : IsCompact (A ∪ Γ) :=
    (hclK.inter_left isClosed_frontier).union hΓ.isPolygonal.isCompact
  have hBp : IsCompact (B ∪ Γ) :=
    (hclK.inter_left isClosed_frontier).union hΓ.isPolygonal.isCompact
  have hAB : A ∩ B = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro a ⟨⟨haΓ₁, haC⟩, haΓ₂, -⟩
    have ha₁ : a ∈ frontier h₁ := haΓ₁
    have ha₂ : a ∈ frontier h₂ := haΓ₂
    rcases hclOU haC with haU | haΓ
    · exact hno a haU ha₁ ha₂ (hclO haC)
    · rw [← hdec] at haΓ
      rcases haΓ with (h | h) | h
      · exact hfr₁.notMem_of_mem_left (hα₁ h) ha₁
      · exact hfr₂.notMem_of_mem_left (hα₂ h) ha₂
      · exact hVcl.notMem_of_mem_left (hβ h) (hclO haC)
  have hΓconn : IsConnected Γ := by
    rw [← hdec]
    exact (h₁c.union ⟨p₂, hp₂⟩ h₂c).union ⟨p₃, Or.inr hp₃.1, hp₃.2⟩ hβc
  have hinter : IsConnected ((A ∪ Γ) ∩ (B ∪ Γ)) := by
    rw [← inter_union_distrib_right, hAB, empty_union]; exact hΓconn
  -- points avoid the sets
  have hS₁A : S₁ ⊆ (A ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hfr₁.notMem_of_mem_left (hS₁ hu).2 h.1
    · exact hUΓ.notMem_of_mem_left (hS₁ hu).1 h
  have hS₃A : S₃ ⊆ (A ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hVcl.notMem_of_mem_left (hS₃ hu).2 (hclO h.2)
    · exact hUΓ.notMem_of_mem_left (hS₃ hu).1 h
  have hS₂B : S₂ ⊆ (B ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hfr₂.notMem_of_mem_left (hS₂ hu).2 h.1
    · exact hUΓ.notMem_of_mem_left (hS₂ hu).1 h
  -- `B ∪ Γ` does not separate `x` from `y`
  have hnB : ¬ SeparatesPts (B ∪ Γ) x y := by
    rintro ⟨-, -, h⟩
    exact h (hS₂c.subset_connectedComponentIn hx₂ hS₂B hy₂)
  -- `A ∪ B ∪ Γ` separates `x` from `y`
  have hsepAB : SeparatesPts ((A ∪ Γ) ∪ (B ∪ Γ)) x y := by
    have hyV : y ∈ V := (hS₃ hy₃).2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact hS₁A hx₁ h
      · exact hS₂B hx₂ h
    · rcases h with h | h
      · exact hS₃A hy₃ h
      · exact hS₂B hy₂ h
    · set K := connectedComponentIn ((A ∪ Γ) ∪ (B ∪ Γ))ᶜ x with hK
      have hKc : IsPreconnected K := isPreconnected_connectedComponentIn
      have hKsub : K ⊆ ((A ∪ Γ) ∪ (B ∪ Γ))ᶜ := connectedComponentIn_subset _ _
      have hxK : x ∈ K := mem_connectedComponentIn (fun h => by
        rcases h with h | h
        · exact hS₁A hx₁ h
        · exact hS₂B hx₂ h)
      have hKU : K ⊆ U := by
        have hKUE : K ⊆ U ∪ E := by
          rw [← hJ]; intro u hu huΓ; exact hKsub hu (Or.inl (Or.inr huΓ))
        rcases isPreconnected_iff_subset_of_disjoint.1 hKc U E hU hE hKUE
          (by rw [hd.inter_eq, inter_empty]) with h | h
        · exact h
        · exact absurd (h hxK) (hd.notMem_of_mem_left (hS₁ hx₁).1)
      have hKC : K ⊆ C := by
        have hcov : K ⊆ C ∪ (closure C)ᶜ := by
          intro u hu
          by_cases huc : u ∈ closure C
          · left
            have huO : u ∈ closure (U ∩ h₁ ∩ h₂) := closure_mono hCO huc
            have huA : u ∉ frontier h₁ := fun h' =>
              hKsub hu (Or.inl (Or.inl ⟨h', huO⟩))
            have huB : u ∉ frontier h₂ := fun h' =>
              hKsub hu (Or.inr (Or.inl ⟨h', huO⟩))
            have hu₁ : u ∈ h₁ := by
              by_contra h'
              exact huA (by rw [ho₁.frontier_eq]; exact ⟨closure_mono
                (hCO.trans fun v hv => hv.1.2) huc, h'⟩)
            have hu₂ : u ∈ h₂ := by
              by_contra h'
              exact huB (by rw [ho₂.frontier_eq]; exact ⟨closure_mono
                (hCO.trans fun v hv => hv.2) huc, h'⟩)
            exact mem_connectedComponentIn_of_mem_closure hO ⟨⟨hKU hu, hu₁⟩, hu₂⟩ huc
          · exact Or.inr huc
        rcases isPreconnected_iff_subset_of_disjoint.1 hKc C (closure C)ᶜ hCo
          isClosed_closure.isOpen_compl hcov (by
            refine eq_empty_of_forall_notMem ?_
            rintro u ⟨-, hu1, hu2⟩; exact hu2 (subset_closure hu1)) with h | h
        · exact h
        · exact absurd (subset_closure hxC) (h hxK)
      exact hVcl.notMem_of_mem_left hyV (subset_closure ⟨(hCO (hKC h)).1.2, (hCO (hKC h)).2⟩)
  -- so `A ∪ Γ` separates `x` from `y`
  have hsepA : SeparatesPts (A ∪ Γ) x y := by
    by_contra hnA
    exact HPC.Moore.janiszewski_compact hAp hBp (Or.inl hinter) hnA hnB hsepAB
  -- but `S₁ ∪ S₃` joins them off `A ∪ Γ`
  obtain ⟨-, -, hfin⟩ := hsepA
  exact hfin ((hS₁c.union z hz₁ hz₃ hS₃c).subset_connectedComponentIn (Or.inl hx₁)
    (union_subset hS₁A hS₃A) (Or.inr hy₃))


/-- **No circular chain of components** (`compFamily_no_circular` without the hypothesis that the
components are polygon interiors): for a simple closed polygon `J` and an open cover `D` of its
interior with no triple points, no subcollection of the components of the sets `polyInterior J ∩ d`
(`d ∈ D`) is a circular chain. -/
theorem compFamily_no_circular_open (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d)
    (hD : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    (hcov : polyInterior J ⊆ ⋃ d ∈ D, d)
    (G : Finset (Set Pt))
    (hG : ∀ h ∈ G, h ∈ compFamily (polyInterior J) D) : ¬ IsCircularChain G := by
  rintro ⟨m, hm, d, hinj, rfl, hcirc⟩
  set d₀ := polyInterior J with hd₀
  have hd₀o : IsOpen d₀ := (hPF.polyInterior_eq hJ).1
  have hmem : ∀ i, d i ∈ compFamily d₀ D := fun i => hG _ (Finset.mem_image_of_mem d
    (Finset.mem_univ i))
  have hP : ∀ i, IsOpen (d i) ∧ IsConnected (d i) ∧ d i ⊆ d₀ := fun i =>
    compFamily_props hd₀o hopen (hmem i)
  -- the chain in `ℕ`-indexing
  set e : ℕ → Set Pt := fun j => if h : j < m then d ⟨j, h⟩ else ∅ with he
  have he' : ∀ (j : ℕ) (h : j < m), e j = d ⟨j, h⟩ := fun j h => by simp [he, h]
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set A₂ := ⋃ j ∈ Set.Icc 2 (m - 1), e j with hA₂
  have hA₂o : IsOpen A₂ := isOpen_biUnion fun j hj => by
    rw [he' j (by simp at hj; omega)]; exact (hP _).1
  have hA₂c : IsConnected A₂ := by
    obtain ⟨z, hz⟩ := (hP ⟨2, by omega⟩).2.1.nonempty
    refine ⟨⟨z, mem_biUnion (x := 2) (by simp; omega) (by rw [he' 2 (by omega)]; exact hz)⟩, ?_⟩
    refine IsPreconnected.biUnion_of_chain Set.ordConnected_Icc (fun j hj => ?_) ?_
    · rw [he' j (by simp at hj; omega)]; exact (hP _).2.1.isPreconnected
    · intro j hj hj'
      simp only [Set.mem_Icc, Order.succ_eq_add_one] at hj hj' ⊢
      rw [he' j (by omega), he' (j + 1) (by omega)]
      refine (hcirc ⟨j, by omega⟩ ⟨j + 1, by omega⟩).2 (Or.inl ?_)
      simp only
      omega
  have hA₂sub : A₂ ⊆ d₀ := iUnion₂_subset fun j hj => by
    rw [he' j (by simp at hj; omega)]; exact (hP _).2.2
  have hne : ∀ i j : Fin m, i ≠ j → d i ≠ d j := fun i j h h' => h (hinj h')
  have h₀₁ : (d i₀ ∩ d i₁).Nonempty := (hcirc i₀ i₁).2 (Or.inl (by simp [i₀, i₁]))
  have h₁₂ : (d i₁ ∩ A₂).Nonempty := by
    obtain ⟨z, hz⟩ := (hcirc i₁ ⟨2, by omega⟩).2 (Or.inl (by simp [i₁]))
    exact ⟨z, hz.1, mem_biUnion (x := 2) (by simp; omega) (by rw [he' 2 (by omega)]; exact hz.2)⟩
  have h₂₀ : (A₂ ∩ d i₀).Nonempty := by
    obtain ⟨z, hz⟩ := (hcirc i₀ ⟨m - 1, by omega⟩).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact ⟨z, mem_biUnion (x := m - 1) (by simp; omega) (by rw [he' _ (by omega)]; exact hz.2),
      hz.1⟩
  have ht : d i₀ ∩ d i₁ ∩ A₂ = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro z ⟨⟨hz₀, hz₁⟩, hz₂⟩
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hz₂
    simp only [Set.mem_Icc] at hj
    rw [he' j (by omega)] at hzj
    have := compFamily_no_triple hD (hmem i₀) (hmem i₁) (hmem ⟨j, by omega⟩)
      (hne _ _ (by simp [i₀, i₁])) (hne _ _ (by simp [i₁, Fin.ext_iff]; omega))
      (hne _ _ (by simp [i₀, Fin.ext_iff]; omega))
    have hz : z ∈ d i₀ ∩ d i₁ ∩ d ⟨j, by omega⟩ := ⟨⟨hz₀, hz₁⟩, hzj⟩
    rw [this] at hz
    exact hz
  obtain ⟨Γ, α₀, α₁, α₂, p₀, p₁, p₂, hΓ, hdec, hc₀, hc₁, hc₂, hp₁, hp₂, hp₀, hs₀, hs₁, hs₂⟩ :=
    exists_theta_polygon (hP i₀).1 (hP i₁).1 hA₂o (hP i₀).2.1 (hP i₁).2.1 hA₂c h₀₁ h₁₂ h₂₀ ht
  obtain ⟨q, hqU, hq₀, hq₁, hqcl⟩ := exists_theta_point_open hPF hΓ hdec hc₀ hc₁ hc₂ hp₁ hp₂
    hp₀ (hP i₀).1 (hP i₁).1 hA₂o hs₀ hs₁ hs₂ (by
      rw [inter_assoc, inter_comm, ht])
  -- the interior of `Γ` lies in `d₀`
  have hΓd₀ : Γ ⊆ d₀ := by
    rw [← hdec]
    exact union_subset (union_subset (hs₀.trans (hP i₀).2.2) (hs₁.trans (hP i₁).2.2))
      (hs₂.trans hA₂sub)
  have hqd₀ : q ∈ d₀ := by
    by_contra hq
    obtain ⟨hWc, hWb⟩ := hPF.compl_polyInterior hJ
    exact (polyInterior_disjoint_of_unbounded hWc hWb
      (Set.disjoint_compl_left_iff_subset.2 hΓd₀)).notMem_of_mem_left hq hqU
  obtain ⟨dd, hdd, hqdd⟩ := mem_iUnion₂.1 (hcov hqd₀)
  obtain ⟨da, hda, xa, hxa, hA⟩ := hmem i₀
  obtain ⟨db, hdb, xb, hxb, hB⟩ := hmem i₁
  have hab : da ≠ db := by
    rintro rfl
    apply hne i₀ i₁ (by simp [i₀, i₁, Fin.ext_iff])
    rw [hA, hB]
    exact connectedComponentIn_eq_of_meet (by rw [← hA, ← hB]; exact h₀₁)
  obtain ⟨u, hu, hu'⟩ := mem_closure_iff.1 hqcl dd (hopen dd hdd) hqdd
  have hua : u ∈ da := by
    have := hu'.1; rw [hA] at this; exact (connectedComponentIn_subset _ _ this).2
  have hub : u ∈ db := by
    have := hu'.2; rw [hB] at this; exact (connectedComponentIn_subset _ _ this).2
  have hcase : dd = da ∨ dd = db := by
    by_contra hc
    push_neg at hc
    have := hD dd hdd da hda db hdb hc.1 hab hc.2
    have hu3 : u ∈ dd ∩ da ∩ db := ⟨⟨hu, hua⟩, hub⟩
    rw [this] at hu3
    exact hu3
  have hfr : ∀ (h : Set Pt), IsOpen h → q ∈ frontier h → q ∉ h := fun h ho hq hqh => by
    rw [ho.frontier_eq] at hq; exact hq.2 hqh
  rcases hcase with rfl | rfl
  · refine hfr _ (hP i₀).1 hq₀ ?_
    rw [hA]
    exact mem_connectedComponentIn_of_mem_closure (hd₀o.inter (hopen _ hdd)) ⟨hqd₀, hqdd⟩
      (hA ▸ closure_mono inter_subset_left hqcl)
  · refine hfr _ (hP i₁).1 hq₁ ?_
    rw [hB]
    exact mem_connectedComponentIn_of_mem_closure (hd₀o.inter (hopen _ hdd)) ⟨hqd₀, hqdd⟩
      (hB ▸ closure_mono inter_subset_right hqcl)


/-- **The tree chain from a cover** (`treeChain_of_cover` without the hypothesis that the
components are polygon interiors): if `M ⊆ polyInterior J` and `D` is a bounded open cover of
`polyInterior J` with no triple points and links of diameter `< ε`, finitely many components of the
sets `polyInterior J ∩ d` form a tree chain of mesh `< ε` covering `M`. -/
theorem treeChain_of_cover_open (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    {J : Set Pt} (hJ : IsSimpleClosedPolygon J) (hMJ : M ⊆ polyInterior J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d) (hbdd : ∀ d ∈ D, Bornology.IsBounded d)
    {ε : ℝ} (hdiam : ∀ d ∈ D, diam d < ε) (hcov : polyInterior J ⊆ ⋃ d ∈ D, d)
    (htriple : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅) :
    ∃ G : Finset (Set Pt), (∀ h ∈ G, h ∈ compFamily (polyInterior J) D) ∧ IsTreeChain G ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧ ∀ h ∈ G, (h ∩ M).Nonempty := by
  set d₀ := polyInterior J with hd₀
  have hd₀o : IsOpen d₀ := (hPF.polyInterior_eq hJ).1
  have hx : ∀ x ∈ M, ∃ d ∈ D, x ∈ d := fun x hx => by
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.1 (hcov (hMJ hx)); exact ⟨d, hd, hxd⟩
  choose! dx hdxD hxdx using hx
  set c : Pt → Set Pt := fun x => connectedComponentIn (d₀ ∩ dx x) x with hc
  have hcmem : ∀ x ∈ M, c x ∈ compFamily d₀ D := fun x hx =>
    ⟨dx x, hdxD x hx, x, ⟨hMJ hx, hxdx x hx⟩, rfl⟩
  obtain ⟨t, htM, htfin, htcov⟩ := hM.1.elim_finite_subcover_image (b := M) (c := c)
    (fun x hx => (compFamily_props hd₀o hopen (hcmem x hx)).1)
    (fun x hx => mem_iUnion₂.2 ⟨x, hx, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩⟩)
  set H := htfin.toFinset.image c with hH
  have hHmem : ∀ h ∈ H, ∃ x ∈ M, h = c x := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨x, htM (htfin.mem_toFinset.1 hx), rfl⟩
  have hHc : ∀ h ∈ H, h ∈ compFamily d₀ D := by
    intro h hh; obtain ⟨x, hx, rfl⟩ := hHmem h hh; exact hcmem x hx
  have hHo : ∀ h ∈ H, IsOpen h := fun h hh => (compFamily_props hd₀o hopen (hHc h hh)).1
  have hHcov : M ⊆ ⋃ h ∈ H, h := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (htcov hy)
    exact mem_iUnion₂.2 ⟨c x, Finset.mem_image.2 ⟨x, htfin.mem_toFinset.2 hx, rfl⟩, hyx⟩
  have hHM : ∀ h ∈ H, (h ∩ M).Nonempty := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    exact ⟨x, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩, hx⟩
  refine ⟨H, hHc, ⟨hHo, ?_, ?_, ?_⟩, ?_, hHcov, hHM⟩
  · exact isCoherent_of_minimal_cover hM.2 H hHo hHcov fun h hh => hHM h hh
  · intro A hA B hB C hC hAB hBC hAC
    exact compFamily_no_triple htriple (hHc A hA) (hHc B hB) (hHc C hC) hAB hBC hAC
  · intro G' hG'
    exact compFamily_no_circular_open hPF hJ hopen htriple hcov G' fun h hh => hHc h (hG' hh)
  · intro h hh
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    refine lt_of_le_of_lt (diam_mono ?_ (hbdd _ (hdxD x hx))) (hdiam _ (hdxD x hx))
    exact (connectedComponentIn_subset _ _).trans inter_subset_right

/-- **Bing 1951 (Duke), Theorem 6, directly**: a bounded plane continuum containing no continuum
that separates the plane is tree-like. The links are the components of `polyInterior J ∩ d`, for a
notched-square cover `D` of `M` with no triple points and an enclosing polygon `J` of `M` inside
`⋃ D`. (Same statement as `theorem6_1951`.) -/
theorem theorem6_direct {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M := by
  refine ⟨hM, fun ε hε => ?_⟩
  obtain ⟨D, hopen, hdiam, hbdd, hcov, htriple⟩ := exists_notched_cover_bdd hM hns hε
  obtain ⟨J, hJ, -, hMJ, hJD⟩ := enclose_holds M hM (hns M subset_rfl hM) (⋃ d ∈ D, d)
    (isOpen_iUnion fun d => isOpen_iUnion fun hd => hopen d hd) hcov
  obtain ⟨G, hGc, hG, hGd, hGM, -⟩ :=
    treeChain_of_cover_open planeFacts_holds hM hJ hMJ hopen hbdd hdiam hJD htriple
  refine ⟨G, hG, fun h hh => ⟨?_, hGd h hh⟩, hGM⟩
  obtain ⟨d, hd, x, -, rfl⟩ := hGc h hh
  exact (hbdd d hd).subset ((connectedComponentIn_subset _ _).trans inter_subset_right)

end HPC.Plane
