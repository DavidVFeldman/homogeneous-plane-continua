import HPC.Moore.Sec7Th38

/-!
# Moore, F.A. (1916), §7: Theorems 42 and 43 — what is proved (batch 139)

* `isSCC_eq_of_subset`: a closed curve contained in a closed curve is that curve.
* **Theorem 43 as printed is refuted** (`not_fa_theorem43_printed`, commission check 7): for `G`
  empty its hypotheses hold vacuously, and its conclusion would make the interior of `J` lie in its
  own exterior.
* **Theorem 42 from Theorem 41** (`fa_theorem42_of_41`): the induction Moore leaves to the reader.
  Connectedness of the union of the interiors gives, at each stage, a curve of `G` whose interior
  meets the union of the interiors already absorbed (commission §2: \"check that connectedness of
  the union gives an ordering in which each new interior meets the previous union\").
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A closed curve contained in a closed curve is that curve. *Axioms used: 1, 3, 4, 5₁.* -/
theorem isSCC_eq_of_subset (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J J' : Set S} (hJ : σ.IsSCC J) (hJ' : σ.IsSCC J')
    (hsub : J' ⊆ J) : J' = J := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨A, B, C₁, C₂, hC₁, hC₂, hC12, rfl⟩ := hJ'
  have hne : C₁ ≠ C₂ := by
    intro h
    obtain ⟨x, hx, hxAB⟩ := ((isArc_iff_tarc h1 h3 h4 h51).mp hC₁).nonempty_diff
    have : x ∈ C₁ ∩ C₂ := ⟨hx, h ▸ hx⟩
    rw [hC12] at this
    exact hxAB this
  exact (two_arcs_eq h1 h3 h4 h51 hJ hC₁ hC₂ (subset_union_left.trans hsub)
    (subset_union_right.trans hsub) hne).2

/-- **Theorem 43 as printed is not a consequence of Axioms 1–8** (unless they have no model): in
any space satisfying them, take a closed curve `J` (Theorem 35), its interior `I`, a point `O` of
`J` and `G = ∅`. The hypotheses hold vacuously, and the conclusion gives a closed curve
`J₁ ⊆ J`, so `J₁ = J` and `I₁ = I` (Theorem 21), with `I₁` in the exterior of `I`. -/
theorem not_fa_theorem43_printed (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) :
    ¬ ∀ (J I : Set S), σ.IsInteriorOf J I → ∀ O ∈ J, ∀ G : Finset (Set S × Set S),
      (∀ p ∈ G, σ.IsInteriorOf p.1 p.2) → (∀ p ∈ G, O ∈ p.2) → (∀ p ∈ G, ¬ I ⊆ p.2) →
      ∃ J₁ I₁ J₂ I₂, σ.IsInteriorOf J₁ I₁ ∧ σ.IsInteriorOf J₂ I₂ ∧ O ∈ J₁ ∧ O ∈ J₂ ∧
        J₁ ∪ J₂ ⊆ J ∪ ⋃ p ∈ G, p.1 ∧ I₁ ⊆ σ.ext I ∧ I₂ ⊆ I ∧
        ∀ p ∈ G, I₁ ∪ I₂ ⊆ p.2 := by
  intro H
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨P, -⟩ := h51
  obtain ⟨R, hR, hPR⟩ := Space.exists_region_mem h1 P
  obtain ⟨J, -, hJ⟩ := fa_theorem35 h1 h2 h3 h4 h5 h6 h7 h8 hR ⟨P, hPR⟩
  obtain ⟨I, hIr, hIJ⟩ := h8 J hJ
  have hI : σ.IsInteriorOf J I := ⟨hJ, hIr, hIJ⟩
  obtain ⟨A, B, C₁, C₂, hC₁, -, -, hJeq⟩ := hJ
  have hAJ : A ∈ J := hJeq ▸ Or.inl hC₁.left_mem
  obtain ⟨J₁, I₁, J₂, I₂, hI₁, -, -, -, hsub, hI₁E, -, -⟩ :=
    H J I hI A hAJ (∅ : Finset (Set S × Set S)) (fun p hp => absurd hp (Finset.notMem_empty p))
      (fun p hp => absurd hp (Finset.notMem_empty p)) (fun p hp => absurd hp (Finset.notMem_empty p))
  have hJ₁J : J₁ ⊆ J := fun x hx => by
    have := hsub (Or.inl hx); simpa using this
  have hJ₁ : J₁ = J := isSCC_eq_of_subset h1 h3 h4 (axiom5₁_of_axiom5 h5) hI.1 hI₁.1 hJ₁J
  subst hJ₁
  have hII : I₁ = I := by
    obtain ⟨R', -, huniq⟩ := existsUnique_interior h1 h3 h4 h5 h7 h8 hI.1
    rw [huniq I₁ hI₁, huniq I hI]
  subst hII
  obtain ⟨-, -, ⟨x, hx⟩, -⟩ := jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hI
  have := hI₁E hx
  rw [ext_eq_compl_closure h1] at this
  exact this (subset_closure hx)

/-- The conclusion of Theorem 41, as a property of the space. -/
def Th41 (σ : Space S) : Prop :=
  ∀ J₁ J₂ I₁ I₂ : Set S, σ.IsInteriorOf J₁ I₁ → σ.IsInteriorOf J₂ I₂ → (I₁ ∩ I₂).Nonempty →
    ∃ J I, J ⊆ J₁ ∪ J₂ ∧ σ.IsInteriorOf J I ∧ I₁ ∪ I₂ ⊆ I

/-- **Theorem 42 from Theorem 41.** If Theorem 41 holds, then Theorem 42 holds. *Axioms used: 1, 2,
3, 4, 5₁, 7* (besides Theorem 41). Induction on the number of curves of `G` not yet absorbed: if
`H ⊊ G` and no interior of a curve of `G − H` met the union of the interiors of `H`, the union of
all the interiors would split into two disjoint nonempty open sets; so some curve `q` of `G − H`
has an interior meeting the interior `I` of the curve already built (which contains those of
`H`), and Theorem 41 applied to the two curves absorbs `q`. -/
theorem fa_theorem42_of_41 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7) (H41 : Th41 σ)
    (G : Finset (Set S × Set S)) (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2)
    (hne : G.Nonempty) (hconn : σ.IsConn (⋃ p ∈ G, p.2)) :
    ∃ J I, σ.IsInteriorOf J I ∧ J ⊆ ⋃ p ∈ G, p.1 ∧ ∀ p ∈ G, p.2 ⊆ I := by
  classical
  letI := σ.topology
  rw [isConn_iff h1] at hconn
  have hopen : ∀ p ∈ G, IsOpen p.2 := fun p hp => (jordan h1 h2 h3 h4 h51 h7 (hG p hp)).1
  have hnonempty : ∀ p ∈ G, p.2.Nonempty := fun p hp => (jordan h1 h2 h3 h4 h51 h7 (hG p hp)).2.2.1
  -- the statement for a subfamily `H`
  let P : Finset (Set S × Set S) → Prop := fun H =>
    ∃ J I, σ.IsInteriorOf J I ∧ J ⊆ ⋃ p ∈ H, p.1 ∧ ∀ p ∈ H, p.2 ⊆ I
  have step : ∀ n : ℕ, ∀ H ⊆ G, H.Nonempty → (G \ H).card = n → P H → P G := by
    intro n
    induction n with
    | zero =>
      intro H hHG _ hcard hP
      have : G \ H = ∅ := Finset.card_eq_zero.mp hcard
      have hGH : G = H := le_antisymm (Finset.sdiff_eq_empty_iff_subset.mp this) hHG
      rw [hGH]; exact hP
    | succ n ih =>
      intro H hHG hHne hcard hP
      obtain ⟨J, I, hJI, hJH, hHI⟩ := hP
      -- some curve of `G − H` has an interior meeting `⋃ H`
      obtain ⟨q, hq, hqI⟩ : ∃ q ∈ G \ H, (q.2 ∩ ⋃ p ∈ H, p.2).Nonempty := by
        by_contra hnone
        push_neg at hnone
        have hU : IsOpen (⋃ p ∈ H, p.2) :=
          isOpen_biUnion fun p hp => hopen p (hHG hp)
        have hV : IsOpen (⋃ p ∈ G \ H, p.2) :=
          isOpen_biUnion fun p hp => hopen p (Finset.mem_sdiff.mp hp).1
        have hcov : (⋃ p ∈ G, p.2) ⊆ (⋃ p ∈ H, p.2) ∪ ⋃ p ∈ G \ H, p.2 := by
          intro x hx
          simp only [mem_iUnion] at hx
          obtain ⟨p, hp, hxp⟩ := hx
          by_cases hpH : p ∈ H
          · exact Or.inl (mem_biUnion hpH hxp)
          · exact Or.inr (mem_biUnion (Finset.mem_sdiff.mpr ⟨hp, hpH⟩) hxp)
        obtain ⟨p₀, hp₀⟩ := hHne
        obtain ⟨x₀, hx₀⟩ := hnonempty p₀ (hHG hp₀)
        have hGH : (G \ H).Nonempty := by
          rw [← Finset.card_pos, hcard]; exact Nat.succ_pos n
        obtain ⟨q₀, hq₀⟩ := hGH
        obtain ⟨y₀, hy₀⟩ := hnonempty q₀ (Finset.mem_sdiff.mp hq₀).1
        have hdisj : (⋃ p ∈ H, p.2) ∩ (⋃ p ∈ G \ H, p.2) = ∅ := by
          ext z
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro hzU hzV
          simp only [mem_iUnion] at hzV
          obtain ⟨p, hp, hzp⟩ := hzV
          exact (hnone p hp).subset ⟨hzp, hzU⟩
        rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _ hU hV hcov
            (by rw [hdisj, inter_empty]) with h' | h'
        · have : y₀ ∈ ⋃ p ∈ H, p.2 := h' (mem_biUnion (Finset.mem_sdiff.mp hq₀).1 hy₀)
          exact (hnone q₀ hq₀).subset ⟨hy₀, this⟩
        · have : x₀ ∈ ⋃ p ∈ G \ H, p.2 := h' (mem_biUnion (hHG hp₀) hx₀)
          simp only [mem_iUnion] at this
          obtain ⟨p, hp, hxp⟩ := this
          exact (hnone p hp).subset ⟨hxp, mem_biUnion hp₀ hx₀⟩
      obtain ⟨x, hxq, hxH⟩ := hqI
      simp only [mem_iUnion] at hxH
      obtain ⟨p, hp, hxp⟩ := hxH
      have hqG := (Finset.mem_sdiff.mp hq).1
      have hqH := (Finset.mem_sdiff.mp hq).2
      obtain ⟨J', I', hJ'sub, hJ'I', hII'⟩ := H41 J q.1 I q.2 hJI (hG q hqG) ⟨x, hHI p hp hxp, hxq⟩
      refine ih (insert q H) (Finset.insert_subset hqG hHG) (Finset.insert_nonempty q H) ?_
        ⟨J', I', hJ'I', ?_, ?_⟩
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hq, hcard]; rfl
      · intro y hy
        rcases hJ'sub hy with h | h
        · have := hJH h
          simp only [mem_iUnion] at this ⊢
          obtain ⟨p, hp, hyp⟩ := this
          exact ⟨p, Finset.mem_insert_of_mem hp, hyp⟩
        · simp only [mem_iUnion]
          exact ⟨q, Finset.mem_insert_self q H, h⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact subset_union_right.trans hII'
        · exact (hHI p hp).trans (subset_union_left.trans hII')
  obtain ⟨p₀, hp₀⟩ := hne
  refine step _ {p₀} (Finset.singleton_subset_iff.mpr hp₀) (Finset.singleton_nonempty p₀) rfl
    ⟨p₀.1, p₀.2, hG p₀ hp₀, ?_, ?_⟩
  · intro y hy; simp only [Finset.mem_singleton, mem_iUnion]; exact ⟨p₀, rfl, hy⟩
  · intro p hp; rw [Finset.mem_singleton.mp hp]

end HPC.Moore
