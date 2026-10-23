import HPC.HO16.Prop19C

/-!
# Batch 196, §3: Proposition 19, consistent complements (S4′) (pp. 207–208)

For a component `D` of `F \ π(S′ᵢ)`, `φ(D)` lies in a component `D̃` of `G \ π(Sᵢ)` and the
frontier of `D` lies over the frontier of `D̃` (`relFrontier_over`). At the regular levels this is
`hasConsCompl_pullback`; at level `i₀` the complement lies in `F₃`; at level `i₀ + 1` Proposition 10
(second part) and Lemma 6 (6) split the frontier between `F₃` and `F₁ ∪ F₂`; for `P′₂` the argument
is the case split of commission §3 (the sentence of p. 208 refuted in `ho16_p208_false` is not
used).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The frontier of a preconnected `D ⊆ F` lying over `G \ A`, whose frontier lies over `A`, lies
over the frontier of the component of `G \ A` containing `φ(D)`. -/
theorem relFrontier_over {G A : Set E} {F D : Set (E × ℝ)} (hG : IsClosed G)
    (hD : IsPreconnected D) {x : E × ℝ} (hx : x ∈ D) (hDA : ∀ y ∈ D, y.1 ∈ G \ A)
    (hfrA : ∀ z ∈ relFrontier F D, z.1 ∈ A) :
    ∀ z ∈ relFrontier F D, z.1 ∈ relFrontier G (connectedComponentIn (G \ A) x.1) := by
  have hDC : Prod.fst '' D ⊆ connectedComponentIn (G \ A) x.1 :=
    (hD.image _ continuous_fst.continuousOn).subset_connectedComponentIn ⟨x, hx, rfl⟩
      (by rintro _ ⟨y, hy, rfl⟩; exact hDA y hy)
  have hCsub : connectedComponentIn (G \ A) x.1 ⊆ G \ A := connectedComponentIn_subset _ _
  intro z hz
  have h1 : z.1 ∈ closure (connectedComponentIn (G \ A) x.1) :=
    closure_mono hDC (map_mem_closure continuous_fst hz.1 fun p hp => ⟨p, hp, rfl⟩)
  rcases closure_subset_union_relFrontier hG (hCsub.trans diff_subset) h1 with h | h
  · exact absurd (hfrA z hz) (hCsub h).2
  · exact h

/-- Consistent complement depends only on `B ∩ X`. -/
theorem hasConsCompl_congr {F X B B' : Set (E × ℝ)} (hF : IsPLGraph F) (hX : IsClosed X)
    (h : HasConsCompl F X B) (hB : B ∩ X = B' ∩ X) : HasConsCompl F X B' := by
  intro x hx
  have hsub := hF.relFrontier_comp_subset hX x
  rcases h x hx with h | h
  · refine Or.inl fun z hz => ?_
    have : z ∈ B ∩ X := ⟨h hz, hsub hz⟩
    rw [hB] at this; exact this.1
  · refine Or.inr (Set.disjoint_left.2 fun z hz hz' => ?_)
    have : z ∈ B' ∩ X := ⟨hz', hsub hz⟩
    rw [← hB] at this
    exact Set.disjoint_left.1 h hz this.1

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

theorem F₁₂closed : IsClosed (F₁ ∪ F₂) :=
  H.F₁PL.isCompact.isClosed.union H.F₂PL.isCompact.isClosed

theorem F₃closed : IsClosed F₃ := H.F₃PL.isCompact.isClosed

theorem imgF_sub : Prod.fst '' (F₁ ∪ F₂ ∪ F₃) ⊆ G := H.imgF.subset

theorem Gclosed : IsClosed G := H.hG.isCompact.isClosed

theorem T_img_closed {i : ℕ} (hi : i ∈ Icc 1 k) : IsClosed (Prod.fst '' T i) :=
  (H.T_straight hi).2.2.2.2.isCompact.isClosed

/-- Lemma 6 (6): a preconnected subset of `F` missing `∂F₃` lies in `F₃` or in `F₁ ∪ F₂`. -/
theorem comp_side {D : Set (E × ℝ)} (hD : IsPreconnected D) (hDF : D ⊆ F₁ ∪ F₂ ∪ F₃)
    (hDM : Disjoint D (F₂ ∩ F₃)) : D ⊆ F₃ ∨ D ⊆ F₁ ∪ F₂ := by
  obtain ⟨U, V, hU, hV, hcov, hdisj, hPU, hQV⟩ := (ho16_lemma6 H.hF).2.2.2.2.2.2.2.2.2.2.1
  have hDsub : D ⊆ (F₁ ∪ F₂ ∪ F₃) \ (F₂ ∩ F₃) := fun y hy =>
    ⟨hDF hy, fun h => Set.disjoint_left.1 hDM hy h⟩
  have hbad : ∀ y ∈ D, y ∈ U → y ∈ V → False := fun y hy hyU hyV => by
    have : y ∈ U ∩ V ∩ ((F₁ ∪ F₂ ∪ F₃) \ (F₂ ∩ F₃)) := ⟨⟨hyU, hyV⟩, hDsub hy⟩
    rw [hdisj] at this; exact this
  rcases isPreconnected_iff_subset_of_disjoint.1 hD U V hU hV (hDsub.trans hcov)
    (eq_empty_iff_forall_notMem.2 fun y hy => hbad y hy.1 hy.2.1 hy.2.2) with h | h
  · left
    intro y hy
    by_contra h3
    have h12 : y ∈ F₁ ∪ F₂ := by
      rcases hDF hy with h' | h'
      · exact h'
      · exact absurd h' h3
    exact hbad y hy (h hy) (hQV ⟨h12, h3⟩)
  · right
    intro y hy
    by_contra h12
    have h3 : y ∈ F₃ := by
      rcases hDF hy with h' | h'
      · exact absurd h' h12
      · exact h'
    exact hbad y hy (hPU ⟨h3, fun h2 => h12 (Or.inr h2)⟩) (h hy)

/-- A component of `F \ X` with `X = F ∩ φ⁻¹(A)` lies over `G \ A`, with frontier over `A`. -/
theorem comp_over {A : Set E} (hA : IsClosed A) {x : E × ℝ}
    (hx : x ∈ (F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A)) :
    ∀ z ∈ relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A)) x),
      z.1 ∈ relFrontier G (connectedComponentIn (G \ A) x.1) := by
  have hX : IsClosed ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) :=
    H.Fclosed.inter (hA.preimage continuous_fst)
  refine relFrontier_over H.Gclosed isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hx) (fun y hy => ?_) (fun z hz => ?_)
  · have hy' := connectedComponentIn_subset _ _ hy
    exact ⟨H.imgF_sub ⟨y, hy'.1, rfl⟩, fun h => hy'.2 ⟨hy'.1, h⟩⟩
  · exact (H.FPL.relFrontier_comp_subset hX x hz).2

/-- (S4′) at the regular levels (p. 207). -/
theorem S4'_reg {A B : Set E} (hA : IsClosed A) (hc : HasConsCompl G A B) :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃) ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A)
      ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' B) :=
  hasConsCompl_pullback H.Gclosed H.FPL H.imgF_sub (H.Fclosed.inter (hA.preimage continuous_fst))
    subset_rfl (fun _ hz => hz.1.2) (closure_minimal diff_subset H.Fclosed) hc

/-- (S4′) at level `i₀` (pp. 207–208): the complement of `π(S′_{i₀})` lies in `F₃`. -/
theorem S4'_i₀ {B : Set E} (hc : HasConsCompl G (Prod.fst '' T i₀) B) :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀)
      (F₃ ∩ Prod.fst ⁻¹' B) := by
  rw [H.image_T'₀]
  have hXc := H.isPLGraph_image_T'₀.isCompact.isClosed
  have hcl : closure ((F₁ ∪ F₂ ∪ F₃) \ (F₁ ∪ F₂ ∪ (F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀)))) ⊆ F₃ := by
    rw [H.compl_image_T'₀]; exact closure_minimal inter_subset_left H.F₃closed
  refine hasConsCompl_pullback H.Gclosed H.FPL H.imgF_sub hXc ?_ ?_ hcl hc
  · rintro x ⟨(h | h) | h, hx⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h, hx⟩
  · rintro x ⟨hxX, hxc⟩
    have hx3 := hcl hxc
    rcases hxX with (h | h) | h
    · exact absurd hx3 (Set.disjoint_left.1 H.disj₁₃ h)
    · have : x.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨x, ⟨h, hx3⟩, rfl⟩
      rw [H.fr23] at this
      exact H.γ_img_sub this
    · exact h.2

/-- **(S4′) at level `i₀ + 1`** (pp. 207–208): by Proposition 10 (second part) and Lemma 6 (6), the
frontier of a component of `F \ π(S′_{i₀+1})` meeting `φ⁻¹(π(β_{i₀}))` lies over `π(β_{i₀})` in
`F₃` or in `F₁ ∪ F₂`. -/
theorem split_i₀1 (hk : i₀ < k) {x : E × ℝ}
    (hx : x ∈ (F₁ ∪ F₂ ∪ F₃) \ Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1)) :
    relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1)) x)
      ⊆ F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) ∨
    relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1)) x)
      ⊆ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) ∨
    Disjoint (relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1)) x))
      (Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1))) := by
  have hi1 : i₀ + 1 ∈ Icc 1 k := ⟨by omega, hk⟩
  have hi : i₀ ∈ Icc 1 k := ⟨H.i₀_pos, H.i₀_le⟩
  rw [H.img_T' hi1 (by omega)] at hx ⊢
  set A := Prod.fst '' T (i₀ + 1) with hAdef
  set A' := Prod.fst '' T i₀ with hA'def
  set B := Prod.fst '' α (i₀ + 1) with hBdef
  set D := connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A)) x with hDdef
  have hAc : IsClosed A := H.T_img_closed hi1
  have hX : IsClosed ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) :=
    H.Fclosed.inter (hAc.preimage continuous_fst)
  have hover := H.comp_over hAc hx
  have hDsub : D ⊆ (F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) :=
    connectedComponentIn_subset _ _
  have hxA : x.1 ∈ G \ A := ⟨H.imgF_sub ⟨x, hx.1, rfl⟩, fun h => hx.2 ⟨hx.1, h⟩⟩
  by_cases hM : (D ∩ (F₂ ∩ F₃)).Nonempty
  · -- `D` meets `∂F₃`: Proposition 10, second part
    right; right
    obtain ⟨z, hzD, hz23⟩ := hM
    have hzγ : z.1 ∈ Prod.fst '' γ := by rw [← H.fr23]; exact ⟨z, hz23, rfl⟩
    have hzA' : z.1 ∈ A' := H.γ_img_sub hzγ
    have hzA : z.1 ∈ G \ A := ⟨H.imgF_sub ⟨z, (hDsub hzD).1, rfl⟩,
      fun h => (hDsub hzD).2 ⟨(hDsub hzD).1, h⟩⟩
    have hDC : Prod.fst '' D ⊆ connectedComponentIn (G \ A) x.1 :=
      (isPreconnected_connectedComponentIn.image _ continuous_fst.continuousOn).subset_connectedComponentIn
        ⟨x, mem_connectedComponentIn hx, rfl⟩ (by
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨H.imgF_sub ⟨y, (hDsub hy).1, rfl⟩, fun h => (hDsub hy).2 ⟨(hDsub hy).1, h⟩⟩)
    have hCeq : connectedComponentIn (G \ A) z.1 = connectedComponentIn (G \ A) x.1 :=
      (connectedComponentIn_eq (hDC ⟨z, hzD, rfl⟩)).symm
    obtain ⟨V₀, hV₀, hV₀eq⟩ := H.S3 i₀ ⟨H.i₀_pos, hk⟩
    have hTA := (H.T_straight hi1).2
    have hTA' := H.Ti₀_straight
    have hBfr : B ⊆ relFrontier G A ∩ relFrontier G A' := by
      refine subset_inter ?_ ?_
      · rw [← hTA.image_endSet, (H.endSet_T hi1 (by omega)).1, image_union]
        exact subset_union_left
      · rw [← hTA'.image_endSet, H.endSet_Ti₀, image_union, image_union]
        exact subset_union_right.trans subset_union_left
    have h10 := (ho16_prop10 H.hG H.hconn hTA.2.2.2 hTA'.2.2.2 hTA.image_subset hTA'.image_subset
      ((H.T_straight hi1).1.image _) ((H.T_straight hi).1.image _) hBfr (H.S4 _ hi1).1
      (H.S4 _ hi).2 hV₀ hV₀eq.symm).2 z.1 hzA
    have hcl : Disjoint (closure (connectedComponentIn (G \ A) x.1)) B := by
      rw [Set.disjoint_iff_inter_eq_empty, ← hCeq]
      by_contra hne
      exact (h10 (Set.nonempty_iff_ne_empty.2 hne)).1.2 hzA'
    exact Set.disjoint_left.2 fun w hw hwB =>
      Set.disjoint_left.1 hcl (hover w hw).1 hwB
  · -- `D` misses `∂F₃`: Lemma 6 (6)
    have hDM : Disjoint D (F₂ ∩ F₃) := Set.disjoint_iff_inter_eq_empty.2
      (Set.not_nonempty_iff_eq_empty.1 hM)
    rcases (H.S4 _ hi1).1 x.1 hxA with hc | hc
    · rcases H.comp_side isPreconnected_connectedComponentIn (hDsub.trans diff_subset) hDM with
        h | h
      · left
        exact fun w hw => ⟨closure_minimal h H.F₃closed hw.1, hc (hover w hw)⟩
      · right; left
        exact fun w hw => ⟨closure_minimal h H.F₁₂closed hw.1, hc (hover w hw)⟩
    · right; right
      exact Set.disjoint_left.2 fun w hw hwB => Set.disjoint_left.1 hc (hover w hw) hwB

/-- (S4′) for `S′_{i₀+1}` and `α′_{i₀+1}`. -/
theorem S4'_i₀1_α (hk : i₀ < k) :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1))
      (Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i₀ + 1)) := by
  rw [p19α_succ, H.img_α₃]
  intro x hx
  rcases H.split_i₀1 hk hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' => H.α₁₂_off (h hw) hw'.1)
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' => Set.disjoint_left.1 h hw hw'.2)

/-- (S4′) for `S′_{i₀+1}` and `γ′_{i₀+1}`. -/
theorem S4'_i₀1_γ (hk : i₀ < k) :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1))
      (Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)) := by
  rw [H.img_α₁₂]
  intro x hx
  rcases H.split_i₀1 hk hx with h | h | h
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' => H.α₁₂_off hw' (h hw).1)
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' => Set.disjoint_left.1 h hw hw'.2)

/-- **(S4′) for `P′₂`** (p. 208), by the case split of commission §3: the frontier of a component
of `F \ π(P′₂)` lies over `π(γ_{i₀})` or over `π(β_{i₀})`. -/
theorem split_P'₂ {x : E × ℝ}
    (hx : x ∈ (F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) :
    relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) x)
      ⊆ Prod.fst ⁻¹' (Prod.fst '' γ) ∨
    relFrontier (F₁ ∪ F₂ ∪ F₃)
        (connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) x)
      ⊆ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) := by
  have hi : i₀ ∈ Icc 1 k := ⟨H.i₀_pos, H.i₀_le⟩
  set A := Prod.fst '' T i₀ with hAdef
  set X := (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A with hXdef
  set D := connectedComponentIn ((F₁ ∪ F₂ ∪ F₃) \ X) x with hDdef
  have hAc : IsClosed A := H.T_img_closed hi
  have hXc : IsClosed X := H.F₁₂closed.inter (hAc.preimage continuous_fst)
  have hDsub : D ⊆ (F₁ ∪ F₂ ∪ F₃) \ X := connectedComponentIn_subset _ _
  have hfrX : relFrontier (F₁ ∪ F₂ ∪ F₃) D ⊆ X := H.FPL.relFrontier_comp_subset hXc x
  have hDM : Disjoint D (F₂ ∩ F₃) := Set.disjoint_left.2 fun y hy h23 => by
    have : y.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨y, h23, rfl⟩
    rw [H.fr23] at this
    exact (hDsub hy).2 ⟨Or.inr h23.1, H.γ_img_sub this⟩
  rcases H.comp_side isPreconnected_connectedComponentIn (hDsub.trans diff_subset) hDM with h | h
  · -- `D ⊆ F₃`: its frontier lies in `∂F₃`, over `π(γ)`
    left
    intro w hw
    have hw3 : w ∈ F₃ := closure_minimal h H.F₃closed hw.1
    have hw12 := (hfrX hw).1
    have hw2 : w ∈ F₂ := by
      rcases hw12 with h1 | h2
      · exact absurd hw3 (Set.disjoint_left.1 H.disj₁₃ h1)
      · exact h2
    show w.1 ∈ Prod.fst '' γ
    rw [← H.fr23]; exact ⟨w, ⟨hw2, hw3⟩, rfl⟩
  · -- `D ⊆ F₁ ∪ F₂`
    have hxD : x ∈ D := mem_connectedComponentIn hx
    have hDA : ∀ y ∈ D, y.1 ∈ G \ A := fun y hy =>
      ⟨H.imgF_sub ⟨y, (hDsub hy).1, rfl⟩, fun hA => (hDsub hy).2 ⟨h hy, hA⟩⟩
    have hover := relFrontier_over H.Gclosed isPreconnected_connectedComponentIn hxD hDA
      (fun z hz => (hfrX hz).2)
    rcases (relFrontier (F₁ ∪ F₂ ∪ F₃) D).eq_empty_or_nonempty with he | ⟨z, hz⟩
    · left; rw [he]; exact empty_subset _
    have hxA := hDA x hxD
    set Dt := connectedComponentIn (G \ A) x.1
    have hzD : z.1 ∈ relFrontier G Dt := hover z hz
    have hz12 : z ∈ F₁ ∪ F₂ := closure_minimal h H.F₁₂closed hz.1
    have hzP : z.1 ∉ Prod.fst '' α i₀ := fun hα => by
      refine Set.disjoint_left.1 H.S6 hα ?_
      rw [image_union]
      rcases hz12 with h1 | h2
      · left; rw [← H.img₁]; exact ⟨z, h1, rfl⟩
      · right; rw [← H.img₂]; exact ⟨z, h2, rfl⟩
    have hfrDt : relFrontier G Dt ⊆ Prod.fst '' α i₀ ∪ Prod.fst '' α (i₀ + 1) ∪ Prod.fst '' γ := by
      refine (H.hG.relFrontier_comp_subset_relFrontier hAc x.1).trans ?_
      show relFrontier G (Prod.fst '' T i₀) ⊆ _
      rw [← H.Ti₀_straight.image_endSet, H.endSet_Ti₀, image_union, image_union]
    rcases (H.S4 _ hi).2 x.1 hxA with hb | hb
    · right; exact fun w hw => hb (hover w hw)
    rcases H.S4γ x.1 hxA with hg | hg
    · left; exact fun w hw => hg (hover w hw)
    exfalso
    rcases hfrDt hzD with (h1 | h2) | h3
    · exact hzP h1
    · exact Set.disjoint_left.1 hb hzD h2
    · exact Set.disjoint_left.1 hg hzD h3

/-- (S4′) for `P′₂` and `𝓔(P′₁)`. -/
theorem S4'_P'₂_E :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃)
      (Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1))
      (Prod.fst '' endSet (F₁ ∪ F₂ ∪ F₃)
        (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)) := by
  rw [H.straight_P'₁.2, H.img_γ, H.img_P'₂]
  intro x hx
  have hsub := H.FPL.relFrontier_comp_subset
    (H.F₁₂closed.inter ((H.T_img_closed ⟨H.i₀_pos, H.i₀_le⟩).preimage continuous_fst)) x
  rcases H.split_P'₂ hx with h | h
  · exact Or.inl fun w hw => ⟨subset_union_left (hsub hw).1, h hw⟩
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' =>
      Set.disjoint_left.1 (H.disj_α_γ H.i₀1_mem) (h hw) hw'.2)

/-- (S4′) for `P′₂` and `γ′_{i₀+1}`. -/
theorem S4'_P'₂_γ :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃)
      (Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1))
      (Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)) := by
  rw [H.img_α₁₂, H.img_P'₂]
  intro x hx
  have hsub := H.FPL.relFrontier_comp_subset
    (H.F₁₂closed.inter ((H.T_img_closed ⟨H.i₀_pos, H.i₀_le⟩).preimage continuous_fst)) x
  rcases H.split_P'₂ hx with h | h
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' =>
      Set.disjoint_left.1 (H.disj_α_γ H.i₀1_mem) hw'.2 (h hw))
  · exact Or.inl fun w hw => ⟨(hsub hw).1, h hw⟩

/-- **(S4′) for the levels** (pp. 207–208). -/
theorem S4'T {i : ℕ} (hi : i ∈ Icc 1 k) (hk : i = i₀ + 1 → i₀ < k) :
    HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i)
        (Prod.fst '' p19α F₁ F₂ F₃ α i₀ i) ∧
      HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i)
        (Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i + 1)) := by
  have hi1 : i ∈ Icc 1 (k + 1) := ⟨hi.1, by have := hi.2; omega⟩
  have hi2 : i + 1 ∈ Icc 1 (k + 1) := ⟨by omega, by have := hi.2; omega⟩
  rcases eq_or_ne i i₀ with rfl | hne
  · constructor
    · rw [p19α_ne _ _ _ _ (by omega), H.img_α hi1]
      have heq : (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' α i) =
          F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' α i) :=
        Subset.antisymm (fun x h => ⟨(H.pre_αi₀ h).1, h.2⟩) fun x h => ⟨Or.inr h.1, h.2⟩
      rw [heq]; exact H.S4'_i₀ (H.S4 _ hi).1
    · rw [p19α_succ, H.img_α₃]; exact H.S4'_i₀ (H.S4 _ hi).2
  · have hreg : ∀ {B : Set E}, HasConsCompl G (Prod.fst '' T i) B →
        HasConsCompl (F₁ ∪ F₂ ∪ F₃) (Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i)
          ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' B) := fun hc => by
      rw [H.img_T' hi hne]; exact H.S4'_reg (H.T_img_closed hi) hc
    constructor
    · rcases eq_or_ne i (i₀ + 1) with rfl | hne'
      · exact H.S4'_i₀1_α (hk rfl)
      · rw [p19α_ne _ _ _ _ hne', H.img_α hi1]; exact hreg (H.S4 _ hi).1
    · rw [p19α_ne _ _ _ _ (by omega), H.img_α hi2]; exact hreg (H.S4 _ hi).2

end P19

end Prop19D

end HPC.HO16
