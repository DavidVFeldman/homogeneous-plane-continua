import HPC.Moore.M19GCuts

/-!
# Moore 1919: the annulus cut into two quadrilaterals (batch 144, item B)

Let `J ∪ I` lie within `J'`, and let `PP'`, `QQ'` be the two cuts of `exists_cuts`. With a
cross-cut `e` of `I` from `P` to `Q`, the arc `γ = P'P + e + QQ'` is a cross-cut of `I'`; it splits
`I'` into the interiors `R₁`, `R₂` of `γ + b₁` and `γ + b₂`, where `b₁`, `b₂` are the two arcs of
`J'` from `P'` to `Q'`. One arc `a₁` of `J` from `P` to `Q` lies in `R₁` and the other, `a₂`, in
`R₂` (`not_both`). Cutting `Rᵢ` along `aᵢ` (`half_split`) leaves the half of `I` bounded by `e + aᵢ`
and the interior `Aᵢ` of the closed curve `PP' + bᵢ + Q'Q + aᵢ`. The two closed curves with their
interiors fill the closed annulus `J' + I' − I` and meet only along the cuts (`annulus_decomp`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Split

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

omit h1 h2 h3 h4 h5 h6 h7 h8 in
theorem mem_of_inter_eq' {s t : Set S} {P x : S} (h : s ∩ t = {P}) (hs : x ∈ s) (ht : x ∈ t) :
    x = P := by
  have : x ∈ s ∩ t := ⟨hs, ht⟩
  rw [h] at this; exact this

omit h6 in
/-- **Cutting a half along an arc of `J`.** Let `R` be the interior of `γ + b`, where
`γ = c₁ + e + c₂` and `b` is an arc of `J'` from `P'` to `Q'`, and let the arc `a` from `P` to `Q`
lie in `R` except for its ends. Then `R − a` is the union of the interior `H` of `e + a` and the
interior `A` of the closed curve `c₁ + b + c₂ + a`, which are disjoint. -/
theorem half_split {P Q P' Q' : S} {c₁ c₂ e b a R H : Set S}
    (hc₁ : @TArc S σ.topology P P' c₁) (hc₂ : @TArc S σ.topology Q Q' c₂)
    (he : @TArc S σ.topology P Q e) (hb : @TArc S σ.topology P' Q' b)
    (ha : @TArc S σ.topology P Q a)
    (hc₁e : c₁ ∩ e = {P}) (hc₂e : c₂ ∩ e = {Q}) (heb : Disjoint e b) (hc₁b : c₁ ∩ b = {P'})
    (hc₂b : c₂ ∩ b = {Q'}) (hc₁₂ : Disjoint c₁ c₂)
    (hR : σ.IsInteriorOf (c₁ ∪ e ∪ c₂ ∪ b) R) (haR : a \ {P, Q} ⊆ R)
    (hH : σ.IsInteriorOf (e ∪ a) H) :
    ∃ A, σ.IsInteriorOf (c₁ ∪ b ∪ c₂ ∪ a) A ∧ R \ a = H ∪ A ∧ Disjoint H A := by
  letI := σ.topology
  haveI := t2Space h1
  have hC₂ : TArc P Q (c₁ ∪ b ∪ c₂) := by
    refine (hc₁.union hb hc₁b).union hc₂.symm ?_
    apply subset_antisymm
    · rintro x ⟨hx | hx, hx₂⟩
      · exact absurd hx₂ (disjoint_left.mp hc₁₂ hx)
      · rw [inter_comm] at hc₂b; exact mem_of_inter_eq' hc₂b hx hx₂
    · rintro x rfl; exact ⟨Or.inr hb.right_mem, hc₂.right_mem⟩
  have hCi : e ∩ (c₁ ∪ b ∪ c₂) = {P, Q} := by
    apply subset_antisymm
    · rintro x ⟨hxe, (hx | hx) | hx⟩
      · exact Or.inl (mem_of_inter_eq' hc₁e hx hxe)
      · exact absurd hx (disjoint_left.mp heb hxe)
      · exact Or.inr (mem_of_inter_eq' hc₂e hx hxe)
    · rintro x (rfl | rfl)
      · exact ⟨he.left_mem, Or.inl (Or.inl hc₁.left_mem)⟩
      · exact ⟨he.right_mem, Or.inr hc₂.left_mem⟩
  have hCu : e ∪ (c₁ ∪ b ∪ c₂) = c₁ ∪ e ∪ c₂ ∪ b := by
    ext x; simp only [mem_union]; tauto
  obtain ⟨R₁, R₂, hR₁, hR₂, hsplit, hdis⟩ :=
    split_interior_of h1 h2 h3 h4 h5 h7 h8 hR he hC₂ hCi hCu ha haR
  have hR₁H : R₁ = H := interior_unique h1 h2 h3 h4 h5 h7 hR₁ (by rw [union_comm]; exact hH)
  subst hR₁H
  refine ⟨R₂, ?_, hsplit, hdis⟩
  have : a ∪ (c₁ ∪ b ∪ c₂) = c₁ ∪ b ∪ c₂ ∪ a := union_comm _ _
  rw [← this]; exact hR₂

/-- **The annulus cut into two quadrilaterals.** With the cuts `c₁ = PP'`, `c₂ = QQ'` of
`exists_cuts`, `J` is the union of two arcs `a₁`, `a₂` from `P` to `Q`, `J'` the union of two arcs
`b₁`, `b₂` from `P'` to `Q'`, and the closed curves `Kᵢ = c₁ + bᵢ + c₂ + aᵢ` have interiors `Aᵢ`
such that `A₁`, `A₂` are disjoint, each `Aᵢ` misses the other curve, and
`K₁ + A₁ + K₂ + A₂ = J' + I' − I`. -/
theorem annulus_decomp {J I J' I' : Set S} (hI : σ.IsInteriorOf J I)
    (hI' : σ.IsInteriorOf J' I') (hsub : J ∪ I ⊆ I') {P Q P' Q' : S} {c₁ c₂ : Set S}
    (hc₁ : @TArc S σ.topology P P' c₁) (hc₂ : @TArc S σ.topology Q Q' c₂)
    (hP : P ∈ J) (hQ : Q ∈ J) (hP' : P' ∈ J') (hQ' : Q' ∈ J') (hc₁₂ : Disjoint c₁ c₂)
    (hc₁D : c₁ ∩ (J ∪ I) = {P}) (hc₂D : c₂ ∩ (J ∪ I) = {Q}) (hc₁J' : c₁ ∩ J' = {P'})
    (hc₂J' : c₂ ∩ J' = {Q'}) (hc₁s : c₁ ⊆ J' ∪ I') (hc₂s : c₂ ⊆ J' ∪ I') :
    ∃ a₁ a₂ b₁ b₂ A₁ A₂ : Set S,
      @TArc S σ.topology P Q a₁ ∧ @TArc S σ.topology P Q a₂ ∧ a₁ ∩ a₂ = {P, Q} ∧ a₁ ∪ a₂ = J ∧
      @TArc S σ.topology P' Q' b₁ ∧ @TArc S σ.topology P' Q' b₂ ∧ b₁ ∩ b₂ = {P', Q'} ∧
      b₁ ∪ b₂ = J' ∧
      σ.IsInteriorOf (c₁ ∪ b₁ ∪ c₂ ∪ a₁) A₁ ∧ σ.IsInteriorOf (c₁ ∪ b₂ ∪ c₂ ∪ a₂) A₂ ∧
      Disjoint A₁ A₂ ∧ Disjoint A₁ (c₁ ∪ b₂ ∪ c₂ ∪ a₂) ∧ Disjoint A₂ (c₁ ∪ b₁ ∪ c₂ ∪ a₁) ∧
      (c₁ ∪ b₁ ∪ c₂ ∪ a₁) ∪ A₁ ∪ ((c₁ ∪ b₂ ∪ c₂ ∪ a₂) ∪ A₂) = (J' ∪ I') \ I := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have tarc : ∀ {a b : S} {K : Set S}, σ.IsArc a b K → TArc a b K := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mp h
  obtain ⟨hIo, -, -, -, -, -, -, -, -, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨-, -, -, -, -, -, -, -, -, hI'J', -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI'
  have hPQ : P ≠ Q := fun h => disjoint_left.mp hc₁₂ hc₁.left_mem (h ▸ hc₂.left_mem)
  have hP'Q' : P' ≠ Q' := fun h => disjoint_left.mp hc₁₂ hc₁.right_mem (h ▸ hc₂.right_mem)
  have nI'J' : ∀ {x}, x ∈ I' → x ∉ J' := fun hx hx' => disjoint_left.mp hI'J' hx hx'
  have nIJ : ∀ {x}, x ∈ I → x ∉ J := fun hx hx' => disjoint_left.mp hIJ hx hx'
  -- the cross-cut `e` of `I`
  obtain ⟨e, he, heI⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hI (Or.inl rfl) hP hQ hPQ
  have heD : e ⊆ J ∪ I := fun x hx => by
    by_cases hx' : x ∈ ({P, Q} : Set S)
    · rcases hx' with rfl | rfl
      · exact Or.inl hP
      · exact Or.inl hQ
    · exact Or.inr (heI ⟨hx, hx'⟩)
  have heJ : ∀ x ∈ e, x ∉ I → x = P ∨ x = Q := fun x hx hxI => by
    by_contra h
    simp only [not_or] at h
    exact hxI (heI ⟨hx, by simp [h.1, h.2]⟩)
  have hc₁e : c₁ ∩ e = {P} := by
    apply subset_antisymm
    · rintro x ⟨hx, hxe⟩; exact mem_of_inter_eq' hc₁D hx (heD hxe)
    · rintro x rfl; exact ⟨hc₁.left_mem, he.left_mem⟩
  have hc₂e : c₂ ∩ e = {Q} := by
    apply subset_antisymm
    · rintro x ⟨hx, hxe⟩; exact mem_of_inter_eq' hc₂D hx (heD hxe)
    · rintro x rfl; exact ⟨hc₂.left_mem, he.right_mem⟩
  -- the cross-cut `γ` of `I'`
  set γ := c₁ ∪ e ∪ c₂ with hγdef
  have hγ : TArc P' Q' γ := by
    refine (hc₁.symm.union he hc₁e).union hc₂ ?_
    apply subset_antisymm
    · rintro x ⟨hx | hx, hx₂⟩
      · exact absurd hx₂ (disjoint_left.mp hc₁₂ hx)
      · rw [inter_comm] at hc₂e; exact mem_of_inter_eq' hc₂e hx hx₂
    · rintro x rfl; exact ⟨Or.inr he.right_mem, hc₂.left_mem⟩
  have hγI' : γ \ {P', Q'} ⊆ I' := by
    rintro x ⟨(hx | hx) | hx, hxn⟩
    · rcases hc₁s hx with h | h
      · exact absurd (Or.inl (mem_of_inter_eq' hc₁J' hx h)) hxn
      · exact h
    · exact hsub (heD hx)
    · rcases hc₂s hx with h | h
      · exact absurd (Or.inr (mem_of_inter_eq' hc₂J' hx h)) hxn
      · exact h
  have hPγ : P ∈ γ := Or.inl (Or.inl hc₁.left_mem)
  have hQγ : Q ∈ γ := Or.inr hc₂.left_mem
  -- the arcs of `J'` and the two halves of `I'`
  obtain ⟨b₁, b₂, hb₁, hb₂, hbi, hbu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hI'.1 hP' hQ' hP'Q'
  replace hb₁ := tarc hb₁
  replace hb₂ := tarc hb₂
  have hb₁J' : b₁ ⊆ J' := hbu ▸ subset_union_left
  have hb₂J' : b₂ ⊆ J' := hbu ▸ subset_union_right
  obtain ⟨R₁, R₂, hR₁, hR₂, hR, hR₁₂⟩ :=
    split_interior_of h1 h2 h3 h4 h5 h7 h8 hI' hb₁ hb₂ hbi hbu hγ hγI'
  obtain ⟨hR₁o, -, -, -, -, -, -, -, hR₁cl, hR₁γ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  obtain ⟨hR₂o, -, -, -, -, -, -, -, hR₂cl, hR₂γ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₂
  have hR₁I' : R₁ ⊆ I' := fun x hx => (hR.symm ▸ Or.inl hx : x ∈ I' \ γ).1
  have hR₂I' : R₂ ⊆ I' := fun x hx => (hR.symm ▸ Or.inr hx : x ∈ I' \ γ).1
  have nR₁γ : ∀ {x}, x ∈ R₁ → x ∉ γ := fun hx hxγ => disjoint_left.mp hR₁γ hx (Or.inl hxγ)
  have nR₂γ : ∀ {x}, x ∈ R₂ → x ∉ γ := fun hx hxγ => disjoint_left.mp hR₂γ hx (Or.inl hxγ)
  -- the arcs of `J` and the two halves of `I`
  obtain ⟨a₁, a₂, ha₁, ha₂, hai, hau⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hI.1 hP hQ hPQ
  replace ha₁ := tarc ha₁
  replace ha₂ := tarc ha₂
  obtain ⟨H₁, H₂, hH₁, hH₂, hH, hH₁₂⟩ :=
    split_interior_of h1 h2 h3 h4 h5 h7 h8 hI ha₁ ha₂ hai hau he heI
  have hH₁I : H₁ ⊆ I := fun x hx => (hH.symm ▸ Or.inl hx : x ∈ I \ e).1
  have hH₂I : H₂ ⊆ I := fun x hx => (hH.symm ▸ Or.inr hx : x ∈ I \ e).1
  -- facts for `half_split`
  have hcb : ∀ {b : Set S}, b ⊆ J' → P' ∈ b → Q' ∈ b →
      c₁ ∩ b = {P'} ∧ c₂ ∩ b = {Q'} ∧ Disjoint e b := by
    intro b hbJ hP'b hQ'b
    refine ⟨?_, ?_, ?_⟩
    · apply subset_antisymm
      · rintro x ⟨hx, hxb⟩; exact mem_of_inter_eq' hc₁J' hx (hbJ hxb)
      · rintro x rfl; exact ⟨hc₁.right_mem, hP'b⟩
    · apply subset_antisymm
      · rintro x ⟨hx, hxb⟩; exact mem_of_inter_eq' hc₂J' hx (hbJ hxb)
      · rintro x rfl; exact ⟨hc₂.right_mem, hQ'b⟩
    · rw [disjoint_left]; intro x hx hxb; exact nI'J' (hsub (heD hx)) (hbJ hxb)
  have hcb₁ := hcb hb₁J' hb₁.left_mem hb₁.right_mem
  have hcb₂ := hcb hb₂J' hb₂.left_mem hb₂.right_mem
  -- each open arc of `J` lies in `R₁` or in `R₂`
  have side : ∀ {a : Set S}, TArc P Q a → a ⊆ J → a \ {P, Q} ⊆ R₁ ∨ a \ {P, Q} ⊆ R₂ := by
    intro a ha haJ
    refine ha.isPreconnected_diff.subset_or_subset hR₁o hR₂o hR₁₂ ?_
    rw [← hR]
    rintro x ⟨hxa, hxn⟩
    refine ⟨hsub (Or.inl (haJ hxa)), ?_⟩
    rintro ((hx | hx) | hx)
    · exact hxn (Or.inl (mem_of_inter_eq' hc₁D hx (Or.inl (haJ hxa))))
    · rcases heJ x hx (nIJ.mt (not_not.mpr (haJ hxa))) with h | h
      · exact hxn (Or.inl h)
      · exact hxn (Or.inr h)
    · exact hxn (Or.inr (mem_of_inter_eq' hc₂D hx (Or.inl (haJ hxa))))
  have ha₁J : a₁ ⊆ J := hau ▸ subset_union_left
  have ha₂J : a₂ ⊆ J := hau ▸ subset_union_right
  -- the two open arcs are not on the same side
  have notboth : ∀ {R R'' b b'' : Set S}, σ.IsInteriorOf (c₁ ∪ e ∪ c₂ ∪ b) R →
      TArc P' Q' b → b ⊆ J' → closure R'' = R'' ∪ (γ ∪ b'') → Disjoint R'' (γ ∪ b'') →
      Disjoint R R'' → a₁ \ {P, Q} ⊆ R → a₂ \ {P, Q} ⊆ R → False := by
    intro R R'' b b'' hRi hb hbJ hcl'' hdis'' hRR'' h₁ h₂
    obtain ⟨hc₁b, hc₂b, heb⟩ := hcb hbJ hb.left_mem hb.right_mem
    obtain ⟨A, -, hA, -⟩ := half_split h1 h2 h3 h4 h5 h7 h8 hc₁ hc₂ he hb ha₁ hc₁e hc₂e heb hc₁b
      hc₂b hc₁₂ hRi h₁ hH₁
    obtain ⟨A', -, hA', -⟩ := half_split h1 h2 h3 h4 h5 h7 h8 hc₁ hc₂ he hb ha₂ hc₁e hc₂e heb
      hc₁b hc₂b hc₁₂ hRi h₂ hH₂
    have hH₁R : H₁ ⊆ R := fun x hx => (hA.symm ▸ Or.inl hx : x ∈ R \ a₁).1
    have hH₂R : H₂ ⊆ R := fun x hx => (hA'.symm ▸ Or.inl hx : x ∈ R \ a₂).1
    obtain ⟨z, hze, hzn⟩ := he.nonempty_diff
    have hzI : z ∈ I := heI ⟨hze, hzn⟩
    have hzcl : z ∈ closure R'' := hcl''.symm ▸ Or.inr (Or.inl (Or.inl (Or.inr hze)))
    obtain ⟨w, hwI, hwR''⟩ := mem_closure_iff.mp hzcl I hIo hzI
    have hwe : w ∉ e := fun hwe => disjoint_left.mp hdis'' hwR'' (Or.inl (Or.inl (Or.inr hwe)))
    have hwH : w ∈ H₁ ∪ H₂ := hH ▸ ⟨hwI, hwe⟩
    rcases hwH with hw | hw
    · exact disjoint_left.mp hRR'' (hH₁R hw) hwR''
    · exact disjoint_left.mp hRR'' (hH₂R hw) hwR''
  have final : ∀ {a a' H H' : Set S}, TArc P Q a → TArc P Q a' → a ∩ a' = {P, Q} →
      a ∪ a' = J → σ.IsInteriorOf (e ∪ a) H → σ.IsInteriorOf (e ∪ a') H' → I \ e = H ∪ H' →
      a \ {P, Q} ⊆ R₁ → a' \ {P, Q} ⊆ R₂ →
      ∃ a₁ a₂ b₁ b₂ A₁ A₂ : Set S,
        TArc P Q a₁ ∧ TArc P Q a₂ ∧ a₁ ∩ a₂ = {P, Q} ∧ a₁ ∪ a₂ = J ∧
        TArc P' Q' b₁ ∧ TArc P' Q' b₂ ∧ b₁ ∩ b₂ = {P', Q'} ∧ b₁ ∪ b₂ = J' ∧
        σ.IsInteriorOf (c₁ ∪ b₁ ∪ c₂ ∪ a₁) A₁ ∧ σ.IsInteriorOf (c₁ ∪ b₂ ∪ c₂ ∪ a₂) A₂ ∧
        Disjoint A₁ A₂ ∧ Disjoint A₁ (c₁ ∪ b₂ ∪ c₂ ∪ a₂) ∧ Disjoint A₂ (c₁ ∪ b₁ ∪ c₂ ∪ a₁) ∧
        (c₁ ∪ b₁ ∪ c₂ ∪ a₁) ∪ A₁ ∪ ((c₁ ∪ b₂ ∪ c₂ ∪ a₂) ∪ A₂) = (J' ∪ I') \ I := by
    intro a a' H H' ha ha' hi hu hHa hHa' hHH hR₁a hR₂a'
    have haJ : a ⊆ J := hu ▸ subset_union_left
    have ha'J : a' ⊆ J := hu ▸ subset_union_right
    obtain ⟨A₁, hA₁, hsp₁, hdis₁⟩ := half_split h1 h2 h3 h4 h5 h7 h8 hc₁ hc₂ he hb₁ ha hc₁e hc₂e
      hcb₁.2.2 hcb₁.1 hcb₁.2.1 hc₁₂ hR₁ hR₁a hHa
    obtain ⟨A₂, hA₂, hsp₂, hdis₂⟩ := half_split h1 h2 h3 h4 h5 h7 h8 hc₁ hc₂ he hb₂ ha' hc₁e hc₂e
      hcb₂.2.2 hcb₂.1 hcb₂.2.1 hc₁₂ hR₂ hR₂a' hHa'
    have hA₁R : A₁ ⊆ R₁ := fun x hx => (hsp₁.symm ▸ Or.inr hx : x ∈ R₁ \ a).1
    have hA₂R : A₂ ⊆ R₂ := fun x hx => (hsp₂.symm ▸ Or.inr hx : x ∈ R₂ \ a').1
    have hHI : H ⊆ I := fun x hx => (hHH.symm ▸ Or.inl hx : x ∈ I \ e).1
    have hH'I : H' ⊆ I := fun x hx => (hHH.symm ▸ Or.inr hx : x ∈ I \ e).1
    have hH'R₂ : H' ⊆ R₂ := fun x hx => (hsp₂.symm ▸ Or.inl hx : x ∈ R₂ \ a').1
    have hHR₁ : H ⊆ R₁ := fun x hx => (hsp₁.symm ▸ Or.inl hx : x ∈ R₁ \ a).1
    have avoid : ∀ {R : Set S} {x : S}, (∀ {y}, y ∈ R → y ∉ γ) → x ∈ R →
        x ∈ ({P, Q} : Set S) → False := by
      intro R x hR hx hxPQ
      rcases hxPQ with rfl | rfl
      · exact hR hx hPγ
      · exact hR hx hQγ
    have F2 : ∀ {Aa R R'' b'' aa' : Set S}, Aa ⊆ R → (∀ {y}, y ∈ R → y ∉ γ) → R ⊆ I' →
        Disjoint R R'' → b'' ⊆ J' → aa' \ {P, Q} ⊆ R'' → Disjoint Aa (c₁ ∪ b'' ∪ c₂ ∪ aa') := by
      intro Aa R R'' b'' aa' hAR hRγ hRI' hRR'' hbJ haR''
      rw [disjoint_left]
      rintro x hxA (((hx | hx) | hx) | hx)
      · exact hRγ (hAR hxA) (Or.inl (Or.inl hx))
      · exact nI'J' (hRI' (hAR hxA)) (hbJ hx)
      · exact hRγ (hAR hxA) (Or.inr hx)
      · by_cases hxPQ : x ∈ ({P, Q} : Set S)
        · exact avoid hRγ (hAR hxA) hxPQ
        · exact disjoint_left.mp hRR'' (hAR hxA) (haR'' ⟨hx, hxPQ⟩)
    refine ⟨a, a', b₁, b₂, A₁, A₂, ha, ha', hi, hu, hb₁, hb₂, hbi, hbu, hA₁, hA₂,
      hR₁₂.mono hA₁R hA₂R, F2 hA₁R nR₁γ hR₁I' hR₁₂ hb₂J' hR₂a',
      F2 hA₂R nR₂γ hR₂I' hR₁₂.symm hb₁J' hR₁a, ?_⟩
    have hPI : P ∉ I := fun h => nIJ h hP
    have hQI : Q ∉ I := fun h => nIJ h hQ
    have curve : ∀ {b aa : Set S}, b ⊆ J' → aa ⊆ J → c₁ ∪ b ∪ c₂ ∪ aa ⊆ (J' ∪ I') \ I := by
      intro b aa hbJ haJ x hx
      rcases hx with ((hx | hx) | hx) | hx
      · refine ⟨hc₁s hx, fun hxI => ?_⟩
        have := mem_of_inter_eq' hc₁D hx (Or.inr hxI)
        exact hPI (this ▸ hxI)
      · exact ⟨Or.inl (hbJ hx), fun hxI => nI'J' (hsub (Or.inr hxI)) (hbJ hx)⟩
      · refine ⟨hc₂s hx, fun hxI => ?_⟩
        have := mem_of_inter_eq' hc₂D hx (Or.inr hxI)
        exact hQI (this ▸ hxI)
      · exact ⟨Or.inr (hsub (Or.inl (haJ hx))), fun hxI => nIJ hxI (haJ hx)⟩
    have inside : ∀ {Aa R R'' Hh Hh'' : Set S}, Aa ⊆ R → (∀ {y}, y ∈ R → y ∉ γ) → R ⊆ I' →
        Disjoint R R'' → Disjoint Hh Aa → Hh'' ⊆ R'' → I \ e = Hh ∪ Hh'' ∨ I \ e = Hh'' ∪ Hh →
        Aa ⊆ (J' ∪ I') \ I := by
      intro Aa R R'' Hh Hh'' hAR hRγ hRI' hRR'' hHA hH''R hsplit x hx
      refine ⟨Or.inr (hRI' (hAR hx)), fun hxI => ?_⟩
      have hxe : x ∉ e := fun h => hRγ (hAR hx) (Or.inl (Or.inr h))
      have hxIe : x ∈ I \ e := ⟨hxI, hxe⟩
      have : x ∈ Hh ∪ Hh'' := by
        rcases hsplit with h | h
        · rw [h] at hxIe; exact hxIe
        · rw [h] at hxIe; exact hxIe.symm
      rcases this with h | h
      · exact disjoint_left.mp hHA h hx
      · exact disjoint_left.mp hRR'' (hAR hx) (hH''R h)
    apply subset_antisymm
    · refine union_subset (union_subset (curve hb₁J' haJ) ?_) (union_subset (curve hb₂J' ha'J) ?_)
      · exact inside hA₁R nR₁γ hR₁I' hR₁₂ hdis₁ hH'R₂ (Or.inl hHH)
      · exact inside hA₂R nR₂γ hR₂I' hR₁₂.symm hdis₂ hHR₁ (Or.inr hHH)
    · rintro x ⟨hxD, hxI⟩
      have inK₁ : x ∈ c₁ ∪ c₂ → x ∈ (c₁ ∪ b₁ ∪ c₂ ∪ a) ∪ A₁ ∪ ((c₁ ∪ b₂ ∪ c₂ ∪ a') ∪ A₂) := by
        rintro (h | h)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      rcases hxD with hxJ' | hxI'
      · rw [← hbu] at hxJ'
        rcases hxJ' with h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · by_cases hxγ : x ∈ γ
        · rcases hxγ with (h | h) | h
          · exact inK₁ (Or.inl h)
          · rcases heJ x h hxI with rfl | rfl
            · exact inK₁ (Or.inl hc₁.left_mem)
            · exact inK₁ (Or.inr hc₂.left_mem)
          · exact inK₁ (Or.inr h)
        · have : x ∈ R₁ ∪ R₂ := hR ▸ ⟨hxI', hxγ⟩
          rcases this with h | h
          · by_cases hxa : x ∈ a
            · exact Or.inl (Or.inl (Or.inr hxa))
            · have : x ∈ H ∪ A₁ := hsp₁ ▸ ⟨h, hxa⟩
              rcases this with h' | h'
              · exact absurd (hHI h') hxI
              · exact Or.inl (Or.inr h')
          · by_cases hxa : x ∈ a'
            · exact Or.inr (Or.inl (Or.inr hxa))
            · have : x ∈ H' ∪ A₂ := hsp₂ ▸ ⟨h, hxa⟩
              rcases this with h' | h'
              · exact absurd (hH'I h') hxI
              · exact Or.inr (Or.inr h')
  rcases side ha₁ ha₁J with h₁ | h₁ <;> rcases side ha₂ ha₂J with h₂ | h₂
  · exact (notboth hR₁ hb₁ hb₁J' hR₂cl hR₂γ hR₁₂ h₁ h₂).elim
  · exact final ha₁ ha₂ hai hau hH₁ hH₂ hH h₁ h₂
  · exact final ha₂ ha₁ (by rw [inter_comm, hai]) (by rw [union_comm, hau]) hH₂ hH₁
      (by rw [hH, union_comm]) h₂ h₁
  · exact (notboth hR₂ hb₂ hb₂J' hR₁cl hR₁γ hR₁₂.symm h₁ h₂).elim

end Split

end HPC.Moore
