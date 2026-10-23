import HPC.Hagopian.H76Schoen

/-!
# Batch 160, item D: the Schoenflies theorem in the plane, with two adjacent sides prescribed

`plane_schoenflies₂_aux`: as `plane_schoenflies_aux` (batch 159), with the quadrilateral chosen so
that its side `AB` is the second prescribed arc `ψ` and its side `DA` is `φ`: the arc
`range ψ ∪ range φ` from `B = ψ 1` to `D = φ 1` has a complementary arc in `J`, which is cut once,
at `C` (`quad_split_two_pt`). Moore's form with all four sides prescribed
(`m19_schoenflies_boundary_proof`) is then applied with `φAB = ψ` and `φAD = φ`.

This differs from the commission's suggestion (a homeomorphism of the square straightening the
corner): no reparametrization of the square is needed, since Moore's form already prescribes two
adjacent sides.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore HPC.Moore.Gen HPC.Jones

section Schoen2

/-- **The quadrilateral with two prescribed sides.** Two arcs `φ`, `ψ` of a simple closed curve `J`
with only their first point `A` in common: the rest of `J` is cut into two arcs `sBC`, `sCD`, from
`B = ψ 1` to `C` and from `C` to `D = φ 1`, and `range ψ`, `sBC`, `sCD`, `range φ` form a
quadrilateral. -/
theorem quad_split_two_pt {J : Set Pt} (hJ : TSCC J) {φ ψ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ) (hφJ : range φ ⊆ J) (hψJ : range ψ ⊆ J)
    (h0 : φ 0 = ψ 0) (hφψ : range φ ∩ range ψ = {φ 0}) :
    ∃ (C : Pt) (sBC sCD : Set Pt), TArc (ψ 1) C sBC ∧ TArc C (φ 1) sCD ∧
      range ψ ∪ sBC ∪ sCD ∪ range φ = J ∧ range ψ ∩ sBC = {ψ 1} ∧ sBC ∩ sCD = {C} ∧
      sCD ∩ range φ = {φ 1} ∧ Disjoint (range ψ) sCD ∧ Disjoint sBC (range φ) := by
  set A := φ 0
  set B := ψ 1
  set D := φ 1
  have hψarc : TArc A B (range ψ) := ⟨fun e => zero_ne_one (hψ.injective (h0 ▸ e)), ψ, hψ, rfl,
    h0.symm, rfl⟩
  have hφarc : TArc A D (range φ) := ⟨fun e => zero_ne_one (hφ.injective e), φ, hφ, rfl, rfl, rfl⟩
  have hBφ : B ∉ range φ := fun h => by
    have : B ∈ range φ ∩ range ψ := ⟨h, mem_range_self 1⟩
    rw [hφψ, mem_singleton_iff] at this
    exact zero_ne_one (hψ.injective (this.trans h0)).symm
  have hDψ : D ∉ range ψ := fun h => by
    have : D ∈ range φ ∩ range ψ := ⟨mem_range_self 1, h⟩
    rw [hφψ, mem_singleton_iff] at this
    exact zero_ne_one (hφ.injective this).symm
  have hBD : B ≠ D := fun e => hBφ (e ▸ mem_range_self 1)
  -- the arc `α = range ψ ∪ range φ`, from `B` to `D`
  have hα : TArc B D (range ψ ∪ range φ) :=
    TArc.union hψarc.symm hφarc (by rw [inter_comm]; exact hφψ)
  have hαJ : range ψ ∪ range φ ⊆ J := union_subset hψJ hφJ
  obtain ⟨P, Q, hP, hQ, hPQ, hPQJ⟩ :=
    tscc_split_at hJ (hψJ (mem_range_self 1)) (hφJ (mem_range_self 1)) hBD
  obtain ⟨K, hK, hKα, hKJ⟩ : ∃ K, TArc B D K ∧ K ∩ (range ψ ∪ range φ) = {B, D} ∧
      K ∪ (range ψ ∪ range φ) = J := by
    rcases TArc.eq_of_subset_union hP hQ hPQ (hPQJ ▸ hαJ) hα with h | h
    · exact ⟨Q, hQ, by rw [h, inter_comm, hPQ], by rw [h, union_comm, hPQJ]⟩
    · exact ⟨P, hP, by rw [h, hPQ], by rw [h, hPQJ]⟩
  obtain ⟨C, hCK, hCBD⟩ := hK.nonempty_diff
  have hCB : C ≠ B := fun e => hCBD (by rw [e]; exact Or.inl rfl)
  have hCD : C ≠ D := fun e => hCBD (by rw [e]; exact Or.inr rfl)
  obtain ⟨K₁, K₂, hK₁, hK₂, hK12, hK12i⟩ := hK.split hCK hCB hCD
  have hK₁K : K₁ ⊆ K := hK12 ▸ subset_union_left
  have hK₂K : K₂ ⊆ K := hK12 ▸ subset_union_right
  have hBnK₂ : B ∉ K₂ := fun h => hCB.symm (by
    have : B ∈ K₁ ∩ K₂ := ⟨hK₁.left_mem, h⟩
    rw [hK12i] at this; exact this)
  have hDnK₁ : D ∉ K₁ := fun h => hCD.symm (by
    have : D ∈ K₁ ∩ K₂ := ⟨h, hK₂.right_mem⟩
    rw [hK12i] at this; exact this)
  have hKα' : ∀ z, z ∈ K → z ∈ range ψ ∪ range φ → z = B ∨ z = D := fun z h1 h2 => by
    have : z ∈ K ∩ (range ψ ∪ range φ) := ⟨h1, h2⟩
    rw [hKα] at this; simpa using this
  refine ⟨C, K₁, K₂, hK₁, hK₂, ?_, ?_, hK12i, ?_, ?_, ?_⟩
  · rw [union_assoc (range ψ), hK12, union_right_comm, union_comm, hKJ]
  · apply Subset.antisymm
    · rintro z ⟨h1, h2⟩
      rcases hKα' z (hK₁K h2) (Or.inl h1) with rfl | rfl
      · rfl
      · exact absurd h2 hDnK₁
    · rintro z rfl; exact ⟨mem_range_self 1, hK₁.left_mem⟩
  · apply Subset.antisymm
    · rintro z ⟨h1, h2⟩
      rcases hKα' z (hK₂K h1) (Or.inr h2) with rfl | rfl
      · exact absurd h1 hBnK₂
      · rfl
    · rintro z rfl; exact ⟨hK₂.right_mem, mem_range_self 1⟩
  · rw [disjoint_left]
    intro z h1 h2
    rcases hKα' z (hK₂K h2) (Or.inl h1) with rfl | rfl
    · exact hBnK₂ h2
    · exact hDψ h1
  · rw [disjoint_left]
    intro z h1 h2
    rcases hKα' z (hK₁K h1) (Or.inr h2) with rfl | rfl
    · exact hBφ h2
    · exact hDnK₁ h1

/-- **Item D: the Schoenflies theorem in the plane, with two adjacent sides prescribed.** -/
theorem plane_schoenflies₂_aux {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D)
    (hDc : IsConnected D) (hDb : Bornology.IsBounded D) (hDJ : frontier D = J)
    {φ ψ : unitInterval → Pt} (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ) (hφJ : range φ ⊆ J)
    (hψJ : range ψ ⊆ J) (h0 : φ 0 = ψ 0) (hφψ : range φ ∩ range ψ = {φ 0}) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ (∀ t, f (0, t) = ψ t) ∧
      f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D := by
  have hG := mooreDecomp_ptSetoid
  set e := ptHomeo
  set σ := spaceRestricted ptSetoid
  have htop := spaceRestricted_topology hG
  obtain ⟨C, sBC, sCD, hBC, hCD, hU, i1, i2, i3, d1, d2⟩ :=
    quad_split_two_pt hJ hφ hψ hφJ hψJ h0 hφψ
  have hAD : φ 0 ≠ φ 1 := fun h => zero_ne_one (hφ.injective h)
  have hφarc : TArc (φ 0) (φ 1) (range φ) := ⟨hAD, φ, hφ, rfl, rfl, rfl⟩
  have hψarc : TArc (φ 0) (ψ 1) (range ψ) :=
    ⟨fun e => zero_ne_one (hψ.injective (h0 ▸ e)), ψ, hψ, rfl, h0.symm, rfl⟩
  set J' := e '' J
  have hJe : IsSCCElt J' := (isSCCElt_iff_tscc hG).2 (tscc_image_embedding e.isEmbedding hJ)
  obtain ⟨hIo, hIc, -, hIf, hEo, hEc, hEb, -, hIE, hIEu⟩ := sccInterior_spec hG hJe
  have hDI : e '' D = sccInterior J' := image_eq_sccInterior hJ hD hDc hDb hDJ
  have arc : ∀ {a b : Pt} {s : Set Pt}, TArc a b s → σ.IsArc (e a) (e b) (e '' s) := fun h =>
    (isArc_restricted_iff hG).2 ((isArcElt_iff_tarc hG).2 (tarc_image_embedding e.isEmbedding h))
  have q : σ.Quad J' (sccInterior J') (e (φ 0)) (e (ψ 1)) (e C) (e (φ 1)) (e '' range ψ)
      (e '' sBC) (e '' sCD) (e '' range φ) :=
    { interior := ⟨(isSCC_restricted_iff hG).2 hJe, ⟨J', hJe, rfl⟩, by
        rw [bdry_restricted hG]; exact hIf⟩
      ab := arc hψarc
      bc := arc hBC
      cd := arc hCD
      da := arc hφarc.symm
      union := by simp only [← image_union, hU, J']
      ab_bc := by rw [← image_inter e.injective, i1, image_singleton]
      bc_cd := by rw [← image_inter e.injective, i2, image_singleton]
      cd_da := by rw [← image_inter e.injective, i3, image_singleton]
      da_ab := by rw [← image_inter e.injective, hφψ, image_singleton]
      ab_cd := (disjoint_image_iff e.injective).2 d1
      bc_da := (disjoint_image_iff e.injective).2 d2 }
  obtain ⟨-, gBC, hgBC, hrBC, h0BC, h1BC⟩ := tarc_image_embedding e.isEmbedding hBC
  obtain ⟨-, gDC, hgDC, hrDC, h0DC, h1DC⟩ := tarc_image_embedding e.isEmbedding hCD.symm
  have hgAD : IsEmbedding (e ∘ φ) := e.isEmbedding.comp hφ
  have hgAB : IsEmbedding (e ∘ ψ) := e.isEmbedding.comp hψ
  have emb : ∀ {g : unitInterval → Quotient ptSetoid}, IsEmbedding g →
      @IsEmbedding _ _ _ σ.topology g := fun h => by rw [htop]; exact h
  obtain ⟨f', hf', hf'r, hs0, hs1, hs2, hs3⟩ := m19_schoenflies_boundary_proof (m25r_axiom1 hG)
    (m25r_axiom2 hG) (m25r_axiom3 hG) (m25r_axiom4 hG) (m25r_axiom5 hG) (m25r_axiom6 hG)
    (m25r_axiom7 hG) (m25r_axiom8 hG) q (e ∘ ψ) gBC gDC (e ∘ φ)
    ⟨emb hgAB, range_comp e ψ, by simp [h0], rfl⟩ ⟨emb hgBC, hrBC, h0BC, h1BC⟩
    ⟨emb hgDC, hrDC, h0DC, h1DC⟩ ⟨emb hgAD, range_comp e φ, rfl, rfl⟩
  rw [htop] at hf'
  set f : unitInterval × unitInterval → Pt := e.symm ∘ f' with hfdef
  have hf : IsEmbedding f := e.symm.isEmbedding.comp hf'
  have hfr : range f = J ∪ D := by
    rw [hfdef, range_comp, hf'r, ← hDI, ← image_union]
    exact e.toEquiv.symm_image_image _
  have hf0 : ∀ t, f (t, 0) = φ t := fun t => by
    simp [hfdef, hs3 t]
  have hf0' : ∀ t, f (0, t) = ψ t := fun t => by
    simp [hfdef, hs0 t]
  -- the four sides go into `J`, and cover it
  have hsideJ : ∀ p : unitInterval × unitInterval,
      ¬ (0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1) → f p ∈ J := by
    rintro ⟨x, y⟩ hp
    have hx0 : (0 : unitInterval) ≤ x := unitInterval.nonneg'
    have hx1 : x ≤ 1 := unitInterval.le_one'
    have hy0 : (0 : unitInterval) ≤ y := unitInterval.nonneg'
    have hy1 : y ≤ 1 := unitInterval.le_one'
    have hmem : ∀ {s : Set Pt} {g : unitInterval → Quotient ptSetoid}, range g = e '' s →
        s ⊆ J → ∀ z, e.symm (g z) ∈ J := by
      intro s g hr hs z
      have : g z ∈ e '' s := hr ▸ mem_range_self z
      obtain ⟨w, hw, hwz⟩ := this
      rw [← hwz, e.symm_apply_apply]; exact hs hw
    rw [← hU] at *
    simp only [not_and_or, not_lt] at hp
    rcases hp with h | h | h | h
    · rw [le_antisymm h hx0]
      simp only [hfdef, Function.comp_apply, hs0]
      exact hmem (range_comp e ψ) (by intro z hz; simp [hz]) y
    · rw [le_antisymm hx1 h]
      simp only [hfdef, Function.comp_apply, hs2]
      exact hmem hrDC (by intro z hz; simp [hz]) y
    · rw [le_antisymm h hy0]
      simp only [hfdef, Function.comp_apply, hs3]
      exact hmem (range_comp e φ) (by intro z hz; simp [hz]) x
    · rw [le_antisymm hy1 h]
      simp only [hfdef, Function.comp_apply, hs1]
      exact hmem hrBC (by intro z hz; simp [hz]) x
  have hJside : ∀ z ∈ J, ∃ p : unitInterval × unitInterval,
      ¬ (0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1) ∧ f p = z := by
    intro z hz
    have pull : ∀ {s : Set Pt} {g : unitInterval → Quotient ptSetoid}, range g = e '' s →
        z ∈ s → ∃ w, e.symm (g w) = z := by
      intro s g hr hs
      obtain ⟨w, hw⟩ : e z ∈ range _ := hr ▸ mem_image_of_mem e hs
      exact ⟨w, by rw [hw, e.symm_apply_apply]⟩
    rw [← hU] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · obtain ⟨w, hw⟩ := pull (range_comp e ψ) hz
      exact ⟨(0, w), by simp, by rw [hf0']; simpa using hw⟩
    · obtain ⟨w, hw⟩ := pull hrBC hz
      exact ⟨(w, 1), by simp, by simp [hfdef, hs1, hw]⟩
    · obtain ⟨w, hw⟩ := pull hrDC hz
      exact ⟨(1, w), by simp, by simp [hfdef, hs2, hw]⟩
    · obtain ⟨w, hw⟩ := pull (range_comp e φ) hz
      exact ⟨(w, 0), by simp, by rw [hf0]; simpa using hw⟩
  have hDJd : Disjoint D J := by
    rw [← hDJ, disjoint_iff_inter_eq_empty]; exact hD.inter_frontier_eq
  refine ⟨f, hf, hfr, hf0, hf0', Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hpr : f p ∈ J ∪ D := hfr ▸ mem_range_self p
    rcases hpr with h | h
    · obtain ⟨p', hp', hfp'⟩ := hJside _ h
      exact absurd (hf.injective hfp' ▸ hp) hp'
    · exact h
  · intro z hz
    obtain ⟨p, hp⟩ : z ∈ range f := hfr ▸ Or.inr hz
    refine ⟨p, ?_, hp⟩
    by_contra hpn
    exact disjoint_left.1 hDJd hz (hp ▸ hsideJ p hpn)

end Schoen2

end HPC.Hagopian
