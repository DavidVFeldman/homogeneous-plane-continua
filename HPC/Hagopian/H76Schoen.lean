import HPC.Hagopian.H76Moore28
import HPC.Moore.M19GBoundary
import HPC.Moore.M25C
import HPC.Jones.Jones55T2A
import HPC.Moore.M19CDSplit

/-!
# Batch 159, item C: the Schoenflies theorem in the plane, with one side prescribed

`plane_schoenflies_aux`: `m19_schoenflies_boundary_proof` (Moore 1919, Axioms 1–8), applied to the
space of the points of the plane with the restricted regions (`spaceRestricted ptSetoid`, which
satisfies Axioms 1–8 by batch 147: `m25r_axiom1` … `m25r_axiom8`), and transported back to `Pt`
along `ptHomeo`. The quadrilateral is obtained by cutting the complementary arc of the prescribed
arc twice (`quad_split_pt`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore HPC.Moore.Gen HPC.Jones

section Schoen

/-- **The quadrilateral.** A simple closed curve `J` and an arc `φ` in it: the complementary arc,
from `A = φ 0` to `D = φ 1`, is cut at two points `B`, `C` into three arcs, and the four arcs form a
quadrilateral `A B C D` with `DA` the range of `φ`. -/
theorem quad_split_pt {J : Set Pt} (hJ : TSCC J) {φ : unitInterval → Pt} (hφ : IsEmbedding φ)
    (hφJ : range φ ⊆ J) :
    ∃ (B C : Pt) (sAB sBC sCD : Set Pt), TArc (φ 0) B sAB ∧ TArc B C sBC ∧ TArc C (φ 1) sCD ∧
      sAB ∪ sBC ∪ sCD ∪ range φ = J ∧ sAB ∩ sBC = {B} ∧ sBC ∩ sCD = {C} ∧
      sCD ∩ range φ = {φ 1} ∧ range φ ∩ sAB = {φ 0} ∧ Disjoint sAB sCD ∧
      Disjoint sBC (range φ) := by
  set A := φ 0
  set D := φ 1
  have hAD : A ≠ D := fun e => zero_ne_one (hφ.injective e)
  have hφarc : TArc A D (range φ) := ⟨hAD, φ, hφ, rfl, rfl, rfl⟩
  obtain ⟨P, Q, hP, hQ, hPQ, hPQJ⟩ :=
    tscc_split_at hJ (hφJ (mem_range_self 0)) (hφJ (mem_range_self 1)) hAD
  -- the complementary arc `K`
  obtain ⟨K, hK, hKφ, hKJ⟩ : ∃ K, TArc A D K ∧ K ∩ range φ = {A, D} ∧ K ∪ range φ = J := by
    rcases TArc.eq_of_subset_union hP hQ hPQ (hPQJ ▸ hφJ) hφarc with h | h
    · exact ⟨Q, hQ, by rw [h, inter_comm, hPQ], by rw [h, union_comm, hPQJ]⟩
    · exact ⟨P, hP, by rw [h, hPQ], by rw [h, hPQJ]⟩
  -- first cut
  obtain ⟨B, hBK, hBAD⟩ := hK.nonempty_diff
  have hBA : B ≠ A := fun e => hBAD (by rw [e]; exact Or.inl rfl)
  have hBD : B ≠ D := fun e => hBAD (by rw [e]; exact Or.inr rfl)
  obtain ⟨K₁, K₂, hK₁, hK₂, hK12, hK12i⟩ := hK.split hBK hBA hBD
  -- second cut
  obtain ⟨C, hCK, hCBD⟩ := hK₂.nonempty_diff
  have hCB : C ≠ B := fun e => hCBD (by rw [e]; exact Or.inl rfl)
  have hCD : C ≠ D := fun e => hCBD (by rw [e]; exact Or.inr rfl)
  obtain ⟨L₁, L₂, hL₁, hL₂, hL12, hL12i⟩ := hK₂.split hCK hCB hCD
  have hL₁K₂ : L₁ ⊆ K₂ := hL12 ▸ subset_union_left
  have hL₂K₂ : L₂ ⊆ K₂ := hL12 ▸ subset_union_right
  have hK₁K : K₁ ⊆ K := hK12 ▸ subset_union_left
  have hK₂K : K₂ ⊆ K := hK12 ▸ subset_union_right
  have hAnK₂ : A ∉ K₂ := fun h => hBA.symm (by
    have : A ∈ K₁ ∩ K₂ := ⟨hK₁.left_mem, h⟩
    rw [hK12i] at this; exact this)
  have hDnK₁ : D ∉ K₁ := fun h => hBD.symm (by
    have : D ∈ K₁ ∩ K₂ := ⟨h, hK₂.right_mem⟩
    rw [hK12i] at this; exact this)
  have hBnL₂ : B ∉ L₂ := fun h => hCB.symm (by
    have : B ∈ L₁ ∩ L₂ := ⟨hL₁.left_mem, h⟩
    rw [hL12i] at this; exact this)
  have hDnL₁ : D ∉ L₁ := fun h => hCD.symm (by
    have : D ∈ L₁ ∩ L₂ := ⟨h, hL₂.right_mem⟩
    rw [hL12i] at this; exact this)
  have hKφ' : ∀ z, z ∈ K → z ∈ range φ → z = A ∨ z = D := fun z h1 h2 => by
    have : z ∈ K ∩ range φ := ⟨h1, h2⟩
    rw [hKφ] at this; simpa using this
  refine ⟨B, C, K₁, L₁, L₂, hK₁, hL₁, hL₂, ?_, ?_, hL12i, ?_, ?_, ?_, ?_⟩
  · rw [union_assoc K₁, hL12, hK12, hKJ]
  · apply Subset.antisymm
    · rintro z ⟨h1, h2⟩
      have : z ∈ K₁ ∩ K₂ := ⟨h1, hL₁K₂ h2⟩
      rwa [hK12i] at this
    · rintro z rfl; exact ⟨hK₁.right_mem, hL₁.left_mem⟩
  · apply Subset.antisymm
    · rintro z ⟨h1, h2⟩
      rcases hKφ' z (hK₂K (hL₂K₂ h1)) h2 with rfl | rfl
      · exact absurd (hL₂K₂ h1) hAnK₂
      · rfl
    · rintro z rfl; exact ⟨hL₂.right_mem, mem_range_self 1⟩
  · apply Subset.antisymm
    · rintro z ⟨h1, h2⟩
      rcases hKφ' z (hK₁K h2) h1 with rfl | rfl
      · rfl
      · exact absurd h2 hDnK₁
    · rintro z rfl; exact ⟨mem_range_self 0, hK₁.left_mem⟩
  · rw [disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    have : z ∈ K₁ ∩ K₂ := ⟨h1, hL₂K₂ h2⟩
    rw [hK12i, mem_singleton_iff] at this
    exact hBnL₂ (this ▸ h2)
  · rw [disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases hKφ' z (hK₂K (hL₁K₂ h1)) h2 with rfl | rfl
    · exact hAnK₂ (hL₁K₂ h1)
    · exact hDnL₁ h1

/-- An open connected nonempty set whose frontier is `J`, in a space where `Jᶜ` is the union of two
disjoint open connected sets `I`, `E`, is one of them. -/
theorem eq_or_eq_of_frontier {X : Type*} [TopologicalSpace X] {D J I E : Set X} (hDo : IsOpen D)
    (hDne : D.Nonempty) (hDc : IsPreconnected D) (hfr : frontier D = J) (hIo : IsOpen I)
    (hEo : IsOpen E) (hIc : IsPreconnected I) (hEc : IsPreconnected E) (hdis : Disjoint I E)
    (hu : I ∪ E = Jᶜ) : D = I ∨ D = E := by
  have hDJ : D ⊆ Jᶜ := fun x hx hxJ => by
    rw [← hfr] at hxJ
    exact hxJ.2 (hDo.interior_eq.symm ▸ hx)
  have key : ∀ {U : Set X}, IsOpen U → IsPreconnected U → U ⊆ Jᶜ → D ⊆ U → D = U := by
    intro U hUo hUc hUJ hDU
    refine Subset.antisymm hDU ?_
    have hcov : U ⊆ D ∪ (closure D)ᶜ := by
      intro x hxU
      by_cases hx : x ∈ closure D
      · left
        by_contra hxD
        exact hUJ hxU (hfr ▸ ⟨hx, by rwa [hDo.interior_eq]⟩)
      · exact Or.inr hx
    exact hUc.subset_left_of_subset_union hDo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) hcov
      (by rwa [inter_eq_right.2 hDU]) 
  rcases hDc.subset_or_subset hIo hEo hdis (hu ▸ hDJ) with h | h
  · exact Or.inl (key hIo hIc (hu ▸ subset_union_left) h)
  · exact Or.inr (key hEo hEc (hu ▸ subset_union_right) h)

/-- **Item C: the Schoenflies theorem in the plane, with one side prescribed.** -/
theorem plane_schoenflies_aux {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J)
    {φ : unitInterval → Pt} (hφ : IsEmbedding φ) (hφJ : range φ ⊆ J) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D := by
  have hG := mooreDecomp_ptSetoid
  set e := ptHomeo
  set σ := spaceRestricted ptSetoid
  have htop := spaceRestricted_topology hG
  obtain ⟨B, C, sAB, sBC, sCD, hAB, hBC, hCD, hU, i1, i2, i3, i4, d1, d2⟩ :=
    quad_split_pt hJ hφ hφJ
  have hAD : φ 0 ≠ φ 1 := fun h => zero_ne_one (hφ.injective h)
  have hφarc : TArc (φ 0) (φ 1) (range φ) := ⟨hAD, φ, hφ, rfl, rfl, rfl⟩
  set J' := e '' J
  have hJe : IsSCCElt J' := (isSCCElt_iff_tscc hG).2 (tscc_image_embedding e.isEmbedding hJ)
  obtain ⟨hIo, hIc, -, hIf, hEo, hEc, hEb, -, hIE, hIEu⟩ := sccInterior_spec hG hJe
  -- the interior is the image of `D`
  have hDI : e '' D = sccInterior J' := by
    have hD'o : IsOpen (e '' D) := e.isOpenMap _ hD
    have hD'f : frontier (e '' D) = J' := by rw [← e.image_frontier, hDJ]
    rcases eq_or_eq_of_frontier hD'o (hDc.nonempty.image _) (hDc.image _ e.continuous.continuousOn
      ).isPreconnected hD'f hIo hEo hIc.isPreconnected hEc.isPreconnected hIE hIEu with h | h
    · exact h
    · exfalso
      apply hEb
      rw [← h]
      show Bornology.IsBounded (e ⁻¹' (e '' D))
      rwa [e.preimage_image]
  have arc : ∀ {a b : Pt} {s : Set Pt}, TArc a b s → σ.IsArc (e a) (e b) (e '' s) := fun h =>
    (isArc_restricted_iff hG).2 ((isArcElt_iff_tarc hG).2 (tarc_image_embedding e.isEmbedding h))
  have q : σ.Quad J' (sccInterior J') (e (φ 0)) (e B) (e C) (e (φ 1)) (e '' sAB) (e '' sBC)
      (e '' sCD) (e '' range φ) :=
    { interior := ⟨(isSCC_restricted_iff hG).2 hJe, ⟨J', hJe, rfl⟩, by
        rw [bdry_restricted hG]; exact hIf⟩
      ab := arc hAB
      bc := arc hBC
      cd := arc hCD
      da := arc hφarc.symm
      union := by simp only [← image_union, hU, J']
      ab_bc := by rw [← image_inter e.injective, i1, image_singleton]
      bc_cd := by rw [← image_inter e.injective, i2, image_singleton]
      cd_da := by rw [← image_inter e.injective, i3, image_singleton]
      da_ab := by rw [← image_inter e.injective, i4, image_singleton]
      ab_cd := (disjoint_image_iff e.injective).2 d1
      bc_da := (disjoint_image_iff e.injective).2 d2 }
  obtain ⟨-, gAB, hgAB, hrAB, h0AB, h1AB⟩ := tarc_image_embedding e.isEmbedding hAB
  obtain ⟨-, gBC, hgBC, hrBC, h0BC, h1BC⟩ := tarc_image_embedding e.isEmbedding hBC
  obtain ⟨-, gDC, hgDC, hrDC, h0DC, h1DC⟩ := tarc_image_embedding e.isEmbedding hCD.symm
  have hgAD : IsEmbedding (e ∘ φ) := e.isEmbedding.comp hφ
  have emb : ∀ {g : unitInterval → Quotient ptSetoid}, IsEmbedding g →
      @IsEmbedding _ _ _ σ.topology g := fun h => by rw [htop]; exact h
  obtain ⟨f', hf', hf'r, hs0, hs1, hs2, hs3⟩ := m19_schoenflies_boundary_proof (m25r_axiom1 hG)
    (m25r_axiom2 hG) (m25r_axiom3 hG) (m25r_axiom4 hG) (m25r_axiom5 hG) (m25r_axiom6 hG)
    (m25r_axiom7 hG) (m25r_axiom8 hG) q gAB gBC gDC (e ∘ φ)
    ⟨emb hgAB, hrAB, h0AB, h1AB⟩ ⟨emb hgBC, hrBC, h0BC, h1BC⟩ ⟨emb hgDC, hrDC, h0DC, h1DC⟩
    ⟨emb hgAD, range_comp e φ, rfl, rfl⟩
  rw [htop] at hf'
  set f : unitInterval × unitInterval → Pt := e.symm ∘ f' with hfdef
  have hf : IsEmbedding f := e.symm.isEmbedding.comp hf'
  have hfr : range f = J ∪ D := by
    rw [hfdef, range_comp, hf'r, ← hDI, ← image_union]
    exact e.toEquiv.symm_image_image _
  have hf0 : ∀ t, f (t, 0) = φ t := fun t => by
    simp [hfdef, hs3 t]
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
      exact hmem hrAB (by intro z hz; simp [hz]) y
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
    · obtain ⟨w, hw⟩ := pull hrAB hz
      exact ⟨(0, w), by simp, by simp [hfdef, hs0, hw]⟩
    · obtain ⟨w, hw⟩ := pull hrBC hz
      exact ⟨(w, 1), by simp, by simp [hfdef, hs1, hw]⟩
    · obtain ⟨w, hw⟩ := pull hrDC hz
      exact ⟨(1, w), by simp, by simp [hfdef, hs2, hw]⟩
    · obtain ⟨w, hw⟩ := pull (range_comp e φ) hz
      exact ⟨(w, 0), by simp, by rw [hf0]; simpa using hw⟩
  have hDJd : Disjoint D J := by
    rw [← hDJ, disjoint_iff_inter_eq_empty]; exact hD.inter_frontier_eq
  refine ⟨f, hf, hfr, hf0, Subset.antisymm ?_ ?_⟩
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

/-- The bounded side of a simple closed curve of the plane corresponds to the interior
`sccInterior` of its image among the elements of `ptSetoid`. -/
theorem image_eq_sccInterior {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) :
    ptHomeo '' D = sccInterior (ptHomeo '' J) := by
  have hG := mooreDecomp_ptSetoid
  set e := ptHomeo
  have hJe : IsSCCElt (e '' J) := (isSCCElt_iff_tscc hG).2 (tscc_image_embedding e.isEmbedding hJ)
  obtain ⟨hIo, hIc, -, hIf, hEo, hEc, hEb, -, hIE, hIEu⟩ := sccInterior_spec hG hJe
  have hD'o : IsOpen (e '' D) := e.isOpenMap _ hD
  have hD'f : frontier (e '' D) = e '' J := by rw [← e.image_frontier, hDJ]
  rcases eq_or_eq_of_frontier hD'o (hDc.nonempty.image _) (hDc.image _ e.continuous.continuousOn
    ).isPreconnected hD'f hIo hEo hIc.isPreconnected hEc.isPreconnected hIE hIEu with h | h
  · exact h
  · exfalso
    apply hEb
    rw [← h]
    show Bornology.IsBounded (e ⁻¹' (e '' D))
    rwa [e.preimage_image]

/-- A restricted region, pulled back to the plane, is a bounded domain whose frontier is the
pull-back of its boundary. -/
theorem region_restricted_pt {R : Set (Quotient ptSetoid)}
    (hR : R ∈ (spaceRestricted ptSetoid).region) :
    IsOpen (ptHomeo ⁻¹' R) ∧ IsConnected (ptHomeo ⁻¹' R) ∧
      Bornology.IsBounded (ptHomeo ⁻¹' R) ∧
      frontier (ptHomeo ⁻¹' R) = ptHomeo ⁻¹' ((spaceRestricted ptSetoid).bdry R) := by
  have hG := mooreDecomp_ptSetoid
  obtain ⟨J, hJ, rfl⟩ := hR
  obtain ⟨hIo, hIc, hIb, -⟩ := sccInterior_spec hG hJ
  refine ⟨hIo.preimage ptHomeo.continuous, ptHomeo.isConnected_preimage.2 hIc, hIb, ?_⟩
  rw [bdry_restricted hG, ptHomeo.preimage_frontier]

/-- **The cross-cut theorem in the plane** (Moore 1919, Theorems 24 and 25, `split_interior_of`,
for the restricted regions of the plane): an arc `γ` from `a` to `b` lying, except for its ends, in
the bounded side `V` of the simple closed curve `C₁ ∪ C₂`, cuts `V` into the bounded sides of
`γ ∪ C₁` and `γ ∪ C₂`. -/
theorem plane_split {K V : Set Pt} (hK : TSCC K) (hVo : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V) (hVf : frontier V = K) {a b : Pt} {C₁ C₂ : Set Pt}
    (hC₁ : TArc a b C₁) (hC₂ : TArc a b C₂) (hCi : C₁ ∩ C₂ = {a, b}) (hCu : C₁ ∪ C₂ = K)
    {γ : Set Pt} (hγ : TArc a b γ) (hγV : γ \ {a, b} ⊆ V) :
    ∃ R₁ R₂ : Set Pt,
      (IsOpen R₁ ∧ IsConnected R₁ ∧ Bornology.IsBounded R₁ ∧ frontier R₁ = γ ∪ C₁) ∧
      (IsOpen R₂ ∧ IsConnected R₂ ∧ Bornology.IsBounded R₂ ∧ frontier R₂ = γ ∪ C₂) ∧
      V \ γ = R₁ ∪ R₂ ∧ Disjoint R₁ R₂ := by
  have hG := mooreDecomp_ptSetoid
  set e := ptHomeo
  set σ := spaceRestricted ptSetoid
  have htop := spaceRestricted_topology hG
  have hJe : IsSCCElt (e '' K) := (isSCCElt_iff_tscc hG).2 (tscc_image_embedding e.isEmbedding hK)
  have hV' : σ.IsInteriorOf (e '' K) (e '' V) :=
    ⟨(isSCC_restricted_iff hG).2 hJe, by
      rw [image_eq_sccInterior hK hVo hVc hVb hVf]; exact ⟨_, hJe, rfl⟩, by
      rw [bdry_restricted hG, ← e.image_frontier, hVf]⟩
  have arc : ∀ {p q : Pt} {C : Set Pt}, TArc p q C → @TArc _ σ.topology (e p) (e q) (e '' C) :=
    fun h => by rw [htop]; exact tarc_image_embedding e.isEmbedding h
  obtain ⟨R₁, R₂, hR₁, hR₂, hU, hdis⟩ := split_interior_of (m25r_axiom1 hG) (m25r_axiom2 hG)
    (m25r_axiom3 hG) (m25r_axiom4 hG) (m25r_axiom5 hG) (m25r_axiom7 hG) (m25r_axiom8 hG) hV'
    (arc hC₁) (arc hC₂) (by rw [← image_inter e.injective, hCi, image_pair])
    (by rw [← image_union, hCu]) (arc hγ)
    (by rw [← image_pair, ← image_diff e.injective]; exact image_mono hγV)
  obtain ⟨o₁, c₁, b₁, f₁⟩ := region_restricted_pt hR₁.2.1
  obtain ⟨o₂, c₂, b₂, f₂⟩ := region_restricted_pt hR₂.2.1
  refine ⟨e ⁻¹' R₁, e ⁻¹' R₂, ⟨o₁, c₁, b₁, ?_⟩, ⟨o₂, c₂, b₂, ?_⟩, ?_, hdis.preimage _⟩
  · rw [f₁, hR₁.2.2, ← image_union, e.preimage_image]
  · rw [f₂, hR₂.2.2, ← image_union, e.preimage_image]
  · rw [← preimage_union, ← hU, preimage_diff, e.preimage_image, e.preimage_image]

end Schoen

end HPC.Hagopian
