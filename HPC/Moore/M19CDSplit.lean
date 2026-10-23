import HPC.Moore.M19CDCells

/-!
# Moore 1919: cutting a quadrilateral along a cross-cut (batch 141, item E, first part)

An arc `XX′` from a point `X` of the open side `AB` to a point `X′` of the open side `CD` of the
quadrilateral `ABCDA`, lying within `ABCDA` except for its ends, cuts it into the two
quadrilaterals `AXX′DA` and `XBCX′X` (`Space.Quad.splitX`). The interior of `ABCDA` less the arc is
the union of their interiors, which are mutually exclusive. `Space.Quad.rot` turns `ABCDA` into
`BCDAB`, so that the same result applies to arcs from `BC` to `DA`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

theorem inter_eq_singleton_of_sub {U V U' V' : Set S} {p : S} (hU : U ⊆ U') (hV : V ⊆ V')
    (h : U' ∩ V' = {p}) (hpU : p ∈ U) (hpV : p ∈ V) : U ∩ V = {p} := by
  apply subset_antisymm
  · rw [← h]; exact inter_subset_inter hU hV
  · rintro y rfl; exact ⟨hpU, hpV⟩

theorem inter_eq_empty_of_sub {U V U' V' : Set S} {p : S} (hU : U ⊆ U') (hV : V ⊆ V')
    (h : U' ∩ V' = {p}) (hpU : p ∉ U) : U ∩ V = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro y ⟨hyU, hyV⟩
  have : y ∈ U' ∩ V' := ⟨hU hyU, hV hyV⟩
  rw [h] at this
  exact hpU (this ▸ hyU)

theorem union_shuffle_A (a b c d : Set S) : b ∪ (a ∪ d ∪ c) = a ∪ b ∪ c ∪ d := by
  ext; simp only [mem_union]; tauto

theorem union_shuffle_B (a b c d : Set S) : d ∪ (a ∪ b ∪ c) = a ∪ b ∪ c ∪ d := by
  ext; simp only [mem_union]; tauto

theorem union_shuffle_J (a a' b c c' d : Set S) :
    a ∪ d ∪ c ∪ (a' ∪ b ∪ c') = (a ∪ a') ∪ b ∪ (c ∪ c') ∪ d := by
  ext; simp only [mem_union]; tauto

theorem union_rot4 (a b c d : Set S) : b ∪ c ∪ d ∪ a = a ∪ b ∪ c ∪ d := by
  ext; simp only [mem_union]; tauto

theorem mem_image_Icc_iff {f : unitInterval → S} (hf : Function.Injective f) {a b u : unitInterval} :
    f u ∈ f '' Icc a b ↔ u ∈ Icc a b :=
  ⟨fun ⟨_, hw, e⟩ => hf e ▸ hw, fun h => mem_image_of_mem f h⟩

section SplitInterior

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Splitting the interior of a closed curve by a cross-cut, with the two arcs named**
(Theorems 24 and 25). If the closed curve `K` (interior `V`) is the union of two arcs `C₁`, `C₂`
from `a` to `b` meeting only in `a` and `b`, and the arc `γ` from `a` to `b` lies in `V` except for
its ends, then `V − γ` is the union of the mutually exclusive interiors of `γ + C₁` and `γ + C₂`. -/
theorem split_interior_of {K V : Set S} (hV : σ.IsInteriorOf K V) {a b : S} {C₁ C₂ : Set S}
    (hC₁ : @TArc S σ.topology a b C₁) (hC₂ : @TArc S σ.topology a b C₂) (hCi : C₁ ∩ C₂ = {a, b})
    (hCu : C₁ ∪ C₂ = K) {γ : Set S} (hγ : @TArc S σ.topology a b γ) (hγV : γ \ {a, b} ⊆ V) :
    ∃ R₁ R₂, σ.IsInteriorOf (γ ∪ C₁) R₁ ∧ σ.IsInteriorOf (γ ∪ C₂) R₂ ∧ V \ γ = R₁ ∪ R₂ ∧
      Disjoint R₁ R₂ := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hdisVK, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hV
  have hγC : ∀ {C : Set S}, C ⊆ K → TArc a b C → γ ∩ C = {a, b} := by
    intro C hCK hC
    apply subset_antisymm
    · rintro x ⟨hxγ, hxC⟩
      by_contra hx
      exact disjoint_left.mp hdisVK (hγV ⟨hxγ, hx⟩) (hCK hxC)
    · rintro x (rfl | rfl)
      · exact ⟨hγ.left_mem, hC.left_mem⟩
      · exact ⟨hγ.right_mem, hC.right_mem⟩
  have hC₁K : C₁ ⊆ K := hCu ▸ subset_union_left
  have hC₂K : C₂ ⊆ K := hCu ▸ subset_union_right
  have hscc : ∀ {C : Set S}, C ⊆ K → TArc a b C → σ.IsSCC (γ ∪ C) := fun hCK hC =>
    (isSCC_iff_tscc h1 h3 h4 h51).mpr ⟨a, b, γ, _, hγ, hC, hγC hCK hC, rfl⟩
  obtain ⟨R₁, hR₁r, hR₁b⟩ := h8 _ (hscc hC₁K hC₁)
  obtain ⟨R₂, hR₂r, hR₂b⟩ := h8 _ (hscc hC₂K hC₂)
  have hR₁ : σ.IsInteriorOf (γ ∪ C₁) R₁ := ⟨hscc hC₁K hC₁, hR₁r, hR₁b⟩
  have hR₂ : σ.IsInteriorOf (γ ∪ C₂) R₂ := ⟨hscc hC₂K hC₂, hR₂r, hR₂b⟩
  obtain ⟨c, hc⟩ := hC₁.nonempty_diff
  obtain ⟨d, hd⟩ := hC₂.nonempty_diff
  have hsep : σ.SeparatesOn K a b c d C₁ C₂ :=
    ⟨(isArc_iff_tarc h1 h3 h4 h51).mpr hC₁, (isArc_iff_tarc h1 h3 h4 h51).mpr hC₂, hCi, hCu, hc, hd⟩
  have hγa := (isArc_iff_tarc h1 h3 h4 h51).mpr hγ
  obtain ⟨-, -, hdis⟩ := fa_theorem24 h1 h2 h3 h4 h5 h7 hV hsep hγV hR₁ hR₂
  have h25 := fa_theorem25 h1 h2 h3 h4 h5 h7 h8 hV hsep hγa hγV hR₁ hR₂
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis₁, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis₂, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₂
  refine ⟨R₁, R₂, hR₁, hR₂, ?_, hdis⟩
  rw [h25]
  ext x
  simp only [mem_diff, mem_union]
  constructor
  · rintro ⟨(⟨h, -⟩ | h) | h, hxγ⟩
    · exact absurd h hxγ
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨Or.inl (Or.inr h), fun hγx => disjoint_left.mp hdis₁ h (Or.inl hγx)⟩
    · exact ⟨Or.inr h, fun hγx => disjoint_left.mp hdis₂ h (Or.inl hγx)⟩

end SplitInterior

namespace Space.Quad

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Rotation**: `ABCDA` is also the quadrilateral `BCDAB`. -/
theorem rot (q : σ.Quad J I A B C D sAB sBC sCD sDA) : σ.Quad J I B C D A sBC sCD sDA sAB where
  interior := q.interior
  ab := q.bc
  bc := q.cd
  cd := q.da
  da := q.ab
  union := by rw [← q.union]; exact union_rot4 _ _ _ _
  ab_bc := q.bc_cd
  bc_cd := q.cd_da
  cd_da := q.da_ab
  da_ab := q.ab_bc
  ab_cd := q.bc_da
  bc_da := q.ab_cd.symm

theorem disjoint_I_J (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7) (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    Disjoint I J :=
  (jordan h1 h2 h3 h4 h51 h7 q.interior).2.2.2.2.2.2.2.2.2.1

section Split

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

/-- **Cutting a quadrilateral along a cross-cut from `AB` to `CD`.** Let `f` parametrize `AB` from
`A` to `B` and `g` parametrize `CD` from `D` to `C`, and let `x` be an arc from `X = f t` to
`X′ = g s` (`0 < t, s < 1`) lying within `ABCDA` except for its ends. Then `AXX′DA` (sides
`f[0,t]`, `x`, `g[0,s]`, `DA`) and `XBCX′X` (sides `f[t,1]`, `BC`, `g[s,1]`, `x`) are
quadrilaterals whose interiors are mutually exclusive and have union `I − x`. -/
theorem splitX (q : σ.Quad J I A B C D sAB sBC sCD sDA) {f g : unitInterval → S}
    (hf : @IsEmbedding _ _ _ σ.topology f) (hfr : range f = sAB) (hf0 : f 0 = A) (hf1 : f 1 = B)
    (hg : @IsEmbedding _ _ _ σ.topology g) (hgr : range g = sCD) (hg0 : g 0 = D) (hg1 : g 1 = C)
    {t s : unitInterval} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) (hs1 : s < 1) {x : Set S}
    (hx : @TArc S σ.topology (f t) (g s) x) (hxI : x \ {f t, g s} ⊆ I) :
    ∃ IA IB, σ.Quad (f '' Icc 0 t ∪ x ∪ g '' Icc 0 s ∪ sDA) IA A (f t) (g s) D (f '' Icc 0 t) x
        (g '' Icc 0 s) sDA ∧
      σ.Quad (f '' Icc t 1 ∪ sBC ∪ g '' Icc s 1 ∪ x) IB (f t) B C (g s) (f '' Icc t 1) sBC
        (g '' Icc s 1) x ∧
      I \ x = IA ∪ IB ∧ Disjoint IA IB := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have arc : ∀ {a b : S} {K : Set S}, TArc a b K → σ.IsArc a b K := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mpr h
  have tarc : ∀ {a b : S} {K : Set S}, σ.IsArc a b K → TArc a b K := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mp h
  have hIJ := q.disjoint_I_J h1 h2 h3 h4 h51 h7
  have hxJ : ∀ {y : S}, y ∈ x → y ∈ J → y = f t ∨ y = g s := by
    intro y hy hyJ
    by_contra hne
    simp only [not_or] at hne
    exact disjoint_left.mp hIJ (hxI ⟨hy, by simp [hne.1, hne.2]⟩) hyJ
  -- the pieces
  set s₁ := f '' Icc 0 t
  set s₂ := f '' Icc t 1
  set t₁ := g '' Icc 0 s
  set t₂ := g '' Icc s 1
  have hs₁ : TArc A (f t) s₁ := hf0 ▸ TArc.image_Icc hf ht0
  have hs₂ : TArc (f t) B s₂ := hf1 ▸ TArc.image_Icc hf ht1
  have ht₁ : TArc D (g s) t₁ := hg0 ▸ TArc.image_Icc hg hs0
  have ht₂ : TArc (g s) C t₂ := hg1 ▸ TArc.image_Icc hg hs1
  have s₁AB : s₁ ⊆ sAB := hfr ▸ image_subset_range _ _
  have s₂AB : s₂ ⊆ sAB := hfr ▸ image_subset_range _ _
  have t₁CD : t₁ ⊆ sCD := hgr ▸ image_subset_range _ _
  have t₂CD : t₂ ⊆ sCD := hgr ▸ image_subset_range _ _
  have mf := fun {a b u : unitInterval} => mem_image_Icc_iff hf.injective (a := a) (b := b) (u := u)
  have mg := fun {a b u : unitInterval} => mem_image_Icc_iff hg.injective (a := a) (b := b) (u := u)
  have hAs₁ : A ∈ s₁ := hf0 ▸ mf.mpr ⟨le_rfl, ht0.le⟩
  have hAs₂ : A ∉ s₂ := hf0 ▸ fun h => (not_le.mpr ht0) (mf.mp h).1
  have hBs₂ : B ∈ s₂ := hf1 ▸ mf.mpr ⟨ht1.le, le_rfl⟩
  have hBs₁ : B ∉ s₁ := hf1 ▸ fun h => (not_le.mpr ht1) (mf.mp h).2
  have hDt₁ : D ∈ t₁ := hg0 ▸ mg.mpr ⟨le_rfl, hs0.le⟩
  have hDt₂ : D ∉ t₂ := hg0 ▸ fun h => (not_le.mpr hs0) (mg.mp h).1
  have hCt₂ : C ∈ t₂ := hg1 ▸ mg.mpr ⟨hs1.le, le_rfl⟩
  have hCt₁ : C ∉ t₁ := hg1 ▸ fun h => (not_le.mpr hs1) (mg.mp h).2
  have hXs₁ : f t ∈ s₁ := mf.mpr ⟨ht0.le, le_rfl⟩
  have hXs₂ : f t ∈ s₂ := mf.mpr ⟨le_rfl, ht1.le⟩
  have hX't₁ : g s ∈ t₁ := mg.mpr ⟨hs0.le, le_rfl⟩
  have hX't₂ : g s ∈ t₂ := mg.mpr ⟨le_rfl, hs1.le⟩
  have hs₁₂ : s₁ ∩ s₂ = {f t} := by
    rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton ht0.le ht1.le, image_singleton]
  have ht₁₂ : t₁ ∩ t₂ = {g s} := by
    rw [← image_inter hg.injective, Icc_inter_Icc_eq_singleton hs0.le hs1.le, image_singleton]
  have hs₁₂u : s₁ ∪ s₂ = sAB := by
    rw [← image_union, Icc_union_Icc_eq_Icc ht0.le ht1.le, unitInterval_Icc_zero_one, image_univ,
      hfr]
  have ht₁₂u : t₁ ∪ t₂ = sCD := by
    rw [← image_union, Icc_union_Icc_eq_Icc hs0.le hs1.le, unitInterval_Icc_zero_one, image_univ,
      hgr]
  have hXAB : f t ∈ sAB := s₁AB hXs₁
  have hX'CD : g s ∈ sCD := t₁CD hX't₁
  have hXA : f t ≠ A := fun e => ht0.ne' (hf.injective (e.trans hf0.symm))
  have hXB : f t ≠ B := fun e => ht1.ne (hf.injective (e.trans hf1.symm))
  have hX'D : g s ≠ D := fun e => hs0.ne' (hg.injective (e.trans hg0.symm))
  have hX'C : g s ≠ C := fun e => hs1.ne (hg.injective (e.trans hg1.symm))
  have nAB_CD : ∀ {y : S}, y ∈ sAB → y ∉ sCD := fun hy hy' => disjoint_left.mp q.ab_cd hy hy'
  have nBC_DA : ∀ {y : S}, y ∈ sBC → y ∉ sDA := fun hy hy' => disjoint_left.mp q.bc_da hy hy'
  have hXDA : f t ∉ sDA := fun h => hXA (by
    have : f t ∈ sDA ∩ sAB := ⟨h, hXAB⟩
    rw [q.da_ab] at this; exact this)
  have hXBC : f t ∉ sBC := fun h => hXB (by
    have : f t ∈ sAB ∩ sBC := ⟨hXAB, h⟩
    rw [q.ab_bc] at this; exact this)
  have hX'DA : g s ∉ sDA := fun h => hX'D (by
    have : g s ∈ sCD ∩ sDA := ⟨hX'CD, h⟩
    rw [q.cd_da] at this; exact this)
  have hX'BC : g s ∉ sBC := fun h => hX'C (by
    have : g s ∈ sBC ∩ sCD := ⟨h, hX'CD⟩
    rw [q.bc_cd] at this; exact this)
  -- intersections of `x` with the pieces
  have hx_sub : ∀ {K : Set S}, K ⊆ J → f t ∉ K → g s ∉ K → x ∩ K = ∅ := by
    intro K hK h₁ h₂
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyK⟩
    rcases hxJ hy (hK hyK) with rfl | rfl
    · exact h₁ hyK
    · exact h₂ hyK
  have hx_one : ∀ {K : Set S} {p : S}, K ⊆ J → p ∈ K → (p = f t ∨ p = g s) → f t ∈ K ∨ g s ∈ K →
      (f t ∈ K → f t = p) → (g s ∈ K → g s = p) → x ∩ K = {p} := by
    intro K p hK hpK hp _ h₁ h₂
    apply subset_antisymm
    · rintro y ⟨hy, hyK⟩
      rcases hxJ hy (hK hyK) with rfl | rfl
      · exact h₁ hyK
      · exact h₂ hyK
    · rintro y rfl
      refine ⟨?_, hpK⟩
      rcases hp with rfl | rfl
      · exact hx.left_mem
      · exact hx.right_mem
  have s₁J : s₁ ⊆ J := s₁AB.trans q.sAB_sub
  have s₂J : s₂ ⊆ J := s₂AB.trans q.sAB_sub
  have t₁J : t₁ ⊆ J := t₁CD.trans q.sCD_sub
  have t₂J : t₂ ⊆ J := t₂CD.trans q.sCD_sub
  have hxs₁ : x ∩ s₁ = {f t} := hx_one s₁J hXs₁ (Or.inl rfl) (Or.inl hXs₁) (fun _ => rfl)
    (fun h => absurd (t₁CD hX't₁) (nAB_CD (s₁AB h)))
  have hxs₂ : x ∩ s₂ = {f t} := hx_one s₂J hXs₂ (Or.inl rfl) (Or.inl hXs₂) (fun _ => rfl)
    (fun h => absurd (t₁CD hX't₁) (nAB_CD (s₂AB h)))
  have hxt₁ : x ∩ t₁ = {g s} := hx_one t₁J hX't₁ (Or.inr rfl) (Or.inr hX't₁)
    (fun h => absurd (t₁CD h) (nAB_CD hXAB)) (fun _ => rfl)
  have hxt₂ : x ∩ t₂ = {g s} := hx_one t₂J hX't₂ (Or.inr rfl) (Or.inr hX't₂)
    (fun h => absurd (t₂CD h) (nAB_CD hXAB)) (fun _ => rfl)
  have hxDA : x ∩ sDA = ∅ := hx_sub q.sDA_sub hXDA hX'DA
  have hxBC : x ∩ sBC = ∅ := hx_sub q.sBC_sub hXBC hX'BC
  -- the two arcs of `J` from `X` to `X′`
  have single : ∀ {y p : S} {U V : Set S}, y ∈ U → y ∈ V → U ∩ V = {p} → y = p :=
    fun {y p U V} hU hV h => by
      have h' : y ∈ U ∩ V := ⟨hU, hV⟩
      rw [h] at h'; exact h'
  have hCA : TArc (f t) (g s) (s₁ ∪ sDA ∪ t₁) := by
    refine TArc.union (TArc.union hs₁.symm (tarc q.da).symm ?_) ht₁ ?_
    · exact inter_eq_singleton_of_sub s₁AB subset_rfl (by rw [inter_comm]; exact q.da_ab) hAs₁
        (tarc q.da).right_mem
    · have e1 : s₁ ∩ t₁ = ∅ := disjoint_iff_inter_eq_empty.mp (q.ab_cd.mono s₁AB t₁CD)
      have e2 : sDA ∩ t₁ = {D} := inter_eq_singleton_of_sub subset_rfl t₁CD
        (by rw [inter_comm]; exact q.cd_da) (tarc q.da).left_mem hDt₁
      rw [union_inter_distrib_right, e1, e2, empty_union]
  have hCB : TArc (f t) (g s) (s₂ ∪ sBC ∪ t₂) := by
    refine TArc.union (TArc.union hs₂ (tarc q.bc) ?_) ht₂.symm ?_
    · exact inter_eq_singleton_of_sub s₂AB subset_rfl q.ab_bc hBs₂ (tarc q.bc).left_mem
    · have e1 : s₂ ∩ t₂ = ∅ := disjoint_iff_inter_eq_empty.mp (q.ab_cd.mono s₂AB t₂CD)
      have e2 : sBC ∩ t₂ = {C} := inter_eq_singleton_of_sub subset_rfl t₂CD q.bc_cd
        (tarc q.bc).right_mem hCt₂
      rw [union_inter_distrib_right, e1, e2, empty_union]
  have hCi : (s₁ ∪ sDA ∪ t₁) ∩ (s₂ ∪ sBC ∪ t₂) = {f t, g s} := by
    apply subset_antisymm
    · rintro y ⟨(⟨hy | hy⟩ | hy), (⟨hy' | hy'⟩ | hy')⟩
      · exact Or.inl (single hy hy' hs₁₂)
      · exact absurd (single (s₁AB hy) hy' q.ab_bc ▸ hy) hBs₁
      · exact absurd (t₂CD hy') (nAB_CD (s₁AB hy))
      · exact absurd (single hy (s₂AB hy') q.da_ab ▸ hy') hAs₂
      · exact absurd hy (nBC_DA hy')
      · exact absurd (single (t₂CD hy') hy q.cd_da ▸ hy') hDt₂
      · exact absurd (t₁CD hy) (nAB_CD (s₂AB hy'))
      · exact absurd (single hy' (t₁CD hy) q.bc_cd ▸ hy) hCt₁
      · exact Or.inr (single hy hy' ht₁₂)
    · rintro y (rfl | rfl)
      · exact ⟨Or.inl (Or.inl hXs₁), Or.inl (Or.inl hXs₂)⟩
      · exact ⟨Or.inr hX't₁, Or.inr hX't₂⟩
  have hCu : (s₁ ∪ sDA ∪ t₁) ∪ (s₂ ∪ sBC ∪ t₂) = J := by
    rw [← q.union, ← hs₁₂u, ← ht₁₂u]; exact union_shuffle_J _ _ _ _ _ _
  obtain ⟨IA, IB, hIA, hIB, hsplit, hdis⟩ :=
    split_interior_of h1 h2 h3 h4 h5 h7 h8 (K := J) (V := I) (a := f t) (b := g s)
      (C₁ := s₁ ∪ sDA ∪ t₁) (C₂ := s₂ ∪ sBC ∪ t₂) (γ := x) q.interior hCA hCB hCi hCu hx hxI
  have eA : x ∪ (s₁ ∪ sDA ∪ t₁) = s₁ ∪ x ∪ t₁ ∪ sDA := union_shuffle_A _ _ _ _
  have eB : x ∪ (s₂ ∪ sBC ∪ t₂) = s₂ ∪ sBC ∪ t₂ ∪ x := union_shuffle_B _ _ _ _
  rw [eA] at hIA
  rw [eB] at hIB
  refine ⟨IA, IB, ⟨hIA, arc hs₁, arc hx, arc ht₁.symm, q.da, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨hIB, arc hs₂, q.bc, arc ht₂.symm, arc hx.symm, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsplit, hdis⟩
  · rw [inter_comm]; exact hxs₁
  · exact hxt₁
  · exact inter_eq_singleton_of_sub t₁CD subset_rfl q.cd_da hDt₁ (tarc q.da).left_mem
  · exact inter_eq_singleton_of_sub subset_rfl s₁AB q.da_ab (tarc q.da).right_mem hAs₁
  · exact q.ab_cd.mono s₁AB t₁CD
  · exact disjoint_iff_inter_eq_empty.mpr hxDA
  · exact inter_eq_singleton_of_sub s₂AB subset_rfl q.ab_bc hBs₂ (tarc q.bc).left_mem
  · exact inter_eq_singleton_of_sub subset_rfl t₂CD q.bc_cd (tarc q.bc).right_mem hCt₂
  · rw [inter_comm]; exact hxt₂
  · exact hxs₂
  · exact q.ab_cd.mono s₂AB t₂CD
  · rw [disjoint_comm]; exact disjoint_iff_inter_eq_empty.mpr hxBC

end Split

end Space.Quad

end HPC.Moore
