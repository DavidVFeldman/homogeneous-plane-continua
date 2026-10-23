import HPC.Moore.M19GBoundary
import HPC.Moore.M19GPaste

/-!
# Moore 1919: tools for the annulus (batch 144, item B)

* `interior_unique`: a closed curve has only one interior.
* `exists_quad`: every closed curve with its interior is a quadrilateral (four points chosen on it).
* `exists_square_of_interior`: the Schoenflies form for a closed curve without chosen vertices:
  an embedding of the square onto `J ∪ I`, the boundary of the square going exactly to `J`.
* `exists_cuts`: if `J ∪ I` lies within `J'`, there are two disjoint arcs `PP'`, `QQ'` from `J` to
  `J'` lying, except for their ends, between the two curves. They are horizontal segments in the
  Schoenflies coordinates of `J' ∪ I'`, from the extreme points of `J ∪ I` on one horizontal line.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-! ### Cuts in a square (pure topology) -/

section SquareCuts

open unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- In an open set of `[0, 1]` around a point `x < 1` there is a larger point. -/
theorem exists_gt_of_mem_nhds_I {O : Set I} {x : I} (hO : O ∈ 𝓝 x) (hx : x < 1) :
    ∃ y ∈ O, x < y := by
  obtain ⟨u, hxu, hu⟩ := exists_Ico_subset_of_mem_nhds hO ⟨1, hx⟩
  obtain ⟨y, hxy, hyu⟩ := exists_between hxu
  exact ⟨y, hu ⟨hxy.le, hyu⟩, hxy⟩

/-- In an open set of `[0, 1]` around a point `x > 0` there is a smaller point. -/
theorem exists_lt_of_mem_nhds_I {O : Set I} {x : I} (hO : O ∈ 𝓝 x) (hx : 0 < x) :
    ∃ y ∈ O, y < x := by
  obtain ⟨u, hux, hu⟩ := exists_Ioc_subset_of_mem_nhds hO ⟨0, hx⟩
  obtain ⟨y, huy, hyx⟩ := exists_between hux
  exact ⟨y, hu ⟨huy, hyx.le⟩, hyx⟩

omit [T2Space X] in
/-- **The extreme points on a horizontal line.** Let `f` embed the square, and let `Jin ∪ Iin`
(closed, `Iin` open and nonempty, disjoint from `Jin`) be the image of a part of the open square.
On the horizontal line through a point of `Iin` the leftmost and rightmost points `f (xl, y₀)`,
`f (xr, y₀)` of `Jin ∪ Iin` lie on `Jin`, and `xl < xr`. -/
theorem extreme_points (f : I × I → X) (hf : IsEmbedding f) {Jin Iin : Set X}
    (hD : IsClosed (Jin ∪ Iin)) (hIo : IsOpen Iin) (hIne : Iin.Nonempty)
    (hdisj : Disjoint Jin Iin)
    (hsub : ∀ p, f p ∈ Jin ∪ Iin → 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1)
    (hrange : Iin ⊆ range f) :
    ∃ y₀ xl xr : I, 0 < y₀ ∧ y₀ < 1 ∧ 0 < xl ∧ xl < xr ∧ xr < 1 ∧ f (xr, y₀) ∈ Jin ∧
      f (xl, y₀) ∈ Jin ∧ (∀ x, xr < x → f (x, y₀) ∉ Jin ∪ Iin) ∧
      (∀ x, x < xl → f (x, y₀) ∉ Jin ∪ Iin) := by
  obtain ⟨u, hu⟩ := hIne
  obtain ⟨p₀, rfl⟩ := hrange hu
  set y₀ := p₀.2
  set g : I → X := fun x => f (x, y₀) with hg
  have hgc : Continuous g := hf.continuous.comp (continuous_id.prodMk continuous_const)
  set L := g ⁻¹' (Jin ∪ Iin) with hL
  have hLc : IsClosed L := hD.preimage hgc
  have hL0 : p₀.1 ∈ L := by show f (p₀.1, p₀.2) ∈ Jin ∪ Iin; exact Or.inr hu
  have hbdd : BddAbove L := ⟨1, fun x _ => le_one'⟩
  have hbdd' : BddBelow L := ⟨0, fun x _ => nonneg'⟩
  set xr := sSup L
  set xl := sInf L
  have hxr : xr ∈ L := hLc.csSup_mem ⟨_, hL0⟩ hbdd
  have hxl : xl ∈ L := hLc.csInf_mem ⟨_, hL0⟩ hbdd'
  have hp₀ := hsub p₀ (Or.inr hu)
  have hr' := hsub (xr, y₀) hxr
  have hl' := hsub (xl, y₀) hxl
  have above : ∀ x, xr < x → g x ∉ Jin ∪ Iin := fun x hx hxL =>
    absurd (le_csSup hbdd hxL) (not_le.mpr hx)
  have below : ∀ x, x < xl → g x ∉ Jin ∪ Iin := fun x hx hxL =>
    absurd (csInf_le hbdd' hxL) (not_le.mpr hx)
  have Jr : g xr ∈ Jin := by
    rcases hxr with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hxy⟩ := exists_gt_of_mem_nhds_I (hgc.continuousAt.preimage_mem_nhds
        (hIo.mem_nhds h)) hr'.2.1
      exact above y hxy (Or.inr hy)
  have Jl : g xl ∈ Jin := by
    rcases hxl with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hxy⟩ := exists_lt_of_mem_nhds_I (hgc.continuousAt.preimage_mem_nhds
        (hIo.mem_nhds h)) hl'.1
      exact below y hxy (Or.inr hy)
  have hlt : xl < xr := by
    have h1 : xl ≤ p₀.1 := csInf_le hbdd' hL0
    have h2 : p₀.1 ≤ xr := le_csSup hbdd hL0
    refine lt_of_le_of_ne (h1.trans h2) fun e => ?_
    have e1 : p₀.1 = xr := le_antisymm h2 (e ▸ h1)
    have : g xr = f p₀ := by rw [← e1]
    exact disjoint_left.mp hdisj Jr (this ▸ hu)
  exact ⟨y₀, xl, xr, hp₀.2.2.1, hp₀.2.2.2, hl'.1, hlt, hr'.2.1, Jr, Jl, above, below⟩

end SquareCuts

section Tools

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

omit h6 h8 in
/-- **A closed curve has only one interior.** *Axioms used: 1–5, 7.* -/
theorem interior_unique {K V W : Set S} (hV : σ.IsInteriorOf K V) (hW : σ.IsInteriorOf K W) :
    V = W := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  have key : ∀ {V W : Set S}, σ.IsInteriorOf K V → σ.IsInteriorOf K W → V ⊆ W := by
    intro V W hV hW
    obtain ⟨hVo, hVc, hVne, -, -, -, -, -, hVcl, hVK, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hV
    obtain ⟨hWo, -, -, -, hEo, hEc, -, -, hWcl, hWK, hEK, hcomp, -, -⟩ :=
      jordan h1 h2 h3 h4 h51 h7 hW
    have hVsub : V ⊆ W ∪ (closure W)ᶜ := by
      rw [← hcomp]; exact fun x hx hxK => disjoint_left.mp hVK hx hxK
    have hdis : Disjoint W (closure W)ᶜ := disjoint_compl_right.mono_left subset_closure
    rcases hVc.subset_or_subset hWo hEo hdis hVsub with h | h
    · exact h
    · exfalso
      -- `V` is open and closed in the exterior of `W`, which it meets
      have hEV : (closure W)ᶜ ⊆ V := by
        refine hEc.subset_of_closure_inter_subset hVo ?_ ?_
        · obtain ⟨x, hx⟩ := hVne; exact ⟨x, h hx, hx⟩
        · rintro x ⟨hxV, hxE⟩
          rw [hVcl] at hxV
          rcases hxV with h' | h'
          · exact h'
          · exact absurd h' (disjoint_left.mp hEK hxE)
      apply not_isCompact_univ h1 h5
      refine ((isCompact_closure_region h1 h4 hW.2.1).union
        (isCompact_closure_region h1 h4 hV.2.1)).of_isClosed_subset isClosed_univ ?_
      intro x _
      by_cases hx : x ∈ closure W
      · exact Or.inl hx
      · exact Or.inr (subset_closure (hEV hx))
  exact subset_antisymm (key hV hW) (key hW hV)

omit h6 h8 in
/-- **Every closed curve is a quadrilateral**: four points can be chosen on it. -/
theorem exists_quad {J I : Set S} (hI : σ.IsInteriorOf J I) :
    ∃ (A B C D : S) (sAB sBC sCD sDA : Set S), σ.Quad J I A B C D sAB sBC sCD sDA := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have arc : ∀ {a b : S} {K : Set S}, TArc a b K → σ.IsArc a b K := fun h =>
    (isArc_iff_tarc h1 h3 h4 h51).mpr h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨A, B, C₁, C₂, hC₁, hC₂, hCi, hJ⟩⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := hC₁
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := hC₂
  set m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hm0 : (0 : unitInterval) < m := Subtype.mk_lt_mk.mpr (by norm_num)
  have hm1 : m < 1 := Subtype.mk_lt_mk.mpr (by norm_num)
  have mf := fun {a b u : unitInterval} => mem_image_Icc_iff hf.injective (a := a) (b := b) (u := u)
  have mg := fun {a b u : unitInterval} => mem_image_Icc_iff hg.injective (a := a) (b := b) (u := u)
  have fsub : ∀ s : Set unitInterval, f '' s ⊆ C₁ := fun s => hfr ▸ image_subset_range _ _
  have gsub : ∀ s : Set unitInterval, g '' s ⊆ C₂ := fun s => hgr ▸ image_subset_range _ _
  -- a point of both `C₁` and `C₂` is `A` or `B`
  have both : ∀ {u v : unitInterval}, f u = g v → (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 1) := by
    intro u v h
    have : f u ∈ C₁ ∩ C₂ := ⟨hfr ▸ mem_range_self u, h ▸ hgr ▸ mem_range_self v⟩
    rw [hCi] at this
    rcases this with e | e
    · left; exact ⟨hf.injective (e.trans hf0.symm), hg.injective ((h.symm.trans e).trans hg0.symm)⟩
    · right
      have e : f u = B := e
      exact ⟨hf.injective (e.trans hf1.symm), hg.injective ((h.symm.trans e).trans hg1.symm)⟩
  refine ⟨A, f m, B, g m, f '' Icc 0 m, f '' Icc m 1, g '' Icc m 1, g '' Icc 0 m, ?_⟩
  refine
    { interior := hI
      ab := arc (hf0 ▸ TArc.image_Icc hf hm0)
      bc := arc (hf1 ▸ TArc.image_Icc hf hm1)
      cd := arc (hg1 ▸ (TArc.image_Icc hg hm1).symm)
      da := arc (hg0 ▸ (TArc.image_Icc hg hm0).symm)
      union := ?_
      ab_bc := ?_
      bc_cd := ?_
      cd_da := ?_
      da_ab := ?_
      ab_cd := ?_
      bc_da := ?_ }
  · rw [hJ, ← hfr, ← hgr, ← image_univ, ← image_univ (f := g)]
    have e1 : f '' Icc 0 m ∪ f '' Icc m 1 = f '' univ := by
      rw [← image_union, Icc_union_Icc_eq_Icc hm0.le hm1.le]
      congr 1; ext x; simp [unitInterval.le_one']
    have e2 : g '' Icc m 1 ∪ g '' Icc 0 m = g '' univ := by
      rw [union_comm, ← image_union, Icc_union_Icc_eq_Icc hm0.le hm1.le]
      congr 1; ext x; simp [unitInterval.le_one']
    rw [e1, union_assoc, e2]
  · rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton hm0.le hm1.le, image_singleton]
  · apply subset_antisymm
    · rintro x ⟨⟨u, hu, rfl⟩, ⟨v, hv, e⟩⟩
      rcases both e.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd hu.1 (not_le.mpr hm0)
      · exact hf1
    · rintro x rfl
      exact ⟨hf1 ▸ mf.mpr ⟨hm1.le, le_rfl⟩, hg1 ▸ mg.mpr ⟨hm1.le, le_rfl⟩⟩
  · rw [inter_comm, ← image_inter hg.injective, Icc_inter_Icc_eq_singleton hm0.le hm1.le,
      image_singleton]
  · apply subset_antisymm
    · rintro x ⟨⟨v, hv, rfl⟩, ⟨u, hu, e⟩⟩
      rcases both e with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hg0
      · exact absurd hv.2 (not_le.mpr hm1)
    · rintro x rfl
      exact ⟨hg0 ▸ mg.mpr ⟨le_rfl, hm0.le⟩, hf0 ▸ mf.mpr ⟨le_rfl, hm0.le⟩⟩
  · rw [disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, e⟩
    rcases both e.symm with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact absurd hv.1 (not_le.mpr hm0)
    · exact absurd hu.2 (not_le.mpr hm1)
  · rw [disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, e⟩
    rcases both e.symm with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact absurd hu.1 (not_le.mpr hm0)
    · exact absurd hv.2 (not_le.mpr hm1)

/-- **Schoenflies for a closed curve**: an embedding of the square onto `J ∪ I` sending a point
into `J` exactly when it is on the boundary of the square. -/
theorem exists_square_of_interior {J I : Set S} (hI : σ.IsInteriorOf J I) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      ∀ p, ((p.1 : ℝ) = 0 ∨ (p.1 : ℝ) = 1 ∨ (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1) ↔ f p ∈ J := by
  letI := σ.topology
  obtain ⟨A, B, C, D, sAB, sBC, sCD, sDA, q⟩ := exists_quad h1 h2 h3 h4 h5 h7 hI
  obtain ⟨f, hf, hfr, -, -, -, -, iAB, iBC, iCD, iDA⟩ :=
    m19_schoenflies_proof h1 h2 h3 h4 h5 h6 h7 h8 q
  refine ⟨f, hf, hfr, fun p => ⟨?_, fun hp => ?_⟩⟩
  · rintro (e | e | e | e)
    · exact q.sAB_sub (iAB ▸ mem_image_of_mem f (Icc.coe_eq_zero.mp e))
    · exact q.sCD_sub (iCD ▸ mem_image_of_mem f (Icc.coe_eq_one.mp e))
    · exact q.sDA_sub (iDA ▸ mem_image_of_mem f (Icc.coe_eq_zero.mp e))
    · exact q.sBC_sub (iBC ▸ mem_image_of_mem f (Icc.coe_eq_one.mp e))
  · rw [← q.union] at hp
    have back : ∀ {s : Set S} {P : unitInterval × unitInterval → Prop}, f '' {p | P p} = s →
        f p ∈ s → P p := by
      intro s P hs h
      rw [← hs] at h
      obtain ⟨p', hp', e⟩ := h
      exact hf.injective e ▸ hp'
    rcases hp with ((h | h) | h) | h
    · left; exact Icc.coe_eq_zero.mpr (back iAB h)
    · right; right; right; exact Icc.coe_eq_one.mpr (back iBC h)
    · right; left; exact Icc.coe_eq_one.mpr (back iCD h)
    · right; right; left; exact Icc.coe_eq_zero.mpr (back iDA h)

/-- **Two cuts of the annulus.** If `J ∪ I` lies within `J'`, there are disjoint arcs `PP'` and
`QQ'` with `P, Q` on `J` and `P', Q'` on `J'`, each meeting `J ∪ I` only in its first end and `J'`
only in its last end, and lying in `J' ∪ I'`. -/
theorem exists_cuts {J I J' I' : Set S} (hI : σ.IsInteriorOf J I) (hI' : σ.IsInteriorOf J' I')
    (hsub : J ∪ I ⊆ I') :
    ∃ (P Q P' Q' : S) (c₁ c₂ : Set S), @TArc S σ.topology P P' c₁ ∧ @TArc S σ.topology Q Q' c₂ ∧
      P ∈ J ∧ Q ∈ J ∧ P' ∈ J' ∧ Q' ∈ J' ∧ Disjoint c₁ c₂ ∧ c₁ ∩ (J ∪ I) = {P} ∧
      c₂ ∩ (J ∪ I) = {Q} ∧ c₁ ∩ J' = {P'} ∧ c₂ ∩ J' = {Q'} ∧ c₁ ⊆ J' ∪ I' ∧ c₂ ⊆ J' ∪ I' := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, hIne, -, -, -, -, -, hIcl, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ', -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI'
  obtain ⟨f, hf, hfr, hbd⟩ := exists_square_of_interior h1 h2 h3 h4 h5 h6 h7 h8 hI'
  have hD : IsClosed (J ∪ I) := by rw [union_comm, ← hIcl]; exact isClosed_closure
  have hin : ∀ p : unitInterval × unitInterval, f p ∉ J' →
      0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1 := by
    intro p hp
    have hn : ¬ ((p.1 : ℝ) = 0 ∨ (p.1 : ℝ) = 1 ∨ (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1) :=
      fun h => hp ((hbd p).mp h)
    push_neg at hn
    exact ⟨lt_of_le_of_ne unitInterval.nonneg' (fun e => hn.1 (by rw [← e]; rfl)),
      lt_of_le_of_ne unitInterval.le_one' (fun e => hn.2.1 (by rw [e]; rfl)),
      lt_of_le_of_ne unitInterval.nonneg' (fun e => hn.2.2.1 (by rw [← e]; rfl)),
      lt_of_le_of_ne unitInterval.le_one' (fun e => hn.2.2.2 (by rw [e]; rfl))⟩
  have hDJ' : ∀ {z}, z ∈ J ∪ I → z ∉ J' := fun hz hzJ => disjoint_left.mp hIJ' (hsub hz) hzJ
  obtain ⟨y₀, xl, xr, hy0, hy1, hxl0, hlr, hxr1, hJr, hJl, above, below⟩ :=
    extreme_points f hf hD hIo hIne (disjoint_comm.mp hIJ) (fun p hp => hin p (hDJ' hp))
      (fun x hx => hfr ▸ Or.inr (hsub (Or.inr hx)))
  set g : unitInterval → S := fun x => f (x, y₀) with hg
  have hge : IsEmbedding g := hf.comp (isEmbedding_prodMkLeft y₀)
  have mg := fun {a b u : unitInterval} => mem_image_Icc_iff hge.injective (a := a) (b := b)
    (u := u)
  have hgJ' : ∀ u, g u ∈ J' → u = 0 ∨ u = 1 := by
    intro u hu
    rcases (hbd _).mpr hu with e | e | e | e
    · exact Or.inl (Icc.coe_eq_zero.mp e)
    · exact Or.inr (Icc.coe_eq_one.mp e)
    · exact absurd (Icc.coe_eq_zero.mp e) hy0.ne'
    · exact absurd (Icc.coe_eq_one.mp e) hy1.ne
  have hg0 : g 0 ∈ J' := (hbd _).mp (Or.inl rfl)
  have hg1 : g 1 ∈ J' := (hbd _).mp (Or.inr (Or.inl rfl))
  refine ⟨g xr, g xl, g 1, g 0, g '' Icc xr 1, g '' Icc 0 xl, TArc.image_Icc hge hxr1,
    (TArc.image_Icc hge hxl0).symm, hJr, hJl, hg1, hg0, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  rotate_left 5
  · obtain ⟨u, -, rfl⟩ := hx; exact hfr ▸ mem_range_self _
  · obtain ⟨u, -, rfl⟩ := hx; exact hfr ▸ mem_range_self _
  · rw [disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, e⟩
    have := hge.injective e
    subst this
    exact absurd (hu.1.trans hv.2) (not_le.mpr hlr)
  · apply subset_antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, hD'⟩
      rcases hu.1.lt_or_eq with h | h
      · exact absurd hD' (above u h)
      · rw [h]; rfl
    · rintro _ rfl; exact ⟨mg.mpr ⟨le_rfl, hxr1.le⟩, Or.inl hJr⟩
  · apply subset_antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, hD'⟩
      rcases hu.2.lt_or_eq with h | h
      · exact absurd hD' (below u h)
      · rw [h]; rfl
    · rintro _ rfl; exact ⟨mg.mpr ⟨hxl0.le, le_rfl⟩, Or.inl hJl⟩
  · apply subset_antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, hu'⟩
      rcases hgJ' u hu' with rfl | rfl
      · exact absurd ((lt_of_lt_of_le hxl0 hlr.le).trans_le hu.1) (lt_irrefl _)
      · rfl
    · rintro _ rfl; exact ⟨mg.mpr ⟨hxr1.le, le_rfl⟩, hg1⟩
  · apply subset_antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, hu'⟩
      rcases hgJ' u hu' with rfl | rfl
      · rfl
      · exact absurd (hu.2.trans_lt (hlr.trans hxr1)) (lt_irrefl _)
    · rintro _ rfl; exact ⟨mg.mpr ⟨le_rfl, hxl0.le⟩, hg0⟩

end Tools

end HPC.Moore
