import HPC.Moore.M19CDCells

/-!
# Moore 1919, Theorem C as printed is false (batch 141, item C)

**The counterexample.** Let `g` be a closed curve lying, except for one point `P`, within
`ABCDA`, with `P` on the segment `AB` (in the number plane: a circle inside a square, tangent to
one side). Then `g` has only one point in common with `ABCDA` and contains none of `A, B, C, D`, so
it satisfies the hypothesis of Theorem C. But no double ruling of `ABCDA` has every subdivision
within or without `g`:

* every point of `g` within `ABCDA` must lie on an arc of the ruling (a subdivision containing it
  would meet the boundary `g` of the interior of `g`);
* near `P` the only arc of the ruling is the arc `XᵢX′ᵢ` with `Xᵢ = P`, if there is one (the arcs
  `Y` meet `ABCDA` only on `BC` and `DA`, the other arcs `X` only away from `P`);
* `g` leaves `P` along two arcs that meet only at their ends, both within `ABCDA`; both would have
  to begin along the single arc `XᵢX′ᵢ` from its endpoint `P`, and so would overlap.

`no_ruling_of_two_branches` is the second half; `tangent_configuration` builds the configuration
in every space satisfying Axioms 1–8, and `not_m19_theoremC_printed` combines them.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Refute

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7)
include h1 h2 h3 h4 h5 h7

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- If `g` leaves a point `p` of the segment `AB` along two arcs lying, except for `p`, within
`ABCDA` and meeting only at their ends, then no double ruling has every subdivision within or
without `g`. -/
theorem no_ruling_of_two_branches {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) {g Ig : Set S} (hg : σ.IsInteriorOf g Ig) {p p' : S}
    (hp : p ∈ sAB) (hpA : p ≠ A) (hpB : p ≠ B) {κ₁ κ₂ : Set S}
    (hκ₁ : @TArc S σ.topology p p' κ₁) (hκ₂ : @TArc S σ.topology p p' κ₂)
    (h12 : κ₁ ∩ κ₂ = {p, p'}) (hκg : κ₁ ∪ κ₂ ⊆ g) (hκ₁I : κ₁ \ {p} ⊆ I)
    (hκ₂I : κ₂ \ {p} ⊆ I) : ¬ ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  classical
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  intro H
  obtain ⟨hIgo, -, -, hfr, -⟩ := jordan h1 h2 h3 h4 h51 h7 hg
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  -- every point of `g` within `J` is on the ruling
  have hsub : ∀ x ∈ g, x ∈ I → x ∈ R.carrier := by
    intro x hxg hxI
    by_contra hxc
    have hxU : x ∈ connectedComponentIn (I \ R.carrier) x := mem_connectedComponentIn ⟨hxI, hxc⟩
    have hxfr : x ∈ frontier Ig := hfr ▸ hxg
    rcases H _ ⟨x, ⟨hxI, hxc⟩, rfl⟩ with h | h
    · exact (Gen.notMem_of_mem_frontier hIgo hxfr) (h hxU)
    · have := h hxU
      rw [ext_eq_compl_closure h1] at this
      exact this hxfr.1
  -- the arcs away from `p`
  have hXt : ∀ i, TArc (R.X i) (R.X' i) (R.arcX i) := fun i =>
    (isArc_iff_tarc h1 h3 h4 h51).mp (R.isArcX i)
  have hYt : ∀ j, TArc (R.Y j) (R.Y' j) (R.arcY j) := fun j =>
    (isArc_iff_tarc h1 h3 h4 h51).mp (R.isArcY j)
  have hpJ : p ∈ J := q.sAB_sub hp
  have hpY : ∀ j, p ∉ R.arcY j := by
    intro j hpY
    have : p ∈ R.arcY j ∩ J := ⟨hpY, hpJ⟩
    rw [R.arcY_inter hIJ] at this
    rcases this with h | h
    · have : p ∈ sAB ∩ sBC := ⟨hp, h ▸ (R.Y_mem j).1⟩
      rw [q.ab_bc] at this; exact hpB this
    · have : p ∈ sDA ∩ sAB := ⟨h ▸ (R.Y'_mem j).1, hp⟩
      rw [q.da_ab] at this; exact hpA this
  have hpX : ∀ i, R.X i ≠ p → p ∉ R.arcX i := by
    intro i hne hpX
    have : p ∈ R.arcX i ∩ J := ⟨hpX, hpJ⟩
    rw [R.arcX_inter hIJ] at this
    rcases this with h | h
    · exact hne h.symm
    · exact disjoint_left.mp q.ab_cd hp (h ▸ (R.X'_mem i).1)
  set N : Set S := ((⋃ j, R.arcY j) ∪ ⋃ (i : Fin n) (_ : R.X i ≠ p), R.arcX i)ᶜ with hN
  have hNo : IsOpen N := by
    refine (IsClosed.union ?_ ?_).isOpen_compl
    · exact isClosed_iUnion_of_finite fun j => (hYt j).isClosed
    · exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => (hXt i).isClosed
  have hpN : p ∈ N := by
    simp only [hN, mem_compl_iff, mem_union, mem_iUnion, not_or, not_exists]
    exact ⟨hpY, fun i hi => hpX i hi⟩
  have hcarN : ∀ x ∈ R.carrier, x ∈ N → ∃ i, R.X i = p ∧ x ∈ R.arcX i := by
    intro x hx hxN
    simp only [hN, mem_compl_iff, mem_union, mem_iUnion, not_or, not_exists] at hxN
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hXi : R.X i = p
      · exact ⟨i, hXi, hi⟩
      · exact absurd hi (hxN.2 i hXi)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact absurd hj (hxN.1 j)
  -- each branch has an initial segment in `N`, away from `p'`
  have branch : ∀ {κ : Set S}, TArc p p' κ → κ ⊆ g → κ \ {p} ⊆ I →
      ∃ ψ : unitInterval → S, IsEmbedding ψ ∧ range ψ = κ ∧ ψ 0 = p ∧ ψ 1 = p' ∧
        ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ ψ '' Icc 0 s ⊆ N := by
    intro κ hκ hκg' hκI'
    obtain ⟨-, ψ, hψ, hψr, hψ0, hψ1⟩ := hκ
    have hV : ψ ⁻¹' N ∩ Iio 1 ∈ 𝓝 (0 : unitInterval) :=
      Filter.inter_mem (hψ.continuous.continuousAt.preimage_mem_nhds (hψ0 ▸ hNo.mem_nhds hpN))
        (Iio_mem_nhds (zero_lt_one' unitInterval))
    obtain ⟨x, y, hxy, h0, hsub', -, -⟩ := exists_Icc_subset_of_mem_nhds_unitInterval hV
    have hx0 : x = 0 := le_antisymm h0.1 bot_le
    subst hx0
    refine ⟨ψ, hψ, hψr, hψ0, hψ1, y, hxy, (hsub' ⟨hxy.le, le_rfl⟩).2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (hsub' ht).1
  obtain ⟨ψ₁, hψ₁, hψ₁r, hψ₁0, hψ₁1, s₁, hs₁0, hs₁1, hs₁N⟩ := branch hκ₁
    (subset_union_left.trans hκg) hκ₁I
  obtain ⟨ψ₂, hψ₂, hψ₂r, hψ₂0, hψ₂1, s₂, hs₂0, hs₂1, hs₂N⟩ := branch hκ₂
    (subset_union_right.trans hκg) hκ₂I
  -- the initial segments lie on the ruling near `p`
  have hseg : ∀ {ψ : unitInterval → S} {κ : Set S} {s : unitInterval},
      range ψ = κ → κ ⊆ g → κ \ {p} ⊆ I → ψ '' Icc 0 s ⊆ N →
      ∀ x ∈ ψ '' Icc 0 s, x ≠ p → ∃ i, R.X i = p ∧ x ∈ R.arcX i := by
    intro ψ κ s hψr hκg' hκI' hsN x hx hxp
    obtain ⟨t, ht, rfl⟩ := hx
    have hxκ : ψ t ∈ κ := hψr ▸ mem_range_self t
    exact hcarN _ (hsub _ (hκg' hxκ) (hκI' ⟨hxκ, hxp⟩)) (hsN ⟨t, ht, rfl⟩)
  have hne₁ : ψ₁ s₁ ≠ p := fun e => hs₁0.ne' (hψ₁.injective (e.trans hψ₁0.symm))
  obtain ⟨i₀, hi₀, -⟩ := hseg hψ₁r (subset_union_left.trans hκg) hκ₁I hs₁N _
    (mem_image_of_mem _ ⟨hs₁0.le, le_rfl⟩) hne₁
  have hE : ∀ {ψ : unitInterval → S} {κ : Set S} {s : unitInterval},
      range ψ = κ → ψ 0 = p → κ ⊆ g → κ \ {p} ⊆ I → ψ '' Icc 0 s ⊆ N →
      ψ '' Icc 0 s ⊆ R.arcX i₀ := by
    intro ψ κ s hψr hψ0 hκg' hκI' hsN x hx
    by_cases hxp : x = p
    · rw [hxp, ← hi₀]; exact (hXt i₀).left_mem
    · obtain ⟨i, hi, hxi⟩ := hseg hψr hκg' hκI' hsN x hx hxp
      rwa [R.X_inj (hi.trans hi₀.symm)] at hxi
  have hE₁ := hE hψ₁r hψ₁0 (subset_union_left.trans hκg) hκ₁I hs₁N
  have hE₂ := hE hψ₂r hψ₂0 (subset_union_right.trans hκg) hκ₂I hs₂N
  obtain ⟨-, φ, hφ, hφr, hφ0, -⟩ := hXt i₀
  rw [hi₀] at hφ0
  have hpre : ∀ {ψ : unitInterval → S} {s : unitInterval}, Continuous ψ → ψ 0 = p →
      ψ '' Icc 0 s ⊆ R.arcX i₀ → ψ s ≠ p →
      ∃ u : unitInterval, 0 < u ∧ Icc 0 u ⊆ φ ⁻¹' (ψ '' Icc 0 s) := by
    intro ψ s hψc hψ0 hsub' hne
    have hc : IsPreconnected (φ ⁻¹' (ψ '' Icc 0 s)) :=
      isPreconnected_preimage_of_embedding hφ (isPreconnected_Icc.image _ hψc.continuousOn)
        (hφr ▸ hsub')
    obtain ⟨u, hu⟩ : ψ s ∈ range φ := hφr ▸ hsub' (mem_image_of_mem _ ⟨bot_le, le_rfl⟩)
    have hu0 : u ≠ 0 := fun e => hne (by rw [← hu, e, hφ0])
    refine ⟨u, lt_of_le_of_ne bot_le (Ne.symm hu0), hc.Icc_subset ?_ ?_⟩
    · show φ 0 ∈ ψ '' Icc 0 s
      rw [hφ0, ← hψ0]; exact mem_image_of_mem _ ⟨le_rfl, bot_le⟩
    · show φ u ∈ ψ '' Icc 0 s
      rw [hu]; exact mem_image_of_mem _ ⟨bot_le, le_rfl⟩
  have hne₂ : ψ₂ s₂ ≠ p := fun e => hs₂0.ne' (hψ₂.injective (e.trans hψ₂0.symm))
  obtain ⟨u₁, hu₁, hU₁⟩ := hpre hψ₁.continuous hψ₁0 hE₁ hne₁
  obtain ⟨u₂, hu₂, hU₂⟩ := hpre hψ₂.continuous hψ₂0 hE₂ hne₂
  set u := min u₁ u₂
  have hu : 0 < u := lt_min hu₁ hu₂
  have hφu₁ : φ u ∈ ψ₁ '' Icc 0 s₁ := hU₁ ⟨bot_le, min_le_left _ _⟩
  have hφu₂ : φ u ∈ ψ₂ '' Icc 0 s₂ := hU₂ ⟨bot_le, min_le_right _ _⟩
  have hmem : φ u ∈ κ₁ ∩ κ₂ := by
    refine ⟨?_, ?_⟩
    · obtain ⟨t, -, ht⟩ := hφu₁; rw [← ht, ← hψ₁r]; exact mem_range_self t
    · obtain ⟨t, -, ht⟩ := hφu₂; rw [← ht, ← hψ₂r]; exact mem_range_self t
  rw [h12] at hmem
  rcases hmem with h | h
  · exact hu.ne' (hφ.injective (h.trans hφ0.symm))
  · obtain ⟨t, ht, htp⟩ := hφu₁
    rw [h, ← hψ₁1] at htp
    have := hψ₁.injective htp
    rw [this] at ht
    exact absurd (lt_of_le_of_lt ht.2 hs₁1) (lt_irrefl _)

end Refute

section Config

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- **A quadrilateral on a closed curve.** If the closed curve `J` (interior `I`) is the union of
two arcs from `a` to `b` parametrized by `f` and `h`, then `a, f t, b, h s` (`0 < t, s < 1`) divide
it into the four sides `f[0, t]`, `f[t, 1]`, `h[s, 1]`, `h[0, s]`. -/
theorem quad_of_params {J I : Set S} (hJ : σ.IsInteriorOf J I) {a b : S}
    {f h : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f)
    (hh : @IsEmbedding _ _ _ σ.topology h) (hf0 : f 0 = a) (hf1 : f 1 = b) (hh0 : h 0 = a)
    (hh1 : h 1 = b) (hint : range f ∩ range h = {a, b}) (hJu : J = range f ∪ range h)
    {t s : unitInterval} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    σ.Quad J I a (f t) b (h s) (f '' Icc 0 t) (f '' Icc t 1) (h '' Icc s 1) (h '' Icc 0 s) := by
  letI := σ.topology
  haveI := t2Space h1
  have arc : ∀ {x y : S} {C : Set S}, TArc x y C → σ.IsArc x y C := fun hC =>
    (isArc_iff_tarc h1 h3 h4 h51).mpr hC
  have hab : a ≠ b := fun e => by
    have := hf.injective (hf0.trans (e.trans hf1.symm))
    exact absurd this zero_ne_one
  have img : ∀ {φ : unitInterval → S} {u v : unitInterval}, IsEmbedding φ →
      φ '' Icc u v ∩ range φ = φ '' Icc u v := fun _ => inter_eq_left.mpr (image_subset_range _ _)
  have mem_img : ∀ {φ : unitInterval → S} {u v w : unitInterval}, IsEmbedding φ →
      φ w ∈ φ '' Icc u v → w ∈ Icc u v := by
    rintro φ u v w hφ ⟨w', hw', e⟩
    rwa [← hφ.injective e]
  have sing : ∀ {φ : unitInterval → S} {u v w : unitInterval}, IsEmbedding φ → u ≤ v → v ≤ w →
      φ '' Icc u v ∩ φ '' Icc v w = {φ v} := by
    intro φ u v w hφ huv hvw
    rw [← image_inter hφ.injective, Icc_inter_Icc_eq_singleton huv hvw, image_singleton]
  -- points of `range f ∩ range h`
  have both : ∀ {x : S}, x ∈ range f → x ∈ range h → x = a ∨ x = b := by
    intro x hx hx'
    have : x ∈ range f ∩ range h := ⟨hx, hx'⟩
    rw [hint] at this; exact this
  refine ⟨hJ, arc (hf0 ▸ TArc.image_Icc hf ht0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := TArc.image_Icc hf ht1; rw [hf1] at this; exact arc this
  · have := (TArc.image_Icc hh hs1).symm; rw [hh1] at this; exact arc this
  · have := (TArc.image_Icc hh hs0).symm; rw [hh0] at this; exact arc this
  · -- union
    rw [hJu, union_assoc, union_comm (h '' Icc s 1), ← image_union, ← image_union,
      Icc_union_Icc_eq_Icc ht0.le ht1.le, Icc_union_Icc_eq_Icc hs0.le hs1.le,
      unitInterval_Icc_zero_one, image_univ, image_univ]
  · exact sing hf bot_le ht1.le
  · -- `f[t,1] ∩ h[s,1] = {b}`
    apply subset_antisymm
    · rintro x ⟨hx, hx'⟩
      rcases both (image_subset_range _ _ hx) (image_subset_range _ _ hx') with rfl | rfl
      · rw [← hf0] at hx
        exact absurd (mem_img hf hx).1 (not_le.mpr ht0)
      · rfl
    · rintro x rfl
      exact ⟨⟨1, ⟨ht1.le, le_rfl⟩, hf1⟩, ⟨1, ⟨hs1.le, le_rfl⟩, hh1⟩⟩
  · rw [inter_comm]; exact sing hh bot_le hs1.le
  · -- `h[0,s] ∩ f[0,t] = {a}`
    apply subset_antisymm
    · rintro x ⟨hx, hx'⟩
      rcases both (image_subset_range _ _ hx') (image_subset_range _ _ hx) with rfl | rfl
      · rfl
      · rw [← hh1] at hx
        exact absurd (mem_img hh hx).2 (not_le.mpr hs1)
    · rintro x rfl
      exact ⟨⟨0, ⟨le_rfl, hs0.le⟩, hh0⟩, ⟨0, ⟨le_rfl, ht0.le⟩, hf0⟩⟩
  · -- `f[0,t] ∩ h[s,1] = ∅`
    rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx'⟩
    rcases both (image_subset_range _ _ hx) (image_subset_range _ _ hx') with rfl | rfl
    · rw [← hh0] at hx'
      exact absurd (mem_img hh hx').1 (not_le.mpr hs0)
    · rw [← hf1] at hx
      exact absurd (mem_img hf hx).2 (not_le.mpr ht1)
  · -- `f[t,1] ∩ h[0,s] = ∅`
    rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx'⟩
    rcases both (image_subset_range _ _ hx) (image_subset_range _ _ hx') with rfl | rfl
    · rw [← hf0] at hx
      exact absurd (mem_img hf hx).1 (not_le.mpr ht0)
    · rw [← hh1] at hx'
      exact absurd (mem_img hh hx').2 (not_le.mpr hs1)

end Config

section Config2

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The configuration of the counterexample**: a quadrilateral `ABCDA` and a closed curve `g`
meeting it in a single point `p` of the segment `AB`, `g` being the union of two arcs from `p` that
lie, except for `p`, within `ABCDA`. -/
theorem tangent_configuration :
    ∃ (J I : Set S) (A B C D : S) (sAB sBC sCD sDA : Set S) (g Ig : Set S) (p p' : S)
      (κ₁ κ₂ : Set S), σ.Quad J I A B C D sAB sBC sCD sDA ∧ σ.IsInteriorOf g Ig ∧
      g ∩ J = {p} ∧ p ∈ sAB ∧ p ≠ A ∧ p ≠ B ∧ @TArc S σ.topology p p' κ₁ ∧
      @TArc S σ.topology p p' κ₂ ∧ κ₁ ∩ κ₂ = {p, p'} ∧ g = κ₁ ∪ κ₂ ∧ κ₁ \ {p} ⊆ I ∧
      κ₂ \ {p} ⊆ I := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  -- a closed curve
  obtain ⟨M, hMinf, -⟩ := id h5
  obtain ⟨x, -⟩ := hMinf.nonempty
  obtain ⟨R, hR, hxR⟩ := Space.exists_region_mem h1 x
  obtain ⟨J, -, I, hJI, -⟩ := fa_theorem36 h1 h2 h3 h4 h5 h6 h7 h8 hR hxR
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ, -, -, -, hJt⟩ := jordan h1 h2 h3 h4 h51 h7 hJI
  obtain ⟨a, b, C₁, C₂, hC₁, hC₂, hint, hJu⟩ := hJt
  obtain ⟨hab, f, hf, hfr, hf0, hf1⟩ := hC₁
  obtain ⟨-, h, hh, hhr, hh0, hh1⟩ := hC₂
  subst hfr hhr
  -- the parameters
  set t₁ : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩
  set t : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩
  set s : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₁0 : (0 : unitInterval) < t₁ := by
    show ((0 : unitInterval) : ℝ) < 1 / 3; norm_num
  have ht₁t : t₁ < t := by show (1 / 3 : ℝ) < 2 / 3; norm_num
  have ht0 : (0 : unitInterval) < t := ht₁0.trans ht₁t
  have ht1 : t < 1 := by show (2 / 3 : ℝ) < ((1 : unitInterval) : ℝ); norm_num
  have hs0 : (0 : unitInterval) < s := by show ((0 : unitInterval) : ℝ) < 1 / 2; norm_num
  have hs1 : s < 1 := by show (1 / 2 : ℝ) < ((1 : unitInterval) : ℝ); norm_num
  have hq := quad_of_params h1 h3 h4 h51 hJI hf hh hf0 hf1 hh0 hh1 hint hJu ht0 ht1 hs0 hs1
  set p := f t₁
  have hpAB : p ∈ f '' Icc 0 t := ⟨t₁, ⟨ht₁0.le, ht₁t.le⟩, rfl⟩
  have hpa : p ≠ a := fun e => ht₁0.ne' (hf.injective (e.trans hf0.symm))
  have hpB : p ≠ f t := fun e => ht₁t.ne (hf.injective e)
  have hpb : p ≠ b := fun e => (ht₁t.trans ht1).ne (hf.injective (e.trans hf1.symm))
  have hpJ : p ∈ J := hJu ▸ Or.inl (mem_range_self t₁)
  have hbJ : b ∈ J := hJu ▸ Or.inl (hf1 ▸ mem_range_self 1)
  -- a cross-cut `κ` from `p` to `b`, and a point `p'` on it
  obtain ⟨κ, hκ, hκI⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hJI (Or.inl rfl) hpJ hbJ hpb
  obtain ⟨p', hp'⟩ := hκ.nonempty_diff
  have hp'I : p' ∈ I := hκI hp'
  simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at hp'
  obtain ⟨κ₁, κ₃, hκ₁, hκ₃, hκu, hκi⟩ := hκ.split hp'.1 hp'.2.1 hp'.2.2
  have hbκ₁ : b ∉ κ₁ := fun hb => hp'.2.2 (by
    have : b ∈ κ₁ ∩ κ₃ := ⟨hb, hκ₃.right_mem⟩
    rw [hκi] at this; exact this.symm)
  have hκ₁κ : κ₁ ⊆ κ := hκu ▸ subset_union_left
  -- the region `R₁` cut off by `κ`, and a second arc from `p` to `p'` within it
  obtain ⟨K₁, R₁, -, R₂, hR₁, -, -, -, hsplit, -, hκK₁, -⟩ :=
    split_interior h1 h2 h3 h4 h5 h7 h8 hJI hpJ hbJ hκ hκI
  have hR₁I : R₁ ⊆ I := fun y hy => (hsplit.symm ▸ Or.inl hy : y ∈ I \ κ).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis₁, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  have hpp' : p ≠ p' := fun e => hp'.2.1 e.symm
  obtain ⟨κ₂, hκ₂, hκ₂R⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hR₁ (Or.inl rfl)
    (hκK₁ hκ.left_mem) (hκK₁ (hκ₁κ hκ₁.right_mem)) hpp'
  have h12 : κ₁ ∩ κ₂ = {p, p'} := by
    apply subset_antisymm
    · rintro y ⟨hy₁, hy₂⟩
      by_contra hy
      exact disjoint_left.mp hdis₁ (hκ₂R ⟨hy₂, hy⟩) (hκK₁ (hκ₁κ hy₁))
    · rintro y (rfl | rfl)
      · exact ⟨hκ₁.left_mem, hκ₂.left_mem⟩
      · exact ⟨hκ₁.right_mem, hκ₂.right_mem⟩
  have hgscc : σ.IsSCC (κ₁ ∪ κ₂) :=
    (isSCC_iff_tscc h1 h3 h4 h51).mpr ⟨p, p', κ₁, κ₂, hκ₁, hκ₂, h12, rfl⟩
  obtain ⟨Ig, hIgr, hIgb⟩ := h8 _ hgscc
  have hκ₁I : κ₁ \ {p} ⊆ I := by
    rintro y ⟨hy, hyp⟩
    refine hκI ⟨hκ₁κ hy, ?_⟩
    rintro (rfl | rfl)
    · exact hyp rfl
    · exact hbκ₁ hy
  have hκ₂I : κ₂ \ {p} ⊆ I := by
    rintro y ⟨hy, hyp⟩
    by_cases hyp' : y = p'
    · rw [hyp']; exact hp'I
    · exact hR₁I (hκ₂R ⟨hy, by rintro (rfl | rfl) <;> simp_all⟩)
  refine ⟨J, I, a, f t, b, h s, _, _, _, _, κ₁ ∪ κ₂, Ig, p, p', κ₁, κ₂, hq, ⟨hgscc, hIgr, hIgb⟩,
    ?_, hpAB, hpa, hpB, hκ₁, hκ₂, h12, rfl, hκ₁I, hκ₂I⟩
  apply subset_antisymm
  · rintro y ⟨hy, hyJ⟩
    by_contra hyp
    rcases hy with hy | hy
    · exact disjoint_left.mp hIJ (hκ₁I ⟨hy, hyp⟩) hyJ
    · exact disjoint_left.mp hIJ (hκ₂I ⟨hy, hyp⟩) hyJ
  · rintro y rfl
    exact ⟨Or.inl hκ₁.left_mem, hpJ⟩

/-- **Theorem C as printed is false** (p. 172): in every space satisfying Axioms 1–8 there are a
closed curve `ABCDA` and a closed curve `g` having only one point in common with `ABCDA` and
containing none of `A, B, C, D`, such that no double ruling of `ABCDA` has every subdivision within
or without `g`. The curve `g` touches the side `AB` from within (see the module docstring). -/
theorem not_m19_theoremC_printed :
    ¬ ∀ (J I : Set S) (A B C D : S) (sAB sBC sCD sDA : Set S)
      (q : σ.Quad J I A B C D sAB sBC sCD sDA) (g Ig : Set S), σ.IsInteriorOf g Ig →
      (g ∩ J).Finite → A ∉ g → B ∉ g → C ∉ g → D ∉ g →
      ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  intro H
  obtain ⟨J, I, A, B, C, D, sAB, sBC, sCD, sDA, g, Ig, p, p', κ₁, κ₂, q, hg, hgJ, hp, hpA, hpB,
    hκ₁, hκ₂, h12, hgu, hκ₁I, hκ₂I⟩ := tangent_configuration h1 h2 h3 h4 h5 h6 h7 h8
  have notg : ∀ {x : S}, x ∈ J → x ≠ p → x ∉ g := fun {x} hx hxp hxg => hxp (by
    have : x ∈ g ∩ J := ⟨hxg, hx⟩
    rw [hgJ] at this; exact this)
  have hCp : C ≠ p := fun e => disjoint_left.mp q.ab_cd hp (e ▸ q.cd.left_mem)
  have hDp : D ≠ p := fun e => disjoint_left.mp q.ab_cd hp (e ▸ q.cd.right_mem)
  obtain ⟨n, m, R, hR⟩ := H J I A B C D sAB sBC sCD sDA q g Ig hg (by rw [hgJ]; exact toFinite _)
    (notg (q.sAB_sub q.ab.left_mem) (Ne.symm hpA)) (notg (q.sAB_sub q.ab.right_mem) (Ne.symm hpB))
    (notg (q.sCD_sub q.cd.left_mem) hCp) (notg (q.sCD_sub q.cd.right_mem) hDp)
  exact no_ruling_of_two_branches h1 h2 h3 h4 h5 h7 R hg hp hpA hpB hκ₁ hκ₂ h12
    (hgu ▸ subset_rfl) hκ₁I hκ₂I hR

end Config2

end HPC.Moore
