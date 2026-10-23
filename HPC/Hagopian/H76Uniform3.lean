import HPC.Hagopian.Hagopian76W

/-!
# Batch 179, §4: uniform heights (III) — the middle-crossing lemmas

`component_over_middle_aux` and `cover_pocket_middle_aux` (batch 175) with the height chosen before
`G`: it comes from `pi_thin_near_layer` and `hagopian76_link_control`, neither of which mentions
`G`. The proofs are the original ones.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Uniform3

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4, uniform height:** `component_over_middle_aux` with `c` before `G`. -/
theorem component_over_middle_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ y ∈ crossSet G π F D', (∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z) →
      (connectedComponentIn (crossSet G π F D') y ∩ layer d 1).Nonempty ∨
        IsCrossingComponent G π F c₁ D' (connectedComponentIn (crossSet G π F D') y) := by
  have hε := he.pos
  have hπc := hπ.continuous
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  set η := min ε₁ (1 / 100) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε₁ := min_le_left _ _
  have hη100 : η ≤ 1 / 100 := min_le_right _ _
  obtain ⟨cT, hcT, hcT1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 3 / 22)
    (b := 19 / 22) (by norm_num) (by norm_num) hη0
  obtain ⟨cL, hcL, hcL1, -, hlink⟩ := hagopian76_link_control hX hi hE he hend hπ hπS hγπ hF
    hLch.isOpen hEL hLG hη0 hηε
  refine ⟨min cT cL, lt_min hcT hcL, (min_le_left _ _).trans hcT1,
    fun G d hG hX0 c₁ D' hc₁ hR y hy hymid => ?_⟩
  have hc₁T : c₁ ≤ cT := hc₁.trans (min_le_left _ _)
  have hc₁L : c₁ ≤ cL := hc₁.trans (min_le_right _ _)
  have hc₁1 : c₁ ≤ 1 := hc₁T.trans hcT1
  obtain ⟨z, hzD, hzmid, hyz⟩ := hymid
  have hzS := hR.sub hzD
  /- `y` lies in a link `Lⱼ`, `1 ≤ j ≤ 9`, hence on a translate `h[E]`. -/
  obtain ⟨z₀, -, -, ⟨j, hyj⟩, hjb⟩ := hlink y ⟨z, ⟨⟨hzS.1.1.le, hzS.1.2.le⟩, hzS.2.1.le,
    hzS.2.2.le.trans hc₁L⟩, hyz.symm⟩
  obtain ⟨hj1, hj9, -⟩ := hjb j hyj
  obtain ⟨h, hh, ⟨x₀, hx₀E, hx₀y⟩, -⟩ := hP1 y j hj1 hj9 hyj
  set x : E := ⟨x₀, hx₀E⟩ with hxdef
  have hxy : h x = y := hx₀y
  have hnear : ∀ (q : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ →
      π (q : Pt) = F z →
      ∃ e : E, (k e : ℝ) ∈ Icc (3 / 22 : ℝ) (19 / 22) ∧ |(k e : ℝ) - z.1| < η ∧
        dist q (e : M) < η := by
    intro q z hz hqz
    obtain ⟨e, he1, he2, he3⟩ :=
      hthin q z ⟨hz.1, by linarith [hz.2.1, hc₁T], by linarith [hz.2.2, hc₁T]⟩ hqz
    exact ⟨e, he1, he2, by rw [Subtype.dist_eq]; exact he3⟩
  /- The parameter of `x` is in `(3/11, 8/11]`. -/
  obtain ⟨ex, -, hex2, hex3⟩ := hnear y z ⟨⟨hzS.1.1.le, hzS.1.2.le⟩, hzS.2.1.le, hzS.2.2.le⟩
    hyz
  have hdx : dist (x : M) (ex : M) < 2 * ε₁ := by
    have := hh (x : M)
    rw [hxy] at this
    linarith [dist_triangle (x : M) y (ex : M)]
  have hex' := abs_lt.1 hex2
  have hx3 : 3 / 11 < (k x : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have := he.sep_of_gap (m := 3) (by norm_num) (x := x) (y := ex) (by push_cast; linarith)
      (by push_cast; linarith [hzmid.1])
    linarith
  have hx8 : (k x : ℝ) ≤ 8 / 11 := by
    by_contra hcon
    push_neg at hcon
    have := he.sep_of_gap (m := 7) (by norm_num) (x := ex) (y := x)
      (by push_cast; linarith [hzmid.2]) (by push_cast; linarith)
    rw [dist_comm] at this
    linarith
  /- The open set over `D`, its closure, its frontier. -/
  set O : Set M := {m | π (m : Pt) ∈ F '' D'} with hOdef
  have hOo : IsOpen O := hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  have hclO : ∀ C ⊆ O, closure C ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := fun C hC =>
    closure_minimal (fun m hm => subset_closure (hC hm))
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc₁1)).isClosed
  have hfr : ∀ q : M, π (q : Pt) ∈ closure (F '' D') → q ∉ O →
      (∃ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) = F (t, 0)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (3 / 22, w)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (19 / 22, w)) := by
    intro q hq hqO
    have hfront : π (q : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hq, hqO⟩
    rcases hR.frontier_sub ⟨hfront, ⟨q, q.2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact Or.inl ⟨z₁, hz1, hFz.symm⟩
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inl ⟨z₂, hz2, hFz.symm⟩)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inr ⟨z₂, hz2, hFz.symm⟩)
  /- Points of `E` outside `[3/22, 19/22]` are not over `Cl D`. -/
  have hEout : ∀ e : E, ((k e : ℝ) < 3 / 22 ∨ 19 / 22 < (k e : ℝ)) →
      π ((e : M) : Pt) ∉ closure (F '' D') := by
    intro e hke hcl
    obtain ⟨w, hw, hFw⟩ := hclD hcl
    have := collar_injOn hF ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩
      ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      ((pi_E_eq hγπ hF e).symm.trans hFw.symm)
    have h1 : (k e : ℝ) = w.1 := congrArg Prod.fst this
    rcases hke with hke | hke <;> linarith [hw.1.1, hw.1.2]
  have h0 : Disjoint (layer d 0) O := by
    rw [hX0, disjoint_left]
    rintro _ ⟨e, he0, rfl⟩ hO
    have hke : (k e : ℝ) = 0 := by rw [mem_preimage, mem_singleton_iff] at he0; rw [he0]; rfl
    exact hEout e (Or.inl (by rw [hke]; norm_num)) (subset_closure hO)
  /- The ends of `h[E]` are not over `D`. -/
  obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
  have hk₀ : (k y₀ : ℝ) = 0 := by rw [hy₀]; rfl
  have hk₁ : (k y₁ : ℝ) = 1 := by rw [hy₁]; rfl
  have hy₀O : h y₀ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (h y₀) z hz hFz.symm
    have := hend.1 (y₀ : M) ⟨y₀, by show (k y₀ : ℝ) ≤ 2 / 22; rw [hk₀]; norm_num, rfl⟩ (e : M)
      ⟨e, he1.1, rfl⟩
    linarith [dist_triangle (y₀ : M) (h y₀) (e : M), hh y₀]
  have hy₁O : h y₁ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (h y₁) z hz hFz.symm
    have := hend.2 (y₁ : M) ⟨y₁, by show (20 / 22 : ℝ) ≤ (k y₁ : ℝ); rw [hk₁]; norm_num, rfl⟩
      (e : M) ⟨e, he1.2, rfl⟩
    linarith [dist_triangle (y₁ : M) (h y₁) (e : M), hh y₁]
  /- Coarse monotonicity. -/
  have hnotb : ∀ y' : E, (k y' : ℝ) ≤ 8 / 11 → ∀ w ∈ Icc 0 c₁,
      π (h y' : Pt) ≠ F (19 / 22, w) := by
    intro y' hy' w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (h y') (19 / 22, w) ⟨⟨by norm_num, le_rfl⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).1
    have := he.sep_of_gap (m := 8) (by norm_num) (x := y') (y := e) (by push_cast; linarith)
      (by push_cast; linarith)
    linarith [dist_triangle (y' : M) (h y') (e : M), hh y']
  have hnota : ∀ y' : E, 3 / 11 < (k y' : ℝ) → ∀ w ∈ Icc 0 c₁,
      π (h y' : Pt) ≠ F (3 / 22, w) := by
    intro y' hy' w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (h y') (3 / 22, w) ⟨⟨le_rfl, by norm_num⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).2
    have := he.sep_of_gap (m := 2) (by norm_num) (x := e) (y := y') (by push_cast; linarith)
      (by push_cast; linarith)
    rw [dist_comm] at he3
    linarith [dist_triangle (e : M) (h y') (y' : M), hh y', dist_comm (y' : M) (h y')]
  /- No point of the closure of a connected part of `O` through `y` is over the axis. -/
  have hyE : (y : M) ∉ E := by
    intro hyE
    have := collar_injOn hF ⟨⟨(k ⟨y, hyE⟩).2.1, (k ⟨y, hyE⟩).2.2⟩, by norm_num, by norm_num⟩
      ⟨⟨by linarith [hzS.1.1], by linarith [hzS.1.2]⟩, by linarith [hzS.2.1],
        by linarith [hzS.2.2]⟩ ((pi_E_eq hγπ hF ⟨y, hyE⟩).symm.trans hyz)
    have h2 : (0 : ℝ) = z.2 := congrArg Prod.snd this
    linarith [hzS.2.1]
  have hnoaxis : ∀ Z : Set M, IsPreconnected Z → y ∈ Z → Z ⊆ O → ∀ q ∈ closure Z,
      ∀ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) ≠ F (t, 0) := by
    intro Z hZ hyZ hZO q hq t ht hqt
    have hqE := mem_E_of_axis hE hπS hγπ hF ⟨by linarith [ht.1], by linarith [ht.2]⟩ hqt
    have hZc : Fold.Q78.IsContinuum (closure Z) :=
      ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyZ⟩, hZ.closure⟩
    have hend' : ∀ s : unitInterval, ((s : ℝ) < 3 / 22 ∨ 19 / 22 < (s : ℝ)) →
        Disjoint (closure Z) (layer k s) := by
      intro s hs
      rw [disjoint_left]
      rintro p hp ⟨e, hes, rfl⟩
      have hke : k e = s := by rwa [mem_preimage, mem_singleton_iff] at hes
      exact hEout e (by rw [hke]; exact hs) (hclO Z hZO hp)
    have hsub := hagopian76_no_hair hX hi hE hZc ⟨q, hq, hqE⟩
      (hend' 0 (Or.inl (by norm_num))) (hend' 1 (Or.inr (by norm_num)))
    exact hyE (hsub (subset_closure hyZ))
  /- The two halves of the translate, bumped inside `G`. -/
  set C := connectedComponentIn (crossSet G π F D') y with hCdef
  have hhalf : ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → k x ∈ S →
      ∀ y' : E, k y' ∈ S → h y' ∉ O →
      ∃ Z : Set M, IsPreconnected Z ∧ y ∈ Z ∧ Z ⊆ C ∧ Z ⊆ O ∧
        ((Z ∩ layer d 1).Nonempty ∨
          ∃ y'' : E, k y'' ∈ S ∧ h y'' ∉ O ∧ (h y'' : M) ∈ closure Z) := by
    intro S hS hSp hxS y' hy'S hy'O
    have hK : Fold.Q78.IsContinuum (h '' layerSet k S) :=
      isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1 hS hSp ⟨_, hxS⟩)
    have hyK : y ∈ h '' layerSet k S := ⟨x, ⟨x, hxS, rfl⟩, hxy⟩
    obtain ⟨Z, hZ, hyZ, hZGO, hZor⟩ := bump_in_extension hHU hAT hG hOo h0 hK hyK hy.1 hy.2
      ⟨y', ⟨y', hy'S, rfl⟩, rfl⟩ hy'O
    have hZC : Z ⊆ C := hZ.subset_connectedComponentIn hyZ fun p hp => (hZGO hp)
    refine ⟨Z, hZ, hyZ, hZC, fun p hp => (hZGO hp).2, ?_⟩
    rcases hZor with hZ1 | ⟨q, ⟨⟨_, ⟨y'', hy'', rfl⟩, rfl⟩, -⟩, hqO, hqcl⟩
    · exact Or.inl hZ1
    · exact Or.inr ⟨y'', hy'', hqO, hqcl⟩
  obtain ⟨ZL, hZL, hyZL, hZLC, hZLO, hZLor⟩ := hhalf (Iic (k x)) isClosed_Iic isPreconnected_Iic
    (mem_Iic.2 le_rfl) y₀ (show k y₀ ≤ k x by rw [hy₀]; exact unitInterval.nonneg') hy₀O
  obtain ⟨ZR, hZR, hyZR, hZRC, hZRO, hZRor⟩ := hhalf (Ici (k x)) isClosed_Ici isPreconnected_Ici
    (mem_Ici.2 le_rfl) y₁ (show k x ≤ k y₁ by rw [hy₁]; exact unitInterval.le_one') hy₁O
  rcases hZLor with hZL1 | ⟨yL, hyL, hyLO, hyLcl⟩
  · exact Or.inl (hZL1.mono (inter_subset_inter_left _ hZLC))
  rcases hZRor with hZR1 | ⟨yR, hyR, hyRO, hyRcl⟩
  · exact Or.inl (hZR1.mono (inter_subset_inter_left _ hZRC))
  right
  have hkyL : (k yL : ℝ) ≤ 8 / 11 := le_trans (Subtype.coe_le_coe.2 (mem_Iic.1 hyL)) hx8
  have hkyR : 3 / 11 < (k yR : ℝ) := lt_of_lt_of_le hx3 (Subtype.coe_le_coe.2 (mem_Ici.1 hyR))
  have hL : ∃ w ∈ Icc 0 c₁, π (h yL : Pt) = F (3 / 22, w) := by
    rcases hfr _ (hclO _ hZLO hyLcl) hyLO with ⟨t, ht, hq⟩ | hq | ⟨w, hw, hq⟩
    · exact absurd hq (hnoaxis ZL hZL hyZL hZLO _ hyLcl t ht)
    · exact hq
    · exact absurd hq (hnotb yL hkyL w hw)
  have hRt : ∃ w ∈ Icc 0 c₁, π (h yR : Pt) = F (19 / 22, w) := by
    rcases hfr _ (hclO _ hZRO hyRcl) hyRO with ⟨t, ht, hq⟩ | ⟨w, hw, hq⟩ | hq
    · exact absurd hq (hnoaxis ZR hZR hyZR hZRO _ hyRcl t ht)
    · exact absurd hq (hnota yR hkyR w hw)
    · exact hq
  obtain ⟨wL, hwL, hFL⟩ := hL
  obtain ⟨wR, hwR, hFR⟩ := hRt
  exact ⟨⟨y, hy, rfl⟩, ⟨h yL, closure_mono hZLC hyLcl, ⟨(3 / 22, wL), ⟨rfl, hwL⟩, hFL.symm⟩⟩,
    ⟨h yR, closure_mono hZRC hyRcl, ⟨(19 / 22, wR), ⟨rfl, hwR⟩, hFR.symm⟩⟩⟩

/-- **§4, uniform height:** `cover_pocket_middle_aux` with `c` before `G`. -/
theorem cover_pocket_middle_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ w ∈ crossSet G π F D', ¬ IsCrossingComponent G π F c₁ D'
        (connectedComponentIn (crossSet G π F D') w) →
      Disjoint (connectedComponentIn (crossSet G π F D') w) (layer d 1) →
      ∀ y ∈ connectedComponentIn (crossSet G π F D') w,
        ¬ ∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z := by
  obtain ⟨c, hc, hc1, hmid⟩ := component_over_middle_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL
    hLG hP1
  refine ⟨c, hc, hc1, fun G d hG hX0 c₁ D' hc₁ hR w hw hnc hdisj y hy hymid => ?_⟩
  have hmid := hmid G d hG hX0
  have hyS : y ∈ crossSet G π F D' := connectedComponentIn_subset _ _ hy
  rw [connectedComponentIn_eq hy] at hnc hdisj
  rcases hmid c₁ D' hc₁ hR y hyS hymid with h1 | h2
  · obtain ⟨q, hq1, hq2⟩ := h1
    exact disjoint_left.1 hdisj hq1 hq2
  · exact hnc h2

end Uniform3

end HPC.Hagopian
