import HPC.Hagopian.H76Defs

/-!
# Batch 156, item C: Lemma 3 of Hagopian 1976

Throughout, `M` is hereditarily unicoherent and atriodic (Lemma 1); `E`, `F ⊆ M` carry minimal
admissible maps `k`, `d`, with end sets `X = k⁻¹(0)`, `Z = k⁻¹(1)`, `T = d⁻¹(0)`, `V = d⁻¹(1)`;
`Y = k⁻¹(s)` with `0 < s < 1`, `U = d⁻¹(u)`.

* `subset_of_meets_avoids` (the 1975 ¶9 triod, `homeo_image_subset_of_meets`, with `h = id`): a
  continuum meeting `F` and missing `T ∪ V` lies in `F`.
* `lemma3_half`: if `h[Y]` meets `U` and misses `T ∪ V`, then `h[Y] ⊆ U`. First `h[Y] ⊆ F`. Let
  `J = F ∩ h[E]` (a continuum, hereditary unicoherence) and `[γ, δ] = k(h⁻¹[J]) ∋ s`.
  - If `γ = s`, the continuum `h k⁻¹[[0, s]]` meets `F` only in `h[Y]`, so it misses `T ∪ V`, so it
    lies in `F`; but then `h[X] ⊆ h[Y]`. Symmetrically if `δ = s`.
  - If `γ < s < δ` and `h[Y] ⊄ U`, then `h[Y]` contains the layers `d⁻¹(v)` for `v` in an open
    interval `(lo, hi)` (interval lemma), an open subset `Ω` of `F`. A point `y ∈ Ω` has a
    neighbourhood `O'` meeting `h[E]` only in `h[Y]`: points of `h k⁻¹(γ, δ)` lie in `J ⊆ F`, hence
    (near `y`) in `Ω ⊆ h[Y]`; the rest of `h[E]` is the closed set `h k⁻¹([0, γ] ∪ [δ, 1])`, which
    misses `y`. Pulling back, `Y` has nonvoid interior in `E`.
* `lemma3_aux`: both halves (the second for `h⁻¹`, using `U ∩ h[X ∪ Z] = ∅`).

The role of the 1975 `ε` (keeping `h k⁻¹[[r, t]]` off the end sets, so that it lies in `E`) is taken
by the hypothesis `h[Y] ∩ (T ∪ V) = ∅`, which puts `h[Y]` inside `F`; the comparison of `h[Y]` with
`Y` in 1975 ¶10 becomes the comparison of `F` with `h[E]` through `J`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma3

variable {M : Set Pt}

/-- A continuum meeting `F` and missing the end sets of `F` lies in `F` (the 1975 ¶9 triod). -/
theorem subset_of_meets_avoids (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {F : Set M} (hFc : Fold.Q78.IsContinuum F)
    {d : F → unitInterval} (hd : IsAdmissibleMap F d) {C : Set M} (hC : Fold.Q78.IsContinuum C)
    (hmeet : (F ∩ C).Nonempty) (havoid : Disjoint C (layer d 0 ∪ layer d 1)) : C ⊆ F := by
  have := homeo_image_subset_of_meets hHU hAT hFc hd hC (Homeomorph.refl M)
    (by simpa using hmeet) (by
      intro z hz w hw hzw
      simp only [Homeomorph.refl_apply, id] at hzw
      subst hzw
      apply havoid.le_bot ⟨hz, ?_⟩
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr ⟨w, hw, rfl⟩)
  simpa using this

/-- The end case of `lemma3_half`: a continuum `h k⁻¹[S]` (`S ∋ s` a closed interval containing an
end value `t ≠ s`) whose points in `F` all come from `Y` cannot exist. -/
theorem lemma3_end_case (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E F : Set M} (hEc : Fold.Q78.IsContinuum E)
    (hFc : Fold.Q78.IsContinuum F) {k : E → unitInterval} {d : F → unitInterval}
    (hk : IsAdmissibleMap E k) (hd : IsAdmissibleMap F d) {s : unitInterval} (h : M ≃ₜ M)
    (hhYF : h '' layer k s ⊆ F) (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1))
    {S : Set unitInterval} (hSc : IsClosed S) (hSp : IsPreconnected S) (hsS : s ∈ S)
    {t : unitInterval} (htS : t ∈ S) (hts : t ≠ s)
    (hPS : ∀ z : E, k z ∈ S → h z ∈ F → k z = s) : False := by
  set C := h '' (Subtype.val '' (k ⁻¹' S)) with hCdef
  have hC : Fold.Q78.IsContinuum C :=
    isContinuum_homeo_image h (isContinuum_img hEc.1 hk hSc hSp ⟨s, hsS⟩)
  have hCF : C ∩ F ⊆ h '' layer k s := by
    rintro _ ⟨⟨_, ⟨z, hz, rfl⟩, rfl⟩, hzF⟩
    exact ⟨z, ⟨z, hPS z hz hzF, rfl⟩, rfl⟩
  have hYC : h '' layer k s ⊆ C := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, ⟨z, ?_, rfl⟩, rfl⟩
    rw [mem_preimage, mem_singleton_iff.1 hz]
    exact hsS
  obtain ⟨y, hy⟩ := hk.2.1 s
  have hyY : h y ∈ h '' layer k s := ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  have hsub : C ⊆ F := by
    refine subset_of_meets_avoids hHU hAT hFc hd hC ⟨h y, hhYF hyY, hYC hyY⟩ ?_
    rw [disjoint_left]
    intro x hxC hxe
    have hxF : x ∈ F := by
      rcases hxe with hxe | hxe <;> exact img_subset _ hxe
    exact disjoint_left.1 h3 (hCF ⟨hxC, hxF⟩) hxe
  obtain ⟨x₀, hx₀⟩ := hk.2.1 t
  have hx₀C : h x₀ ∈ C := ⟨x₀, ⟨x₀, by rw [mem_preimage, hx₀]; exact htS, rfl⟩, rfl⟩
  have := hPS x₀ (by rw [hx₀]; exact htS) (hsub hx₀C)
  exact hts (hx₀ ▸ this)

/-- **Lemma 3, the half `h[Y] ⊆ U`.** -/
theorem lemma3_half (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    {s u : unitInterval} (hs0 : 0 < s) (hs1 : s < 1) (h : M ≃ₜ M)
    (h1 : (layer d u ∩ h '' layer k s).Nonempty)
    (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1)) :
    h '' layer k s ⊆ layer d u := by
  obtain ⟨⟨a, b, hab⟩, hk, hk0⟩ := hE
  obtain ⟨⟨a', b', hab'⟩, hd, -⟩ := hF
  have hEc := hab.1
  have hFc := hab'.1
  set Y := layer k s with hYdef
  have hY : Fold.Q78.IsContinuum Y := isContinuum_layer hEc.1 hk s
  have hhY := isContinuum_homeo_image h hY
  have hYE : Y ⊆ E := img_subset _
  have hUF : layer d u ⊆ F := img_subset _
  have hhYF : h '' Y ⊆ F := subset_of_meets_avoids hHU hAT hFc hd hhY
    (by obtain ⟨p, hpU, hpY⟩ := h1; exact ⟨p, hUF hpU, hpY⟩) h3
  have hhE := isContinuum_homeo_image h hEc
  set J := F ∩ h '' E with hJdef
  have hJ : Fold.Q78.IsContinuum J := isContinuum_inter_of_HU hHU hFc hhE
    (by obtain ⟨p, hpU, hpY⟩ := h1; exact ⟨p, hUF hpU, image_mono hYE hpY⟩)
  have hYJ : h '' Y ⊆ J := fun p hp => ⟨hhYF hp, image_mono hYE hp⟩
  set P := h.symm '' J with hPdef
  have hP : Fold.Q78.IsContinuum P := isContinuum_homeo_image h.symm hJ
  have hPE : P ⊆ E := by
    rintro _ ⟨p, ⟨-, z, hz, rfl⟩, rfl⟩
    simpa using hz
  have hmemP : ∀ z : E, h z ∈ F → (z : M) ∈ P := fun z hz =>
    ⟨h z, ⟨hz, z, z.2, rfl⟩, by simp⟩
  -- extreme values of `k` on `P`
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  set P' : Set E := Subtype.val ⁻¹' P
  have hP'c : IsCompact P' := (hP.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨y₀, hy₀⟩ := hk.2.1 s
  have hy₀Y : (y₀ : M) ∈ Y := ⟨y₀, hy₀, rfl⟩
  have hy₀P : y₀ ∈ P' := hmemP y₀ (hhYF ⟨y₀, hy₀Y, rfl⟩)
  obtain ⟨y₁, hy₁, hmin⟩ := hP'c.exists_isMinOn ⟨y₀, hy₀P⟩ hk.1.continuousOn
  obtain ⟨y₂, hy₂, hmax⟩ := hP'c.exists_isMaxOn ⟨y₀, hy₀P⟩ hk.1.continuousOn
  have hγs : k y₁ ≤ s := hy₀ ▸ hmin hy₀P
  have hsδ : s ≤ k y₂ := hy₀ ▸ hmax hy₀P
  have hFP : ∀ z : E, h z ∈ F → k y₁ ≤ k z ∧ k z ≤ k y₂ := fun z hz =>
    ⟨hmin (hmemP z hz), hmax (hmemP z hz)⟩
  rcases hγs.lt_or_eq with hγs | hγs
  swap
  · exact (lemma3_end_case hHU hAT hEc hFc hk hd h hhYF h3 isClosed_Icc isPreconnected_Icc
      ⟨hs0.le, le_rfl⟩ ⟨le_rfl, hs0.le⟩ hs0.ne fun z hz hzF =>
        le_antisymm hz.2 (hγs ▸ (hFP z hzF).1)).elim
  rcases hsδ.lt_or_eq with hsδ | hsδ
  swap
  · exact (lemma3_end_case hHU hAT hEc hFc hk hd h hhYF h3 isClosed_Icc isPreconnected_Icc
      ⟨le_rfl, hs1.le⟩ ⟨hs1.le, le_rfl⟩ hs1.ne' fun z hz hzF =>
        le_antisymm (hsδ ▸ (hFP z hzF).2) hz.1).elim
  -- the main case `γ < s < δ`
  by_contra hnot
  rw [not_subset] at hnot
  obtain ⟨w, hwY, hwU⟩ := hnot
  have hwF := hhYF hwY
  set c := d ⟨w, hwF⟩
  have hcu : c ≠ u := fun hc => hwU ⟨⟨w, hwF⟩, hc, rfl⟩
  have hmc : (h '' Y ∩ layer d c).Nonempty := ⟨w, hwY, ⟨w, hwF⟩, rfl, rfl⟩
  have hmu : (h '' Y ∩ layer d u).Nonempty := by
    obtain ⟨p, hpU, hpY⟩ := h1; exact ⟨p, hpY, hpU⟩
  obtain ⟨lo, hi, hlohi, hmlo, hmhi⟩ : ∃ lo hi : unitInterval, lo < hi ∧
      (h '' Y ∩ layer d lo).Nonempty ∧ (h '' Y ∩ layer d hi).Nonempty := by
    rcases lt_or_gt_of_ne hcu with hlt | hlt
    · exact ⟨c, u, hlt, hmc, hmu⟩
    · exact ⟨u, c, hlt, hmu, hmc⟩
  have hmid : ∀ v, lo < v → v < hi → layer d v ⊆ h '' Y := fun v hv1 hv2 =>
    layer_subset_of_meets' hab' hd hhYF hhY hmlo hmhi hv1 hv2
  obtain ⟨v₀, hv₀1, hv₀2⟩ := exists_between hlohi
  obtain ⟨y, hy⟩ := hd.2.1 v₀
  have hyY : (y : M) ∈ h '' Y := hmid v₀ hv₀1 hv₀2 ⟨y, hy, rfl⟩
  -- the open set `Ω = d⁻¹(lo, hi)` of `F`
  have hΩ : IsOpen (d ⁻¹' Ioo lo hi) := isOpen_Ioo.preimage hd.1
  obtain ⟨O, hO, hOΩ⟩ := isOpen_induced_iff.1 hΩ
  -- the closed rest of `h[E]`
  set Cl := h '' (Subtype.val '' (k ⁻¹' (Iic (k y₁) ∪ Ici (k y₂))))
  have hCl : IsClosed Cl :=
    ((isCompact_img hEc.1 hk.1 (isClosed_Iic.union isClosed_Ici)).image h.continuous).isClosed
  obtain ⟨y₃, hy₃Y, hy₃⟩ := hyY
  have hy₃E := hYE hy₃Y
  have hk3 : k ⟨y₃, hy₃E⟩ = s := by
    obtain ⟨z, hz, hz'⟩ := hy₃Y
    have : z = ⟨y₃, hy₃E⟩ := Subtype.ext hz'
    rw [← this]; exact hz
  -- the open set `Q ⊆ E`
  set Q : Set E := {z | h z ∈ O ∩ Clᶜ}
  have hQo : IsOpen Q :=
    (hO.inter hCl.isOpen_compl).preimage (h.continuous.comp continuous_subtype_val)
  have hQne : Q.Nonempty := by
    refine ⟨⟨y₃, hy₃E⟩, ?_, ?_⟩
    · show h y₃ ∈ O
      rw [hy₃]
      have : y ∈ Subtype.val ⁻¹' O := hOΩ ▸ (show d y ∈ Ioo lo hi from hy ▸ ⟨hv₀1, hv₀2⟩)
      exact this
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzy⟩
      have hz3 : (z : M) = y₃ := h.injective hzy
      have : z = ⟨y₃, hy₃E⟩ := Subtype.ext hz3
      rw [this, mem_preimage, hk3] at hz
      rcases hz with hz | hz
      · exact absurd (hz : s ≤ k y₁) (not_le.2 hγs)
      · exact absurd (hz : k y₂ ≤ s) (not_le.2 hsδ)
  have hQs : Q ⊆ k ⁻¹' {s} := by
    rintro z ⟨hzO, hzCl⟩
    have hkz : k y₁ < k z ∧ k z < k y₂ := by
      constructor
      · by_contra hle
        exact hzCl ⟨z, ⟨z, Or.inl (not_lt.1 hle), rfl⟩, rfl⟩
      · by_contra hle
        exact hzCl ⟨z, ⟨z, Or.inr (not_lt.1 hle), rfl⟩, rfl⟩
    have hzP : (z : M) ∈ P := layer_subset_of_meets' hab hk hPE hP ⟨y₁, hy₁, y₁, rfl, rfl⟩
      ⟨y₂, hy₂, y₂, rfl, rfl⟩ hkz.1 hkz.2 ⟨z, rfl, rfl⟩
    obtain ⟨p, hpJ, hpz⟩ := hzP
    have hpe : p = h z := by rw [← hpz]; simp
    have hzF : h z ∈ F := hpe ▸ hpJ.1
    have hΩz : (⟨h z, hzF⟩ : F) ∈ d ⁻¹' Ioo lo hi := by
      rw [← hOΩ]; exact hzO
    have hzhY : h z ∈ h '' Y := hmid _ hΩz.1 hΩz.2 ⟨⟨h z, hzF⟩, rfl, rfl⟩
    obtain ⟨z', hz'Y, hz'e⟩ := hzhY
    have hzz : (z : M) = z' := (h.injective hz'e).symm
    obtain ⟨z'', hz'', hz''e⟩ := hz'Y
    have : z = z'' := Subtype.ext (hzz.trans hz''e.symm)
    rw [this]; exact hz''
  have hint : (interior (k ⁻¹' {s})).Nonempty :=
    hQne.mono (interior_maximal hQs hQo)
  rw [hk0 s] at hint
  exact not_nonempty_empty hint

/-- **Lemma 3.** Both halves. -/
theorem lemma3_aux (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    {s u : unitInterval} (hs0 : 0 < s) (hs1 : s < 1) (h : M ≃ₜ M)
    (h1 : (layer d u ∩ h '' layer k s).Nonempty)
    (h2 : Disjoint (layer d u) (h '' (layer k 0 ∪ layer k 1)))
    (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1)) :
    h '' layer k s = layer d u := by
  have hsub := lemma3_half hHU hAT hE hF hs0 hs1 h h1 h3
  refine subset_antisymm hsub ?_
  -- `u` is an interior value
  obtain ⟨p, hpU, hpY⟩ := h1
  have hu0 : 0 < u := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun hu => ?_
    exact disjoint_left.1 h3 hpY (Or.inl (hu ▸ hpU))
  have hu1 : u < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun hu => ?_
    exact disjoint_left.1 h3 hpY (Or.inr (hu ▸ hpU))
  have hsub' := lemma3_half hHU hAT hF hE hu0 hu1 h.symm
    (by
      obtain ⟨y, hy, rfl⟩ := hpY
      exact ⟨y, hy, h y, hpU, by simp⟩)
    (by
      rw [disjoint_left]
      rintro x ⟨w, hw, rfl⟩ hx
      refine disjoint_left.1 h2 hw ⟨h.symm w, ?_, by simp⟩
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx)
  intro x hx
  have := hsub' ⟨x, hx, rfl⟩
  exact ⟨h.symm x, this, by simp⟩

end Lemma3

end HPC.Hagopian
