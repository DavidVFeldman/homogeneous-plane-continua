import HPC.Jones.Jones75Line

/-!
# Jones 1975 I (batch 189), part 3: homeomorphisms on lines; no small reversal

Commission 189 §2.4 and §3 (skeleton `Jones75A.lean` §2–§3, split).

* arcs inside a line are parameter intervals (`JonesSetting.line_arc`, `JonesSetting.arc_unique`,
  `JonesSetting.arc_in_line`);
* a homeomorphism acts on lines by continuous monotone bijections of the parameters
  (`JonesSetting.homeo_on_line`);
* **(R0)** (`JonesSetting.no_reversal_arc`), **(R)** (`JonesSetting.exists_no_reversal`) and
  **(O)** (`JonesSetting.orientation`): the replacement for Jones's (f).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen unitInterval

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-! ## §2.4. Arcs in lines; homeomorphisms on lines -/

omit [CompactSpace Y] in
/-- **§2.4**: the arcs inside a line are its parameter intervals; here, the parameter intervals
are arcs. (Shape: the hypothesis `JonesSetting Y` of the skeleton is not used and was dropped.) -/
theorem JonesSetting.line_arc {ℓ : ℝ → Y} (hℓ : IsLine ℓ) {s t : ℝ} (hst : s < t) :
    TArc (ℓ s) (ℓ t) (ℓ '' Icc s t) := by
  set g : I → Y := fun u => ℓ (s + u * (t - s)) with hg
  have hts : 0 < t - s := sub_pos.mpr hst
  have hgc : Continuous g := hℓ.1.comp (by fun_prop)
  have hgi : Function.Injective g := by
    intro u v h
    have := hℓ.2.1 h
    apply Subtype.ext
    have h2 : (u : ℝ) * (t - s) = v * (t - s) := by linarith
    exact mul_right_cancel₀ hts.ne' h2
  have := TArc.of_inj hgc hgi
  have h0 : g 0 = ℓ s := by simp [hg]
  have h1 : g 1 = ℓ t := by simp [hg]
  rw [h0, h1] at this
  convert this using 1
  ext y
  constructor
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    refine ⟨⟨(w - s) / (t - s), div_nonneg (by linarith) hts.le,
      (div_le_one hts).mpr (by linarith)⟩, ?_⟩
    simp only [hg]
    congr 1
    field_simp
    ring
  · rintro ⟨u, rfl⟩
    refine ⟨s + u * (t - s), ⟨?_, ?_⟩, rfl⟩
    · nlinarith [u.2.1]
    · nlinarith [u.2.2]

omit [CompactSpace Y] in
theorem JonesSetting.line_arc_uIcc {ℓ : ℝ → Y} (hℓ : IsLine ℓ) {s t : ℝ} (hst : s ≠ t) :
    TArc (ℓ s) (ℓ t) (ℓ '' uIcc s t) := by
  rcases lt_or_gt_of_ne hst with h | h
  · rw [uIcc_of_le h.le]; exact JonesSetting.line_arc hℓ h
  · rw [uIcc_of_ge h.le]; exact (JonesSetting.line_arc hℓ h).symm

/-- Two arcs with the same end points are equal (Jones (c)). -/
theorem JonesSetting.arc_unique (S : JonesSetting Y) {p q : Y} {K K' : Set Y} (hK : TArc p q K)
    (hK' : TArc p q K') : K = K' := by
  obtain ⟨u, v, hW⟩ := S.union_arc hK hK' ⟨p, hK.left_mem, hK'.left_mem⟩
  obtain ⟨-, f, hf, hW, -, -⟩ := hW
  obtain ⟨s, t, hst, hKs, hKe⟩ := sub_arc_param hf hK (hW ▸ subset_union_left)
  obtain ⟨s', t', hst', hKs', hKe'⟩ := sub_arc_param hf hK' (hW ▸ subset_union_right)
  rw [hKs, hKs']
  have hi := hf.injective
  rcases hKe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hKe' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · rw [hi (h1.trans h1'.symm), hi (h2.trans h2'.symm)]
  · have e1 := hi (h1.trans h2'.symm); have e2 := hi (h2.trans h1'.symm)
    exact absurd (hst.trans (e2 ▸ e1 ▸ hst')) (lt_irrefl _)
  · have e1 := hi (h1.trans h2'.symm); have e2 := hi (h2.trans h1'.symm)
    exact absurd (hst.trans (e2 ▸ e1 ▸ hst')) (lt_irrefl _)
  · rw [hi (h1.trans h1'.symm), hi (h2.trans h2'.symm)]

/-- An arc between two points of a line is the parameter interval between them. -/
theorem JonesSetting.arc_in_line (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) {u v : ℝ}
    (huv : u ≠ v) {K : Set Y} (hK : TArc (ℓ u) (ℓ v) K) : K = ℓ '' uIcc u v :=
  S.arc_unique hK (JonesSetting.line_arc_uIcc hℓ huv)

omit [CompactSpace Y] in
theorem IsLine.range_eq {ℓ : ℝ → Y} (hℓ : IsLine ℓ) (s : ℝ) : range ℓ = arcComp (ℓ s) := by
  have h : ℓ s ∈ arcComp (ℓ 0) := hℓ.2.2 ▸ mem_range_self s
  rw [hℓ.2.2, arcComp_eq_of_mem h]

omit [CompactSpace Y] in
/-- The image of a line under a homeomorphism is a line. -/
theorem IsLine.comp_homeo {ℓ : ℝ → Y} (hℓ : IsLine ℓ) (h : Y ≃ₜ Y) : IsLine (h ∘ ℓ) :=
  ⟨h.continuous.comp hℓ.1, h.injective.comp hℓ.2.1, by
    rw [range_comp, hℓ.2.2, image_arcComp]; rfl⟩

omit [CompactSpace Y] in
/-- A shifted line is a line. -/
theorem IsLine.shift {ℓ : ℝ → Y} (hℓ : IsLine ℓ) (c : ℝ) : IsLine (fun s => ℓ (s + c)) := by
  refine ⟨hℓ.1.comp (continuous_add_right c), fun s t h => add_right_cancel (hℓ.2.1 h), ?_⟩
  have : range (fun s => ℓ (s + c)) = range ℓ :=
    (Equiv.addRight c).surjective.range_comp ℓ
  rw [this, hℓ.range_eq c]
  simp only [zero_add]

omit [CompactSpace Y] in
/-- A reversed line is a line. -/
theorem IsLine.neg {ℓ : ℝ → Y} (hℓ : IsLine ℓ) : IsLine (fun s => ℓ (-s)) := by
  refine ⟨hℓ.1.comp continuous_neg, fun s t h => neg_inj.mp (hℓ.2.1 h), ?_⟩
  have : range (fun s => ℓ (-s)) = range ℓ := (Equiv.neg ℝ).surjective.range_comp ℓ
  rw [this, hℓ.2.2]
  simp only [neg_zero]

/-- **§2.4**, general form: a homeomorphism carrying one point of `ℓ` into `ℓ'` acts by a
continuous monotone bijection of the parameters. -/
theorem JonesSetting.homeo_on_line_gen (S : JonesSetting Y) {ℓ ℓ' : ℝ → Y} (hℓ : IsLine ℓ)
    (hℓ' : IsLine ℓ') (h : Y ≃ₜ Y) {s₀ : ℝ} (h0 : h (ℓ s₀) ∈ range ℓ') :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Bijective ψ ∧ (StrictMono ψ ∨ StrictAnti ψ) ∧
      ∀ s, h (ℓ s) = ℓ' (ψ s) := by
  have hrange : h '' range ℓ = range ℓ' := by
    rw [hℓ.range_eq s₀, image_arcComp, hℓ'.2.2,
      arcComp_eq_of_mem (show h (ℓ s₀) ∈ arcComp (ℓ' 0) from hℓ'.2.2 ▸ h0)]
  have hex : ∀ s, ∃ w, ℓ' w = h (ℓ s) := fun s =>
    hrange.subset (mem_image_of_mem h (mem_range_self s))
  choose ψ hψ using hex
  have hinj : Function.Injective ψ := fun s t hst =>
    hℓ.2.1 (h.injective (by rw [← hψ, ← hψ, hst]))
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hrange.symm.subset (mem_range_self w)
    exact ⟨s, hℓ'.2.1 ((hψ s).trans hs)⟩
  -- continuity on compact intervals
  have hcon : ∀ s t, s < t → ContinuousOn ψ (Icc s t) := by
    intro s t hst
    have hne : ψ s ≠ ψ t := fun e => hst.ne (hinj e)
    have hK : h '' (ℓ '' Icc s t) = ℓ' '' uIcc (ψ s) (ψ t) := by
      apply S.arc_in_line hℓ' hne
      rw [hψ, hψ]
      exact TArc.image_homeomorph (JonesSetting.line_arc hℓ hst) h
    have hmem : ∀ r ∈ Icc s t, ψ r ∈ uIcc (ψ s) (ψ t) := by
      intro r hr
      have : ℓ' (ψ r) ∈ ℓ' '' uIcc (ψ s) (ψ t) := by
        rw [← hK, hψ]; exact mem_image_of_mem h (mem_image_of_mem ℓ hr)
      obtain ⟨w, hw, hwe⟩ := this
      rwa [← hℓ'.2.1 hwe]
    haveI : CompactSpace (uIcc (ψ s) (ψ t)) := isCompact_iff_compactSpace.mp isCompact_uIcc
    set g : uIcc (ψ s) (ψ t) → Y := fun w => ℓ' w
    have hg : IsInducing g :=
      ((hℓ'.1.comp continuous_subtype_val).isClosedEmbedding
        (fun a b hab => Subtype.ext (hℓ'.2.1 hab))).isInducing
    set F : Icc s t → uIcc (ψ s) (ψ t) := fun r => ⟨ψ r, hmem r r.2⟩
    have hF : Continuous F := by
      rw [hg.continuous_iff]
      have : g ∘ F = fun r : Icc s t => h (ℓ r) := funext fun r => hψ r
      rw [this]
      exact h.continuous.comp (hℓ.1.comp continuous_subtype_val)
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_subtype_val.comp hF
  have hc : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hcon (s - 1) (s + 1) (by linarith)).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  exact ⟨ψ, hc, ⟨hinj, hsurj⟩, hc.strictMono_of_inj hinj, fun s => (hψ s).symm⟩

/-- **§2.4**: a homeomorphism acts on lines by monotone continuous bijections of the
parameters. -/
theorem JonesSetting.homeo_on_line (S : JonesSetting Y) {ℓ ℓ' : ℝ → Y} (hℓ : IsLine ℓ)
    (hℓ' : IsLine ℓ') (h : Y ≃ₜ Y) (h0 : h (ℓ 0) ∈ range ℓ') :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Bijective ψ ∧ (StrictMono ψ ∨ StrictAnti ψ) ∧
      ∀ s, h (ℓ s) = ℓ' (ψ s) :=
  S.homeo_on_line_gen hℓ hℓ' h h0

/-! ## §3. No small reversal (replaces Jones (f)) -/

/-- **§3.1, (R0)**: a homeomorphism fixing an interior point `p` of an arc `A ∪ C` and moving no
point by `min(ρ(a, C), ρ(c, A))` or more does not fold `A` onto the side of `C`. (Shape: the
skeleton's hypothesis `A ∩ C = {p}` is not used and was dropped.) -/
theorem JonesSetting.no_reversal_arc (S : JonesSetting Y) {a p c : Y} {A C : Set Y}
    (hA : TArc a p A) (hC : TArc p c C) {h : Y ≃ₜ Y} (hp : h p = p)
    (hsmall : ∀ x, dist x (h x) < min (infDist a C) (infDist c A)) : h '' A ∩ C = {p} := by
  have hpA : p ∈ h '' A ∩ C := ⟨⟨p, hA.right_mem, hp⟩, hC.left_mem⟩
  rcases (show (h '' A ∩ C).Nonempty from ⟨p, hpA⟩).exists_eq_singleton_or_nontrivial with
    ⟨z, hz⟩ | hnt
  · rw [hz] at hpA ⊢; rw [mem_singleton_iff.mp hpA]
  exfalso
  have hhA : TArc p (h a) (h '' A) := hp ▸ (TArc.image_homeomorph hA h).symm
  rcases S.nested hhA hC hnt with hsub | hsub
  · have : h a ∈ C := hsub (mem_image_of_mem h hA.left_mem)
    have h1 := hsmall a
    have h2 := infDist_le_dist_of_mem (x := a) this
    linarith [min_le_left (infDist a C) (infDist c A)]
  · obtain ⟨y, hy, hyc⟩ := hsub hC.right_mem
    have h1 := hsmall y
    have h2 := infDist_le_dist_of_mem (x := c) hy
    have h3 : dist c y = dist y (h y) := by rw [← hyc, dist_comm]
    linarith [min_le_right (infDist a C) (infDist c A)]

/-- **§3.2, (R), local form**: near each point `q`, one `ε` for all fixed points and lines. -/
theorem JonesSetting.local_no_reversal (S : JonesSetting Y) (q : Y) :
    ∃ δ > 0, ∃ ε > 0, ∀ b, dist b q < δ → ∀ h : Y ≃ₜ Y, (∀ x, dist x (h x) < ε) →
      ∀ ℓ : ℝ → Y, IsLine ℓ → ∀ s, ℓ s = b → h b = b →
        ∀ t, s < t → ∃ t', s < t' ∧ h (ℓ t) = ℓ t' := by
  obtain ⟨a', c', A₀, hA₀, hqA, hqa, hqc⟩ := S.exists_arc_through q
  obtain ⟨Γ₁, Γ₂, h₁, h₂, -, hint⟩ := hA₀.split hqA hqa hqc
  have ha2 : a' ∉ Γ₂ := fun h => hqa ((hint.subset ⟨h₁.left_mem, h⟩ : a' ∈ ({q} : Set Y))).symm
  have hc1 : c' ∉ Γ₁ := fun h => hqc ((hint.subset ⟨h, h₂.right_mem⟩ : c' ∈ ({q} : Set Y))).symm
  set ρ := min (infDist a' Γ₂) (infDist c' Γ₁) with hρ
  have hρ0 : 0 < ρ := lt_min
    ((infDist_pos_iff_notMem_closure ⟨q, h₂.left_mem⟩).1 (h₂.isClosed.closure_eq.symm ▸ ha2))
    ((infDist_pos_iff_notMem_closure ⟨q, h₁.right_mem⟩).1 (h₁.isClosed.closure_eq.symm ▸ hc1))
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous S.hom (by linarith : 0 < ρ / 3)
  refine ⟨δ, hδ, ρ / 3, by linarith, ?_⟩
  intro b hb h hsmall ℓ hℓ s hsb hhb
  by_contra hrev
  push_neg at hrev
  obtain ⟨t, hst, hrev⟩ := hrev
  obtain ⟨g, hgb, hgsmall⟩ := hEff b q hb
  obtain ⟨ψ, hψc, hψb, hψm, hψ⟩ := S.homeo_on_line_gen hℓ hℓ h (s₀ := s)
    (by rw [hsb, hhb, ← hsb]; exact mem_range_self s)
  have hψs : ψ s = s := hℓ.2.1 (by rw [← hψ, hsb, hhb])
  have hψt : ψ t < s := by
    refine lt_of_le_of_ne (not_lt.mp fun h' => hrev (ψ t) h' (hψ t)) fun e => hst.ne' ?_
    exact hψb.1 (e.trans hψs.symm)
  have hanti : StrictAnti ψ := hψm.resolve_left fun hm => by
    have := hm hst; rw [hψs] at this; linarith
  -- the line through `q`
  set lam : ℝ → Y := g ∘ ℓ with hlam
  have hlaml : IsLine lam := hℓ.comp_homeo g
  have hlams : lam s = q := by simp [hlam, hsb, hgb]
  have hmemlam : ∀ {y : Y} {e : Y} {Γ : Set Y}, (TArc y q Γ ∨ TArc q y Γ) → y ∈ range lam := by
    intro y e Γ hΓ
    rw [hlaml.range_eq s, hlams]
    rcases hΓ with hΓ | hΓ
    · exact subset_arcComp hΓ hΓ.right_mem hΓ.left_mem
    · exact subset_arcComp hΓ hΓ.left_mem hΓ.right_mem
  obtain ⟨α, hα⟩ := hmemlam (e := q) (Or.inl h₁)
  obtain ⟨γ, hγ⟩ := hmemlam (e := q) (Or.inr h₂)
  have hαs : α ≠ s := fun e => hqa (by rw [← hlams, ← e, hα])
  have hγs : γ ≠ s := fun e => hqc (by rw [← hlams, ← e, hγ])
  have hΓ₁ : Γ₁ = lam '' uIcc α s := S.arc_in_line hlaml hαs (by rw [hα, hlams]; exact h₁)
  have hΓ₂ : Γ₂ = lam '' uIcc s γ := S.arc_in_line hlaml hγs.symm (by rw [hγ, hlams]; exact h₂)
  -- the conjugate
  set k : Y ≃ₜ Y := (g.symm.trans h).trans g with hk
  have hkapp : ∀ y, k y = g (h (g.symm y)) := fun y => rfl
  have hgsb : g.symm q = b := by rw [← hgb, Homeomorph.symm_apply_apply]
  have hkq : k q = q := by rw [hkapp, hgsb, hhb, hgb]
  have hklam : ∀ r, k (lam r) = lam (ψ r) := fun r => by
    simp only [hkapp, hlam, Function.comp, Homeomorph.symm_apply_apply, hψ]
  have hksmall : ∀ x, dist x (k x) < min (infDist a' Γ₂) (infDist c' Γ₁) := by
    intro x
    rw [hkapp, ← hρ]
    set y := g.symm x
    have hx : x = g y := (Homeomorph.apply_symm_apply g x).symm
    rw [hx]
    have e1 := hgsmall y
    have e2 := hsmall y
    have e3 := hgsmall (h y)
    calc dist (g y) (g (h y)) ≤ dist (g y) y + dist y (h y) + dist (h y) (g (h y)) :=
          dist_triangle4 _ _ _ _
      _ < ρ / 3 + ρ / 3 + ρ / 3 := by
          rw [dist_comm] at e3
          linarith
      _ = ρ := by ring
  have hkey := S.no_reversal_arc h₁ h₂ hkq hksmall
  -- a point of `k Γ₁ ∩ Γ₂` other than `q`
  have hcont : ContinuousOn ψ (uIcc α s) := hψc.continuousOn
  have hside : (α < s ∧ s < γ) ∨ (γ < s ∧ s < α) := by
    rcases lt_or_gt_of_ne hαs with h1 | h1 <;> rcases lt_or_gt_of_ne hγs with h2 | h2
    · exfalso
      have hm : lam (max α γ) ∈ Γ₁ ∩ Γ₂ := by
        rw [hΓ₁, hΓ₂]
        refine ⟨mem_image_of_mem _ ?_, mem_image_of_mem _ ?_⟩
        · rw [uIcc_of_le h1.le]; exact ⟨le_max_left _ _, max_le h1.le h2.le⟩
        · rw [uIcc_of_ge h2.le]; exact ⟨le_max_right _ _, max_le h1.le h2.le⟩
      rw [hint, mem_singleton_iff, ← hlams] at hm
      have := hlaml.2.1 hm
      exact absurd this (ne_of_lt (max_lt h1 h2))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exfalso
      have hm : lam (min α γ) ∈ Γ₁ ∩ Γ₂ := by
        rw [hΓ₁, hΓ₂]
        refine ⟨mem_image_of_mem _ ?_, mem_image_of_mem _ ?_⟩
        · rw [uIcc_of_ge h1.le]; exact ⟨le_min h1.le h2.le, min_le_left _ _⟩
        · rw [uIcc_of_le h2.le]; exact ⟨le_min h1.le h2.le, min_le_right _ _⟩
      rw [hint, mem_singleton_iff, ← hlams] at hm
      have := hlaml.2.1 hm
      exact absurd this (ne_of_gt (lt_min h1 h2))
  have hfind : ∃ w, w ≠ s ∧ w ∈ uIcc s γ ∧ w ∈ uIcc (ψ α) (ψ s) := by
    rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hψα : s < ψ α := hψs ▸ hanti h1
      refine ⟨min (ψ α) γ, (ne_of_gt (lt_min hψα h2)), ?_, ?_⟩
      · rw [uIcc_of_le h2.le]; exact ⟨(lt_min hψα h2).le, min_le_right _ _⟩
      · rw [hψs, uIcc_of_ge hψα.le]; exact ⟨(lt_min hψα h2).le, min_le_left _ _⟩
    · have hψα : ψ α < s := hψs ▸ hanti h2
      refine ⟨max (ψ α) γ, (ne_of_lt (max_lt hψα h1)), ?_, ?_⟩
      · rw [uIcc_of_ge h1.le]; exact ⟨le_max_right _ _, (max_lt hψα h1).le⟩
      · rw [hψs, uIcc_of_le hψα.le]; exact ⟨le_max_left _ _, (max_lt hψα h1).le⟩
  obtain ⟨w, hws, hwγ, hwψ⟩ := hfind
  obtain ⟨r, hr, hrw⟩ := intermediate_value_uIcc hcont hwψ
  have hmem : lam w ∈ k '' Γ₁ ∩ Γ₂ := by
    refine ⟨⟨lam r, hΓ₁ ▸ mem_image_of_mem _ hr, by rw [hklam, hrw]⟩, hΓ₂ ▸ mem_image_of_mem _ hwγ⟩
  rw [hkey, mem_singleton_iff, ← hlams] at hmem
  exact hws (hlaml.2.1 hmem)

/-- **§3.2, (R), uniform**: one `ε` for all fixed points and all lines. -/
theorem JonesSetting.exists_no_reversal (S : JonesSetting Y) :
    ∃ ε > 0, ∀ h : Y ≃ₜ Y, (∀ x, dist x (h x) < ε) → ∀ ℓ : ℝ → Y, IsLine ℓ → ∀ s, h (ℓ s) = ℓ s →
      ∀ t, s < t → ∃ t', s < t' ∧ h (ℓ t) = ℓ t' := by
  choose! δ hδ ε hε hloc using S.local_no_reversal
  obtain ⟨a, -, -, -⟩ := S.arc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun q : Y => ball q (δ q))
    (fun _ => isOpen_ball) (fun q _ => mem_iUnion.2 ⟨q, mem_ball_self (hδ q)⟩)
  have hTne : T.Nonempty := by
    obtain ⟨q, hq, -⟩ := mem_iUnion₂.1 (hT (mem_univ a)); exact ⟨q, hq⟩
  refine ⟨T.inf' hTne ε, (Finset.lt_inf'_iff hTne).2 fun q _ => hε q, ?_⟩
  intro h hsmall ℓ hℓ s hfix t hst
  obtain ⟨q, hq, hbq⟩ := mem_iUnion₂.1 (hT (mem_univ (ℓ s)))
  exact hloc q (ℓ s) hbq h (fun x => (hsmall x).trans_le (Finset.inf'_le ε hq)) ℓ hℓ s rfl hfix
    t hst

/-- **§3.3, (O), orientation**: a small homeomorphism that carries a point of a line into the same
line preserves the line's orientation (`ψ` continuous and onto as well, for §5). -/
theorem JonesSetting.orientation (S : JonesSetting Y) :
    ∃ ε > 0, ∀ h : Y ≃ₜ Y, (∀ x, dist x (h x) < ε) → ∀ ℓ : ℝ → Y, IsLine ℓ →
      h (ℓ 0) ∈ range ℓ → ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ Continuous ψ ∧ Function.Surjective ψ ∧
        ∀ s, h (ℓ s) = ℓ (ψ s) := by
  obtain ⟨ε, hε, hR⟩ := S.exists_no_reversal
  refine ⟨ε, hε, fun h hsmall ℓ hℓ h0 => ?_⟩
  obtain ⟨ψ, hψc, hψb, hψm, hψ⟩ := S.homeo_on_line hℓ hℓ h h0
  refine ⟨ψ, hψm.resolve_right fun hanti => ?_, hψc, hψb.2, hψ⟩
  -- a decreasing `ψ` has a fixed point
  have hfix : ∃ s, ψ s = s := by
    have hgc : ContinuousOn (fun s => ψ s - s) (uIcc 0 (ψ 0)) :=
      (hψc.sub continuous_id).continuousOn
    have h0mem : (0 : ℝ) ∈ uIcc (ψ 0 - 0) (ψ (ψ 0) - ψ 0) := by
      rw [mem_uIcc]
      rcases le_or_gt 0 (ψ 0) with hp | hp
      · right
        have : ψ (ψ 0) ≤ ψ 0 := hanti.antitone hp
        constructor <;> linarith
      · left
        have : ψ 0 < ψ (ψ 0) := hanti hp
        constructor <;> linarith
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hgc h0mem
    exact ⟨s, by simp only at hs; linarith⟩
  obtain ⟨s, hs⟩ := hfix
  obtain ⟨t', ht', ht'e⟩ := hR h hsmall ℓ hℓ s (by rw [hψ, hs]) (s + 1) (by linarith)
  have : ψ (s + 1) = t' := hℓ.2.1 ((hψ _).symm.trans ht'e)
  have := hanti (show s < s + 1 by linarith)
  linarith

end General

end HPC.Hagopian
