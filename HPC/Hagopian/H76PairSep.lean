import HPC.Hagopian.H76Crosscut

/-!
# Batch 168, item B: a crossing continuum separates `D′` along the vertical

In the domain `D′` of `rect_domain_aux` (under the arc `I` from `r = (a, r₂)` to `s = (b, s₂)`):
* `rect_domain_crosscut_arc`: `rect_domain_crosscut` with the low vertical segment replaced by any
  arc `T` from a bottom point `(x₀, 0)` to a point `w` of `I`, with `T − {(x₀, 0), w} ⊆ D′`. Same
  proof: one Jordan curve `J = I_L ∪ {a} × [0, r₂] ∪ [a, x₀] × {0} ∪ T`.
* `seg_subset_rect_domain`: the vertical segment from the bottom up to the lowest point of `I` over
  `x₀` lies in `D′`.
* `rect_domain_crossing_separates`: a connected `B ⊆ D′` whose closure misses `I` and the bottom
  and meets both open side edges separates, in `D′`, a point `(x₀, u₁)` of the vertical below
  `Cl B` from a point `(x₀, u₂)` above it. Proof: a connected `S ⊆ D′ − Cl B` through both points
  gives a polygonal arc from `(x₀, u₁)` to `(x₀, u₂)` in the component of `D′ − Cl B`; with the two
  vertical segments it gives (by loop erasure) an arc `T` from `(x₀, 0)` to `(x₀, w₂)` missing
  `Cl B`, and `rect_domain_crosscut_arc` applies to `B`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **An arc from the bottom to `I` through `D′` is a cross-cut of `D′`.** -/
theorem rect_domain_crosscut_arc {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) {w : ℝ × ℝ}
    (hwI : w ∈ I) (hw1 : w.1 ∈ Ioo a b) {T : Set (ℝ × ℝ)} (hT : TArc ((x₀, 0) : ℝ × ℝ) w T)
    (hTD : T \ {((x₀, 0) : ℝ × ℝ), w} ⊆ D)
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSD : S ⊆ D \ T)
    {p q : ℝ × ℝ} (hp : p ∈ ({a} : Set ℝ) ×ˢ Ioo 0 r.2) (hq : q ∈ ({b} : Set ℝ) ×ˢ Ioo 0 s.2)
    (hpS : p ∈ closure S) (hqS : q ∈ closure S) : False := by
  have hrI := hI.left_mem
  have hrR := hIR hrI
  have hr2 : 0 < r.2 := hrR.2.1
  have hwR := hIR hwI
  have hc0 : 0 ≤ c := hr2.le.trans hrR.2.2
  have hDI : ∀ z ∈ D, z ∉ I := by
    intro z hzD hzI
    have : z ∈ frontier D := by rw [hDf]; exact Or.inl (Or.inl (Or.inl hzI))
    exact (hDo.frontier_eq ▸ this).2 hzD
  have hTcase : ∀ z ∈ T, z = ((x₀, 0) : ℝ × ℝ) ∨ z = w ∨ z ∈ D := by
    intro z hz
    by_cases h1 : z = ((x₀, 0) : ℝ × ℝ)
    · exact Or.inl h1
    by_cases h2 : z = w
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hTD ⟨hz, by rintro (h | h) <;> contradiction⟩))
  have hrw : r ≠ w := by
    intro h
    have := hw1.1
    rw [← h, hr] at this
    exact lt_irrefl _ this
  obtain ⟨IL, hILI, hIL⟩ := hI.exists_sub hrI hwI hrw
  set PL0 : Set (ℝ × ℝ) := ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪ Icc a x₀ ×ˢ {0} with hPL0def
  have hPL0 : TArc r ((x₀, 0) : ℝ × ℝ) PL0 := by
    have h1 := tarc_vseg a hr2.ne'
    have h2 := tarc_hseg 0 hx₀.1.ne
    rw [uIcc_of_ge hr2.le] at h1
    rw [uIcc_of_le hx₀.1.le] at h2
    have h12 : ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∩ Icc a x₀ ×ˢ {0} = {((a, 0) : Pt)} := by
      ext ⟨x, y⟩
      simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Icc, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl, -⟩, -, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, le_rfl, hr2.le⟩, ⟨le_rfl, hx₀.1.le⟩, rfl⟩
    have h := h1.union h2 h12
    rwa [show ((a, r.2) : Pt) = r from Prod.ext hr.symm rfl] at h
  have hPLT : PL0 ∩ T = {((x₀, 0) : ℝ × ℝ)} := by
    apply subset_antisymm
    · rintro z ⟨hz0, hzT⟩
      rcases hTcase z hzT with h | h | h
      · exact h
      · exfalso
        subst h
        rcases hz0 with ⟨hx, -⟩ | ⟨-, hy⟩
        · have hx' : z.1 = a := hx
          linarith [hw1.1]
        · have hy' : z.2 = 0 := hy
          linarith [hwR.2.1]
      · exfalso
        have hzR := hDR h
        rcases hz0 with ⟨hx, -⟩ | ⟨-, hy⟩
        · have hx' : z.1 = a := hx
          linarith [hzR.1.1]
        · have hy' : z.2 = 0 := hy
          linarith [hzR.2.1]
    · rintro z (rfl : z = _)
      exact ⟨Or.inr ⟨⟨hx₀.1.le, le_rfl⟩, rfl⟩, hT.left_mem⟩
  have hPL : TArc r w (PL0 ∪ T) := hPL0.union hT hPLT
  have hIPL : IL ∩ (PL0 ∪ T) = {r, w} := by
    apply subset_antisymm
    · rintro z ⟨hzIL, hzP⟩
      have hzI := hILI hzIL
      have hzR := hIR hzI
      rcases hzP with ((⟨hx, hy⟩ | ⟨hx, hy⟩) | hzT)
      · have hx' : z.1 = a := hx
        have : z ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) := ⟨hzI, Or.inl hx', hy.1, hzR.2.2⟩
        rw [hIs] at this
        rcases this with h | h
        · exact Or.inl h
        · exfalso
          have h1 := congrArg Prod.fst h
          rw [hs] at h1
          linarith
      · have hy' : z.2 = 0 := hy
        linarith [hzR.2.1]
      · rcases hTcase z hzT with h | h | h
        · exfalso
          have h2 := congrArg Prod.snd h
          simp only at h2
          linarith [hzR.2.1]
        · exact Or.inr h
        · exact absurd hzI (hDI z h)
    · rintro z (rfl | rfl)
      · exact ⟨hIL.left_mem, hPL.left_mem⟩
      · exact ⟨hIL.right_mem, hPL.right_mem⟩
  have hJ : TSCC (IL ∪ (PL0 ∪ T)) := ⟨r, _, IL, PL0 ∪ T, hIL, hPL, hIPL, rfl⟩
  obtain ⟨U, O, hUo, -, hOo, -, hUO, hUOu, hUb, -, hUf, -⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hJR : IL ∪ (PL0 ∪ T) ⊆ Icc a b ×ˢ Icc 0 c := by
    rintro z (hz | ((⟨hx, hy⟩ | ⟨hx, hy⟩) | hzT))
    · have := hIR (hILI hz)
      exact ⟨this.1, this.2.1.le, this.2.2⟩
    · have hx' : z.1 = a := hx
      exact ⟨⟨hx'.ge, by rw [hx']; exact hab.le⟩, hy.1, hy.2.trans hrR.2.2⟩
    · have hy' : z.2 = 0 := hy
      exact ⟨⟨hx.1, hx.2.trans hx₀.2.le⟩, by rw [hy'], by rw [hy']; exact hc0⟩
    · rcases hTcase z hzT with rfl | rfl | h
      · exact ⟨⟨hx₀.1.le, hx₀.2.le⟩, le_rfl, hc0⟩
      · exact ⟨hwR.1, hwR.2.1.le, hwR.2.2⟩
      · have := hDR h
        exact ⟨⟨this.1.1.le, this.1.2.le⟩, this.2.1.le, this.2.2.le⟩
  have hCO : (Icc a b ×ˢ Icc 0 c : Set (ℝ × ℝ))ᶜ ⊆ O := by
    obtain ⟨hCc, hCb⟩ := isConnected_compl_rect a b 0 c
    have hsub : (Icc a b ×ˢ Icc 0 c : Set (ℝ × ℝ))ᶜ ⊆ U ∪ O := by
      rw [hUOu]; exact compl_subset_compl.2 hJR
    rcases hCc.isPreconnected.subset_or_subset hUo hOo hUO hsub with h | h
    · exact absurd (hUb.subset h) hCb
    · exact h
  -- `S` misses the curve
  have hSJ : S ⊆ U ∪ O := by
    rw [hUOu]
    intro z hzS hzJ
    obtain ⟨hzD, hzT⟩ := hSD hzS
    have hzF : z ∉ frontier D := fun h => (hDo.frontier_eq ▸ h).2 hzD
    rcases hzJ with hzIL | ((hz1 | hz2) | hz3)
    · exact hzF (by rw [hDf]; exact Or.inl (Or.inl (Or.inl (hILI hzIL))))
    · exact hzF (by rw [hDf]; exact Or.inl (Or.inr hz1))
    · exact hzF (by
        rw [hDf]; exact Or.inl (Or.inl (Or.inr ⟨⟨hz2.1.1, hz2.1.2.trans hx₀.2.le⟩, hz2.2⟩)))
    · exact hzT hz3
  -- the right-edge point is in the unbounded domain
  obtain ⟨hq1, hq2⟩ := hq
  have hq1' : q.1 = b := hq1
  have hqO : q ∈ O := by
    set Ray : Set (ℝ × ℝ) := Ici b ×ˢ {q.2} with hRay
    have hRayc : IsPreconnected Ray :=
      ((convex_Ici b).prod (convex_singleton q.2)).isPreconnected
    have hRayJ : Ray ⊆ U ∪ O := by
      rw [hUOu]
      rintro z ⟨hz1, hz2⟩ hzJ
      have hz1' : b ≤ z.1 := hz1
      have hz2' : z.2 = q.2 := hz2
      rcases hzJ with hzIL | ((hz' | hz') | hz')
      · have hzI := hILI hzIL
        have hzR := hIR hzI
        have hzb : z.1 = b := le_antisymm hzR.1.2 hz1'
        have : z ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) := ⟨hzI, Or.inr hzb, hzR.2.1.le, hzR.2.2⟩
        rw [hIs] at this
        rcases this with h | h
        · have h1 := congrArg Prod.fst h
          rw [hzb, hr] at h1
          linarith
        · have h2 := congrArg Prod.snd h
          rw [hz2'] at h2
          linarith [hq2.2]
      · have : z.1 = a := hz'.1
        linarith
      · linarith [hz'.1.2, hx₀.2]
      · rcases hTcase z hz' with rfl | rfl | h
        · simp only at hz1'; linarith [hx₀.2]
        · linarith [hw1.2]
        · linarith [(hDR h).1.2]
    rcases hRayc.subset_or_subset hUo hOo hUO hRayJ with h | h
    · exfalso
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall q).1 (hUb.subset h)
      have hmem : ((b + |R| + 1, q.2) : ℝ × ℝ) ∈ Ray :=
        ⟨show b ≤ b + |R| + 1 by linarith [abs_nonneg R], rfl⟩
      have h1 := hR hmem
      rw [Metric.mem_closedBall, Prod.dist_eq] at h1
      have h2 := (le_max_left _ _).trans h1
      rw [Real.dist_eq, hq1', show b + |R| + 1 - b = |R| + 1 by ring,
        abs_of_pos (by positivity)] at h2
      linarith [le_abs_self R]
    · exact h ⟨show b ≤ q.1 from hq1'.ge, rfl⟩
  -- the points of `D` near the left-edge point are in the bounded domain
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : p.1 = a := hp1
  set K : Set (ℝ × ℝ) := IL ∪ Icc a x₀ ×ˢ {0} ∪ T with hKdef
  have hKc : IsCompact K :=
    (hIL.isCompact.union (isCompact_Icc.prod isCompact_singleton)).union hT.isCompact
  have hpK : p ∉ K := by
    rintro ((hpIL | ⟨-, hy⟩) | hpT)
    · have hpI := hILI hpIL
      have : p ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) :=
        ⟨hpI, Or.inl hp1', hp2.1.le, (hIR hpI).2.2⟩
      rw [hIs] at this
      rcases this with h | h
      · have h2 := congrArg Prod.snd h
        linarith [hp2.2]
      · have h1 := congrArg Prod.fst h
        rw [hs] at h1
        linarith
    · have hy' : p.2 = 0 := hy
      linarith [hp2.1]
    · rcases hTcase p hpT with h | h | h
      · have h2 := congrArg Prod.snd h
        simp only at h2
        linarith [hp2.1]
      · rw [h] at hp1'
        linarith [hw1.1]
      · linarith [(hDR h).1.1]
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl p hpK
  set δ := min δ₀ (min p.2 (r.2 - p.2)) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min hp2.1 (by linarith [hp2.2]))
  have hball2 : ∀ z, dist z p < δ → |z.2 - p.2| < δ := fun z hz =>
    lt_of_le_of_lt (by rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _) hz
  have hJa : ∀ z, dist z p < δ → z ∈ IL ∪ (PL0 ∪ T) → z.1 = a := by
    intro z hz hzJ
    have hzK : z ∉ K := hball (mem_ball.2 (lt_of_lt_of_le hz (min_le_left _ _)))
    rcases hzJ with hzIL | ((hz1 | hz2) | hz3)
    · exact absurd (Or.inl (Or.inl hzIL)) hzK
    · exact hz1.1
    · exact absurd (Or.inl (Or.inr hz2)) hzK
    · exact absurd (Or.inr hz3) hzK
  -- the left half-disc lies in `O`
  have hLH : ∀ z, dist z p < δ → z.1 < a → z ∈ O := fun z _ hz =>
    hCO fun h => by linarith [h.1.1]
  -- the right half-disc lies in `U`
  set RH : Set (ℝ × ℝ) := ball p δ ∩ {z | a < z.1} with hRH
  have hRHc : IsPreconnected RH :=
    ((convex_ball p δ).inter (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear a)).isPreconnected
  have hRHJ : RH ⊆ U ∪ O := by
    rw [hUOu]
    rintro z ⟨hzb, hza⟩ hzJ
    have := hJa z (mem_ball.1 hzb) hzJ
    have hza' : a < z.1 := hza
    linarith
  have hpU : p ∈ closure U := by
    apply frontier_subset_closure
    rw [hUf]
    exact Or.inr (Or.inl (Or.inl ⟨hp1, hp2.1.le, hp2.2.le⟩))
  obtain ⟨z, hzU, hzp⟩ := Metric.mem_closure_iff.1 hpU δ hδpos
  rw [dist_comm] at hzp
  have hzRH : z ∈ RH := by
    refine ⟨mem_ball.2 hzp, ?_⟩
    rcases lt_trichotomy z.1 a with h | h | h
    · exact absurd (hLH z hzp h) (disjoint_left.1 hUO hzU)
    · exfalso
      have hzJ : z ∈ IL ∪ (PL0 ∪ T) := by
        refine Or.inr (Or.inl (Or.inl ⟨h, ?_, ?_⟩))
        · have := abs_lt.1 (hball2 z hzp)
          have := min_le_right δ₀ (min p.2 (r.2 - p.2))
          have := min_le_left p.2 (r.2 - p.2)
          linarith
        · have := abs_lt.1 (hball2 z hzp)
          have := min_le_right δ₀ (min p.2 (r.2 - p.2))
          have := min_le_right p.2 (r.2 - p.2)
          linarith
      have : z ∈ U ∪ O := Or.inl hzU
      rw [hUOu] at this
      exact this hzJ
    · exact h
  have hRHU : RH ⊆ U := by
    rcases hRHc.subset_or_subset hUo hOo hUO hRHJ with h | h
    · exact h
    · exact absurd (h hzRH) (disjoint_left.1 hUO hzU)
  obtain ⟨u, huS, hup⟩ := Metric.mem_closure_iff.1 hpS δ hδpos
  rw [dist_comm] at hup
  have huU : u ∈ U := hRHU ⟨mem_ball.2 hup, (hDR (hSD huS).1).1.1⟩
  obtain ⟨v, hvO, hvS⟩ := mem_closure_iff.1 hqS O hOo hqO
  rcases hS.subset_or_subset hUo hOo hUO hSJ with h | h
  · exact disjoint_left.1 hUO (h hvS) hvO
  · exact disjoint_left.1 hUO huU (h huS)

/-- **The low vertical segment lies in `D′`.** -/
theorem seg_subset_rect_domain {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : 0 < w₂)
    (hsegI : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) I) :
    ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D := by
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hI.isCompact fun z hz => (hIR hz).2.1
  have hlow := rect_domain_low (r := r) (s := s) hab hDR hDf hc₀ fun z hz => (hc₀I z hz).le
  set seg := ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂
  have hsegc : IsPreconnected seg :=
    ((convex_singleton x₀).prod (convex_Ioo 0 w₂)).isPreconnected
  have hsub : seg ⊆ D ∪ (closure D)ᶜ := by
    rintro z ⟨hx, hy⟩
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · right
      intro hzcl
      have hzf : z ∈ frontier D := ⟨hzcl, by rwa [hDo.interior_eq]⟩
      rw [hDf] at hzf
      have hx' : z.1 = x₀ := hx
      rcases hzf with ((hzI | ⟨-, hy0⟩) | ⟨hxa, -⟩) | ⟨hxb, -⟩
      · exact disjoint_left.1 hsegI ⟨hx, hy⟩ hzI
      · have : z.2 = 0 := hy0
        linarith [hy.1]
      · have : z.1 = a := hxa
        linarith [hx₀.1]
      · have : z.1 = b := hxb
        linarith [hx₀.2]
  have hDcl : Disjoint D (closure D)ᶜ := disjoint_compl_right.mono_left subset_closure
  rcases hsegc.subset_or_subset hDo isClosed_closure.isOpen_compl hDcl hsub with h | h
  · exact h
  · exfalso
    have hm0 : 0 < min c₀ w₂ := lt_min hc₀ hw₂
    have hm1 := min_le_left c₀ w₂
    have hm2 := min_le_right c₀ w₂
    have hu0 : 0 < min c₀ w₂ / 2 := by linarith
    have hu1 : min c₀ w₂ / 2 < c₀ := by linarith
    have hu2 : min c₀ w₂ / 2 < w₂ := by linarith
    have hm : ((x₀, min c₀ w₂ / 2) : ℝ × ℝ) ∈ D := hlow ⟨hx₀, hu0, hu1⟩
    exact h ⟨mem_singleton x₀, hu0, hu2⟩ (subset_closure hm)

/-- A point of the segment between two points of the vertical over `x₀`. -/
theorem mem_vsegment {x₀ y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ ((x₀, y₁) : ℝ × ℝ) (x₀, y₂)) : z.1 = x₀ ∧ z.2 ∈ Icc y₁ y₂ := by
  have h := Prod.segment_subset ((x₀, y₁) : ℝ × ℝ) (x₀, y₂) hz
  simp only [segment_same, segment_eq_Icc hy] at h
  exact ⟨h.1, h.2⟩

/-- **A crossing connected set separates the vertical in `D′`.** -/
theorem rect_domain_crossing_separates {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ}
    {I D : Set (ℝ × ℝ)} (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a)
    (hs : s.1 = b) (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : 0 < w₂)
    (hwI : ((x₀, w₂) : ℝ × ℝ) ∈ I) (hsegI : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) I)
    {B : Set (ℝ × ℝ)} (hB : IsPreconnected B) (hBD : B ⊆ D)
    (hBe : Disjoint (closure B) (I ∪ Icc a b ×ˢ {0}))
    (hBl : (closure B ∩ ({a} : Set ℝ) ×ˢ Ioo 0 r.2).Nonempty)
    (hBr : (closure B ∩ ({b} : Set ℝ) ×ˢ Ioo 0 s.2).Nonempty)
    {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu₁₂ : u₁ < u₂) (hu₂ : u₂ < w₂)
    (hlo : Disjoint (closure B) (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))
    (hhi : Disjoint (closure B) (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂))
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSB : S ⊆ D \ closure B)
    (h1 : ((x₀, u₁) : ℝ × ℝ) ∈ S) (h2 : ((x₀, u₂) : ℝ × ℝ) ∈ S) : False := by
  have hsegD := seg_subset_rect_domain hab hI hIR hDo hDR hDf hx₀ hw₂ hsegI
  set P : ℝ × ℝ := (x₀, u₁)
  set Q : ℝ × ℝ := (x₀, u₂)
  set G := connectedComponentIn (D \ closure B) P with hGdef
  have hGo : IsOpen G := (hDo.sdiff isClosed_closure).connectedComponentIn
  have hPG : P ∈ G := mem_connectedComponentIn (hSB h1)
  have hGc : IsConnected G := isConnected_connectedComponentIn_iff.2 (hSB h1)
  have hQG : Q ∈ G := hS.subset_connectedComponentIn h1 hSB h2
  have hGsub : G ⊆ D \ closure B := connectedComponentIn_subset _ _
  obtain ⟨v, n, hn, hv0, hv1, hvG⟩ := exists_vpath_of_isConnected hGo hGc hPG hQG
  have hPQ : P ≠ Q := fun h => by
    have := congrArg Prod.snd h
    simp only [P, Q] at this
    linarith
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    subst this
    exact hPQ (hv0.symm.trans hv1)
  set v₁ : ℕ → ℝ × ℝ := fun i => if i = 0 then ((x₀, 0) : ℝ × ℝ) else P with hv₁
  set v₃ : ℕ → ℝ × ℝ := fun i => if i = 0 then Q else ((x₀, w₂) : ℝ × ℝ) with hv₃
  have hpath1 : vpath (vcat v₁ 2 v) (2 + n - 1) = vpath v₁ 2 ∪ vpath v n :=
    vpath_vcat (by norm_num) hn (by simp [v₁, hv0])
  have hlast : vcat v₁ 2 v (2 + n - 1 - 1) = v₃ 0 := by
    simp only [vcat, v₃, if_true]
    rw [if_neg (by omega), show 2 + n - 1 - 1 - (2 - 1) = n - 1 by omega, hv1]
  have hpath : vpath (vcat (vcat v₁ 2 v) (2 + n - 1) v₃) (2 + n - 1 + 2 - 1) =
      vpath v₁ 2 ∪ vpath v n ∪ vpath v₃ 2 := by
    rw [vpath_vcat (by omega) (by norm_num) hlast, hpath1]
  have hseg2 : ∀ u : ℕ → ℝ × ℝ, vpath u 2 = segment ℝ (u 0) (u 1) := by
    intro u
    simp [vpath]
  have hV0 : vcat (vcat v₁ 2 v) (2 + n - 1) v₃ 0 = ((x₀, 0) : ℝ × ℝ) := by
    simp [vcat, v₁]
  have hV1 : vcat (vcat v₁ 2 v) (2 + n - 1) v₃ (2 + n - 1 + 2 - 1 - 1) =
      ((x₀, w₂) : ℝ × ℝ) := by
    simp only [vcat]
    rw [if_neg (by omega), show 2 + n - 1 + 2 - 1 - 1 - (2 + n - 1 - 1) = 1 by omega]
    simp [v₃]
  have hne : ((x₀, 0) : ℝ × ℝ) ≠ (x₀, w₂) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    linarith
  obtain ⟨u, k, hu, hu0, hu1, husub⟩ := exists_sarc_of_vpath (by omega) hV0 hV1 hne
  rw [hpath, hseg2, hseg2] at husub
  set T := vpath u k with hTdef
  have hT : TArc ((x₀, 0) : ℝ × ℝ) (x₀, w₂) T := by
    have := tarc_vpath hu k hu.1 le_rfl
    rwa [hu0, hu1] at this
  have hs1 : ∀ z ∈ segment ℝ (v₁ 0) (v₁ 1), z.1 = x₀ ∧ z.2 ∈ Icc 0 u₁ := fun z hz =>
    mem_vsegment hu₁.le (by simpa [v₁, P] using hz)
  have hs3 : ∀ z ∈ segment ℝ (v₃ 0) (v₃ 1), z.1 = x₀ ∧ z.2 ∈ Icc u₂ w₂ := fun z hz =>
    mem_vsegment (hu₂.le) (by simpa [v₃, Q] using hz)
  have hTD : T \ {((x₀, 0) : ℝ × ℝ), (x₀, w₂)} ⊆ D := by
    rintro z ⟨hzT, hzne⟩
    have hz0 : z ≠ ((x₀, 0) : ℝ × ℝ) := fun h => hzne (Or.inl h)
    have hzw : z ≠ ((x₀, w₂) : ℝ × ℝ) := fun h => hzne (Or.inr h)
    rcases husub hzT with (hz | hz) | hz
    · obtain ⟨hx, hy⟩ := hs1 z hz
      have hy0 : z.2 ≠ 0 := fun h => hz0 (Prod.ext hx h)
      exact hsegD ⟨hx, lt_of_le_of_ne hy.1 (Ne.symm hy0), by linarith [hy.2]⟩
    · exact (hGsub (hvG hz)).1
    · obtain ⟨hx, hy⟩ := hs3 z hz
      have hyw : z.2 ≠ w₂ := fun h => hzw (Prod.ext hx h)
      exact hsegD ⟨hx, by linarith [hy.1], lt_of_le_of_ne hy.2 hyw⟩
  have hBT : B ⊆ D \ T := by
    intro z hzB
    refine ⟨hBD hzB, fun hzT => ?_⟩
    have hzc := subset_closure hzB
    rcases husub hzT with (hz | hz) | hz
    · obtain ⟨hx, hy⟩ := hs1 z hz
      rcases eq_or_lt_of_le hy.1 with h0 | h0
      · exact disjoint_left.1 hBe hzc
          (Or.inr ⟨⟨hx ▸ hx₀.1.le, hx ▸ hx₀.2.le⟩, show z.2 = 0 from h0.symm⟩)
      · exact disjoint_left.1 hlo hzc ⟨hx, h0, hy.2⟩
    · exact (hGsub (hvG hz)).2 hzc
    · obtain ⟨hx, hy⟩ := hs3 z hz
      rcases eq_or_lt_of_le hy.2 with hw | hw
      · have : z = ((x₀, w₂) : ℝ × ℝ) := Prod.ext hx hw
        exact disjoint_left.1 hBe hzc (Or.inl (this ▸ hwI))
      · exact disjoint_left.1 hhi hzc ⟨hx, hy.1, hw⟩
  obtain ⟨p, hpB, hp⟩ := hBl
  obtain ⟨q, hqB, hq⟩ := hBr
  exact rect_domain_crosscut_arc hab hI hIR hr hs hIs hDo hDR hDf hx₀ hwI hx₀ hT hTD hB hBT hp hq
    hpB hqB

end HPC.Hagopian
