import HPC.Plane.CantorOrgan

/-!
# Batch 97: the Cantor organ, part two — layers

The layer of `t ∈ [0,1]` is `F⁻¹{t}`. It is one strand (`t` not dyadic, or `t ∈ {0,1}`) or two
strands glued at the top or at the bottom (`t` dyadic). `lft t` and `rgt t` are the parameters
of its left and right strands (equal for a single strand); `gam t` parametrises the layer by
`[0,2]`, from the bottom of the left strand to the end of the right strand.
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-! ## Ends and the fibres of `λ` -/

/-- `b = w 0 1 1 1 …`: the left endpoint of a gap. -/
def IsLeftEnd (b : Cs) : Prop := ∃ m b', Pair m b b'
/-- `b = w 1 0 0 0 …`: the right endpoint of a gap. -/
def IsRightEnd (b : Cs) : Prop := ∃ m b', Pair m b' b

theorem lam_eq_cases {b b' : Cs} (h : lam b = lam b') :
    b = b' ∨ (∃ m, Pair m b b') ∨ ∃ m, Pair m b' b := by
  by_cases hbb : b = b'
  · exact Or.inl hbb
  obtain ⟨m, hm | hm⟩ := exists_firstDiff hbb
  · exact Or.inr (Or.inl ⟨m, (lam_eq_iff hm).mp h⟩)
  · exact Or.inr (Or.inr ⟨m, (lam_eq_iff hm).mp h.symm⟩)

theorem not_leftEnd_of_rightEnd {b : Cs} (hr : IsRightEnd b) : ¬ IsLeftEnd b := by
  rintro ⟨m, b', h⟩
  obtain ⟨m', b'', h'⟩ := hr
  have h1 := (h.2 (max m m' + 1) (by omega)).1
  have h2 := (h'.2 (max m m' + 1) (by omega)).2
  rw [h1] at h2; exact Bool.noConfusion h2

theorem Pair.index_unique {m m' : ℕ} {b b' : Cs} (h : Pair m b b') (h' : Pair m' b b') : m = m' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.1.1 m hlt; rw [h.1.2.1, h.1.2.2] at this; exact Bool.noConfusion this
  · have := h.1.1 m' hlt; rw [h'.1.2.1, h'.1.2.2] at this; exact Bool.noConfusion this

theorem lam_const_false : lam (fun _ => false) = 0 := by
  simp [lam, Wt.sum, ind]

theorem lam_const_true : lam (fun _ => true) = 1 := by
  have h := wL.hasSum_p_tail 0
  simp only [add_zero] at h
  simp only [lam, Wt.sum, ind, if_true, one_mul]
  rw [h.tsum_eq]; simp [wL]

/-- Flip all digits from `m` on. -/
def flipFrom (m : ℕ) (b : Cs) : Cs := fun k => if k < m then b k else !b k

/-- An eventually-`false` sequence other than `0^∞` is a right end. -/
theorem isRightEnd_of_last_true {b : Cs} {m : ℕ} (hm : b m = true)
    (hk : ∀ k, m < k → b k = false) : IsRightEnd b := by
  refine ⟨m, flipFrom m b, ⟨⟨fun k hk' => ?_, ?_, hm⟩, fun k hk' => ⟨?_, hk k hk'⟩⟩⟩
  · simp [flipFrom, hk']
  · simp [flipFrom, hm]
  · simp [flipFrom, show ¬ k < m by omega, hk k hk']

theorem isLeftEnd_of_last_false {b : Cs} {m : ℕ} (hm : b m = false)
    (hk : ∀ k, m < k → b k = true) : IsLeftEnd b := by
  refine ⟨m, flipFrom m b, ⟨⟨fun k hk' => ?_, hm, ?_⟩, fun k hk' => ⟨hk k hk', ?_⟩⟩⟩
  · simp [flipFrom, hk']
  · simp [flipFrom, hm]
  · simp [flipFrom, show ¬ k < m by omega, hk k hk']

/-- A non-right-end with positive value has infinitely many `true` digits. -/
theorem frequently_true {b : Cs} (hb : ¬ IsRightEnd b) (hpos : 0 < lam b) :
    ∀ N, ∃ k, N ≤ k ∧ b k = true := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨N, hN⟩ := hno
  by_cases hex : ∃ k, b k = true
  · -- the last `true`
    have hfin : ∃ M, ∀ k, b k = true → k ≤ M := ⟨N, fun k hk => by
      by_contra hlt; push_neg at hlt; exact hN k hlt.le hk⟩
    let M := Nat.find hfin
    have hM := Nat.find_spec hfin
    have hbM : b M = true := by
      obtain ⟨k0, hk0⟩ := hex
      by_contra hne
      have hM0 : M ≠ 0 := by
        intro h0
        have := hM k0 hk0
        have hk00 : k0 = 0 := by omega
        rw [hk00] at hk0
        exact hne (by rw [show M = 0 from h0]; exact hk0)
      have := Nat.find_min hfin (show M - 1 < M by omega)
      apply this
      intro k hk
      have := hM k hk
      rcases Nat.lt_or_ge k M with h | h
      · omega
      · have : k = M := le_antisymm this h
        rw [this] at hk; exact absurd hk hne
    exact hb (isRightEnd_of_last_true hbM fun k hk => by
      by_contra hne
      have := hM k (by simpa using hne)
      omega)
  · push_neg at hex
    have : b = fun _ => false := funext fun k => by simpa using hex k
    rw [this, lam_const_false] at hpos
    exact lt_irrefl _ hpos

/-- A non-left-end with value below `1` has infinitely many `false` digits. -/
theorem frequently_false {b : Cs} (hb : ¬ IsLeftEnd b) (hlt : lam b < 1) :
    ∀ N, ∃ k, N ≤ k ∧ b k = false := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨N, hN⟩ := hno
  by_cases hex : ∃ k, b k = false
  · have hfin : ∃ M, ∀ k, b k = false → k ≤ M := ⟨N, fun k hk => by
      by_contra hlt'; push_neg at hlt'; exact hN k hlt'.le hk⟩
    let M := Nat.find hfin
    have hM := Nat.find_spec hfin
    have hbM : b M = false := by
      obtain ⟨k0, hk0⟩ := hex
      by_contra hne
      have hM0 : M ≠ 0 := by
        intro h0
        have := hM k0 hk0
        have hk00 : k0 = 0 := by omega
        rw [hk00] at hk0
        exact hne (by rw [show M = 0 from h0]; exact hk0)
      have := Nat.find_min hfin (show M - 1 < M by omega)
      apply this
      intro k hk
      have := hM k hk
      rcases Nat.lt_or_ge k M with h | h
      · omega
      · have : k = M := le_antisymm this h
        rw [this] at hk; exact absurd hk hne
    exact hb (isLeftEnd_of_last_false hbM fun k hk => by
      by_contra hne
      have := hM k (by simpa using hne)
      omega)
  · push_neg at hex
    have : b = fun _ => true := funext fun k => by simpa using hex k
    rw [this, lam_const_true] at hlt
    exact lt_irrefl _ hlt

/-! ## The left and right parameters of a layer -/

theorem exists_lft {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ∃ c, lam c = t ∧ ¬ IsRightEnd c := by
  obtain ⟨b, hb⟩ := lam_surj ht
  by_cases hr : IsRightEnd b
  · obtain ⟨m, b', hp⟩ := hr
    exact ⟨b', by rw [← hb, lam_pair hp], not_leftEnd_of_rightEnd.mt (not_not.mpr ⟨m, b, hp⟩)⟩
  · exact ⟨b, hb, hr⟩

theorem exists_rgt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ∃ c, lam c = t ∧ ¬ IsLeftEnd c := by
  obtain ⟨b, hb⟩ := lam_surj ht
  by_cases hl : IsLeftEnd b
  · obtain ⟨m, b', hp⟩ := hl
    exact ⟨b', by rw [← hb, lam_pair hp], fun h => not_leftEnd_of_rightEnd ⟨m, b, hp⟩ h⟩
  · exact ⟨b, hb, hl⟩

/-- The parameter of the left strand of the layer `t`. -/
noncomputable def lft (t : ℝ) : Cs := Classical.epsilon fun c => lam c = t ∧ ¬ IsRightEnd c
/-- The parameter of the right strand of the layer `t`. -/
noncomputable def rgt (t : ℝ) : Cs := Classical.epsilon fun c => lam c = t ∧ ¬ IsLeftEnd c

theorem lft_spec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : lam (lft t) = t ∧ ¬ IsRightEnd (lft t) :=
  Classical.epsilon_spec (exists_lft ht)

theorem rgt_spec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : lam (rgt t) = t ∧ ¬ IsLeftEnd (rgt t) :=
  Classical.epsilon_spec (exists_rgt ht)

theorem eq_lft {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {c : Cs} (hc : lam c = t) (hr : ¬ IsRightEnd c) :
    c = lft t := by
  obtain ⟨h1, h2⟩ := lft_spec ht
  rcases lam_eq_cases (hc.trans h1.symm) with h | ⟨m, h⟩ | ⟨m, h⟩
  · exact h
  · exact absurd ⟨m, c, h⟩ h2
  · exact absurd ⟨m, lft t, h⟩ hr

theorem eq_rgt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {c : Cs} (hc : lam c = t) (hl : ¬ IsLeftEnd c) :
    c = rgt t := by
  obtain ⟨h1, h2⟩ := rgt_spec ht
  rcases lam_eq_cases (hc.trans h1.symm) with h | ⟨m, h⟩ | ⟨m, h⟩
  · exact h
  · exact absurd ⟨m, rgt t, h⟩ hl
  · exact absurd ⟨m, c, h⟩ h2

theorem lam_eq_lft_or_rgt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {c : Cs} (hc : lam c = t) :
    c = lft t ∨ c = rgt t := by
  by_cases hr : IsRightEnd c
  · exact Or.inr (eq_rgt ht hc (not_leftEnd_of_rightEnd hr))
  · exact Or.inl (eq_lft ht hc hr)

theorem lft_eq_or_pair {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lft t = rgt t ∨ ∃ m, Pair m (lft t) (rgt t) := by
  obtain ⟨h1, h2⟩ := lft_spec ht
  obtain ⟨h3, h4⟩ := rgt_spec ht
  rcases lam_eq_cases (h1.trans h3.symm) with h | h | ⟨m, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ⟨m, lft t, h⟩ h4

/-- The index of the gap of a dyadic layer. -/
noncomputable def gidx (t : ℝ) : ℕ :=
  Classical.epsilon fun m => Pair m (lft t) (rgt t)

theorem gidx_spec {t : ℝ} (h : ∃ m, Pair m (lft t) (rgt t)) : Pair (gidx t) (lft t) (rgt t) :=
  Classical.epsilon_spec h

/-- The glueing height of a dyadic layer: `1` for odd gaps, `0` for even ones. -/
noncomputable def gh (t : ℝ) : ℝ := if Odd (gidx t) then 1 else 0

theorem gh_mem (t : ℝ) : gh t ∈ Icc (0 : ℝ) 1 := by
  unfold gh; split_ifs <;> norm_num

/-! ## Points and strands -/

/-- The point of the strand `c` at height `y` (clamped to `[0,1]`). -/
noncomputable def pt (c : Cs) (y : ℝ) : Organ := Phi (c, projIcc 0 1 zero_le_one y)

theorem continuous_pt (c : Cs) : Continuous (pt c) :=
  continuous_Phi.comp (continuous_const.prodMk continuous_projIcc)

theorem pt_height (c : Cs) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (pt c y : ℝ × ℝ).2 = y := by
  simp [pt, Phi_height, projIcc_of_mem _ hy]

theorem F_pt (c : Cs) (y : ℝ) : F (pt c y) = lam c := F_Phi _

theorem Phi_eq_pt (d : Dom) : Phi d = pt d.1 d.2 := by
  simp [pt, projIcc_val]

/-- Points of `Organ`. -/
theorem exists_pt (s : Organ) : ∃ c : Cs, ∃ y ∈ Icc (0 : ℝ) 1, s = pt c y := by
  obtain ⟨d, rfl⟩ := surjective_Phi s
  exact ⟨d.1, d.2, d.2.2, Phi_eq_pt d⟩

/-- **The identifications, for `pt`.** -/
theorem pt_eq_pt_iff {c c' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    pt c y = pt c' y' ↔ y = y' ∧ (c = c' ∨ ∃ m, (Pair m c c' ∨ Pair m c' c) ∧
      ((y = 1 ∧ Odd m) ∨ (y = 0 ∧ Even m))) := by
  simp only [pt, Phi_eq_iff, projIcc_of_mem _ hy, projIcc_of_mem _ hy']
  exact psi_eq_psi_iff hy

/-- The strand of `c`. -/
def strand (c : Cs) : Set Organ := pt c '' Icc 0 1

theorem isPreconnected_strand (c : Cs) : IsPreconnected (strand c) :=
  isPreconnected_Icc.image _ (continuous_pt c).continuousOn

/-- The glue point of a dyadic layer lies on both strands. -/
theorem pt_lft_gh {t : ℝ} (h : ∃ m, Pair m (lft t) (rgt t)) :
    pt (lft t) (gh t) = pt (rgt t) (gh t) := by
  rw [pt_eq_pt_iff (gh_mem t) (gh_mem t)]
  refine ⟨rfl, Or.inr ⟨gidx t, Or.inl (gidx_spec h), ?_⟩⟩
  unfold gh
  split_ifs with ho
  · exact Or.inl ⟨rfl, ho⟩
  · exact Or.inr ⟨rfl, Nat.not_odd_iff_even.mp ho⟩

/-- Across the two strands of a dyadic layer, the only identification is at the glue height. -/
theorem cross_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hne : lft t ≠ rgt t) {y y' : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) (h : pt (lft t) y = pt (rgt t) y') :
    y = gh t ∧ y' = gh t := by
  obtain ⟨rfl, h | ⟨m, hp, hyo⟩⟩ := (pt_eq_pt_iff hy hy').mp h
  · exact absurd h hne
  have hpair : ∃ m, Pair m (lft t) (rgt t) := by
    rcases lft_eq_or_pair ht with h | h
    · exact absurd h hne
    · exact h
  have hg := gidx_spec hpair
  rcases hp with hp | hp
  · have := hp.index_unique hg
    subst this
    unfold gh
    rcases hyo with ⟨rfl, ho⟩ | ⟨rfl, he⟩
    · simp [ho]
    · simp [Nat.not_odd_iff_even.mpr he]
  · exact absurd ⟨m, lft t, hp⟩ (rgt_spec ht).2

theorem pt_inj {c : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1)
    (h : pt c y = pt c y') : y = y' := ((pt_eq_pt_iff hy hy').mp h).1

/-! ## Layers -/

/-- The layer of `t`. -/
def layer (t : ℝ) : Set Organ := F ⁻¹' {t}

theorem layer_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : layer t = strand (lft t) ∪ strand (rgt t) := by
  ext s
  constructor
  · intro hs
    obtain ⟨c, y, hy, rfl⟩ := exists_pt s
    have hc : lam c = t := by rw [← F_pt c y]; exact hs
    rcases lam_eq_lft_or_rgt ht hc with rfl | rfl
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩)
    · show F _ = t; rw [F_pt, (lft_spec ht).1]
    · show F _ = t; rw [F_pt, (rgt_spec ht).1]

open Classical in
/-- **The parametrisation of a layer by `[0,2]`.** -/
noncomputable def gam (t : ℝ) (τ : ℝ) : Organ :=
  if lft t = rgt t then pt (lft t) (τ / 2)
  else if Odd (gidx t) then (if τ ≤ 1 then pt (lft t) τ else pt (rgt t) (2 - τ))
  else (if τ ≤ 1 then pt (lft t) (1 - τ) else pt (rgt t) (τ - 1))

theorem continuous_gam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Continuous (gam t) := by
  unfold gam
  split_ifs with h1 h2
  · exact (continuous_pt _).comp (continuous_id.div_const 2)
  · have hp : ∃ m, Pair m (lft t) (rgt t) := (lft_eq_or_pair ht).resolve_left h1
    refine Continuous.if_le ((continuous_pt _)) ((continuous_pt _).comp
      (continuous_const.sub continuous_id)) continuous_id continuous_const ?_
    intro τ hτ
    subst hτ
    have := pt_lft_gh hp
    simp only [gh, h2, if_true] at this
    norm_num; exact this
  · have hp : ∃ m, Pair m (lft t) (rgt t) := (lft_eq_or_pair ht).resolve_left h1
    refine Continuous.if_le ((continuous_pt _).comp (continuous_const.sub continuous_id))
      ((continuous_pt _).comp (continuous_id.sub continuous_const)) continuous_id
      continuous_const ?_
    intro τ hτ
    subst hτ
    have := pt_lft_gh hp
    simp only [gh, h2, if_false] at this
    norm_num; exact this

theorem gam_mem_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (τ : ℝ) : gam t τ ∈ layer t := by
  show F _ = t
  unfold gam
  split_ifs <;> rw [F_pt] <;> first | exact (lft_spec ht).1 | exact (rgt_spec ht).1

theorem image_gam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : gam t '' Icc 0 2 = layer t := by
  apply Subset.antisymm
  · rintro _ ⟨τ, -, rfl⟩; exact gam_mem_layer ht τ
  rw [layer_eq ht]
  rintro s (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
  · by_cases h1 : lft t = rgt t
    · exact ⟨2 * y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by simp [gam, h1]⟩
    by_cases h2 : Odd (gidx t)
    · exact ⟨y, ⟨hy.1, by linarith [hy.2]⟩, by simp [gam, h1, h2, hy.2]⟩
    · refine ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
      simp [gam, h1, h2, hy.1]
  · by_cases h1 : lft t = rgt t
    · exact ⟨2 * y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by simp [gam, h1]⟩
    by_cases h2 : Odd (gidx t)
    · rcases eq_or_lt_of_le hy.2 with hy1 | hy1
      · -- the glue point
        have hp : ∃ m, Pair m (lft t) (rgt t) := (lft_eq_or_pair ht).resolve_left h1
        refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
        have := pt_lft_gh hp
        simp only [gh, h2, if_true] at this
        simp [gam, h1, h2, hy1, this]
      · refine ⟨2 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
        simp [gam, h1, h2, show ¬ (2 - y ≤ 1) by linarith]
    · rcases eq_or_lt_of_le hy.1 with hy0 | hy0
      · have hp : ∃ m, Pair m (lft t) (rgt t) := (lft_eq_or_pair ht).resolve_left h1
        refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
        have := pt_lft_gh hp
        simp only [gh, h2, if_false] at this
        simp [gam, h1, h2, ← hy0, this]
      · refine ⟨1 + y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
        simp [gam, h1, h2, show ¬ (1 + y ≤ 1) by linarith]

theorem gam_injOn {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : InjOn (gam t) (Icc 0 2) := by
  intro τ hτ τ' hτ' h
  unfold gam at h
  split_ifs at h with h1 h2 hA hB hB hA hB hB
  · have := pt_inj ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩ h
    linarith
  · exact pt_inj ⟨hτ.1, hA⟩ ⟨hτ'.1, hB⟩ h
  · obtain ⟨e1, e2⟩ := cross_eq ht h1 ⟨hτ.1, hA⟩ ⟨by linarith [hτ'.2], by linarith⟩ h
    simp only [gh, h2, if_true] at e1 e2
    linarith
  · obtain ⟨e1, e2⟩ := cross_eq ht h1 ⟨hτ'.1, hB⟩ ⟨by linarith [hτ.2], by linarith⟩ h.symm
    simp only [gh, h2, if_true] at e1 e2
    linarith
  · have := pt_inj ⟨by linarith [hτ.2], by linarith⟩ ⟨by linarith [hτ'.2], by linarith⟩ h
    linarith
  · have := pt_inj ⟨by linarith [hA], by linarith [hτ.1]⟩ ⟨by linarith [hB], by linarith [hτ'.1]⟩ h
    linarith
  · obtain ⟨e1, e2⟩ := cross_eq ht h1 ⟨by linarith, by linarith [hτ.1]⟩
      ⟨by linarith, by linarith [hτ'.2]⟩ h
    simp only [gh, h2, if_false] at e1 e2
    linarith
  · obtain ⟨e1, e2⟩ := cross_eq ht h1 ⟨by linarith, by linarith [hτ'.1]⟩
      ⟨by linarith, by linarith [hτ.2]⟩ h.symm
    simp only [gh, h2, if_false] at e1 e2
    linarith
  · have := pt_inj ⟨by linarith, by linarith [hτ.2]⟩ ⟨by linarith, by linarith [hτ'.2]⟩ h
    linarith

theorem gam_zero_mem {t : ℝ} : gam t 0 ∈ strand (lft t) := by
  by_cases h1 : lft t = rgt t
  · rw [gam, if_pos h1]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by norm_num⟩
  by_cases h2 : Odd (gidx t)
  · rw [gam, if_neg h1, if_pos h2, if_pos zero_le_one]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  · rw [gam, if_neg h1, if_neg h2, if_pos zero_le_one]
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, by norm_num⟩

theorem gam_two_mem {t : ℝ} : gam t 2 ∈ strand (rgt t) := by
  by_cases h1 : lft t = rgt t
  · rw [gam, if_pos h1]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [← h1]; norm_num⟩
  by_cases h2 : Odd (gidx t)
  · rw [gam, if_neg h1, if_pos h2, if_neg (by norm_num)]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by norm_num⟩
  · rw [gam, if_neg h1, if_neg h2, if_neg (by norm_num)]
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, by norm_num⟩

theorem isPreconnected_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : IsPreconnected (layer t) := by
  rw [← image_gam ht]
  exact isPreconnected_Icc.image _ (continuous_gam ht).continuousOn

theorem layer_nonempty {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (layer t).Nonempty :=
  ⟨gam t 0, gam_mem_layer ht 0⟩

/-! ## Preimages of intervals are connected -/

theorem isPreconnected_preimage_F {J : Set ℝ} (hJ : IsPreconnected J) :
    IsPreconnected (F ⁻¹' J) := by
  set s := J ∩ Icc (0 : ℝ) 1 with hs
  have hpre : F ⁻¹' J = F ⁻¹' s := by
    ext x; simp [hs, F_mem x]
  rw [hpre]
  have hsc : IsPreconnected s := by
    rw [isPreconnected_iff_ordConnected] at hJ ⊢
    exact hJ.inter ordConnected_Icc
  rcases (F ⁻¹' s).eq_empty_or_nonempty with he | ⟨a, ha⟩
  · rw [he]; exact isPreconnected_empty
  set g := s.restrictPreimage F with hg
  have hgc : Continuous g := continuous_F.restrictPreimage
  have hgcl : IsClosedMap g := isClosedMap_F.restrictPreimage s
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := F_surj hy.2
    exact ⟨⟨x, by simp [hx, hy]⟩, Subtype.ext hx⟩
  have hq := hgcl.isQuotientMap hgc hgs
  have hfib : ∀ y : s, IsConnected (g ⁻¹' {y}) := by
    intro y
    have himg : Subtype.val '' (g ⁻¹' {y}) = layer y := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        have := congrArg Subtype.val hx'
        exact this
      · intro hx
        refine ⟨⟨x, ?_⟩, ?_, rfl⟩
        · show F x ∈ s; rw [show F x = y from hx]; exact y.2
        · exact Subtype.ext hx
    have hyI : (y : ℝ) ∈ Icc (0 : ℝ) 1 := y.2.2
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := layer_nonempty hyI
      rw [← himg] at hx
      obtain ⟨x', hx', -⟩ := hx
      exact ⟨x', hx'⟩
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
      exact isPreconnected_layer hyI
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace hsc
  have hcc := hq.preimage_connectedComponent hfib ⟨a, ha⟩
  rw [PreconnectedSpace.connectedComponent_eq_univ, preimage_univ] at hcc
  have : IsPreconnected (univ : Set (F ⁻¹' s)) := by
    rw [hcc]; exact isPreconnected_connectedComponent
  have := this.image _ continuous_subtype_val.continuousOn
  simpa using this

end HPC.Plane.Org
