import HPC.Plane.CantorOrganLayers

/-!
# Batch 97: the Cantor organ, part three — subcontinua

The main result is `mem_of_between`: a closed connected set meeting the layers `t₁ < t₂`
contains every layer strictly between them. The proof (`mem_of_good`) works at a *good*
parameter `c` (digits ending in `0 1 1 0 1 1 …`): around the strand of `c` there are cylinders
whose boundary gaps are both odd (glued at the top) and cylinders whose boundary gaps are both
even (glued at the bottom); a connected set missing a point of the strand would split along one
of them. Good parameters are dense, which gives the general case.

Then `layer_inter_isPreconnected`: a subcontinuum meets each layer in a connected set.
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-! ## Cylinders -/

/-- The cylinder of sequences agreeing with `c` below `n`. -/
def cyl (c : Cs) (n : ℕ) : Set Cs := {b | ∀ k < n, b k = c k}

theorem cyl_eq (c : Cs) (n : ℕ) : cyl c n = ⋂ k ∈ Finset.range n, (fun b : Cs => b k) ⁻¹' {c k} := by
  ext b; simp [cyl]

theorem isOpen_cyl (c : Cs) (n : ℕ) : IsOpen (cyl c n) := by
  rw [cyl_eq]
  exact isOpen_biInter_finset fun k _ => (continuous_apply k).isOpen_preimage _ (isOpen_discrete _)

theorem isClosed_cyl (c : Cs) (n : ℕ) : IsClosed (cyl c n) := by
  rw [cyl_eq]
  exact isClosed_biInter fun k _ => (isClosed_discrete _).preimage (continuous_apply k)

theorem mem_cyl_self (c : Cs) (n : ℕ) : c ∈ cyl c n := fun _ _ => rfl

theorem cyl_anti (c : Cs) {m n : ℕ} (h : m ≤ n) : cyl c n ⊆ cyl c m :=
  fun _ hb k hk => hb k (by omega)

theorem exists_cyl_subset {c : Cs} {U : Set Cs} (hU : IsOpen U) (hc : c ∈ U) :
    ∃ N, cyl c N ⊆ U := by
  obtain ⟨_, ⟨x, n, rfl⟩, hcx, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open hc hU
  refine ⟨n, fun b hb => hsub ?_⟩
  rw [PiNat.mem_cylinder_iff] at hcx ⊢
  intro i hi; rw [hb i hi, hcx i hi]

/-- Eventually in every cylinder. -/
theorem eventually_cyl {α : Type*} {l : Filter α} {u : α → Cs} {c : Cs}
    (h : Tendsto u l (𝓝 c)) (n : ℕ) : ∀ᶠ a in l, u a ∈ cyl c n :=
  h (isOpen_cyl c n |>.mem_nhds (mem_cyl_self c n))

/-! ## Flipping one digit -/

/-- Flip digit `k`. -/
def flip1 (c : Cs) (k : ℕ) : Cs := Function.update c k (!c k)

theorem lam_flip1_true {c : Cs} {k : ℕ} (hk : c k = true) : lam (flip1 c k) = lam c - wL.p k := by
  have hfd : FirstDiff k (flip1 c k) c :=
    ⟨fun j hj => by simp [flip1, Function.update_of_ne (show j ≠ k by omega)],
      by simp [flip1, hk], hk⟩
  have h := wL.hasSum_diff_tail hfd
  have hz : (fun j => (ind (c (j + (k + 1))) - ind (flip1 c k (j + (k + 1)))) *
      wL.p (j + (k + 1))) = fun _ => 0 := by
    funext j; simp [flip1, Function.update_of_ne (show j + (k + 1) ≠ k by omega)]
  rw [hz] at h
  have := h.unique hasSum_zero
  unfold lam; linarith

theorem lam_flip1_false {c : Cs} {k : ℕ} (hk : c k = false) :
    lam (flip1 c k) = lam c + wL.p k := by
  have hfd : FirstDiff k c (flip1 c k) :=
    ⟨fun j hj => by simp [flip1, Function.update_of_ne (show j ≠ k by omega)],
      hk, by simp [flip1, hk]⟩
  have h := wL.hasSum_diff_tail hfd
  have hz : (fun j => (ind (flip1 c k (j + (k + 1))) - ind (c (j + (k + 1)))) *
      wL.p (j + (k + 1))) = fun _ => 0 := by
    funext j; simp [flip1, Function.update_of_ne (show j + (k + 1) ≠ k by omega)]
  rw [hz] at h
  have := h.unique hasSum_zero
  unfold lam; linarith

theorem wL_p_le (k : ℕ) : wL.p k ≤ (1 / 2 : ℝ) ^ k := by
  simp only [Wt.p, wL]
  have : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
  linarith

theorem tendsto_flip1 (c : Cs) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun n => flip1 c (k n)) atTop (𝓝 c) := by
  rw [tendsto_pi_nhds]
  intro j
  apply tendsto_const_nhds.congr'
  filter_upwards [hk.eventually_gt_atTop j] with n hn
  simp [flip1, Function.update_of_ne (show j ≠ k n by omega)]

theorem continuous_pt_param (y : ℝ) : Continuous fun c : Cs => pt c y :=
  continuous_Phi.comp (continuous_id.prodMk continuous_const)

/-- **Points of a strand are limits from the left** (when the parameter has infinitely many
`true` digits). -/
theorem pt_mem_closure_left {c : Cs} (hc : ∀ N, ∃ k, N ≤ k ∧ c k = true) {t' : ℝ}
    (ht' : t' < lam c) (y : ℝ) : pt c y ∈ closure (F ⁻¹' Ioo t' (lam c)) := by
  choose k hk1 hk2 using hc
  have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk1 tendsto_id
  apply mem_closure_of_tendsto ((continuous_pt_param y).continuousAt.tendsto.comp
    (tendsto_flip1 c hkt))
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hpow (Iio_mem_nhds (sub_pos.mpr ht'))] with n hn
  show F (pt (flip1 c (k n)) y) ∈ Ioo t' (lam c)
  rw [F_pt, lam_flip1_true (hk2 n)]
  have hn' : (1 / 2 : ℝ) ^ n < lam c - t' := hn
  have h1 := wL.p_pos (k n)
  have h2 : wL.p (k n) ≤ (1 / 2 : ℝ) ^ n :=
    (wL_p_le _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hk1 n))
  exact ⟨by linarith, by linarith⟩

/-- **Points of a strand are limits from the right** (infinitely many `false` digits). -/
theorem pt_mem_closure_right {c : Cs} (hc : ∀ N, ∃ k, N ≤ k ∧ c k = false) {t' : ℝ}
    (ht' : lam c < t') (y : ℝ) : pt c y ∈ closure (F ⁻¹' Ioo (lam c) t') := by
  choose k hk1 hk2 using hc
  have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk1 tendsto_id
  apply mem_closure_of_tendsto ((continuous_pt_param y).continuousAt.tendsto.comp
    (tendsto_flip1 c hkt))
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hpow (Iio_mem_nhds (sub_pos.mpr ht'))] with n hn
  show F (pt (flip1 c (k n)) y) ∈ Ioo (lam c) t'
  rw [F_pt, lam_flip1_false (hk2 n)]
  have hn' : (1 / 2 : ℝ) ^ n < t' - lam c := hn
  have h1 := wL.p_pos (k n)
  have h2 : wL.p (k n) ≤ (1 / 2 : ℝ) ^ n :=
    (wL_p_le _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hk1 n))
  exact ⟨by linarith, by linarith⟩

/-! ## Limits from one side land on one strand -/

theorem F_preimage_eq_image (A : Set ℝ) : F ⁻¹' A = Phi '' {d : Dom | lam d.1 ∈ A} := by
  ext s
  constructor
  · intro hs
    obtain ⟨d, rfl⟩ := surjective_Phi s
    exact ⟨d, by simpa [F_Phi] using hs, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    simpa [F_Phi] using hd

/-- Near a right end `w 1 0 0 …`, the value of `λ` does not drop. -/
theorem lam_ge_of_cyl_rightEnd {r b : Cs} {m : ℕ} (hr : ∀ k, m < k → r k = false)
    (hb : b ∈ cyl r (m + 1)) : lam r ≤ lam b := by
  by_cases hbr : b = r
  · rw [hbr]
  obtain ⟨j, hj | hj⟩ := exists_firstDiff hbr
  · -- `b j = false`, `r j = true`: impossible past `m`, and below `m + 1` they agree
    rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · have := hb j hjm; rw [hj.2.1, hj.2.2] at this; exact Bool.noConfusion this
    · have := hr j (by omega); rw [hj.2.2] at this; exact Bool.noConfusion this
  · exact lam_le_of hj

theorem lam_le_of_cyl_leftEnd {l b : Cs} {m : ℕ} (hl : ∀ k, m < k → l k = true)
    (hb : b ∈ cyl l (m + 1)) : lam b ≤ lam l := by
  by_cases hbl : b = l
  · rw [hbl]
  obtain ⟨j, hj | hj⟩ := exists_firstDiff hbl
  · exact lam_le_of hj
  · rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · have := hb j hjm; rw [hj.2.1, hj.2.2] at this; exact Bool.noConfusion this
    · have := hl j (by omega); rw [hj.2.1] at this; exact Bool.noConfusion this

/-- **Left limits lie on the left strand.** -/
theorem closure_left_inter_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closure (F ⁻¹' Iio t) ∩ layer t ⊆ strand (lft t) := by
  rintro p ⟨hp, hpt⟩
  rw [F_preimage_eq_image, isClosedMap_Phi.closure_image_eq_of_continuous continuous_Phi]
    at hp
  obtain ⟨d, hd, rfl⟩ := hp
  have hlam : lam d.1 = t := by rw [← F_Phi]; exact hpt
  rcases lam_eq_lft_or_rgt ht hlam with h | h
  · exact ⟨d.2, d.2.2, by rw [Phi_eq_pt, h]⟩
  -- `d.1 = rgt t`; if it is also `lft t` we are done
  by_cases hlr : lft t = rgt t
  · exact ⟨d.2, d.2.2, by rw [Phi_eq_pt, h, hlr]⟩
  exfalso
  obtain ⟨m, hm⟩ := (lft_eq_or_pair ht).resolve_left hlr
  have hU : IsOpen (cyl (rgt t) (m + 1) ×ˢ (univ : Set (Icc (0 : ℝ) 1))) :=
    (isOpen_cyl _ _).prod isOpen_univ
  obtain ⟨d', hd'U, hd'A⟩ := mem_closure_iff.mp hd _ hU ⟨by rw [h]; exact mem_cyl_self _ _,
    mem_univ _⟩
  have := lam_ge_of_cyl_rightEnd (fun k hk => (hm.2 k hk).2) hd'U.1
  rw [(rgt_spec ht).1] at this
  exact absurd hd'A (not_lt.mpr this)

/-- **Right limits lie on the right strand.** -/
theorem closure_right_inter_layer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closure (F ⁻¹' Ioi t) ∩ layer t ⊆ strand (rgt t) := by
  rintro p ⟨hp, hpt⟩
  rw [F_preimage_eq_image, isClosedMap_Phi.closure_image_eq_of_continuous continuous_Phi]
    at hp
  obtain ⟨d, hd, rfl⟩ := hp
  have hlam : lam d.1 = t := by rw [← F_Phi]; exact hpt
  rcases lam_eq_lft_or_rgt ht hlam with h | h
  swap
  · exact ⟨d.2, d.2.2, by rw [Phi_eq_pt, h]⟩
  by_cases hlr : lft t = rgt t
  · exact ⟨d.2, d.2.2, by rw [Phi_eq_pt, h, hlr]⟩
  exfalso
  obtain ⟨m, hm⟩ := (lft_eq_or_pair ht).resolve_left hlr
  have hU : IsOpen (cyl (lft t) (m + 1) ×ˢ (univ : Set (Icc (0 : ℝ) 1))) :=
    (isOpen_cyl _ _).prod isOpen_univ
  obtain ⟨d', hd'U, hd'A⟩ := mem_closure_iff.mp hd _ hU ⟨by rw [h]; exact mem_cyl_self _ _,
    mem_univ _⟩
  have := lam_le_of_cyl_leftEnd (fun k hk => (hm.2 k hk).1) hd'U.1
  rw [(lft_spec ht).1] at this
  exact absurd hd'A (not_lt.mpr this)

/-! ## Good parameters -/

/-- A *good* parameter: from some place `s` on, the digits are `0 1 1 0 1 1 …`. -/
def Good (c : Cs) : Prop :=
  ∃ s, ∀ j, c (s + 3 * j) = false ∧ c (s + 3 * j + 1) = true ∧ c (s + 3 * j + 2) = true

theorem Good.not_leftEnd {c : Cs} (hc : Good c) : ¬ IsLeftEnd c := by
  rintro ⟨m, b', h⟩
  obtain ⟨s, hs⟩ := hc
  have := (h.2 (s + 3 * (m + 1)) (by omega)).1
  rw [(hs (m + 1)).1] at this; exact Bool.noConfusion this

theorem Good.not_rightEnd {c : Cs} (hc : Good c) : ¬ IsRightEnd c := by
  rintro ⟨m, b', h⟩
  obtain ⟨s, hs⟩ := hc
  have := (h.2 (s + 3 * (m + 1) + 1) (by omega)).2
  rw [(hs (m + 1)).2.1] at this; exact Bool.noConfusion this

theorem Good.lam_eq {c b : Cs} (hc : Good c) (h : lam b = lam c) : b = c := by
  rcases lam_eq_cases h with h | ⟨m, h⟩ | ⟨m, h⟩
  · exact h
  · exact absurd ⟨m, b, h⟩ hc.not_rightEnd
  · exact absurd ⟨m, b, h⟩ hc.not_leftEnd

/-- **The crossing lemma.** If the digits of `c` at `n-3, n-2, n-1` are `0 1 1`, the only
identifications between the cylinder `cyl c n` and its complement happen at height `1` when
`n - 1` is odd and at height `0` when `n - 1` is even. -/
theorem cross_cyl {c : Cs} {n : ℕ} (hn : 3 ≤ n) (h3 : c (n - 3) = false) (h2 : c (n - 2) = true)
    (h1 : c (n - 1) = true) {b b' : Cs} (hb : b ∈ cyl c n) (hb' : b' ∉ cyl c n) {y y' : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) (h : pt b y = pt b' y') :
    y = if Odd (n - 1) then 1 else 0 := by
  obtain ⟨rfl, hbb | ⟨m, hp, hyo⟩⟩ := (pt_eq_pt_iff hy hy').mp h
  · exact absurd (hbb ▸ hb) hb'
  -- the gap index `m` is `n - 3` or `n - 1`
  have hmlt : m < n := by
    by_contra hge; push_neg at hge
    apply hb'
    intro k hk
    rcases hp with hp | hp
    · rw [← hp.1.1 k (by omega)]; exact hb k hk
    · rw [hp.1.1 k (by omega)]; exact hb k hk
  have hpar : (Odd m ↔ Odd (n - 1)) := by
    rcases hp with hp | hp
    · -- `b = w 0 1 1 …`
      have hbm : c m = false := by rw [← hb m hmlt]; exact hp.1.2.1
      have hm : m = n - 3 ∨ m = n - 1 := by
        by_contra hno; push_neg at hno
        rcases Nat.lt_or_ge m (n - 3) with hlt | hge
        · have := (hp.2 (n - 3) (by omega)).1
          rw [hb (n - 3) (by omega), h3] at this; exact Bool.noConfusion this
        · have hm2 : m = n - 2 := by omega
          rw [hm2, h2] at hbm; exact Bool.noConfusion hbm
      rcases hm with rfl | rfl
      · constructor <;> intro ho
        · have : n - 1 = (n - 3) + 2 := by omega
          rw [this]; exact ho.add_even even_two
        · have : n - 1 = (n - 3) + 2 := by omega
          rw [this] at ho; exact (Nat.odd_add.mp ho).mpr even_two
      · exact Iff.rfl
    · -- `b = w 1 0 0 …`
      have hbm : c m = true := by rw [← hb m hmlt]; exact hp.1.2.2
      have hm : m = n - 1 := by
        by_contra hno
        rcases Nat.lt_or_ge m (n - 3) with hlt | hge
        · have := (hp.2 (n - 1) (by omega)).2
          rw [hb (n - 1) (by omega), h1] at this; exact Bool.noConfusion this
        · rcases Nat.lt_or_ge m (n - 1) with hlt' | hge'
          · rcases (show m = n - 3 ∨ m = n - 2 by omega) with hm3 | hm2
            · rw [hm3, h3] at hbm; exact Bool.noConfusion hbm
            · have := (hp.2 (n - 1) (by omega)).2
              rw [hb (n - 1) (by omega), h1] at this; exact Bool.noConfusion this
          · omega
      rw [hm]
  rcases hyo with ⟨rfl, ho⟩ | ⟨rfl, he⟩
  · rw [if_pos (hpar.mp ho)]
  · rw [if_neg (fun ho => Nat.not_odd_iff_even.mpr he (hpar.mpr ho))]

theorem dist_pt_same_height {b c : Cs} {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (pt b y) (pt c y) ≤ max |PP b - PP c| |QQ b - QQ c| := by
  rw [Subtype.dist_eq]
  simp only [pt, Phi, projIcc_of_mem _ hy, psi, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
  rw [max_eq_left (abs_nonneg _)]
  have e : y * PP b + (1 - y) * QQ b - (y * PP c + (1 - y) * QQ c) =
      y * (PP b - PP c) + (1 - y) * (QQ b - QQ c) := by ring
  rw [e]
  calc |y * (PP b - PP c) + (1 - y) * (QQ b - QQ c)|
      ≤ |y * (PP b - PP c)| + |(1 - y) * (QQ b - QQ c)| := abs_add_le _ _
    _ = y * |PP b - PP c| + (1 - y) * |QQ b - QQ c| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy.1, abs_of_nonneg (sub_nonneg.mpr hy.2)]
    _ ≤ y * max |PP b - PP c| |QQ b - QQ c| + (1 - y) * max |PP b - PP c| |QQ b - QQ c| := by
        gcongr
        all_goals first | exact hy.1 | exact sub_nonneg.mpr hy.2 | exact le_max_left _ _ |
          exact le_max_right _ _
    _ = _ := by ring

/-- Points of `Organ` coming from a set of parameters form a closed set when the set is closed. -/
theorem isClosed_Phi_image {A : Set Dom} (hA : IsClosed A) : IsClosed (Phi '' A) :=
  isClosedMap_Phi A hA

/-- **The splitting step (top).** Let `K` be closed and connected and `B` a clopen set of
parameters such that no `pt b y₀` with `b ∈ B` lies in `K`, and all identifications between
`B` and its complement happen at height `1`. If `K` has a point outside `B`, then `K` has no
point `pt b y` with `b ∈ B`, `y ≤ y₀`. -/
theorem split_top {K : Set Organ} (hKc : IsPreconnected K) {B : Set Cs}
    (hBc : IsClosed B) (hBo : IsOpen B) {y₀ : ℝ} (hy₀ : y₀ ∈ Icc (0 : ℝ) 1)
    (hmiss : ∀ b ∈ B, pt b y₀ ∉ K)
    (hcross : ∀ b ∈ B, ∀ b' ∉ B, ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1,
      pt b y = pt b' y' → y = 1)
    (hout : ∃ c' ∉ B, ∃ y ∈ Icc (0 : ℝ) 1, pt c' y ∈ K) :
    ∀ b ∈ B, ∀ y ∈ Icc (0 : ℝ) 1, y ≤ y₀ → pt b y ∉ K := by
  set A₁ : Set Dom := {d | d.1 ∈ B ∧ (d.2 : ℝ) ≤ y₀} with hA₁
  set A₂ : Set Dom := {d | d.1 ∉ B ∨ y₀ ≤ (d.2 : ℝ)} with hA₂
  have hA₁c : IsClosed A₁ :=
    (hBc.preimage continuous_fst).inter (isClosed_le (continuous_subtype_val.comp continuous_snd)
      continuous_const)
  have hA₂c : IsClosed A₂ :=
    (hBo.isClosed_compl.preimage continuous_fst).union
      (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd))
  have hcov : K ⊆ Phi '' A₁ ∪ Phi '' A₂ := by
    intro s _
    obtain ⟨d, rfl⟩ := surjective_Phi s
    by_cases hdB : d.1 ∈ B
    · rcases le_total (d.2 : ℝ) y₀ with h | h
      · exact Or.inl ⟨d, ⟨hdB, h⟩, rfl⟩
      · exact Or.inr ⟨d, Or.inr h, rfl⟩
    · exact Or.inr ⟨d, Or.inl hdB, rfl⟩
  have hdisj : K ∩ (Phi '' A₁ ∩ Phi '' A₂) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hsK ⟨d₁, ⟨hd₁B, hd₁y⟩, rfl⟩ ⟨d₂, hd₂, hd₂e⟩
    have he : pt d₂.1 d₂.2 = pt d₁.1 d₁.2 := by rw [← Phi_eq_pt, ← Phi_eq_pt, hd₂e]
    have hyy : (d₂.2 : ℝ) = d₁.2 := ((pt_eq_pt_iff d₂.2.2 d₁.2.2).mp he).1
    have hy₁ : (d₁.2 : ℝ) = y₀ := by
      rcases hd₂ with h | h
      · have := hcross d₁.1 hd₁B d₂.1 h d₁.2 d₁.2.2 d₂.2 d₂.2.2 he.symm
        linarith [hy₀.2]
      · linarith
    apply hmiss d₁.1 hd₁B
    rw [← hy₁, ← Phi_eq_pt]; exact hsK
  intro b hb y hy hyy hbK
  obtain ⟨c', hc', y', hy', hc'K⟩ := hout
  have h1 : (K ∩ Phi '' A₁).Nonempty :=
    ⟨pt b y, hbK, ⟨(b, ⟨y, hy⟩), ⟨hb, hyy⟩, Phi_eq_pt _⟩⟩
  have h2 : (K ∩ Phi '' A₂).Nonempty :=
    ⟨pt c' y', hc'K, ⟨(c', ⟨y', hy'⟩), Or.inl hc', Phi_eq_pt _⟩⟩
  have := isPreconnected_closed_iff.mp hKc _ _ (isClosed_Phi_image hA₁c)
    (isClosed_Phi_image hA₂c) hcov h1 h2
  rw [hdisj] at this
  exact this.ne_empty rfl

/-- **The splitting step (bottom).** -/
theorem split_bot {K : Set Organ} (hKc : IsPreconnected K) {B : Set Cs}
    (hBc : IsClosed B) (hBo : IsOpen B) {y₀ : ℝ} (hy₀ : y₀ ∈ Icc (0 : ℝ) 1)
    (hmiss : ∀ b ∈ B, pt b y₀ ∉ K)
    (hcross : ∀ b ∈ B, ∀ b' ∉ B, ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1,
      pt b y = pt b' y' → y = 0)
    (hout : ∃ c' ∉ B, ∃ y ∈ Icc (0 : ℝ) 1, pt c' y ∈ K) :
    ∀ b ∈ B, ∀ y ∈ Icc (0 : ℝ) 1, y₀ ≤ y → pt b y ∉ K := by
  set A₁ : Set Dom := {d | d.1 ∈ B ∧ y₀ ≤ (d.2 : ℝ)} with hA₁
  set A₂ : Set Dom := {d | d.1 ∉ B ∨ (d.2 : ℝ) ≤ y₀} with hA₂
  have hA₁c : IsClosed A₁ :=
    (hBc.preimage continuous_fst).inter (isClosed_le continuous_const
      (continuous_subtype_val.comp continuous_snd))
  have hA₂c : IsClosed A₂ :=
    (hBo.isClosed_compl.preimage continuous_fst).union
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hcov : K ⊆ Phi '' A₁ ∪ Phi '' A₂ := by
    intro s _
    obtain ⟨d, rfl⟩ := surjective_Phi s
    by_cases hdB : d.1 ∈ B
    · rcases le_total y₀ (d.2 : ℝ) with h | h
      · exact Or.inl ⟨d, ⟨hdB, h⟩, rfl⟩
      · exact Or.inr ⟨d, Or.inr h, rfl⟩
    · exact Or.inr ⟨d, Or.inl hdB, rfl⟩
  have hdisj : K ∩ (Phi '' A₁ ∩ Phi '' A₂) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hsK ⟨d₁, ⟨hd₁B, hd₁y⟩, rfl⟩ ⟨d₂, hd₂, hd₂e⟩
    have he : pt d₂.1 d₂.2 = pt d₁.1 d₁.2 := by rw [← Phi_eq_pt, ← Phi_eq_pt, hd₂e]
    have hyy : (d₂.2 : ℝ) = d₁.2 := ((pt_eq_pt_iff d₂.2.2 d₁.2.2).mp he).1
    have hy₁ : (d₁.2 : ℝ) = y₀ := by
      rcases hd₂ with h | h
      · have := hcross d₁.1 hd₁B d₂.1 h d₁.2 d₁.2.2 d₂.2 d₂.2.2 he.symm
        linarith [hy₀.1]
      · linarith
    apply hmiss d₁.1 hd₁B
    rw [← hy₁, ← Phi_eq_pt]; exact hsK
  intro b hb y hy hyy hbK
  obtain ⟨c', hc', y', hy', hc'K⟩ := hout
  have h1 : (K ∩ Phi '' A₁).Nonempty :=
    ⟨pt b y, hbK, ⟨(b, ⟨y, hy⟩), ⟨hb, hyy⟩, Phi_eq_pt _⟩⟩
  have h2 : (K ∩ Phi '' A₂).Nonempty :=
    ⟨pt c' y', hc'K, ⟨(c', ⟨y', hy'⟩), Or.inl hc', Phi_eq_pt _⟩⟩
  have := isPreconnected_closed_iff.mp hKc _ _ (isClosed_Phi_image hA₁c)
    (isClosed_Phi_image hA₂c) hcov h1 h2
  rw [hdisj] at this
  exact this.ne_empty rfl

/-- **Irreducibility at a good strand.** -/
theorem mem_of_good {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K) {s₁ s₂ : Organ}
    (hs₁ : s₁ ∈ K) (hs₂ : s₂ ∈ K) {c : Cs} (hc : Good c) (h₁ : F s₁ < lam c) (h₂ : lam c < F s₂)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : pt c y ∈ K := by
  by_contra hyK
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hyK
  set U : Set Cs := {b | |PP b - PP c| < δ ∧ |QQ b - QQ c| < δ ∧ lam b ∈ Ioo (F s₁) (F s₂)}
  have hUo : IsOpen U := by
    refine ((isOpen_lt ((continuous_PP.sub continuous_const).abs) continuous_const).inter
      ((isOpen_lt ((continuous_QQ.sub continuous_const).abs) continuous_const).inter
        (isOpen_Ioo.preimage continuous_lam)))
  have hcU : c ∈ U := ⟨by simpa using hδ, by simpa using hδ, h₁, h₂⟩
  obtain ⟨N, hN⟩ := exists_cyl_subset hUo hcU
  obtain ⟨s, hs⟩ := hc
  -- a cylinder of each parity
  have hpat : ∀ j, c (s + 3 * j + 3 - 3) = false ∧ c (s + 3 * j + 3 - 2) = true ∧
      c (s + 3 * j + 3 - 1) = true := by
    intro j
    refine ⟨?_, ?_, ?_⟩
    · rw [show s + 3 * j + 3 - 3 = s + 3 * j by omega]; exact (hs j).1
    · rw [show s + 3 * j + 3 - 2 = s + 3 * j + 1 by omega]; exact (hs j).2.1
    · rw [show s + 3 * j + 3 - 1 = s + 3 * j + 2 by omega]; exact (hs j).2.2
  have hpar : ∀ j, (Odd (s + 3 * j + 3 - 1) ↔ ¬ Odd (s + 3 * (j + 1) + 3 - 1)) := by
    intro j
    rw [show s + 3 * (j + 1) + 3 - 1 = (s + 3 * j + 3 - 1) + 3 by omega, Nat.odd_add]
    have : ¬ Even 3 := by decide
    tauto
  obtain ⟨n₁, n₂, hn₁N, hn₂N, hp₁, hp₂, ho₁, he₂⟩ : ∃ n₁ n₂, N ≤ n₁ ∧ N ≤ n₂ ∧
      (3 ≤ n₁ ∧ c (n₁ - 3) = false ∧ c (n₁ - 2) = true ∧ c (n₁ - 1) = true) ∧
      (3 ≤ n₂ ∧ c (n₂ - 3) = false ∧ c (n₂ - 2) = true ∧ c (n₂ - 1) = true) ∧
      Odd (n₁ - 1) ∧ ¬ Odd (n₂ - 1) := by
    by_cases hoN : Odd (s + 3 * N + 3 - 1)
    · exact ⟨s + 3 * N + 3, s + 3 * (N + 1) + 3, by omega, by omega,
        ⟨by omega, hpat N⟩, ⟨by omega, hpat (N + 1)⟩, hoN, (hpar N).mp hoN⟩
    · refine ⟨s + 3 * (N + 1) + 3, s + 3 * N + 3, by omega, by omega,
        ⟨by omega, hpat (N + 1)⟩, ⟨by omega, hpat N⟩, ?_, hoN⟩
      by_contra h; exact hoN ((hpar N).mpr h)
  have hmiss : ∀ n, N ≤ n → ∀ b ∈ cyl c n, pt b y ∉ K := by
    intro n hn b hb hbK
    have hbU := hN (cyl_anti c hn hb)
    apply hball _ hbK
    rw [Metric.mem_ball]
    exact (dist_pt_same_height hy).trans_lt (max_lt hbU.1 hbU.2.1)
  have hout : ∀ n, N ≤ n → ∃ c' ∉ cyl c n, ∃ y ∈ Icc (0 : ℝ) 1, pt c' y ∈ K := by
    intro n hn
    obtain ⟨c', y', hy', rfl⟩ := exists_pt s₂
    refine ⟨c', fun hc' => ?_, y', hy', hs₂⟩
    have := (hN (cyl_anti c hn hc')).2.2
    rw [F_pt] at this
    exact lt_irrefl _ this.2
  have htop := split_top hKc (isClosed_cyl c n₁) (isOpen_cyl c n₁) hy (hmiss n₁ hn₁N)
    (fun b hb b' hb' y₁ hy₁ y₂ hy₂ h => by
      have := cross_cyl hp₁.1 hp₁.2.1 hp₁.2.2.1 hp₁.2.2.2 hb hb' hy₁ hy₂ h
      rwa [if_pos ho₁] at this) (hout n₁ hn₁N)
  have hbot := split_bot hKc (isClosed_cyl c n₂) (isOpen_cyl c n₂) hy (hmiss n₂ hn₂N)
    (fun b hb b' hb' y₁ hy₁ y₂ hy₂ h => by
      have := cross_cyl hp₂.1 hp₂.2.1 hp₂.2.2.1 hp₂.2.2.2 hb hb' hy₁ hy₂ h
      rwa [if_neg he₂] at this) (hout n₂ hn₂N)
  -- the layer of `c` meets `K`
  have hIVT := (hKc.image F continuous_F.continuousOn).Icc_subset (mem_image_of_mem F hs₁)
    (mem_image_of_mem F hs₂) ⟨h₁.le, h₂.le⟩
  obtain ⟨p, hpK, hpF⟩ := hIVT
  obtain ⟨b, y', hy', rfl⟩ := exists_pt p
  rw [F_pt] at hpF
  have hbc : b = c := Good.lam_eq ⟨s, hs⟩ hpF
  subst hbc
  rcases le_total y' y with h | h
  · exact htop b (mem_cyl_self b n₁) y' hy' h hpK
  · exact hbot b (mem_cyl_self b n₂) y' hy' h hpK

/-- Good approximants. -/
def goodApprox (b : Cs) (N : ℕ) : Cs := fun k => if k < N then b k else decide ((k - N) % 3 ≠ 0)

theorem goodApprox_good (b : Cs) (N : ℕ) : Good (goodApprox b N) := by
  refine ⟨N, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [goodApprox, if_neg (by omega)]; exact decide_eq_false (by omega)
  · rw [goodApprox, if_neg (by omega)]; exact decide_eq_true (by omega)
  · rw [goodApprox, if_neg (by omega)]; exact decide_eq_true (by omega)

theorem tendsto_goodApprox (b : Cs) : Tendsto (goodApprox b) atTop (𝓝 b) := by
  rw [tendsto_pi_nhds]
  intro j
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  simp [goodApprox, hN]

/-- **Irreducibility**: a closed connected set meeting the layers `F s₁ < F s₂` contains every
point of every layer strictly between. -/
theorem mem_of_between {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K)
    {s₁ s₂ : Organ} (hs₁ : s₁ ∈ K) (hs₂ : s₂ ∈ K) {b : Cs} (h₁ : F s₁ < lam b)
    (h₂ : lam b < F s₂) (y : ℝ) : pt b y ∈ K := by
  have hy : ((projIcc 0 1 zero_le_one y : Icc (0 : ℝ) 1) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    (projIcc 0 1 zero_le_one y).2
  have hpt : pt b y = pt b (projIcc 0 1 zero_le_one y : Icc (0 : ℝ) 1) := by
    simp only [pt, projIcc_val]
  rw [hpt]
  have ht := tendsto_goodApprox b
  apply hK.mem_of_tendsto ((continuous_pt_param _).continuousAt.tendsto.comp ht)
  have hl := (continuous_lam.tendsto b).comp ht
  filter_upwards [hl (isOpen_Ioo.mem_nhds ⟨h₁, h₂⟩)] with N hN
  exact mem_of_good hK hKc hs₁ hs₂ (goodApprox_good b N) hN.1 hN.2 hy

/-- The same, for points. -/
theorem mem_of_F_between {K : Set Organ} (hK : IsClosed K) (hKc : IsPreconnected K)
    {s₁ s₂ : Organ} (hs₁ : s₁ ∈ K) (hs₂ : s₂ ∈ K) {p : Organ} (h₁ : F s₁ < F p)
    (h₂ : F p < F s₂) : p ∈ K := by
  obtain ⟨b, y, -, rfl⟩ := exists_pt p
  rw [F_pt] at h₁ h₂
  exact mem_of_between hK hKc hs₁ hs₂ h₁ h₂ y

end HPC.Plane.Org
