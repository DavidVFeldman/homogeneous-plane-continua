import HPC.Jones.Jones49COrder
import HPC.Plane.Tree7Star

/-!
# Batch 151, item A (part 3): continua crossing the square annulus

`Ecov P` maps the strip `r₁ ≤ y ≤ r₂` onto the square annulus `Ann P r₁ r₂` (sup metric) by
polar coordinates for the sup norm, `2π`-periodically. A continuum crossing the annulus that is
missed by another one has a continuous argument about `P` (`exists_log_cross`, by the component
criterion and the fact that the other continuum joins the inner square to the outer one), hence
lifts to a crossing set of the strip (`exists_lift`).

* `sector_two`: **two disjoint crossing continua cut the annulus into two pieces**, nonempty,
  disjoint and open in the annulus;
* `sector_cyclic`: **the cyclic order** — from infinitely many pairwise disjoint crossing continua
  a subsequence can be extracted in which each `k (g n)` (`n ≥ 1`) lies in a piece `V n` cut off by
  its two neighbours, missing all the other continua and every `V m` with `|n - m| ≥ 2`.

The order comes from the lifts (a monotone subsequence of the normalized lifts,
`exists_increasing_or_nonincreasing_subseq`), not from the points on the middle square.
-/

namespace HPC.Jones.Sector

open Set Topology Metric HPC.Plane

/-! ### The square annulus and its covering by the strip -/

section Annulus

open Complex

/-- The closed square annulus `r₁ ≤ d(z, P) ≤ r₂` (sup metric). -/
def Ann (P : ℝ × ℝ) (r₁ r₂ : ℝ) : Set (ℝ × ℝ) := {z | r₁ ≤ dist z P ∧ dist z P ≤ r₂}

/-- A continuum **crossing the annulus**: it lies in the annulus and meets both squares. -/
structure IsCrossA (P : ℝ × ℝ) (r₁ r₂ : ℝ) (K : Set (ℝ × ℝ)) : Prop where
  compact : IsCompact K
  conn : IsConnected K
  sub : K ⊆ Ann P r₁ r₂
  inner : ∃ z ∈ K, dist z P = r₁
  outer : ∃ z ∈ K, dist z P = r₂

/-- `max |cos θ| |sin θ|`. -/
noncomputable def mx (θ : ℝ) : ℝ := max |Real.cos θ| |Real.sin θ|

theorem mx_pos (θ : ℝ) : 0 < mx θ := by
  by_contra h
  push_neg at h
  have h1 : |Real.cos θ| ≤ 0 := (le_max_left _ _).trans h
  have h2 : |Real.sin θ| ≤ 0 := (le_max_right _ _).trans h
  have hc : Real.cos θ = 0 := abs_nonpos_iff.1 h1
  have hs : Real.sin θ = 0 := abs_nonpos_iff.1 h2
  have := Real.sin_sq_add_cos_sq θ
  rw [hc, hs] at this
  norm_num at this

theorem continuous_mx : Continuous mx := by
  unfold mx; fun_prop

/-- The covering map of the annulus by the strip: polar coordinates for the sup metric. -/
noncomputable def Ecov (P : ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (P.1 + x.2 * (Real.cos x.1 / mx x.1), P.2 + x.2 * (Real.sin x.1 / mx x.1))

theorem continuous_Ecov (P : ℝ × ℝ) : Continuous (Ecov P) := by
  unfold Ecov
  have h1 : Continuous fun x : ℝ × ℝ => Real.cos x.1 / mx x.1 :=
    (Real.continuous_cos.comp continuous_fst).div (continuous_mx.comp continuous_fst)
      fun x => (mx_pos _).ne'
  have h2 : Continuous fun x : ℝ × ℝ => Real.sin x.1 / mx x.1 :=
    (Real.continuous_sin.comp continuous_fst).div (continuous_mx.comp continuous_fst)
      fun x => (mx_pos _).ne'
  exact (continuous_const.add (continuous_snd.mul h1)).prodMk
    (continuous_const.add (continuous_snd.mul h2))

theorem dist_Ecov (P x : ℝ × ℝ) : dist (Ecov P x) P = |x.2| := by
  have hm := mx_pos x.1
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [Ecov, add_sub_cancel_left, abs_mul, abs_div, abs_of_pos hm]
  rw [← mul_max_of_nonneg _ _ (abs_nonneg _), max_div_div_right hm.le]
  rw [show max |Real.cos x.1| |Real.sin x.1| = mx x.1 from rfl, div_self hm.ne', mul_one]

theorem toCpx_Ecov (P x : ℝ × ℝ) :
    toCpx (Ecov P x) - toCpx P = ((x.2 / mx x.1 : ℝ) : ℂ) * exp (x.1 * I) := by
  apply Complex.ext
  · simp only [toCpx, Ecov, Complex.sub_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  · simp only [toCpx, Ecov, Complex.sub_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    ring

theorem Ecov_eq_of {P z : ℝ × ℝ} {r θ : ℝ} (hr : 0 < r)
    (h : toCpx z - toCpx P = (r : ℂ) * exp (θ * I)) : Ecov P (θ, dist z P) = z := by
  have h1 : z.1 - P.1 = r * Real.cos θ := by
    have := congrArg Complex.re h
    simpa [toCpx, Complex.exp_ofReal_mul_I_re] using this
  have h2 : z.2 - P.2 = r * Real.sin θ := by
    have := congrArg Complex.im h
    simpa [toCpx, Complex.exp_ofReal_mul_I_im] using this
  have hd : dist z P = r * mx θ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, h1, h2, abs_mul, abs_mul, abs_of_pos hr,
      ← mul_max_of_nonneg _ _ hr.le]
    rfl
  have hm := (mx_pos θ).ne'
  ext
  · simp only [Ecov, hd]; field_simp; linarith
  · simp only [Ecov, hd]; field_simp; linarith

theorem Ecov_sh (P x : ℝ × ℝ) (j : ℤ) : Ecov P (x.1 + 2 * Real.pi * j, x.2) = Ecov P x := by
  have hc : Real.cos (x.1 + 2 * Real.pi * j) = Real.cos x.1 := by
    rw [show 2 * Real.pi * (j : ℝ) = j * (2 * Real.pi) by ring]; exact Real.cos_add_int_mul_two_pi _ _
  have hs : Real.sin (x.1 + 2 * Real.pi * j) = Real.sin x.1 := by
    rw [show 2 * Real.pi * (j : ℝ) = j * (2 * Real.pi) by ring]; exact Real.sin_add_int_mul_two_pi _ _
  simp only [Ecov, mx, hc, hs]

theorem Ecov_eq_Ecov {P x y : ℝ × ℝ} (hx : 0 < x.2) (hy : 0 < y.2) (h : Ecov P x = Ecov P y) :
    y.2 = x.2 ∧ ∃ j : ℤ, y.1 = x.1 + 2 * Real.pi * j := by
  have h2 : y.2 = x.2 := by
    have := dist_Ecov P x
    rw [h, dist_Ecov, abs_of_pos hx, abs_of_pos hy] at this
    exact this
  refine ⟨h2, ?_⟩
  have hc := toCpx_Ecov P x
  rw [h, toCpx_Ecov] at hc
  have hn := congrArg norm hc
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs] at hn
  rw [abs_of_pos (div_pos hy (mx_pos _)), abs_of_pos (div_pos hx (mx_pos _))] at hn
  rw [hn] at hc
  have hne : ((x.2 / mx x.1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos hx (mx_pos _)).ne'
  have he := mul_left_cancel₀ hne hc
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

theorem Ecov_surj {P z : ℝ × ℝ} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (hz : z ∈ Ann P r₁ r₂) :
    ∃ x ∈ Strip r₁ r₂, Ecov P x = z := by
  set w := toCpx z - toCpx P
  have hw : w ≠ 0 := by
    intro h
    have : z = P := by
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp [w, toCpx] at h1 h2
      ext <;> linarith
    have h1 := hz.1
    rw [this, dist_self] at h1
    linarith
  refine ⟨(Complex.arg w, dist z P), hz, Ecov_eq_of (norm_pos_iff.2 hw) ?_⟩
  exact (Complex.norm_mul_exp_arg_mul_I w).symm

theorem Ecov_mem_ann {P x : ℝ × ℝ} {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (hx : x ∈ Strip r₁ r₂) :
    Ecov P x ∈ Ann P r₁ r₂ := by
  have := dist_Ecov P x
  rw [abs_of_nonneg (h0.trans hx.1)] at this
  exact ⟨this ▸ hx.1, this ▸ hx.2⟩

theorem Ecov_image_sh (P : ℝ × ℝ) (S : Set (ℝ × ℝ)) (j : ℤ) :
    Ecov P '' sh (2 * Real.pi * j) S = Ecov P '' S := by
  rw [sh, image_image]
  congr 1
  funext x
  exact Ecov_sh P x j

/-- `L` **lifts** `K`: a crossing set of the strip whose translates are exactly the preimage of
`K`, mapped injectively onto `K`. -/
structure IsLift (P : ℝ × ℝ) (r₁ r₂ : ℝ) (K L : Set (ℝ × ℝ)) : Prop where
  cross : IsCross r₁ r₂ L
  pre : ∀ x ∈ Strip r₁ r₂, Ecov P x ∈ K ↔ ∃ j : ℤ, x ∈ sh (2 * Real.pi * j) L
  inj : ∀ x ∈ L, ∀ y ∈ L, Ecov P x = Ecov P y → x = y

theorem IsLift.image_eq {P : ℝ × ℝ} {r₁ r₂ : ℝ} {K L : Set (ℝ × ℝ)} (h0 : 0 < r₁)
    (hL : IsLift P r₁ r₂ K L) (hK : K ⊆ Ann P r₁ r₂) : Ecov P '' L = K := by
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hL.pre x (hL.cross.sub hx)).2 ⟨0, by simpa [sh_zero] using hx⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Ecov_surj h0 (hK hz)
    obtain ⟨j, hj⟩ := (hL.pre x hx).1 hz
    rw [← Ecov_image_sh P L j]
    exact mem_image_of_mem _ hj

theorem IsLift.disjoint_sh {P : ℝ × ℝ} {r₁ r₂ : ℝ} {K L : Set (ℝ × ℝ)} (hL : IsLift P r₁ r₂ K L)
    {i j : ℤ} (hij : i ≠ j) : Disjoint (sh (2 * Real.pi * i) L) (sh (2 * Real.pi * j) L) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have huv : Ecov P u = Ecov P v := by
    rw [← Ecov_sh P u i, ← Ecov_sh P v j]
    exact congrArg (Ecov P) hvu.symm
  have := hL.inj u hu v hv huv
  subst this
  have := congrArg Prod.fst hvu
  simp only [add_right_inj, mul_eq_mul_left_iff, Int.cast_inj] at this
  rcases this with h | h
  · exact hij h.symm
  · exact absurd h (by positivity)

theorem Ecov_image_disjoint {P : ℝ × ℝ} {r₁ r₂ : ℝ} (h0 : 0 < r₁) {S S' : Set (ℝ × ℝ)}
    (hS : S ⊆ Strip r₁ r₂) (hS' : S' ⊆ Strip r₁ r₂)
    (h : ∀ j : ℤ, Disjoint S (sh (2 * Real.pi * j) S')) : Disjoint (Ecov P '' S) (Ecov P '' S') := by
  refine disjoint_left.2 ?_
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy⟩
  obtain ⟨h2, j, hj⟩ := Ecov_eq_Ecov (h0.trans_le (hS' hy').1) (h0.trans_le (hS hy).1) hyy
  refine disjoint_left.1 (h j) hy ⟨y', hy', ?_⟩
  ext
  · exact hj.symm
  · exact h2.symm

theorem Ecov_image_open {P : ℝ × ℝ} {r₁ r₂ : ℝ} (h0 : 0 < r₁) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ Strip r₁ r₂) (hopen : ∀ y ∈ S, ∃ η > 0, ball y η ∩ Strip r₁ r₂ ⊆ S) :
    ∀ z ∈ Ecov P '' S, ∃ η > 0, ball z η ∩ Ann P r₁ r₂ ⊆ Ecov P '' S := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨η, hη, hsub⟩ := hopen x hx
  set z := Ecov P x
  have hx2 : 0 < x.2 := h0.trans_le (hS hx).1
  set w₀ := toCpx z - toCpx P
  have hw₀ : w₀ = ((x.2 / mx x.1 : ℝ) : ℂ) * exp (x.1 * I) := toCpx_Ecov P x
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀]
    exact mul_ne_zero (by exact_mod_cast (div_pos hx2 (mx_pos _)).ne') (Complex.exp_ne_zero _)
  set f : ℝ × ℝ → ℝ := fun z' => Complex.arg ((toCpx z' - toCpx P) / w₀)
  have hf : ContinuousAt f z := by
    have h1 : (toCpx z - toCpx P) / w₀ ∈ slitPlane := by
      rw [div_self hw₀ne]; exact Complex.one_mem_slitPlane
    exact (Complex.continuousAt_arg h1).comp (f := fun z' => (toCpx z' - toCpx P) / w₀)
      ((continuous_toCpx.sub continuous_const).div_const _).continuousAt
  have hfz : f z = 0 := by simp only [f]; rw [div_self hw₀ne, Complex.arg_one]
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf η hη
  refine ⟨min δ η, lt_min hδ hη, fun z' hz' => ?_⟩
  have hz'1 : dist z' z < δ := lt_of_lt_of_le hz'.1 (min_le_left _ _)
  have hz'2 : dist z' z < η := lt_of_lt_of_le hz'.1 (min_le_right _ _)
  have hfz' : |f z'| < η := by
    have := hδf hz'1; rwa [hfz, Real.dist_eq, sub_zero] at this
  set w' := toCpx z' - toCpx P
  have hw'ne : w' ≠ 0 := by
    intro h
    have : z' = P := by
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp [w', toCpx] at h1 h2
      ext <;> linarith
    have := hz'.2.1
    rw [‹z' = P›, dist_self] at this
    linarith
  set x' : ℝ × ℝ := (x.1 + f z', dist z' P)
  have hEx' : Ecov P x' = z' := by
    have hr : 0 < ‖w' / w₀‖ * (x.2 / mx x.1) :=
      mul_pos (norm_pos_iff.2 (div_ne_zero hw'ne hw₀ne)) (div_pos hx2 (mx_pos _))
    refine Ecov_eq_of hr ?_
    have e2 : ((‖w' / w₀‖ : ℝ) : ℂ) * exp (↑(f z') * I) = w' / w₀ :=
      Complex.norm_mul_exp_arg_mul_I _
    have hexp : exp (↑(x.1 + f z') * I) = exp (↑(f z') * I) * exp (↑x.1 * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    calc w' = (w' / w₀) * w₀ := (div_mul_cancel₀ _ hw₀ne).symm
      _ = (((‖w' / w₀‖ : ℝ) : ℂ) * exp (↑(f z') * I)) *
          (((x.2 / mx x.1 : ℝ) : ℂ) * exp (↑x.1 * I)) := by rw [e2, ← hw₀]
      _ = _ := by push_cast; ring
  have hx'S : x' ∈ S := by
    refine hsub ⟨?_, hz'.2⟩
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt ?_ ?_
    · simpa [x'] using hfz'
    · have hdx : dist z P = x.2 := by rw [dist_Ecov, abs_of_pos hx2]
      have : |dist z' P - x.2| ≤ dist z' z := by
        rw [← hdx]; exact abs_dist_sub_le z' z P
      simp only [x']
      linarith
  exact ⟨x', hx'S, hEx'⟩

end Annulus

/-! ### Lifting a crossing continuum to the strip -/

section LiftSec

open Complex

variable {P : ℝ × ℝ} {r₁ r₂ : ℝ}

theorem dist_lineMap (P a : ℝ × ℝ) {t : ℝ} (ht : 0 ≤ t) : dist (P + t • (a - P)) P = t * dist a P := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht, dist_eq_norm]

/-- **A crossing continuum has a continuous argument about the centre**, provided another crossing
continuum misses it (so it does not separate the centre from infinity). -/
theorem exists_log_cross (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (hK' : IsCrossA P r₁ r₂ K') (hd : Disjoint K K') :
    ∃ g : ℝ × ℝ → ℂ, ContinuousOn g K ∧ ∀ z ∈ K, exp (g z) = toCpx z - toCpx P := by
  obtain ⟨a, haK', ha⟩ := hK'.inner
  obtain ⟨b, hbK', hb⟩ := hK'.outer
  set Q : ℝ × ℝ := (P.1 - 3 * r₂, P.2)
  have hr₂ : 0 < r₂ := h0.trans h12
  have hQ : dist Q P = 3 * r₂ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Q, sub_sub_cancel_left, sub_self, abs_zero, abs_neg]
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
  have hnotK : ∀ z, dist z P < r₁ ∨ r₂ < dist z P → z ∉ K := by
    intro z hz hzK
    have := hK.sub hzK
    rcases hz with h | h
    · linarith [this.1]
    · linarith [this.2]
  set b' : ℝ × ℝ := P + (2 : ℝ) • (b - P)
  set Z := segment ℝ P a ∪ K' ∪ segment ℝ b b' ∪ (closedBall P r₂)ᶜ
  have hb' : dist b' P = 2 * r₂ := by rw [dist_lineMap P b (by norm_num), hb]
  have hZK : Z ⊆ Kᶜ := by
    rintro z (((hz | hz) | hz) | hz)
    · rw [segment_eq_image'] at hz
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
      rcases ht1.lt_or_eq with ht1 | rfl
      · refine hnotK _ (Or.inl ?_)
        rw [dist_lineMap P a ht0, ha]
        nlinarith
      · simp only [one_smul, add_sub_cancel]
        exact fun h => disjoint_left.1 hd h haK'
    · exact fun h => disjoint_left.1 hd h hz
    · rw [segment_eq_image'] at hz
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
      have e : b + t • (b' - b) = P + (1 + t) • (b - P) := by
        simp only [b']
        ext <;> simp <;> ring
      rcases ht0.lt_or_eq with ht0 | rfl
      · refine hnotK _ (Or.inr ?_)
        show r₂ < dist (b + t • (b' - b)) P
        rw [e, dist_lineMap P b (by linarith), hb]
        nlinarith
      · simp only [zero_smul, add_zero]
        exact fun h => disjoint_left.1 hd h hbK'
    · refine hnotK z (Or.inr ?_)
      simpa using hz
  have hZ : IsPreconnected Z := by
    have h1 : IsPreconnected (segment ℝ P a ∪ K') :=
      (convex_segment P a).isPreconnected.union a (right_mem_segment ℝ P a) haK'
        hK'.conn.isPreconnected
    have h2 : IsPreconnected (segment ℝ P a ∪ K' ∪ segment ℝ b b') :=
      h1.union b (Or.inr hbK') (left_mem_segment ℝ b b') (convex_segment b b').isPreconnected
    refine h2.union b' (Or.inr (right_mem_segment ℝ b b')) ?_
      (HPC.Plane.isConnected_compl_closedBall_pt P r₂).1.isPreconnected
    show ¬ dist b' P ≤ r₂
    rw [hb']; linarith
  have hPZ : P ∈ Z := Or.inl (Or.inl (Or.inl (left_mem_segment ℝ P a)))
  have hQZ : Q ∈ Z := Or.inr (show ¬ dist Q P ≤ r₂ by rw [hQ]; linarith)
  have hPK : P ∉ K := hZK hPZ
  obtain ⟨g₁, hg₁c, hg₁⟩ := HPC.Moore.exists_log_of_mem_component hK.compact.isClosed hPK
    (hZ.subset_connectedComponentIn hPZ hZK hQZ)
  have hre : ∀ z ∈ K, 0 < (toCpx z - toCpx Q).re := by
    intro z hz
    have h1 : |z.1 - P.1| ≤ dist z P := by
      rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
    have h2 := (hK.sub hz).2
    simp only [toCpx, Complex.sub_re, Q]
    linarith [neg_abs_le (z.1 - P.1)]
  refine ⟨fun z => g₁ z + Complex.log (toCpx z - toCpx Q), ?_, fun z hz => ?_⟩
  · refine hg₁c.add (ContinuousOn.clog ?_ fun z hz => Complex.mem_slitPlane_iff.2 (Or.inl (hre z hz)))
    exact (continuous_toCpx.sub continuous_const).continuousOn
  · have hne : toCpx z - toCpx Q ≠ 0 := fun h => by
      have := hre z hz; rw [h] at this; simp at this
    simp only [Complex.exp_add, hg₁ z hz, Complex.exp_log hne]
    exact div_mul_cancel₀ _ hne

/-- **Lifting.** A crossing continuum missed by another crossing continuum lifts to the strip. -/
theorem exists_lift (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (hK' : IsCrossA P r₁ r₂ K') (hd : Disjoint K K') :
    ∃ L, IsLift P r₁ r₂ K L := by
  obtain ⟨g, hgc, hge⟩ := exists_log_cross h0 h12 hK hK' hd
  set ℓ : ℝ × ℝ → ℝ × ℝ := fun z => ((g z).im, dist z P)
  have hℓc : ContinuousOn ℓ K :=
    (Complex.continuous_im.comp_continuousOn hgc).prodMk (continuous_id.dist continuous_const).continuousOn
  have hEℓ : ∀ z ∈ K, Ecov P (ℓ z) = z := by
    intro z hz
    refine Ecov_eq_of (r := Real.exp (g z).re) (Real.exp_pos _) ?_
    rw [← hge z hz]
    conv_lhs => rw [← Complex.re_add_im (g z)]
    rw [Complex.exp_add, Complex.ofReal_exp]
  have hℓs : ∀ z ∈ K, ℓ z ∈ Strip r₁ r₂ := fun z hz => hK.sub hz
  refine ⟨ℓ '' K, ⟨hK.compact.image_of_continuousOn hℓc, hK.conn.image _ hℓc, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩; exact hℓs z hz
  · obtain ⟨z, hz, hz1⟩ := hK.inner; exact ⟨ℓ z, mem_image_of_mem _ hz, hz1⟩
  · obtain ⟨z, hz, hz1⟩ := hK.outer; exact ⟨ℓ z, mem_image_of_mem _ hz, hz1⟩
  · intro x hx
    constructor
    · intro hxK
      set z := Ecov P x
      have h := hEℓ z hxK
      obtain ⟨h2, j, hj⟩ := Ecov_eq_Ecov (h0.trans_le (hℓs z hxK).1) (h0.trans_le hx.1)
        (h.trans rfl)
      refine ⟨j, ℓ z, mem_image_of_mem _ hxK, ?_⟩
      ext
      · exact hj.symm
      · exact h2.symm
    · rintro ⟨j, _, ⟨z, hz, rfl⟩, rfl⟩
      rw [Ecov_sh P (ℓ z) j, hEℓ z hz]
      exact hz
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ h
    rw [hEℓ z hz, hEℓ z' hz'] at h
    rw [h]

end LiftSec

/-! ### Two crossing continua cut the annulus into two pieces -/

section TwoPiece

variable {P : ℝ × ℝ} {r₁ r₂ : ℝ}

/-- A subset of the annulus open in the annulus. -/
def RelOpenAnn (P : ℝ × ℝ) (r₁ r₂ : ℝ) (V : Set (ℝ × ℝ)) : Prop :=
  ∀ z ∈ V, ∃ η > 0, ball z η ∩ Ann P r₁ r₂ ⊆ V

theorem sh_sh_int (L : Set (ℝ × ℝ)) (i j : ℤ) :
    sh (2 * Real.pi * j) (sh (2 * Real.pi * i) L) = sh (2 * Real.pi * (i + j : ℤ)) L := by
  rw [sh_sh]; congr 1; push_cast; ring

theorem sh_two_pi (L : Set (ℝ × ℝ)) : sh (2 * Real.pi) L = sh (2 * Real.pi * (1 : ℤ)) L := by
  simp

theorem IsLift.sh {K L : Set (ℝ × ℝ)} (hL : IsLift P r₁ r₂ K L) (j : ℤ) :
    IsLift P r₁ r₂ K (sh (2 * Real.pi * j) L) where
  cross := hL.cross.sh _
  pre := by
    intro x hx
    rw [hL.pre x hx]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i - j, ?_⟩
      rw [sh_sh_int]; simpa using hi
    · rintro ⟨i, hi⟩
      rw [sh_sh_int] at hi
      exact ⟨_, hi⟩
  inj := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ h
    have h' : Ecov P u = Ecov P v := by
      rw [← Ecov_sh P u j, ← Ecov_sh P v j]; exact h
    rw [hL.inj u hu v hv h']

/-- All translates of two lifts. -/
def fam2 (A B : Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {X | ∃ j : ℤ, X = sh (2 * Real.pi * j) A ∨ X = sh (2 * Real.pi * j) B}

theorem liftFam_fam2 {K K' A B : Set (ℝ × ℝ)} (hA : IsLift P r₁ r₂ K A) (hB : IsLift P r₁ r₂ K' B)
    (hd : Disjoint K K') : LiftFam r₁ r₂ (2 * Real.pi) (fam2 A B) := by
  have hcross : ∀ X ∈ fam2 A B, IsCross r₁ r₂ X := by
    rintro X ⟨j, rfl | rfl⟩
    · exact hA.cross.sh _
    · exact hB.cross.sh _
  have hAB : ∀ i j : ℤ, Disjoint (sh (2 * Real.pi * i) A) (sh (2 * Real.pi * j) B) := by
    intro i j
    refine disjoint_left.2 fun x hxA hxB => ?_
    have hxs : x ∈ Strip r₁ r₂ := (hA.cross.sh _).sub hxA
    exact disjoint_left.1 hd ((hA.pre x hxs).2 ⟨i, hxA⟩) ((hB.pre x hxs).2 ⟨j, hxB⟩)
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rintro X ⟨i, rfl | rfl⟩ Y ⟨j, rfl | rfl⟩ hne
    · exact hA.disjoint_sh fun h => hne (h ▸ rfl)
    · exact hAB i j
    · exact (hAB j i).symm
    · exact hB.disjoint_sh fun h => hne (h ▸ rfl)
  · rintro X ⟨i, rfl | rfl⟩ j
    · exact ⟨i + j, Or.inl (sh_sh_int A i j)⟩
    · exact ⟨i + j, Or.inr (sh_sh_int B i j)⟩
  · rintro X hX j hj heq
    obtain ⟨z, hz⟩ := (hcross X hX).conn.nonempty
    obtain ⟨i, rfl | rfl⟩ := hX
    · rw [sh_sh_int] at heq
      have := hA.disjoint_sh (i := i + j) (j := i) (by omega)
      rw [heq] at this
      exact disjoint_left.1 this hz hz
    · rw [sh_sh_int] at heq
      have := hB.disjoint_sh (i := i + j) (j := i) (by omega)
      rw [heq] at this
      exact disjoint_left.1 this hz hz

theorem LiftFam.le_shift_mono {a b T : ℝ} {F : Set (Set (ℝ × ℝ))} (hF : LiftFam a b T F)
    (hab : a < b) (hT : 0 < T) {L : Set (ℝ × ℝ)} (hL : L ∈ F) {i j : ℤ} (hij : i ≤ j) :
    PrecLe a b (sh (T * i) L) (sh (T * j) L) := by
  have h := hF.le_shift_nonneg hab hT (hF.shift L hL i) (j := j - i) (by omega)
  rwa [sh_sh, show T * (i : ℝ) + T * ((j - i : ℤ) : ℝ) = T * j by push_cast; ring] at h

theorem mem_fam2_A {A B : Set (ℝ × ℝ)} (j : ℤ) : sh (2 * Real.pi * j) A ∈ fam2 A B := ⟨j, Or.inl rfl⟩
theorem mem_fam2_B {A B : Set (ℝ × ℝ)} (j : ℤ) : sh (2 * Real.pi * j) B ∈ fam2 A B := ⟨j, Or.inr rfl⟩

theorem self_mem_fam2_A {A B : Set (ℝ × ℝ)} : A ∈ fam2 A B := ⟨0, Or.inl (by simp [sh_zero])⟩
theorem self_mem_fam2_B {A B : Set (ℝ × ℝ)} : B ∈ fam2 A B := ⟨0, Or.inr (by simp [sh_zero])⟩

/-- **Two pieces, in lifted form.** For lifts `A < B < A + 2π` of disjoint crossing continua `K`,
`K'`, the images of the sectors `(A, B)` and `(B, A + 2π)` are nonempty, disjoint, open in the
annulus, and cover the annulus off `K ∪ K'`. -/
theorem two_piece_lift (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' A B : Set (ℝ × ℝ)}
    (hA : IsLift P r₁ r₂ K A) (hB : IsLift P r₁ r₂ K' B) (hd : Disjoint K K')
    (h1 : Prec r₁ r₂ A B) (h2 : Prec r₁ r₂ B (sh (2 * Real.pi) A)) :
    (Ecov P '' Sec r₁ r₂ A B).Nonempty ∧ (Ecov P '' Sec r₁ r₂ B (sh (2 * Real.pi) A)).Nonempty ∧
      Disjoint (Ecov P '' Sec r₁ r₂ A B) (Ecov P '' Sec r₁ r₂ B (sh (2 * Real.pi) A)) ∧
      Ecov P '' Sec r₁ r₂ A B ∪ Ecov P '' Sec r₁ r₂ B (sh (2 * Real.pi) A) =
        Ann P r₁ r₂ \ (K ∪ K') ∧
      RelOpenAnn P r₁ r₂ (Ecov P '' Sec r₁ r₂ A B) ∧
      RelOpenAnn P r₁ r₂ (Ecov P '' Sec r₁ r₂ B (sh (2 * Real.pi) A)) := by
  have hF := liftFam_fam2 hA hB hd
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hAF : A ∈ fam2 A B := self_mem_fam2_A
  have hBF : B ∈ fam2 A B := self_mem_fam2_B
  have hA1F : sh (2 * Real.pi) A ∈ fam2 A B := by rw [sh_two_pi]; exact mem_fam2_A 1
  have hAc := hA.cross
  have hBc := hB.cross
  have hA1c := hA.cross.sh (2 * Real.pi)
  -- every translate lies weakly outside each sector
  have hout1 : ∀ X ∈ fam2 A B, ∀ j : ℤ, (X = sh (2 * Real.pi * j) A ∨
      X = sh (2 * Real.pi * j) B) → PrecLe r₁ r₂ X A ∨ PrecLe r₁ r₂ B X := by
    intro X hX j hj
    rcases hj with rfl | rfl
    · rcases le_or_gt j 0 with hj | hj
      · left; exact hF.shift_le_nonpos h12 hT hAF hj
      · right
        refine Or.inr (hF.lt_of_lt_of_le h12 hBF hA1F h2 ?_)
        rw [sh_two_pi]
        exact hF.le_shift_mono h12 hT hAF (by omega)
    · rcases le_or_gt 0 j with hj | hj
      · right; exact hF.le_shift_nonneg h12 hT hBF hj
      · left
        have hm : Prec r₁ r₂ (sh (2 * Real.pi * (-1 : ℤ)) B) A := by
          have := (hF.prec_sh_iff' hBF (2 * Real.pi * (-1 : ℤ))).2 h2
          rwa [sh_sh, show 2 * Real.pi + 2 * Real.pi * ((-1 : ℤ) : ℝ) = 0 by push_cast; ring,
            sh_zero] at this
        exact Or.inr (hF.lt_of_le_of_lt h12 (mem_fam2_B j) (mem_fam2_B (-1))
          (hF.le_shift_mono h12 hT hBF (by omega)) hm)
  have hout2 : ∀ X ∈ fam2 A B, ∀ j : ℤ, (X = sh (2 * Real.pi * j) A ∨
      X = sh (2 * Real.pi * j) B) → PrecLe r₁ r₂ X B ∨ PrecLe r₁ r₂ (sh (2 * Real.pi) A) X := by
    intro X hX j hj
    rcases hj with rfl | rfl
    · rcases le_or_gt j 0 with hj | hj
      · left
        exact Or.inr (hF.lt_of_le_of_lt h12 (mem_fam2_A j) hAF (hF.shift_le_nonpos h12 hT hAF hj) h1)
      · right
        rw [sh_two_pi]
        exact hF.le_shift_mono h12 hT hAF (by omega)
    · rcases le_or_gt j 0 with hj | hj
      · left; exact hF.shift_le_nonpos h12 hT hBF hj
      · right
        have hm : Prec r₁ r₂ (sh (2 * Real.pi) A) (sh (2 * Real.pi) B) :=
          (hF.prec_sh_iff' hAF _).2 h1
        refine Or.inr (hF.lt_of_lt_of_le h12 hA1F (by rw [sh_two_pi]; exact mem_fam2_B 1) hm ?_)
        rw [sh_two_pi]
        exact hF.le_shift_mono h12 hT hBF (by omega)
  refine ⟨(hF.sec_nonempty h12 hAF hBF h1).image _, (hF.sec_nonempty h12 hBF hA1F h2).image _,
    ?_, ?_, ?_, ?_⟩
  · refine Ecov_image_disjoint h0 sec_subset sec_subset fun j => ?_
    exact hF.sec_disjoint h12 hT hAF hBF hBF hA1F (Or.inl rfl) (Or.inl rfl) j
  · apply subset_antisymm
    · rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨Ecov_mem_ann h0.le (sec_subset hy), ?_⟩
        rintro (hK | hK)
        · obtain ⟨j, hj⟩ := (hA.pre y (sec_subset hy)).1 hK
          have hX := mem_fam2_A (A := A) (B := B) j
          exact disjoint_left.1 (hF.sec_disjoint_mem h12 hAF hX (hout1 _ hX j (Or.inl rfl)))
            hy hj
        · obtain ⟨j, hj⟩ := (hB.pre y (sec_subset hy)).1 hK
          have hX := mem_fam2_B (A := A) (B := B) j
          exact disjoint_left.1 (hF.sec_disjoint_mem h12 hAF hX (hout1 _ hX j (Or.inr rfl)))
            hy hj
      · refine ⟨Ecov_mem_ann h0.le (sec_subset hy), ?_⟩
        rintro (hK | hK)
        · obtain ⟨j, hj⟩ := (hA.pre y (sec_subset hy)).1 hK
          have hX := mem_fam2_A (A := A) (B := B) j
          exact disjoint_left.1 (hF.sec_disjoint_mem h12 hBF hX (hout2 _ hX j (Or.inl rfl)))
            hy hj
        · obtain ⟨j, hj⟩ := (hB.pre y (sec_subset hy)).1 hK
          have hX := mem_fam2_B (A := A) (B := B) j
          exact disjoint_left.1 (hF.sec_disjoint_mem h12 hBF hX (hout2 _ hX j (Or.inr rfl)))
            hy hj
    · rintro z ⟨hz, hzK⟩
      obtain ⟨y, hy, rfl⟩ := Ecov_surj h0 hz
      have hyA : ∀ j : ℤ, y ∉ sh (2 * Real.pi * j) A := fun j hj =>
        hzK (Or.inl ((hA.pre y hy).2 ⟨j, hj⟩))
      have hyB : ∀ j : ℤ, y ∉ sh (2 * Real.pi * j) B := fun j hj =>
        hzK (Or.inr ((hB.pre y hy).2 ⟨j, hj⟩))
      obtain ⟨j, hj | hj⟩ := hF.sec_cover h12 hT hAF hBF hy hyA hyB
      · left; rw [← Ecov_image_sh P _ j]; exact mem_image_of_mem _ hj
      · right; rw [← Ecov_image_sh P _ j]; exact mem_image_of_mem _ hj
  · exact Ecov_image_open h0 sec_subset fun y hy =>
      sec_open_rel hAc.compact.isClosed hBc.compact.isClosed hy
  · exact Ecov_image_open h0 sec_subset fun y hy =>
      sec_open_rel hBc.compact.isClosed hA1c.compact.isClosed hy

/-- Some translate of a lift of `K'` lies between a lift `A` of `K` and `A + 2π`. -/
theorem exists_between_lift (h12 : r₁ < r₂) {K K' A B : Set (ℝ × ℝ)} (hA : IsLift P r₁ r₂ K A)
    (hB : IsLift P r₁ r₂ K' B) (hd : Disjoint K K') :
    ∃ j : ℤ, Prec r₁ r₂ A (sh (2 * Real.pi * j) B) ∧
      Prec r₁ r₂ (sh (2 * Real.pi * j) B) (sh (2 * Real.pi) A) := by
  classical
  have hF := liftFam_fam2 hA hB hd
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hAF : A ∈ fam2 A B := self_mem_fam2_A
  have hne : ∀ j : ℤ, sh (2 * Real.pi * j) B ≠ A := by
    intro j h
    obtain ⟨z, hz⟩ := hA.cross.conn.nonempty
    have := hF.disj _ hAF _ (mem_fam2_B j)
    have hd' : Disjoint (sh (2 * Real.pi * (0 : ℤ)) A) (sh (2 * Real.pi * j) B) := by
      refine disjoint_left.2 fun x hxA hxB => ?_
      have hxs : x ∈ Strip r₁ r₂ := (hA.cross.sh _).sub hxA
      exact disjoint_left.1 hd ((hA.pre x hxs).2 ⟨0, hxA⟩) ((hB.pre x hxs).2 ⟨j, hxB⟩)
    simp only [Int.cast_zero, mul_zero, sh_zero] at hd'
    rw [h] at hd'
    exact disjoint_left.1 hd' hz hz
  obtain ⟨M₁, hM₁⟩ := (hA.cross.compact.image continuous_fst).isBounded.bddBelow
  obtain ⟨M₂, hM₂⟩ := (hA.cross.compact.image continuous_fst).isBounded.bddAbove
  obtain ⟨N₁, hN₁⟩ := (hB.cross.compact.image continuous_fst).isBounded.bddBelow
  obtain ⟨w, hw⟩ := hB.cross.conn.nonempty
  set S : ℤ → Prop := fun j => Prec r₁ r₂ A (sh (2 * Real.pi * j) B)
  have hbdd : ∃ N : ℤ, ∀ j, S j → N ≤ j := by
    refine ⟨⌊(M₁ - w.1) / (2 * Real.pi)⌋, fun j hj => ?_⟩
    obtain ⟨z, hz, hzle⟩ := prec_min h12 hA.cross hj (w.1 + 2 * Real.pi * j, w.2)
      ⟨w, hw, rfl⟩
    have := hM₁ (mem_image_of_mem Prod.fst hz)
    have h1 : (M₁ - w.1) / (2 * Real.pi) ≤ j := by
      rw [div_le_iff₀ hT]; simp only at hzle; linarith
    exact Int.floor_le_iff.2 (by exact_mod_cast h1.trans_lt (lt_add_one _))
  have hinh : ∃ j, S j := by
    by_contra hcon
    push_neg at hcon
    set j := ⌈(M₂ - N₁) / (2 * Real.pi)⌉ + 1
    have hp := (hF.total hAF (mem_fam2_B j) (hne j).symm).resolve_left (hcon j)
    obtain ⟨z, hz⟩ := hA.cross.conn.nonempty
    obtain ⟨_, ⟨u, hu, rfl⟩, hle⟩ := prec_min h12 (hF.cross _ (mem_fam2_B j)) hp z hz
    have h1 := hM₂ (mem_image_of_mem Prod.fst hz)
    have h2 := hN₁ (mem_image_of_mem Prod.fst hu)
    have h3 : (M₂ - N₁) / (2 * Real.pi) < j := by
      simp only [j]; push_cast; linarith [Int.le_ceil ((M₂ - N₁) / (2 * Real.pi))]
    rw [div_lt_iff₀ hT] at h3
    simp only at hle h1 h2
    linarith
  obtain ⟨j₁, hj₁, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨j₁, hj₁, ?_⟩
  have hnot : ¬ S (j₁ - 1) := fun h => by have := hmin _ h; omega
  have hp := (hF.total hAF (mem_fam2_B (j₁ - 1)) (hne _).symm).resolve_left hnot
  have := (hF.prec_sh_iff' (mem_fam2_B (j₁ - 1)) (2 * Real.pi)).2 hp
  rwa [sh_sh, show 2 * Real.pi * ((j₁ - 1 : ℤ) : ℝ) + 2 * Real.pi = 2 * Real.pi * j₁ by
    push_cast; ring] at this

end TwoPiece

/-! ### Infinitely many crossing continua: the cyclic order -/

section Cyclic

variable {P : ℝ × ℝ} {r₁ r₂ : ℝ}

/-- All translates of a sequence of lifts. -/
def famSeq (L : ℕ → Set (ℝ × ℝ)) : Set (Set (ℝ × ℝ)) :=
  {X | ∃ n : ℕ, ∃ j : ℤ, X = sh (2 * Real.pi * j) (L n)}

theorem liftFam_famSeq {k L : ℕ → Set (ℝ × ℝ)} (hL : ∀ n, IsLift P r₁ r₂ (k n) (L n))
    (hdisj : Pairwise fun m n => Disjoint (k m) (k n)) :
    LiftFam r₁ r₂ (2 * Real.pi) (famSeq L) := by
  have hcross : ∀ X ∈ famSeq L, IsCross r₁ r₂ X := by
    rintro X ⟨n, j, rfl⟩; exact (hL n).cross.sh _
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rintro X ⟨n, i, rfl⟩ Y ⟨m, j, rfl⟩ hne
    by_cases hnm : n = m
    · subst hnm
      exact (hL n).disjoint_sh fun h => hne (h ▸ rfl)
    · refine disjoint_left.2 fun x hx hy => ?_
      have hxs : x ∈ Strip r₁ r₂ := ((hL n).cross.sh _).sub hx
      exact disjoint_left.1 (hdisj hnm) (((hL n).pre x hxs).2 ⟨i, hx⟩)
        (((hL m).pre x hxs).2 ⟨j, hy⟩)
  · rintro X ⟨n, i, rfl⟩ j
    exact ⟨n, i + j, sh_sh_int _ i j⟩
  · rintro X hX j hj heq
    obtain ⟨z, hz⟩ := (hcross X hX).conn.nonempty
    obtain ⟨n, i, rfl⟩ := hX
    rw [sh_sh_int] at heq
    have := (hL n).disjoint_sh (i := i + j) (j := i) (by omega)
    rw [heq] at this
    exact disjoint_left.1 this hz hz

theorem mem_famSeq {L : ℕ → Set (ℝ × ℝ)} (n : ℕ) (j : ℤ) :
    sh (2 * Real.pi * j) (L n) ∈ famSeq L := ⟨n, j, rfl⟩

theorem self_mem_famSeq {L : ℕ → Set (ℝ × ℝ)} (n : ℕ) : L n ∈ famSeq L :=
  ⟨n, 0, by simp [sh_zero]⟩

theorem sh_two_pi_mem_famSeq {L : ℕ → Set (ℝ × ℝ)} (n : ℕ) :
    sh (2 * Real.pi) (L n) ∈ famSeq L := by
  rw [sh_two_pi]; exact mem_famSeq n 1

/-- A normalized lift: its leftmost points have first coordinate in `[0, 2π)`. -/
theorem exists_normalized_lift (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (hK' : IsCrossA P r₁ r₂ K') (hd : Disjoint K K') :
    ∃ L, IsLift P r₁ r₂ K L ∧ (∀ z ∈ L, 0 ≤ z.1) ∧ ∃ z ∈ L, z.1 < 2 * Real.pi := by
  obtain ⟨L₀, hL₀⟩ := exists_lift h0 h12 hK hK' hd
  obtain ⟨w, hw, hmin⟩ := hL₀.cross.compact.exists_isMinOn hL₀.cross.conn.nonempty
    continuous_fst.continuousOn
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  set j : ℤ := -⌊w.1 / (2 * Real.pi)⌋
  have hfl := Int.floor_le (w.1 / (2 * Real.pi))
  have hlt := Int.lt_floor_add_one (w.1 / (2 * Real.pi))
  have e1 : (2 * Real.pi) * ⌊w.1 / (2 * Real.pi)⌋ ≤ w.1 := by
    rw [le_div_iff₀ hT] at hfl; linarith
  have e2 : w.1 < (2 * Real.pi) * (⌊w.1 / (2 * Real.pi)⌋ + 1) := by
    rw [div_lt_iff₀ hT] at hlt; linarith
  refine ⟨sh (2 * Real.pi * j) L₀, hL₀.sh j, ?_, ⟨_, mem_image_of_mem _ hw, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    have : w.1 ≤ z.1 := hmin hz
    simp only [j]; push_cast; linarith
  · simp only [j]; push_cast; linarith

/-- A relatively open subset of the annulus is the trace of an open set. -/
theorem exists_open_of_relOpenAnn {V : Set (ℝ × ℝ)} (hV : RelOpenAnn P r₁ r₂ V)
    (hVs : V ⊆ Ann P r₁ r₂) : ∃ U, IsOpen U ∧ U ∩ Ann P r₁ r₂ = V := by
  choose! η hη hsub using hV
  refine ⟨⋃ z ∈ V, ball z (η z), isOpen_biUnion fun z _ => isOpen_ball, ?_⟩
  apply subset_antisymm
  · rintro w ⟨hw, hwA⟩
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 hw
    exact hsub z hz ⟨hwz, hwA⟩
  · intro z hz
    exact ⟨mem_iUnion₂.2 ⟨z, hz, mem_ball_self (hη z hz)⟩, hVs hz⟩

/-- A preconnected set covered by two disjoint relatively open pieces lies in one of them. -/
theorem preconnected_sub_piece {V W C : Set (ℝ × ℝ)} (hV : RelOpenAnn P r₁ r₂ V)
    (hW : RelOpenAnn P r₁ r₂ W) (hVs : V ⊆ Ann P r₁ r₂) (hWs : W ⊆ Ann P r₁ r₂)
    (hVW : Disjoint V W) (hC : IsPreconnected C) (hCs : C ⊆ V ∪ W) (hne : (C ∩ V).Nonempty) :
    C ⊆ V := by
  obtain ⟨U₁, hU₁, e₁⟩ := exists_open_of_relOpenAnn hV hVs
  obtain ⟨U₂, hU₂, e₂⟩ := exists_open_of_relOpenAnn hW hWs
  have hCA : C ⊆ Ann P r₁ r₂ := hCs.trans (union_subset hVs hWs)
  rcases isPreconnected_iff_subset_of_disjoint.1 hC U₁ U₂ hU₁ hU₂ (fun z hz => by
      rcases hCs hz with h | h
      · exact Or.inl (e₁.symm ▸ h |>.1)
      · exact Or.inr (e₂.symm ▸ h |>.1))
    (by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hzC hz1 hz2
      have h1 : z ∈ V := e₁ ▸ ⟨hz1, hCA hzC⟩
      have h2 : z ∈ W := e₂ ▸ ⟨hz2, hCA hzC⟩
      exact disjoint_left.1 hVW h1 h2) with h | h
  · intro z hz
    exact e₁ ▸ ⟨h hz, hCA hz⟩
  · exfalso
    obtain ⟨z, hzC, hzV⟩ := hne
    have : z ∈ W := e₂ ▸ ⟨h hzC, hCA hzC⟩
    exact disjoint_left.1 hVW hzV this

/-- The sector data for one index: the two neighbours `A`, `B` of `X` in the order. -/
theorem sector_props (h0 : 0 < r₁) (h12 : r₁ < r₂) {k L : ℕ → Set (ℝ × ℝ)}
    (hL : ∀ n, IsLift P r₁ r₂ (k n) (L n)) (hk : ∀ n, k n ⊆ Ann P r₁ r₂)
    (hdisj : Pairwise fun m n => Disjoint (k m) (k n))
    (hper : ∀ m n, Prec r₁ r₂ (L m) (sh (2 * Real.pi) (L n)))
    {a b x : ℕ} (hax : Prec r₁ r₂ (L a) (L x)) (hxb : Prec r₁ r₂ (L x) (L b)) (hab : a ≠ b) :
    k x ⊆ Ecov P '' Sec r₁ r₂ (L a) (L b) ∧ Ecov P '' Sec r₁ r₂ (L a) (L b) ⊆ Ann P r₁ r₂ ∧
      (∀ m, (PrecLe r₁ r₂ (L m) (L a) ∨ PrecLe r₁ r₂ (L b) (L m)) →
        Disjoint (Ecov P '' Sec r₁ r₂ (L a) (L b)) (k m)) ∧
      (∀ C, IsPreconnected C → C ⊆ Ann P r₁ r₂ \ (k a ∪ k b) →
        (C ∩ Ecov P '' Sec r₁ r₂ (L a) (L b)).Nonempty → C ⊆ Ecov P '' Sec r₁ r₂ (L a) (L b)) := by
  have hF := liftFam_famSeq hL hdisj
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem := fun n => self_mem_famSeq (L := L) n
  refine ⟨?_, fun z ⟨y, hy, hyz⟩ => hyz ▸ Ecov_mem_ann h0.le (sec_subset hy), ?_, ?_⟩
  · rw [← (hL x).image_eq h0 (hk x)]
    exact image_mono (hF.sub_sec h12 (hmem b) (hmem x) hax hxb)
  · intro m hm
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyk
    obtain ⟨j, hj⟩ := ((hL m).pre y (sec_subset hy)).1 hyk
    have hX := mem_famSeq (L := L) m j
    have hout : PrecLe r₁ r₂ (sh (2 * Real.pi * j) (L m)) (L a) ∨
        PrecLe r₁ r₂ (L b) (sh (2 * Real.pi * j) (L m)) := by
      rcases lt_trichotomy j 0 with hj0 | rfl | hj0
      · left
        have hm1 : Prec r₁ r₂ (sh (2 * Real.pi * (-1 : ℤ)) (L m)) (L a) := by
          have := (hF.prec_sh_iff' (hmem m) (2 * Real.pi * (-1 : ℤ))).2 (hper m a)
          rwa [sh_sh, show 2 * Real.pi + 2 * Real.pi * ((-1 : ℤ) : ℝ) = 0 by push_cast; ring,
            sh_zero] at this
        exact Or.inr (hF.lt_of_le_of_lt h12 hX (mem_famSeq m (-1))
          (hF.le_shift_mono h12 hT (hmem m) (by omega)) hm1)
      · simpa [sh_zero] using hm
      · right
        refine Or.inr (hF.lt_of_lt_of_le h12 (hmem b) (sh_two_pi_mem_famSeq m) (hper b m) ?_)
        rw [sh_two_pi]
        exact hF.le_shift_mono h12 hT (hmem m) (by omega)
    exact disjoint_left.1 (hF.sec_disjoint_mem h12 (hmem a) hX hout) hy hj
  · intro C hC hCs hne
    have hab' : Disjoint (k a) (k b) := hdisj hab
    obtain ⟨-, -, hVW, hcov, hV, hW⟩ := two_piece_lift h0 h12 (hL a) (hL b) hab'
      (hF.trans h12 (hmem a) (hmem x) hax hxb) (hper b a)
    rw [← hcov] at hCs
    exact preconnected_sub_piece hV hW
      (fun z hz => (hcov ▸ (Or.inl hz : z ∈ _ ∪ _) : z ∈ Ann P r₁ r₂ \ (k a ∪ k b)).1)
      (fun z hz => (hcov ▸ (Or.inr hz : z ∈ _ ∪ _) : z ∈ Ann P r₁ r₂ \ (k a ∪ k b)).1)
      hVW hC hCs hne

end Cyclic

section Cyclic2

variable {P : ℝ × ℝ} {r₁ r₂ : ℝ}

/-- **The cyclic order of infinitely many disjoint crossing continua.** From pairwise disjoint
continua `k n` crossing the annulus one can extract a subsequence `k (g n)` and, for each `n ≥ 1`,
an open piece `V n` of the annulus containing `k (g n)`, cut off by its neighbours `k (g (n - 1))`
and `k (g (n + 1))` (every connected subset of the annulus missing both neighbours and meeting
`V n` lies in `V n`), missing every other `k (g m)`, and disjoint from `V m` whenever
`|n - m| ≥ 2`. -/
theorem sector_cyclic (h0 : 0 < r₁) (h12 : r₁ < r₂) {k : ℕ → Set (ℝ × ℝ)}
    (hk : ∀ n, IsCrossA P r₁ r₂ (k n)) (hdisj : Pairwise fun m n => Disjoint (k m) (k n)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ V : ℕ → Set (ℝ × ℝ), ∀ n, 1 ≤ n →
      k (g n) ⊆ V n ∧ V n ⊆ Ann P r₁ r₂ ∧ (∀ m, m ≠ n → Disjoint (V n) (k (g m))) ∧
      (∀ m, (n + 2 ≤ m ∨ m + 2 ≤ n) → Disjoint (V n) (V m)) ∧
      (∀ C, IsPreconnected C → C ⊆ Ann P r₁ r₂ \ (k (g (n - 1)) ∪ k (g (n + 1))) →
        (C ∩ V n).Nonempty → C ⊆ V n) := by
  have hex : ∀ n, ∃ L, IsLift P r₁ r₂ (k n) L ∧ (∀ z ∈ L, 0 ≤ z.1) ∧
      ∃ z ∈ L, z.1 < 2 * Real.pi := fun n =>
    exists_normalized_lift h0 h12 (hk n) (hk (n + 1)) (hdisj (by omega))
  choose L hL hnn hlt using hex
  have hF := liftFam_famSeq hL hdisj
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem := fun n => self_mem_famSeq (L := L) n
  have hks : ∀ n, k n ⊆ Ann P r₁ r₂ := fun n => (hk n).sub
  have hne : ∀ m n, m ≠ n → L m ≠ L n := by
    intro m n hmn heq
    obtain ⟨z, hz⟩ := (hL m).cross.conn.nonempty
    have := hF.disj _ (mem_famSeq (L := L) m 0) _ (mem_famSeq (L := L) n 0)
    have hd : Disjoint (sh (2 * Real.pi * (0 : ℤ)) (L m)) (sh (2 * Real.pi * (0 : ℤ)) (L n)) := by
      refine disjoint_left.2 fun x hx hy => ?_
      have hxs : x ∈ Strip r₁ r₂ := ((hL m).cross.sh _).sub hx
      exact disjoint_left.1 (hdisj hmn) (((hL m).pre x hxs).2 ⟨0, hx⟩)
        (((hL n).pre x hxs).2 ⟨0, hy⟩)
    simp only [Int.cast_zero, mul_zero, sh_zero] at hd
    rw [heq] at hd
    exact disjoint_left.1 hd (heq ▸ hz) (heq ▸ hz)
  -- the period bound
  have hper : ∀ m n, Prec r₁ r₂ (L m) (sh (2 * Real.pi) (L n)) := by
    intro m n
    by_cases hmn : m = n
    · subst hmn; exact hF.prec_shift_one hT (hmem m)
    · have hX := sh_two_pi_mem_famSeq (L := L) n
      have hne' : L m ≠ sh (2 * Real.pi) (L n) := by
        intro heq
        obtain ⟨z, hz⟩ := (hL m).cross.conn.nonempty
        have hxs : z ∈ Strip r₁ r₂ := (hL m).cross.sub hz
        have h1 : z ∈ sh (2 * Real.pi * (1 : ℤ)) (L n) := by rw [← sh_two_pi, ← heq]; exact hz
        exact disjoint_left.1 (hdisj hmn) (((hL m).pre z hxs).2 ⟨0, by simpa [sh_zero] using hz⟩)
          (((hL n).pre z hxs).2 ⟨1, h1⟩)
      rcases hF.total (hmem m) hX hne' with h | h
      · exact h
      · exfalso
        obtain ⟨z', hz', hz'lt⟩ := hlt m
        obtain ⟨_, ⟨u, hu, rfl⟩, hle⟩ := prec_min h12 (hF.cross _ hX) h z' hz'
        have := hnn n u hu
        simp only at hle
        linarith
  -- a monotone subsequence
  haveI : IsTrans ℕ fun a b => Prec r₁ r₂ (L a) (L b) :=
    ⟨fun a b c h1 h2 => hF.trans h12 (hmem a) (hmem b) h1 h2⟩
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq
    (fun a b => Prec r₁ r₂ (L a) (L b)) id
  simp only [id] at hg
  have hgi : ∀ m n, m ≠ n → g m ≠ g n := fun m n h h' => h (g.injective h')
  refine ⟨g, g.strictMono, ?_⟩
  rcases hg with hinc | hdec
  · -- increasing
    have hle : ∀ m n, m ≤ n → PrecLe r₁ r₂ (L (g m)) (L (g n)) := by
      intro m n hmn
      rcases hmn.lt_or_eq with h | rfl
      · exact Or.inr (hinc m n h)
      · exact Or.inl rfl
    refine ⟨fun n => Ecov P '' Sec r₁ r₂ (L (g (n - 1))) (L (g (n + 1))), fun n hn => ?_⟩
    obtain ⟨p1, p2, p3, p4⟩ := sector_props h0 h12 hL hks hdisj hper
      (hinc (n - 1) n (by omega)) (hinc n (n + 1) (by omega)) (hgi _ _ (by omega))
    refine ⟨p1, p2, fun m hm => p3 _ ?_, fun m hm => ?_, p4⟩
    · rcases lt_or_gt_of_ne hm with h | h
      · exact Or.inl (hle m (n - 1) (by omega))
      · exact Or.inr (hle (n + 1) m (by omega))
    · rcases hm with hm | hm
      · refine Ecov_image_disjoint h0 sec_subset sec_subset fun j => ?_
        exact hF.sec_disjoint h12 hT (hmem _) (hmem _) (hmem _) (hmem _)
          (hle (n + 1) (m - 1) (by omega)) (Or.inr (hper _ _)) j
      · refine (Ecov_image_disjoint h0 sec_subset sec_subset fun j => ?_).symm
        exact hF.sec_disjoint h12 hT (hmem _) (hmem _) (hmem _) (hmem _)
          (hle (m + 1) (n - 1) (by omega)) (Or.inr (hper _ _)) j
  · -- decreasing
    have hdec' : ∀ m n, m < n → Prec r₁ r₂ (L (g n)) (L (g m)) := fun m n h =>
      (hF.total (hmem _) (hmem _) (hne _ _ (hgi _ _ h.ne))).resolve_left (hdec m n h)
    have hle : ∀ m n, m ≤ n → PrecLe r₁ r₂ (L (g n)) (L (g m)) := by
      intro m n hmn
      rcases hmn.lt_or_eq with h | rfl
      · exact Or.inr (hdec' m n h)
      · exact Or.inl rfl
    refine ⟨fun n => Ecov P '' Sec r₁ r₂ (L (g (n + 1))) (L (g (n - 1))), fun n hn => ?_⟩
    obtain ⟨p1, p2, p3, p4⟩ := sector_props h0 h12 hL hks hdisj hper
      (hdec' n (n + 1) (by omega)) (hdec' (n - 1) n (by omega)) (hgi _ _ (by omega))
    refine ⟨p1, p2, fun m hm => p3 _ ?_, fun m hm => ?_, fun C hC hCs => p4 C hC
      (by rwa [union_comm])⟩
    · rcases lt_or_gt_of_ne hm with h | h
      · exact Or.inr (hle m (n - 1) (by omega))
      · exact Or.inl (hle (n + 1) m (by omega))
    · rcases hm with hm | hm
      · refine (Ecov_image_disjoint h0 sec_subset sec_subset fun j => ?_).symm
        exact hF.sec_disjoint h12 hT (hmem _) (hmem _) (hmem _) (hmem _)
          (hle (n + 1) (m - 1) (by omega)) (Or.inr (hper _ _)) j
      · refine Ecov_image_disjoint h0 sec_subset sec_subset fun j => ?_
        exact hF.sec_disjoint h12 hT (hmem _) (hmem _) (hmem _) (hmem _)
          (hle (m + 1) (n - 1) (by omega)) (Or.inr (hper _ _)) j

/-- **Two disjoint crossing continua cut the annulus into two pieces.** The annulus minus
`K ∪ K'` is the union of two nonempty disjoint sets, each open in the annulus. -/
theorem sector_two (h0 : 0 < r₁) (h12 : r₁ < r₂) {K K' : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (hK' : IsCrossA P r₁ r₂ K') (hd : Disjoint K K') :
    ∃ V₁ V₂ : Set (ℝ × ℝ), V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ∪ V₂ = Ann P r₁ r₂ \ (K ∪ K') ∧ RelOpenAnn P r₁ r₂ V₁ ∧ RelOpenAnn P r₁ r₂ V₂ := by
  obtain ⟨A, hA⟩ := exists_lift h0 h12 hK hK' hd
  obtain ⟨B, hB⟩ := exists_lift h0 h12 hK' hK hd.symm
  obtain ⟨j, h1, h2⟩ := exists_between_lift h12 hA hB hd
  obtain ⟨n1, n2, d, c, o1, o2⟩ := two_piece_lift h0 h12 hA (hB.sh j) hd h1 h2
  exact ⟨_, _, n1, n2, d, c, o1, o2⟩

end Cyclic2

end HPC.Jones.Sector
