import HPC.Hagopian.H76Schoen

/-!
# Batch 159, item C: half-collars on the two sides of a simple closed curve

`IsHalfCollar φ S Ŝ g`: an embedding `g` of the square with `g (t, 0) = φ t`, into `Ŝ` (a side `S`
of a simple closed curve together with the curve), whose interior goes into `S`, which meets the
arc `range φ` only on the bottom side, and which is relatively open along the bottom side.

* `isHalfCollar_bounded`: from `plane_schoenflies_aux`, for the bounded side.
* `isHalfCollar_unbounded`: for the unbounded side, by the inversion `z ↦ c + (z − c)/|z − c|²` about
  a point `c` of the bounded side, `plane_schoenflies_aux`, and a restriction of the square to a strip
  `[0, 1] × [0, h]` along the bottom side avoiding the preimage of the point at infinity.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore HPC.Moore.Gen HPC.Jones

/-- A half-collar of the arc `φ` on the side `S` (with `Ŝ = S ∪ J`). -/
def IsHalfCollar (φ : unitInterval → Pt) (S Ŝ : Set Pt) (g : unitInterval × unitInterval → Pt) :
    Prop :=
  IsEmbedding g ∧ (∀ t, g (t, 0) = φ t) ∧ range g ⊆ Ŝ ∧ (∀ p, g p ∈ range φ → p.2 = 0) ∧
    (∀ p : unitInterval × unitInterval, 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → g p ∈ S) ∧
    ∃ W, IsOpen W ∧ W ∩ Ŝ = g '' {p | 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 1}

theorem isOpen_strip {h : ℝ} :
    IsOpen {p : unitInterval × unitInterval | 0 < p.1 ∧ p.1 < 1 ∧ (p.2 : ℝ) < h} := by
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
  · exact isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)
  · exact isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const
  · exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const

/-- An embedding is relatively open onto its range. -/
theorem exists_open_inter_range {X : Type*} [TopologicalSpace X] {f : X → Pt} (hf : IsEmbedding f)
    {O : Set X} (hO : IsOpen O) : ∃ W, IsOpen W ∧ W ∩ range f = f '' O := by
  obtain ⟨W, hW, hWO⟩ := hf.isInducing.isOpen_iff.1 hO
  exact ⟨W, hW, by rw [← hWO, image_preimage_eq_inter_range]⟩

/-- **The half-collar on the bounded side.** -/
theorem isHalfCollar_bounded {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) {φ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hφJ : range φ ⊆ J) : ∃ g, IsHalfCollar φ D (D ∪ J) g := by
  obtain ⟨f, hf, hfr, hf0, hfD⟩ := plane_schoenflies_aux hJ hD hDc hDb hDJ hφ hφJ
  have hO : IsOpen {p : unitInterval × unitInterval | 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 1} := by
    have := isOpen_strip (h := 1)
    convert this using 3 with p
  obtain ⟨W, hW, hWO⟩ := exists_open_inter_range hf hO
  refine ⟨f, hf, hf0, by rw [hfr, union_comm], ?_, ?_, W, hW, by rw [union_comm, ← hfr, hWO]⟩
  · rintro p ⟨t, ht⟩
    rw [← hf0] at ht
    rw [← hf.injective ht]
  · intro p h1 h2 h3 h4
    rw [← hfD]; exact ⟨p, ⟨h1, h2, h3, h4⟩, rfl⟩

/-! ### The inversion -/

/-- The square of the Euclidean norm. -/
def nsq (u : Pt) : ℝ := u.1 ^ 2 + u.2 ^ 2

/-- The inversion in the unit circle. -/
noncomputable def inv0 (u : Pt) : Pt := (u.1 / nsq u, u.2 / nsq u)

theorem nsq_pos {u : Pt} (hu : u ≠ 0) : 0 < nsq u := by
  unfold nsq
  rcases u with ⟨x, y⟩
  by_contra h
  push_neg at h
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact hu (by simp [hx, hy])

theorem nsq_inv0 {u : Pt} (hu : u ≠ 0) : nsq (inv0 u) = 1 / nsq u := by
  have := nsq_pos hu
  unfold inv0
  unfold nsq at *
  field_simp

theorem inv0_ne_zero {u : Pt} (hu : u ≠ 0) : inv0 u ≠ 0 := by
  intro h
  have := nsq_inv0 hu
  rw [h] at this
  have h0 : nsq (0 : Pt) = 0 := by simp [nsq]
  rw [h0] at this
  have := nsq_pos hu
  have : 1 / nsq u > 0 := by positivity
  linarith

theorem inv0_inv0 {u : Pt} (hu : u ≠ 0) : inv0 (inv0 u) = u := by
  have h1 := nsq_inv0 hu
  have h2 := nsq_pos hu
  have e : ∀ x : ℝ, x / nsq u / (1 / nsq u) = x := fun x => by field_simp
  ext
  · show (inv0 u).1 / nsq (inv0 u) = u.1
    rw [h1]; exact e u.1
  · show (inv0 u).2 / nsq (inv0 u) = u.2
    rw [h1]; exact e u.2

theorem continuousOn_inv0 : ContinuousOn inv0 {0}ᶜ := by
  have hn : Continuous nsq := by unfold nsq; fun_prop
  intro u hu
  have hne : nsq u ≠ 0 := (nsq_pos hu).ne'
  apply ContinuousAt.continuousWithinAt
  exact ((continuous_fst.continuousAt).div hn.continuousAt hne).prodMk
    ((continuous_snd.continuousAt).div hn.continuousAt hne)

theorem sq_le_nsq (u : Pt) : ‖u‖ ^ 2 ≤ nsq u := by
  rw [Prod.norm_def]
  unfold nsq
  rcases le_total ‖u.1‖ ‖u.2‖ with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg u.1]
  · rw [max_eq_left h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg u.2]

theorem nsq_le_sq (u : Pt) : nsq u ≤ 2 * ‖u‖ ^ 2 := by
  rw [Prod.norm_def]
  unfold nsq
  have h1 : u.1 ^ 2 ≤ max ‖u.1‖ ‖u.2‖ ^ 2 := by
    rw [← sq_abs u.1, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
  have h2 : u.2 ^ 2 ≤ max ‖u.1‖ ‖u.2‖ ^ 2 := by
    rw [← sq_abs u.2, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
  linarith

/-- The inversion about `c`. -/
noncomputable def invc (c : Pt) (z : Pt) : Pt := inv0 (z - c)

/-- Its inverse. -/
noncomputable def invcInv (c : Pt) (w : Pt) : Pt := c + inv0 w

theorem invcInv_invc {c z : Pt} (hz : z ≠ c) : invcInv c (invc c z) = z := by
  unfold invcInv invc
  rw [inv0_inv0 (sub_ne_zero.2 hz)]; abel

theorem invc_invcInv {c w : Pt} (hw : w ≠ 0) : invc c (invcInv c w) = w := by
  unfold invcInv invc
  rw [add_sub_cancel_left, inv0_inv0 hw]

theorem invc_ne_zero {c z : Pt} (hz : z ≠ c) : invc c z ≠ 0 := inv0_ne_zero (sub_ne_zero.2 hz)

theorem invcInv_ne {c w : Pt} (hw : w ≠ 0) : invcInv c w ≠ c := by
  unfold invcInv
  intro h
  exact inv0_ne_zero hw (by simpa using h)

theorem continuousOn_invc (c : Pt) : ContinuousOn (invc c) {c}ᶜ :=
  continuousOn_inv0.comp (continuous_sub_right c).continuousOn fun _ hz =>
    sub_ne_zero.2 hz

theorem continuousOn_invcInv (c : Pt) : ContinuousOn (invcInv c) {0}ᶜ :=
  continuousOn_const.add continuousOn_inv0

theorem invc_injOn (c : Pt) : InjOn (invc c) {c}ᶜ := fun z hz w hw h => by
  rw [← invcInv_invc hz, ← invcInv_invc hw, h]

/-- The image of an arc under a map continuous and injective on a set containing it. -/
theorem tarc_image_of_injOn {g : Pt → Pt} {S : Set Pt} (hg : ContinuousOn g S) (hinj : InjOn g S)
    {a b : Pt} {C : Set Pt} (hC : TArc a b C) (hCS : C ⊆ S) : TArc (g a) (g b) (g '' C) := by
  obtain ⟨hab, f, hf, rfl, rfl, rfl⟩ := hC
  have hc : Continuous (g ∘ f) :=
    hg.comp_continuous hf.continuous fun t => hCS (mem_range_self t)
  have hi : Function.Injective (g ∘ f) := fun s t h =>
    hf.injective (hinj (hCS (mem_range_self s)) (hCS (mem_range_self t)) h)
  have := TArc.of_inj hc hi
  rwa [range_comp] at this

theorem tscc_image_of_injOn {g : Pt → Pt} {S : Set Pt} (hg : ContinuousOn g S) (hinj : InjOn g S)
    {J : Set Pt} (hJ : TSCC J) (hJS : J ⊆ S) : TSCC (g '' J) := by
  obtain ⟨A, B, C₁, C₂, h₁, h₂, h12, rfl⟩ := hJ
  have s1 : C₁ ⊆ S := fun z hz => hJS (Or.inl hz)
  have s2 : C₂ ⊆ S := fun z hz => hJS (Or.inr hz)
  refine ⟨g A, g B, g '' C₁, g '' C₂, tarc_image_of_injOn hg hinj h₁ s1,
    tarc_image_of_injOn hg hinj h₂ s2, ?_, image_union g C₁ C₂⟩
  rw [← (hinj.mono (union_subset s1 s2)).image_inter subset_union_left subset_union_right, h12,
    image_pair]

theorem invcInv_injOn (c : Pt) : InjOn (invcInv c) {0}ᶜ := fun w hw w' hw' h => by
  rw [← invc_invcInv (c := c) hw, ← invc_invcInv (c := c) hw', h]

/-- **The half-collar on the unbounded side.** `J` a simple closed curve, `I` and `E` its bounded and
unbounded sides. -/
theorem isHalfCollar_unbounded {J I E : Set Pt} (hJ : TSCC J) (hIo : IsOpen I) (hIne : I.Nonempty)
    (hIb : Bornology.IsBounded I) (hEo : IsOpen E) (hEc : IsConnected E) (hEf : frontier E = J)
    (hIE : Disjoint I E) (hU : I ∪ E = Jᶜ) {φ : unitInterval → Pt} (hφ : IsEmbedding φ)
    (hφJ : range φ ⊆ J) : ∃ g, IsHalfCollar φ E (E ∪ J) g := by
  obtain ⟨c, hcI⟩ := hIne
  have hJc : IsCompact J := TSCC.isCompact' hJ
  have hIJ : Disjoint I J := disjoint_left.2 fun z hz hzJ =>
    (hU.symm ▸ (Or.inl hz : z ∈ I ∪ E) : z ∈ Jᶜ) hzJ
  have hEJ : Disjoint E J := disjoint_left.2 fun z hz hzJ =>
    (hU.symm ▸ (Or.inr hz : z ∈ I ∪ E) : z ∈ Jᶜ) hzJ
  have hsubJ : J ⊆ {c}ᶜ := fun z hz e => disjoint_left.1 hIJ (mem_singleton_iff.1 e ▸ hcI) hz
  have hsubE : E ⊆ {c}ᶜ := fun z hz e => disjoint_left.1 hIE (mem_singleton_iff.1 e ▸ hcI) hz
  set ι := invc c
  set κ := invcInv c
  have hκι : ∀ z, z ≠ c → κ (ι z) = z := fun z hz => invcInv_invc hz
  have hικ : ∀ w, w ≠ (0 : Pt) → ι (κ w) = w := fun w hw => invc_invcInv hw
  have hιc := continuousOn_invc c
  have hκc := continuousOn_invcInv c
  set J' := ι '' J
  set E' := ι '' E
  have hJ' : TSCC J' := tscc_image_of_injOn hιc (invc_injOn c) hJ hsubJ
  -- (F1)
  have F1 : ∀ w, w ≠ 0 → (w ∈ E' ↔ κ w ∈ E) := by
    intro w hw
    constructor
    · rintro ⟨z, hz, rfl⟩; rw [hκι z (hsubE hz)]; exact hz
    · intro h; exact ⟨κ w, h, hικ w hw⟩
  have E'ne : ∀ w ∈ E', w ≠ 0 := by rintro _ ⟨z, hz, rfl⟩; exact invc_ne_zero (hsubE hz)
  -- (F2) `E` is away from `c`
  obtain ⟨d, hd, hdI⟩ := Metric.isOpen_iff.1 hIo c hcI
  have F2 : ∀ z ∈ E, d ≤ ‖z - c‖ := by
    intro z hz
    by_contra h
    push_neg at h
    exact disjoint_left.1 hIE (hdI (by rw [mem_ball, dist_eq_norm]; exact h)) hz
  -- (F3) `E` contains everything far away
  obtain ⟨R, hR⟩ := (hIb.union hJc.isBounded).subset_ball (0 : Pt)
  have F3 : ∀ z : Pt, R ≤ ‖z‖ → z ∈ E := by
    intro z hz
    have hz' : z ∉ I ∪ J := fun h => by
      have := hR h; rw [mem_ball, dist_zero_right] at this; linarith
    have : z ∈ Jᶜ := fun h => hz' (Or.inr h)
    rw [← hU] at this
    exact this.resolve_left fun h => hz' (Or.inl h)
  -- (F4) bounded
  have F4 : ∀ z ∈ E, ‖ι z‖ ≤ 1 / d := by
    intro z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.2 (hsubE hz)
    have h1 := sq_le_nsq (ι z)
    have h2 : nsq (ι z) = 1 / nsq (z - c) := nsq_inv0 hzc
    have h3 := sq_le_nsq (z - c)
    have h4 := F2 z hz
    have h5 : d ^ 2 ≤ nsq (z - c) := le_trans (pow_le_pow_left₀ hd.le h4 2) h3
    have h6 : ‖ι z‖ ^ 2 ≤ (1 / d) ^ 2 := by
      rw [h2] at h1
      calc ‖ι z‖ ^ 2 ≤ 1 / nsq (z - c) := h1
        _ ≤ 1 / d ^ 2 := one_div_le_one_div_of_le (by positivity) h5
        _ = (1 / d) ^ 2 := by rw [one_div_pow]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h6
  -- (F5) a punctured ball about `0` in `E'`
  set M : ℝ := |R| + ‖c‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set r : ℝ := 1 / (4 * M) with hr
  have hr0 : 0 < r := by positivity
  have F5 : ∀ w : Pt, w ≠ 0 → ‖w‖ ≤ 2 * r → w ∈ E' := by
    intro w hw hwr
    rw [F1 w hw]
    apply F3
    have h1 := nsq_le_sq w
    have h2 := nsq_le_sq (inv0 w)
    have h3 : nsq (inv0 w) * nsq w = 1 := by
      rw [nsq_inv0 hw]; field_simp [(nsq_pos hw).ne']
    have hwM : ‖w‖ * (2 * M) ≤ 1 := by
      have : 2 * r * (2 * M) = 1 := by rw [hr]; field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right hwr (by positivity : (0:ℝ) ≤ 2 * M)]
    have hinv : M ≤ ‖inv0 w‖ := by
      by_contra hlt
      push_neg at hlt
      have a1 : ‖inv0 w‖ ^ 2 < M ^ 2 := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
      have a2 : nsq w * (2 * M ^ 2) ≤ 1 := by
        have : ‖w‖ ^ 2 * (2 * M) ^ 2 ≤ 1 := by
          have := pow_le_pow_left₀ (by positivity) hwM 2
          rwa [mul_pow, one_pow] at this
        nlinarith
      have a3 : 0 ≤ nsq w := (nsq_pos hw).le
      have b1 : nsq (inv0 w) * nsq w ≤ 2 * ‖inv0 w‖ ^ 2 * nsq w := mul_le_mul_of_nonneg_right h2 a3
      have b2 : 2 * ‖inv0 w‖ ^ 2 * nsq w < 2 * M ^ 2 * nsq w := by
        have := nsq_pos hw; nlinarith
      linarith
    have : ‖inv0 w‖ ≤ ‖κ w‖ + ‖c‖ := by
      have e : inv0 w = κ w - c := by simp [κ, invcInv]
      rw [e]; exact norm_sub_le _ _
    have : R ≤ |R| := le_abs_self R
    linarith
  -- the domain `D'`
  set D' : Set Pt := E' ∪ ball 0 r with hD'def
  have h0D' : (0 : Pt) ∈ D' := Or.inr (mem_ball_self hr0)
  have hD'E' : ∀ w ∈ D', w ≠ 0 → w ∈ E' := by
    rintro w (h | h) hw
    · exact h
    · exact F5 w hw (by rw [mem_ball, dist_zero_right] at h; linarith)
  have hE'o : IsOpen E' := by
    have : E' = {0}ᶜ ∩ κ ⁻¹' E := by
      ext w
      constructor
      · intro h; exact ⟨E'ne w h, (F1 w (E'ne w h)).1 h⟩
      · rintro ⟨hw, h⟩; exact (F1 w hw).2 h
    rw [this]; exact hκc.isOpen_inter_preimage isOpen_compl_singleton hEo
  have hD'o : IsOpen D' := hE'o.union isOpen_ball
  have hE'c : IsConnected E' := hEc.image _ (hιc.mono hsubE)
  have hD'c : IsConnected D' := by
    have hw : ((r / 2 : ℝ), (0 : ℝ)) ≠ (0 : Pt) := by
      intro h; have := congrArg Prod.fst h; simp at this; linarith
    have hn : ‖((r / 2 : ℝ), (0 : ℝ))‖ = r / 2 := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < r / 2), abs_zero]
      exact max_eq_left (by positivity)
    refine IsConnected.union ⟨((r / 2 : ℝ), (0 : ℝ)), F5 _ hw (by rw [hn]; linarith), ?_⟩ hE'c
      (isConnected_ball hr0)
    rw [mem_ball, dist_zero_right, hn]; linarith
  have hD'b : Bornology.IsBounded D' := by
    refine (isBounded_iff_forall_norm_le.2 ⟨1 / d, ?_⟩).union isBounded_ball
    rintro _ ⟨z, hz, rfl⟩; exact F4 z hz
  have hJE : ∀ z ∈ J, z ∉ E := fun z hz hzE => disjoint_left.1 hEJ hzE hz
  have hD'f : frontier D' = J' := by
    rw [hD'o.frontier_eq]
    apply Subset.antisymm
    · rintro w ⟨hwc, hwD⟩
      have hw0 : w ≠ 0 := fun e => hwD (e ▸ h0D')
      rw [closure_union] at hwc
      rcases hwc with hwc | hwc
      · have hκw : ContinuousAt κ w := hκc.continuousAt (isOpen_compl_singleton.mem_nhds hw0)
        have h1 := mem_closure_image hκw hwc
        have hκE : κ '' E' = E := by
          ext z
          constructor
          · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rw [hκι y (hsubE hy)]; exact hy
          · intro hz; exact ⟨ι z, ⟨z, hz, rfl⟩, hκι z (hsubE hz)⟩
        rw [hκE, closure_eq_self_union_frontier, hEf] at h1
        rcases h1 with h1 | h1
        · exact absurd (Or.inl ((F1 w hw0).2 h1)) hwD
        · exact ⟨κ w, h1, hικ w hw0⟩
      · have := closure_ball_subset_closedBall hwc
        rw [mem_closedBall, dist_zero_right] at this
        exact absurd (Or.inl (F5 w hw0 (by linarith))) hwD
    · rintro _ ⟨z, hz, rfl⟩
      have hzc : z ≠ c := hsubJ hz
      have hιz : ContinuousAt ι z := hιc.continuousAt (isOpen_compl_singleton.mem_nhds hzc)
      refine ⟨closure_mono subset_union_left ?_, ?_⟩
      · exact mem_closure_image hιz (frontier_subset_closure (hEf.symm ▸ hz : z ∈ frontier E))
      · intro h
        have h0 : ι z ≠ 0 := invc_ne_zero hzc
        have := (F1 _ h0).1 (hD'E' _ h h0)
        rw [hκι z hzc] at this
        exact hJE z hz this
  -- Schoenflies for `D'`
  have hφ' : IsEmbedding (ι ∘ φ) := by
    have hc : Continuous (ι ∘ φ) :=
      hιc.comp_continuous hφ.continuous fun t => hsubJ (hφJ (mem_range_self t))
    have hi : Function.Injective (ι ∘ φ) := fun s t h =>
      hφ.injective (invc_injOn c (hsubJ (hφJ (mem_range_self s)))
        (hsubJ (hφJ (mem_range_self t))) h)
    exact (hc.isClosedEmbedding hi).isEmbedding
  obtain ⟨f, hf, hfr, hf0, hfD⟩ := plane_schoenflies_aux hJ' hD'o hD'c hD'b hD'f hφ'
    (by rw [range_comp]; exact image_mono hφJ)
  obtain ⟨p₀, hp₀, hfp₀⟩ : (0 : Pt) ∈ f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} :=
    hfD ▸ h0D'
  set h : ℝ := (p₀.2 : ℝ) / 2 with hhdef
  have hh0 : 0 < h := by have : (0 : ℝ) < p₀.2 := hp₀.2.2.1; positivity
  have hh1 : h ≤ 1 / 2 := by have : (p₀.2 : ℝ) ≤ 1 := p₀.2.2.2; rw [hhdef]; linarith
  have hmem : ∀ s : unitInterval, h * (s : ℝ) ∈ unitInterval := fun s =>
    ⟨by have := s.2.1; positivity, by have := s.2.2; nlinarith⟩
  set sc : unitInterval × unitInterval → unitInterval × unitInterval :=
    fun p => (p.1, ⟨h * p.2, hmem p.2⟩) with hscdef
  have hsc_cont : Continuous sc :=
    continuous_fst.prodMk (Continuous.subtype_mk (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)) _)
  have hsc_inj : Function.Injective sc := by
    rintro ⟨x, s⟩ ⟨x', s'⟩ e
    simp only [hscdef, Prod.mk.injEq, Subtype.mk.injEq] at e
    obtain ⟨rfl, e2⟩ := e
    have : (s : ℝ) = s' := mul_left_cancel₀ hh0.ne' e2
    rw [Subtype.ext this]
  have hsc0 : ∀ t, sc (t, 0) = (t, 0) := fun t => by
    simp only [hscdef]; congr 1; apply Subtype.ext; simp
  have hsc_ne : ∀ p, f (sc p) ≠ 0 := by
    intro p e
    rw [← hfp₀] at e
    have := congrArg (fun q : unitInterval × unitInterval => (q.2 : ℝ)) (hf.injective e)
    simp only [hscdef] at this
    have : (p.2 : ℝ) ≤ 1 := p.2.2.2
    have hp0 : (0 : ℝ) < p₀.2 := hp₀.2.2.1
    nlinarith
  set g : unitInterval × unitInterval → Pt := fun p => κ (f (sc p)) with hgdef
  have hg_cont : Continuous g := hκc.comp_continuous (hf.continuous.comp hsc_cont) hsc_ne
  have hg_inj : Function.Injective g := fun p q e =>
    hsc_inj (hf.injective (invcInv_injOn c (hsc_ne p) (hsc_ne q) e))
  have hgι : ∀ p, ι (g p) = f (sc p) := fun p => invc_invcInv (hsc_ne p)
  have hrange : ∀ p, g p ∈ E ∪ J := by
    intro p
    have h1 : f (sc p) ∈ J' ∪ D' := hfr ▸ mem_range_self _
    rcases h1 with ⟨z, hz, hz'⟩ | h1
    · right; show κ (f (sc p)) ∈ J; rw [← hz', hκι z (hsubJ hz)]; exact hz
    · left; exact (F1 _ (hsc_ne p)).1 (hD'E' _ h1 (hsc_ne p))
  have hO' := isOpen_strip (h := h)
  obtain ⟨W', hW'o, hW'⟩ := exists_open_inter_range hf hO'
  refine ⟨g, (hg_cont.isClosedEmbedding hg_inj).isEmbedding, fun t => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hgdef, hsc0, hf0, Function.comp_apply]
    exact hκι _ (hsubJ (hφJ (mem_range_self t)))
  · rintro _ ⟨p, rfl⟩; exact hrange p
  · rintro p ⟨t, ht⟩
    have e : f (sc p) = f (t, 0) := by
      rw [← hgι p, ← ht, hf0]; rfl
    have := congrArg (fun q : unitInterval × unitInterval => (q.2 : ℝ)) (hf.injective e)
    simp only [hscdef] at this
    have : (p.2 : ℝ) = 0 := by
      rcases mul_eq_zero.1 (this.trans (by simp)) with h' | h'
      · exact absurd h' hh0.ne'
      · exact h'
    exact Subtype.ext this
  · intro p h1 h2 h3 h4
    have hin : f (sc p) ∈ D' := by
      rw [← hfD]
      refine ⟨sc p, ⟨h1, h2, ?_, ?_⟩, rfl⟩
      · show (0 : ℝ) < h * p.2
        have : (0 : ℝ) < p.2 := h3
        positivity
      · show h * (p.2 : ℝ) < 1
        have : (p.2 : ℝ) < 1 := h4
        have : (0 : ℝ) ≤ p.2 := p.2.2.1
        nlinarith
    exact (F1 _ (hsc_ne p)).1 (hD'E' _ hin (hsc_ne p))
  · refine ⟨{c}ᶜ ∩ ι ⁻¹' W', hιc.isOpen_inter_preimage isOpen_compl_singleton hW'o, ?_⟩
    apply Subset.antisymm
    · rintro x ⟨⟨hxc, hxW⟩, hxS⟩
      have hxr : ι x ∈ range f := by
        rw [hfr]
        rcases hxS with hx | hx
        · exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
        · exact Or.inl ⟨x, hx, rfl⟩
      have hx' : ι x ∈ W' ∩ range f := ⟨hxW, hxr⟩
      rw [hW'] at hx'
      obtain ⟨q, hq, hqx⟩ := hx'
      have hq2 : (0 : ℝ) ≤ q.2 / h := div_nonneg q.2.2.1 hh0.le
      have hq3 : (q.2 : ℝ) / h < 1 := (div_lt_one hh0).2 hq.2.2
      refine ⟨(q.1, ⟨q.2 / h, hq2, hq3.le⟩), ⟨hq.1, hq.2.1, ?_⟩, ?_⟩
      · show ((⟨(q.2 : ℝ) / h, hq2, hq3.le⟩ : unitInterval) : ℝ) < 1
        exact hq3
      · have hsc : sc (q.1, ⟨q.2 / h, hq2, hq3.le⟩) = q := by
          simp only [hscdef]
          ext
          · rfl
          · show h * ((q.2 : ℝ) / h) = q.2
            field_simp
        simp only [hgdef, hsc, hqx]
        exact hκι x hxc
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨⟨invcInv_ne (hsc_ne p), ?_⟩, hrange p⟩
      show ι (g p) ∈ W'
      rw [hgι p]
      have : f (sc p) ∈ f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ (p.2 : ℝ) < h} := by
        refine ⟨sc p, ⟨hp.1, hp.2.1, ?_⟩, rfl⟩
        show h * (p.2 : ℝ) < h
        have : (p.2 : ℝ) < 1 := hp.2.2
        nlinarith
      rw [← hW'] at this
      exact this.1

end HPC.Hagopian
