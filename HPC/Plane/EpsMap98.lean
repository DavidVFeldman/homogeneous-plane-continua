import HPC.Plane.Snake51

/-!
# Batch 98: the `ε`-map criterion for snake-likeness

A compact connected metric space admitting, for every `ε > 0`, a continuous real function whose
fibres have diameter less than `ε` (an `ε`-map into the line) is snake-like: pull back a chain of
short open intervals covering the (interval) image.
-/

namespace HPC.Plane

open Set Metric

/-- A uniform version of small fibres: on a compact space, a continuous real function with fibres
of diameter less than `ε` has `|f x - f y| < δ → dist x y < ε` for some `δ > 0`. -/
theorem exists_delta_of_fibres {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) {ε : ℝ} (hfib : ∀ x y, f x = f y → dist x y < ε) :
    ∃ δ > 0, ∀ x y, |f x - f y| < δ → dist x y < ε := by
  set K : Set (X × X) := {p | ε ≤ dist p.1 p.2}
  have hKc : IsCompact K :=
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd)).isCompact
  have hg : Continuous fun p : X × X => |f p.1 - f p.2| :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).abs
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun x y _ => ?_⟩
    by_contra hxy
    have : (x, y) ∈ K := not_lt.mp hxy
    rw [hK] at this; exact this
  · obtain ⟨p0, hp0, hmin⟩ := hKc.exists_isMinOn hK hg.continuousOn
    have hpos : 0 < |f p0.1 - f p0.2| := by
      rcases (abs_nonneg (f p0.1 - f p0.2)).lt_or_eq with h | h
      · exact h
      · exfalso
        have he : f p0.1 = f p0.2 := by
          have := h.symm; rw [abs_eq_zero, sub_eq_zero] at this; exact this
        exact absurd hp0 (not_le.mpr (hfib _ _ he))
    refine ⟨_, hpos, fun x y hxy => ?_⟩
    by_contra hd
    have hm := hmin (show (x, y) ∈ K from not_lt.mp hd)
    simp only [mem_setOf_eq] at hm
    linarith

/-- **The `ε`-map criterion.** A compact connected metric space with, for every `ε > 0`, a
continuous real function whose fibres have diameter less than `ε`, is snake-like. -/
theorem isSnakeLike_univ_of_epsMap {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    (hmap : ∀ ε : ℝ, 0 < ε → ∃ f : X → ℝ, Continuous f ∧ ∀ x y, f x = f y → dist x y < ε) :
    IsSnakeLike (univ : Set X) := by
  refine ⟨⟨isCompact_univ, isConnected_univ⟩, fun ε hε => ?_⟩
  obtain ⟨f, hf, hfib⟩ := hmap (ε / 2) (by linarith)
  obtain ⟨δ, hδ, hunif⟩ := exists_delta_of_fibres hf hfib
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨x1, -, hx1⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  set a := f x0
  set b := f x1
  have ha : ∀ x, a ≤ f x := fun x => hx0 (mem_univ x)
  have hb : ∀ x, f x ≤ b := fun x => hx1 (mem_univ x)
  have hrange : Icc a b ⊆ range f :=
    (isPreconnected_range hf).Icc_subset ⟨x0, rfl⟩ ⟨x1, rfl⟩
  set h := δ / 3 with hh
  have hh0 : 0 < h := by positivity
  set n := ⌊(b - a) / h⌋₊ + 1 with hn
  have hn_le : ((n - 1 : ℕ) : ℝ) * h ≤ b - a := by
    have h1 : n - 1 = ⌊(b - a) / h⌋₊ := by omega
    rw [h1]
    have := Nat.floor_le (div_nonneg (sub_nonneg.mpr (ha x1)) hh0.le)
    rwa [le_div_iff₀ hh0] at this
  -- the links
  let I : ℕ → Set ℝ := fun i => Ioo (a + ((i : ℝ) - 1) * h) (a + ((i : ℝ) + 1) * h)
  have hval : ∀ i : ℕ, i < n → ∀ t : ℝ, t ∈ Icc a b → t ∈ I i → ∃ x, x ∈ f ⁻¹' I i ∧ f x = t :=
    fun i _ t ht hti => by
      obtain ⟨x, rfl⟩ := hrange ht
      exact ⟨x, hti, rfl⟩
  let D : Chain X n :=
    { link := fun i => f ⁻¹' I i
      isOpen := fun i => isOpen_Ioo.preimage hf
      adjacent := by
        intro i j
        constructor
        · rintro ⟨x, hxi, hxj⟩
          simp only [I, mem_preimage, mem_Ioo] at hxi hxj
          have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 2 := by nlinarith
          have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 2 := by nlinarith
          have h1' : (i : ℕ) < j + 2 := by exact_mod_cast h1
          have h2' : (j : ℕ) < i + 2 := by exact_mod_cast h2
          omega
        · intro hij
          have hi := i.isLt
          have hj := j.isLt
          have key1 : ∀ i : ℕ, i < n → ((f ⁻¹' I i) ∩ (f ⁻¹' I i)).Nonempty := by
            intro i hi
            have hile : (i : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i ≤ n - 1)
            have hib : (i : ℝ) * h ≤ b - a := le_trans (by nlinarith) hn_le
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            obtain ⟨x, hx, -⟩ := hval i hi (a + (i : ℝ) * h)
              ⟨by nlinarith, by linarith⟩ ⟨by linarith, by linarith⟩
            exact ⟨x, hx, hx⟩
          have key2 : ∀ i : ℕ, i + 1 < n → ((f ⁻¹' I i) ∩ (f ⁻¹' I (i + 1))).Nonempty := by
            intro i hi
            have hile : ((i + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
              exact_mod_cast (by omega : i + 1 ≤ n - 1)
            have hib : ((i + 1 : ℕ) : ℝ) * h ≤ b - a := le_trans (by nlinarith) hn_le
            push_cast at hib
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            obtain ⟨x, -, hx⟩ := hval i (by omega) (a + ((i : ℝ) + 1 / 2) * h)
              ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩
            refine ⟨x, ?_, ?_⟩
            · simp only [I, mem_preimage, mem_Ioo, hx]; constructor <;> nlinarith
            · simp only [I, mem_preimage, mem_Ioo, hx]; push_cast; constructor <;> nlinarith
          have : (j : ℕ) = i ∨ (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 := by omega
          rcases this with h | h | h
          · rw [h]; exact key1 i hi
          · rw [h]; exact key2 i (by omega)
          · rw [h, inter_comm]; exact key2 j (by omega) }
  refine ⟨n, D, fun i => ⟨isBounded_of_compactSpace, ?_⟩, fun x _ => ?_⟩
  · have : Metric.diam (D.link i) ≤ ε / 2 := by
      apply Metric.diam_le_of_forall_dist_le (by linarith)
      intro x hx y hy
      simp only [D, I, mem_preimage, mem_Ioo] at hx hy
      refine (hunif x y ?_).le
      rw [abs_lt]; constructor <;> nlinarith
    linarith
  · have hq : 0 ≤ (f x - a) / h := div_nonneg (sub_nonneg.mpr (ha x)) hh0.le
    set i := ⌊(f x - a) / h⌋₊ with hi
    have hin : i < n := by
      have : i ≤ ⌊(b - a) / h⌋₊ :=
        Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [hb x]) hh0.le)
      omega
    have h1 := Nat.floor_le hq
    have h2 := Nat.lt_floor_add_one ((f x - a) / h)
    rw [← hi] at h1 h2
    rw [le_div_iff₀ hh0] at h1
    rw [div_lt_iff₀ hh0] at h2
    simp only [Chain.union, mem_iUnion]
    refine ⟨⟨i, hin⟩, ?_⟩
    simp only [D, I, mem_preimage, mem_Ioo]
    constructor <;> nlinarith

/-- The uniform version of small fibres on a compact subset. -/
theorem exists_delta_of_fibres_on {X : Type*} [MetricSpace X] [CompactSpace X] {M : Set X}
    (hM : IsClosed M) {f : X → ℝ} (hf : Continuous f) {ε : ℝ}
    (hfib : ∀ x ∈ M, ∀ y ∈ M, f x = f y → dist x y < ε) :
    ∃ δ > 0, ∀ x ∈ M, ∀ y ∈ M, |f x - f y| < δ → dist x y < ε := by
  set K : Set (X × X) := (M ×ˢ M) ∩ {p | ε ≤ dist p.1 p.2}
  have hKc : IsCompact K :=
    ((hM.prod hM).inter (isClosed_le continuous_const
      (continuous_fst.dist continuous_snd))).isCompact
  have hg : Continuous fun p : X × X => |f p.1 - f p.2| :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).abs
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun x hx y hy _ => ?_⟩
    by_contra hxy
    have : (x, y) ∈ K := ⟨⟨hx, hy⟩, not_lt.mp hxy⟩
    rw [hK] at this; exact this
  · obtain ⟨p0, hp0, hmin⟩ := hKc.exists_isMinOn hK hg.continuousOn
    have hpos : 0 < |f p0.1 - f p0.2| := by
      rcases (abs_nonneg (f p0.1 - f p0.2)).lt_or_eq with h | h
      · exact h
      · exfalso
        have he : f p0.1 = f p0.2 := by
          have := h.symm; rw [abs_eq_zero, sub_eq_zero] at this; exact this
        exact absurd hp0.2 (not_le.mpr (hfib _ hp0.1.1 _ hp0.1.2 he))
    refine ⟨_, hpos, fun x hx y hy hxy => ?_⟩
    by_contra hd
    have hm := hmin (show (x, y) ∈ K from ⟨⟨hx, hy⟩, not_lt.mp hd⟩)
    simp only [mem_setOf_eq] at hm
    linarith

/-- **The `ε`-map criterion, for a subcontinuum.** A continuum `M` in a compact metric space such
that for every `ε > 0` some continuous real function has fibres *within `M`* of diameter less
than `ε` is snake-like. The links are preimages of short intervals, cut down to a thin
neighbourhood of `M`. -/
theorem isSnakeLike_of_epsMap {X : Type*} [MetricSpace X] [CompactSpace X] {M : Set X}
    (hM : Fold.Q78.IsContinuum M)
    (hmap : ∀ ε : ℝ, 0 < ε → ∃ f : X → ℝ, Continuous f ∧
      ∀ x ∈ M, ∀ y ∈ M, f x = f y → dist x y < ε) :
    IsSnakeLike M := by
  refine ⟨hM, fun ε hε => ?_⟩
  obtain ⟨f, hf, hfib⟩ := hmap (ε / 4) (by linarith)
  obtain ⟨δ, hδ, hunif⟩ := exists_delta_of_fibres_on hM.1.isClosed hf hfib
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (δ / 6) (by positivity)
  set η' := min η (ε / 8) with hη'
  have hη'0 : 0 < η' := lt_min hη (by linarith)
  obtain ⟨x0, hx0M, hx0⟩ := hM.1.exists_isMinOn hM.2.nonempty hf.continuousOn
  obtain ⟨x1, hx1M, hx1⟩ := hM.1.exists_isMaxOn hM.2.nonempty hf.continuousOn
  set a := f x0
  set b := f x1
  have ha : ∀ x ∈ M, a ≤ f x := fun x hx => hx0 hx
  have hb : ∀ x ∈ M, f x ≤ b := fun x hx => hx1 hx
  have hrange : Icc a b ⊆ f '' M :=
    (hM.2.isPreconnected.image f hf.continuousOn).Icc_subset ⟨x0, hx0M, rfl⟩ ⟨x1, hx1M, rfl⟩
  set h := δ / 6 with hh
  have hh0 : 0 < h := by positivity
  set n := ⌊(b - a) / h⌋₊ + 1 with hn
  have hn_le : ((n - 1 : ℕ) : ℝ) * h ≤ b - a := by
    have h1 : n - 1 = ⌊(b - a) / h⌋₊ := by omega
    rw [h1]
    have := Nat.floor_le (div_nonneg (sub_nonneg.mpr (ha x1 hx1M)) hh0.le)
    rwa [le_div_iff₀ hh0] at this
  let I : ℕ → Set ℝ := fun i => Ioo (a + ((i : ℝ) - 1) * h) (a + ((i : ℝ) + 1) * h)
  let V : Set X := Metric.thickening η' M
  have hMV : M ⊆ V := Metric.self_subset_thickening hη'0 M
  have hval : ∀ i : ℕ, ∀ t : ℝ, t ∈ Icc a b → t ∈ I i → ∃ x, x ∈ f ⁻¹' I i ∩ V ∧ f x = t :=
    fun i t ht hti => by
      obtain ⟨x, hx, rfl⟩ := hrange ht
      exact ⟨x, ⟨hti, hMV hx⟩, rfl⟩
  let D : Chain X n :=
    { link := fun i => f ⁻¹' I i ∩ V
      isOpen := fun i => (isOpen_Ioo.preimage hf).inter Metric.isOpen_thickening
      adjacent := by
        intro i j
        constructor
        · rintro ⟨x, ⟨hxi, -⟩, hxj, -⟩
          simp only [I, mem_preimage, mem_Ioo] at hxi hxj
          have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 2 := by nlinarith
          have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 2 := by nlinarith
          have h1' : (i : ℕ) < j + 2 := by exact_mod_cast h1
          have h2' : (j : ℕ) < i + 2 := by exact_mod_cast h2
          omega
        · intro hij
          have hi := i.isLt
          have hj := j.isLt
          have key1 : ∀ i : ℕ, i < n → ((f ⁻¹' I i ∩ V) ∩ (f ⁻¹' I i ∩ V)).Nonempty := by
            intro i hi
            have hile : (i : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i ≤ n - 1)
            have hib : (i : ℝ) * h ≤ b - a := le_trans (by nlinarith) hn_le
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            obtain ⟨x, hx, -⟩ := hval i (a + (i : ℝ) * h)
              ⟨by nlinarith, by linarith⟩ ⟨by linarith, by linarith⟩
            exact ⟨x, hx, hx⟩
          have key2 : ∀ i : ℕ, i + 1 < n →
              ((f ⁻¹' I i ∩ V) ∩ (f ⁻¹' I (i + 1) ∩ V)).Nonempty := by
            intro i hi
            have hile : ((i + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
              exact_mod_cast (by omega : i + 1 ≤ n - 1)
            have hib : ((i + 1 : ℕ) : ℝ) * h ≤ b - a := le_trans (by nlinarith) hn_le
            push_cast at hib
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            obtain ⟨x, ⟨-, hxV⟩, hx⟩ := hval i (a + ((i : ℝ) + 1 / 2) * h)
              ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩
            refine ⟨x, ⟨?_, hxV⟩, ?_, hxV⟩
            · simp only [I, mem_preimage, mem_Ioo, hx]; constructor <;> nlinarith
            · simp only [I, mem_preimage, mem_Ioo, hx]; push_cast; constructor <;> nlinarith
          have : (j : ℕ) = i ∨ (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 := by omega
          rcases this with h | h | h
          · rw [h]; exact key1 i hi
          · rw [h]; exact key2 i (by omega)
          · rw [h, inter_comm]; exact key2 j (by omega) }
  refine ⟨n, D, fun i => ⟨isBounded_of_compactSpace, ?_⟩, fun x hx => ?_⟩
  · have : Metric.diam (D.link i) ≤ ε / 2 := by
      apply Metric.diam_le_of_forall_dist_le (by linarith)
      intro x hx y hy
      obtain ⟨hxI, hxV⟩ := hx
      obtain ⟨hyI, hyV⟩ := hy
      obtain ⟨x', hx'M, hxx'⟩ := Metric.mem_thickening_iff.mp hxV
      obtain ⟨y', hy'M, hyy'⟩ := Metric.mem_thickening_iff.mp hyV
      simp only [I, mem_preimage, mem_Ioo] at hxI hyI
      have e1 := hηf (lt_of_lt_of_le hxx' (min_le_left _ _))
      have e2 := hηf (lt_of_lt_of_le hyy' (min_le_left _ _))
      rw [Real.dist_eq] at e1 e2
      have hfx'y' : |f x' - f y'| < δ := by
        rw [abs_lt] at e1 e2 ⊢; constructor <;> nlinarith
      have hd := hunif x' hx'M y' hy'M hfx'y'
      have h3 : dist x y ≤ dist x x' + dist x' y' + dist y' y := dist_triangle4 _ _ _ _
      have h4 : dist x x' < ε / 8 := lt_of_lt_of_le hxx' (min_le_right _ _)
      have h5 : dist y' y < ε / 8 := by
        rw [dist_comm]; exact lt_of_lt_of_le hyy' (min_le_right _ _)
      linarith
    linarith
  · have hq : 0 ≤ (f x - a) / h := div_nonneg (sub_nonneg.mpr (ha x hx)) hh0.le
    set i := ⌊(f x - a) / h⌋₊ with hi
    have hin : i < n := by
      have : i ≤ ⌊(b - a) / h⌋₊ :=
        Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [hb x hx]) hh0.le)
      omega
    have h1 := Nat.floor_le hq
    have h2 := Nat.lt_floor_add_one ((f x - a) / h)
    rw [← hi] at h1 h2
    rw [le_div_iff₀ hh0] at h1
    rw [div_lt_iff₀ hh0] at h2
    simp only [Chain.union, mem_iUnion]
    refine ⟨⟨i, hin⟩, ?_, hMV hx⟩
    simp only [I, mem_preimage, mem_Ioo]
    constructor <;> nlinarith

end HPC.Plane
