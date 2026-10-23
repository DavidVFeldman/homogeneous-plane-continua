import HPC.Span.OT82Parity
import HPC.Span.OT82Zero
import HPC.Fold.Questions78

/-!
# Batch 192, §5: strips (commission 192 §5)

The strip `S_t = B₀ ∪ f[0, t] ∪ B_t ∪ g[0, t]` (O–T Lemma 2.2) as the closed polygon
`stripPoly a b t`, its crossing parity, the sign function `stripSign` (O–T Lemma 2.3, the function
`φ`), and the strip lemma (O–T Theorem 2.7 in the form used).

Changes of shape (recorded in the report):
* §5.1 `strip_basic` is a list of lemmas: `plPath_zero`, `plPath_one`, `continuous_plPath`,
  `plPath_eq_piece`, `dist_plPath_le`, `stripPoly_edge_cases`, `polygonOf_stripPoly_subset`,
  `parity_stripPoly_zero_of_fst_ne`, `parity_stripPoly_left`.
* §5.2 `parity_strip_eventually` is stated for every `t₀` (no `t₀ ∈ [0, 1]` is needed).
* §5.3: the sign is attached to the predicate `StripInner a b t z` ("`z` is on `x = 0`, or off
  `S_t` with parity `1`"), and the key lemma is `stripInner_eventually` (local constancy of that
  predicate near a point off `f`, `g` and `B_{t₀}`). The set `V` of the commission is not used:
  the paths `h`, `k` are only required to stay in `{x ≥ 0}`, off `f[0, 1]` and `g[0, 1]`, to meet
  `x = 0` only inside `B₀`, and to satisfy `StripInner a b 1`. `stripSign_continuousOn` and the
  boundary facts `stripSign_zero_nonneg`, `stripSign_nonpos_of_inner`, `stripSign_eq_zero` follow.
* §5.4 `strip_lemma`: as in the skeleton. Step 1 of the commission (`W ∖ L₀ ⊆ U₁`) is replaced by
  `stripInner_one_of_isPreconnected` (the predicate `StripInner a b 1` is locally constant on the
  region off `f`, `g`, `B₁`; it holds on `W ∩ L₀`; `W` is connected); no boundary bumping.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane

/-! ## Piecewise linear paths -/

/-- The piecewise linear path through `a 0, …, a s` at the times `j / s`, frozen outside `[0, 1]`
(the skeleton's definition, unchanged). -/
noncomputable def plPath {s : ℕ} (a : Fin (s + 1) → Pt) (t : ℝ) : Pt :=
  a 0 + ∑ j : Fin s, (max 0 (min 1 ((s : ℝ) * t - j))) • (a j.succ - a j.castSucc)

/-- The closed polygon `S_t = B₀ ∪ f[0, t] ∪ B_t ∪ g[0, t]` (the skeleton's definition, unchanged):
`f(min(t, k/s))` for `k ≤ s`, then `g(min(t, (2s + 1 − k)/s))`. Edge `s` is `B_t`, the closing
edge is `B₀`. -/
noncomputable def stripPoly {s : ℕ} (a b : Fin (s + 1) → Pt) (t : ℝ) : Fin (2 * s + 2) → Pt :=
  fun k => if k.val ≤ s then plPath a (min t ((k.val : ℝ) / s))
    else plPath b (min t (((2 * s + 1 - k.val : ℕ) : ℝ) / s))

/-- The vertices extended to `ℕ` (constant beyond `s`). -/
def finExt {s : ℕ} {E : Type*} (a : Fin (s + 1) → E) (k : ℕ) : E :=
  a ⟨min k s, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem finExt_of_le {s : ℕ} {E : Type*} (a : Fin (s + 1) → E) {k : ℕ} (hk : k ≤ s) :
    finExt a k = a ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp only [finExt, min_eq_left hk]

theorem continuous_plPath {s : ℕ} (a : Fin (s + 1) → Pt) : Continuous (plPath a) := by
  unfold plPath
  refine continuous_const.add (continuous_finset_sum _ fun j _ => ?_)
  exact ((continuous_const.max (continuous_const.min
    ((continuous_const.mul continuous_id).sub continuous_const))).smul continuous_const)

/-- `plPath` as a sum over `range s`. -/
theorem plPath_eq_range {s : ℕ} (a : Fin (s + 1) → Pt) (t : ℝ) :
    plPath a t = finExt a 0 + ∑ i ∈ Finset.range s,
      (max 0 (min 1 ((s : ℝ) * t - i))) • (finExt a (i + 1) - finExt a i) := by
  unfold plPath
  rw [← Fin.sum_univ_eq_sum_range (fun i => (max 0 (min 1 ((s : ℝ) * t - i))) •
    (finExt a (i + 1) - finExt a i)) s]
  have h0 : finExt a 0 = a 0 := by simp [finExt]
  rw [h0]
  refine congrArg (a 0 + ·) (Finset.sum_congr rfl fun j _ => ?_)
  rw [finExt_of_le a (Nat.succ_le_of_lt j.2), finExt_of_le a j.2.le]
  rfl

/-- **The piece formula**: on `[j/s, (j+1)/s]`, `plPath a` is affine. -/
theorem plPath_piece {s : ℕ} (a : Fin (s + 1) → Pt) {j : ℕ} (hj : j < s) {t : ℝ}
    (ht : (j : ℝ) ≤ s * t) (ht' : (s : ℝ) * t ≤ j + 1) :
    plPath a t = (1 - ((s : ℝ) * t - j)) • finExt a j + ((s : ℝ) * t - j) • finExt a (j + 1) := by
  rw [plPath_eq_range, ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hj),
    Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range j, (max 0 (min 1 ((s : ℝ) * t - i))) •
      (finExt a (i + 1) - finExt a i) = finExt a j - finExt a 0 := by
    rw [← Finset.sum_range_sub (fun i => finExt a i)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : (i : ℝ) + 1 ≤ j := by
      have := Finset.mem_range.1 hi; exact_mod_cast this
    rw [min_eq_left (by linarith), max_eq_right zero_le_one, one_smul]
  have h2 : ∑ i ∈ Finset.Ico (j + 1) s, (max 0 (min 1 ((s : ℝ) * t - i))) •
      (finExt a (i + 1) - finExt a i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : (j : ℝ) + 1 ≤ i := by
      have := (Finset.mem_Ico.1 hi).1; exact_mod_cast this
    rw [max_eq_left (min_le_of_right_le (by linarith)), zero_smul]
  have h3 : max 0 (min 1 ((s : ℝ) * t - j)) = (s : ℝ) * t - j := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  rw [h1, h2, h3, add_zero]
  module

theorem piece_mem_Icc {s : ℕ} {j : ℕ} (hj : j < s) {t : ℝ}
    (ht : (j : ℝ) ≤ s * t) (ht' : (s : ℝ) * t ≤ j + 1) : t ∈ Icc (0 : ℝ) 1 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hjs : (j : ℝ) + 1 ≤ s := by exact_mod_cast hj
  constructor
  · by_contra h; push_neg at h
    have : (s : ℝ) * t < 0 := mul_neg_of_pos_of_neg hs h
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · by_contra h; push_neg at h
    have : (s : ℝ) < s * t := by nlinarith
    linarith

/-- Every time in `[0, 1]` lies in some piece; the same piece and parameter serve every vertex
list. -/
theorem plPath_eq_piece {s : ℕ} (hs : 0 < s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ j < s, ∃ l ∈ Icc (0 : ℝ) 1, (s : ℝ) * t = j + l ∧ ∀ a : Fin (s + 1) → Pt,
      plPath a t = (1 - l) • finExt a j + l • finExt a (j + 1) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hst0 : 0 ≤ (s : ℝ) * t := mul_nonneg hs'.le ht.1
  have hst1 : (s : ℝ) * t ≤ s := by nlinarith [ht.2]
  set j := min ⌊(s : ℝ) * t⌋₊ (s - 1)
  have hjs : j < s := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hs one_pos)
  have hj1 : (j : ℝ) ≤ s * t :=
    le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hst0)
  have hj2 : (s : ℝ) * t ≤ j + 1 := by
    rcases le_total ⌊(s : ℝ) * t⌋₊ (s - 1) with h | h
    · rw [show j = ⌊(s : ℝ) * t⌋₊ from min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [show j = s - 1 from min_eq_right h]
      have : ((s - 1 : ℕ) : ℝ) = s - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hs.ne'), Nat.cast_one]
      rw [this]; linarith
  refine ⟨j, hjs, (s : ℝ) * t - j, ⟨by linarith, by linarith⟩, by ring, fun a => ?_⟩
  exact plPath_piece a hjs hj1 hj2

theorem plPath_zero {s : ℕ} (a : Fin (s + 1) → Pt) : plPath a 0 = a 0 := by
  unfold plPath
  refine (add_eq_left.2 (Finset.sum_eq_zero fun j _ => ?_))
  rw [mul_zero, zero_sub, max_eq_left (min_le_of_right_le (by
    have := (Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j); linarith)), zero_smul]

theorem plPath_one {s : ℕ} (hs : 0 < s) (a : Fin (s + 1) → Pt) :
    plPath a 1 = a (Fin.last s) := by
  have hcast : ((s - 1 : ℕ) : ℝ) = s - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hs.ne'), Nat.cast_one]
  rw [plPath_piece a (j := s - 1) (Nat.sub_lt hs one_pos) (by rw [hcast]; linarith)
    (by rw [hcast]; linarith), hcast]
  have e : s - 1 + 1 = s := by omega
  rw [show (s : ℝ) * 1 - (s - 1) = 1 by ring, sub_self, zero_smul, zero_add, one_smul, e,
    finExt_of_le a le_rfl]
  rfl

theorem plPath_at {s : ℕ} (hs : 0 < s) (a : Fin (s + 1) → Pt) (k : Fin (s + 1)) :
    plPath a ((k : ℝ) / s) = a k := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rcases Nat.lt_or_ge k.val s with h | h
  · have e : (s : ℝ) * ((k.val : ℝ) / s) = k.val := mul_div_cancel₀ _ hs'.ne'
    rw [plPath_piece a h (by rw [e]) (by rw [e]; linarith), e, sub_self, sub_zero, one_smul,
      zero_smul, add_zero, finExt_of_le a h.le]
  · have hk : k = Fin.last s := Fin.ext (le_antisymm (Nat.lt_succ_iff.1 k.2) h)
    rw [hk, Fin.val_last, div_self hs'.ne', plPath_one hs]

/-- Values of `plPath` lie in the segments between consecutive vertices. -/
theorem plPath_mem_segment {s : ℕ} {j : ℕ} {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1)
    (a : Fin (s + 1) → Pt) :
    (1 - l) • finExt a j + l • finExt a (j + 1) ∈ segment ℝ (finExt a j) (finExt a (j + 1)) :=
  ⟨1 - l, l, by linarith [hl.2], hl.1, by ring, rfl⟩

theorem plPath_fst_nonneg {s : ℕ} (hs : 0 < s) {a : Fin (s + 1) → Pt} (haR : ∀ j, 0 ≤ (a j).1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (plPath a t).1 := by
  obtain ⟨j, -, l, hl, -, h⟩ := plPath_eq_piece hs ht
  rw [h a]
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  have h1 := haR ⟨min j s, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have h2 := haR ⟨min (j + 1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩
  simp only [finExt]
  nlinarith [hl.1, hl.2]

/-- A convex combination with the same weights moves by at most the larger displacement. -/
theorem dist_combo_le' {x y x' y' : Pt} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    dist (α • x + β • y) (α • x' + β • y') ≤ max (dist x x') (dist y y') := by
  calc dist (α • x + β • y) (α • x' + β • y')
      ≤ dist (α • x) (α • x') + dist (β • y) (β • y') := dist_add_add_le _ _ _ _
    _ = α * dist x x' + β * dist y y' := by
        rw [dist_smul₀, dist_smul₀, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
    _ ≤ α * max (dist x x') (dist y y') + β * max (dist x x') (dist y y') := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max (dist x x') (dist y y') := by rw [← add_mul, hαβ, one_mul]

theorem dist_combo_le {x y x' y' : Pt} {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    dist ((1 - l) • x + l • y) ((1 - l) • x' + l • y') ≤ max (dist x x') (dist y y') :=
  dist_combo_le' (by linarith [hl.2]) hl.1 (by ring)

/-- `‖f t − g t‖ ≤ ε` on `[0, 1]`. -/
theorem dist_plPath_le {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt} {ε : ℝ}
    (hab : ∀ j, dist (a j) (b j) ≤ ε) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (plPath a t) (plPath b t) ≤ ε := by
  obtain ⟨j, -, l, hl, -, h⟩ := plPath_eq_piece hs ht
  rw [h a, h b]
  exact (dist_combo_le hl).trans (max_le (hab _) (hab _))

/-- Within a piece, the segment between two values of `plPath` lies on the path. -/
theorem segment_plPath_subset {s : ℕ} (a : Fin (s + 1) → Pt) {j : ℕ} (hj : j < s) {u u' : ℝ}
    (hu : (j : ℝ) ≤ s * u) (hu' : (s : ℝ) * u ≤ j + 1) (hv : (j : ℝ) ≤ s * u')
    (hv' : (s : ℝ) * u' ≤ j + 1) :
    segment ℝ (plPath a u) (plPath a u') ⊆ plPath a '' Icc 0 1 := by
  rintro z ⟨α, β, hα, hβ, hαβ, rfl⟩
  set w := α * u + β * u'
  have hw : (j : ℝ) ≤ s * w ∧ (s : ℝ) * w ≤ j + 1 := by
    simp only [w]
    constructor <;> nlinarith
  refine ⟨w, piece_mem_Icc hj hw.1 hw.2, ?_⟩
  rw [plPath_piece a hj hw.1 hw.2, plPath_piece a hj hu hu', plPath_piece a hj hv hv']
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  simp only [w]
  module

/-! ## The polygon `S_t` -/

theorem stripPoly_continuous {s : ℕ} (a b : Fin (s + 1) → Pt) (k : Fin (2 * s + 2)) :
    Continuous fun t => stripPoly a b t k := by
  unfold stripPoly
  split_ifs
  · exact (continuous_plPath a).comp (continuous_id.min continuous_const)
  · exact (continuous_plPath b).comp (continuous_id.min continuous_const)

/-- On a piece of the path, `[f(min(t, k/s)), f(min(t, (k+1)/s))]` lies on `f[0, 1]`. -/
theorem segment_min_subset {s : ℕ} (hs : 0 < s) (a : Fin (s + 1) → Pt) {k : ℕ} (hk : k < s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segment ℝ (plPath a (min t ((k : ℝ) / s))) (plPath a (min t (((k + 1 : ℕ) : ℝ) / s))) ⊆
      plPath a '' Icc 0 1 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rcases lt_or_ge t ((k : ℝ) / s) with h | h
  · have h' : t < (((k + 1 : ℕ) : ℝ)) / s := lt_of_lt_of_le h
      (div_le_div_of_nonneg_right (by push_cast; linarith) hs'.le)
    rw [min_eq_left h.le, min_eq_left h'.le, segment_same]
    exact singleton_subset_iff.2 ⟨t, ht, rfl⟩
  · have hsk : (s : ℝ) * ((k : ℝ) / s) = k := mul_div_cancel₀ _ hs'.ne'
    have hsk1 : (s : ℝ) * (((k + 1 : ℕ) : ℝ) / s) = k + 1 := by
      rw [mul_div_cancel₀ _ hs'.ne']; push_cast; ring
    rw [min_eq_right h]
    have hst : (k : ℝ) ≤ s * t := by
      have := mul_le_mul_of_nonneg_left h hs'.le; rwa [hsk] at this
    refine segment_plPath_subset a hk (by rw [hsk]) (by rw [hsk]; linarith) ?_ ?_
    · rcases le_total t (((k + 1 : ℕ) : ℝ) / s) with h2 | h2
      · rw [min_eq_left h2]; exact hst
      · rw [min_eq_right h2, hsk1]; linarith
    · rcases le_total t (((k + 1 : ℕ) : ℝ) / s) with h2 | h2
      · rw [min_eq_left h2]
        have := mul_le_mul_of_nonneg_left h2 hs'.le; rwa [hsk1] at this
      · rw [min_eq_right h2, hsk1]

/-- **The edges of `S_t`.** -/
theorem stripPoly_edge_cases {s : ℕ} (hs : 0 < s) (a b : Fin (s + 1) → Pt) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin (2 * s + 2)) :
    (i.val ≠ 2 * s + 1 ∧ i.val ≠ s ∧
      segment ℝ (stripPoly a b t i)
        (stripPoly a b t ⟨(i.val + 1) % (2 * s + 2), Nat.mod_lt _ (Fin.pos i)⟩) ⊆
        plPath a '' Icc 0 1 ∪ plPath b '' Icc 0 1) ∨
      (i.val = s ∧ stripPoly a b t i = plPath a t ∧
        stripPoly a b t ⟨(i.val + 1) % (2 * s + 2), Nat.mod_lt _ (Fin.pos i)⟩ = plPath b t) ∨
      (i.val = 2 * s + 1 ∧ stripPoly a b t i = b 0 ∧
        stripPoly a b t ⟨(i.val + 1) % (2 * s + 2), Nat.mod_lt _ (Fin.pos i)⟩ = a 0) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨k, hk⟩ := i
  simp only
  rcases Nat.lt_or_ge k s with h | h
  · -- an edge of `f`
    left
    refine ⟨by omega, by omega, ?_⟩
    have e : (k + 1) % (2 * s + 2) = k + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [stripPoly, e, if_pos h.le, if_pos (Nat.succ_le_of_lt h)]
    exact (segment_min_subset hs a h ht).trans subset_union_left
  rcases Nat.eq_or_lt_of_le h with h | h
  · -- `B_t`
    subst h
    right; left
    have e : (s + 1) % (2 * s + 2) = s + 1 := Nat.mod_eq_of_lt (by omega)
    have e' : 2 * s + 1 - (s + 1) = s := by omega
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stripPoly, if_pos le_rfl, div_self hs'.ne', min_eq_left ht.2]
    · simp only [stripPoly, e, if_neg (Nat.not_succ_le_self s), e', div_self hs'.ne',
        min_eq_left ht.2]
  rcases Nat.lt_or_ge k (2 * s + 1) with h' | h'
  · -- an edge of `g`
    left
    refine ⟨by omega, by omega, ?_⟩
    have e : (k + 1) % (2 * s + 2) = k + 1 := Nat.mod_eq_of_lt (by omega)
    have e1 : 2 * s + 1 - k = (2 * s - k) + 1 := by omega
    have e2 : 2 * s + 1 - (k + 1) = 2 * s - k := by omega
    simp only [stripPoly, e, if_neg (by omega : ¬ k ≤ s), if_neg (by omega : ¬ k + 1 ≤ s), e1, e2]
    rw [segment_symm]
    exact (segment_min_subset hs b (k := 2 * s - k) (by omega) ht).trans subset_union_right
  · -- `B₀`
    have hk' : k = 2 * s + 1 := by omega
    subst hk'
    right; right
    have e : (2 * s + 1 + 1) % (2 * s + 2) = 0 := by
      rw [show 2 * s + 1 + 1 = 2 * s + 2 by ring, Nat.mod_self]
    have e' : 2 * s + 1 - (2 * s + 1) = 0 := by omega
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stripPoly, if_neg (by omega : ¬ 2 * s + 1 ≤ s), e', Nat.cast_zero, zero_div,
        min_eq_right ht.1, plPath_zero]
    · simp only [stripPoly, e, if_pos (Nat.zero_le s), Nat.cast_zero, zero_div,
        min_eq_right ht.1, plPath_zero]

/-- `S_t ⊆ f[0, 1] ∪ g[0, 1] ∪ B_t ∪ B₀`. -/
theorem polygonOf_stripPoly_subset {s : ℕ} (hs : 0 < s) (a b : Fin (s + 1) → Pt) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    polygonOf (stripPoly a b t) ⊆ (plPath a '' Icc 0 1 ∪ plPath b '' Icc 0 1) ∪
      segment ℝ (plPath a t) (plPath b t) ∪ segment ℝ (a 0) (b 0) := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  rcases stripPoly_edge_cases hs a b ht i with ⟨-, -, h⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · exact Or.inl (Or.inl (h hi))
  · rw [h1, h2] at hi; exact Or.inl (Or.inr hi)
  · rw [h1, h2, segment_symm] at hi; exact Or.inr hi

/-- The vertices of `S_t` lie in `{x ≥ 0}`. -/
theorem stripPoly_fst_nonneg {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt}
    (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (k : Fin (2 * s + 2)) : 0 ≤ (stripPoly a b t k).1 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  unfold stripPoly
  split_ifs
  · exact plPath_fst_nonneg hs haR ⟨le_min ht.1 (by positivity), (min_le_left _ _).trans ht.2⟩
  · exact plPath_fst_nonneg hs hbR ⟨le_min ht.1 (by positivity), (min_le_left _ _).trans ht.2⟩

/-- Left of `x = 0` the parity of `S_t` is `0` (§3.1 with the convex hull of the vertices). -/
theorem parity_stripPoly_left {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt}
    (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {z : Pt} (hz : z.1 < 0) : parity (stripPoly a b t) z = 0 := by
  have hhalf : Convex ℝ {z : Pt | 0 ≤ z.1} :=
    convex_halfSpace_ge (LinearMap.fst ℝ ℝ ℝ).isLinear 0
  refine parity_eq_zero_of_not_mem_convex _ (convex_convexHull ℝ _)
    (finite_range _).isCompact_convexHull (fun i => subset_convexHull ℝ _ (mem_range_self i)) ?_
  intro hmem
  have := convexHull_min (fun w hw => by
    obtain ⟨i, rfl⟩ := hw; exact stripPoly_fst_nonneg hs haR hbR ht i) hhalf hmem
  simp only [mem_setOf_eq] at this; linarith

/-- `S_0` lies on `B₀`, so its parity vanishes off `x = 0`. -/
theorem parity_stripPoly_zero_of_fst_ne {s : ℕ} (a b : Fin (s + 1) → Pt) (ha0 : (a 0).1 = 0)
    (hb0 : (b 0).1 = 0) {z : Pt} (hz : z.1 ≠ 0) : parity (stripPoly a b 0) z = 0 := by
  refine parity_eq_zero_of_not_mem_convex _ (convex_segment (a 0) (b 0))
    (isCompact_segment' _ _) (fun k => ?_) ?_
  · unfold stripPoly
    split_ifs
    · rw [min_eq_left (by positivity), plPath_zero]; exact left_mem_segment ℝ _ _
    · rw [min_eq_left (by positivity), plPath_zero]; exact right_mem_segment ℝ _ _
  · intro hzs
    obtain ⟨h1, -⟩ := mem_segment_coords hzs
    rw [ha0, hb0, uIcc_self] at h1
    exact hz h1

/-! ## §5.2: O–T Lemma 2.2 -/

/-- Moving the vertices by at most `ρ` keeps the polygon within `ρ` of the old one. -/
theorem infDist_polygonOf_le {n : ℕ} {v w : Fin n → Pt} {ρ : ℝ}
    (hvw : ∀ i, dist (v i) (w i) ≤ ρ) {z : Pt} (hz : z ∈ polygonOf w) :
    infDist z (polygonOf v) ≤ ρ := by
  obtain ⟨i, α, β, hα, hβ, hαβ, rfl⟩ := mem_iUnion.1 hz
  set j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩
  have hy : α • v i + β • v j ∈ polygonOf v := mem_iUnion.2 ⟨i, α, β, hα, hβ, hαβ, rfl⟩
  refine (infDist_le_dist_of_mem hy).trans ?_
  rw [dist_comm]
  exact (dist_combo_le' hα hβ hαβ).trans (max_le (hvw i) (hvw j))

theorem polygonOf_nonempty {n : ℕ} (hn : 0 < n) (v : Fin n → Pt) : (polygonOf v).Nonempty :=
  ⟨v ⟨0, hn⟩, mem_iUnion.2 ⟨⟨0, hn⟩, left_mem_segment ℝ _ _⟩⟩

/-- **§5.2, O–T Lemma 2.2**: near `(t₀, z₀)` with `z₀ ∉ S_{t₀}`, the point `z` is off `S_t` and the
parity of `S_t` at `z` is that of `S_{t₀}` at `z₀`. -/
theorem parity_strip_eventually {s : ℕ} (a b : Fin (s + 1) → Pt) {t₀ : ℝ} {z₀ : Pt}
    (hz₀ : z₀ ∉ polygonOf (stripPoly a b t₀)) :
    ∀ᶠ x in 𝓝 (t₀, z₀), x.2 ∉ polygonOf (stripPoly a b x.1) ∧
      parity (stripPoly a b x.1) x.2 = parity (stripPoly a b t₀) z₀ := by
  set v := stripPoly a b t₀
  have hne := polygonOf_nonempty (Nat.succ_pos (2 * s + 1)) v
  have hd : 0 < infDist z₀ (polygonOf v) :=
    ((isClosed_polygonOf v).notMem_iff_infDist_pos hne).1 hz₀
  set d := infDist z₀ (polygonOf v)
  have hvert : ∀ᶠ t in 𝓝 t₀, ∀ k, dist (stripPoly a b t k) (v k) < d / 4 :=
    eventually_all.2 fun k => ((stripPoly_continuous a b k).tendsto t₀).eventually
      (ball_mem_nhds _ (div_pos hd (by norm_num)))
  have hz : ∀ᶠ z in 𝓝 z₀, dist z z₀ < d / 4 ∧ parity v z = parity v z₀ :=
    Filter.Eventually.and (show ∀ᶠ z in 𝓝 z₀, dist z z₀ < d / 4 from
      ball_mem_nhds z₀ (div_pos hd (by norm_num))) (parity_eventually_eq v hz₀)
  rw [nhds_prod_eq]
  filter_upwards [hvert.prod_mk hz] with x ⟨hx1, hx2, hx3⟩
  have hfar : d / 4 < infDist x.2 (polygonOf v) := by
    have := infDist_le_infDist_add_dist (x := z₀) (y := x.2) (s := polygonOf v)
    rw [dist_comm] at this
    linarith
  have hvw : ∀ k, dist (v k) (stripPoly a b x.1 k) ≤ d / 4 := fun k => by
    rw [dist_comm]; exact (hx1 k).le
  refine ⟨fun hmem => ?_, ?_⟩
  · have := infDist_polygonOf_le hvw hmem
    linarith
  · rw [← parity_eq_of_perturb v _ hvw hfar, hx3]

/-! ## Distance to a moving segment -/

/-- The distance to a segment moves by at most the displacement of the point plus that of the
ends. -/
theorem infDist_segment_le (z z' p q p' q' : Pt) :
    infDist z (segment ℝ p q) ≤
      infDist z' (segment ℝ p' q') + dist z z' + max (dist p p') (dist q q') := by
  have h1 := infDist_le_infDist_add_dist (x := z) (y := z') (s := segment ℝ p q)
  suffices h2 : infDist z' (segment ℝ p q) ≤ infDist z' (segment ℝ p' q') +
      max (dist p p') (dist q q') by linarith
  by_contra hlt
  push_neg at hlt
  obtain ⟨y', hy', hdy'⟩ := (infDist_lt_iff ⟨p', left_mem_segment ℝ _ _⟩).1
    (show infDist z' (segment ℝ p' q') < infDist z' (segment ℝ p q) - max (dist p p') (dist q q')
      by linarith)
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy'
  have hy : (α • p + β • q) ∈ segment ℝ p q := ⟨α, β, hα, hβ, hαβ, rfl⟩
  have h3 := infDist_le_dist_of_mem hy (x := z')
  have h4 : dist (α • p + β • q) (α • p' + β • q') ≤ max (dist p p') (dist q q') :=
    dist_combo_le' hα hβ hαβ
  have h5 := dist_triangle z' (α • p' + β • q') (α • p + β • q)
  rw [dist_comm (α • p' + _)] at h5
  linarith

theorem continuous_infDist_segment :
    Continuous fun x : Pt × Pt × Pt => infDist x.1 (segment ℝ x.2.1 x.2.2) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun x y => ?_).continuous
  rw [Real.dist_eq, abs_le]
  have hxy : dist x y = max (dist x.1 y.1) (max (dist x.2.1 y.2.1) (dist x.2.2 y.2.2)) := by
    rw [Prod.dist_eq (x := x) (y := y), Prod.dist_eq (x := x.2) (y := y.2)]
  have h1 := infDist_segment_le x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2
  have h2 := infDist_segment_le y.1 x.1 y.2.1 y.2.2 x.2.1 x.2.2
  rw [dist_comm y.1, dist_comm y.2.1, dist_comm y.2.2] at h2
  have hm1 : dist x.1 y.1 ≤ dist x y := by rw [hxy]; exact le_max_left _ _
  have hm2 : max (dist x.2.1 y.2.1) (dist x.2.2 y.2.2) ≤ dist x y := by
    rw [hxy]; exact le_max_right _ _
  push_cast
  constructor <;> linarith

/-! ## §5.3: the sign function -/

/-- `z` is on `x = 0`, or off `S_t` with parity `1`. -/
def StripInner {s : ℕ} (a b : Fin (s + 1) → Pt) (t : ℝ) (z : Pt) : Prop :=
  z.1 = 0 ∨ (z ∉ polygonOf (stripPoly a b t) ∧ parity (stripPoly a b t) z = 1)

open Classical in
/-- **The sign function** `φ_h(t, u) = ∓ dist(h u, B_t)`, negative when `h u` is inner. -/
noncomputable def stripSign {s : ℕ} (a b : Fin (s + 1) → Pt) (h : ℝ → Pt) (x : ℝ × ℝ) : ℝ :=
  (if StripInner a b x.1 (h x.2) then -1 else 1) *
    infDist (h x.2) (segment ℝ (plPath a x.1) (plPath b x.1))

/-- Points of the line `x = c` strictly between two others lie in the open segment. -/
theorem mem_openSegment_vertical {p q z : Pt} {c : ℝ} (hp : p.1 = c) (hq : q.1 = c) (hz : z.1 = c)
    (h : (p.2 < z.2 ∧ z.2 < q.2) ∨ (q.2 < z.2 ∧ z.2 < p.2)) : z ∈ openSegment ℝ p q := by
  have hne : q.2 - p.2 ≠ 0 := by rcases h with h | h <;> intro h' <;> linarith [h.1, h.2]
  set l := (z.2 - p.2) / (q.2 - p.2)
  have hl0 : 0 < l := by
    rcases h with h | h
    · exact div_pos (by linarith [h.1]) (by linarith [h.1, h.2])
    · exact div_pos_of_neg_of_neg (by linarith [h.1, h.2]) (by linarith [h.1, h.2])
  have hl1 : l < 1 := by
    rcases h with h | h
    · rw [div_lt_one (by linarith [h.1, h.2])]; linarith [h.2]
    · rw [div_lt_one_of_neg (by linarith [h.1, h.2])]; linarith [h.1]
  refine ⟨1 - l, l, by linarith, hl0, by ring, Prod.ext ?_ ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hp, hq, hz]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, l]
    field_simp
    ring

/-- Heights in an open segment on a vertical line are strictly between. -/
theorem height_of_mem_openSegment_vertical {p q z : Pt} (hpq : p.1 = q.1) (hne : p ≠ q)
    (hz : z ∈ openSegment ℝ p q) :
    (p.2 < z.2 ∧ z.2 < q.2) ∨ (q.2 < z.2 ∧ z.2 < p.2) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  have h2 : p.2 ≠ q.2 := fun h => hne (Prod.ext hpq h)
  have hα' : α = 1 - β := by linarith
  subst hα'
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rcases lt_or_gt_of_ne h2 with h | h
  · left; constructor <;> nlinarith [mul_pos hβ (sub_pos.2 h), mul_pos hα (sub_pos.2 h)]
  · right; constructor <;> nlinarith [mul_pos hβ (sub_pos.2 h), mul_pos hα (sub_pos.2 h)]

/-- **§5.3, the key lemma**: near a point off `f[0, 1]`, `g[0, 1]` and `B_{t₀}`, in `{x ≥ 0}` and
meeting `x = 0` only in `B₀`, the predicate `StripInner` is locally constant (on `{x ≥ 0}`). -/
theorem stripInner_eventually {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt} (ha0 : (a 0).1 = 0)
    (hb0 : (b 0).1 = 0) (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) {z₀ : Pt} (hz₀R : 0 ≤ z₀.1) (hz₀f : z₀ ∉ plPath a '' Icc 0 1)
    (hz₀g : z₀ ∉ plPath b '' Icc 0 1) (hz₀B : z₀ ∉ segment ℝ (plPath a t₀) (plPath b t₀))
    (hz₀L : z₀.1 = 0 → z₀ ∈ segment ℝ (a 0) (b 0)) :
    ∀ᶠ x in 𝓝 (t₀, z₀), x.1 ∈ Icc (0 : ℝ) 1 → 0 ≤ x.2.1 →
      (StripInner a b x.1 x.2 ↔ StripInner a b t₀ z₀) := by
  rcases lt_or_eq_of_le hz₀R with hpos | hzero
  · -- off the line `x = 0`
    have hz₀P : z₀ ∉ polygonOf (stripPoly a b t₀) := by
      intro hmem
      rcases polygonOf_stripPoly_subset hs a b ht₀ hmem with (h | h) | h
      · rcases h with h | h
        · exact hz₀f h
        · exact hz₀g h
      · exact hz₀B h
      · obtain ⟨h1, -⟩ := mem_segment_coords h
        rw [ha0, hb0, uIcc_self] at h1
        exact hpos.ne' h1
    have hfst : ∀ᶠ x in 𝓝 (t₀, z₀), 0 < x.2.1 :=
      continuousAt_const.eventually_lt (continuous_fst.comp continuous_snd).continuousAt hpos
    filter_upwards [parity_strip_eventually a b hz₀P, hfst] with x ⟨hx1, hx2⟩ hx3 _ _
    unfold StripInner
    rw [hx2]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h hx3.ne'
      · exact Or.inr ⟨hz₀P, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact absurd h hpos.ne'
      · exact Or.inr ⟨hx1, h⟩
  · -- on the line `x = 0`: inside `B₀`
    have hz₀1 : z₀.1 = 0 := hzero.symm
    have hz₀B₀ := hz₀L hz₀1
    have ha0f : a 0 ∈ plPath a '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, plPath_zero a⟩
    have hb0g : b 0 ∈ plPath b '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, plPath_zero b⟩
    have hz₀a : z₀ ≠ a 0 := fun h => hz₀f (h ▸ ha0f)
    have hz₀b : z₀ ≠ b 0 := fun h => hz₀g (h ▸ hb0g)
    have hz₀o : z₀ ∈ openSegment ℝ (a 0) (b 0) :=
      mem_openSegment_of_ne_left_right hz₀a.symm hz₀b.symm hz₀B₀
    have hab0 : a 0 ≠ b 0 := by
      intro h; rw [h, openSegment_same] at hz₀o; exact hz₀b hz₀o
    set E := plPath a '' Icc 0 1 ∪ plPath b '' Icc 0 1
    have hEc : IsClosed E := ((isCompact_Icc.image (continuous_plPath a)).union
      (isCompact_Icc.image (continuous_plPath b))).isClosed
    have hEne : E.Nonempty := ⟨a 0, Or.inl ha0f⟩
    have hr₁ : 0 < infDist z₀ E :=
      (hEc.notMem_iff_infDist_pos hEne).1 (fun h => h.elim hz₀f hz₀g)
    have hr₂ : 0 < infDist z₀ (segment ℝ (plPath a t₀) (plPath b t₀)) :=
      ((isCompact_segment' _ _).isClosed.notMem_iff_infDist_pos
        ⟨_, left_mem_segment ℝ _ _⟩).1 hz₀B
    set r := min (infDist z₀ E) (infDist z₀ (segment ℝ (plPath a t₀) (plPath b t₀)))
    have hr : 0 < r := lt_min hr₁ hr₂
    -- the moving segment stays away
    have hBt : ∀ᶠ t in 𝓝 t₀, r / 2 < infDist z₀ (segment ℝ (plPath a t) (plPath b t)) := by
      have hc : Continuous fun t => infDist z₀ (segment ℝ (plPath a t) (plPath b t)) :=
        continuous_infDist_segment.comp
          (f := fun t : ℝ => ((z₀, plPath a t, plPath b t) : Pt × Pt × Pt))
          (continuous_const.prodMk ((continuous_plPath a).prodMk (continuous_plPath b)))
      have h0 : r / 2 < infDist z₀ (segment ℝ (plPath a t₀) (plPath b t₀)) := by
        have := min_le_right (infDist z₀ E) (infDist z₀ (segment ℝ (plPath a t₀) (plPath b t₀)))
        linarith
      exact hc.continuousAt.eventually (lt_mem_nhds h0)
    have hev : ∀ᶠ x in 𝓝 (t₀, z₀), r / 2 < infDist z₀ (segment ℝ (plPath a x.1) (plPath b x.1)) ∧
        x.2 ∈ ball z₀ (r / 4) := by
      rw [nhds_prod_eq]
      exact hBt.prod_mk (show ∀ᶠ y in 𝓝 z₀, y ∈ ball z₀ (r / 4) from
        ball_mem_nhds z₀ (div_pos hr (by norm_num)))
    filter_upwards [hev] with x ⟨hxB, hxz⟩ hxt hx0
    rw [mem_ball] at hxz
    refine iff_of_true ?_ (Or.inl hz₀1)
    rcases lt_or_eq_of_le hx0 with hxpos | hxzero
    swap
    · exact Or.inl hxzero.symm
    right
    -- every point of `f`, `g`, `B_t` is farther than `r / 2` from `z₀`
    have hfarE : ∀ y ∈ E ∪ segment ℝ (plPath a x.1) (plPath b x.1), r / 2 < dist y z₀ := by
      intro y hy
      rw [dist_comm]
      rcases hy with hy | hy
      · have := infDist_le_dist_of_mem hy (x := z₀)
        have : r ≤ infDist z₀ E := min_le_left _ _
        linarith
      · have := infDist_le_dist_of_mem hy (x := z₀)
        linarith
    have hdz : dist x.2 z₀ < r / 4 := hxz
    have hxP : x.2 ∉ polygonOf (stripPoly a b x.1) := by
      intro hmem
      rcases polygonOf_stripPoly_subset hs a b hxt hmem with (h | h) | h
      · have := hfarE _ (Or.inl h); linarith
      · have := hfarE _ (Or.inr h); linarith
      · obtain ⟨h1, -⟩ := mem_segment_coords h
        rw [ha0, hb0, uIcc_self] at h1
        exact hxpos.ne' h1
    refine ⟨hxP, ?_⟩
    -- the flip across `B₀`
    set i : Fin (2 * s + 2) := ⟨2 * s + 1, by omega⟩
    obtain ⟨-, hvi, hvi'⟩ : i.val = 2 * s + 1 ∧ stripPoly a b x.1 i = b 0 ∧
        stripPoly a b x.1 ⟨(i.val + 1) % (2 * s + 2), Nat.mod_lt _ (Fin.pos i)⟩ = a 0 := by
      rcases stripPoly_edge_cases hs a b hxt i with ⟨h, -⟩ | ⟨h, -⟩ | h
      · exact absurd rfl h
      · simp only [i] at h; omega
      · exact h
    set bb : Pt := (0, x.2.2)
    have hdbz : dist bb z₀ < r / 4 := by
      refine lt_of_le_of_lt ?_ hdz
      rw [Prod.dist_eq, Prod.dist_eq]
      simp only [bb, hz₀1, dist_self]
      exact max_le (dist_nonneg.trans (le_max_left _ _)) (le_max_right _ _)
    have hbb : bb ∈ openSegment ℝ (b 0) (a 0) := by
      have hh := height_of_mem_openSegment_vertical (ha0.trans hb0.symm) hab0 hz₀o
      have hda : r / 2 < |(a 0).2 - z₀.2| := by
        have := hfarE (a 0) (Or.inl (Or.inl ha0f))
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, ha0, hz₀1, sub_self, abs_zero,
          max_eq_right (abs_nonneg _)] at this
        exact this
      have hdb : r / 2 < |(b 0).2 - z₀.2| := by
        have := hfarE (b 0) (Or.inl (Or.inr hb0g))
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hb0, hz₀1, sub_self, abs_zero,
          max_eq_right (abs_nonneg _)] at this
        exact this
      have hdbb : |bb.2 - z₀.2| < r / 4 := by
        refine lt_of_le_of_lt ?_ hdbz
        rw [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
      refine mem_openSegment_vertical hb0 ha0 rfl ?_
      simp only [bb] at hdbb ⊢
      have hy := abs_sub_lt_iff.1 hdbb
      rcases lt_abs.1 hda with ha | ha <;> rcases lt_abs.1 hdb with hb | hb <;>
        rcases hh with h | h <;>
        first
          | (left; constructor <;> linarith [h.1, h.2, hy.1, hy.2])
          | (right; constructor <;> linarith [h.1, h.2, hy.1, hy.2])
    have hfar : ∀ j : Fin (2 * s + 2), j ≠ i → ∀ y ∈ polyEdge (stripPoly a b x.1) j,
        r / 4 < dist y bb := by
      intro j hj y hy
      have hyE : y ∈ E ∪ segment ℝ (plPath a x.1) (plPath b x.1) := by
        rcases stripPoly_edge_cases hs a b hxt j with ⟨-, -, h⟩ | ⟨-, h1, h2⟩ | ⟨h, -⟩
        · exact Or.inl (h hy)
        · unfold polyEdge at hy; rw [h1, h2] at hy; exact Or.inr hy
        · exact absurd (Fin.ext h) hj
      have h1 := hfarE y hyE
      have h2 := dist_triangle y bb z₀
      linarith
    have hx1 : x.2.1 < r / 4 := by
      refine lt_of_le_of_lt ?_ hdz
      rw [Prod.dist_eq, Real.dist_eq, hz₀1, sub_zero, abs_of_pos hxpos]
      exact le_max_left _ _
    have hflip := parity_flip_vertical_edge (stripPoly a b x.1) i (c := 0)
      (by rw [hvi, hb0]) (by rw [hvi', ha0]) (by rw [hvi, hvi']; exact hab0.symm)
      (by rw [hvi, hvi']; exact hbb) hfar hxpos hx1
    rw [parity_stripPoly_left hs haR hbR hxt (z := (0 - x.2.1, x.2.2))
      (show 0 - x.2.1 < 0 by linarith), zero_add] at hflip
    simp only [bb] at hflip
    have hxeq : ((x.2.1, x.2.2) : Pt) = x.2 := rfl
    rw [hxeq] at hflip
    generalize parity (stripPoly a b x.1) x.2 = w at hflip ⊢
    fin_cases w
    · exact absurd rfl hflip
    · rfl

/-- **§5.3, continuity of the sign function** for a path `h` in `{x ≥ 0}`, off `f[0, 1]` and
`g[0, 1]`, meeting `x = 0` only in `B₀`. -/
theorem stripSign_continuousOn {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt} (ha0 : (a 0).1 = 0)
    (hb0 : (b 0).1 = 0) (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1) {h : ℝ → Pt}
    (hc : ContinuousOn h (Icc 0 1)) (hR : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ (h u).1)
    (hf : ∀ u ∈ Icc (0 : ℝ) 1, h u ∉ plPath a '' Icc 0 1)
    (hg : ∀ u ∈ Icc (0 : ℝ) 1, h u ∉ plPath b '' Icc 0 1)
    (hL : ∀ u ∈ Icc (0 : ℝ) 1, (h u).1 = 0 → h u ∈ segment ℝ (a 0) (b 0)) :
    ContinuousOn (stripSign a b h) (Icc 0 1 ×ˢ Icc 0 1) := by
  classical
  set D : ℝ × ℝ → ℝ := fun x => infDist (h x.2) (segment ℝ (plPath a x.1) (plPath b x.1))
  have hpair : ContinuousOn (fun x : ℝ × ℝ => (x.1, h x.2)) (Icc 0 1 ×ˢ Icc 0 1) :=
    continuousOn_fst.prodMk (hc.comp continuousOn_snd fun x hx => hx.2)
  have hD : ContinuousOn D (Icc 0 1 ×ˢ Icc 0 1) := by
    have : ContinuousOn (fun x : ℝ × ℝ => ((h x.2, plPath a x.1, plPath b x.1) : Pt × Pt × Pt))
        (Icc 0 1 ×ˢ Icc 0 1) :=
      (hc.comp continuousOn_snd fun x hx => hx.2).prodMk
        (((continuous_plPath a).comp continuous_fst).continuousOn.prodMk
          ((continuous_plPath b).comp continuous_fst).continuousOn)
    exact continuous_infDist_segment.comp_continuousOn
      (f := fun x : ℝ × ℝ => ((h x.2, plPath a x.1, plPath b x.1) : Pt × Pt × Pt)) this
  intro x₀ hx₀
  by_cases hD0 : D x₀ = 0
  · -- the sign does not matter where the distance vanishes
    have habs : ∀ x, |stripSign a b h x| = D x := fun x => by
      unfold stripSign
      rw [abs_mul, abs_of_nonneg infDist_nonneg]
      split_ifs <;> simp only [abs_neg, abs_one, one_mul, D]
    have hval : stripSign a b h x₀ = 0 := by
      rw [← abs_eq_zero, habs, hD0]
    rw [ContinuousWithinAt, hval]
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
    have hcomp : (abs ∘ stripSign a b h) = D := funext habs
    rw [hcomp]
    have := hD x₀ hx₀
    rw [ContinuousWithinAt, hD0] at this
    exact this
  · have hz₀B : h x₀.2 ∉ segment ℝ (plPath a x₀.1) (plPath b x₀.1) := fun hm =>
      hD0 (infDist_zero_of_mem hm)
    have hev := stripInner_eventually hs ha0 hb0 haR hbR hx₀.1 (hR _ hx₀.2) (hf _ hx₀.2)
      (hg _ hx₀.2) hz₀B (hL _ hx₀.2)
    have hev' : ∀ᶠ x in 𝓝[Icc 0 1 ×ˢ Icc 0 1] x₀,
        StripInner a b x.1 (h x.2) ↔ StripInner a b x₀.1 (h x₀.2) := by
      have := (hpair x₀ hx₀).tendsto
      filter_upwards [this.eventually hev, self_mem_nhdsWithin] with x hx hxS
      exact hx hxS.1 (hR _ hxS.2)
    refine ContinuousWithinAt.congr_of_eventuallyEq
      (f := fun x => (if StripInner a b x₀.1 (h x₀.2) then (-1 : ℝ) else 1) * D x)
      (continuousWithinAt_const.mul (hD x₀ hx₀)) ?_ rfl
    filter_upwards [hev'] with x hx
    simp only [stripSign, D]
    rw [if_congr hx rfl rfl]

/-- At `t = 0` the sign function is `≥ 0`. -/
theorem stripSign_zero_nonneg {s : ℕ} {a b : Fin (s + 1) → Pt} (ha0 : (a 0).1 = 0)
    (hb0 : (b 0).1 = 0) {h : ℝ → Pt} {u : ℝ}
    (hL : (h u).1 = 0 → h u ∈ segment ℝ (a 0) (b 0)) : 0 ≤ stripSign a b h (0, u) := by
  classical
  unfold stripSign
  simp only
  split_ifs with hin
  · by_cases h0 : (h u).1 = 0
    · rw [plPath_zero, plPath_zero, infDist_zero_of_mem (hL h0), mul_zero]
    · rcases hin with h0' | ⟨-, hpar⟩
      · exact absurd h0' h0
      · rw [parity_stripPoly_zero_of_fst_ne a b ha0 hb0 h0] at hpar
        exact absurd hpar (by decide)
  · rw [one_mul]; exact infDist_nonneg

/-- Where `h u` is inner, the sign function is `≤ 0`. -/
theorem stripSign_nonpos_of_inner {s : ℕ} {a b : Fin (s + 1) → Pt} {h : ℝ → Pt} {t u : ℝ}
    (hin : StripInner a b t (h u)) : stripSign a b h (t, u) ≤ 0 := by
  classical
  unfold stripSign
  simp only [if_pos hin, neg_one_mul, neg_nonpos]
  exact infDist_nonneg

/-- The zeros of the sign function. -/
theorem stripSign_eq_zero {s : ℕ} {a b : Fin (s + 1) → Pt} {h : ℝ → Pt} {t u : ℝ}
    (h0 : stripSign a b h (t, u) = 0) : h u ∈ segment ℝ (plPath a t) (plPath b t) := by
  classical
  unfold stripSign at h0
  simp only at h0
  have hD : infDist (h u) (segment ℝ (plPath a t) (plPath b t)) = 0 := by
    split_ifs at h0 <;> linarith
  exact ((isCompact_segment' _ _).isClosed.mem_iff_infDist_zero
    ⟨_, left_mem_segment ℝ _ _⟩).2 hD

/-! ## §5.4: the strip lemma -/

/-- On a preconnected set in the region off `f`, `g` and `B₁` (in `{x ≥ 0}`, meeting `x = 0` only
in `B₀`), `StripInner a b 1` holds everywhere once it holds somewhere. -/
theorem stripInner_one_of_isPreconnected {s : ℕ} (hs : 0 < s) {a b : Fin (s + 1) → Pt}
    (ha0 : (a 0).1 = 0) (hb0 : (b 0).1 = 0) (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1)
    {C : Set Pt} (hC : IsPreconnected C)
    (hreg : ∀ z ∈ C, 0 ≤ z.1 ∧ z ∉ plPath a '' Icc 0 1 ∧ z ∉ plPath b '' Icc 0 1 ∧
      z ∉ segment ℝ (a (Fin.last s)) (b (Fin.last s)) ∧
      (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0)))
    {z₁ : Pt} (hz₁ : z₁ ∈ C) (h₁ : StripInner a b 1 z₁) : ∀ z ∈ C, StripInner a b 1 z := by
  classical
  set χ : Pt → ℕ := fun z => if StripInner a b 1 z then 1 else 0
  have hχ : ContinuousOn χ C := by
    intro z₀ hz₀
    obtain ⟨h0, hf, hg, hB, hL⟩ := hreg z₀ hz₀
    rw [← plPath_one hs a, ← plPath_one hs b] at hB
    have hev := stripInner_eventually hs ha0 hb0 haR hbR ⟨zero_le_one, le_rfl⟩ h0 hf hg hB hL
    have hev' : ∀ᶠ z in 𝓝 z₀, 0 ≤ z.1 → (StripInner a b 1 z ↔ StripInner a b 1 z₀) := by
      have ht : Tendsto (fun z : Pt => ((1 : ℝ), z)) (𝓝 z₀) (𝓝 (1, z₀)) :=
        (continuous_const.prodMk continuous_id).tendsto z₀
      filter_upwards [ht.eventually hev] with z hz hz0
      exact hz ⟨zero_le_one, le_rfl⟩ hz0
    refine (continuousWithinAt_const (b := χ z₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [nhdsWithin_le_nhds hev', self_mem_nhdsWithin] with z hz hzC
    simp only [χ, if_congr (hz (hreg z hzC).1) rfl rfl]
  intro z hz
  have := hC.constant_of_mapsTo (T := (univ : Set ℕ)) IsDiscrete.univ hχ (mapsTo_univ _ _) hz₁ hz
  simp only [χ, if_pos h₁] at this
  by_contra hn
  rw [if_neg hn] at this
  exact one_ne_zero this

/-- An `η`-chain in a preconnected set (constant after its last index). -/
theorem exists_eps_chain {E : Type*} [PseudoMetricSpace E] {C : Set E} (hC : IsPreconnected C)
    {η : ℝ} (hη : 0 < η) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ∃ (m : ℕ) (c : ℕ → E), c 0 = x ∧ c m = y ∧ (∀ j, c j ∈ C) ∧
      ∀ j < m, dist (c j) (c (j + 1)) < η := by
  set R : Set E := {z | ∃ (m : ℕ) (c : ℕ → E), c 0 = x ∧ c m = z ∧ (∀ j, c j ∈ C) ∧
      ∀ j < m, dist (c j) (c (j + 1)) < η}
  have hsnoc : ∀ z ∈ R, ∀ z' ∈ C, dist z z' < η → z' ∈ R := by
    rintro z ⟨m, c, h0, hm, hC', hd⟩ z' hz' hzz'
    refine ⟨m + 1, fun j => if j ≤ m then c j else z', by simp [h0], by simp,
      fun j => by dsimp only; split_ifs; exacts [hC' j, hz'], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j m with hjm | hjm
    · simp only [if_pos hjm.le, if_pos (Nat.succ_le_of_lt hjm)]; exact hd j hjm
    · have : j = m := by omega
      subst this
      simp only [le_refl, if_true, if_neg (Nat.not_succ_le_self j)]
      rw [hm]; exact hzz'
  have hxR : x ∈ R := ⟨0, fun _ => x, rfl, rfl, fun _ => hx, fun j hj => absurd hj (by omega)⟩
  set u := ⋃ z ∈ C ∩ R, ball z η
  set v := ⋃ z ∈ C ∩ Rᶜ, ball z η
  have hcover : C ⊆ u ∪ v := by
    intro c hc
    by_cases h : c ∈ R
    · exact Or.inl (mem_biUnion ⟨hc, h⟩ (mem_ball_self hη))
    · exact Or.inr (mem_biUnion ⟨hc, h⟩ (mem_ball_self hη))
  have hdisj : C ∩ (u ∩ v) = ∅ := by
    ext c
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hc hcu hcv
    obtain ⟨z₁, ⟨-, h₁⟩, hc₁⟩ := mem_iUnion₂.1 hcu
    obtain ⟨z₂, ⟨hz₂, h₂⟩, hc₂⟩ := mem_iUnion₂.1 hcv
    have hcR := hsnoc z₁ h₁ c hc (by rw [dist_comm]; exact hc₁)
    exact h₂ (hsnoc c hcR z₂ hz₂ hc₂)
  rcases isPreconnected_iff_subset_of_disjoint.1 hC u v (isOpen_biUnion fun _ _ => isOpen_ball)
    (isOpen_biUnion fun _ _ => isOpen_ball) hcover hdisj with hCu | hCv
  · obtain ⟨z₁, ⟨-, h₁⟩, hc₁⟩ := mem_iUnion₂.1 (hCu hy)
    exact hsnoc z₁ h₁ y hy (by rw [dist_comm]; exact hc₁)
  · exfalso
    obtain ⟨z₂, ⟨hz₂, h₂⟩, hc₂⟩ := mem_iUnion₂.1 (hCv hx)
    exact h₂ (hsnoc x hxR z₂ hz₂ hc₂)

theorem dist_le_of_mem_segment_left {p q z : Pt} (hz : z ∈ segment ℝ p q) :
    dist z p ≤ dist p q := by
  have := (convex_closedBall p (dist p q)).segment_subset (mem_closedBall_self dist_nonneg)
    (by rw [mem_closedBall, dist_comm]) hz
  exact this

theorem dist_le_of_mem_segment {p q x y : Pt} (hx : x ∈ segment ℝ p q)
    (hy : y ∈ segment ℝ p q) : dist x y ≤ dist p q := by
  have hxp := dist_le_of_mem_segment_left hx
  have hxq : dist x q ≤ dist p q := by
    rw [segment_symm] at hx; rw [dist_comm p q]; exact dist_le_of_mem_segment_left hx
  have := (convex_closedBall x (dist p q)).segment_subset
    (by rw [mem_closedBall, dist_comm]; exact hxp) (by rw [mem_closedBall, dist_comm]; exact hxq) hy
  rw [mem_closedBall, dist_comm] at this
  exact this

/-- **§5.4, the strip lemma** (O–T Theorem 2.7, in the form used): a continuum `W` in the strip
bounded by `B₀ = [a 0, b 0]` on the line `x = 0`, the paths through the `a j` and the `b j`, and
`B₁ = [a s, b s]`, touching `x = 0` only inside `B₀`, has every surjective-span witness meeting
`{d ≤ ε}`. -/
theorem strip_lemma {s : ℕ} (hs : 0 < s) (a b : Fin (s + 1) → Pt) {ε : ℝ}
    (hab : ∀ j, dist (a j) (b j) ≤ ε) (ha0 : (a 0).1 = 0) (hb0 : (b 0).1 = 0)
    (haR : ∀ j, 0 ≤ (a j).1) (hbR : ∀ j, 0 ≤ (b j).1)
    {W : Set Pt} (hW : Fold.Q78.IsContinuum W) (hWR : ∀ z ∈ W, 0 ≤ z.1)
    (hW0 : ∃ z ∈ W, z.1 = 0) (hWB₀ : ∀ z ∈ W, z.1 = 0 → z ∈ openSegment ℝ (a 0) (b 0))
    (hWf : Disjoint W (plPath a '' Icc 0 1)) (hWg : Disjoint W (plPath b '' Icc 0 1))
    (hWB₁ : Disjoint W (segment ℝ (a (Fin.last s)) (b (Fin.last s)))) :
    ∀ Z ⊆ W ×ˢ W, Fold.Q78.IsContinuum Z → Prod.fst '' Z = W → Prod.snd '' Z = W →
      ∃ p ∈ Z, dist p.1 p.2 ≤ ε := by
  intro Z hZW hZ hZ1 hZ2
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₀, hw₀, hw₀0⟩ := hW0
  -- the minimum of `d` on `Z`
  obtain ⟨zA, hzA, hzA1⟩ : ∃ zA ∈ Z, zA.1 = w₀ := by
    rw [← hZ1] at hw₀; exact hw₀
  obtain ⟨zB, hzB, hzB2⟩ : ∃ zB ∈ Z, zB.2 = w₀ := by
    rw [← hZ2] at hw₀; exact hw₀
  obtain ⟨zm, hzm, hzmin⟩ := hZ.1.exists_isMinOn ⟨zA, hzA⟩
    (continuous_fst.dist continuous_snd).continuousOn
  set α := dist zm.1 zm.2
  have hαε : ε < α := hcon zm hzm
  have hαle : ∀ p ∈ Z, α ≤ dist p.1 p.2 := fun p hp => hzmin hp
  -- the distance from `W` to `f`, `g`, `B₁`
  set Kb := (plPath a '' Icc 0 1 ∪ plPath b '' Icc 0 1) ∪
    segment ℝ (a (Fin.last s)) (b (Fin.last s))
  have hKbc : IsClosed Kb := (((isCompact_Icc.image (continuous_plPath a)).union
    (isCompact_Icc.image (continuous_plPath b))).union (isCompact_segment' _ _)).isClosed
  have hKbne : Kb.Nonempty := ⟨a 0, Or.inl (Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, plPath_zero a⟩)⟩
  have hWKb : ∀ w ∈ W, w ∉ Kb := by
    rintro w hw ((h | h) | h)
    · exact disjoint_left.1 hWf hw h
    · exact disjoint_left.1 hWg hw h
    · exact disjoint_left.1 hWB₁ hw h
  obtain ⟨wm, hwm, hwmin⟩ := hW.1.exists_isMinOn ⟨w₀, hw₀⟩ (continuous_infDist_pt Kb).continuousOn
  set δ := infDist wm Kb
  have hδ : 0 < δ := (hKbc.notMem_iff_infDist_pos hKbne).1 (hWKb wm hwm)
  have hδle : ∀ w ∈ W, ∀ y ∈ Kb, δ ≤ dist w y := fun w hw y hy =>
    (hwmin hw).trans (infDist_le_dist_of_mem hy)
  set η := min (δ / 2) ((α - ε) / 3)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηα : η ≤ (α - ε) / 3 := min_le_right _ _
  -- `StripInner a b 1` on `W`
  have hreg : ∀ z : Pt, (∃ w ∈ W, dist z w < η ∧ (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0))) →
      0 ≤ z.1 → 0 ≤ z.1 ∧ z ∉ plPath a '' Icc 0 1 ∧ z ∉ plPath b '' Icc 0 1 ∧
        z ∉ segment ℝ (a (Fin.last s)) (b (Fin.last s)) ∧
        (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0)) := by
    rintro z ⟨w, hw, hzw, hL⟩ h0
    have hoff : ∀ y ∈ Kb, z ≠ y := by
      rintro y hy rfl
      have := hδle w hw z hy
      rw [dist_comm] at this
      linarith
    exact ⟨h0, fun h => hoff z (Or.inl (Or.inl h)) rfl, fun h => hoff z (Or.inl (Or.inr h)) rfl,
      fun h => hoff z (Or.inr h) rfl, hL⟩
  have hWreg : ∀ z ∈ W, 0 ≤ z.1 ∧ z ∉ plPath a '' Icc 0 1 ∧ z ∉ plPath b '' Icc 0 1 ∧
      z ∉ segment ℝ (a (Fin.last s)) (b (Fin.last s)) ∧ (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0)) :=
    fun z hz => hreg z ⟨z, hz, by rw [dist_self]; exact hη,
      fun h => openSegment_subset_segment ℝ _ _ (hWB₀ z hz h)⟩ (hWR z hz)
  have hWin : ∀ z ∈ W, StripInner a b 1 z :=
    stripInner_one_of_isPreconnected hs ha0 hb0 haR hbR hW.2.isPreconnected hWreg hw₀
      (Or.inl hw₀0)
  -- segments of length `< η` between points of `W` stay in the region and are inner
  have hseg : ∀ w ∈ W, ∀ w' ∈ W, dist w w' < η → ∀ z ∈ segment ℝ w w',
      (0 ≤ z.1 ∧ z ∉ plPath a '' Icc 0 1 ∧ z ∉ plPath b '' Icc 0 1 ∧
        (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0))) ∧ StripInner a b 1 z := by
    intro w hw w' hw' hww'
    have hsegreg : ∀ z ∈ segment ℝ w w', 0 ≤ z.1 ∧ z ∉ plPath a '' Icc 0 1 ∧
        z ∉ plPath b '' Icc 0 1 ∧ z ∉ segment ℝ (a (Fin.last s)) (b (Fin.last s)) ∧
        (z.1 = 0 → z ∈ segment ℝ (a 0) (b 0)) := by
      intro z hz
      have hz0 : 0 ≤ z.1 := by
        obtain ⟨h1, -⟩ := mem_segment_coords hz
        exact le_trans (le_min (hWR w hw) (hWR w' hw')) h1.1
      refine hreg z ⟨w, hw, lt_of_le_of_lt (dist_le_of_mem_segment_left hz) hww', ?_⟩ hz0
      intro hz1
      obtain ⟨α', β', hα', hβ', hαβ', rfl⟩ := hz
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hz1
      have h1 := hWR w hw
      have h2 := hWR w' hw'
      have e1 : α' * w.1 = 0 := by nlinarith
      have e2 : β' * w'.1 = 0 := by nlinarith
      rcases eq_or_lt_of_le hα' with hα0 | hα0
      · subst hα0
        rw [show β' = 1 by linarith, zero_smul, zero_add, one_smul]
        exact openSegment_subset_segment ℝ _ _ (hWB₀ w' hw' (by
          rcases mul_eq_zero.1 e2 with h | h
          · linarith
          · exact h))
      rcases eq_or_lt_of_le hβ' with hβ0 | hβ0
      · subst hβ0
        rw [show α' = 1 by linarith, zero_smul, add_zero, one_smul]
        exact openSegment_subset_segment ℝ _ _ (hWB₀ w hw (by
          rcases mul_eq_zero.1 e1 with h | h
          · linarith
          · exact h))
      have hw1 : w.1 = 0 := (mul_eq_zero.1 e1).resolve_left hα0.ne'
      have hw'1 : w'.1 = 0 := (mul_eq_zero.1 e2).resolve_left hβ0.ne'
      exact (convex_segment _ _) (openSegment_subset_segment ℝ _ _ (hWB₀ w hw hw1))
        (openSegment_subset_segment ℝ _ _ (hWB₀ w' hw' hw'1)) hα' hβ' hαβ'
    intro z hz
    obtain ⟨h0, hf, hg, -, hL⟩ := hsegreg z hz
    exact ⟨⟨h0, hf, hg, hL⟩, stripInner_one_of_isPreconnected hs ha0 hb0 haR hbR
      (convex_segment w w').isPreconnected hsegreg (left_mem_segment ℝ _ _) (hWin w hw) z hz⟩
  -- the chain in `Z`
  obtain ⟨m, c, hc0, hcm, hcZ, hcd⟩ := exists_eps_chain hZ.2.isPreconnected hη hzA hzB
  set cF : Fin (m + 1 + 1) → Pt × Pt := fun j => c (min j.val m)
  set hpath := plPath (fun j => (cF j).1)
  set kpath := plPath (fun j => (cF j).2)
  have hm1 : 0 < m + 1 := Nat.succ_pos m
  have hfinExt : ∀ (F : Pt × Pt → Pt) (k : ℕ), finExt (fun j => F (cF j)) k = F (c (min k m)) := by
    intro F k
    simp only [finExt, cF]
    congr 2
    omega
  have hstep : ∀ j : ℕ, dist (c (min j m)) (c (min (j + 1) m)) < η := by
    intro j
    rcases Nat.lt_or_ge j m with h | h
    · rw [min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h)]; exact hcd j h
    · rw [min_eq_right h, min_eq_right (by omega), dist_self]; exact hη
  have hcW : ∀ j, (c j).1 ∈ W ∧ (c j).2 ∈ W := fun j => hZW (hcZ j)
  have hpiece : ∀ u ∈ Icc (0 : ℝ) 1, ∃ j : ℕ, ∃ l ∈ Icc (0 : ℝ) 1,
      hpath u = (1 - l) • (c (min j m)).1 + l • (c (min (j + 1) m)).1 ∧
      kpath u = (1 - l) • (c (min j m)).2 + l • (c (min (j + 1) m)).2 := by
    intro u hu
    obtain ⟨j, -, l, hl, -, h⟩ := plPath_eq_piece hm1 hu
    refine ⟨j, l, hl, ?_, ?_⟩
    · simp only [hpath]; rw [h, hfinExt Prod.fst, hfinExt Prod.fst]
    · simp only [kpath]; rw [h, hfinExt Prod.snd, hfinExt Prod.snd]
  have hpathP : ∀ (F : Pt × Pt → Pt), (F = Prod.fst ∨ F = Prod.snd) → ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, ∀ l ∈ Icc (0 : ℝ) 1,
      (0 ≤ ((1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m))).1 ∧
        (1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m)) ∉ plPath a '' Icc 0 1 ∧
        (1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m)) ∉ plPath b '' Icc 0 1 ∧
        (((1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m))).1 = 0 →
          (1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m)) ∈ segment ℝ (a 0) (b 0))) ∧
      StripInner a b 1 ((1 - l) • F (c (min j m)) + l • F (c (min (j + 1) m))) := by
    intro F hF u _ j l hl
    have hFW : ∀ k, F (c k) ∈ W := fun k => by
      rcases hF with rfl | rfl
      · exact (hcW k).1
      · exact (hcW k).2
    have hFd : dist (F (c (min j m))) (F (c (min (j + 1) m))) < η := by
      refine lt_of_le_of_lt ?_ (hstep j)
      rcases hF with rfl | rfl
      · exact (le_max_left _ _).trans_eq Prod.dist_eq.symm
      · exact (le_max_right _ _).trans_eq Prod.dist_eq.symm
    exact hseg _ (hFW _) _ (hFW _) hFd _ ⟨1 - l, l, by linarith [hl.2], hl.1, by ring, rfl⟩
  have hH : ∀ u ∈ Icc (0 : ℝ) 1, (0 ≤ (hpath u).1 ∧ hpath u ∉ plPath a '' Icc 0 1 ∧
      hpath u ∉ plPath b '' Icc 0 1 ∧ ((hpath u).1 = 0 → hpath u ∈ segment ℝ (a 0) (b 0))) ∧
      StripInner a b 1 (hpath u) := by
    intro u hu
    obtain ⟨j, l, hl, h1, -⟩ := hpiece u hu
    rw [h1]; exact hpathP Prod.fst (Or.inl rfl) u hu j l hl
  have hK : ∀ u ∈ Icc (0 : ℝ) 1, (0 ≤ (kpath u).1 ∧ kpath u ∉ plPath a '' Icc 0 1 ∧
      kpath u ∉ plPath b '' Icc 0 1 ∧ ((kpath u).1 = 0 → kpath u ∈ segment ℝ (a 0) (b 0))) ∧
      StripInner a b 1 (kpath u) := by
    intro u hu
    obtain ⟨j, l, hl, -, h2⟩ := hpiece u hu
    rw [h2]; exact hpathP Prod.snd (Or.inr rfl) u hu j l hl
  -- `d(h u, k u) > ε`
  have hdist : ∀ u ∈ Icc (0 : ℝ) 1, ε < dist (hpath u) (kpath u) := by
    intro u hu
    obtain ⟨j, l, hl, h1, h2⟩ := hpiece u hu
    rw [h1, h2]
    set P := c (min j m)
    set Q := c (min (j + 1) m)
    have hP := hαle P (hcZ _)
    have hPQ : dist P Q < η := hstep j
    have hPQ1 : ‖Q.1 - P.1‖ < η := by
      rw [← dist_eq_norm, dist_comm]
      exact lt_of_le_of_lt ((le_max_left _ _).trans_eq Prod.dist_eq.symm) hPQ
    have hPQ2 : ‖Q.2 - P.2‖ < η := by
      rw [← dist_eq_norm, dist_comm]
      exact lt_of_le_of_lt ((le_max_right _ _).trans_eq Prod.dist_eq.symm) hPQ
    rw [dist_eq_norm] at hP ⊢
    have heq : (1 - l) • P.1 + l • Q.1 - ((1 - l) • P.2 + l • Q.2) =
        (P.1 - P.2) + l • ((Q.1 - P.1) - (Q.2 - P.2)) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [heq]
    have h3 : ‖l • ((Q.1 - P.1) - (Q.2 - P.2))‖ ≤ 2 * η := by
      rw [norm_smul, Real.norm_of_nonneg hl.1]
      calc l * ‖(Q.1 - P.1) - (Q.2 - P.2)‖ ≤ 1 * (‖Q.1 - P.1‖ + ‖Q.2 - P.2‖) :=
            mul_le_mul hl.2 (norm_sub_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ 2 * η := by linarith
    have h4 := norm_sub_norm_le (P.1 - P.2) (-(l • ((Q.1 - P.1) - (Q.2 - P.2))))
    rw [sub_neg_eq_add, norm_neg] at h4
    linarith
  -- the boundary signs and the common zero
  have hcontH := stripSign_continuousOn hs ha0 hb0 haR hbR (h := hpath)
    (continuous_plPath _).continuousOn (fun u hu => (hH u hu).1.1) (fun u hu => (hH u hu).1.2.1)
    (fun u hu => (hH u hu).1.2.2.1) (fun u hu => (hH u hu).1.2.2.2)
  have hcontK := stripSign_continuousOn hs ha0 hb0 haR hbR (h := kpath)
    (continuous_plPath _).continuousOn (fun u hu => (hK u hu).1.1) (fun u hu => (hK u hu).1.2.1)
    (fun u hu => (hK u hu).1.2.2.1) (fun u hu => (hK u hu).1.2.2.2)
  have hH0 : (hpath 0).1 = 0 := by
    simp only [hpath]; rw [plPath_zero]; simp only [cF, Nat.zero_min, Fin.val_zero, hc0, hzA1]
    exact hw₀0
  have hK1 : (kpath 1).1 = 0 := by
    simp only [kpath]; rw [plPath_one (Nat.succ_pos m)]
    simp only [cF, Fin.val_last, min_eq_right (Nat.le_succ m), hcm, hzB2]
    exact hw₀0
  obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, h1, h2⟩ := common_zero_rect zero_lt_one hcontH hcontK
    (fun u hu => ⟨stripSign_zero_nonneg ha0 hb0 (hH u hu).1.2.2.2,
      stripSign_zero_nonneg ha0 hb0 (hK u hu).1.2.2.2⟩)
    (fun u hu => ⟨stripSign_nonpos_of_inner (hH u hu).2, stripSign_nonpos_of_inner (hK u hu).2⟩)
    (fun t _ => stripSign_nonpos_of_inner (Or.inl hH0))
    (fun t _ => stripSign_nonpos_of_inner (Or.inl hK1))
  have hm1 := stripSign_eq_zero h1
  have hm2 := stripSign_eq_zero h2
  have := (dist_le_of_mem_segment hm1 hm2).trans (dist_plPath_le hs hab ht)
  linarith [hdist u hu]

end HPC.Span
