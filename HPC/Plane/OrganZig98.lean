import HPC.Plane.CantorOrganCont

/-!
# Batch 98: the zigzag maps of the Cantor organ

For every `n` we build a continuous map `organZig n : Organ → ℝ` whose fibres have diameter at most
`2 · 2⁻ⁿ`. The construction: cut Cantor space into the `2ⁿ` cylinders of length `n`. A cylinder
`w` is glued to its left neighbour along the gap whose index is the position of the last `1` of
`w`, and to its right neighbour along the gap whose index is the position of the last `0` of `w`;
the gluing is at the top for odd indices and at the bottom for even ones. If the two indices have
different parities (`¬ Conf`), the cylinder is traversed once, from the height of its left gluing to
the height of its right gluing, over the interval `[2v, 2v+2]` (`v` the binary value of `w`). If
they have the same parity (`Conf`), the cylinder is split into its two halves, each traversed once,
over `[2v, 2v+1]` and `[2v+1, 2v+2]`; the halves are glued along the gap of index `n`, whose parity
is the opposite one. The map is the height, read up or down, plus the offset; identified points
get the same value (`zz_pair`), and equal values force the points into one cylinder or into two
cylinders glued at the common value (`dist_le_of_zz_eq`).
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-! ## Combinatorics of prefixes -/

/-- Index of the last `true` among the first `n` digits. -/
def lastT (b : Cs) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if b n = true then some n else lastT b n

/-- Index of the last `false` among the first `n` digits. -/
def lastF (b : Cs) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if b n = false then some n else lastF b n

/-- Binary value of the first `n` digits (most significant first). -/
def bval (b : Cs) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * bval b n + (if b n = true then 1 else 0)

/-- The cylinder of length `n` has both gluings of the same parity. -/
def Conf (b : Cs) (n : ℕ) : Prop :=
  ∃ l r, lastT b n = some l ∧ lastF b n = some r ∧ l % 2 = r % 2

/-- Orientation of the cylinder of length `n` (`true`: traversed upwards), read from its right
gluing (or from its left gluing for the last cylinder). -/
def ori (b : Cs) (n : ℕ) : Bool :=
  match lastF b n with
  | some r => decide (r % 2 = 1)
  | none => match lastT b n with
    | some l => decide (l % 2 = 0)
    | none => true

/-- Height read upwards or downwards. -/
noncomputable def fy (s : Bool) (y : ℝ) : ℝ := if s then y else 1 - y

open Classical in
/-- **The zigzag map at level `n`**, on parameters. -/
noncomputable def zz (n : ℕ) (b : Cs) (y : ℝ) : ℝ :=
  if Conf b n then 2 * (bval b n : ℝ) + ind (b n) + fy (ori b (n + 1)) y
  else 2 * (bval b n : ℝ) + 2 * fy (ori b n) y

/-- The gluing height of the gap of index `m`. -/
noncomputable def hgt (m : ℕ) : ℝ := if m % 2 = 1 then 1 else 0

/-- Agreement of the first `n` digits. -/
def Agree (n : ℕ) (b c : Cs) : Prop := ∀ k < n, b k = c k

theorem Agree.mono {n n' : ℕ} {b c : Cs} (h : Agree n b c) (hn : n' ≤ n) : Agree n' b c :=
  fun k hk => h k (by omega)

theorem Agree.succ {n : ℕ} {b c : Cs} (h : Agree n b c) (hn : b n = c n) : Agree (n + 1) b c :=
  fun k hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h k hk
    · exact hn

theorem lastT_congr {n : ℕ} {b c : Cs} (h : Agree n b c) : lastT b n = lastT c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lastT, h n (by omega), ih (h.mono (by omega))]

theorem lastF_congr {n : ℕ} {b c : Cs} (h : Agree n b c) : lastF b n = lastF c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lastF, h n (by omega), ih (h.mono (by omega))]

theorem bval_congr {n : ℕ} {b c : Cs} (h : Agree n b c) : bval b n = bval c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bval, h n (by omega), ih (h.mono (by omega))]

theorem conf_congr {n : ℕ} {b c : Cs} (h : Agree n b c) : Conf b n ↔ Conf c n := by
  simp only [Conf, lastT_congr h, lastF_congr h]

theorem ori_congr {n : ℕ} {b c : Cs} (h : Agree n b c) : ori b n = ori c n := by
  simp only [ori, lastT_congr h, lastF_congr h]

theorem zz_congr {n : ℕ} {b c : Cs} (h : Agree (n + 1) b c) (y : ℝ) : zz n b y = zz n c y := by
  have h' := h.mono (Nat.le_succ n)
  unfold zz
  by_cases hc : Conf b n
  · rw [if_pos hc, if_pos ((conf_congr h').mp hc), bval_congr h', ori_congr h, h n (by omega)]
  · rw [if_neg hc, if_neg (fun h'' => hc ((conf_congr h').mpr h'')), bval_congr h', ori_congr h']

theorem lastT_succ_true {b : Cs} {n : ℕ} (h : b n = true) : lastT b (n + 1) = some n := by
  simp [lastT, h]

theorem lastF_succ_false {b : Cs} {n : ℕ} (h : b n = false) : lastF b (n + 1) = some n := by
  simp [lastF, h]

theorem lastT_succ_false {b : Cs} {n : ℕ} (h : b n = false) : lastT b (n + 1) = lastT b n := by
  simp [lastT, h]

theorem lastF_succ_true {b : Cs} {n : ℕ} (h : b n = true) : lastF b (n + 1) = lastF b n := by
  simp [lastF, h]

/-- In a `Conf` cylinder, both gluing indices have the parity of `n - 1`. -/
theorem conf_parity {b : Cs} {n : ℕ} (h : Conf b n) :
    ∃ l r, lastT b n = some l ∧ lastF b n = some r ∧ l % 2 = r % 2 ∧ (l + 1) % 2 = n % 2 := by
  obtain ⟨l, r, hl, hr, hlr⟩ := h
  refine ⟨l, r, hl, hr, hlr, ?_⟩
  cases n with
  | zero => simp [lastT] at hl
  | succ n =>
    cases hb : b n
    · rw [lastF_succ_false hb] at hr; cases hr; omega
    · rw [lastT_succ_true hb] at hl; cases hl; omega

/-! ## Gap pairs -/

section Pairs

variable {m n : ℕ} {b b' : Cs}

theorem pair_lastF_left (hp : Pair m b b') (hn : m < n) : lastF b n = some m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
    · rw [lastF_succ_true (hp.2 n h).1, ih h]
    · exact lastF_succ_false hp.1.2.1

theorem pair_lastT_right (hp : Pair m b b') (hn : m < n) : lastT b' n = some m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
    · rw [lastT_succ_false (hp.2 n h).2, ih h]
    · exact lastT_succ_true hp.1.2.2

theorem pair_bval (hp : Pair m b b') (hn : m < n) : bval b' n = bval b n + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
    · simp only [bval, (hp.2 n h).1, (hp.2 n h).2, ih h]; simp; ring
    · simp only [bval, hp.1.2.1, hp.1.2.2, bval_congr (fun k hk => (hp.1.1 k hk).symm)]
      simp

/-- If the cylinder of the left end of a gap is `Conf`, the gap index has the parity of `n - 1`. -/
theorem pair_conf_left_parity (hp : Pair m b b') (hn : m < n) (hc : Conf b n) :
    (m + 1) % 2 = n % 2 := by
  obtain ⟨l, r, hl, hr, hlr, hln⟩ := conf_parity hc
  rw [pair_lastF_left hp hn] at hr
  cases hr
  omega

theorem pair_conf_right_parity (hp : Pair m b b') (hn : m < n) (hc : Conf b' n) :
    (m + 1) % 2 = n % 2 := by
  obtain ⟨l, r, hl, hr, hlr, hln⟩ := conf_parity hc
  rw [pair_lastT_right hp hn] at hl
  cases hl
  omega

theorem fy_hgt_true_iff (m : ℕ) : fy (decide (m % 2 = 1)) (hgt m) = 1 := by
  unfold fy hgt
  by_cases h : m % 2 = 1 <;> simp [h]

theorem fy_hgt_false_iff (m : ℕ) : fy (decide (m % 2 = 0)) (hgt m) = 0 := by
  unfold fy hgt
  by_cases h : m % 2 = 1
  · simp [h]
  · have : m % 2 = 0 := by omega
    simp [this]

/-- **Right end of a cylinder.** -/
theorem zz_pair_left (hp : Pair m b b') (hn : m < n) :
    zz n b (hgt m) = 2 * (bval b n : ℝ) + 2 := by
  have hbn : b n = true := (hp.2 n hn).1
  unfold zz
  split_ifs with hc
  · rw [ori, lastF_succ_true hbn, pair_lastF_left hp hn]
    simp only [hbn, ind, if_true, fy_hgt_true_iff]; ring
  · rw [ori, pair_lastF_left hp hn]
    simp only [fy_hgt_true_iff]; ring

/-- **Left end of a cylinder.** -/
theorem zz_pair_right (hp : Pair m b b') (hn : m < n) :
    zz n b' (hgt m) = 2 * (bval b' n : ℝ) := by
  have hbn : b' n = false := (hp.2 n hn).2
  unfold zz
  split_ifs with hc
  · have hpar := pair_conf_right_parity hp hn hc
    rw [ori, lastF_succ_false hbn]
    simp only [hbn, ind]
    have : fy (decide (n % 2 = 1)) (hgt m) = 0 := by
      unfold fy hgt
      by_cases h : n % 2 = 1
      · have : m % 2 ≠ 1 := by omega
        simp [h, this]
      · have : m % 2 = 1 := by omega
        simp [h, this]
    rw [this]; simp
  · have hfy : fy (ori b' n) (hgt m) = 0 := by
      rw [ori]
      rcases hr : lastF b' n with _ | r
      · simp only [pair_lastT_right hp hn]
        exact fy_hgt_false_iff m
      · simp only
        have hne : m % 2 ≠ r % 2 := fun h => hc ⟨m, r, pair_lastT_right hp hn, hr, h⟩
        have : decide (r % 2 = 1) = decide (m % 2 = 0) := by
          by_cases h : r % 2 = 1
          · simp [h]; omega
          · simp [h]; omega
        rw [this]; exact fy_hgt_false_iff m
    rw [hfy]; ring

/-- **The middle gluing of a split cylinder.** -/
theorem zz_pair_mid (hp : Pair n b b') (hc : Conf b n) :
    zz n b (hgt n) = 2 * (bval b n : ℝ) + 1 ∧ zz n b' (hgt n) = 2 * (bval b n : ℝ) + 1 := by
  have hag : Agree n b b' := fun k hk => hp.1.1 k hk
  have hc' : Conf b' n := (conf_congr hag).mp hc
  obtain ⟨l, r, hl, hr, hlr, hln⟩ := conf_parity hc
  constructor
  · unfold zz
    rw [if_pos hc, ori, lastF_succ_false hp.1.2.1]
    simp only [hp.1.2.1, ind, fy_hgt_true_iff]; simp
  · unfold zz
    rw [if_pos hc', ori, lastF_succ_true hp.1.2.2, ← lastF_congr hag, hr, ← bval_congr hag]
    simp only [hp.1.2.2, ind, if_true]
    have : fy (decide (r % 2 = 1)) (hgt n) = 0 := by
      have : decide (r % 2 = 1) = decide (n % 2 = 0) := by
        by_cases h : r % 2 = 1
        · simp [h]; omega
        · simp [h]; omega
      rw [this]; exact fy_hgt_false_iff n
    rw [this]; ring

/-- **Identified parameters have the same value.** -/
theorem zz_pair (hp : Pair m b b') (n : ℕ) : zz n b (hgt m) = zz n b' (hgt m) := by
  rcases lt_trichotomy m n with h | rfl | h
  · rw [zz_pair_left hp h, zz_pair_right hp h, pair_bval hp h]; push_cast; ring
  · by_cases hc : Conf b m
    · rw [(zz_pair_mid hp hc).1, (zz_pair_mid hp hc).2]
    · have hag : Agree m b b' := fun k hk => hp.1.1 k hk
      have hc' : ¬ Conf b' m := fun h => hc ((conf_congr hag).mpr h)
      simp only [zz, if_neg hc, if_neg hc', bval_congr hag, ori_congr hag]
  · exact zz_congr (fun k hk => hp.1.1 k (by omega)) _

end Pairs

/-- Gluing heights. -/
theorem hgt_of_height {m : ℕ} {y : ℝ} (h : (y = 1 ∧ Odd m) ∨ (y = 0 ∧ Even m)) : y = hgt m := by
  unfold hgt
  rcases h with ⟨rfl, ho⟩ | ⟨rfl, he⟩
  · rw [if_pos (Nat.odd_iff.mp ho)]
  · rw [if_neg (by rw [Nat.even_iff] at he; omega)]

theorem height_of_hgt (m : ℕ) : (hgt m = 1 ∧ Odd m) ∨ (hgt m = 0 ∧ Even m) := by
  unfold hgt
  by_cases h : m % 2 = 1
  · left; exact ⟨if_pos h, Nat.odd_iff.mpr h⟩
  · right; exact ⟨if_neg h, Nat.even_iff.mpr (by omega)⟩

theorem hgt_mem (m : ℕ) : hgt m ∈ Icc (0 : ℝ) 1 := by
  unfold hgt; split_ifs <;> norm_num

/-- `zz` respects the identifications. -/
theorem zz_eq_of_pt_eq {c c' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1)
    (h : pt c y = pt c' y') (n : ℕ) : zz n c y = zz n c' y' := by
  obtain ⟨rfl, rfl | ⟨m, hp | hp, hh⟩⟩ := (pt_eq_pt_iff hy hy').mp h
  · rfl
  · rw [hgt_of_height hh]; exact zz_pair hp n
  · rw [hgt_of_height hh]; exact (zz_pair hp n).symm

/-! ## Bounds and injectivity on a unit -/

theorem fy_mem (s : Bool) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : fy s y ∈ Icc (0 : ℝ) 1 := by
  unfold fy; cases s <;> simp only [Bool.false_eq_true, if_false, if_true]
  · constructor <;> linarith [hy.1, hy.2]
  · exact hy

theorem fy_inj (s : Bool) {y y' : ℝ} (h : fy s y = fy s y') : y = y' := by
  unfold fy at h; cases s <;> simp at h <;> linarith

theorem zz_bounds (n : ℕ) (b : Cs) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2 * (bval b n : ℝ) ≤ zz n b y ∧ zz n b y ≤ 2 * (bval b n : ℝ) + 2 := by
  have h1 := fy_mem (ori b (n + 1)) hy
  have h2 := fy_mem (ori b n) hy
  have h3 := ind_nonneg (b n)
  have h4 := ind_le_one (b n)
  unfold zz; split_ifs <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem zz_le_of_conf_false {n : ℕ} {b : Cs} (hc : Conf b n) (hb : b n = false) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : zz n b y ≤ 2 * (bval b n : ℝ) + 1 := by
  have h1 := fy_mem (ori b (n + 1)) hy
  unfold zz; rw [if_pos hc]; simp only [hb, ind]; simp; linarith [h1.2]

theorem zz_ge_of_conf_true {n : ℕ} {b : Cs} (hc : Conf b n) (hb : b n = true) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : 2 * (bval b n : ℝ) + 1 ≤ zz n b y := by
  have h1 := fy_mem (ori b (n + 1)) hy
  unfold zz; rw [if_pos hc]; simp only [hb, ind, if_true]; linarith [h1.1]

/-- On one unit (same cylinder, and the same half if the cylinder is split) the value determines
the height. -/
theorem eq_of_zz_eq_unit {n : ℕ} {b c : Cs} (hag : Agree n b c) (hhalf : Conf b n → b n = c n)
    {y y' : ℝ} (h : zz n b y = zz n c y') : y = y' := by
  have hc := conf_congr hag
  unfold zz at h
  by_cases hcb : Conf b n
  · have hag' := hag.succ (hhalf hcb)
    rw [if_pos hcb, if_pos (hc.mp hcb), bval_congr hag, ori_congr hag', hhalf hcb] at h
    exact fy_inj _ (by linarith)
  · rw [if_neg hcb, if_neg (fun h => hcb (hc.mpr h)), bval_congr hag, ori_congr hag] at h
    exact fy_inj _ (by linarith)

/-! ## Binary values -/

theorem agree_of_bval_eq {n : ℕ} {b c : Cs} (h : bval b n = bval c n) : Agree n b c := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [bval] at h
    have hbn : b n = c n := by
      cases hb : b n <;> cases hc : c n <;> simp [hb, hc] at h ⊢ <;> omega
    have : bval b n = bval c n := by
      rw [hbn] at h; omega
    exact (ih this).succ hbn

/-- **Converse of the increment.** -/
theorem exists_pair_of_bval_succ {n : ℕ} {b c : Cs} (h : bval c n = bval b n + 1) :
    ∃ m < n, FirstDiff m b c ∧ ∀ k, m < k → k < n → b k = true ∧ c k = false := by
  induction n with
  | zero => simp [bval] at h
  | succ n ih =>
    simp only [bval] at h
    cases hb : b n <;> cases hc : c n <;> simp only [hb, hc] at h <;> simp at h
    · omega
    · -- b n = false, c n = true: equal prefixes
      have hag : Agree n b c := agree_of_bval_eq (by omega)
      exact ⟨n, by omega, ⟨hag, hb, hc⟩, fun k hk hk' => by omega⟩
    · obtain ⟨m, hm, hfd, hrest⟩ := ih (by omega)
      refine ⟨m, by omega, hfd, fun k hk hk' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
      · exact hrest k hk h'
      · exact ⟨hb, hc⟩
    · omega

/-! ## Widths -/

theorem Wt.abs_sum_sub_le (w : Wt) {n : ℕ} {b c : Cs} (h : Agree n b c) :
    |w.sum b - w.sum c| ≤ w.r n := by
  have hd : HasSum (fun k => (ind (b k) - ind (c k)) * w.p k) (w.sum b - w.sum c) := by
    have := ((w.summable_term b).hasSum).sub ((w.summable_term c).hasSum)
    simpa [sub_mul] using this
  have hfin : ∑ k ∈ Finset.range n, (ind (b k) - ind (c k)) * w.p k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h k (Finset.mem_range.mp hk)]; ring
  have ht := (hasSum_nat_add_iff' n).mpr hd
  rw [hfin, sub_zero] at ht
  have hp := w.hasSum_p_tail n
  have hle : ∀ k, (ind (b (k + n)) - ind (c (k + n))) * w.p (k + n) ≤ w.p (k + n) := fun k => by
    have := ind_le_one (b (k + n)); have := ind_nonneg (c (k + n)); have := w.p_pos (k + n)
    nlinarith
  have hge : ∀ k, -w.p (k + n) ≤ (ind (b (k + n)) - ind (c (k + n))) * w.p (k + n) := fun k => by
    have := ind_nonneg (b (k + n)); have := ind_le_one (c (k + n)); have := w.p_pos (k + n)
    nlinarith
  rw [abs_le]
  exact ⟨by simpa using hasSum_le hge hp.neg ht, hasSum_le hle ht hp⟩

theorem dist_pt_le_of_agree {n : ℕ} {b c : Cs} (h : Agree n b c) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : dist (pt b y) (pt c y) ≤ (1 / 2 : ℝ) ^ n := by
  refine (dist_pt_same_height hy).trans (max_le ?_ ?_)
  · exact ((wR true).abs_sum_sub_le h).trans (rr_le true n)
  · exact ((wR false).abs_sum_sub_le h).trans (rr_le false n)

/-! ## Fibres -/

/-- The fibre bound, ordered case. -/
theorem dist_le_of_zz_eq_aux {n : ℕ} {b b' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) (hle : bval b n ≤ bval b' n)
    (hbn : bval b n = bval b' n → Conf b n → b n = false ∨ b n = b' n)
    (h : zz n b y = zz n b' y') : dist (pt b y) (pt b' y') ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have hw : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  have hb1 := zz_bounds n b hy
  have hb2 := zz_bounds n b' hy'
  rcases (show bval b' n = bval b n ∨ bval b' n = bval b n + 1 ∨ bval b n + 2 ≤ bval b' n by
    omega) with hv | hv | hv
  · have hag : Agree n b b' := agree_of_bval_eq hv.symm
    by_cases hc : Conf b n
    · rcases hbn hv.symm hc with hf | he
      · by_cases he : b n = b' n
        · have := eq_of_zz_eq_unit hag (fun _ => he) h
          subst this
          linarith [dist_pt_le_of_agree hag hy]
        · have ht : b' n = true := by rw [hf] at he; cases h' : b' n <;> simp_all
          -- the middle gluing
          let c : Cs := fun k => if k < n then b k else if k = n then false else true
          let c' : Cs := fun k => if k < n then b k else if k = n then true else false
          have hp : Pair n c c' := ⟨⟨fun k hk => by simp [c, c', hk], by simp [c], by simp [c']⟩,
            fun k hk => by simp [c, c', show ¬ k < n by omega, show k ≠ n by omega]⟩
          have hagc : Agree (n + 1) b c := by
            intro k hk
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · simp [c, hk]
            · simp [c, hf]
          have hagc' : Agree (n + 1) b' c' := by
            intro k hk
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · simp [c', hk, hag k hk]
            · simp [c', ht]
          have hcc : Conf c n := (conf_congr (hagc.mono (Nat.le_succ n))).mp hc
          obtain ⟨hm1, hm2⟩ := zz_pair_mid hp hcc
          have hvc : bval c n = bval b n := (bval_congr (hagc.mono (Nat.le_succ n))).symm
          have hu1 := zz_le_of_conf_false hc hf hy
          have hc' : Conf b' n := (conf_congr hag).mp hc
          have hu2 := zz_ge_of_conf_true hc' ht hy'
          have e1 : zz n b y = zz n c (hgt n) := by rw [hm1, hvc]; rw [hv] at hu2; linarith
          have e2 : zz n b' y' = zz n c' (hgt n) := by rw [hm2, hvc]; rw [hv] at hu2; linarith
          have hy1 := eq_of_zz_eq_unit (hagc.mono (Nat.le_succ n)) (fun _ => hagc n (by omega)) e1
          have hy2 := eq_of_zz_eq_unit (hagc'.mono (Nat.le_succ n)) (fun _ => hagc' n (by omega))
            e2
          subst hy1 hy2
          have hpe : pt c (hgt n) = pt c' (hgt n) :=
            (pt_eq_pt_iff (hgt_mem n) (hgt_mem n)).mpr ⟨rfl, Or.inr ⟨n, Or.inl hp, height_of_hgt n⟩⟩
          calc dist (pt b (hgt n)) (pt b' (hgt n))
              ≤ dist (pt b (hgt n)) (pt c (hgt n)) + dist (pt c (hgt n)) (pt b' (hgt n)) :=
                dist_triangle _ _ _
            _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := by
                gcongr
                · exact dist_pt_le_of_agree (hagc.mono (Nat.le_succ n)) (hgt_mem n)
                · rw [hpe, dist_comm]
                  exact dist_pt_le_of_agree (hagc'.mono (Nat.le_succ n)) (hgt_mem n)
            _ = 2 * (1 / 2) ^ n := by ring
      · have := eq_of_zz_eq_unit hag (fun _ => he) h
        subst this
        linarith [dist_pt_le_of_agree hag hy]
    · have := eq_of_zz_eq_unit hag (fun h => absurd h hc) h
      subst this
      linarith [dist_pt_le_of_agree hag hy]
  · -- adjacent cylinders
    obtain ⟨m, hmn, hfd, hrest⟩ := exists_pair_of_bval_succ hv
    let c : Cs := fun k => if k < n then b k else true
    let c' : Cs := fun k => if k < n then b' k else false
    have hp : Pair m c c' := by
      refine ⟨⟨fun k hk => ?_, ?_, ?_⟩, fun k hk => ?_⟩
      · simp [c, c', show k < n by omega, hfd.1 k hk]
      · simp [c, hmn, hfd.2.1]
      · simp [c', hmn, hfd.2.2]
      · by_cases hkn : k < n
        · simp [c, c', hkn, hrest k hk hkn]
        · simp [c, c', hkn]
    have hagc : Agree n b c := fun k hk => by simp [c, hk]
    have hagc' : Agree n b' c' := fun k hk => by simp [c', hk]
    have hm1 := zz_pair_left hp hmn
    have hm2 := zz_pair_right hp hmn
    rw [← bval_congr hagc] at hm1
    rw [← bval_congr hagc'] at hm2
    have hval : zz n b y = 2 * (bval b n : ℝ) + 2 := by
      have : (bval b' n : ℝ) = bval b n + 1 := by rw [hv]; push_cast; ring
      linarith
    have hval' : zz n b' y' = 2 * (bval b' n : ℝ) := by
      have : (bval b' n : ℝ) = bval b n + 1 := by rw [hv]; push_cast; ring
      linarith
    have hhalf : Conf b n → b n = c n := by
      intro hc
      have hcn : c n = true := by simp [c]
      rw [hcn]
      by_contra hf
      have := zz_le_of_conf_false hc (by simpa using hf) hy
      linarith
    have hhalf' : Conf b' n → b' n = c' n := by
      intro hc
      have hcn : c' n = false := by simp [c']
      rw [hcn]
      by_contra ht
      have := zz_ge_of_conf_true hc (by simpa using ht) hy'
      linarith
    have hy1 := eq_of_zz_eq_unit hagc hhalf (hval.trans hm1.symm)
    have hy2 := eq_of_zz_eq_unit hagc' hhalf' (hval'.trans hm2.symm)
    subst hy1 hy2
    have hpe : pt c (hgt m) = pt c' (hgt m) :=
      (pt_eq_pt_iff (hgt_mem m) (hgt_mem m)).mpr ⟨rfl, Or.inr ⟨m, Or.inl hp, height_of_hgt m⟩⟩
    calc dist (pt b (hgt m)) (pt b' (hgt m))
        ≤ dist (pt b (hgt m)) (pt c (hgt m)) + dist (pt c (hgt m)) (pt b' (hgt m)) :=
          dist_triangle _ _ _
      _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := by
          gcongr
          · exact dist_pt_le_of_agree hagc (hgt_mem m)
          · rw [hpe, dist_comm]
            exact dist_pt_le_of_agree hagc' (hgt_mem m)
      _ = 2 * (1 / 2) ^ n := by ring
  · exfalso
    have : (bval b n : ℝ) + 2 ≤ bval b' n := by exact_mod_cast hv
    linarith

/-- **The fibre bound.** -/
theorem dist_le_of_zz_eq {n : ℕ} {b b' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) (h : zz n b y = zz n b' y') :
    dist (pt b y) (pt b' y') ≤ 2 * (1 / 2 : ℝ) ^ n := by
  rcases lt_or_ge (bval b n) (bval b' n) with hlt | hge
  · exact dist_le_of_zz_eq_aux hy hy' hlt.le (fun he => absurd he hlt.ne) h
  · rcases hge.lt_or_eq with hlt | heq
    · rw [dist_comm]
      exact dist_le_of_zz_eq_aux hy' hy hlt.le (fun he => absurd he (by omega)) h.symm
    · -- equal values: order the halves
      by_cases hc : Conf b n
      · cases hb : b n
        · exact dist_le_of_zz_eq_aux hy hy' heq.ge (fun _ _ => Or.inl hb) h
        · rw [dist_comm]
          have hag : Agree n b' b := agree_of_bval_eq heq
          refine dist_le_of_zz_eq_aux hy' hy heq.le (fun _ hc' => ?_) h.symm
          cases hb' : b' n
          · exact Or.inl rfl
          · exact Or.inr hb.symm
      · exact dist_le_of_zz_eq_aux hy hy' heq.ge (fun _ h => absurd h hc) h

/-! ## Continuity -/

theorem continuous_fy (s : Bool) : Continuous (fy s) := by
  cases s
  · have : fy false = fun y => 1 - y := by funext y; simp [fy]
    rw [this]; fun_prop
  · have : fy true = fun y => y := by funext y; simp [fy]
    rw [this]; fun_prop

theorem continuous_zz (n : ℕ) : Continuous fun p : Cs × ℝ => zz n p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨b0, y0⟩
  have hev : (fun p : Cs × ℝ => zz n p.1 p.2) =ᶠ[𝓝 (b0, y0)] fun p => zz n b0 p.2 := by
    have : cyl b0 (n + 1) ×ˢ (univ : Set ℝ) ∈ 𝓝 (b0, y0) :=
      prod_mem_nhds ((isOpen_cyl b0 (n + 1)).mem_nhds (mem_cyl_self b0 (n + 1))) univ_mem
    filter_upwards [this] with p hp
    exact zz_congr (fun k hk => hp.1 k hk) p.2
  refine ContinuousAt.congr ?_ hev.symm
  apply Continuous.continuousAt
  unfold zz
  split_ifs
  · exact continuous_const.add ((continuous_fy _).comp continuous_snd)
  · exact continuous_const.add (continuous_const.mul ((continuous_fy _).comp continuous_snd))

/-! ## The maps on the organ -/

/-- **The zigzag map** `Organ → ℝ` at level `n`. -/
noncomputable def organZig (n : ℕ) (s : Organ) : ℝ := zz n (rep s).1 (rep s).2

theorem organZig_pt (n : ℕ) (c : Cs) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    organZig n (pt c y) = zz n c y := by
  have h := Phi_rep (pt c y)
  rw [Phi_eq_pt] at h
  exact zz_eq_of_pt_eq (rep (pt c y)).2.2 hy h n

theorem continuous_organZig (n : ℕ) : Continuous (organZig n) := by
  rw [isQuotientMap_Phi.continuous_iff]
  have : organZig n ∘ Phi = fun d : Dom => zz n d.1 d.2 := by
    funext d
    simp only [Function.comp, Phi_eq_pt]
    exact organZig_pt n d.1 d.2.2
  rw [this]
  exact (continuous_zz n).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- **Small fibres.** -/
theorem dist_le_of_organZig_eq (n : ℕ) {s s' : Organ} (h : organZig n s = organZig n s') :
    dist s s' ≤ 2 * (1 / 2 : ℝ) ^ n := by
  obtain ⟨c, y, hy, rfl⟩ := exists_pt s
  obtain ⟨c', y', hy', rfl⟩ := exists_pt s'
  rw [organZig_pt n c hy, organZig_pt n c' hy'] at h
  exact dist_le_of_zz_eq hy hy' h

end HPC.Plane.Org
