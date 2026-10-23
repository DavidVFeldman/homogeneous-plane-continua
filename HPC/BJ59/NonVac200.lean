import HPC.BJ59.Zigzag

/-!
# Batch 200, §8: non-vacuity of §2

* `starImage` on degenerate inputs;
* `nonvac_zigzag` (statement verbatim from the skeleton): triadic chains on `[0, 1]`, with
  `N i = 2 * 3 ^ i`, links the intervals of radius `3 / (4 N i)` about `k / N i`, and `K i k`
  the integer nearest `k / 3`, i.e. `(k + 1) / 3`;
* `nonvac_zigzag_homeomorph`, `nonvac_zigzag_fibre`: `zigzag_homeomorph` and `zigzag_fibre`
  applied to them (with `H i` the identity): the homeomorphism exists and is the identity.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-! ### `starImage` on degenerate inputs -/

section Degenerate

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem starImage_eq_empty_of_notMem {n m : ℕ} (D : Chain X n) (E : Chain Y m)
    (H : Fin n → Fin m) {p : X} (hp : p ∉ D.union) : starImage D E H p = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => hp ?_
  obtain ⟨j, hj, -⟩ := mem_starImage.1 hy
  exact mem_iUnion.2 ⟨j, hj⟩

theorem starImage_zero {m : ℕ} (D : Chain X 0) (E : Chain Y m) (H : Fin 0 → Fin m) (p : X) :
    starImage D E H p = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨j, -, -⟩ := mem_starImage.1 hy
  exact j.elim0

theorem starImage_self_id {n : ℕ} (D : Chain X n) (p : X) :
    starImage D D id p = ⋃ (j : Fin n) (_ : p ∈ D.link j), D.link j := rfl

end Degenerate

/-! ### Triadic chains on `[0, 1]` -/

/-- `N i = 2 * 3 ^ i`. -/
abbrev nvN (i : ℕ) : ℕ := 2 * 3 ^ i

theorem nvN_pos (i : ℕ) : (0 : ℝ) < nvN i := by
  unfold nvN; positivity

theorem nvN_pos' (i : ℕ) : 0 < nvN i := by
  unfold nvN; positivity

theorem nvN_succ (i : ℕ) : (nvN (i + 1) : ℝ) = 3 * nvN i := by
  unfold nvN; push_cast; ring

/-- The `k`-th link at level `i`. -/
def nvLink (i k : ℕ) : Set unitInterval :=
  {x | |(x : ℝ) - k / nvN i| < 3 / (4 * nvN i)}

theorem nvLink_isOpen (i k : ℕ) : IsOpen (nvLink i k) :=
  isOpen_lt ((continuous_subtype_val.sub continuous_const).abs) continuous_const

theorem nvLink_mem (i k : ℕ) (hk : k ≤ nvN i) :
    (⟨(k : ℝ) / nvN i, div_nonneg (Nat.cast_nonneg _) (nvN_pos i).le,
      (div_le_one (nvN_pos i)).2 (by exact_mod_cast hk)⟩ : unitInterval) ∈ nvLink i k := by
  have := nvN_pos i
  simp only [nvLink, mem_setOf_eq, sub_self, abs_zero]
  positivity

theorem nvLink_inter_iff (i k l : ℕ) (hk : k ≤ nvN i) (hl : l ≤ nvN i) :
    (nvLink i k ∩ nvLink i l).Nonempty ↔ ((k : ℤ) - l).natAbs ≤ 1 := by
  have hN := nvN_pos i
  constructor
  · rintro ⟨x, hxk, hxl⟩
    simp only [nvLink, mem_setOf_eq] at hxk hxl
    have h1 : |(k : ℝ) / nvN i - l / nvN i| < 3 / (2 * nvN i) := by
      calc |(k : ℝ) / nvN i - l / nvN i| = |((x : ℝ) - l / nvN i) - ((x : ℝ) - k / nvN i)| := by
            ring_nf
        _ ≤ |(x : ℝ) - l / nvN i| + |(x : ℝ) - k / nvN i| := abs_sub _ _
        _ < 3 / (4 * nvN i) + 3 / (4 * nvN i) := add_lt_add hxl hxk
        _ = 3 / (2 * nvN i) := by field_simp; ring
    rw [← sub_div, abs_div, abs_of_pos hN, div_lt_div_iff₀ hN (by positivity)] at h1
    have h2 : |(k : ℝ) - l| < 3 / 2 := by nlinarith
    rw [abs_lt] at h2
    have h3 : ((k : ℤ) - l : ℝ) < 2 := by push_cast; linarith
    have h4 : (-2 : ℝ) < ((k : ℤ) - l : ℤ) := by push_cast; linarith
    have h3' : (k : ℤ) - l < 2 := by exact_mod_cast h3
    have h4' : -2 < (k : ℤ) - l := by exact_mod_cast h4
    omega
  · intro h
    have hkl : |(k : ℝ) - l| ≤ 1 := by
      rw [abs_le]
      have h1 : (k : ℤ) - l ≤ 1 := by omega
      have h2 : -1 ≤ (k : ℤ) - l := by omega
      constructor
      · have : ((-1 : ℤ) : ℝ) ≤ ((k : ℤ) - l : ℤ) := by exact_mod_cast h2
        push_cast at this; linarith
      · have : (((k : ℤ) - l : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h1
        push_cast at this; linarith
    refine ⟨⟨((k : ℝ) + l) / (2 * nvN i), by positivity, ?_⟩, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      have : (k : ℝ) + l ≤ 2 * nvN i := by
        have := (Nat.cast_le (α := ℝ)).2 hk; have := (Nat.cast_le (α := ℝ)).2 hl; linarith
      exact this
    · simp only [nvLink, mem_setOf_eq]
      have : ((k : ℝ) + l) / (2 * nvN i) - k / nvN i = ((l : ℝ) - k) / (2 * nvN i) := by
        field_simp; ring
      rw [this, abs_div, abs_of_pos (show (0 : ℝ) < 2 * nvN i by positivity),
        div_lt_div_iff₀ (show (0 : ℝ) < 2 * nvN i by positivity)
        (show (0 : ℝ) < 4 * nvN i by positivity)]
      rw [abs_sub_comm] at hkl
      nlinarith
    · simp only [nvLink, mem_setOf_eq]
      have : ((k : ℝ) + l) / (2 * nvN i) - l / nvN i = ((k : ℝ) - l) / (2 * nvN i) := by
        field_simp; ring
      rw [this, abs_div, abs_of_pos (show (0 : ℝ) < 2 * nvN i by positivity),
        div_lt_div_iff₀ (show (0 : ℝ) < 2 * nvN i by positivity)
        (show (0 : ℝ) < 4 * nvN i by positivity)]
      nlinarith

/-- The chain at level `i`. -/
def nvChain (i : ℕ) : Chain unitInterval (nvN i + 1) where
  link k := nvLink i k
  isOpen k := nvLink_isOpen i k
  adjacent k l := nvLink_inter_iff i k l (by omega) (by omega)

theorem nvChain_cover (i : ℕ) : univ ⊆ (nvChain i).union := by
  intro x _
  have hN := nvN_pos i
  set k := ⌊(x : ℝ) * nvN i + 1 / 2⌋₊
  have hk1 : (k : ℝ) ≤ (x : ℝ) * nvN i + 1 / 2 := Nat.floor_le (by nlinarith [x.2.1])
  have hk2 : (x : ℝ) * nvN i + 1 / 2 < k + 1 := Nat.lt_floor_add_one _
  have hkN : k ≤ nvN i := by
    have : (k : ℝ) < nvN i + 1 := by nlinarith [x.2.2]
    have : k < nvN i + 1 := by exact_mod_cast this
    omega
  refine mem_iUnion.2 ⟨⟨k, by omega⟩, ?_⟩
  show x ∈ nvLink i k
  simp only [nvLink, mem_setOf_eq]
  have : (x : ℝ) - k / nvN i = ((x : ℝ) * nvN i - k) / nvN i := by field_simp
  rw [this, abs_div, abs_of_pos hN, div_lt_div_iff₀ hN (by positivity)]
  have : |(x : ℝ) * nvN i - k| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

theorem nvChain_nonempty (i : ℕ) (j : Fin (nvN i + 1)) : ((nvChain i).link j).Nonempty :=
  ⟨_, nvLink_mem i j (by omega)⟩

theorem nvChain_bj (i : ℕ) : IsBJChain (nvChain i) := by
  intro k l hkl
  have hN := nvN_pos i
  refine ⟨1 / (2 * nvN i), by positivity, fun x hx y hy => ?_⟩
  change x ∈ nvLink i k at hx
  change y ∈ nvLink i l at hy
  simp only [nvLink, mem_setOf_eq] at hx hy
  have h2 : 2 ≤ |(k : ℝ) - l| := by
    rcases le_or_gt 0 ((k : ℤ) - l) with h | h
    · have : (2 : ℤ) ≤ (k : ℤ) - l := by omega
      have : ((2 : ℤ) : ℝ) ≤ (((k : ℤ) - l : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (2 : ℤ) ≤ (l : ℤ) - k := by omega
      have : ((2 : ℤ) : ℝ) ≤ (((l : ℤ) - k : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      rw [abs_of_neg (by linarith)]; linarith
  rw [Subtype.dist_eq, Real.dist_eq]
  have h3 : |(k : ℝ) / nvN i - l / nvN i| ≤
      |(x : ℝ) - k / nvN i| + |(x : ℝ) - y| + |(y : ℝ) - l / nvN i| := by
    calc |(k : ℝ) / nvN i - l / nvN i|
        = |-((x : ℝ) - k / nvN i) + ((x : ℝ) - y) + ((y : ℝ) - l / nvN i)| := by ring_nf
      _ ≤ |-((x : ℝ) - k / nvN i) + ((x : ℝ) - y)| + |(y : ℝ) - l / nvN i| := abs_add_le _ _
      _ ≤ |-((x : ℝ) - k / nvN i)| + |(x : ℝ) - y| + |(y : ℝ) - l / nvN i| := by
          gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_neg]
  rw [← sub_div, abs_div, abs_of_pos hN] at h3
  have h4 : 2 / (nvN i : ℝ) ≤ |(k : ℝ) - l| / nvN i := by gcongr
  have h5 : 2 / (nvN i : ℝ) = 1 / (2 * nvN i) + 3 / (4 * nvN i) + 3 / (4 * nvN i) := by
    field_simp; ring
  linarith

theorem nvChain_eps (i : ℕ) : IsEpsChain (nvChain i) (1 / 2 ^ i) := by
  intro k
  have hN := nvN_pos i
  refine ⟨(isCompact_univ.isBounded).subset (subset_univ _), ?_⟩
  have hd : Metric.diam ((nvChain i).link k) ≤ 3 / (2 * nvN i) := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    change x ∈ nvLink i k at hx
    change y ∈ nvLink i k at hy
    simp only [nvLink, mem_setOf_eq] at hx hy
    rw [Subtype.dist_eq, Real.dist_eq]
    have : |(x : ℝ) - y| ≤ |(x : ℝ) - k / nvN i| + |(y : ℝ) - k / nvN i| := by
      rw [show (x : ℝ) - y = ((x : ℝ) - k / nvN i) - ((y : ℝ) - k / nvN i) by ring]
      exact abs_sub _ _
    have h5 : 3 / (2 * (nvN i : ℝ)) = 3 / (4 * nvN i) + 3 / (4 * nvN i) := by field_simp; ring
    linarith
  refine lt_of_le_of_lt hd ?_
  have h23 : (2 : ℝ) ^ i ≤ 3 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have : (nvN i : ℝ) = 2 * 3 ^ i := by unfold nvN; push_cast; ring
  rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]

/-- `K i k = (k + 1) / 3`, the integer nearest `k / 3`. -/
def nvK (i : ℕ) (k : Fin (nvN (i + 1) + 1)) : Fin (nvN i + 1) :=
  ⟨(k.val + 1) / 3, by
    have h := k.isLt
    have : nvN (i + 1) = 3 * nvN i := by unfold nvN; ring
    omega⟩

theorem nvK_chainMap (i : ℕ) : IsChainMap (nvK i) := by
  intro a b hab
  simp only [nvK]
  omega

theorem nvK_refine (i : ℕ) (j : Fin (nvN (i + 1) + 1)) :
    (nvChain (i + 1)).link j ⊆ (nvChain i).link (nvK i j) := by
  intro x hx
  change x ∈ nvLink (i + 1) j at hx
  change x ∈ nvLink i ((j.val + 1) / 3)
  simp only [nvLink, mem_setOf_eq, nvN_succ] at hx ⊢
  have hN := nvN_pos i
  set c := (j.val + 1) / 3
  have hc1 : (j.val : ℤ) - 3 * c ≤ 1 := by omega
  have hc2 : -1 ≤ (j.val : ℤ) - 3 * c := by omega
  have hc : |(j.val : ℝ) - 3 * c| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : ((-1 : ℤ) : ℝ) ≤ (((j.val : ℤ) - 3 * c : ℤ) : ℝ) := by exact_mod_cast hc2
      push_cast at this; linarith
    · have : (((j.val : ℤ) - 3 * c : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast hc1
      push_cast at this; linarith
  have h1 : |(j.val : ℝ) / (3 * nvN i) - c / nvN i| ≤ 1 / (3 * nvN i) := by
    have : (j.val : ℝ) / (3 * nvN i) - c / nvN i = ((j.val : ℝ) - 3 * c) / (3 * nvN i) := by
      field_simp
    rw [this, abs_div, abs_of_pos (show (0 : ℝ) < 3 * nvN i by positivity)]
    exact div_le_div_of_nonneg_right hc (by positivity)
  have h2 : |(x : ℝ) - c / nvN i| ≤
      |(x : ℝ) - j.val / (3 * nvN i)| + |(j.val : ℝ) / (3 * nvN i) - c / nvN i| := by
    rw [show (x : ℝ) - c / nvN i = ((x : ℝ) - j.val / (3 * nvN i)) +
      ((j.val : ℝ) / (3 * nvN i) - c / nvN i) by ring]
    exact abs_add_le _ _
  have h3 : 3 / (4 * (3 * (nvN i : ℝ))) + 1 / (3 * nvN i) < 3 / (4 * nvN i) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  linarith

/-- `zigzag_homeomorph` with a non-degenerate witness: `P = Q = [0, 1]`, `D i = E i`, `H i` the
identity. One choice: with `N i = 2 * 3 ^ i`, the links of `D i` are the intervals of radius
`3 / (4 * N i)` about `k / N i` (`k = 0, …, N i`), and `K i` sends `k` to the integer nearest
`k / 3`. (Halving the index does not work: a link of the finer chain can straddle two links.) -/
theorem nonvac_zigzag : ∃ (n : ℕ → ℕ) (D : ∀ i, Chain unitInterval (n i))
    (K : ∀ i, Fin (n (i + 1)) → Fin (n i)), (∀ i, univ ⊆ (D i).union) ∧
    (∀ i j, ((D i).link j).Nonempty) ∧ (∀ i, IsBJChain (D i)) ∧
    (∀ i, IsEpsChain (D i) (1 / 2 ^ i)) ∧ (∀ i, IsChainMap (K i)) ∧
    ∀ i j, (D (i + 1)).link j ⊆ (D i).link (K i j) :=
  ⟨fun i => nvN i + 1, nvChain, nvK, nvChain_cover, nvChain_nonempty, nvChain_bj, nvChain_eps,
    nvK_chainMap, nvK_refine⟩

theorem tendsto_one_div_two_pow : Tendsto (fun i : ℕ => (1 : ℝ) / 2 ^ i) atTop (𝓝 0) := by
  simp_rw [one_div, ← inv_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- **Non-vacuity of `zigzag_homeomorph` and `zigzag_fibre`**: on the triadic chains of
`nonvac_zigzag` (with `H i` the identity) all hypotheses hold, and the homeomorphism they give is
the identity of `[0, 1]` (by `zigzag_fibre` with `φ = ψ = id`). -/
theorem nonvac_zigzag_homeomorph :
    ∃ h : (univ : Set unitInterval) ≃ₜ (univ : Set unitInterval), ∀ p, h p = p := by
  have hP : IsCompact (univ : Set unitInterval) := isCompact_univ
  have hDp : ∀ i j, ((nvChain i).link j ∩ univ).Nonempty := fun i j => by
    rw [inter_univ]; exact nvChain_nonempty i j
  obtain ⟨h, hh⟩ := zigzag_homeomorph (P := univ) (Q := univ) hP hP nvChain nvChain
    (fun i => nvChain_cover i) hDp (fun i => nvChain_cover i) hDp nvChain_bj
    tendsto_one_div_two_pow nvChain_eps nvChain_eps (fun i => id) nvK (fun i a b h => h)
    (fun i => Function.surjective_id) nvK_chainMap (fun i j => nvK_refine i j)
    (fun i j => nvK_refine i j)
  have hf := zigzag_fibre (P := univ) (Q := univ) nvChain nvChain tendsto_one_div_two_pow
    nvChain_eps (fun i => id) (T := unitInterval) id id
    (fun t => by simp)
    (fun i j p _ hp => ⟨p, mem_univ _, hp, rfl⟩) h hh
  exact ⟨h, fun p => Subtype.ext (hf p)⟩

end HPC.BJ59
