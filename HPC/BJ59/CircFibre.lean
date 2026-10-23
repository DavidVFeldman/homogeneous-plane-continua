import HPC.BJ59.CircDescr

/-!
# Batch 202, §3 (second part): runs and fibres

Runs (commission (3.8)): the links of level `k` whose arcs contain `y` are the indices
`runA k y ≤ t ≤ runB k y`; they form a chain `runChain k y` of `X`. A run of level `k + 1` is
crooked in the run of level `k` ((3.9), the enlarged form of `crooked_of_tight_pat`), and every
fibre is a pseudo-arc of `X` ((3.10)).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

namespace CircDescr

variable {X : Type*} [MetricSpace X] (Δ : CircDescr X)

/-- The first index of the run of `y` at level `k`. -/
noncomputable def runA (k : ℕ) (y : ℝ) : ℤ :=
  ⌈(Δ.N k : ℝ) * (y - Δ.o k) - Δ.lam k * Δ.N k / 2⌉

/-- The last index of the run of `y` at level `k`. -/
noncomputable def runB (k : ℕ) (y : ℝ) : ℤ :=
  ⌊(Δ.N k : ℝ) * (y - Δ.o k) + Δ.lam k * Δ.N k / 2⌋

theorem run_iff (k : ℕ) (y : ℝ) (t : ℤ) :
    |y - Δ.c k t| ≤ Δ.lam k / 2 ↔ Δ.runA k y ≤ t ∧ t ≤ Δ.runB k y := by
  have hN := Δ.N_pos' k
  have key : (Δ.N k : ℝ) * (y - Δ.c k t) = Δ.N k * (y - Δ.o k) - t := by
    unfold c; field_simp; ring
  have e : |y - Δ.c k t| ≤ Δ.lam k / 2 ↔
      |(Δ.N k : ℝ) * (y - Δ.o k) - t| ≤ Δ.lam k * Δ.N k / 2 := by
    rw [← key, abs_mul, abs_of_pos hN]
    constructor
    · intro h; nlinarith
    · intro h
      by_contra hc; push_neg at hc; nlinarith
  rw [e, abs_le, runA, runB, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem run_len (k : ℕ) (y : ℝ) :
    3 ≤ Δ.runB k y - Δ.runA k y ∧ Δ.runB k y - Δ.runA k y + 4 ≤ Δ.N k := by
  have h5 := Δ.five_le_lam k
  have h4 := Δ.lam_add_four_le k
  have a1 := Int.ceil_lt_add_one ((Δ.N k : ℝ) * (y - Δ.o k) - Δ.lam k * Δ.N k / 2)
  have b2 := Int.lt_floor_add_one ((Δ.N k : ℝ) * (y - Δ.o k) + Δ.lam k * Δ.N k / 2)
  have a2 := Int.le_ceil ((Δ.N k : ℝ) * (y - Δ.o k) - Δ.lam k * Δ.N k / 2)
  have b1 := Int.floor_le ((Δ.N k : ℝ) * (y - Δ.o k) + Δ.lam k * Δ.N k / 2)
  unfold runA runB
  constructor
  · have : ((2 : ℤ) : ℝ) < ((⌊(Δ.N k : ℝ) * (y - Δ.o k) + Δ.lam k * Δ.N k / 2⌋ -
        ⌈(Δ.N k : ℝ) * (y - Δ.o k) - Δ.lam k * Δ.N k / 2⌉ : ℤ) : ℝ) := by push_cast; linarith
    have := (Int.cast_lt (R := ℝ)).mp this
    omega
  · have : ((⌊(Δ.N k : ℝ) * (y - Δ.o k) + Δ.lam k * Δ.N k / 2⌋ -
        ⌈(Δ.N k : ℝ) * (y - Δ.o k) - Δ.lam k * Δ.N k / 2⌉ + 4 : ℤ) : ℝ) ≤ ((Δ.N k : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this

/-- The length of the run chain. -/
noncomputable def runN (k : ℕ) (y : ℝ) : ℕ := (Δ.runB k y - Δ.runA k y + 1).toNat

theorem runN_eq (k : ℕ) (y : ℝ) : (Δ.runN k y : ℤ) = Δ.runB k y - Δ.runA k y + 1 := by
  have := Δ.run_len k y; unfold runN; omega

/-- **The run chain** of `y` at level `k` (commission (3.8)). -/
noncomputable def runChain (k : ℕ) (y : ℝ) : Chain X (Δ.runN k y) where
  link i := Δ.L k (Δ.runA k y + i)
  isOpen i := Δ.isOpen_L k _
  adjacent i j := by
    have hl := Δ.run_len k y
    have hn := Δ.runN_eq k y
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · intro h
      have := Δ.meet_small h (by rw [abs_le]; omega)
      rw [abs_le] at this
      omega
    · intro h
      exact (Δ.meet_iff k _ _).mpr ⟨0, by rw [abs_le]; omega⟩

theorem runChain_link (k : ℕ) (y : ℝ) (i : Fin (Δ.runN k y)) :
    (Δ.runChain k y).link i = Δ.L k (Δ.runA k y + i) := rfl

theorem mem_runChain_union {k : ℕ} {y : ℝ} {q : X} :
    q ∈ (Δ.runChain k y).union ↔ ∃ t, |y - Δ.c k t| ≤ Δ.lam k / 2 ∧ q ∈ Δ.L k t := by
  have hn := Δ.runN_eq k y
  simp only [Chain.union, mem_iUnion, runChain_link]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, (Δ.run_iff k y _).mpr ⟨by omega, by have := i.isLt; omega⟩, hi⟩
  · rintro ⟨t, ht, hq⟩
    rw [Δ.run_iff] at ht
    refine ⟨⟨(t - Δ.runA k y).toNat, by omega⟩, ?_⟩
    simp only
    rwa [show Δ.runA k y + ((t - Δ.runA k y).toNat : ℕ) = t by omega]

theorem fib_eq_iInter (y : ℝ) : Δ.fib y = ⋂ k, (Δ.runChain k y).union := by
  ext q
  simp only [mem_iInter, Δ.mem_runChain_union, Δ.mem_fib_iff]

theorem fib_subset_union (k : ℕ) (y : ℝ) : Δ.fib y ⊆ (Δ.runChain k y).union := by
  rw [fib_eq_iInter]; exact iInter_subset _ k

/-! ### (3.9) Runs are crooked -/

/-- The image of a run under the pattern lies in the run below. -/
theorem pat_mem_run {k : ℕ} {y : ℝ} {t : ℤ} (ht : |y - Δ.c (k + 1) t| ≤ Δ.lam (k + 1) / 2) :
    |y - Δ.c k (Δ.pat k t)| ≤ Δ.lam k / 2 := by
  have h := Δ.arcNest k t
  have := abs_sub_le y (Δ.c (k + 1) t) (Δ.c k (Δ.pat k t))
  unfold c at *
  linarith

/-- Tightness inside runs: the integer shift vanishes. -/
theorem tight_run {k : ℕ} {y : ℝ} {t l : ℤ} (ht : |y - Δ.c (k + 1) t| ≤ Δ.lam (k + 1) / 2)
    (hl : |y - Δ.c k l| ≤ Δ.lam k / 2) (h : (Δ.L (k + 1) t ∩ Δ.L k l).Nonempty) :
    ∃ t', |t' - t| ≤ 1 ∧ Δ.pat k t' = l := by
  obtain ⟨t', n, h1, h2⟩ := Δ.tight k t l h
  refine ⟨t', h1, ?_⟩
  have hp := (Δ.run_iff k y _).mp (Δ.pat_mem_run ht)
  have hl' := (Δ.run_iff k y _).mp hl
  have hlen := Δ.run_len k y
  have hstep : |Δ.pat k t' - Δ.pat k t| ≤ 1 := by
    rw [abs_le] at h1 ⊢
    rcases (show t' = t ∨ t' = t + 1 ∨ t' + 1 = t by omega) with e | e | e
    · subst e; omega
    · subst e; have := Δ.pat_step k t; rw [abs_le] at this; omega
    · have := Δ.pat_step k t'; rw [abs_le] at this; rw [← e]; omega
  have h4 : (4 : ℤ) ≤ Δ.N k := by exact_mod_cast Δ.four_le k
  rw [abs_le] at hstep
  rcases mul_cases h4 n with e | e | e
  · subst e; simpa using h2
  · omega
  · omega

/-- **A run of level `k + 1` is crooked in the run of level `k`** (commission (3.9)). -/
theorem runChain_crooked (k : ℕ) (y : ℝ) :
    (Δ.runChain (k + 1) y).IsCrookedIn' (Δ.runChain k y) := by
  have hnE := Δ.runN_eq (k + 1) y
  have hnD := Δ.runN_eq k y
  -- membership in runs
  have memE : ∀ u : Fin (Δ.runN (k + 1) y), |y - Δ.c (k + 1) ((Δ.runA (k + 1) y) + u)| ≤ Δ.lam (k + 1) / 2 :=
    fun u => (Δ.run_iff _ y _).mpr ⟨by omega, by have := u.isLt; omega⟩
  have memD : ∀ i : Fin (Δ.runN k y), |y - Δ.c k ((Δ.runA k y) + i)| ≤ Δ.lam k / 2 :=
    fun i => (Δ.run_iff _ y _).mpr ⟨by omega, by have := i.isLt; omega⟩
  have patD : ∀ u : Fin (Δ.runN (k + 1) y),
      (Δ.runA k y) ≤ Δ.pat k ((Δ.runA (k + 1) y) + u) ∧ Δ.pat k ((Δ.runA (k + 1) y) + u) - (Δ.runA k y) < Δ.runN k y := by
    intro u
    have := (Δ.run_iff k y _).mp (Δ.pat_mem_run (memE u))
    omega
  have hsubD : ∀ (t : ℤ) (i : Fin (Δ.runN k y)), Δ.pat k t = (Δ.runA k y) + i →
      Δ.L (k + 1) t ⊆ (Δ.runChain k y).link i := by
    intro t i h
    rw [runChain_link, ← h]; exact Δ.L_succ_subset k t
  refine ⟨fun u => ⟨⟨(Δ.pat k ((Δ.runA (k + 1) y) + u) - (Δ.runA k y)).toNat, by have := patD u; omega⟩,
    hsubD _ _ (by have := patD u; simp only; omega)⟩, ?_⟩
  intro h k' hk i j hi hj
  -- tightness
  obtain ⟨u', hu1, hu2⟩ := Δ.tight_run (memE i) (memD h) hi
  obtain ⟨v', hv1, hv2⟩ := Δ.tight_run (memE j) (memD k') hj
  -- crookedness on the enlarged window
  have hcr := Δ.crook k ((Δ.runA (k + 1) y) - 1)
  have hlen1 := Δ.run_len (k + 1) y
  have hH : (Δ.runN (k + 1) y : ℤ) + 1 ≤ ((⌈Δ.lam (k + 1) * Δ.N (k + 1)⌉₊ + 3 : ℕ) : ℤ) := by
    have h1 : (Δ.runB (k + 1) y : ℝ) - Δ.runA (k + 1) y ≤ Δ.lam (k + 1) * Δ.N (k + 1) := by
      have a2 := Int.le_ceil ((Δ.N (k + 1) : ℝ) * (y - Δ.o (k + 1)) -
        Δ.lam (k + 1) * Δ.N (k + 1) / 2)
      have b1 := Int.floor_le ((Δ.N (k + 1) : ℝ) * (y - Δ.o (k + 1)) +
        Δ.lam (k + 1) * Δ.N (k + 1) / 2)
      unfold runA runB
      linarith
    have h2 := Nat.le_ceil (Δ.lam (k + 1) * Δ.N (k + 1))
    have h3 : ((Δ.runB (k + 1) y - Δ.runA (k + 1) y : ℤ) : ℝ) ≤
        ((⌈Δ.lam (k + 1) * Δ.N (k + 1)⌉₊ : ℕ) : ℤ) := by push_cast; linarith
    have := (Int.cast_le (R := ℝ)).mp h3
    push_cast; omega
  have hi' := i.isLt
  have hj' := j.isLt
  rw [abs_le] at hu1 hv1
  obtain ⟨r, s, hb, hr, hs⟩ := hcr (u' - ((Δ.runA (k + 1) y) - 1)).toNat (v' - ((Δ.runA (k + 1) y) - 1)).toNat (Nat.zero_le _)
    (by omega) (Nat.zero_le _) (by omega) ((Δ.runA k y) + h) ((Δ.runA k y) + k')
    (by simp only; rw [show (Δ.runA (k + 1) y) - 1 + ((u' - ((Δ.runA (k + 1) y) - 1)).toNat : ℕ) = u' by omega, hu2])
    (by simp only; rw [show (Δ.runA (k + 1) y) - 1 + ((v' - ((Δ.runA (k + 1) y) - 1)).toNat : ℕ) = v' by omega, hv2])
    (by omega)
  simp only at hr hs
  -- the images of `i` and `j` are near `h` and `k'`
  have near : ∀ (p q : ℤ), |p - q| ≤ 1 → |Δ.pat k p - Δ.pat k q| ≤ 1 := by
    intro p q hpq
    rw [abs_le] at hpq
    rcases (show p = q ∨ p = q + 1 ∨ q = p + 1 by omega) with e | e | e
    · subst e; simp
    · subst e; exact Δ.pat_step k q
    · subst e; rw [abs_sub_comm]; exact Δ.pat_step k p
  have ni := near u' ((Δ.runA (k + 1) y) + i) (by rw [abs_le]; omega)
  have nj := near v' ((Δ.runA (k + 1) y) + j) (by rw [abs_le]; omega)
  rw [hu2, abs_le] at ni
  rw [hv2, abs_le] at nj
  have hri : r ≠ i.val + 1 := fun e => by
    rw [e, show (Δ.runA (k + 1) y) - 1 + ((i.val + 1 : ℕ) : ℤ) = (Δ.runA (k + 1) y) + i by push_cast; ring] at hr; omega
  have hsj : s ≠ j.val + 1 := fun e => by
    rw [e, show (Δ.runA (k + 1) y) - 1 + ((j.val + 1 : ℕ) : ℤ) = (Δ.runA (k + 1) y) + j by push_cast; ring] at hs; omega
  unfold HPC.Fold.NBetween at hb
  have hr1 : 1 ≤ r := by omega
  have hs1 : 1 ≤ s := by omega
  have hrn : r - 1 < Δ.runN (k + 1) y := by omega
  have hsn : s - 1 < Δ.runN (k + 1) y := by omega
  refine ⟨⟨r - 1, hrn⟩, ⟨s - 1, hsn⟩, ?_, ?_, ?_⟩
  · unfold Chain.Between
    simp only [Fin.lt_def, gt_iff_lt]
    omega
  · rw [runChain_link]
    simp only
    have : (Δ.runA (k + 1) y) + ((r - 1 : ℕ) : ℤ) = (Δ.runA (k + 1) y) - 1 + (r : ℤ) := by push_cast [Nat.cast_sub hr1]; ring
    rw [this]
    exact hsubD _ ⟨k'.val - 1, by omega⟩ (by simp only; rw [hr]; omega)
  · rw [runChain_link]
    simp only
    have : (Δ.runA (k + 1) y) + ((s - 1 : ℕ) : ℤ) = (Δ.runA (k + 1) y) - 1 + (s : ℤ) := by push_cast [Nat.cast_sub hs1]; ring
    rw [this]
    exact hsubD _ ⟨h.val + 1, by omega⟩ (by simp only; rw [hs]; push_cast; omega)

/-! ### (3.10) Fibres are pseudo-arcs -/

/-- The surviving indices: `l`, `l + 1`, `l + 2` all lie in shrunk arcs containing `y`. -/
theorem exists_two (k : ℕ) (y : ℝ) :
    ∃ l : ℤ, |y - (Δ.o k + (l : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k) ∧
      |y - (Δ.o k + ((l + 2 : ℤ) : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k) := by
  have hN := Δ.N_pos' k
  have h5 := Δ.five_le_lam k
  set x := (Δ.N k : ℝ) * (y - Δ.o k)
  set l := ⌈x - (Δ.lam k * Δ.N k - 1) / 2⌉
  have l1 := Int.le_ceil (x - (Δ.lam k * Δ.N k - 1) / 2)
  have l2 := Int.ceil_lt_add_one (x - (Δ.lam k * Δ.N k - 1) / 2)
  have key : ∀ t : ℤ, |x - t| ≤ (Δ.lam k * Δ.N k - 1) / 2 →
      |y - (Δ.o k + (t : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k) := by
    intro t ht
    have e : y - (Δ.o k + (t : ℝ) / Δ.N k) = (x - t) / Δ.N k := by
      simp only [x]; field_simp; ring
    rw [e, abs_div, abs_of_pos hN, div_le_iff₀ hN]
    have : (Δ.lam k / 2 - 1 / (2 * Δ.N k)) * Δ.N k = (Δ.lam k * Δ.N k - 1) / 2 := by
      field_simp
    linarith
  refine ⟨l, key l ?_, key (l + 2) ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; push_cast; constructor <;> linarith

theorem fib_nonempty (y : ℝ) : (Δ.fib y).Nonempty := by
  obtain ⟨l, hl, -⟩ := Δ.exists_two 0 y
  obtain ⟨q, hq, -⟩ := Δ.fib_meets 0 l y hl
  exact ⟨q, hq⟩

theorem fib_nontrivial (y : ℝ) : (Δ.fib y).Nontrivial := by
  obtain ⟨l, hl, hl2⟩ := Δ.exists_two 0 y
  obtain ⟨p, hp, hpl⟩ := Δ.fib_meets 0 l y hl
  obtain ⟨q, hq, hql⟩ := Δ.fib_meets 0 (l + 2) y hl2
  refine ⟨p, hp, q, hq, fun e => ?_⟩
  subst e
  have h4 : (4 : ℤ) ≤ Δ.N 0 := by exact_mod_cast Δ.four_le 0
  have := Δ.meet_small ⟨p, hpl, hql⟩ (by rw [abs_le]; omega)
  rw [abs_le] at this
  omega

theorem closure_run_succ (k : ℕ) (y : ℝ) :
    closure ((Δ.runChain (k + 1) y).union) ⊆ (Δ.runChain k y).union := by
  rw [Chain.union, closure_iUnion_of_finite]
  refine iUnion_subset fun i => ?_
  intro x hx
  have hi : |y - Δ.c (k + 1) (Δ.runA (k + 1) y + i)| ≤ Δ.lam (k + 1) / 2 := by
    have := Δ.runN_eq (k + 1) y
    exact (Δ.run_iff _ y _).mpr ⟨by omega, by have := i.isLt; omega⟩
  exact Δ.mem_runChain_union.mpr ⟨_, Δ.pat_mem_run hi, Δ.nest k _ hx⟩

theorem runChain_union_subset_K (k : ℕ) (y : ℝ) : (Δ.runChain k y).union ⊆ Δ.K :=
  iUnion_subset fun _ => Δ.L_subset _ _

theorem isPreconnected_runChain_union (k : ℕ) (y : ℝ) :
    IsPreconnected ((Δ.runChain k y).union) := by
  have hl := Δ.run_len k y
  set A := Δ.runA k y
  set B := Δ.runB k y
  have e : (Δ.runChain k y).union = ⋃ t : ℤ, Δ.L k (max A (min B t)) := by
    ext q
    rw [Δ.mem_runChain_union, mem_iUnion]
    constructor
    · rintro ⟨t, ht, hq⟩
      rw [Δ.run_iff] at ht
      exact ⟨t, by rwa [show max A (min B t) = t by omega]⟩
    · rintro ⟨t, ht⟩
      exact ⟨_, (Δ.run_iff k y _).mpr ⟨by omega, by omega⟩, ht⟩
  rw [e]
  refine IsPreconnected.iUnion_of_chain (fun t => Δ.preconn k _) (fun t => ?_)
  rw [Order.succ_eq_add_one]
  by_cases h : max A (min B (t + 1)) = max A (min B t)
  · rw [h, inter_self]; exact Δ.L_nonempty k _
  · rw [show max A (min B (t + 1)) = max A (min B t) + 1 by omega]
    exact Δ.meet_succ k _

theorem isContinuum_fib (y : ℝ) : Fold.Q78.IsContinuum (Δ.fib y) := by
  have e : Δ.fib y = ⋂ k, closure ((Δ.runChain k y).union) := by
    apply Subset.antisymm
    · rw [fib_eq_iInter]; exact iInter_mono fun k => subset_closure
    · rw [fib_eq_iInter]
      exact fun x hx => mem_iInter.mpr fun k => Δ.closure_run_succ k y (mem_iInter.mp hx (k + 1))
  have hcpt : ∀ k, IsCompact (closure ((Δ.runChain k y).union)) := fun k =>
    Δ.isCompact_K.of_isClosed_subset isClosed_closure
      (closure_minimal (Δ.runChain_union_subset_K k y) Δ.isCompact_K.isClosed)
  refine ⟨?_, Δ.fib_nonempty y, ?_⟩
  · rw [e]; exact (hcpt 0).of_isClosed_subset (isClosed_iInter fun k => isClosed_closure)
      (iInter_subset _ 0)
  · rw [e]
    exact HPC.Moore.moore_isPreconnected_iInter
      (antitone_nat_of_succ_le fun k => (Δ.closure_run_succ k y).trans subset_closure) hcpt
      (fun k => (Δ.isPreconnected_runChain_union k y).closure)

theorem ε_nonneg (k : ℕ) : 0 ≤ Δ.ε k := diam_nonneg.trans (Δ.diam_le k 0)

theorem isSnakeLike_fib (y : ℝ) : IsSnakeLike (Δ.fib y) := by
  refine ⟨Δ.isContinuum_fib y, fun ε hε => ?_⟩
  obtain ⟨k, hk⟩ := (Δ.ε_tendsto.eventually_lt_const hε).exists
  exact ⟨_, Δ.runChain k y, fun i => ⟨Δ.L_bdd _ _, lt_of_le_of_lt (Δ.diam_le _ _) hk⟩,
    Δ.fib_subset_union k y⟩

/-- Every fibre is hereditarily indecomposable: Bing's argument of `Description.theorem10`, with
crookedness from (3.9). -/
theorem isHereditarilyIndecomposable_fib (y : ℝ) :
    IsHereditarilyIndecomposable (Δ.fib y) := by
  intro K hKM hK
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨hAne, hBne⟩ := hne
  obtain ⟨p, hpK, hpA⟩ : ∃ p ∈ K, p ∉ A := by
    by_contra h; push_neg at h; exact hAne (Subset.antisymm hAK h)
  obtain ⟨q, hqK, hqB⟩ : ∃ q ∈ K, q ∉ B := by
    by_contra h; push_neg at h; exact hBne (Subset.antisymm hBK h)
  have hqA : q ∈ A := by
    have : q ∈ A ∪ B := hAB ▸ hqK
    exact this.resolve_right hqB
  have hpB : p ∈ B := by
    have : p ∈ A ∪ B := hAB ▸ hpK
    exact this.resolve_left hpA
  obtain ⟨δ1, hδ1, hb1⟩ := Metric.isOpen_iff.mp hA.1.isClosed.isOpen_compl p hpA
  obtain ⟨δ2, hδ2, hb2⟩ := Metric.isOpen_iff.mp hB.1.isClosed.isOpen_compl q hqB
  set δ := min δ1 δ2 with hδ
  have hδpos : 0 < δ := lt_min hδ1 hδ2
  obtain ⟨j, hj⟩ : ∃ j, Δ.ε j < δ / 3 :=
    (Δ.ε_tendsto.eventually_lt_const (by positivity)).exists
  have hKE : K ⊆ (Δ.runChain (j + 1) y).union := hKM.trans (Δ.fib_subset_union (j + 1) y)
  have hpD := Δ.fib_subset_union j y (hKM hpK)
  have hqD := Δ.fib_subset_union j y (hKM hqK)
  simp only [Chain.union, mem_iUnion] at hpD hqD
  obtain ⟨h, hph⟩ := hpD
  obtain ⟨k, hqk⟩ := hqD
  have hdist := (Δ.runChain j y).dist_le_of_mem_link (fun t => Δ.L_bdd _ _)
    (fun t => Δ.diam_le _ _)
  have hεpos := Δ.ε_nonneg j
  have hpq : δ ≤ dist p q := by
    by_contra hlt
    push_neg at hlt
    have : q ∈ ball p δ1 := by
      rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hlt (min_le_left _ _)
    exact hb1 this hqA
  have hnear : ∀ (a b : Fin (Δ.runN j y)) (x₁ x₂ : X), x₁ ∈ (Δ.runChain j y).link a →
      x₂ ∈ (Δ.runChain j y).link b → a.val ≤ b.val + 2 → b.val ≤ a.val + 2 →
      dist x₁ x₂ < δ := by
    intro a b x₁ x₂ hx hy h1 h2
    rcases le_total a.val b.val with hab | hab
    · have := hdist (b.val - a.val) a b (by omega) x₁ hx x₂ hy
      have hc : ((b.val - a.val : ℕ) : ℝ) ≤ 2 := by
        exact_mod_cast (by omega : b.val - a.val ≤ 2)
      nlinarith
    · have := hdist (a.val - b.val) b a (by omega) x₂ hy x₁ hx
      have hc : ((a.val - b.val : ℕ) : ℝ) ≤ 2 := by
        exact_mod_cast (by omega : a.val - b.val ≤ 2)
      rw [dist_comm]; nlinarith
  have hfar : h.val + 2 < k.val ∨ k.val + 2 < h.val := by
    by_contra hc
    push_neg at hc
    have := hnear h k p q hph hqk (by omega) (by omega)
    linarith
  have hcr := Δ.runChain_crooked j y
  rcases hfar with hhk | hkh
  · refine Description.theorem10_core hcr hKE hK.2.isPreconnected hA.2.isPreconnected hAK
      hAB.symm.subset hpK hqA h k hhk hph hqk ?_ ?_
    · intro z hz hzA
      have := hnear h ⟨h.val + 1, by omega⟩ p z hph hz (by simp only; omega)
        (by simp only; omega)
      exact hb1 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_left _ _)) hzA
    · intro z hz hzB
      have := hnear k ⟨k.val - 1, by omega⟩ q z hqk hz (by simp only; omega)
        (by simp only; omega)
      exact hb2 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_right _ _)) hzB
  · have hKBA : K ⊆ B ∪ A := by rw [← hAB, union_comm]
    refine Description.theorem10_core hcr hKE hK.2.isPreconnected hB.2.isPreconnected hBK hKBA
      hqK hpB k h hkh hqk hph ?_ ?_
    · intro z hz hzB
      have := hnear k ⟨k.val + 1, by omega⟩ q z hqk hz (by simp only; omega)
        (by simp only; omega)
      exact hb2 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_right _ _)) hzB
    · intro z hz hzA
      have := hnear h ⟨h.val - 1, by omega⟩ p z hph hz (by simp only; omega)
        (by simp only; omega)
      exact hb1 (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le this (min_le_left _ _)) hzA

/-- (3.10) **Every fibre is a pseudo-arc** (of `X`). -/
theorem isPseudoArc_fib (y : ℝ) : IsPseudoArc (Δ.fib y) :=
  ⟨Δ.isSnakeLike_fib y, Δ.isHereditarilyIndecomposable_fib y, Δ.fib_nontrivial y⟩

end CircDescr

end HPC.BJ59
