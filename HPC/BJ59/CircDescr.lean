import HPC.BJ59.SweepPattern

import HPC.BJ59.Transfer
import HPC.BJ59.CircleLike
import HPC.PseudoArc.Theorem10
import HPC.Moore.Thm15

/-!
# Batch 202, §2–§3 (first part): circular descriptions

The structure `CircDescr` of the skeleton (`doc/batches/skeletons/BJ59E.lean`, §2), verbatim, and
the first steps of the recognition theorem (commission 202 §3): (3.1) `M` is a continuum,
(3.2) consecutive links meet in `M`, and (3.5) survival (`fib_meets`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-- **A circular description** in `X` (commission §2). Level `k` is a circular chain of `N k`
links `L k t`, indexed by integers read modulo `N k`. Level `k + 1` refines level `k` along the
lifted pattern `pat k` (degree one: `pat k (t + N (k+1)) = pat k t + N k`), with closures nested
and tightness. Link `t` of level `k` carries the closed arc of the base circle `ℝ / ℤ` of length
`lam k` centred at `o k + t / N k` (lifted to `ℝ`; the arcs are labels, not geometry). The arcs
of new links lie in the arcs of their images (`arcNest`); every point of a shrunk arc is in the
shrunk arc of a child (`surv`); and the lifted patterns are crooked on every window a run of
level `k + 1` can occupy (`crook`). -/
structure CircDescr (X : Type*) [MetricSpace X] where
  /-- the number of links of level `k` -/
  N : ℕ → ℕ
  four_le : ∀ k, 4 ≤ N k
  /-- link `t` of level `k` -/
  L : ℕ → ℤ → Set X
  isOpen_L : ∀ k t, IsOpen (L k t)
  periodic : ∀ k (t : ℤ), L k (t + N k) = L k t
  meet_iff : ∀ k s t, (L k s ∩ L k t).Nonempty ↔ ∃ n : ℤ, |s - t - n * (N k : ℤ)| ≤ 1
  preconn : ∀ k t, IsPreconnected (L k t)
  /-- a compact set containing every link -/
  K : Set X
  isCompact_K : IsCompact K
  L_subset : ∀ k t, L k t ⊆ K
  /-- a mesh bound tending to zero -/
  ε : ℕ → ℝ
  ε_tendsto : Tendsto ε atTop (𝓝 0)
  diam_le : ∀ k t, diam (L k t) ≤ ε k
  /-- the lifted pattern of level `k + 1` in level `k` -/
  pat : ℕ → ℤ → ℤ
  pat_period : ∀ k (t : ℤ), pat k (t + N (k + 1)) = pat k t + N k
  pat_step : ∀ k t, |pat k (t + 1) - pat k t| ≤ 1
  nest : ∀ k t, closure (L (k + 1) t) ⊆ L k (pat k t)
  tight : ∀ k t l, (L (k + 1) t ∩ L k l).Nonempty →
    ∃ t' n : ℤ, |t' - t| ≤ 1 ∧ pat k t' = l + n * (N k : ℤ)
  /-- the offset of the centres of level `k` -/
  o : ℕ → ℝ
  /-- the length of the arcs of level `k` -/
  lam : ℕ → ℝ
  lam_tendsto : Tendsto lam atTop (𝓝 0)
  five_le_lam : ∀ k, 5 ≤ lam k * N k
  lam_add_four_le : ∀ k, lam k * N k + 4 ≤ N k
  arcNest : ∀ k (t : ℤ),
    |(o (k + 1) + (t : ℝ) / N (k + 1)) - (o k + (pat k t : ℝ) / N k)| ≤
      (lam k - lam (k + 1)) / 2
  surv : ∀ k (l : ℤ) (y : ℝ), |y - (o k + (l : ℝ) / N k)| ≤ lam k / 2 - 1 / (2 * N k) →
    ∃ t : ℤ, pat k t = l ∧
      |y - (o (k + 1) + (t : ℝ) / N (k + 1))| ≤ lam (k + 1) / 2 - 1 / (2 * N (k + 1))
  crook : ∀ k (a : ℤ),
    HPC.Fold.PatCrookedOn (fun u : ℕ => pat k (a + u)) 0 (⌈lam (k + 1) * N (k + 1)⌉₊ + 3)

namespace CircDescr

variable {X : Type*} [MetricSpace X] (Δ : CircDescr X)

/-- The continuum described: the intersection of the unions of the levels. -/
def M : Set X := ⋂ k, ⋃ t, Δ.L k t

/-- The fibre over `y` (commission (3.4)): the intersection over the levels of the union of the
links whose arcs contain `y`. By periodicity of `L`, unshifted centres suffice. -/
def fib (y : ℝ) : Set X :=
  ⋂ k, ⋃ (t : ℤ) (_ : |y - (Δ.o k + (t : ℝ) / Δ.N k)| ≤ Δ.lam k / 2), Δ.L k t

/-- The centre of link `t` of level `k`. -/
noncomputable def c (k : ℕ) (t : ℤ) : ℝ := Δ.o k + (t : ℝ) / Δ.N k

/-- The union of level `k`. -/
def U (k : ℕ) : Set X := ⋃ t, Δ.L k t

/-! ### Elementary facts -/

theorem N_pos (k : ℕ) : 0 < Δ.N k := by have := Δ.four_le k; omega

theorem N_pos' (k : ℕ) : (0 : ℝ) < Δ.N k := by exact_mod_cast Δ.N_pos k

theorem lam_pos (k : ℕ) : 0 < Δ.lam k := by
  have h := Δ.five_le_lam k
  have hN := Δ.N_pos' k
  by_contra hc; push_neg at hc; nlinarith

/-- `1 / N ≤ λ / 5`. -/
theorem inv_N_le (k : ℕ) : 1 / (Δ.N k : ℝ) ≤ Δ.lam k / 5 := by
  have h := Δ.five_le_lam k
  have hN := Δ.N_pos' k
  rw [div_le_div_iff₀ hN (by norm_num)]; linarith

theorem L_add_mul (k : ℕ) (t n : ℤ) : Δ.L k (t + n * Δ.N k) = Δ.L k t := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [show t + (n + 1) * Δ.N k = (t + n * Δ.N k) + Δ.N k by ring, Δ.periodic, ih]
  | pred n ih =>
      rw [← ih, show t + (-n : ℤ) * Δ.N k = (t + (-n - 1) * Δ.N k) + Δ.N k by ring, Δ.periodic]

theorem c_add_mul (k : ℕ) (t n : ℤ) : Δ.c k (t + n * Δ.N k) = Δ.c k t + n := by
  unfold c; have := Δ.N_pos' k; push_cast; field_simp; ring

theorem c_succ (k : ℕ) (t : ℤ) : Δ.c k (t + 1) = Δ.c k t + 1 / Δ.N k := by
  unfold c; push_cast; ring

theorem pat_add_mul (k : ℕ) (t n : ℤ) :
    Δ.pat k (t + n * Δ.N (k + 1)) = Δ.pat k t + n * Δ.N k := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show t + (n + 1) * Δ.N (k + 1) = (t + n * Δ.N (k + 1)) + Δ.N (k + 1) by ring,
        Δ.pat_period, ih]; ring
  | pred n ih =>
      have := Δ.pat_period k (t + (-n - 1) * Δ.N (k + 1))
      rw [show t + (-n - 1) * Δ.N (k + 1) + Δ.N (k + 1) = t + (-n : ℤ) * Δ.N (k + 1) by ring,
        ih] at this
      linarith

theorem L_bdd (k : ℕ) (t : ℤ) : Bornology.IsBounded (Δ.L k t) :=
  Δ.isCompact_K.isBounded.subset (Δ.L_subset k t)

theorem L_nonempty (k : ℕ) (t : ℤ) : (Δ.L k t).Nonempty := by
  obtain ⟨x, hx, -⟩ := (Δ.meet_iff k t t).mpr ⟨0, by simp⟩
  exact ⟨x, hx⟩

theorem meet_succ (k : ℕ) (t : ℤ) : (Δ.L k t ∩ Δ.L k (t + 1)).Nonempty :=
  (Δ.meet_iff k t (t + 1)).mpr ⟨0, by simp⟩

/-- Integer multiples of `N ≥ 4` are `0` or far from `0`. -/
theorem mul_cases {N : ℤ} (hN : 4 ≤ N) (n : ℤ) : n = 0 ∨ N ≤ n * N ∨ n * N ≤ -N := by
  rcases lt_trichotomy n 0 with h | h | h
  · right; right; nlinarith
  · left; exact h
  · right; left; nlinarith

/-- Links of a level meet only if the index difference is within `1` of a multiple of `N`; for
small differences, only if it is within `1`. -/
theorem meet_small {k : ℕ} {s t : ℤ} (h : (Δ.L k s ∩ Δ.L k t).Nonempty)
    (hst : |s - t| ≤ Δ.N k - 2) : |s - t| ≤ 1 := by
  obtain ⟨n, hn⟩ := (Δ.meet_iff k s t).mp h
  have h4 : (4 : ℤ) ≤ Δ.N k := by exact_mod_cast Δ.four_le k
  rw [abs_le] at hn hst ⊢
  rcases mul_cases h4 n with e | e | e
  · subst e; simp at hn; omega
  · omega
  · omega

theorem L_succ_subset (k : ℕ) (t : ℤ) : Δ.L (k + 1) t ⊆ Δ.L k (Δ.pat k t) :=
  subset_closure.trans (Δ.nest k t)

/-! ### (3.1) `M` is a continuum -/

theorem U_eq_fin (k : ℕ) : Δ.U k = ⋃ t : Fin (Δ.N k), Δ.L k t := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    have hN : (0 : ℤ) < Δ.N k := by exact_mod_cast Δ.N_pos k
    have e : t = t % Δ.N k + (t / Δ.N k) * Δ.N k := by
      have := Int.mul_ediv_add_emod t (Δ.N k); linarith [mul_comm ((Δ.N k : ℤ)) (t / Δ.N k)]
    rw [e, Δ.L_add_mul] at ht
    have h0 := Int.emod_nonneg t hN.ne'
    have h1 := Int.emod_lt_of_pos t hN
    refine mem_iUnion.mpr ⟨⟨(t % Δ.N k).toNat, by omega⟩, ?_⟩
    simp only
    rwa [Int.toNat_of_nonneg h0]
  · exact iUnion_subset fun t => subset_iUnion (fun s : ℤ => Δ.L k s) (t : ℤ)

theorem U_succ_subset (k : ℕ) : Δ.U (k + 1) ⊆ Δ.U k :=
  iUnion_subset fun t => (Δ.L_succ_subset k t).trans (subset_iUnion _ _)

theorem U_anti : Antitone Δ.U := antitone_nat_of_succ_le Δ.U_succ_subset

theorem closure_U_succ (k : ℕ) : closure (Δ.U (k + 1)) ⊆ Δ.U k := by
  rw [Δ.U_eq_fin (k + 1), closure_iUnion_of_finite]
  exact iUnion_subset fun t => (Δ.nest k t).trans (subset_iUnion _ _)

theorem U_subset_K (k : ℕ) : Δ.U k ⊆ Δ.K := iUnion_subset fun t => Δ.L_subset k t

theorem isCompact_closure_U (k : ℕ) : IsCompact (closure (Δ.U k)) :=
  Δ.isCompact_K.of_isClosed_subset isClosed_closure
    (closure_minimal (Δ.U_subset_K k) Δ.isCompact_K.isClosed)

theorem M_eq : Δ.M = ⋂ k, closure (Δ.U k) := by
  apply Subset.antisymm
  · exact iInter_mono fun k => subset_closure
  · intro x hx
    exact mem_iInter.mpr fun k => Δ.closure_U_succ k (mem_iInter.mp hx (k + 1))

theorem M_subset_U (k : ℕ) : Δ.M ⊆ Δ.U k := iInter_subset (fun k => ⋃ t, Δ.L k t) k

/-- (3.1) -/
theorem isCompact_M : IsCompact Δ.M := by
  rw [M_eq]
  exact (Δ.isCompact_closure_U 0).of_isClosed_subset (isClosed_iInter fun k => isClosed_closure)
    (iInter_subset _ 0)

theorem isPreconnected_U (k : ℕ) : IsPreconnected (Δ.U k) := by
  refine IsPreconnected.iUnion_of_chain (fun t => Δ.preconn k t) (fun t => ?_)
  rw [Order.succ_eq_add_one]; exact Δ.meet_succ k t

theorem U_nonempty (k : ℕ) : (Δ.U k).Nonempty := by
  obtain ⟨x, hx⟩ := Δ.L_nonempty k 0
  exact ⟨x, mem_iUnion.mpr ⟨0, hx⟩⟩

theorem M_nonempty : Δ.M.Nonempty := by
  rw [M_eq]
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun k => closure_mono (Δ.U_succ_subset k)) (fun k => (Δ.U_nonempty k).closure)
    (Δ.isCompact_closure_U 0) (fun k => isClosed_closure)

theorem isConnected_M : IsConnected Δ.M := by
  refine ⟨Δ.M_nonempty, ?_⟩
  rw [M_eq]
  exact HPC.Moore.moore_isPreconnected_iInter (fun a b hab => closure_mono (Δ.U_anti hab))
    Δ.isCompact_closure_U (fun k => (Δ.isPreconnected_U k).closure)

/-! ### (3.2) Consecutive links meet in `M` -/

/-- A nested sequence of links has a point in common. -/
theorem exists_mem_nested (k : ℕ) (s : ℕ → ℤ)
    (hs : ∀ j, Δ.pat (k + j) (s (j + 1)) = s j) :
    ∃ q, ∀ j, q ∈ closure (Δ.L (k + j) (s j)) := by
  have hanti : ∀ j, closure (Δ.L (k + (j + 1)) (s (j + 1))) ⊆ closure (Δ.L (k + j) (s j)) := by
    intro j
    have := Δ.nest (k + j) (s (j + 1))
    rw [hs j] at this
    exact this.trans subset_closure
  have hcpt : ∀ j, IsCompact (closure (Δ.L (k + j) (s j))) := fun j =>
    Δ.isCompact_K.of_isClosed_subset isClosed_closure
      (closure_minimal (Δ.L_subset _ _) Δ.isCompact_K.isClosed)
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun j => closure (Δ.L (k + j) (s j))) hanti (fun j => (Δ.L_nonempty _ _).closure)
    (hcpt 0) (fun j => isClosed_closure)
  exact ⟨q, fun j => mem_iInter.mp hq j⟩

/-- From a nested sequence of links to points of `M`. -/
theorem mem_M_of_nested (k : ℕ) (s : ℕ → ℤ) (hs : ∀ j, Δ.pat (k + j) (s (j + 1)) = s j)
    {q : X} (hq : ∀ j, q ∈ closure (Δ.L (k + j) (s j))) : ∀ j, q ∈ Δ.L (k + j) (s j) := by
  intro j
  have := Δ.nest (k + j) (s (j + 1)) (hq (j + 1))
  rwa [hs j] at this

theorem mem_M_of_forall_ge (k : ℕ) {q : X} (hq : ∀ j, q ∈ Δ.U (k + j)) : q ∈ Δ.M := by
  refine mem_iInter.mpr fun i => ?_
  rcases le_total i k with h | h
  · exact Δ.U_anti h (by simpa using hq 0)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hq j

/-- A pair of consecutive indices with consecutive images. -/
theorem exists_pat_pair (k : ℕ) (t : ℤ) : ∃ s, Δ.pat k s = t ∧ Δ.pat k (s + 1) = t + 1 := by
  have hN : (1 : ℤ) ≤ Δ.N k := by exact_mod_cast (show 1 ≤ Δ.N k by have := Δ.four_le k; omega)
  have hN' : (1 : ℤ) ≤ Δ.N (k + 1) := by
    exact_mod_cast (show 1 ≤ Δ.N (k + 1) by have := Δ.four_le (k + 1); omega)
  set a := Δ.pat k 0
  -- an index with value `≤ t` and a later one with value `≥ t + 1`
  set n := |a - t| + 1
  have h1 : Δ.pat k (0 + (-n) * Δ.N (k + 1)) ≤ t := by
    rw [Δ.pat_add_mul]
    have : n ≤ n * Δ.N k := by nlinarith [abs_nonneg (a - t)]
    have := le_abs_self (a - t)
    nlinarith
  have h2 : t + 1 ≤ Δ.pat k (0 + n * Δ.N (k + 1)) := by
    rw [Δ.pat_add_mul]
    have : n ≤ n * Δ.N k := by nlinarith [abs_nonneg (a - t)]
    have := neg_abs_le (a - t)
    nlinarith
  have hle : 0 + (-n) * (Δ.N (k + 1) : ℤ) ≤ 0 + n * Δ.N (k + 1) := by
    have : 0 ≤ n := by positivity
    nlinarith
  obtain ⟨s, s1, s2, s3, s4⟩ := exists_last_le (Δ.pat k) hle h1
  have hs : s < 0 + n * Δ.N (k + 1) := by
    rcases eq_or_lt_of_le s2 with e | e
    · rw [e] at s3; omega
    · exact e
  have := s4 (s + 1) (by omega) (by omega)
  have hst := Δ.pat_step k s
  rw [abs_le] at hst
  exact ⟨s, by omega, by omega⟩

/-- (3.2) Consecutive links meet in `M`. -/
theorem inter_M_nonempty (k : ℕ) (t : ℤ) : (Δ.L k t ∩ Δ.L k (t + 1) ∩ Δ.M).Nonempty := by
  classical
  -- the sequence of pairs
  let step : ℕ → ℤ → ℤ := fun j u => Classical.choose (Δ.exists_pat_pair (k + j) u)
  have hstep : ∀ j u, Δ.pat (k + j) (step j u) = u ∧ Δ.pat (k + j) (step j u + 1) = u + 1 :=
    fun j u => Classical.choose_spec (Δ.exists_pat_pair (k + j) u)
  let s : ℕ → ℤ := fun j => Nat.rec t (fun j u => step j u) j
  have hs0 : s 0 = t := rfl
  have hs : ∀ j, s (j + 1) = step j (s j) := fun j => rfl
  have hA : ∀ j, Δ.pat (k + j) (s (j + 1)) = s j := fun j => by rw [hs]; exact (hstep j _).1
  have hB : ∀ j, Δ.pat (k + j) (s (j + 1) + 1) = s j + 1 := fun j => by
    rw [hs]; exact (hstep j _).2
  -- the compact sets `C j`
  set C : ℕ → Set X := fun j =>
    closure (Δ.L (k + j) (s j)) ∩ closure (Δ.L (k + j) (s j + 1)) with hC
  have hanti : ∀ j, C (j + 1) ⊆ C j := by
    intro j
    refine inter_subset_inter ?_ ?_
    · have := Δ.nest (k + j) (s (j + 1)); rw [hA j] at this; exact this.trans subset_closure
    · have := Δ.nest (k + j) (s (j + 1) + 1); rw [hB j] at this; exact this.trans subset_closure
  have hne : ∀ j, (C j).Nonempty := by
    intro j
    obtain ⟨x, hx1, hx2⟩ := Δ.meet_succ (k + j) (s j)
    exact ⟨x, subset_closure hx1, subset_closure hx2⟩
  have hcpt : IsCompact (C 0) :=
    (Δ.isCompact_K.of_isClosed_subset isClosed_closure
      (closure_minimal (Δ.L_subset _ _) Δ.isCompact_K.isClosed)).inter_right isClosed_closure
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti
    hne hcpt (fun j => isClosed_closure.inter isClosed_closure)
  have hqj : ∀ j, q ∈ Δ.L (k + j) (s j) ∧ q ∈ Δ.L (k + j) (s j + 1) := by
    intro j
    have hq1 := (mem_iInter.mp hq (j + 1))
    refine ⟨?_, ?_⟩
    · have := Δ.nest (k + j) (s (j + 1)) hq1.1; rwa [hA j] at this
    · have := Δ.nest (k + j) (s (j + 1) + 1) hq1.2; rwa [hB j] at this
  refine ⟨q, ⟨?_, ?_⟩, Δ.mem_M_of_forall_ge k fun j => mem_iUnion.mpr ⟨_, (hqj j).1⟩⟩
  · simpa [hs0] using (hqj 0).1
  · simpa [hs0] using (hqj 0).2

/-! ### (3.5) Survival -/

theorem fib_eq (y : ℝ) :
    Δ.fib y = ⋂ k, ⋃ (t : ℤ) (_ : |y - Δ.c k t| ≤ Δ.lam k / 2), Δ.L k t := rfl

theorem mem_fib_iff {y : ℝ} {q : X} :
    q ∈ Δ.fib y ↔ ∀ k, ∃ t, |y - Δ.c k t| ≤ Δ.lam k / 2 ∧ q ∈ Δ.L k t := by
  simp only [fib_eq, mem_iInter, mem_iUnion, exists_prop]

/-- Going down a level keeps the arc condition. -/
theorem down {k : ℕ} {t : ℤ} {y : ℝ} {q : X} (hq : q ∈ Δ.L (k + 1) t)
    (hy : |y - Δ.c (k + 1) t| ≤ Δ.lam (k + 1) / 2) :
    q ∈ Δ.L k (Δ.pat k t) ∧ |y - Δ.c k (Δ.pat k t)| ≤ Δ.lam k / 2 := by
  refine ⟨Δ.L_succ_subset k t hq, ?_⟩
  have h := Δ.arcNest k t
  have := abs_sub_le y (Δ.c (k + 1) t) (Δ.c k (Δ.pat k t))
  unfold c at *
  linarith

theorem down_iter {k : ℕ} {t : ℤ} {y : ℝ} {q : X} (hq : q ∈ Δ.L k t)
    (hy : |y - Δ.c k t| ≤ Δ.lam k / 2) :
    ∀ i ≤ k, ∃ s, |y - Δ.c i s| ≤ Δ.lam i / 2 ∧ q ∈ Δ.L i s := by
  induction k generalizing t with
  | zero => intro i hi; obtain rfl : i = 0 := by omega
            exact ⟨t, hy, hq⟩
  | succ k ih =>
      intro i hi
      rcases eq_or_lt_of_le hi with e | e
      · subst e; exact ⟨t, hy, hq⟩
      · obtain ⟨h1, h2⟩ := Δ.down hq hy
        exact ih h1 h2 i (by omega)

theorem fib_subset_M (y : ℝ) : Δ.fib y ⊆ Δ.M := by
  intro q hq
  rw [mem_fib_iff] at hq
  refine mem_iInter.mpr fun k => ?_
  obtain ⟨t, -, ht⟩ := hq k
  exact mem_iUnion.mpr ⟨t, ht⟩

/-- (3.5) **Survival**: the fibre over a point of a shrunk arc meets the link. -/
theorem fib_meets (k : ℕ) (l : ℤ) (y : ℝ)
    (hy : |y - (Δ.o k + (l : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k)) :
    (Δ.fib y ∩ Δ.L k l).Nonempty := by
  classical
  -- the surviving sequence
  have hsurv : ∀ j (u : ℤ), |y - Δ.c (k + j) u| ≤ Δ.lam (k + j) / 2 - 1 / (2 * Δ.N (k + j)) →
      ∃ t, Δ.pat (k + j) t = u ∧
        |y - Δ.c (k + j + 1) t| ≤ Δ.lam (k + j + 1) / 2 - 1 / (2 * Δ.N (k + j + 1)) :=
    fun j u h => Δ.surv (k + j) u y h
  let P : ℕ → Type := fun j =>
    {u : ℤ // |y - Δ.c (k + j) u| ≤ Δ.lam (k + j) / 2 - 1 / (2 * Δ.N (k + j))}
  let nxt : ∀ j, P j → P (j + 1) := fun j u =>
    ⟨Classical.choose (hsurv j u.1 u.2), (Classical.choose_spec (hsurv j u.1 u.2)).2⟩
  have hnxt : ∀ j (u : P j), Δ.pat (k + j) (nxt j u).1 = u.1 := fun j u =>
    (Classical.choose_spec (hsurv j u.1 u.2)).1
  let sP : ∀ j, P j := fun j => Nat.rec (motive := P) ⟨l, hy⟩ (fun j u => nxt j u) j
  let s : ℕ → ℤ := fun j => (sP j).1
  have hs : ∀ j, Δ.pat (k + j) (s (j + 1)) = s j := fun j => hnxt j (sP j)
  obtain ⟨q, hq⟩ := Δ.exists_mem_nested k s hs
  have hqs := Δ.mem_M_of_nested k s hs hq
  refine ⟨q, ?_, by simpa using hqs 0⟩
  rw [mem_fib_iff]
  intro i
  have hN : ∀ i, 0 ≤ 1 / (2 * (Δ.N i : ℝ)) := fun i => by have := Δ.N_pos' i; positivity
  rcases le_total k i with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨s j, by have := (sP j).2; have := hN (k + j); linarith, hqs j⟩
  · have h0 : |y - Δ.c k (s 0)| ≤ Δ.lam k / 2 := by
      have := (sP 0).2; have := hN k; simp only [add_zero] at *; linarith
    exact Δ.down_iter (by simpa using hqs 0) h0 i h

end CircDescr

end HPC.BJ59
