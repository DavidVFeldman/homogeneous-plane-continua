import HPC.Chains.Basic

/-!
# Batch 89: the combinatorial core of Bing's Theorem 3 (1951, *Concerning hereditarily
indecomposable continua*)

An abstract form of Bing's windows. Points `y` of a metric space `B` (the decomposition space)
each carry a nonempty interval of indices `{i | R y i}` below `n` (the links of a chain `c` of `M`
meeting the fibre over `y`); `G p q` (the points whose fibre lies in `c(p) ∪ ⋯ ∪ c(q)`) is open.
From these data we build a chain of `B`, of mesh at most `6 η` when fibres meeting the same or
adjacent links have images within `η`.

The windows are Bing's `D(n_{3k+1}, n_{3k+5})`, with his `n_i` replaced by block boundaries
`N k`: `N 0 = 0`, `N (k+1) = s (N k) + 1` where `s i` is the largest last index of a fibre whose
first index is at most `i`. The `+ 1` (absent in Bing) makes the boundaries increase strictly.
Every block `[N k, N (k+1) - 1]` lies in the interval of a single fibre `z k`, and every fibre
starting in block `k` ends before block `k + 2`.

**Note (batch 91).** Bing's own windows are valid: with his sequence `n_i` (strictly increasing
because adjacent links of the chain are met by a common fibre, `M` being connected) and his
windows `D(n_{3k+1}, n_{3k+5})`, consecutive windows meet by the connectedness of `M'`. This is
proved in `HPC/Plane/Windows91.lean` (`Mono.exists_bing_windows`) and `HPC/Plane/Recon91.lean`
(`theorem3_HIC_bing`). The block boundaries used here are an alternative construction, not a
repair of a defect in Bing's proof.
-/

namespace HPC.Plane.Mono

open Set

variable {B : Type*} [MetricSpace B]

/-- **Bing's windows, abstractly.** -/
theorem exists_chain_of_intervals [Nonempty B] {n : ℕ} (R : B → ℕ → Prop)
    (G : ℕ → ℕ → Set B) {η : ℝ}
    (hR1 : ∀ y i, R y i → i < n)
    (hR2 : ∀ y, ∃ i, R y i)
    (hR3 : ∀ y i j k, R y i → R y k → i ≤ j → j ≤ k → R y j)
    (hR4 : ∀ i, i < n → ∃ y, R y i)
    (hR5 : ∀ y y' i i', R y i → R y' i' → i ≤ i' + 1 → i' ≤ i + 1 → dist y y' < η)
    (hGo : ∀ p q, IsOpen (G p q))
    (hG1 : ∀ y p q, (∀ i, R y i → p ≤ i ∧ i ≤ q) → y ∈ G p q)
    (hG2 : ∀ y p q, y ∈ G p q → ∃ i, R y i ∧ p ≤ i ∧ i ≤ q)
    (hG3 : ∀ y p q p' q', y ∈ G p q → y ∈ G p' q' → q + 2 ≤ p' → False) :
    ∃ (m : ℕ) (D : Chain B m), univ ⊆ D.union ∧
      ∀ j, Bornology.IsBounded (D.link j) ∧ Metric.diam (D.link j) ≤ 6 * η := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty B›
  have hη : 0 < η := by
    obtain ⟨i, hi⟩ := hR2 y₀
    simpa using hR5 y₀ y₀ i i hi hi (by omega) (by omega)
  -- first and last index of a fibre
  set a : B → ℕ := fun y => sInf {i | R y i} with ha_def
  set b : B → ℕ := fun y => Nat.findGreatest (R y) n with hb_def
  have ha_mem : ∀ y, R y (a y) := fun y => Nat.sInf_mem (hR2 y)
  have ha_le : ∀ y i, R y i → a y ≤ i := fun y i h => Nat.sInf_le h
  have hb_mem : ∀ y, R y (b y) := fun y => by
    obtain ⟨i, hi⟩ := hR2 y
    exact Nat.findGreatest_spec (hR1 y i hi).le hi
  have hle_b : ∀ y i, R y i → i ≤ b y := fun y i h => Nat.le_findGreatest (hR1 y i h).le h
  have hb_lt : ∀ y, b y < n := fun y => hR1 y _ (hb_mem y)
  have hR_iff : ∀ y i, R y i ↔ a y ≤ i ∧ i ≤ b y := fun y i =>
    ⟨fun h => ⟨ha_le y i h, hle_b y i h⟩, fun h => hR3 y _ i _ (ha_mem y) (hb_mem y) h.1 h.2⟩
  -- Bing's step: the furthest a fibre starting by `i` reaches
  set s : ℕ → ℕ := fun i => Nat.findGreatest (fun k => ∃ y, a y ≤ i ∧ b y = k) n with hs_def
  have hs_mono : Monotone s := fun i j hij =>
    Nat.findGreatest_mono_left (fun k hk => by
      obtain ⟨y, hy, hk⟩ := hk
      exact ⟨y, hy.trans hij, hk⟩) n
  have hb_le_s : ∀ y i, a y ≤ i → b y ≤ s i := fun y i h =>
    Nat.le_findGreatest (hb_lt y).le ⟨y, h, rfl⟩
  have hs_spec : ∀ i, i < n → ∃ z, a z ≤ i ∧ b z = s i := fun i hi => by
    obtain ⟨y, hy⟩ := hR4 i hi
    exact Nat.findGreatest_spec (P := fun k => ∃ y, a y ≤ i ∧ b y = k) (m := b y) (hb_lt y).le
      ⟨y, ha_le y i hy, rfl⟩
  have hs_ge : ∀ i, i < n → i ≤ s i := fun i hi => by
    obtain ⟨y, hy⟩ := hR4 i hi
    exact (hle_b y i hy).trans (hb_le_s y i (ha_le y i hy))
  -- block boundaries
  obtain ⟨N, hN0, hNs⟩ : ∃ N : ℕ → ℕ, N 0 = 0 ∧ ∀ k, N (k + 1) = max (s (N k)) (N k) + 1 :=
    ⟨fun k => Nat.rec 0 (fun _ m => max (s m) m + 1) k, rfl, fun k => rfl⟩
  have hNsm : StrictMono N := strictMono_nat_of_lt_succ (fun k => by rw [hNs]; omega)
  have hNk : ∀ k, k ≤ N k := fun k => hNsm.id_le k
  have hNs' : ∀ k, N k < n → N (k + 1) = s (N k) + 1 := fun k hk => by
    rw [hNs, max_eq_left (hs_ge _ hk)]
  have hNmono : ∀ k k', k ≤ k' → N k ≤ N k' := fun k k' h => hNsm.monotone h
  have hNpos : ∀ k, N (k + 1) ≥ 1 := fun k => by rw [hNs]; omega
  have hblock : ∀ i, ∃ k, N k ≤ i ∧ i < N (k + 1) := by
    intro i
    have hex : ∃ k, i < N (k + 1) := ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hNk _)⟩
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, hN0]; exact Nat.zero_le _
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [not_lt, Nat.sub_add_cancel h] at hmin
      exact hmin
  -- a fibre covering each block
  have hz_ex : ∀ k, ∃ z : B, N k < n → a z ≤ N k ∧ b z = s (N k) := fun k => by
    by_cases hk : N k < n
    · obtain ⟨z, hz⟩ := hs_spec _ hk; exact ⟨z, fun _ => hz⟩
    · exact ⟨y₀, fun h => absurd h hk⟩
  choose z hz using hz_ex
  have hz_R : ∀ k i, N k < n → N k ≤ i → i < N (k + 1) → R (z k) i := by
    intro k i hk h1 h2
    rw [hR_iff]
    obtain ⟨hza, hzb⟩ := hz k hk
    rw [hNs' k hk] at h2
    omega
  have hz_a : ∀ k, N (k + 1) < n → N k ≤ a (z (k + 1)) := by
    intro k hk
    obtain ⟨hza, hzb⟩ := hz (k + 1) hk
    rcases le_or_gt (N k) (a (z (k + 1))) with hle | hlt
    · exact hle
    exfalso
    have h1 : b (z (k + 1)) ≤ s (N k) := hb_le_s _ _ hlt.le
    have h2 : s (N k) < N (k + 1) := by rw [hNs]; omega
    have h3 : N (k + 1) ≤ s (N (k + 1)) := hs_ge _ hk
    omega
  have hz_step : ∀ k, N (k + 1) < n → dist (z k) (z (k + 1)) < η := by
    intro k hk
    have hk' : N k < n := lt_trans (hNsm (show k < k + 1 by omega)) hk
    have hlt := hNsm (show k < k + 1 by omega)
    have h1 : R (z k) (N (k + 1) - 1) := hz_R _ _ hk' (by omega) (by omega)
    have h2 : R (z (k + 1)) (N (k + 1)) := hz_R _ _ hk le_rfl (hNsm (show k + 1 < k + 1 + 1 by omega))
    exact hR5 _ _ _ _ h1 h2 (by omega) (by omega)
  have hz_dist : ∀ k d, N (k + d) < n → dist (z k) (z (k + d)) ≤ d * η := by
    intro k d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have hd' : N (k + d) < n := lt_of_le_of_lt (hNmono (k + d) (k + (d + 1)) (by omega)) hd
      have h1 := ih hd'
      have h2 := hz_step (k + d) hd
      calc dist (z k) (z (k + (d + 1)))
          ≤ dist (z k) (z (k + d)) + dist (z (k + d)) (z (k + d + 1)) := dist_triangle _ _ _
        _ ≤ d * η + η := by linarith
        _ = ((d + 1 : ℕ) : ℝ) * η := by push_cast; ring
  have hzz : ∀ k k', k ≤ k' → k' ≤ k + 4 → N k' < n → dist (z k) (z k') ≤ 4 * η := by
    intro k k' h1 h2 h3
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
    have := hz_dist k d h3
    have hd4 : (d : ℝ) ≤ 4 := by exact_mod_cast (by omega : d ≤ 4)
    nlinarith
  -- the number of windows
  have hJex : ∃ j, 1 ≤ j ∧ n ≤ N (3 * j + 2) :=
    ⟨n + 1, by omega, (by omega : n ≤ 3 * (n + 1) + 2).trans (hNk _)⟩
  set J := Nat.find hJex with hJ_def
  have hJ1 : 1 ≤ J := (Nat.find_spec hJex).1
  have hJn : n ≤ N (3 * J + 2) := (Nat.find_spec hJex).2
  have hJlt : 2 ≤ J → N (3 * J - 1) < n := fun h => by
    have hmin := Nat.find_min hJex (show J - 1 < J by omega)
    push_neg at hmin
    have e : 3 * (J - 1) + 2 = 3 * J - 1 := by omega
    rw [e] at hmin
    exact hmin (by omega)
  -- the windows
  set L : ℕ → Set B := fun j => G (N (3 * j)) (N (3 * j + 5) - 1) with hL_def
  have hcover : ∀ y, ∃ j, j < J ∧ y ∈ L j := by
    intro y
    obtain ⟨k, hk1, hk2⟩ := hblock (a y)
    have hby : b y < N (k + 2) := by
      have h1 := hb_le_s y (N (k + 1)) hk2.le
      have h2 : N (k + 2) = max (s (N (k + 1))) (N (k + 1)) + 1 := hNs (k + 1)
      omega
    by_cases hkJ : k / 3 < J
    · refine ⟨k / 3, hkJ, hG1 _ _ _ fun i hi => ?_⟩
      rw [hR_iff] at hi
      have m1 : N (3 * (k / 3)) ≤ N k := hNmono (3 * (k / 3)) k (by omega)
      have m2 : N (k + 2) ≤ N (3 * (k / 3) + 5) := hNmono (k + 2) (3 * (k / 3) + 5) (by omega)
      omega
    · refine ⟨J - 1, by omega, hG1 _ _ _ fun i hi => ?_⟩
      have m1 : N (3 * (J - 1)) ≤ N k := hNmono (3 * (J - 1)) k (by omega)
      have e : 3 * (J - 1) + 5 = 3 * J + 2 := by omega
      rw [e]
      rw [hR_iff] at hi
      have := hb_lt y
      omega
  have hconsec : ∀ j, j + 1 < J → z (3 * j + 4) ∈ L j ∧ z (3 * j + 4) ∈ L (j + 1) := by
    intro j hj
    have hlt : N (3 * j + 4) < n :=
      lt_of_le_of_lt (hNmono (3 * j + 4) (3 * J - 1) (by omega)) (hJlt (by omega))
    obtain ⟨hza, hzb⟩ := hz (3 * j + 4) hlt
    have hza' : N (3 * j + 3) ≤ a (z (3 * j + 4)) := hz_a (3 * j + 3) hlt
    have e : N (3 * j + 5) = s (N (3 * j + 4)) + 1 := hNs' (3 * j + 4) hlt
    have m1 : N (3 * j) ≤ N (3 * j + 3) := hNmono (3 * j) (3 * j + 3) (by omega)
    have m2 : N (3 * j + 5) ≤ N (3 * (j + 1) + 5) := hNmono (3 * j + 5) (3 * (j + 1) + 5) (by omega)
    have e' : 3 * (j + 1) = 3 * j + 3 := by ring
    constructor
    · refine hG1 _ _ _ fun i hi => ?_
      rw [hR_iff] at hi
      omega
    · refine hG1 _ _ _ fun i hi => ?_
      rw [hR_iff] at hi
      rw [e'] at m2 ⊢
      omega
  have hne : ∀ j, j < J → (L j).Nonempty := by
    intro j hj
    by_cases h1 : j + 1 < J
    · exact ⟨_, (hconsec j h1).1⟩
    · by_cases h2 : 1 ≤ j
      · have := (hconsec (j - 1) (by omega)).2
        rw [Nat.sub_add_cancel h2] at this
        exact ⟨_, this⟩
      · obtain ⟨j', hj', hy⟩ := hcover y₀
        have : j' = j := by omega
        exact ⟨y₀, this ▸ hy⟩
  have hdisj : ∀ j j', j + 2 ≤ j' → ∀ y, y ∈ L j → y ∈ L j' → False := by
    intro j j' h y h1 h2
    refine hG3 y (N (3 * j)) (N (3 * j + 5) - 1) (N (3 * j')) (N (3 * j' + 5) - 1) h1 h2 ?_
    have m1 : N (3 * j + 6) ≤ N (3 * j') := hNmono (3 * j + 6) (3 * j') (by omega)
    have m2 : N (3 * j + 5) < N (3 * j + 6) := hNsm (Nat.lt_succ_self (3 * j + 5))
    have m3 : N (3 * j + 5) ≥ 1 := hNpos (3 * j + 4)
    omega
  have hnear : ∀ y j, y ∈ L j → ∃ k, 3 * j ≤ k ∧ k ≤ 3 * j + 4 ∧ N k < n ∧ dist y (z k) < η := by
    intro y j hy
    obtain ⟨i, hi, h1, h2⟩ := hG2 _ _ _ hy
    obtain ⟨k, hk1, hk2⟩ := hblock i
    have hin := hR1 _ _ hi
    have hk3 : 3 * j ≤ k := by
      by_contra h
      push_neg at h
      have := hNmono _ _ (show k + 1 ≤ 3 * j by omega)
      omega
    have hk4 : k ≤ 3 * j + 4 := by
      by_contra h
      push_neg at h
      have := hNmono _ _ (show 3 * j + 5 ≤ k by omega)
      have : N (3 * j + 5) ≥ 1 := hNpos (3 * j + 4)
      omega
    have hkn : N k < n := by omega
    exact ⟨k, hk3, hk4, hkn, hR5 _ _ _ _ hi (hz_R k i hkn hk1 hk2) (by omega) (by omega)⟩
  have hdist : ∀ y y' j, y ∈ L j → y' ∈ L j → dist y y' ≤ 6 * η := by
    intro y y' j hy hy'
    obtain ⟨k, hk1, hk2, hkn, hd⟩ := hnear y j hy
    obtain ⟨k', hk1', hk2', hkn', hd'⟩ := hnear y' j hy'
    have hm : dist (z k) (z k') ≤ 4 * η := by
      rcases le_total k k' with h | h
      · exact hzz k k' h (by omega) hkn'
      · rw [dist_comm]; exact hzz k' k h (by omega) hkn
    calc dist y y' ≤ dist y (z k) + dist (z k) (z k') + dist (z k') y' := dist_triangle4 _ _ _ _
      _ ≤ η + 4 * η + η := by rw [dist_comm (z k') y']; linarith
      _ = 6 * η := by ring
  -- the chain
  refine ⟨J, { link := fun j => L j.val, isOpen := fun j => hGo _ _, adjacent := ?_ }, ?_, ?_⟩
  · intro i j
    constructor
    · rintro ⟨y, h1, h2⟩
      by_contra hfar
      have : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by omega
      rcases this with h | h
      · exact hdisj _ _ h y h1 h2
      · exact hdisj _ _ h y h2 h1
    · intro hclose
      have : i.val = j.val ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
      rcases this with h | h | h
      · obtain ⟨y, hy⟩ := hne i i.isLt
        exact ⟨y, hy, by simpa [← h] using hy⟩
      · have := hconsec i.val (by omega)
        refine ⟨_, this.1, ?_⟩
        simpa [← h] using this.2
      · have := hconsec j.val (by omega)
        refine ⟨_, ?_, this.1⟩
        simpa [← h] using this.2
  · intro y _
    obtain ⟨j, hj, hy⟩ := hcover y
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hy⟩
  · intro j
    refine ⟨Metric.isBounded_iff.mpr ⟨6 * η, fun x hx y hy => hdist x y j hx hy⟩, ?_⟩
    exact Metric.diam_le_of_forall_dist_le (by linarith) fun x hx y hy => hdist x y j hx hy

end HPC.Plane.Mono
