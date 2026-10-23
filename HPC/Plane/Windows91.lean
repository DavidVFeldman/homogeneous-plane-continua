import HPC.Chains.Basic

/-!
# Batch 91: Bing's own windows for Theorem 3 (1951, *Concerning hereditarily indecomposable
continua*; Nadler 12.13)

An abstract form of Bing's construction, with **his** sequence `n_i`. Points `y` of a connected
metric space `B` (the decomposition space) each carry a nonempty interval of indices
`{i | R y i}` below `n` (the links of a chain `c` of `M` meeting the fibre over `y`); `G p q` (the
points whose fibre lies in `c(p) ∪ ⋯ ∪ c(q)`) is open.

* `bingNext R n i` is Bing's `n_{i+1}` as a function of `n_i = i`: the largest `j` such that some
  fibre meets both link `i` and link `j`;
* `bingSeq R n k` is `n_{k+1}` (indices from `0`): `bingSeq 0 = 0`, `bingSeq (k+1) = bingNext (bingSeq k)`;
* the windows are `G (n_{3k}) (n_{3k+4})` (0-indexed; Bing's `D(n_{3k+1}, n_{3k+5})`), the last one
  running to `n_J = n - 1`.

`exists_bing_windows` proves that these windows form a chain covering `B`, of mesh at most `5 η`
when fibres meeting the same or adjacent links have images within `η`. Consecutive windows meet by
the connectedness of `B` (Bing's argument as completed by Nadler), not by an explicit point.
-/

namespace HPC.Plane.Mono

open Set

variable {B : Type*}

open Classical in
/-- **Bing's step**: the largest index `j ≤ n` such that some fibre meets both link `i` and link
`j` (Bing's `n_{i+1} = max {j : some element of G meets c(n_i) and c(j)}`). -/
noncomputable def bingNext (R : B → ℕ → Prop) (n i : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ∃ y, R y i ∧ R y j) n

/-- **Bing's sequence** `n_1 = 1, n_2, …` (here indexed from `0` and with links indexed from `0`):
`bingSeq R n 0 = 0`, `bingSeq R n (k+1) = bingNext R n (bingSeq R n k)`. It is strictly increasing
until it reaches the last link `n - 1`, and constant afterwards. -/
noncomputable def bingSeq (R : B → ℕ → Prop) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bingNext R n (bingSeq R n k)

theorem bingSeq_zero (R : B → ℕ → Prop) (n : ℕ) : bingSeq R n 0 = 0 := rfl

theorem bingSeq_succ (R : B → ℕ → Prop) (n k : ℕ) :
    bingSeq R n (k + 1) = bingNext R n (bingSeq R n k) := rfl

/-- `bingSeq` depends only on which pairs of indices are met by a common fibre. -/
theorem bingSeq_congr {B' : Type*} (R : B → ℕ → Prop) (R' : B' → ℕ → Prop) (n : ℕ)
    (h : ∀ i j, (∃ y, R y i ∧ R y j) ↔ (∃ y, R' y i ∧ R' y j)) (k : ℕ) :
    bingSeq R n k = bingSeq R' n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bingSeq_succ, bingSeq_succ, ih]
    unfold bingNext
    congr 1
    funext j
    exact propext (h _ j)

/-- **Bing's windows** (Pacific J. Math. Theorem 3; Nadler 12.13), abstractly. With `N = bingSeq R n`,
`J` the first index with `N J = n - 1` and `K = (J - 2) / 3`, the sets
`G (N (3k)) (N (3k + 4))` for `k < K` and `G (N (3K)) (N J)` form a chain covering `B` with
mesh at most `5 η`. -/
theorem exists_bing_windows [Nonempty B] [MetricSpace B] [PreconnectedSpace B] {n : ℕ}
    (R : B → ℕ → Prop) (G : ℕ → ℕ → Set B) {η : ℝ}
    (hR1 : ∀ y i, R y i → i < n)
    (hR2 : ∀ y, ∃ i, R y i)
    (hR3 : ∀ y i j k, R y i → R y k → i ≤ j → j ≤ k → R y j)
    (hR4 : ∀ i, i < n → ∃ y, R y i)
    (hR5 : ∀ y y' i i', R y i → R y' i' → i ≤ i' + 1 → i' ≤ i + 1 → dist y y' < η)
    (hR6 : ∀ i, i + 1 < n → ∃ y, R y i ∧ R y (i + 1))
    (hGo : ∀ p q, IsOpen (G p q))
    (hG1 : ∀ y p q, (∀ i, R y i → p ≤ i ∧ i ≤ q) → y ∈ G p q)
    (hG2 : ∀ y p q, y ∈ G p q → ∃ i, R y i ∧ p ≤ i ∧ i ≤ q)
    (hG3 : ∀ y p q p' q', y ∈ G p q → y ∈ G p' q' → q + 2 ≤ p' → False) :
    ∃ J K : ℕ, bingSeq R n J = n - 1 ∧ (∀ k < J, bingSeq R n k < bingSeq R n (k + 1)) ∧
      K = (J - 2) / 3 ∧
      ∃ D : Chain B (K + 1), univ ⊆ D.union ∧
        (∀ k : Fin (K + 1), D.link k = G (bingSeq R n (3 * k.val))
          (if k.val = K then bingSeq R n J else bingSeq R n (3 * k.val + 4))) ∧
        ∀ k, Bornology.IsBounded (D.link k) ∧ Metric.diam (D.link k) ≤ 5 * η := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty B›
  have hn : 0 < n := by
    obtain ⟨i, hi⟩ := hR2 y₀
    exact lt_of_le_of_lt (Nat.zero_le _) (hR1 _ _ hi)
  set N := bingSeq R n with hN_def
  set t := bingNext R n with ht_def
  have hNs : ∀ k, N (k + 1) = t (N k) := fun k => rfl
  -- properties of Bing's step
  have t_spec : ∀ i, i < n → ∃ y, R y i ∧ R y (t i) := by
    intro i hi
    obtain ⟨y, hy⟩ := hR4 i hi
    exact Nat.findGreatest_spec (P := fun j => ∃ y, R y i ∧ R y j) (m := i) hi.le ⟨y, hy, hy⟩
  have t_le : ∀ i y j, R y i → R y j → j ≤ t i := fun i y j hi hj =>
    Nat.le_findGreatest (P := fun j => ∃ y, R y i ∧ R y j) (hR1 y j hj).le ⟨y, hi, hj⟩
  have t_lt : ∀ i, i < n → t i < n := fun i hi => by
    obtain ⟨y, -, hy⟩ := t_spec i hi
    exact hR1 _ _ hy
  have t_ge : ∀ i, i < n → i ≤ t i := fun i hi => by
    obtain ⟨y, hy⟩ := hR4 i hi
    exact t_le i y i hy hy
  have t_succ : ∀ i, i + 1 < n → i + 1 ≤ t i := fun i hi => by
    obtain ⟨y, h1, h2⟩ := hR6 i hi
    exact t_le i y _ h1 h2
  -- properties of Bing's sequence
  have N_lt : ∀ k, N k < n := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih => rw [hNs]; exact t_lt _ ih
  have N_le_succ : ∀ k, N k ≤ N (k + 1) := fun k => by rw [hNs]; exact t_ge _ (N_lt k)
  have N_mono : Monotone N := monotone_nat_of_le_succ N_le_succ
  have N_strict : ∀ k, N k < n - 1 → N k + 1 ≤ N (k + 1) := fun k hk => by
    rw [hNs]; exact t_succ _ (by omega)
  have N_ge : ∀ k, min k (n - 1) ≤ N k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := N_lt k
      by_cases hk : N k < n - 1
      · have := N_strict k hk; omega
      · have := N_le_succ k; omega
  have hJex : ∃ k, N k = n - 1 := ⟨n - 1, by have := N_ge (n - 1); have := N_lt (n - 1); omega⟩
  set J := Nat.find hJex with hJ_def
  have hJ : N J = n - 1 := Nat.find_spec hJex
  have hbelow : ∀ k, k < J → N k < n - 1 := fun k hk => by
    have := Nat.find_min hJex hk
    have := N_lt k
    omega
  have hstrict : ∀ k d, k + d ≤ J → N k + d ≤ N (k + d) := by
    intro k d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := N_strict (k + d) (hbelow _ (by omega))
      show N k + (d + 1) ≤ N (k + d + 1)
      omega
  have hlt : ∀ k, k < J → N k < N (k + 1) := fun k hk => by
    have := hstrict k 1 (by omega); omega
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
  -- a fibre meeting link `N l` ends by link `N (l+1)`
  have hreach : ∀ y l, a y ≤ N l → N l ≤ b y → b y ≤ N (l + 1) := fun y l h1 h2 => by
    rw [hNs]; exact t_le _ y _ ((hR_iff y _).mpr ⟨h1, h2⟩) (hb_mem y)
  -- every fibre lies in two consecutive blocks
  have hfib : ∀ y, ∃ l, l ≤ J ∧ N l ≤ a y ∧ b y ≤ N (l + 2) := by
    intro y
    set l := Nat.findGreatest (fun l => N l ≤ a y) J with hl_def
    have hl1 : l ≤ J := Nat.findGreatest_le J
    have hl2 : N l ≤ a y := Nat.findGreatest_spec (P := fun l => N l ≤ a y) (Nat.zero_le J)
      (by show N 0 ≤ a y; simp [hN_def, bingSeq_zero])
    refine ⟨l, hl1, hl2, ?_⟩
    rcases lt_or_eq_of_le hl1 with hlJ | hlJ
    · have hl3 : a y < N (l + 1) := by
        have := Nat.findGreatest_is_greatest (P := fun l => N l ≤ a y) (n := J) (k := l + 1)
          (by omega) (by omega)
        simpa using this
      by_cases hb : b y < N (l + 1)
      · exact hb.le.trans (N_mono (by omega))
      · push_neg at hb
        have := hreach y (l + 1) hl3.le hb
        exact this
    · have := hb_lt y
      have := N_mono (show J ≤ l + 2 by omega)
      omega
  -- a window spanning at least two blocks is nonempty
  have hnonempty : ∀ p q, p + 2 ≤ q → q ≤ J → (G (N p) (N q)).Nonempty := by
    intro p q hpq hqJ
    obtain ⟨z, hz1, hz2⟩ := t_spec (N (p + 1)) (N_lt _)
    rw [← hNs] at hz2
    refine ⟨z, hG1 _ _ _ fun i hi => ⟨?_, ?_⟩⟩
    · by_contra hcon
      push_neg at hcon
      have hm : N p ≤ N (p + 1) := N_mono (by omega)
      have hzp : R z (N p) := hR3 z i (N p) (N (p + 1)) hi hz1 hcon.le hm
      have h1 := t_le (N p) z _ hzp hz2
      rw [← hNs] at h1
      have := hstrict (p + 1) 1 (by omega)
      omega
    · have h1 := t_le (N (p + 1)) z i hz1 hi
      rw [← hNs] at h1
      exact h1.trans (N_mono (by omega))
  -- the windows
  set K := (J - 2) / 3 with hK_def
  have hKJ : 3 * K ≤ J := by omega
  set q : ℕ → ℕ := fun k => if k = K then J else 3 * k + 4 with hq_def
  set L : ℕ → Set B := fun k => G (N (3 * k)) (N (q k)) with hL_def
  have hqJ : ∀ k, k ≤ K → q k ≤ J := fun k hk => by
    simp only [hq_def]; split_ifs with h
    · exact le_rfl
    · omega
  have hq_ge : ∀ k, k ≤ K → 3 * k ≤ q k := fun k hk => by
    simp only [hq_def]; split_ifs <;> omega
  have hq_le : ∀ k, k ≤ K → q k ≤ 3 * k + 4 := fun k hk => by
    simp only [hq_def]; split_ifs with h
    · omega
    · omega
  have hcover : ∀ y, ∃ k, k ≤ K ∧ y ∈ L k := by
    intro y
    obtain ⟨l, hlJ, hl1, hl2⟩ := hfib y
    refine ⟨min (l / 3) K, min_le_right _ _, hG1 _ _ _ fun i hi => ?_⟩
    rw [hR_iff] at hi
    have m1 : N (3 * min (l / 3) K) ≤ N l := N_mono (by omega)
    refine ⟨by omega, ?_⟩
    simp only [hq_def]
    split_ifs with h
    · have := hb_lt y; omega
    · have hk : min (l / 3) K = l / 3 := by omega
      rw [hk]
      have := N_mono (show l + 2 ≤ 3 * (l / 3) + 4 by omega)
      omega
  have hne : ∀ k, k ≤ K → (L k).Nonempty := by
    intro k hk
    by_cases hJ2 : 2 ≤ J
    · refine hnonempty _ _ ?_ (hqJ k hk)
      simp only [hq_def]; split_ifs <;> omega
    · have hK0 : K = 0 := by omega
      have hk0 : k = 0 := by omega
      refine ⟨y₀, hG1 _ _ _ fun i hi => ⟨?_, ?_⟩⟩
      · simp [hk0, hN_def, bingSeq_zero]
      · have hqk : q k = J := by simp [hq_def, hk0, hK0]
        rw [hqk, hJ]
        have := hR1 _ _ hi
        omega
  have hdisj : ∀ k k', k + 2 ≤ k' → k' ≤ K → ∀ y, y ∈ L k → y ∈ L k' → False := by
    intro k k' hkk hk' y h1 h2
    refine hG3 y _ _ _ _ h1 h2 ?_
    have hqk : q k = 3 * k + 4 := by simp only [hq_def]; rw [if_neg (by omega)]
    rw [hqk]
    have hJ2 : 2 ≤ J := by
      by_contra h
      omega
    have h1 := hstrict (3 * k + 4) 2 (by omega)
    have h2 := N_mono (show 3 * k + 4 + 2 ≤ 3 * k' by omega)
    omega
  -- consecutive windows meet, by connectedness
  have hconsec : ∀ k, k + 1 ≤ K → (L k ∩ L (k + 1)).Nonempty := by
    intro k hk
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    set U := ⋃ (i : ℕ) (_ : i ≤ k), L i with hU_def
    set V := ⋃ (i : ℕ) (_ : k + 1 ≤ i ∧ i ≤ K), L i with hV_def
    have hUo : IsOpen U := isOpen_biUnion fun i _ => hGo _ _
    have hVo : IsOpen V := isOpen_biUnion fun i _ => hGo _ _
    have hcov : univ ⊆ U ∪ V := by
      intro y _
      obtain ⟨i, hi, hy⟩ := hcover y
      by_cases hik : i ≤ k
      · exact Or.inl (mem_biUnion hik hy)
      · exact Or.inr (mem_biUnion (x := i) ⟨by omega, hi⟩ hy)
    have hU : (univ ∩ U).Nonempty := by
      obtain ⟨y, hy⟩ := hne k (by omega)
      exact ⟨y, mem_univ _, mem_biUnion (le_refl k) hy⟩
    have hV : (univ ∩ V).Nonempty := by
      obtain ⟨y, hy⟩ := hne (k + 1) hk
      exact ⟨y, mem_univ _, mem_biUnion (x := k + 1) ⟨le_refl _, hk⟩ hy⟩
    obtain ⟨y, -, hyU, hyV⟩ := isPreconnected_univ (α := B) U V hUo hVo hcov hU hV
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hyU
    obtain ⟨i', hi', hyi'⟩ := mem_iUnion₂.mp hyV
    by_cases h2 : i + 2 ≤ i'
    · exact hdisj i i' h2 hi'.2 y hyi hyi'
    · have e1 : i = k := by omega
      have e2 : i' = k + 1 := by omega
      subst e1; subst e2
      have : y ∈ L i ∩ L (i + 1) := ⟨hyi, hyi'⟩
      rw [hcon] at this
      exact this
  -- the mesh
  have z_ex : ∀ l, ∃ z, R z (N l) ∧ R z (N (l + 1)) := fun l => by
    rw [hNs]; exact t_spec _ (N_lt l)
  choose z hz using z_ex
  have hz_step : ∀ l, dist (z l) (z (l + 1)) < η := fun l =>
    hR5 _ _ _ _ (hz l).2 (hz (l + 1)).1 (by omega) (by omega)
  have hz_dist : ∀ l d, dist (z l) (z (l + d)) ≤ d * η := by
    intro l d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 := hz_step (l + d)
      calc dist (z l) (z (l + (d + 1)))
          ≤ dist (z l) (z (l + d)) + dist (z (l + d)) (z (l + d + 1)) := dist_triangle _ _ _
        _ ≤ d * η + η := by linarith
        _ = ((d + 1 : ℕ) : ℝ) * η := by push_cast; ring
  have hη : 0 ≤ η := by
    obtain ⟨i, hi⟩ := hR2 y₀
    exact (dist_nonneg).trans (hR5 y₀ y₀ i i hi hi (by omega) (by omega)).le
  have hnear : ∀ y k, k ≤ K → y ∈ L k →
      ∃ l, 3 * k ≤ l ∧ l ≤ 3 * k + 3 ∧ dist y (z l) < η := by
    intro y k hk hy
    obtain ⟨i, hi, h1, h2⟩ := hG2 _ _ _ hy
    have hqk1 := hq_ge k hk
    have hqk2 := hq_le k hk
    set top := max (3 * k) (q k - 1) with htop
    set l := Nat.findGreatest (fun l => N l ≤ i) top with hl_def
    have hl1 : 3 * k ≤ l := Nat.le_findGreatest (le_max_left _ _) h1
    have hl2 : l ≤ top := Nat.findGreatest_le top
    have hl3 : N l ≤ i := Nat.findGreatest_spec (P := fun l => N l ≤ i) (le_max_left _ _) h1
    have hl4 : i ≤ N (l + 1) := by
      rcases lt_or_eq_of_le hl2 with hlt' | heq
      · have := Nat.findGreatest_is_greatest (P := fun l => N l ≤ i) (n := top) (k := l + 1)
          (by omega) (by omega)
        push_neg at this
        exact this.le
      · rcases Nat.lt_or_ge (3 * k) (q k) with hlt'' | hge
        · have e : l + 1 = q k := by omega
          rw [e]; exact h2
        · have e : q k = 3 * k := by omega
          rw [e] at h2
          exact h2.trans (N_mono (by omega))
    have hzi : R (z l) i := hR3 _ _ _ _ (hz l).1 (hz l).2 hl3 hl4
    have htop3 : top ≤ 3 * k + 3 := max_le (by omega) (by omega)
    exact ⟨l, hl1, hl2.trans htop3, hR5 _ _ _ _ hi hzi (by omega) (by omega)⟩
  have hdist : ∀ y y' k, k ≤ K → y ∈ L k → y' ∈ L k → dist y y' ≤ 5 * η := by
    intro y y' k hk hy hy'
    obtain ⟨l, hl1, hl2, hd⟩ := hnear y k hk hy
    obtain ⟨l', hl1', hl2', hd'⟩ := hnear y' k hk hy'
    have hm : dist (z l) (z l') ≤ 3 * η := by
      rcases le_total l l' with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        have := hz_dist l d
        have hd3 : (d : ℝ) ≤ 3 := by exact_mod_cast (by omega : d ≤ 3)
        nlinarith
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        have := hz_dist l' d
        have hd3 : (d : ℝ) ≤ 3 := by exact_mod_cast (by omega : d ≤ 3)
        rw [dist_comm]; nlinarith
    calc dist y y' ≤ dist y (z l) + dist (z l) (z l') + dist (z l') y' := dist_triangle4 _ _ _ _
      _ ≤ η + 3 * η + η := by rw [dist_comm (z l') y']; linarith
      _ = 5 * η := by ring
  -- the chain
  refine ⟨J, K, hJ, hlt, rfl,
    { link := fun k => L k.val, isOpen := fun k => hGo _ _, adjacent := ?_ }, ?_, ?_, ?_⟩
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · rintro ⟨y, h1, h2⟩
      by_contra hfar
      have : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by omega
      rcases this with h | h
      · exact hdisj _ _ h (by omega) y h1 h2
      · exact hdisj _ _ h (by omega) y h2 h1
    · intro hclose
      have : i.val = j.val ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
      rcases this with h | h | h
      · obtain ⟨y, hy⟩ := hne i (by omega)
        exact ⟨y, hy, by simpa [← h] using hy⟩
      · obtain ⟨y, hy1, hy2⟩ := hconsec i.val (by omega)
        exact ⟨y, hy1, by simpa [← h] using hy2⟩
      · obtain ⟨y, hy1, hy2⟩ := hconsec j.val (by omega)
        exact ⟨y, by simpa [← h] using hy2, hy1⟩
  · intro y _
    obtain ⟨k, hk, hy⟩ := hcover y
    exact mem_iUnion.mpr ⟨⟨k, by omega⟩, hy⟩
  · intro k
    simp only [hL_def, hq_def]
    split_ifs <;> rfl
  · intro k
    have hk : k.val ≤ K := by have := k.isLt; omega
    refine ⟨Metric.isBounded_iff.mpr ⟨5 * η, fun x hx y hy => hdist x y k hk hx hy⟩, ?_⟩
    exact Metric.diam_le_of_forall_dist_le (by linarith) fun x hx y hy => hdist x y k hk hx hy

end HPC.Plane.Mono
