import HPC.BJ59.Thm8

/-!
# Batch 200, §4: the corollary to Theorem 8 (p. 178)

Route: commission 200 §4 (numbering from 0). `G` is the chain of Theorem 8 for the pattern
`4i + c ↦ H₁(i)` (`4ℓ` links); `ε` is below a Lebesgue number of `G` and below half of a uniform
lower bound `κ` for the spread of the fibres (`exists_fibre_spread`); `R(f) = ⌊a/4⌋` for a chosen
link `g_a ⊇ f`. The three consecutive links come from a discrete intermediate value argument
(`walk_core` and its variants): along a covering subchain the indices `a` run from `≤ 1` to
`≥ 4ℓ − 2` in steps of at most one.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ### Walks with steps of at most one -/

/-- A walk with steps of at most one from `≤ b + 1` to `≥ b + 4` stays in `[b, b + 3]` for three
consecutive steps. -/
theorem walk_core (a : ℕ → ℤ) {p q : ℕ} (hpq : p ≤ q)
    (hstep : ∀ j, p ≤ j → j < q → |a (j + 1) - a j| ≤ 1) {b : ℤ} (hp : a p ≤ b + 1)
    (hq : b + 4 ≤ a q) :
    ∃ k, p ≤ k ∧ k + 2 ≤ q ∧ ∀ c ≤ 2, b ≤ a (k + c) ∧ a (k + c) ≤ b + 3 := by
  classical
  have hex : ∃ j, p ≤ j ∧ b + 4 ≤ a j := ⟨q, hpq, hq⟩
  set j1 := Nat.find hex with hj1
  have hj1s := Nat.find_spec hex
  have hj1q : j1 ≤ q := Nat.find_min' hex ⟨hpq, hq⟩
  have hj1min : ∀ j, p ≤ j → j < j1 → a j < b + 4 := fun j h1 h2 => by
    by_contra h; push_neg at h; exact Nat.find_min hex h2 ⟨h1, h⟩
  have hpj1 : p < j1 := by
    rcases eq_or_lt_of_le hj1s.1 with h | h
    · rw [← h] at hj1s; linarith [hj1s.2]
    · exact h
  set P : ℕ → Prop := fun j => p ≤ j ∧ a j ≤ b + 1
  set j0 := Nat.findGreatest P (j1 - 1) with hj0
  have hj0s : P j0 := Nat.findGreatest_spec (m := p) (by omega) ⟨le_rfl, hp⟩
  have hj0le : j0 ≤ j1 - 1 := Nat.findGreatest_le _
  have hj0max : ∀ j, j0 < j → j ≤ j1 - 1 → ¬ P j := fun j h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hst : ∀ j, p ≤ j → j < q → a (j + 1) - a j ≤ 1 ∧ a j - a (j + 1) ≤ 1 := fun j h1 h2 => by
    have := hstep j h1 h2
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hmid : ∀ j, j0 < j → j < j1 → b + 1 < a j ∧ a j < b + 4 := fun j h1 h2 => by
    refine ⟨?_, hj1min j (by omega) h2⟩
    by_contra h; push_neg at h
    exact hj0max j h1 (by omega) ⟨by omega, h⟩
  -- `j0 + 1 < j1`
  have h01 : j0 + 1 < j1 := by
    by_contra h
    have e : j0 + 1 = j1 := by omega
    have := hst j0 hj0s.1 (by omega)
    rw [e] at this
    linarith [hj0s.2, hj1s.2, this.1]
  have ha1 := hmid (j0 + 1) (by omega) h01
  have hs0 := hst j0 hj0s.1 (by omega)
  -- `j0 + 2 < j1`
  have h02 : j0 + 2 < j1 := by
    by_contra h
    have e : j0 + 1 + 1 = j1 := by omega
    have := hst (j0 + 1) (by omega) (by omega)
    rw [e] at this
    linarith [hj0s.2, hj1s.2, this.1, hs0.1]
  have ha2 := hmid (j0 + 2) (by omega) h02
  refine ⟨j0, hj0s.1, by omega, fun c hc => ?_⟩
  interval_cases c
  · simp only [add_zero]
    constructor <;> linarith [hj0s.2, hs0.2, ha1.1]
  · constructor <;> linarith [ha1.1, ha1.2, hs0.1, hj0s.2]
  · have hs1 := hst (j0 + 1) (by omega) (by omega)
    constructor <;> linarith [ha2.1, hs1.1, ha1.1, hs0.1, hj0s.2]

/-- `walk_core` with the two positions in either order, inside an interval `[v, w]`. -/
theorem walk_any (a : ℕ → ℤ) {v w : ℕ}
    (hstep : ∀ j, v ≤ j → j < w → |a (j + 1) - a j| ≤ 1) {p q : ℕ} (hpv : v ≤ p) (hpw : p ≤ w)
    (hqv : v ≤ q) (hqw : q ≤ w) {b : ℤ} (hp : a p ≤ b + 1) (hq : b + 4 ≤ a q) :
    ∃ k, v ≤ k ∧ k + 2 ≤ w ∧ ∀ c ≤ 2, b ≤ a (k + c) ∧ a (k + c) ≤ b + 3 := by
  rcases le_total p q with hpq | hqp
  · obtain ⟨k, hk1, hk2, hk⟩ := walk_core a hpq (fun j h1 h2 => hstep j (by omega) (by omega))
      hp hq
    exact ⟨k, by omega, by omega, hk⟩
  · set a' : ℕ → ℤ := fun j => a (q + p - j)
    have hstep' : ∀ j, q ≤ j → j < p → |a' (j + 1) - a' j| ≤ 1 := by
      intro j h1 h2
      simp only [a']
      have := hstep (q + p - (j + 1)) (by omega) (by omega)
      rw [show q + p - (j + 1) + 1 = q + p - j by omega] at this
      rw [abs_sub_comm]; exact this
    obtain ⟨k, hk1, hk2, hk⟩ := walk_core a' hqp hstep'
      (by simp only [a']; rw [show q + p - q = p by omega]; exact hp)
      (by simp only [a']; rw [show q + p - p = q by omega]; exact hq)
    refine ⟨q + p - k - 2, by omega, by omega, fun c hc => ?_⟩
    have := hk (2 - c) (by omega)
    simp only [a'] at this
    rw [show q + p - (k + (2 - c)) = q + p - k - 2 + c by omega] at this
    exact this

/-- The reflected form: from `≤ b − 1` to `≥ b + 2`. -/
theorem walk_any' (a : ℕ → ℤ) {v w : ℕ}
    (hstep : ∀ j, v ≤ j → j < w → |a (j + 1) - a j| ≤ 1) {p q : ℕ} (hpv : v ≤ p) (hpw : p ≤ w)
    (hqv : v ≤ q) (hqw : q ≤ w) {b : ℤ} (hp : a p ≤ b - 1) (hq : b + 2 ≤ a q) :
    ∃ k, v ≤ k ∧ k + 2 ≤ w ∧ ∀ c ≤ 2, b ≤ a (k + c) ∧ a (k + c) ≤ b + 3 := by
  set a' : ℕ → ℤ := fun j => 2 * b + 3 - a j
  obtain ⟨k, hk1, hk2, hk⟩ := walk_any a' (fun j h1 h2 => by
    simp only [a']; rw [show 2 * b + 3 - a (j + 1) - (2 * b + 3 - a j) = -(a (j + 1) - a j) by
      ring, abs_neg]; exact hstep j h1 h2) hqv hqw hpv hpw (b := b)
    (by simp only [a']; linarith) (by simp only [a']; linarith)
  refine ⟨k, hk1, hk2, fun c hc => ?_⟩
  have := hk c hc
  simp only [a'] at this
  constructor <;> linarith [this.1, this.2]

section Cor

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- **Uniform spread of the fibres**: if `f` is open and every fibre is non-degenerate, every fibre
contains two points at distance at least a fixed `κ > 0`. -/
theorem exists_fibre_spread {f : X → unitInterval} (hfo : IsOpenMap f)
    (hnt : ∀ t, (f ⁻¹' {t}).Nontrivial) :
    ∃ κ > 0, ∀ t, ∃ p ∈ f ⁻¹' {t}, ∃ q ∈ f ⁻¹' {t}, κ ≤ dist p q := by
  classical
  choose p hp q hq hpq using hnt
  have hd : ∀ t, 0 < dist (p t) (q t) := fun t => dist_pos.2 (hpq t)
  set O : unitInterval → Set unitInterval := fun t =>
    f '' ball (p t) (dist (p t) (q t) / 3) ∩ f '' ball (q t) (dist (p t) (q t) / 3)
  have hO : ∀ t, IsOpen (O t) := fun t => (hfo _ isOpen_ball).inter (hfo _ isOpen_ball)
  have htO : ∀ t, t ∈ O t := fun t => ⟨⟨p t, mem_ball_self (by linarith [hd t]), hp t⟩,
    ⟨q t, mem_ball_self (by linarith [hd t]), hq t⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO fun t _ => mem_iUnion.2 ⟨t, htO t⟩
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_forall_le
    (fun t : {t // t ∈ s} => dist (p t) (q t) / 3) fun t => by simp only; linarith [hd t]
  refine ⟨κ, hκ, fun t' => ?_⟩
  obtain ⟨t, hts, ht'⟩ := mem_iUnion₂.1 (hs (mem_univ t'))
  obtain ⟨⟨p', hp', hp'f⟩, ⟨q', hq', hq'f⟩⟩ := ht'
  refine ⟨p', hp'f, q', hq'f, ?_⟩
  have h1 : κ ≤ dist (p t) (q t) / 3 := hκle ⟨t, hts⟩
  rw [mem_ball] at hp' hq'
  linarith [dist_triangle (p t) p' (q t), dist_triangle p' q' (q t), dist_comm p' (p t)]

/-- **Corollary to Theorem 8** (p. 178), with `D(r, s)` an abstract chain of `ℓ` indices mapped
onto `E` by `H₁`, and the arc `Q(i/k, (i+1)/k)` reparametrized as the whole space. The
irreducibility of `F` is not assumed. -/
theorem bj_theorem8_cor {f : X → unitInterval} (hf : IsContArcPA f)
    (hS : IsSnakeLike (univ : Set X)) {n ℓ : ℕ} (hn : 3 ≤ n) (E : Chain X n)
    (hE : univ ⊆ E.union) (hEf : ∀ t j, (E.link j ∩ f ⁻¹' {t}).Nonempty)
    (H₁ : Fin ℓ → Fin n) (hH₁ : IsChainMap H₁) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain X N), IsEpsChain F ε → univ ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧ Function.Surjective R ∧
        (∀ j, F.link j ⊆ E.link (H₁ (R j))) ∧
        ∀ (t : unitInterval) (v w : ℕ) (hw : w < N), v ≤ w →
          f ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  classical
  have hℓ : 0 < ℓ := by
    obtain ⟨i, -⟩ := hH₁s ⟨0, by omega⟩
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  -- the chain `G` of Theorem 8, with `4ℓ` links
  set Hq : Fin (4 * ℓ) → Fin n := fun a => H₁ ⟨a.val / 4, by omega⟩ with hHqdef
  have hHq : IsChainMap Hq := fun a b hab => hH₁ _ _ (by simp only; omega)
  have hHqs : Function.Surjective Hq := fun j => by
    obtain ⟨i, hi⟩ := hH₁s j
    refine ⟨⟨4 * i.val, by omega⟩, ?_⟩
    simp only [hHqdef]
    rw [← hi]
    congr 1
    ext
    simp only
    omega
  obtain ⟨G, -, hGcov, hGf, hGE⟩ := bj_theorem8 hf hS hn E hE hEf Hq hHq hHqs
  -- a Lebesgue number of `G`, and the spread of the fibres
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := X)) G.isOpen
    (fun x _ => hGcov (mem_univ x))
  obtain ⟨κ, hκ, hκf⟩ := exists_fibre_spread hf.2.1 fun t => (hf.2.2.2 t).2.2
  refine ⟨min δ (κ / 2), lt_min hδ (by linarith), fun N F hFε hFcov => ?_⟩
  have hg : ∀ j : Fin N, ∃ a : Fin (4 * ℓ), F.link j ⊆ G.link a := by
    intro j
    obtain ⟨x, hx⟩ := F.link_nonempty j
    obtain ⟨a, ha⟩ := hleb x (mem_univ x)
    refine ⟨a, fun y hy => ha ?_⟩
    rw [mem_ball]
    calc dist y x ≤ diam (F.link j) := dist_le_diam_of_mem (hFε j).1 hy hx
      _ < min δ (κ / 2) := (hFε j).2
      _ ≤ δ := min_le_left _ _
  choose g hgF using hg
  set R : Fin N → Fin ℓ := fun j => ⟨(g j).val / 4, by omega⟩ with hRdef
  have hadj : ∀ j k : Fin N, ((j : ℤ) - k).natAbs ≤ 1 → ((g j : ℤ) - g k).natAbs ≤ 1 := by
    intro j k hjk
    obtain ⟨x, hxj, hxk⟩ := (F.adjacent j k).2 hjk
    exact (G.adjacent _ _).1 ⟨x, hgF j hxj, hgF k hxk⟩
  have hR : IsChainMap R := fun j k hjk => by
    have := hadj j k hjk
    simp only [hRdef]
    omega
  have hRE : ∀ j, F.link j ⊆ E.link (H₁ (R j)) := fun j => (hgF j).trans (hGE (g j))
  have hmain : ∀ (t : unitInterval) (v w : ℕ) (hw : w < N), v ≤ w →
      f ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
      ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
        ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
    intro t v w hw hvw hcov d
    set a : ℕ → ℤ := fun j => if h : j < N then ((g ⟨j, h⟩ : ℕ) : ℤ) else 0 with hadef
    have haval : ∀ j (h : j < N), a j = ((g ⟨j, h⟩ : ℕ) : ℤ) := fun j h => by
      simp only [hadef, dif_pos h]
    have hstep : ∀ j, v ≤ j → j < w → |a (j + 1) - a j| ≤ 1 := by
      intro j _ hj
      rw [haval (j + 1) (by omega), haval j (by omega)]
      have := hadj ⟨j + 1, by omega⟩ ⟨j, by omega⟩ (by simp)
      rw [abs_le]
      constructor <;> omega
    obtain ⟨z0, hz0, hz0f⟩ := hGf t ⟨0, by omega⟩
    obtain ⟨k0, ⟨hk0v, hk0w⟩, hz0k⟩ := mem_iUnion₂.1 (hcov hz0f)
    have ha0 : a k0 ≤ 1 := by
      have := (G.adjacent_iff (g k0) ⟨0, by omega⟩).1 ⟨z0, hgF k0 hz0k, hz0⟩
      rw [haval k0 k0.isLt, Fin.eta]
      simp only at this
      omega
    obtain ⟨z1, hz1, hz1f⟩ := hGf t ⟨4 * ℓ - 1, by omega⟩
    obtain ⟨k1, ⟨hk1v, hk1w⟩, hz1k⟩ := mem_iUnion₂.1 (hcov hz1f)
    have ha1 : (4 * ℓ : ℤ) - 2 ≤ a k1 := by
      have := (G.adjacent_iff (g k1) ⟨4 * ℓ - 1, by omega⟩).1 ⟨z1, hgF k1 hz1k, hz1⟩
      rw [haval k1 k1.isLt, Fin.eta]
      simp only at this
      omega
    have hblock : ∀ k (hk : k + 2 ≤ w),
        (∀ c ≤ 2, (4 * d.val : ℤ) ≤ a (k + c) ∧ a (k + c) ≤ 4 * d.val + 3) →
        ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
      intro k hk h c hc
      have := h c hc
      rw [haval (k + c) (by omega)] at this
      exact Fin.ext (by simp only [hRdef]; omega)
    by_cases hℓ1 : ℓ = 1
    · have hvw2 : v + 2 ≤ w := by
        by_contra h
        obtain ⟨p, hp, q, hq, hpq⟩ := hκf t
        obtain ⟨kp, ⟨hkp1, hkp2⟩, hpk⟩ := mem_iUnion₂.1 (hcov hp)
        obtain ⟨kq, ⟨hkq1, hkq2⟩, hqk⟩ := mem_iUnion₂.1 (hcov hq)
        have := dist_lt_of_adjacent hFε (a := kp) (b := kq) (by omega) hpk hqk
        linarith [min_le_right δ (κ / 2)]
      refine ⟨v, hvw2, le_rfl, fun c hc => Fin.ext ?_⟩
      have := d.isLt
      have := (R ⟨v + c, by omega⟩).isLt
      omega
    · by_cases hd : d.val + 1 < ℓ
      · obtain ⟨k, hk1, hk2, hk⟩ := walk_any a hstep hk0v hk0w hk1v hk1w
          (b := 4 * d.val) (by omega) (by omega)
        exact ⟨k, hk2, hk1, hblock k hk2 hk⟩
      · obtain ⟨k, hk1, hk2, hk⟩ := walk_any' a hstep hk0v hk0w hk1v hk1w
          (b := 4 * d.val) (by omega) (by omega)
        exact ⟨k, hk2, hk1, hblock k hk2 hk⟩
  refine ⟨R, hR, fun d => ?_, hRE, hmain⟩
  obtain ⟨x0, -⟩ := hf.2.2.1 0
  obtain ⟨j0, -⟩ := mem_iUnion.1 (hFcov (mem_univ x0))
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j0.isLt
  obtain ⟨k, hk, -, hkd⟩ := hmain 0 0 (N - 1) (by omega) (Nat.zero_le _) (fun x _ => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hFcov (mem_univ x))
    exact mem_iUnion₂.2 ⟨j, ⟨Nat.zero_le _, by omega⟩, hj⟩) d
  exact ⟨_, hkd 0 (by omega)⟩

end Cor

end HPC.BJ59
