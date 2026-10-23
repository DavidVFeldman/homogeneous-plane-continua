import HPC.BJ59.Thm10Window

/-!
# Batch 201, §4 (f)–(g): gluing the maps of the pieces

The construction of `E′` and `K` of commission 201 §4 (f) and its verification §4 (g), stated
abstractly: given a fine chain `F` on `Y`, pieces `p = 0, …, M` with chain maps `R p` of `F` into
runs `[σ p, σ' p]` of `D` (Conditions (R1)–(R3) of §4 (d) in the form `hP1`, `hP2a`, `hP2b`,
`hC0`, `hC1`), and windows `[l w, l' w]` (`w < M`) between consecutive pieces, with runs of `F`
on which both neighbouring maps take every value three times, the conclusion of the step holds.

The map `K` of a link `e` of `G` is `R (π e) (β e)`: `π e` counts the windows whose right side
(with the transition set) contains `e`, and `β e` is the transition link if `e` meets a transition
set, otherwise a link of `F` containing `e`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-- `R` takes every value `j ∈ [σ, σ']` at three consecutive indices of the run `[t, u]`. -/
def IsPatternOn {N n : ℕ} (R : Fin N → Fin n) (σ σ' t u : ℕ) : Prop :=
  ∀ j : Fin n, σ ≤ j.val → j.val ≤ σ' → ∃ k : ℕ, k + 2 ≤ u ∧ t ≤ k ∧
    ∀ c ≤ 2, ∃ h : k + c < N, R ⟨k + c, h⟩ = j

theorem unitInterval_mem_Icc_iff {a b s : unitInterval} :
    s ∈ Icc a b ↔ (a : ℝ) ≤ s ∧ (s : ℝ) ≤ b := Iff.rfl

theorem unitInterval_mem_Ioo_iff {a b s : unitInterval} :
    s ∈ Ioo a b ↔ (a : ℝ) < s ∧ (s : ℝ) < b := Iff.rfl

section Glue

variable {X Y : Type} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]

/-- **The gluing of the pieces** (commission 201 §4 (e)–(g)). -/
theorem bj_glue {f : X → unitInterval} {g : Y → unitInterval} (hg : IsContArcPA g)
    (hSY : IsSnakeLike (univ : Set Y))
    (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0}) (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) {n m : ℕ} (D : Chain X n)
    (hDp : HasPrivatePoints D) (E : Chain Y m) (H : Fin n → Fin m) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (F : Chain Y N) (hF : univ ⊆ F.union)
    {M : ℕ} (hM : 1 ≤ M) (l l' : ℕ → ℝ)
    (hl0 : 0 < l 0) (hll' : ∀ w < M, l w < l' w) (hl'l : ∀ w, w + 1 < M → l' w < l (w + 1))
    (hl'1 : l' (M - 1) < 1)
    (α β : ℕ → ℝ) (hα0 : α 0 ≤ 0) (hα : ∀ p, 1 ≤ p → p ≤ M → α p ≤ l (p - 1))
    (hβ : ∀ p < M, l' p < β p) (hβM : 1 ≤ β M)
    (σ σ' : ℕ → ℕ) (R : ℕ → Fin N → Fin n)
    (hRc : ∀ p ≤ M, IsChainMap (R p))
    (hRS : ∀ p ≤ M, ∀ b, σ p ≤ (R p b).val ∧ (R p b).val ≤ σ' p)
    (hP1 : ∀ p ≤ M, ∀ b, ∀ y ∈ F.link b, α p ≤ (g y : ℝ) → (g y : ℝ) ≤ β p →
      y ∈ E.link (H (R p b)))
    (hP2a : ∀ p ≤ M, ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p → ∀ j : Fin n,
      σ p ≤ j.val → j.val ≤ σ' p → (D.link j ∩ f ⁻¹' {x}).Nonempty)
    (hP2b : ∀ p ≤ M, ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p →
      f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : σ p ≤ j.val ∧ j.val ≤ σ' p), D.link j)
    (t u : ℕ → ℕ) (htu : ∀ w < M, t w ≤ u w) (huN : ∀ w < M, u w < N)
    (hTf : ∀ w < M, ∀ x : unitInterval, l w ≤ x → (x : ℝ) ≤ l' w → ∀ k : Fin N,
      t w ≤ k.val → k.val ≤ u w → (F.link k ∩ g ⁻¹' {x}).Nonempty)
    (hTc : ∀ w < M, ∀ x : unitInterval, l w ≤ x → (x : ℝ) ≤ l' w →
      g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : t w ≤ k.val ∧ k.val ≤ u w), F.link k)
    (hTp : ∀ w < M, IsPatternOn (R w) (σ w) (σ' w) (t w) (u w) ∧
      IsPatternOn (R (w + 1)) (σ (w + 1)) (σ' (w + 1)) (t w) (u w))
    (hout : ∀ p ≤ M, ∀ x : unitInterval, (p = 0 ∨ l' (p - 1) < x) → (p = M ∨ (x : ℝ) < l p) →
      ∃ t' u', t' ≤ u' ∧ u' < N ∧ (∀ k : Fin N, t' ≤ k.val → k.val ≤ u' →
        (F.link k ∩ g ⁻¹' {x}).Nonempty) ∧ IsPatternOn (R p) (σ p) (σ' p) t' u')
    (hC0 : ∀ b (z : g ⁻¹' {0}), (z : Y) ∈ F.link b → (h₀.symm z : X) ∈ D.link (R 0 b))
    (hC1 : ∀ b (z : g ⁻¹' {1}), (z : Y) ∈ F.link b → (h₁.symm z : X) ∈ D.link (R M b)) :
    ∃ (N' : ℕ) (E' : Chain Y N') (K : Fin N' → Fin n), univ ⊆ E'.union ∧ IsBJChain E' ∧
      IsEpsChain E' δ ∧ HasPrivatePoints E' ∧ IsFibreChainMap g f E' D K ∧
      EndCompat g f h₀.symm h₁.symm E' D K ∧ ∀ k, E'.link k ⊆ E.link (H (K k)) := by
  classical
  ------------------------------------------------------------------
  -- the windows
  ------------------------------------------------------------------
  have hmono0 : ∀ d w, w + d + 1 < M → l' w < l (w + d + 1) := by
    intro d
    induction d with
    | zero => intro w hw; exact hl'l w (by omega)
    | succ d ih =>
      intro w hw
      have h1 := ih w (by omega)
      have h2 := hll' (w + d + 1) (by omega)
      have h3 := hl'l (w + d + 1) (by omega)
      rw [show w + (d + 1) + 1 = w + d + 1 + 1 by omega]
      linarith
  have hmono : ∀ w w', w < w' → w' < M → l' w < l w' := by
    intro w w' h1 h2
    have := hmono0 (w' - w - 1) w (by omega)
    rwa [show w + (w' - w - 1) + 1 = w' by omega] at this
  have hl_pos : ∀ w < M, 0 < l w := by
    intro w hw
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; exact hl0
    · linarith [hmono 0 w h hw, hll' 0 (by omega)]
  have hl'_lt : ∀ w < M, l' w < 1 := by
    intro w hw
    rcases Nat.lt_or_ge w (M - 1) with h | h
    · linarith [hmono w (M - 1) h (by omega), hll' (M - 1) (by omega)]
    · rw [show w = M - 1 by omega]; exact hl'1
  set aw : ℕ → unitInterval := fun w => Set.projIcc 0 1 zero_le_one (l w) with haw_def
  set bw : ℕ → unitInterval := fun w => Set.projIcc 0 1 zero_le_one (l' w) with hbw_def
  have haw : ∀ w < M, ((aw w : unitInterval) : ℝ) = l w := fun w hw => by
    simp only [haw_def]
    rw [Set.projIcc_of_mem _ ⟨(hl_pos w hw).le, by linarith [hll' w hw, hl'_lt w hw]⟩]
  have hbw : ∀ w < M, ((bw w : unitInterval) : ℝ) = l' w := fun w hw => by
    simp only [hbw_def]
    rw [Set.projIcc_of_mem _ ⟨by linarith [hll' w hw, hl_pos w hw], (hl'_lt w hw).le⟩]
  -- the intervals of the pieces contain the windows next to them
  have hαw : ∀ w < M, α w ≤ l w := by
    intro w hw
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; linarith [hl0]
    · have := hα w h hw.le
      have := hmono (w - 1) w (by omega) hw
      linarith [hll' (w - 1) (by omega)]
  have hαw1 : ∀ w < M, α (w + 1) ≤ l w := fun w hw => by
    have := hα (w + 1) (by omega) (by omega); simpa using this
  have hβw1 : ∀ w < M, l' w < β (w + 1) := by
    intro w hw
    rcases Nat.lt_or_ge (w + 1) M with h | h
    · linarith [hl'l w h, hll' (w + 1) h, hβ (w + 1) h]
    · rw [show w + 1 = M by omega]; linarith [hl'_lt w hw]
  ------------------------------------------------------------------
  -- transition links, transition sets and sides
  ------------------------------------------------------------------
  have hNpos : 0 < N := by
    obtain ⟨y, -⟩ := (hg.2.2.2 0).2.2.nonempty
    obtain ⟨b, -⟩ := mem_iUnion.1 (hF (mem_univ y))
    exact lt_of_le_of_lt (Nat.zero_le _) b.isLt
  haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hwin : ∀ w, w < M → ∃ (y : Fin N) (U A B : Set Y), t w ≤ y.val ∧ y.val ≤ u w ∧
      ((R w y : ℤ) - R (w + 1) y).natAbs ≤ 1 ∧ IsOpen U ∧ U ⊆ g ⁻¹' Ioo (aw w) (bw w) ∧
      closure U ⊆ F.link y ∧ IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧
      g ⁻¹' Icc 0 (aw w) ⊆ A ∧ g ⁻¹' Icc (bw w) 1 ⊆ B ∧ ∀ s ∈ Icc (aw w) (bw w),
        (∀ k : Fin N, t w ≤ k.val → k.val ≤ u w → (F.link k ∩ (A ∩ g ⁻¹' {s})).Nonempty) ∨
        (∀ k : Fin N, t w ≤ k.val → k.val ≤ u w → (F.link k ∩ (B ∩ g ⁻¹' {s})).Nonempty) := by
    intro w hw
    have hab : aw w < bw w := by
      show (aw w : ℝ) < bw w
      rw [haw w hw, hbw w hw]; exact hll' w hw
    have hTf' : ∀ s ∈ Icc (aw w) (bw w), ∀ k : Fin N, t w ≤ k.val → k.val ≤ u w →
        (F.link k ∩ g ⁻¹' {s}).Nonempty := by
      intro s hs k hk1 hk2
      rw [unitInterval_mem_Icc_iff, haw w hw, hbw w hw] at hs
      exact hTf w hw s hs.1 hs.2 k hk1 hk2
    have hTc' : g ⁻¹' Icc (aw w) (bw w) ⊆
        ⋃ (k : Fin N) (_ : t w ≤ k.val ∧ k.val ≤ u w), F.link k := by
      intro z hz
      have hz' := hz
      simp only [mem_preimage] at hz'
      rw [unitInterval_mem_Icc_iff, haw w hw, hbw w hw] at hz'
      exact hTc w hw (g z) hz'.1 hz'.2 rfl
    -- the transition link
    set x₀ : unitInterval := aw w
    have hx₀ : (x₀ : ℝ) = l w := haw w hw
    have hcovR : ∀ p, p ≤ M → α p ≤ x₀ → (x₀ : ℝ) ≤ β p →
        IsPatternOn (R p) (σ p) (σ' p) (t w) (u w) →
        f ⁻¹' {x₀} ⊆ ⋃ (a : Fin N) (_ : t w ≤ a.val ∧ a.val ≤ u w), D.link (R p a) := by
      intro p hp h1 h2 hpat z hz
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 (hP2b p hp x₀ h1 h2 hz)
      obtain ⟨k, hk1, hk2, hk⟩ := hpat j hj.1 hj.2
      obtain ⟨hkN, hkj⟩ := hk 0 (by omega)
      refine mem_iUnion₂.2 ⟨⟨k + 0, hkN⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_⟩
      rw [hkj]; exact hzj
    have hA1 : α w ≤ x₀ := by rw [hx₀]; exact hαw w hw
    have hA2 : (x₀ : ℝ) ≤ β w := by rw [hx₀]; linarith [hll' w hw, hβ w hw]
    have hB1 : α (w + 1) ≤ x₀ := by rw [hx₀]; exact hαw1 w hw
    have hB2 : (x₀ : ℝ) ≤ β (w + 1) := by rw [hx₀]; linarith [hll' w hw, hβw1 w hw]
    obtain ⟨y, hy1, hy2, hyadj⟩ := adjacent_of_properCover D (C := f ⁻¹' {x₀}) (hRc w hw.le)
      (hRc (w + 1) (by omega)) (htu w hw) (huN w hw)
      (fun a h1 h2 => hP2a w hw.le x₀ hA1 hA2 _ (hRS w hw.le a).1 (hRS w hw.le a).2)
      (fun a h1 h2 => hP2a (w + 1) (by omega) x₀ hB1 hB2 _ (hRS (w + 1) (by omega) a).1
        (hRS (w + 1) (by omega) a).2)
      (hcovR w hw.le hA1 hA2 (hTp w hw).1) (hcovR (w + 1) (by omega) hB1 hB2 (hTp w hw).2)
    obtain ⟨U, hUo, hUne, hUab, hUcl, hFU⟩ := exists_window_set hg hab F hTf' hy1 hy2
    obtain ⟨A, B, hA, hB, hAB, hABU, hA0, hB1', hdich⟩ := bj_theorem5_window hg hSY hab F
      (htu w hw) hTf' hTc' hUo hUne hUab ⟨y, hy1, hy2, hUcl⟩ hFU
    exact ⟨y, U, A, B, hy1, hy2, hyadj, hUo, hUab, hUcl, hA, hB, hAB, hABU, hA0, hB1', hdich⟩
  choose! y U A B hy1 hy2 hyadj hUo hUab hUcl hAc hBc hAB hABU hA0 hB1 hdich using hwin
  -- basic facts on the sides, in terms of `g`
  have hAleft : ∀ w < M, ∀ z, (g z : ℝ) ≤ l w → z ∈ A w := fun w hw z hz =>
    hA0 w hw (show g z ∈ Icc 0 (aw w) from ⟨(g z).2.1, by
      show (g z : ℝ) ≤ aw w; rw [haw w hw]; exact hz⟩)
  have hBright : ∀ w < M, ∀ z, l' w ≤ (g z : ℝ) → z ∈ B w := fun w hw z hz =>
    hB1 w hw (show g z ∈ Icc (bw w) 1 from ⟨by
      show (bw w : ℝ) ≤ g z; rw [hbw w hw]; exact hz, (g z).2.2⟩)
  have hUg : ∀ w < M, ∀ z ∈ U w, l w < (g z : ℝ) ∧ (g z : ℝ) < l' w := fun w hw z hz => by
    have := hUab w hw hz
    simp only [mem_preimage] at this
    rw [unitInterval_mem_Ioo_iff, haw w hw, hbw w hw] at this
    exact this
  have hABd : ∀ w < M, ∀ z ∈ A w, z ∉ B w := fun w hw z hzA hzB =>
    Set.disjoint_left.1 (hAB w hw) hzA hzB
  have hAU : ∀ w < M, ∀ z ∈ A w, z ∉ U w := fun w hw z hz hzU => by
    have : z ∈ A w ∪ B w := Or.inl hz
    rw [hABU w hw] at this
    exact this hzU
  have hBU : ∀ w < M, ∀ z ∈ B w, z ∉ U w := fun w hw z hz hzU => by
    have : z ∈ A w ∪ B w := Or.inr hz
    rw [hABU w hw] at this
    exact this hzU
  have hcovAB : ∀ w < M, ∀ z, z ∉ U w → z ∈ A w ∨ z ∈ B w := fun w hw z hz => by
    have : z ∈ (U w)ᶜ := hz
    rw [← hABU w hw] at this
    exact this
  have hBg : ∀ w < M, ∀ z ∈ B w, l w < (g z : ℝ) := fun w hw z hz => by
    by_contra h
    exact hABd w hw z (hAleft w hw z (not_lt.1 h)) hz
  have hAg : ∀ w < M, ∀ z ∈ A w, (g z : ℝ) < l' w := fun w hw z hz => by
    by_contra h
    exact hABd w hw z hz (hBright w hw z (not_lt.1 h))
  ------------------------------------------------------------------
  -- the margin and `μ`
  ------------------------------------------------------------------
  obtain ⟨m', hm', hm'le⟩ := exists_pos_forall_le (fun w : Fin M =>
    min (β w - l' w) (if w.val + 1 < M then l (w.val + 1) - l' w else 1)) (fun w => by
      refine lt_min (by linarith [hβ w w.isLt]) ?_
      split_ifs with h
      · linarith [hl'l w h]
      · exact one_pos)
  have hm'β : ∀ p < M, l' p + m' ≤ β p := fun p hp => by
    have := (hm'le ⟨p, hp⟩).trans (min_le_left _ _); simp only at this; linarith
  have hgap : ∀ w w', w < w' → w' < M → l' w + m' ≤ l w' := by
    intro w w' h1 h2
    have h3 := (hm'le ⟨w, by omega⟩).trans (min_le_right _ _)
    simp only [if_pos (show w + 1 < M by omega)] at h3
    rcases eq_or_lt_of_le (show w + 1 ≤ w' by omega) with h | h
    · rw [← h]; linarith
    · linarith [hmono w (w + 1) (by omega) (by omega), hll' (w + 1) (by omega),
        hmono (w + 1) w' h h2, hll' w' h2, hl'l w (by omega)]
  -- Lebesgue number of `F`
  obtain ⟨lamF, hlamF, hlebF⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := Y))
    (c := F.link) F.isOpen (fun z _ => hF (mem_univ z))
  -- uniform continuity of `g`
  obtain ⟨μg, hμg, hμgg⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hg.1) m' hm'
  -- thickenings
  have hthU : ∀ w, w < M → ∃ r > 0, thickening r (closure (U w)) ⊆ F.link (y w) := by
    intro w hw
    obtain ⟨r, hr, h⟩ := (isClosed_closure.isCompact).exists_thickening_subset_open
      (F.isOpen (y w)) (hUcl w hw)
    exact ⟨r, hr, h⟩
  have hthA : ∀ w, w < M → ∃ s > 0, thickening s (A w) ⊆ (B w)ᶜ := by
    intro w hw
    obtain ⟨s, hs, h⟩ := ((hAc w hw).isCompact).exists_thickening_subset_open
      (hBc w hw).isOpen_compl (fun z hz => hABd w hw z hz)
    exact ⟨s, hs, h⟩
  choose! rU hrU hrUsub using hthU
  choose! sA hsA hsAsub using hthA
  obtain ⟨μw, hμw, hμwle⟩ := exists_pos_forall_le (fun w : Fin M => min (rU w) (sA w))
    (fun w => lt_min (hrU w w.isLt) (hsA w w.isLt))
  set μ := min (min δ lamF) (min μg μw) with hμdef
  have hμpos : 0 < μ := lt_min (lt_min hδ hlamF) (lt_min hμg hμw)
  have hμδ : μ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hμlam : μ ≤ lamF := (min_le_left _ _).trans (min_le_right _ _)
  have hμg' : μ ≤ μg := (min_le_right _ _).trans (min_le_left _ _)
  have hμU : ∀ w < M, μ ≤ rU w := fun w hw =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans ((hμwle ⟨w, hw⟩).trans (min_le_left _ _))
  have hμA : ∀ w < M, μ ≤ sA w := fun w hw =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans ((hμwle ⟨w, hw⟩).trans (min_le_right _ _))
  ------------------------------------------------------------------
  -- the chain `G`
  ------------------------------------------------------------------
  have hnt : (univ : Set Y).Nontrivial := (hg.2.2.2 0).2.2.mono (subset_univ _)
  obtain ⟨N', G, hGc, hGbj, hGε, hGp⟩ := exists_fine_bjChain_private hSY hnt hμpos
  have hGd : ∀ e, ∀ z ∈ G.link e, ∀ z' ∈ G.link e, dist z z' < μ := fun e z hz z' hz' =>
    lt_of_le_of_lt (dist_le_diam_of_mem (hGε e).1 hz hz') (hGε e).2
  have hGg : ∀ e, ∀ z ∈ G.link e, ∀ z' ∈ G.link e, |(g z : ℝ) - g z'| < m' := by
    intro e z hz z' hz'
    have := hμgg (lt_of_lt_of_le (hGd e z hz z' hz') hμg')
    rwa [Subtype.dist_eq, Real.dist_eq] at this
  have hGleb : ∀ e, ∃ b, G.link e ⊆ F.link b := by
    intro e
    obtain ⟨z, hz⟩ := G.link_nonempty e
    obtain ⟨b, hb⟩ := hlebF z (mem_univ z)
    exact ⟨b, fun z' hz' => hb (by
      rw [mem_ball]; exact lt_of_lt_of_le (hGd e z' hz' z hz) hμlam)⟩
  -- the side lemma
  have hGside : ∀ e, ∀ w < M, (G.link e ∩ A w).Nonempty → ∀ z ∈ G.link e, z ∉ B w := by
    intro e w hw ⟨a, haG, haA⟩ z hz
    have : z ∈ thickening (sA w) (A w) :=
      Metric.mem_thickening_iff.2 ⟨a, haA, lt_of_lt_of_le (hGd e z hz a haG) (hμA w hw)⟩
    exact hsAsub w hw this
  have hGtrans : ∀ e, ∀ w < M, (G.link e ∩ U w).Nonempty → G.link e ⊆ F.link (y w) := by
    intro e w hw ⟨a, haG, haU⟩ z hz
    exact hrUsub w hw (Metric.mem_thickening_iff.2 ⟨a, subset_closure haU,
      lt_of_lt_of_le (hGd e z hz a haG) (hμU w hw)⟩)
  have hG1 : ∀ e, ∀ w < M, ∀ w' < M, (G.link e ∩ U w).Nonempty → (G.link e ∩ U w').Nonempty →
      w = w' := by
    intro e w hw w' hw' ⟨a, haG, haU⟩ ⟨a', ha'G, ha'U⟩
    by_contra hne
    have h1 := hUg w hw a haU
    have h2 := hUg w' hw' a' ha'U
    have h3 := hGg e a haG a' ha'G
    rw [abs_lt] at h3
    rcases lt_or_gt_of_ne hne with h | h
    · linarith [hgap w w' h hw']
    · linarith [hgap w' w h hw]
  ------------------------------------------------------------------
  -- `β`, `π` and `K`
  ------------------------------------------------------------------
  set β' : Fin N' → Fin N := fun e =>
    if h : ∃ w, w < M ∧ (G.link e ∩ U w).Nonempty then y (Nat.find h) else (hGleb e).choose
    with hβ'def
  have hβ'_trans : ∀ e, ∀ w < M, (G.link e ∩ U w).Nonempty → β' e = y w := by
    intro e w hw hwe
    have h : ∃ w, w < M ∧ (G.link e ∩ U w).Nonempty := ⟨w, hw, hwe⟩
    simp only [hβ'def, dif_pos h]
    congr 1
    exact hG1 e _ (Nat.find_spec h).1 w hw (Nat.find_spec h).2 hwe
  have hG6 : ∀ e, G.link e ⊆ F.link (β' e) := by
    intro e
    by_cases h : ∃ w, w < M ∧ (G.link e ∩ U w).Nonempty
    · obtain ⟨w, hw, hwe⟩ := h
      rw [hβ'_trans e w hw hwe]
      exact hGtrans e w hw hwe
    · simp only [hβ'def, dif_neg h]
      exact (hGleb e).choose_spec
  set π : Fin N' → ℕ := fun e =>
    ((Finset.range M).filter (fun w => w < M ∧ G.link e ⊆ B w ∪ U w)).card with hπdef
  set πpt : Y → ℕ := fun z => ((Finset.range M).filter (fun w => w < M ∧ z ∈ B w)).card
    with hπptdef
  have hBUg : ∀ w < M, ∀ z, z ∈ B w ∪ U w → l w < (g z : ℝ) := fun w hw z hz => by
    rcases hz with hz | hz
    · exact hBg w hw z hz
    · exact (hUg w hw z hz).1
  have hπ_iff : ∀ e, ∀ w < M, (G.link e ⊆ B w ∪ U w ↔ w < π e) := by
    intro e
    have := card_filter_lt_iff_of_downward (fun w => w < M ∧ G.link e ⊆ B w ∪ U w)
      (fun w w' hw'w ⟨hwM, hsub⟩ => ⟨by omega, by
        rcases eq_or_lt_of_le hw'w with h | h
        · rw [h]; exact hsub
        · intro z hz
          left
          apply hBright w' (by omega) z
          have := hBUg w hwM z (hsub hz)
          linarith [hmono w' w h hwM, hll' w' (by omega)]⟩) M
    intro w hw
    rw [← this w hw]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hπpt_iff : ∀ z, ∀ w < M, (z ∈ B w ↔ w < πpt z) := by
    intro z
    have := card_filter_lt_iff_of_downward (fun w => w < M ∧ z ∈ B w)
      (fun w w' hw'w ⟨hwM, hz⟩ => ⟨by omega, by
        rcases eq_or_lt_of_le hw'w with h | h
        · rw [h]; exact hz
        · apply hBright w' (by omega) z
          have := hBg w hwM z hz
          linarith [hmono w' w h hwM, hll' w' (by omega)]⟩) M
    intro w hw
    rw [← this w hw]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hπle : ∀ e, π e ≤ M := fun e => card_filter_le _ M
  have hπptle : ∀ z, πpt z ≤ M := fun z => card_filter_le _ M
  have hlt_eq : ∀ a b : ℕ, a ≤ M → b ≤ M → (∀ w < M, (w < a ↔ w < b)) → a = b := by
    intro a b ha hb h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · have := (h a (by omega)).2 h'; omega
    · have := (h b (by omega)).1 h'; omega
  -- (G4)
  have hG4 : ∀ e, ∀ z ∈ G.link e, (∀ w < M, z ∉ U w) → π e = πpt z := by
    intro e z hz hzU
    have key : ∀ w < M, (w < π e ↔ w < πpt z) := by
      intro w hw
      rw [← hπ_iff e w hw, ← hπpt_iff z w hw]
      constructor
      · intro hsub
        rcases hsub hz with h | h
        · exact h
        · exact absurd h (hzU w hw)
      · intro hzB z' hz'
        by_cases hA : (G.link e ∩ A w).Nonempty
        · exact absurd hzB (hGside e w hw hA z hz)
        · by_cases hz'U : z' ∈ U w
          · exact Or.inr hz'U
          · rcases hcovAB w hw z' hz'U with h | h
            · exact absurd ⟨z', hz', h⟩ hA
            · exact Or.inl h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · have := (key (π e) (by linarith [hπptle z])).2 h'; omega
    · have := (key (πpt z) (by linarith [hπle e])).1 h'; omega
  -- (G3)
  have hG3 : ∀ e, ∀ w < M, (G.link e ∩ U w).Nonempty → w ≤ π e ∧ π e ≤ w + 1 := by
    intro e w hw ⟨a, haG, haU⟩
    have hga := hUg w hw a haU
    constructor
    · rcases Nat.eq_zero_or_pos w with h | h
      · omega
      · have : w - 1 < π e := by
          rw [← hπ_iff e (w - 1) (by omega)]
          intro z hz
          left
          apply hBright (w - 1) (by omega) z
          have h1 := hGg e z hz a haG
          rw [abs_lt] at h1
          linarith [hgap (w - 1) w (by omega) hw]
        omega
    · rcases Nat.lt_or_ge (w + 1) M with h | h
      · by_contra hlt
        have : w + 1 < π e := by omega
        rw [← hπ_iff e (w + 1) h] at this
        have haA : a ∈ A (w + 1) := hAleft (w + 1) h a (by linarith [hl'l w h])
        rcases this haG with h' | h'
        · exact hABd (w + 1) h a haA h'
        · exact hAU (w + 1) h a haA h'
      · linarith [hπle e]
  -- (G5)
  have hG5 : ∀ e, ∀ z ∈ G.link e, α (π e) ≤ (g z : ℝ) ∧ (g z : ℝ) ≤ β (π e) := by
    intro e z hz
    constructor
    · rcases Nat.eq_zero_or_pos (π e) with h | h
      · rw [h]; linarith [(g z).2.1]
      · have hπM := hπle e
        have hsub := (hπ_iff e (π e - 1) (by omega)).2 (by omega)
        have := hBUg (π e - 1) (by omega) z (hsub hz)
        linarith [hα (π e) h (hπle e)]
    · rcases Nat.lt_or_ge (π e) M with h | h
      · have hnot : ¬ G.link e ⊆ B (π e) ∪ U (π e) := fun hsub =>
          (lt_irrefl _) ((hπ_iff e (π e) h).1 hsub)
        rw [Set.not_subset] at hnot
        obtain ⟨z', hz', hz'n⟩ := hnot
        have hz'A : z' ∈ A (π e) := by
          rcases hcovAB (π e) h z' (fun hU => hz'n (Or.inr hU)) with h1 | h1
          · exact h1
          · exact absurd (Or.inl h1) hz'n
        have h1 := hAg (π e) h z' hz'A
        have h2 := hGg e z hz z' hz'
        rw [abs_lt] at h2
        linarith [hm'β (π e) h]
      · rw [show π e = M by linarith [hπle e]]; linarith [(g z).2.2]
  set K : Fin N' → Fin n := fun e => R (π e) (β' e) with hKdef
  ------------------------------------------------------------------
  -- the core of Condition A′ and of ontoness
  ------------------------------------------------------------------
  have coreΓ : ∀ p ≤ M, ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p →
      ∀ (Γ : Set Y) (t' u' : ℕ), Γ ⊆ g ⁻¹' {x} → (∀ z ∈ Γ, (∀ w < M, z ∉ U w) ∧ πpt z = p) →
      (∀ k : Fin N, t' ≤ k.val → k.val ≤ u' → (F.link k ∩ Γ).Nonempty) →
      IsPatternOn (R p) (σ p) (σ' p) t' u' →
      f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : σ p ≤ j.val ∧ j.val ≤ σ' p), D.link j ∧
      ∀ j : Fin n, σ p ≤ j.val → j.val ≤ σ' p →
        ∃ z ∈ g ⁻¹' {x}, ∀ e, z ∈ G.link e → K e = j := by
    intro p hp x hx1 hx2 Γ t' u' hΓ hΓz hΓT hpat
    refine ⟨hP2b p hp x hx1 hx2, fun j hj1 hj2 => ?_⟩
    obtain ⟨k, hk1, hk2, hk⟩ := hpat j hj1 hj2
    obtain ⟨hk1N, hk1j⟩ := hk 1 (by omega)
    obtain ⟨z, hzF, hzΓ⟩ := hΓT ⟨k + 1, hk1N⟩ (by simp only; omega) (by simp only; omega)
    refine ⟨z, hΓ hzΓ, fun e hze => ?_⟩
    have hπe : π e = p := (hG4 e z hze (hΓz z hzΓ).1).trans (hΓz z hzΓ).2
    have hadj := (F.adjacent_iff (β' e) ⟨k + 1, hk1N⟩).1 ⟨z, hG6 e hze, hzF⟩
    simp only at hadj
    obtain ⟨c, hc, hce⟩ : ∃ c, c ≤ 2 ∧ (β' e).val = k + c := ⟨(β' e).val - k, by omega, by omega⟩
    obtain ⟨hcN, hcj⟩ := hk c hc
    show R (π e) (β' e) = j
    rw [hπe, show β' e = ⟨k + c, hcN⟩ from Fin.ext hce, hcj]
  have core : ∀ x : unitInterval, ∃ p ≤ M,
      f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : σ p ≤ j.val ∧ j.val ≤ σ' p), D.link j ∧
      ∀ j : Fin n, σ p ≤ j.val → j.val ≤ σ' p →
        ∃ z ∈ g ⁻¹' {x}, ∀ e, z ∈ G.link e → K e = j := by
    intro x
    by_cases hwx : ∃ w, w < M ∧ l w ≤ x ∧ (x : ℝ) ≤ l' w
    · obtain ⟨w, hw, hxw1, hxw2⟩ := hwx
      have hxs : x ∈ Icc (aw w) (bw w) := by
        rw [unitInterval_mem_Icc_iff, haw w hw, hbw w hw]; exact ⟨hxw1, hxw2⟩
      -- points of the fibre over `x` meet no other transition set
      have hUo' : ∀ z ∈ g ⁻¹' {x}, ∀ w' < M, w' ≠ w → z ∉ U w' := by
        intro z hz w' hw' hne hzU
        have h1 := hUg w' hw' z hzU
        simp only [mem_preimage, mem_singleton_iff] at hz
        rw [hz] at h1
        rcases lt_or_gt_of_ne hne with h | h
        · linarith [hmono w' w h hw]
        · linarith [hmono w w' h hw']
      have hBlt : ∀ z ∈ g ⁻¹' {x}, ∀ w' < w, z ∈ B w' := by
        intro z hz w' hw'
        simp only [mem_preimage, mem_singleton_iff] at hz
        apply hBright w' (by omega) z
        rw [hz]; linarith [hmono w' w hw' hw]
      have hAgt : ∀ z ∈ g ⁻¹' {x}, ∀ w', w < w' → w' < M → z ∉ B w' := by
        intro z hz w' hw' hw'M hzB
        simp only [mem_preimage, mem_singleton_iff] at hz
        apply hABd w' hw'M z _ hzB
        apply hAleft w' hw'M z
        rw [hz]; linarith [hmono w w' hw' hw'M]
      rcases hdich w hw x hxs with hA | hB
      · refine ⟨w, hw.le, coreΓ w hw.le x (by linarith [hαw w hw]) (by linarith [hβ w hw])
          (A w ∩ g ⁻¹' {x}) (t w) (u w) inter_subset_right (fun z hz => ⟨fun w' hw' => ?_, ?_⟩)
          hA (hTp w hw).1⟩
        · by_cases h : w' = w
          · rw [h]; exact hAU w hw z hz.1
          · exact hUo' z hz.2 w' hw' h
        · have : ∀ w' < M, (w' < πpt z ↔ w' < w) := by
            intro w' hw'
            rw [← hπpt_iff z w' hw']
            constructor
            · intro hzB
              by_contra h
              rcases eq_or_lt_of_le (not_lt.1 h) with h' | h'
              · rw [← h'] at hzB; exact hABd w hw z hz.1 hzB
              · exact hAgt z hz.2 w' h' hw' hzB
            · intro h; exact hBlt z hz.2 w' h
          exact hlt_eq _ _ (hπptle z) hw.le this
      · refine ⟨w + 1, by omega, coreΓ (w + 1) (by omega) x (by linarith [hαw1 w hw])
          (by linarith [hβw1 w hw]) (B w ∩ g ⁻¹' {x}) (t w) (u w) inter_subset_right
          (fun z hz => ⟨fun w' hw' => ?_, ?_⟩) hB (hTp w hw).2⟩
        · by_cases h : w' = w
          · rw [h]; exact hBU w hw z hz.1
          · exact hUo' z hz.2 w' hw' h
        · have : ∀ w' < M, (w' < πpt z ↔ w' < w + 1) := by
            intro w' hw'
            rw [← hπpt_iff z w' hw']
            constructor
            · intro hzB
              by_contra h
              exact hAgt z hz.2 w' (by omega) hw' hzB
            · intro h
              rcases eq_or_lt_of_le (show w' ≤ w by omega) with h' | h'
              · rw [h']; exact hz.1
              · exact hBlt z hz.2 w' h'
          exact hlt_eq _ _ (hπptle z) (by omega) this
    · push_neg at hwx
      set p := ((Finset.range M).filter (fun w => w < M ∧ l' w < x)).card with hpdef
      have hp_iff : ∀ w < M, (l' w < x ↔ w < p) := by
        intro w hw
        have := card_filter_lt_iff_of_downward (fun w => w < M ∧ l' w < x)
          (fun w w' hw'w ⟨hwM, h⟩ => ⟨by omega, by
            rcases eq_or_lt_of_le hw'w with h' | h'
            · rw [h']; exact h
            · linarith [hmono w' w h' hwM, hll' w hwM]⟩) M w hw
        rw [← this]
        exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
      have hpM : p ≤ M := card_filter_le _ M
      have hpl : p = 0 ∨ l' (p - 1) < x := by
        rcases Nat.eq_zero_or_pos p with h | h
        · exact Or.inl h
        · exact Or.inr ((hp_iff (p - 1) (by omega)).2 (by omega))
      have hpr : p = M ∨ (x : ℝ) < l p := by
        rcases eq_or_lt_of_le hpM with h | h
        · exact Or.inl h
        · right
          have h1 : ¬ l' p < x := fun h' => lt_irrefl _ ((hp_iff p h).1 h')
          by_contra h2
          exact h1 (hwx p h (not_lt.1 h2))
      obtain ⟨t', u', -, -, hlinks, hpat⟩ := hout p hpM x hpl hpr
      refine ⟨p, hpM, coreΓ p hpM x ?_ ?_ (g ⁻¹' {x}) t' u' subset_rfl
        (fun z hz => ⟨?_, ?_⟩) hlinks hpat⟩
      · rcases Nat.eq_zero_or_pos p with h | h
        · rw [h]; linarith [x.2.1]
        · have := (hp_iff (p - 1) (by omega)).2 (by omega)
          linarith [hα p h hpM, hll' (p - 1) (by omega)]
      · rcases eq_or_lt_of_le hpM with h | h
        · rw [h]; linarith [x.2.2]
        · rcases hpr with h' | h'
          · omega
          · linarith [hll' p h, hβ p h]
      · intro w hw hzU
        have h1 := hUg w hw z hzU
        simp only [mem_preimage, mem_singleton_iff] at hz
        rw [hz] at h1
        have := hwx w hw h1.1.le
        linarith [h1.2]
      · apply hlt_eq _ _ (hπptle z) hpM
        intro w hw
        rw [← hπpt_iff z w hw, ← hp_iff w hw]
        simp only [mem_preimage, mem_singleton_iff] at hz
        constructor
        · intro hzB
          have := hBg w hw z hzB
          rw [hz] at this
          exact hwx w hw this.le
        · intro h
          exact hBright w hw z (by rw [hz]; exact h.le)
  ------------------------------------------------------------------
  -- verification
  ------------------------------------------------------------------
  refine ⟨N', G, K, hGc, hGbj, fun i => ⟨(hGε i).1, lt_of_lt_of_le (hGε i).2 hμδ⟩, hGp,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- chain map
    intro i j hij
    obtain ⟨z, hzi, hzj⟩ := (G.adjacent i j).2 hij
    by_cases hzU : ∃ w, w < M ∧ z ∈ U w
    · obtain ⟨w, hw, hzw⟩ := hzU
      have hi := hβ'_trans i w hw ⟨z, hzi, hzw⟩
      have hj := hβ'_trans j w hw ⟨z, hzj, hzw⟩
      have hpi := hG3 i w hw ⟨z, hzi, hzw⟩
      have hpj := hG3 j w hw ⟨z, hzj, hzw⟩
      show ((R (π i) (β' i) : ℤ) - R (π j) (β' j)).natAbs ≤ 1
      rw [hi, hj]
      have ha := hyadj w hw
      rcases (show π i = w ∨ π i = w + 1 by omega) with h1 | h1 <;>
      rcases (show π j = w ∨ π j = w + 1 by omega) with h2 | h2 <;> rw [h1, h2] <;> omega
    · push_neg at hzU
      have hi := hG4 i z hzi hzU
      have hj := hG4 j z hzj hzU
      show ((R (π i) (β' i) : ℤ) - R (π j) (β' j)).natAbs ≤ 1
      rw [hi, hj]
      exact hRc _ (hπptle z) _ _ ((F.adjacent _ _).1 ⟨z, hG6 i hzi, hG6 j hzj⟩)
  · -- onto
    intro j
    obtain ⟨zj, hzj, hzjo⟩ := hDp j
    obtain ⟨p, hp, hcov, hall⟩ := core (f zj)
    obtain ⟨j', hj', hzj'⟩ := mem_iUnion₂.1 (hcov (show zj ∈ f ⁻¹' {f zj} from rfl))
    have hjj : j' = j := by
      by_contra hne
      exact hzjo j' hne (subset_closure hzj')
    subst hjj
    obtain ⟨z, -, hz⟩ := hall j' hj'.1 hj'.2
    obtain ⟨e, he⟩ := mem_iUnion.1 (hGc (mem_univ z))
    exact ⟨e, hz e he⟩
  · -- A′, first clause
    intro x e ⟨z, hze, hzx⟩
    have h5 := hG5 e z hze
    simp only [mem_preimage, mem_singleton_iff] at hzx
    rw [hzx] at h5
    exact hP2a (π e) (hπle e) x h5.1 h5.2 _ (hRS _ (hπle e) _).1 (hRS _ (hπle e) _).2
  · -- A′, second clause
    intro x a b _ hcov z hz
    obtain ⟨p, -, hcovD, hall⟩ := core x
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 (hcovD hz)
    obtain ⟨z', hz'x, hz'⟩ := hall j hj.1 hj.2
    obtain ⟨e, he, hz'e⟩ := mem_iUnion₂.1 (hcov hz'x)
    exact mem_iUnion₂.2 ⟨e, he, by show z ∈ D.link (K e); rw [hz' e hz'e]; exact hzj⟩
  · -- C′ at 0
    intro e z hze
    have hπ0 : π e = 0 := by
      apply hlt_eq _ _ (hπle e) (Nat.zero_le _)
      intro w hw
      rw [← hπ_iff e w hw]
      simp only [Nat.not_lt_zero, iff_false]
      intro hsub
      have hz0 : g z = 0 := z.2
      have hzA : (z : Y) ∈ A w := hAleft w hw z (by
        rw [hz0, Set.Icc.coe_zero]; exact (hl_pos w hw).le)
      rcases hsub hze with h | h
      · exact hABd w hw z hzA h
      · exact hAU w hw z hzA h
    show (h₀.symm z : X) ∈ D.link (R (π e) (β' e))
    rw [hπ0]
    exact hC0 (β' e) z (hG6 e hze)
  · -- C′ at 1
    intro e z hze
    have hπM : π e = M := by
      apply hlt_eq _ _ (hπle e) le_rfl
      intro w hw
      rw [← hπ_iff e w hw]
      simp only [hw, iff_true]
      have hz1 : g z = 1 := z.2
      have hzB : (z : Y) ∈ B w := hBright w hw z (by
        rw [hz1, Set.Icc.coe_one]; exact (hl'_lt w hw).le)
      intro z' hz'
      by_cases hA : (G.link e ∩ A w).Nonempty
      · exact absurd hzB (hGside e w hw hA z hze)
      · by_cases hz'U : z' ∈ U w
        · exact Or.inr hz'U
        · rcases hcovAB w hw z' hz'U with h | h
          · exact absurd ⟨z', hz', h⟩ hA
          · exact Or.inl h
    show (h₁.symm z : X) ∈ D.link (R (π e) (β' e))
    rw [hπM]
    exact hC1 (β' e) z (hG6 e hze)
  · -- B′
    intro e z hz
    exact hP1 (π e) (hπle e) (β' e) z (hG6 e hz) (hG5 e z hz).1 (hG5 e z hz).2

end Glue

end HPC.BJ59
