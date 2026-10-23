import HPC.BJ59.Thm10Pieces
import HPC.BJ59.Thm10Induct
import HPC.BJ59.Step1b

/-!
# Batch 201, §4: the step lemma

`bj_step : BJStep` (statement as in the skeleton). The sub-arcs, the end runs, the chain `F`,
the maps, `τ` and the windows of commission 201 §4 (a)–(e), assembled and fed to `bj_glue`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

set_option maxHeartbeats 4000000 in
/-- **The step lemma** (main item). -/
theorem bj_step : BJStep := by
  intro X Y _ _ _ _ f g hf hg hSX hSY h₀ h₁ n m D E H hDc hEc hDp hEf hA hC δ hδ
  classical
  ------------------------------------------------------------------
  -- (a) sub-arcs
  ------------------------------------------------------------------
  have hfa : IsArcOfContinua f := ⟨hf.1, hf.2.2.1, fun t => (hf.2.2.2 t).1.1⟩
  obtain ⟨δD, hδD, h1b⟩ := bj_step1b hfa hf.2.1 D hDc
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / δD)
  have hN₀pos : (0 : ℝ) < N₀ := lt_trans (by positivity) hN₀
  have hN₀1 : 1 ≤ N₀ := by
    rcases Nat.eq_zero_or_pos N₀ with h | h
    · rw [h] at hN₀pos; simp at hN₀pos
    · exact h
  set ι : ℝ := 1 / (N₀ : ℝ) with hι
  have hιpos : 0 < ι := by positivity
  have hιle : ι ≤ 1 := by
    rw [hι, div_le_one hN₀pos]; exact_mod_cast hN₀1
  have hιδ : 5 / 4 * ι ≤ δD := by
    rw [hι]
    have h1 : 2 / δD * δD = 2 := by field_simp
    have h2 : (2 / δD) * δD < N₀ * δD := mul_lt_mul_of_pos_right hN₀ hδD
    rw [h1] at h2
    rw [show 5 / 4 * (1 / (N₀ : ℝ)) = 5 / (4 * N₀) by ring, div_le_iff₀ (by positivity)]
    nlinarith
  set η : ℝ := ι / 8 with hη
  have hηpos : 0 < η := by positivity
  set c : ℕ → ℝ := fun i => (i : ℝ) * ι with hc
  have hc0 : c 0 = 0 := by simp [hc]
  have hcN : c N₀ = 1 := by simp only [hc, hι]; field_simp
  have hcs : ∀ i, c (i + 1) = c i + ι := fun i => by simp only [hc]; push_cast; ring
  have hcle : ∀ i j, i ≤ j → c i ≤ c j := fun i j h => by
    simp only [hc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hιpos.le
  have hc_nonneg : ∀ i, 0 ≤ c i := fun i => by rw [← hc0]; exact hcle 0 i (Nat.zero_le _)
  have hc_le1 : ∀ i, i ≤ N₀ → c i ≤ 1 := fun i hi => by rw [← hcN]; exact hcle i N₀ hi
  have hc_lt : ∀ i, i < N₀ → c i + ι ≤ 1 := fun i hi => by
    rw [← hcs]; exact hc_le1 (i + 1) hi
  set aJ : ℕ → unitInterval := fun i => Set.projIcc 0 1 zero_le_one (c i - η) with haJ
  set bJ : ℕ → unitInterval := fun i => Set.projIcc 0 1 zero_le_one (c (i + 1) + η) with hbJ
  have haJc : ∀ i, ((aJ i : unitInterval) : ℝ) = max 0 (min 1 (c i - η)) := fun i => by
    simp only [haJ, Set.coe_projIcc]
  have hbJc : ∀ i, ((bJ i : unitInterval) : ℝ) = max 0 (min 1 (c (i + 1) + η)) := fun i => by
    simp only [hbJ, Set.coe_projIcc]
  have hJmem : ∀ i (x : unitInterval), c i - η ≤ x → (x : ℝ) ≤ c (i + 1) + η →
      x ∈ Icc (aJ i) (bJ i) := by
    intro i x h1 h2
    rw [unitInterval_mem_Icc_iff, haJc, hbJc]
    exact ⟨max_le x.2.1 ((min_le_right _ _).trans h1),
      le_max_of_le_right (le_min x.2.2 h2)⟩
  have hJab : ∀ i, i < N₀ → aJ i < bJ i := by
    intro i hi
    show (aJ i : ℝ) < bJ i
    rw [haJc, hbJc]
    have h1 := hc_lt i hi
    have h2 := hc_nonneg i
    rw [hcs]
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨one_pos, by linarith⟩, ?_⟩
    exact ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith),
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have hJlen : ∀ i, i < N₀ → ((bJ i : unitInterval) : ℝ) - aJ i ≤ δD := by
    intro i hi
    rw [haJc, hbJc]
    have h1 := hc_lt i hi
    have h2 := hc_nonneg i
    have e1 : max 0 (min 1 (c (i + 1) + η)) ≤ c (i + 1) + η :=
      max_le (by rw [hcs]; linarith) (min_le_right _ _)
    have e2 : c i - η ≤ max 0 (min 1 (c i - η)) :=
      le_max_of_le_right (le_min (by linarith) le_rfl)
    have := hcs i
    linarith
  have hpieces : ∀ i, i < N₀ → ∃ r s : ℕ, r ≤ s ∧ s < n ∧
      (∀ x ∈ Icc (aJ i) (bJ i), ∀ j : Fin n, r ≤ j.val → j.val ≤ s →
        (D.link j ∩ f ⁻¹' {x}).Nonempty) ∧
      (∀ x ∈ Icc (aJ i) (bJ i), f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : r ≤ j.val ∧ j.val ≤ s), D.link j) ∧
      ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → univ ⊆ F.union →
        ∃ R : Fin N → Fin n, IsChainMap R ∧ (∀ k, r ≤ (R k).val ∧ (R k).val ≤ s) ∧
          (∀ k, ∀ y ∈ F.link k, g y ∈ Icc (aJ i) (bJ i) → y ∈ E.link (H (R k))) ∧
          ∀ x ∈ Icc (aJ i) (bJ i), ∀ v w : ℕ, w < N → v ≤ w →
            g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
            IsPatternOn R r s v w := fun i hi =>
    exists_subarc_piece hf hg hSY D E H hDc hEf hA (hJab i hi)
      (h1b (aJ i) (bJ i) (hJab i hi).le (hJlen i hi))
  choose! rr ss hrs hsn hPm hPc εs hεs hRs using hpieces
  ------------------------------------------------------------------
  -- (c) the ends
  ------------------------------------------------------------------
  obtain ⟨v₁, v₂, hv, hvn, hW0m, hW0c, ε₀, hε₀, hR0⟩ := exists_end_piece hf hg h₀ D hDc
  obtain ⟨v₁', v₂', hv', hvn', hW1m, hW1c, ε₁, hε₁, hR1⟩ := exists_end_piece hf hg h₁ D hDc
  ------------------------------------------------------------------
  -- (d) the chain `F` and the maps
  ------------------------------------------------------------------
  obtain ⟨εm, hεm, hεmle⟩ := exists_pos_forall_le (fun i : Fin N₀ => εs i) (fun i => hεs i i.isLt)
  set ε := min (min ε₀ ε₁) εm with hεdef
  have hεpos : 0 < ε := lt_min (lt_min hε₀ hε₁) hεm
  obtain ⟨N, F, hFε, hFc⟩ := hSY.2 ε hεpos
  have hFε' : ∀ ε', ε ≤ ε' → IsEpsChain F ε' := fun ε' h k =>
    ⟨(hFε k).1, lt_of_lt_of_le (hFε k).2 h⟩
  obtain ⟨R0, hR0c, hR0S, hR0cl, hR0p⟩ := hR0 N F (hFε' ε₀
    ((min_le_left _ _).trans (min_le_left _ _))) hFc
  obtain ⟨R1, hR1c, hR1S, hR1cl, hR1p⟩ := hR1 N F (hFε' ε₁
    ((min_le_left _ _).trans (min_le_right _ _))) hFc
  have hRsF : ∀ i, i < N₀ → ∃ R : Fin N → Fin n, IsChainMap R ∧
      (∀ k, rr i ≤ (R k).val ∧ (R k).val ≤ ss i) ∧
      (∀ k, ∀ y ∈ F.link k, g y ∈ Icc (aJ i) (bJ i) → y ∈ E.link (H (R k))) ∧
      ∀ x ∈ Icc (aJ i) (bJ i), ∀ v w : ℕ, w < N → v ≤ w →
        g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
        IsPatternOn R (rr i) (ss i) v w := fun i hi =>
    hRs i hi N F (hFε' _ ((min_le_right _ _).trans (hεmle ⟨i, hi⟩))) hFc
  haveI : Nonempty (Fin n) := ⟨⟨v₁, by omega⟩⟩
  choose! Rs hRsc hRsS hRs1 hRs2 using hRsF
  ------------------------------------------------------------------
  -- (e) runs and `τ`
  ------------------------------------------------------------------
  have hfibY : ∀ x : unitInterval, IsPreconnected (g ⁻¹' {x}) ∧ (g ⁻¹' {x}).Nonempty :=
    fun x => ⟨(hg.2.2.2 x).1.1.2.isPreconnected, (hg.2.2.2 x).2.2.nonempty⟩
  have hrun : ∀ x : unitInterval, ∃ t u : ℕ, t ≤ u ∧ u < N ∧
      (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {x}).Nonempty) ∧
      g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k ∧
      ∀ k : Fin N, (F.link k ∩ g ⁻¹' {x}).Nonempty → t ≤ k.val ∧ k.val ≤ u := fun x =>
    exists_run_meeting F (hfibY x).1 (hfibY x).2 (fun z _ => hFc (mem_univ z))
  choose tr ur htur hurN hrunm hrunc hrunin using hrun
  -- the pattern at the ends, on the runs over `0` and `1`
  have hpat0 : IsPatternOn R0 v₁ v₂ (tr 0) (ur 0) := by
    intro j hj1 hj2
    obtain ⟨a, ha, hac⟩ := hR0p j hj1 hj2
    have h0 := hrunin 0 ⟨a + 0, by omega⟩ (hac 0 (by omega)).1
    have h2 := hrunin 0 ⟨a + 2, by omega⟩ (hac 2 (by omega)).1
    simp only at h0 h2
    exact ⟨a, by omega, by omega, fun c' hc' => ⟨by omega, (hac c' hc').2⟩⟩
  have hpat1 : IsPatternOn R1 v₁' v₂' (tr 1) (ur 1) := by
    intro j hj1 hj2
    obtain ⟨a, ha, hac⟩ := hR1p j hj1 hj2
    have h0 := hrunin 1 ⟨a + 0, by omega⟩ (hac 0 (by omega)).1
    have h2 := hrunin 1 ⟨a + 2, by omega⟩ (hac 2 (by omega)).1
    simp only at h0 h2
    exact ⟨a, by omega, by omega, fun c' hc' => ⟨by omega, (hac c' hc').2⟩⟩
  -- `τ`
  obtain ⟨τa, hτa, hτaP⟩ := exists_tau_run hg.1 hg.2.1 F (hrunm 0) (hrunc 0)
  obtain ⟨τb, hτb, hτbP⟩ := exists_tau_run hg.1 hg.2.1 F (hrunm 1) (hrunc 1)
  obtain ⟨τc, hτc, hτcP⟩ := exists_tau_run hf.1 hf.2.1 D hW0m hW0c
  obtain ⟨τd, hτd, hτdP⟩ := exists_tau_run hf.1 hf.2.1 D hW1m hW1c
  obtain ⟨τe, hτe, hτeP⟩ := exists_tau_incl hg.1 F (c := 0) (fun k => E.link (H (R0 k)))
    (fun k => E.isOpen _) (fun k z hz => by
      have h1 := hR0cl k ⟨z, hz.2⟩ hz.1
      have h2 := hC.1 (R0 k) (h₀.symm ⟨z, hz.2⟩) h1
      simpa using h2)
  obtain ⟨τf, hτf, hτfP⟩ := exists_tau_incl hg.1 F (c := 1) (fun k => E.link (H (R1 k)))
    (fun k => E.isOpen _) (fun k z hz => by
      have h1 := hR1cl k ⟨z, hz.2⟩ hz.1
      have h2 := hC.2 (R1 k) (h₁.symm ⟨z, hz.2⟩) h1
      simpa using h2)
  set cc : ℕ → unitInterval := fun i => Set.projIcc 0 1 zero_le_one (c i) with hcc
  have hccv : ∀ i, i ≤ N₀ → ((cc i : unitInterval) : ℝ) = c i := fun i hi => by
    simp only [hcc]; rw [Set.projIcc_of_mem _ ⟨hc_nonneg i, hc_le1 i hi⟩]
  have hcut : ∀ i : Fin (N₀ + 1), ∃ τ > 0, ∀ x : unitInterval, |(x : ℝ) - cc i| ≤ τ →
      (∀ k : Fin N, tr (cc i) ≤ k.val → k.val ≤ ur (cc i) →
        (F.link k ∩ g ⁻¹' {x}).Nonempty) ∧
      g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : tr (cc i) ≤ k.val ∧ k.val ≤ ur (cc i)), F.link k :=
    fun i => exists_tau_run hg.1 hg.2.1 F (hrunm (cc i)) (hrunc (cc i))
  choose τg hτg hτgP using hcut
  obtain ⟨τh, hτh, hτhle⟩ := exists_pos_forall_le τg hτg
  set τ := min (min (min τa τb) (min τc τd)) (min (min τe τf) (min τh (η / 8))) with hτdef
  have hτpos : 0 < τ := lt_min (lt_min (lt_min hτa hτb) (lt_min hτc hτd))
    (lt_min (lt_min hτe hτf) (lt_min hτh (by positivity)))
  have hτa' : τ ≤ τa := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτb' : τ ≤ τb := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτc' : τ ≤ τc := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτd' : τ ≤ τd := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτe' : τ ≤ τe := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτf' : τ ≤ τf := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτh' : τ ≤ τh := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτη : τ ≤ η / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτg' : ∀ i (hi : i ≤ N₀), τ ≤ τg ⟨i, Nat.lt_succ_of_le hi⟩ := fun i hi =>
    hτh'.trans (hτhle _)
  have hτ1 : τ ≤ ι / 64 := by rw [hη] at hτη; linarith
  ------------------------------------------------------------------
  -- (e) windows and pieces
  ------------------------------------------------------------------
  obtain ⟨l, hl⟩ : ∃ l : ℕ → ℝ, l = fun w => if w = 0 then τ / 4 else if w = N₀ then 1 - τ / 2
      else c w := ⟨_, rfl⟩
  obtain ⟨l', hl'⟩ : ∃ l' : ℕ → ℝ, l' = fun w => if w = 0 then τ / 2 else if w = N₀ then
      1 - τ / 4 else c w + τ / 2 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, α = fun p => if p = 0 then -1 else if p = N₀ + 1 then 1 - τ
      else c (p - 1) - η := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun p => if p = 0 then τ else if p = N₀ + 1 then 2
      else c p + η := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, σ = fun p => if p = 0 then v₁ else if p = N₀ + 1 then v₁'
      else rr (p - 1) := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℕ → ℕ, σ' = fun p => if p = 0 then v₂ else if p = N₀ + 1 then v₂'
      else ss (p - 1) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Fin N → Fin n, R = fun p => if p = 0 then R0
      else if p = N₀ + 1 then R1 else Rs (p - 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ, t = fun w => if w = 0 then tr 0 else if w = N₀ then tr 1
      else tr (cc w) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℕ, u = fun w => if w = 0 then ur 0 else if w = N₀ then ur 1
      else ur (cc w) := ⟨_, rfl⟩
  -- evaluations
  have el0 : l 0 = τ / 4 := by rw [hl]; simp
  have elN : l N₀ = 1 - τ / 2 := by rw [hl]; simp only [if_neg (show N₀ ≠ 0 by omega)]; simp
  have eli : ∀ w, w ≠ 0 → w ≠ N₀ → l w = c w := fun w h1 h2 => by
    rw [hl]; simp only [if_neg h1, if_neg h2]
  have el'0 : l' 0 = τ / 2 := by rw [hl']; simp
  have el'N : l' N₀ = 1 - τ / 4 := by rw [hl']; simp only [if_neg (show N₀ ≠ 0 by omega)]; simp
  have el'i : ∀ w, w ≠ 0 → w ≠ N₀ → l' w = c w + τ / 2 := fun w h1 h2 => by
    rw [hl']; simp only [if_neg h1, if_neg h2]
  have eα0 : α 0 = -1 := by rw [hα]; simp
  have eαM : α (N₀ + 1) = 1 - τ := by rw [hα]; simp
  have eαi : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → α p = c (p - 1) - η := fun p h1 h2 => by
    rw [hα]; simp only [if_neg h1, if_neg h2]
  have eβ0 : β 0 = τ := by rw [hβ]; simp
  have eβM : β (N₀ + 1) = 2 := by rw [hβ]; simp
  have eβi : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → β p = c p + η := fun p h1 h2 => by
    rw [hβ]; simp only [if_neg h1, if_neg h2]
  have eσ0 : σ 0 = v₁ := by rw [hσ]; simp
  have eσM : σ (N₀ + 1) = v₁' := by rw [hσ]; simp
  have eσi : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → σ p = rr (p - 1) := fun p h1 h2 => by
    rw [hσ]; simp only [if_neg h1, if_neg h2]
  have eσ'0 : σ' 0 = v₂ := by rw [hσ']; simp
  have eσ'M : σ' (N₀ + 1) = v₂' := by rw [hσ']; simp
  have eσ'i : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → σ' p = ss (p - 1) := fun p h1 h2 => by
    rw [hσ']; simp only [if_neg h1, if_neg h2]
  have eR0 : R 0 = R0 := by rw [hR]; simp
  have eRM : R (N₀ + 1) = R1 := by rw [hR]; simp
  have eRi : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → R p = Rs (p - 1) := fun p h1 h2 => by
    rw [hR]; simp only [if_neg h1, if_neg h2]
  have et0 : t 0 = tr 0 := by rw [ht]; simp
  have etN : t N₀ = tr 1 := by rw [ht]; simp only [if_neg (show N₀ ≠ 0 by omega)]; simp
  have eti : ∀ w, w ≠ 0 → w ≠ N₀ → t w = tr (cc w) := fun w h1 h2 => by
    rw [ht]; simp only [if_neg h1, if_neg h2]
  have eu0 : u 0 = ur 0 := by rw [hu]; simp
  have euN : u N₀ = ur 1 := by rw [hu]; simp only [if_neg (show N₀ ≠ 0 by omega)]; simp
  have eui : ∀ w, w ≠ 0 → w ≠ N₀ → u w = ur (cc w) := fun w h1 h2 => by
    rw [hu]; simp only [if_neg h1, if_neg h2]
  have hcases : ∀ p, p ≤ N₀ + 1 → p = 0 ∨ p = N₀ + 1 ∨ (p ≠ 0 ∧ p ≠ N₀ + 1 ∧ 1 ≤ p ∧ p ≤ N₀) :=
    fun p hp => by omega
  have hwcases : ∀ w, w < N₀ + 1 → w = 0 ∨ w = N₀ ∨ (w ≠ 0 ∧ w ≠ N₀ ∧ 1 ≤ w ∧ w < N₀) :=
    fun w hw => by omega
  have hcN1 : ∀ w, 1 ≤ w → w < N₀ → c w + ι ≤ 1 := fun w _ hw => hc_lt w hw
  have hcsub : ∀ p, 1 ≤ p → c p = c (p - 1) + ι := fun p hp => by
    rw [← hcs]; congr 1; omega
  have hcpos : ∀ w, 1 ≤ w → ι ≤ c w := fun w hw => by
    have := hcle 1 w hw; rw [hcs 0, hc0] at this; linarith
  have habs0 : ∀ x : unitInterval, ∀ r : ℝ, (x : ℝ) ≤ r →
      |(x : ℝ) - ((0 : unitInterval) : ℝ)| ≤ r := fun x r h => by
    rw [Set.Icc.coe_zero, sub_zero, abs_of_nonneg x.2.1]; exact h
  have habs1 : ∀ x : unitInterval, ∀ r : ℝ, 1 - r ≤ (x : ℝ) →
      |(x : ℝ) - ((1 : unitInterval) : ℝ)| ≤ r := fun x r h => by
    rw [Set.Icc.coe_one, abs_sub_comm, abs_of_nonneg (by linarith [x.2.2])]; linarith
  have hιpos' := hιpos
  -- the inequalities of the windows
  have g_hl0 : 0 < l 0 := by rw [el0]; linarith
  have g_hll' : ∀ w < N₀ + 1, l w < l' w := by
    intro w hw
    rcases hwcases w hw with h | h | ⟨h1, h2, -, -⟩
    · rw [h, el0, el'0]; linarith
    · rw [h, elN, el'N]; linarith
    · rw [eli w h1 h2, el'i w h1 h2]; linarith
  have g_hl'l : ∀ w, w + 1 < N₀ + 1 → l' w < l (w + 1) := by
    intro w hw
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h, el'0]
      by_cases h1 : 1 = N₀
      · rw [show (0 : ℕ) + 1 = N₀ by omega, elN]; linarith
      · rw [eli (0 + 1) (by omega) (by omega), hcs, hc0]; linarith
    · rw [el'i w (by omega) (by omega)]
      by_cases h1 : w + 1 = N₀
      · rw [h1, elN]
        have e1 := hcs w
        rw [h1, hcN] at e1
        linarith
      · rw [eli (w + 1) (by omega) h1, hcs]; linarith
  have g_hl'1 : l' (N₀ + 1 - 1) < 1 := by
    rw [show N₀ + 1 - 1 = N₀ by omega, el'N]; linarith
  have g_hα0 : α 0 ≤ 0 := by rw [eα0]; norm_num
  have g_hα : ∀ p, 1 ≤ p → p ≤ N₀ + 1 → α p ≤ l (p - 1) := by
    intro p hp1 hp2
    rcases hcases p hp2 with h | h | ⟨h1, h2, -, h4⟩
    · omega
    · rw [h, eαM, show N₀ + 1 - 1 = N₀ by omega, elN]; linarith
    · rw [eαi p h1 h2]
      by_cases h5 : p - 1 = 0
      · rw [h5, el0, hc0]; linarith
      · rw [eli (p - 1) h5 (by omega)]; linarith
  have g_hβ : ∀ p < N₀ + 1, l' p < β p := by
    intro p hp
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, el'0, eβ0]; linarith
    · rw [eβi p (by omega) (by omega)]
      by_cases h1 : p = N₀
      · rw [h1, el'N, hcN]; linarith
      · rw [el'i p (by omega) h1]; linarith
  have g_hβM : 1 ≤ β (N₀ + 1) := by rw [eβM]; norm_num
  -- the maps
  have g_hRc : ∀ p ≤ N₀ + 1, IsChainMap (R p) := by
    intro p hp
    rcases hcases p hp with h | h | ⟨h1, h2, h3, h4⟩
    · rw [h, eR0]; exact hR0c
    · rw [h, eRM]; exact hR1c
    · rw [eRi p h1 h2]; exact hRsc (p - 1) (by omega)
  have g_hRS : ∀ p ≤ N₀ + 1, ∀ b, σ p ≤ (R p b).val ∧ (R p b).val ≤ σ' p := by
    intro p hp b
    rcases hcases p hp with h | h | ⟨h1, h2, h3, h4⟩
    · rw [h, eR0, eσ0, eσ'0]; exact hR0S b
    · rw [h, eRM, eσM, eσ'M]; exact hR1S b
    · rw [eRi p h1 h2, eσi p h1 h2, eσ'i p h1 h2]; exact hRsS (p - 1) (by omega) b
  have hJsub : ∀ p, p ≠ 0 → p ≠ N₀ + 1 → ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p →
      x ∈ Icc (aJ (p - 1)) (bJ (p - 1)) := by
    intro p h1 h2 x hx1 hx2
    rw [eαi p h1 h2] at hx1
    rw [eβi p h1 h2] at hx2
    exact hJmem (p - 1) x hx1 (by rw [show p - 1 + 1 = p by omega]; exact hx2)
  have g_hP1 : ∀ p ≤ N₀ + 1, ∀ b, ∀ y ∈ F.link b, α p ≤ (g y : ℝ) → (g y : ℝ) ≤ β p →
      y ∈ E.link (H (R p b)) := by
    intro p hp b y hy h1 h2
    rcases hcases p hp with h | h | ⟨h1', h2', h3, h4⟩
    · rw [h, eR0]; rw [h, eβ0] at h2
      exact hτeP b y hy (habs0 _ _ (h2.trans hτe'))
    · rw [h, eRM]; rw [h, eαM] at h1
      exact hτfP b y hy (habs1 _ _ (by linarith))
    · rw [eRi p h1' h2']
      exact hRs1 (p - 1) (by omega) b y hy (hJsub p h1' h2' (g y) h1 h2)
  have g_hP2a : ∀ p ≤ N₀ + 1, ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p → ∀ j : Fin n,
      σ p ≤ j.val → j.val ≤ σ' p → (D.link j ∩ f ⁻¹' {x}).Nonempty := by
    intro p hp x h1 h2 j hj1 hj2
    rcases hcases p hp with h | h | ⟨h1', h2', h3, h4⟩
    · rw [h, eσ0] at hj1; rw [h, eσ'0] at hj2; rw [h, eβ0] at h2
      exact (hτcP x (habs0 _ _ (h2.trans hτc'))).1 j hj1 hj2
    · rw [h, eσM] at hj1; rw [h, eσ'M] at hj2; rw [h, eαM] at h1
      exact (hτdP x (habs1 _ _ (by linarith))).1 j hj1 hj2
    · rw [eσi p h1' h2'] at hj1; rw [eσ'i p h1' h2'] at hj2
      exact hPm (p - 1) (by omega) x (hJsub p h1' h2' x h1 h2) j hj1 hj2
  have g_hP2b : ∀ p ≤ N₀ + 1, ∀ x : unitInterval, α p ≤ x → (x : ℝ) ≤ β p →
      f ⁻¹' {x} ⊆ ⋃ (j : Fin n) (_ : σ p ≤ j.val ∧ j.val ≤ σ' p), D.link j := by
    intro p hp x h1 h2
    rcases hcases p hp with h | h | ⟨h1', h2', h3, h4⟩
    · rw [h, eσ0, eσ'0]; rw [h, eβ0] at h2
      exact (hτcP x (habs0 _ _ (h2.trans hτc'))).2
    · rw [h, eσM, eσ'M]; rw [h, eαM] at h1
      exact (hτdP x (habs1 _ _ (by linarith))).2
    · rw [eσi p h1' h2', eσ'i p h1' h2']
      exact hPc (p - 1) (by omega) x (hJsub p h1' h2' x h1 h2)
  -- the runs at the windows
  have g_htu : ∀ w < N₀ + 1, t w ≤ u w := by
    intro w hw
    rcases hwcases w hw with h | h | ⟨h1, h2, -, -⟩
    · rw [h, et0, eu0]; exact htur 0
    · rw [h, etN, euN]; exact htur 1
    · rw [eti w h1 h2, eui w h1 h2]; exact htur _
  have g_huN : ∀ w < N₀ + 1, u w < N := by
    intro w hw
    rcases hwcases w hw with h | h | ⟨h1, h2, -, -⟩
    · rw [h, eu0]; exact hurN 0
    · rw [h, euN]; exact hurN 1
    · rw [eui w h1 h2]; exact hurN _
  have hcut' : ∀ w, w ≠ 0 → w ≠ N₀ → 1 ≤ w → w < N₀ → ∀ x : unitInterval, l w ≤ x →
      (x : ℝ) ≤ l' w → (∀ k : Fin N, tr (cc w) ≤ k.val → k.val ≤ ur (cc w) →
        (F.link k ∩ g ⁻¹' {x}).Nonempty) ∧
      g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : tr (cc w) ≤ k.val ∧ k.val ≤ ur (cc w)), F.link k := by
    intro w h1 h2 h3 h4 x hx1 hx2
    rw [eli w h1 h2] at hx1
    rw [el'i w h1 h2] at hx2
    obtain ⟨i, rfl⟩ : ∃ i : Fin (N₀ + 1), i.val = w := ⟨⟨w, by omega⟩, rfl⟩
    have hgi : τ ≤ τg i := hτh'.trans (hτhle i)
    have hcw := hccv i.val h4.le
    have hle : |(x : ℝ) - ((cc i.val : unitInterval) : ℝ)| ≤ τg i := by
      rw [hcw, abs_of_nonneg (by linarith only [hx1])]
      linarith only [hx2, hgi, hτpos]
    exact hτgP i x hle
  have g_hTf : ∀ w < N₀ + 1, ∀ x : unitInterval, l w ≤ x → (x : ℝ) ≤ l' w → ∀ k : Fin N,
      t w ≤ k.val → k.val ≤ u w → (F.link k ∩ g ⁻¹' {x}).Nonempty := by
    intro w hw x hx1 hx2 k hk1 hk2
    rcases hwcases w hw with h | h | ⟨h1, h2, h3, h4⟩
    · rw [h, et0] at hk1; rw [h, eu0] at hk2; rw [h, el'0] at hx2
      exact (hτaP x (habs0 x τa (by linarith))).1 k hk1 hk2
    · rw [h, etN] at hk1; rw [h, euN] at hk2; rw [h, elN] at hx1
      exact (hτbP x (habs1 x τb (by linarith))).1 k hk1 hk2
    · rw [eti w h1 h2] at hk1; rw [eui w h1 h2] at hk2
      exact (hcut' w h1 h2 h3 h4 x hx1 hx2).1 k hk1 hk2
  have g_hTc : ∀ w < N₀ + 1, ∀ x : unitInterval, l w ≤ x → (x : ℝ) ≤ l' w →
      g ⁻¹' {x} ⊆ ⋃ (k : Fin N) (_ : t w ≤ k.val ∧ k.val ≤ u w), F.link k := by
    intro w hw x hx1 hx2
    rcases hwcases w hw with h | h | ⟨h1, h2, h3, h4⟩
    · rw [h, et0, eu0]; rw [h, el'0] at hx2
      exact (hτaP x (habs0 x τa (by linarith))).2
    · rw [h, etN, euN]; rw [h, elN] at hx1
      exact (hτbP x (habs1 x τb (by linarith))).2
    · rw [eti w h1 h2, eui w h1 h2]
      exact (hcut' w h1 h2 h3 h4 x hx1 hx2).2
  -- membership of the cut points in the sub-arcs
  have hmem0 : (0 : unitInterval) ∈ Icc (aJ 0) (bJ 0) :=
    hJmem 0 0 (by rw [hc0, Set.Icc.coe_zero]; linarith)
      (by rw [Set.Icc.coe_zero, hcs, hc0]; linarith)
  have hmem1 : (1 : unitInterval) ∈ Icc (aJ (N₀ - 1)) (bJ (N₀ - 1)) :=
    hJmem (N₀ - 1) 1 (by rw [Set.Icc.coe_one]; linarith [hc_le1 (N₀ - 1) (by omega)])
      (by rw [Set.Icc.coe_one, show N₀ - 1 + 1 = N₀ by omega, hcN]; linarith)
  have hmemc : ∀ w i, w ≤ N₀ → (i + 1 = w ∨ i = w) → (cc w) ∈ Icc (aJ i) (bJ i) := by
    intro w i hw hi
    apply hJmem i (cc w)
    · rw [hccv w hw]
      rcases hi with hi | hi
      · rw [← hi, hcs]; linarith
      · rw [hi]; linarith
    · rw [hccv w hw]
      rcases hi with hi | hi
      · rw [hi]; linarith
      · rw [hi, hcs]; linarith
  have g_hTp : ∀ w < N₀ + 1, IsPatternOn (R w) (σ w) (σ' w) (t w) (u w) ∧
      IsPatternOn (R (w + 1)) (σ (w + 1)) (σ' (w + 1)) (t w) (u w) := by
    intro w hw
    rcases hwcases w hw with h | h | ⟨h1, h2, h3, h4⟩
    · subst h
      rw [eR0, eσ0, eσ'0, et0, eu0, eRi 1 (by omega) (by omega), eσi 1 (by omega) (by omega),
        eσ'i 1 (by omega) (by omega)]
      exact ⟨hpat0, hRs2 0 (by omega) 0 hmem0 (tr 0) (ur 0) (hurN 0) (htur 0) (hrunc 0)⟩
    · subst h
      rw [eRM, eσM, eσ'M, etN, euN, eRi w (by omega) (by omega), eσi w (by omega) (by omega),
        eσ'i w (by omega) (by omega)]
      exact ⟨hRs2 (w - 1) (by omega) 1 hmem1 (tr 1) (ur 1) (hurN 1) (htur 1) (hrunc 1), hpat1⟩
    · rw [eRi w h1 (by omega), eσi w h1 (by omega), eσ'i w h1 (by omega), eti w h1 h2,
        eui w h1 h2, eRi (w + 1) (by omega) (by omega), eσi (w + 1) (by omega) (by omega),
        eσ'i (w + 1) (by omega) (by omega)]
      refine ⟨hRs2 (w - 1) (by omega) (cc w) (hmemc w (w - 1) h4.le (Or.inl (by omega))) _ _
        (hurN _) (htur _) (hrunc _), ?_⟩
      have := hRs2 w h4 (cc w) (hmemc w w h4.le (Or.inr rfl)) _ _ (hurN _) (htur _) (hrunc _)
      simpa using this
  have g_hout : ∀ p ≤ N₀ + 1, ∀ x : unitInterval, (p = 0 ∨ l' (p - 1) < x) →
      (p = N₀ + 1 ∨ (x : ℝ) < l p) →
      ∃ t' u', t' ≤ u' ∧ u' < N ∧ (∀ k : Fin N, t' ≤ k.val → k.val ≤ u' →
        (F.link k ∩ g ⁻¹' {x}).Nonempty) ∧ IsPatternOn (R p) (σ p) (σ' p) t' u' := by
    intro p hp x hl1 hl2
    rcases hcases p hp with h | h | ⟨h1, h2, h3, h4⟩
    · subst h
      rcases hl2 with h' | h'
      · omega
      rw [el0] at h'
      rw [eR0, eσ0, eσ'0]
      exact ⟨tr 0, ur 0, htur 0, hurN 0, (hτaP x (habs0 x τa (by linarith))).1, hpat0⟩
    · subst h
      rcases hl1 with h' | h'
      · omega
      rw [show N₀ + 1 - 1 = N₀ by omega, el'N] at h'
      rw [eRM, eσM, eσ'M]
      exact ⟨tr 1, ur 1, htur 1, hurN 1, (hτbP x (habs1 x τb (by linarith))).1, hpat1⟩
    · rw [eRi p h1 h2, eσi p h1 h2, eσ'i p h1 h2]
      refine ⟨tr x, ur x, htur x, hurN x, hrunm x, hRs2 (p - 1) (by omega) x ?_ _ _ (hurN x)
        (htur x) (hrunc x)⟩
      apply hJmem
      · rcases hl1 with h' | h'
        · omega
        by_cases h5 : p - 1 = 0
        · rw [h5, el'0] at h'; rw [h5, hc0]; linarith
        · rw [el'i (p - 1) h5 (by omega)] at h'; linarith
      · rcases hl2 with h' | h'
        · omega
        rw [show p - 1 + 1 = p by omega]
        by_cases h5 : p = N₀
        · rw [h5, elN] at h'; rw [h5, hcN]; linarith
        · rw [eli p h1 h5] at h'; linarith
  have g_hC0 : ∀ b (z : g ⁻¹' {0}), (z : Y) ∈ F.link b → (h₀.symm z : X) ∈ D.link (R 0 b) := by
    intro b z hz; rw [eR0]; exact hR0cl b z (subset_closure hz)
  have g_hC1 : ∀ b (z : g ⁻¹' {1}), (z : Y) ∈ F.link b →
      (h₁.symm z : X) ∈ D.link (R (N₀ + 1) b) := by
    intro b z hz; rw [eRM]; exact hR1cl b z (subset_closure hz)
  exact bj_glue hg hSY h₀ h₁ D hDp E H hδ F hFc (M := N₀ + 1) (by omega) l l' g_hl0 g_hll'
    g_hl'l g_hl'1 α β g_hα0 g_hα g_hβ g_hβM σ σ' R g_hRc g_hRS g_hP1 g_hP2a g_hP2b t u g_htu
    g_huN g_hTf g_hTc g_hTp g_hout g_hC0 g_hC1

end HPC.BJ59