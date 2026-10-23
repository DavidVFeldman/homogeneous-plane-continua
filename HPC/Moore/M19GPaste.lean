import Mathlib

/-!
# Pasting compatible embeddings of growing squares (batch 144, item C)

Pure topology. If `Ψₙ` embeds the square `[-(n+1), n+1]²` (the closed ball of radius `n + 1` of
`ℝ × ℝ` with its sup metric) onto `Dₙ`, each `Ψₙ₊₁` extends `Ψₙ`, each `Dₙ` lies in the interior
of `Dₙ₊₁`, and the `Dₙ` cover the Hausdorff space `X`, then `ℝ × ℝ ≃ₜ X` (`exhaust_homeomorph`).
-/

namespace HPC.Sq

open Set Topology Metric Filter

/-- The closed square of radius `r` (sup metric). -/
abbrev Bsq (r : ℝ) : Set (ℝ × ℝ) := closedBall 0 r

section Paste

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **Pasting.** Compatible embeddings of the squares `[-(n+1), n+1]²` onto an exhaustion
`D₀ ⊆ int D₁ ⊆ D₁ ⊆ int D₂ ⊆ ⋯` of a Hausdorff space give a homeomorphism `ℝ × ℝ ≃ₜ X` which
agrees with each `Ψₙ` on its square. -/
theorem exhaust_homeomorph (Ψ : ℕ → ℝ × ℝ → X) (D : ℕ → Set X)
    (hc : ∀ n, ContinuousOn (Ψ n) (Bsq (n + 1))) (hi : ∀ n, InjOn (Ψ n) (Bsq (n + 1)))
    (hext : ∀ n, EqOn (Ψ (n + 1)) (Ψ n) (Bsq (n + 1))) (himg : ∀ n, Ψ n '' Bsq (n + 1) = D n)
    (hint : ∀ n, D n ⊆ interior (D (n + 1))) (hcov : ∀ x, ∃ n, x ∈ D n) :
    ∃ e : ℝ × ℝ ≃ₜ X, ∀ n, EqOn e (Ψ n) (Bsq (n + 1)) := by
  -- compatibility
  have compat : ∀ m n, m ≤ n → EqOn (Ψ n) (Ψ m) (Bsq (m + 1)) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ n hmn ih =>
      intro p hp
      have hp' : p ∈ Bsq (n + 1) := closedBall_subset_closedBall
        (by exact_mod_cast Nat.add_le_add_right hmn 1) hp
      rw [hext n hp', ih hp]
  let N : ℝ × ℝ → ℕ := fun p => ⌈‖p‖⌉₊
  have hN : ∀ p, p ∈ Bsq (N p + 1) := fun p => by
    rw [mem_closedBall, dist_zero_right]
    have := Nat.le_ceil ‖p‖; linarith
  let F : ℝ × ℝ → X := fun p => Ψ (N p) p
  have hFn : ∀ n, EqOn F (Ψ n) (Bsq (n + 1)) := by
    intro n p hp
    rw [mem_closedBall, dist_zero_right] at hp
    have hNp : N p ≤ n + 1 := by
      have := Nat.ceil_le.mpr (show ‖p‖ ≤ ((n + 1 : ℕ) : ℝ) by push_cast; exact hp)
      exact this
    rcases Nat.lt_or_eq_of_le hNp with h | h
    · exact (compat (N p) n (Nat.lt_succ_iff.mp h) (hN p)).symm
    · show Ψ (N p) p = Ψ n p
      rw [h]; exact hext n (by rw [mem_closedBall, dist_zero_right]; exact hp)
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hmem : Bsq (N p + 1) ∈ 𝓝 p := by
      refine mem_of_superset (ball_mem_nhds p (one_pos : (0 : ℝ) < 1)) ?_
      intro q hq
      rw [mem_ball] at hq
      rw [mem_closedBall]
      have h1 := dist_triangle q p 0
      have h2 : dist p 0 ≤ N p := by
        rw [dist_zero_right]; exact Nat.le_ceil _
      linarith
    have := ((hc (N p)).continuousAt hmem)
    exact this.congr (eventuallyEq_of_mem hmem fun q hq => (hFn (N p) hq).symm)
  have hinj : Function.Injective F := by
    intro p q hpq
    set n := max (N p) (N q)
    have hp : p ∈ Bsq (n + 1) := closedBall_subset_closedBall
      (by exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1) (hN p)
    have hq : q ∈ Bsq (n + 1) := closedBall_subset_closedBall
      (by exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1) (hN q)
    rw [hFn n hp, hFn n hq] at hpq
    exact hi n hp hq hpq
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨n, hn⟩ := hcov x
    rw [← himg n] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    exact ⟨p, hFn n hp⟩
  have hopen : IsOpenMap F := by
    intro U hU
    have heq : F '' U = ⋃ n, Ψ n '' (U ∩ Bsq (n + 1)) ∩ interior (D n) := by
      ext x
      simp only [mem_image, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨p, hpU, rfl⟩
        obtain ⟨n, hn⟩ := hcov (F p)
        refine ⟨n + 1, ?_, hint n hn⟩
        have hx : F p ∈ D (n + 1) := interior_subset (hint n hn)
        rw [← himg] at hx
        obtain ⟨q, hq, hqp⟩ := hx
        have : q = p := hinj ((hFn _ hq).trans hqp)
        subst this
        exact ⟨q, ⟨hpU, hq⟩, hqp⟩
      · rintro ⟨n, ⟨p, ⟨hpU, hp⟩, rfl⟩, -⟩
        exact ⟨p, hpU, hFn n hp⟩
    rw [heq]
    refine isOpen_iUnion fun n => ?_
    have hK : IsCompact (Ψ n '' (Bsq (n + 1) \ U)) :=
      ((isCompact_closedBall _ _).diff hU).image_of_continuousOn
        ((hc n).mono diff_subset)
    have : Ψ n '' (U ∩ Bsq (n + 1)) ∩ interior (D n) =
        (Ψ n '' (Bsq (n + 1) \ U))ᶜ ∩ interior (D n) := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_diff]
      constructor
      · rintro ⟨⟨p, ⟨hpU, hp⟩, rfl⟩, hx⟩
        refine ⟨?_, hx⟩
        rintro ⟨q, ⟨hq, hqU⟩, hqp⟩
        exact hqU (hi n hp hq hqp.symm ▸ hpU)
      · rintro ⟨hx, hxD⟩
        have hx' : x ∈ D n := interior_subset hxD
        rw [← himg] at hx'
        obtain ⟨p, hp, rfl⟩ := hx'
        refine ⟨⟨p, ⟨?_, hp⟩, rfl⟩, hxD⟩
        by_contra hpU
        exact hx ⟨p, ⟨hp, hpU⟩, rfl⟩
    rw [this]
    exact hK.isClosed.isOpen_compl.inter isOpen_interior
  let e := Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective F ⟨hinj, hsurj⟩) hcont hopen
  exact ⟨e, fun n p hp => hFn n hp⟩

end Paste

end HPC.Sq

namespace HPC.Sq

open Set Topology Metric Filter Function

section Radial

variable {X : Type*} [TopologicalSpace X]

/-- The properties of the `n`-th stage: an embedding of the square of radius `r` onto `J ∪ I`
sending its boundary onto `J`. -/
def StageProp (r : ℝ) (J I : Set X) (Ψ : ℝ × ℝ → X) : Prop :=
  ContinuousOn Ψ (Bsq r) ∧ InjOn Ψ (Bsq r) ∧ Ψ '' Bsq r = J ∪ I ∧ Ψ '' sphere 0 r = J

/-- A *collar* of `J` in `D'`: an embedding `H` of `J × [0, 1]` onto `D' − I`, the identity on
`J × 0`, sending `J × 1` onto `J'`. -/
def CollarProp (J I D' J' : Set X) (H : X × ℝ → X) : Prop :=
  ContinuousOn H (J ×ˢ Icc 0 1) ∧ InjOn H (J ×ˢ Icc 0 1) ∧ (∀ z ∈ J, H (z, 0) = z) ∧
    H '' (J ×ˢ Icc 0 1) = D' \ I ∧ H '' (J ×ˢ {1}) = J'

/-- **The radial step.** A stage of radius `r` and a collar of its boundary give a stage of radius
`r + 1` extending it: `Ψ' p = H (Ψ (r p / ‖p‖), ‖p‖ - r)` outside the square of radius `r`. -/
theorem radial_step {r : ℝ} (hr : 0 < r) {J I D' J' : Set X} {Ψ : ℝ × ℝ → X}
    (hΨ : StageProp r J I Ψ) (hID : I ⊆ D') {H : X × ℝ → X}
    (hH : CollarProp J I D' J' H) :
    ∃ Ψ', StageProp (r + 1) J' (D' \ J') Ψ' ∧ EqOn Ψ' Ψ (Bsq r) ∧ Ψ' '' Bsq (r + 1) = D' := by
  classical
  obtain ⟨hc, hi, himg, hsph⟩ := hΨ
  obtain ⟨hHc, hHi, hH0, hHimg, hH1⟩ := hH
  set ρ : ℝ × ℝ → ℝ × ℝ := fun p => (r / ‖p‖) • p with hρ
  have nρ : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ‖ρ p‖ = r := by
    intro p hp
    have hp0 : 0 < ‖p‖ := lt_of_lt_of_le hr hp
    simp only [hρ, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_of_pos hp0]
    field_simp
  have ρsph : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ρ p ∈ sphere (0 : ℝ × ℝ) r := fun p hp => by
    rw [mem_sphere, dist_zero_right]; exact nρ p hp
  have ρsq : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ρ p ∈ Bsq r := fun p hp => sphere_subset_closedBall (ρsph p hp)
  have ρid : ∀ p : ℝ × ℝ, ‖p‖ = r → ρ p = p := by
    intro p hp; simp only [hρ, hp, div_self hr.ne', one_smul]
  have ρcont : ContinuousOn ρ {p | r ≤ ‖p‖} := by
    refine ContinuousOn.smul ?_ continuousOn_id
    refine continuousOn_const.div continuous_norm.continuousOn fun p hp => ?_
    exact (lt_of_lt_of_le hr hp).ne'
  have hJsub : J ⊆ D' \ I := by
    intro z hz
    rw [← hHimg]
    exact ⟨(z, 0), ⟨hz, left_mem_Icc.mpr zero_le_one⟩, hH0 z hz⟩
  have sphJ : ∀ p ∈ sphere (0 : ℝ × ℝ) r, Ψ p ∈ J := fun p hp => hsph ▸ mem_image_of_mem Ψ hp
  set G : ℝ × ℝ → X := fun p => H (Ψ (ρ p), ‖p‖ - r) with hG
  set Ψ' : ℝ × ℝ → X := fun p => if ‖p‖ ≤ r then Ψ p else G p with hΨ'
  have hBr : ∀ p, p ∈ Bsq r ↔ ‖p‖ ≤ r := fun p => by rw [mem_closedBall, dist_zero_right]
  have hBr1 : ∀ p, p ∈ Bsq (r + 1) ↔ ‖p‖ ≤ r + 1 := fun p => by
    rw [mem_closedBall, dist_zero_right]
  have Gin : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ‖p‖ ≤ r + 1 → (Ψ (ρ p), ‖p‖ - r) ∈ J ×ˢ Icc (0 : ℝ) 1 :=
    fun p h1 h2 => ⟨sphJ _ (ρsph p h1), by constructor <;> linarith⟩
  have GΨ : ∀ p : ℝ × ℝ, ‖p‖ = r → G p = Ψ p := by
    intro p hp
    simp only [hG, ρid p hp, hp, sub_self]
    exact hH0 _ (sphJ p (by rw [mem_sphere, dist_zero_right]; exact hp))
  have Ψ'G : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → Ψ' p = G p := by
    intro p hp
    simp only [hΨ']
    split_ifs with h
    · exact (GΨ p (le_antisymm h hp)).symm
    · rfl
  -- continuity
  have hcont : ContinuousOn Ψ' (Bsq (r + 1)) := by
    have hsplit : Bsq (r + 1) = Bsq r ∪ {p | r ≤ ‖p‖ ∧ ‖p‖ ≤ r + 1} := by
      ext p; simp only [mem_union, hBr, hBr1, mem_setOf_eq]
      constructor
      · intro h; by_cases h' : ‖p‖ ≤ r
        · exact Or.inl h'
        · exact Or.inr ⟨le_of_lt (not_le.mp h'), h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closedBall ?_
    · exact hc.congr fun p hp => if_pos ((hBr p).mp hp)
    · refine ContinuousOn.congr ?_ fun p hp => Ψ'G p hp.1
      refine hHc.comp (ContinuousOn.prodMk ?_ ?_) fun p hp => Gin p hp.1 hp.2
      · exact hc.comp (ρcont.mono fun p hp => hp.1) fun p hp => ρsq p hp.1
      · exact (continuous_norm.sub continuous_const).continuousOn
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  -- the outer part lies in `D' − I`
  have Gout : ∀ p : ℝ × ℝ, r ≤ ‖p‖ → ‖p‖ ≤ r + 1 → G p ∈ D' \ I := fun p h1 h2 =>
    hHimg ▸ mem_image_of_mem H (Gin p h1 h2)
  -- reconstruction of a point from its sphere point and radius
  have recon : ∀ (p₀ : ℝ × ℝ), ‖p₀‖ = r → ∀ s : ℝ, 0 ≤ s →
      ‖((r + s) / r) • p₀‖ = r + s ∧ ρ (((r + s) / r) • p₀) = p₀ := by
    intro p₀ hp₀ s hs
    have hn : ‖((r + s) / r) • p₀‖ = r + s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hp₀]; field_simp
    refine ⟨hn, ?_⟩
    simp only [hρ, hn, smul_smul]
    rw [show r / (r + s) * ((r + s) / r) = 1 by field_simp, one_smul]
  have hinj : InjOn Ψ' (Bsq (r + 1)) := by
    -- a point inside cannot match a point strictly outside
    have cross : ∀ p q : ℝ × ℝ, ‖p‖ ≤ r → r < ‖q‖ → ‖q‖ ≤ r + 1 → Ψ p ≠ G q := by
      intro p q hp hq1 hq2 he
      have hGq := Gout q hq1.le hq2
      have hΨJ : Ψ p ∈ J := by
        have : Ψ p ∈ J ∪ I := himg ▸ mem_image_of_mem Ψ ((hBr p).mpr hp)
        exact this.resolve_right fun h => hGq.2 (he ▸ h)
      have h0 : H (Ψ p, 0) = Ψ p := hH0 _ hΨJ
      have := hHi ⟨hΨJ, left_mem_Icc.mpr zero_le_one⟩ (Gin q hq1.le hq2) (h0.trans he)
      simp only [Prod.mk.injEq] at this
      linarith [this.2]
    intro p hp q hq hpq
    rw [hBr1] at hp hq
    by_cases hp' : ‖p‖ ≤ r <;> by_cases hq' : ‖q‖ ≤ r
    · simp only [hΨ', if_pos hp', if_pos hq'] at hpq
      exact hi ((hBr p).mpr hp') ((hBr q).mpr hq') hpq
    · simp only [hΨ', if_pos hp', if_neg hq'] at hpq
      exact absurd hpq (cross p q hp' (not_le.mp hq') hq)
    · simp only [hΨ', if_neg hp', if_pos hq'] at hpq
      exact absurd hpq.symm (cross q p hq' (not_le.mp hp') hp)
    · simp only [hΨ', if_neg hp', if_neg hq'] at hpq
      have h1 := not_le.mp hp'
      have h2 := not_le.mp hq'
      have := hHi (Gin p h1.le hp) (Gin q h2.le hq) hpq
      simp only [Prod.mk.injEq] at this
      have hn : ‖p‖ = ‖q‖ := by linarith [this.2]
      have hρ' : ρ p = ρ q := hi (ρsq p h1.le) (ρsq q h2.le) this.1
      have hp0 : 0 < ‖p‖ := lt_of_lt_of_le hr h1.le
      have ep : p = (‖p‖ / r) • ρ p := by
        simp only [hρ, smul_smul]; rw [show ‖p‖ / r * (r / ‖p‖) = 1 by field_simp, one_smul]
      have eq : q = (‖q‖ / r) • ρ q := by
        have hq0 : 0 < ‖q‖ := lt_of_lt_of_le hr h2.le
        simp only [hρ, smul_smul]; rw [show ‖q‖ / r * (r / ‖q‖) = 1 by field_simp, one_smul]
      rw [ep, eq, hn, hρ']
  -- the image
  have himg' : Ψ' '' Bsq (r + 1) = D' := by
    apply subset_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [hBr1] at hp
      by_cases hp' : ‖p‖ ≤ r
      · simp only [hΨ', if_pos hp']
        have : Ψ p ∈ J ∪ I := himg ▸ mem_image_of_mem Ψ ((hBr p).mpr hp')
        rcases this with h | h
        · exact (hJsub h).1
        · exact hID h
      · rw [Ψ'G p (not_le.mp hp').le]; exact (Gout p (not_le.mp hp').le hp).1
    · intro x hx
      by_cases hxI : x ∈ I
      · have : x ∈ Ψ '' Bsq r := himg ▸ Or.inr hxI
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨p, closedBall_subset_closedBall (by linarith) hp, if_pos ((hBr p).mp hp)⟩
      · have : x ∈ H '' (J ×ˢ Icc 0 1) := hHimg ▸ ⟨hx, hxI⟩
        obtain ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩ := this
        obtain ⟨p₀, hp₀, rfl⟩ : z ∈ Ψ '' sphere 0 r := hsph ▸ hz
        rw [mem_sphere, dist_zero_right] at hp₀
        obtain ⟨hn, hρq⟩ := recon p₀ hp₀ s hs.1
        refine ⟨((r + s) / r) • p₀, (hBr1 _).mpr (by rw [hn]; linarith [hs.2]), ?_⟩
        rw [Ψ'G _ (by rw [hn]; linarith [hs.1])]
        simp only [hG, hρq, hn, add_sub_cancel_left]
  refine ⟨Ψ', ⟨hcont, hinj, ?_, ?_⟩, fun p hp => if_pos ((hBr p).mp hp), himg'⟩
  · -- `D' = J' ∪ (D' − J')`
    rw [himg']
    have hJ'D : J' ⊆ D' := by
      rw [← hH1]
      rintro _ ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
      have hmem : (z, s) ∈ J ×ˢ Icc (0 : ℝ) 1 :=
        ⟨hz, by rw [mem_singleton_iff.mp hs]; exact right_mem_Icc.mpr zero_le_one⟩
      have : H (z, s) ∈ D' \ I := hHimg ▸ mem_image_of_mem H hmem
      exact this.1
    exact (union_diff_cancel hJ'D).symm
  · apply subset_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [mem_sphere, dist_zero_right] at hp
      rw [Ψ'G p (by linarith), ← hH1]
      refine ⟨(Ψ (ρ p), ‖p‖ - r), ⟨sphJ _ (ρsph p (by linarith)), ?_⟩, rfl⟩
      rw [hp, mem_singleton_iff]; ring
    · intro x hx
      rw [← hH1] at hx
      obtain ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩ := hx
      rw [mem_singleton_iff] at hs
      subst hs
      obtain ⟨p₀, hp₀, rfl⟩ : z ∈ Ψ '' sphere 0 r := hsph ▸ hz
      rw [mem_sphere, dist_zero_right] at hp₀
      obtain ⟨hn, hρq⟩ := recon p₀ hp₀ 1 zero_le_one
      refine ⟨((r + 1) / r) • p₀, by rw [mem_sphere, dist_zero_right, hn], ?_⟩
      rw [Ψ'G _ (by rw [hn]; linarith)]
      simp only [hG, hρq, hn, add_sub_cancel_left]

/-- **A plane from an exhaustion with collars.** If `Jₙ ∪ Iₙ ⊆ Iₙ₊₁` (with `Iₙ` open and disjoint
from `Jₙ`), the `Iₙ` cover the Hausdorff space `X`, `J₀ ∪ I₀` is a square with boundary `J₀`, and
each `Jₙ` has a collar in `Jₙ₊₁ ∪ Iₙ₊₁` ending on `Jₙ₊₁`, then `X` is homeomorphic to `ℝ × ℝ`. -/
theorem plane_of_collars [T2Space X] (Jn In : ℕ → Set X) (hdisj : ∀ n, Disjoint (Jn n) (In n))
    (hsub : ∀ n, Jn n ∪ In n ⊆ In (n + 1)) (hopen : ∀ n, IsOpen (In n))
    (hcov : ∀ x, ∃ n, x ∈ In n) (base : ∃ Ψ, StageProp 1 (Jn 0) (In 0) Ψ)
    (collar : ∀ n, ∃ H, CollarProp (Jn n) (In n) (Jn (n + 1) ∪ In (n + 1)) (Jn (n + 1)) H) :
    ∃ e : ℝ × ℝ ≃ₜ X, ∃ Ψ : ℕ → ℝ × ℝ → X,
      (∀ n : ℕ, StageProp ((n : ℝ) + 1) (Jn n) (In n) (Ψ n)) ∧
      ∀ n : ℕ, EqOn e (Ψ n) (Bsq ((n : ℝ) + 1)) := by
  classical
  have step : ∀ (n : ℕ) (Ψ : ℝ × ℝ → X), StageProp ((n : ℝ) + 1) (Jn n) (In n) Ψ →
      ∃ Ψ', StageProp (((n + 1 : ℕ) : ℝ) + 1) (Jn (n + 1)) (In (n + 1)) Ψ' ∧
        EqOn Ψ' Ψ (Bsq ((n : ℝ) + 1)) := by
    intro n Ψ hΨ
    obtain ⟨H, hH⟩ := collar n
    have hID : In n ⊆ Jn (n + 1) ∪ In (n + 1) := fun x hx =>
      Or.inr (hsub n (Or.inr hx))
    obtain ⟨Ψ', hΨ', heq, -⟩ := radial_step (by positivity) hΨ hID hH
    refine ⟨Ψ', ?_, heq⟩
    have e1 : (Jn (n + 1) ∪ In (n + 1)) \ Jn (n + 1) = In (n + 1) := by
      rw [union_diff_left]; exact (hdisj (n + 1)).symm.sdiff_eq_left
    rw [e1] at hΨ'
    have e2 : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) + 1 := by push_cast; ring
    rw [e2]; exact hΨ'
  let P : ℕ → Type _ := fun n => {Ψ : ℝ × ℝ → X // StageProp ((n : ℝ) + 1) (Jn n) (In n) Ψ}
  have base' : StageProp (((0 : ℕ) : ℝ) + 1) (Jn 0) (In 0) (Classical.choose base) := by
    simpa using Classical.choose_spec base
  let seq : ∀ n, P n := fun n => Nat.rec (motive := P) ⟨_, base'⟩
    (fun n x => ⟨Classical.choose (step n x.1 x.2), (Classical.choose_spec (step n x.1 x.2)).1⟩) n
  have hseq : ∀ n, EqOn (seq (n + 1)).1 (seq n).1 (Bsq ((n : ℝ) + 1)) := fun n =>
    (Classical.choose_spec (step n (seq n).1 (seq n).2)).2
  obtain ⟨e, he⟩ := exhaust_homeomorph (fun n => (seq n).1) (fun n => Jn n ∪ In n)
    (fun n => (seq n).2.1) (fun n => (seq n).2.2.1) hseq (fun n => (seq n).2.2.2.1)
    (fun n => (hsub n).trans (interior_maximal subset_union_right (hopen (n + 1))))
    (fun x => by obtain ⟨n, hn⟩ := hcov x; exact ⟨n, Or.inr hn⟩)
  exact ⟨e, fun n => (seq n).1, fun n => (seq n).2, he⟩

/-- `t ↦ (t + 1) / 2`, from `[-1, 1]` to the unit interval. -/
noncomputable def toI (t : ℝ) : unitInterval := projIcc 0 1 zero_le_one ((t + 1) / 2)

theorem toI_val {t : ℝ} (h : |t| ≤ 1) : (toI t : ℝ) = (t + 1) / 2 := by
  rw [toI, projIcc_of_mem]
  rw [abs_le] at h
  constructor <;> linarith

/-- **The base stage.** An embedding of the unit square onto `J ∪ I` sending exactly its boundary
into `J` gives a stage of radius `1`. -/
theorem stage_of_square {J I : Set X} (f : unitInterval × unitInterval → X)
    (hf : IsEmbedding f) (hr : range f = J ∪ I)
    (hbd : ∀ p, ((p.1 : ℝ) = 0 ∨ (p.1 : ℝ) = 1 ∨ (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1) ↔ f p ∈ J) :
    ∃ Ψ, StageProp 1 J I Ψ := by
  set Ψ : ℝ × ℝ → X := fun p => f (toI p.1, toI p.2) with hΨ
  have hmem : ∀ p : ℝ × ℝ, p ∈ Bsq 1 ↔ |p.1| ≤ 1 ∧ |p.2| ≤ 1 := fun p => by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have hcont : Continuous Ψ :=
    hf.continuous.comp ((continuous_projIcc.comp ((continuous_fst.add continuous_const).div_const
      _)).prodMk (continuous_projIcc.comp ((continuous_snd.add continuous_const).div_const _)))
  have hinj : InjOn Ψ (Bsq 1) := by
    intro p hp q hq hpq
    rw [hmem] at hp hq
    have := hf.injective hpq
    simp only [Prod.mk.injEq] at this
    have e1 := congrArg Subtype.val this.1
    have e2 := congrArg Subtype.val this.2
    rw [toI_val hp.1, toI_val hq.1] at e1
    rw [toI_val hp.2, toI_val hq.2] at e2
    exact Prod.ext (by linarith) (by linarith)
  have hpre : ∀ u : unitInterval × unitInterval, ∃ p ∈ Bsq 1, (toI p.1, toI p.2) = u := by
    intro u
    have h1 : |2 * (u.1 : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.1.2.1], by linarith [u.1.2.2]⟩
    have h2 : |2 * (u.2 : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.2.2.1], by linarith [u.2.2.2]⟩
    refine ⟨(2 * u.1 - 1, 2 * u.2 - 1), (hmem _).mpr ⟨h1, h2⟩, ?_⟩
    ext
    · rw [toI_val h1]; ring
    · rw [toI_val h2]; ring
  refine ⟨Ψ, hcont.continuousOn, hinj, ?_, ?_⟩
  · rw [← hr]
    apply subset_antisymm
    · rintro _ ⟨p, -, rfl⟩; exact mem_range_self _
    · rintro _ ⟨u, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hpre u
      exact ⟨p, hp, rfl⟩
  · have key : ∀ p ∈ Bsq 1, p ∈ sphere (0 : ℝ × ℝ) 1 ↔
        ((toI p.1 : ℝ) = 0 ∨ (toI p.1 : ℝ) = 1 ∨ (toI p.2 : ℝ) = 0 ∨ (toI p.2 : ℝ) = 1) := by
      intro p hp
      have hp' := (hmem p).mp hp
      rw [mem_sphere, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
        toI_val hp'.1, toI_val hp'.2]
      obtain ⟨a1, a2⟩ := abs_le.mp hp'.1
      obtain ⟨b1, b2⟩ := abs_le.mp hp'.2
      constructor
      · intro h
        rcases le_total |p.1| |p.2| with h' | h'
        · rw [max_eq_right h'] at h
          rcases abs_eq (zero_le_one' ℝ) |>.mp h with e | e
          · right; right; right; rw [e]; norm_num
          · right; right; left; rw [e]; norm_num
        · rw [max_eq_left h'] at h
          rcases abs_eq (zero_le_one' ℝ) |>.mp h with e | e
          · right; left; rw [e]; norm_num
          · left; rw [e]; norm_num
      · rintro (e | e | e | e)
        · have : p.1 = -1 := by linarith
          rw [this, abs_neg, abs_one]; exact max_eq_left hp'.2
        · have : p.1 = 1 := by linarith
          rw [this, abs_one]; exact max_eq_left hp'.2
        · have : p.2 = -1 := by linarith
          rw [this, abs_neg, abs_one]; exact max_eq_right hp'.1
        · have : p.2 = 1 := by linarith
          rw [this, abs_one]; exact max_eq_right hp'.1
    apply subset_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (hbd _).mp ((key p (sphere_subset_closedBall hp)).mp hp)
    · intro x hx
      have hxr : x ∈ range f := hr ▸ Or.inl hx
      obtain ⟨u, rfl⟩ := hxr
      obtain ⟨p, hp, rfl⟩ := hpre u
      exact ⟨p, (key p hp).mpr ((hbd _).mpr hx), rfl⟩

end Radial

end HPC.Sq
