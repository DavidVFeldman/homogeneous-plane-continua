import HPC.PseudoArc.T5Read
import HPC.PseudoArc.PatRuns

/-!
# Theorem 5: lifts over runs of links in `D_2(u, v)`

Batch 80. The extended pattern `xext` is `h - 1, x_1, …, x_N, k + 1`: the pattern with the two
end values of the end-zone reading added at its ends. `run_lift_geom` lifts it over any interval
of times of the fine chain `F` whose links all lie in `D_2(u, v)` and whose two end links meet
`d(2)_u ∪ d(2)_v`, applying `HPC.PatCore.run_lift` to the end-zone reading restricted (by
clamping) to the positions near the interval.
-/

namespace HPC.T5

open Set

variable {X : Type*} [MetricSpace X] {n0 n1 nR nF : ℕ}

/-- The extended pattern `h - 1, x_1, …, x_N, k + 1` (indices `0, …, N + 1`). -/
def xext {N : ℕ} (x : Fin N → Fin n0) (h k : ℤ) (i : ℕ) : ℤ :=
  if h0 : i = 0 then h - 1 else if hi : i ≤ N then ((x ⟨i - 1, by omega⟩ : ℕ) : ℤ) else k + 1

section Pattern

variable {N : ℕ} {x : Fin N → Fin n0} {h k : Fin n0}

/-- The unpacked hypotheses on a pattern from `h` to `k`. -/
structure Pat (x : Fin N → Fin n0) (h k : Fin n0) : Prop where
  pos : 0 < N
  first : x ⟨0, pos⟩ = h
  last : x ⟨N - 1, by have := pos; omega⟩ = k
  range : ∀ t, h ≤ x t ∧ x t ≤ k
  step : ∀ t t' : Fin N, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1

theorem xext_zero : xext x h k 0 = (h : ℤ) - 1 := by simp [xext]

theorem xext_top : xext x h k (N + 1) = (k : ℤ) + 1 := by simp [xext]

theorem xext_mid {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ N) :
    xext x h k i = ((x ⟨i - 1, by omega⟩ : ℕ) : ℤ) := by
  simp [xext, show i ≠ 0 by omega, h2]

variable (hx : Pat x h k)
include hx

theorem xext_mid_range {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ N) :
    (h : ℤ) ≤ xext x h k i ∧ xext x h k i ≤ (k : ℤ) := by
  rw [xext_mid h1 h2]
  have := hx.range ⟨i - 1, by omega⟩
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

theorem hk_le : h ≤ k := (hx.range ⟨0, hx.pos⟩).1.trans (hx.range ⟨0, hx.pos⟩).2

theorem xext_step (i : ℕ) (hi : i < N + 1) : |xext x h k (i + 1) - xext x h k i| ≤ 1 := by
  have hN := hx.pos
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [xext_mid le_rfl (by omega), xext_zero]
    have := hx.first
    simp only [Nat.sub_self]
    rw [this]; simp
  · rcases Nat.lt_or_ge i N with hlt | hge
    · rw [xext_mid (by omega) (by omega), xext_mid h0 (by omega)]
      have := hx.step ⟨i - 1, by omega⟩ ⟨i + 1 - 1, by omega⟩ (by simp only; omega)
      rw [abs_le]; omega
    · have : i = N := by omega
      subst this
      rw [xext_top, xext_mid h0 le_rfl]
      have := hx.last
      rw [this]; simp

theorem xext_lo (i : ℕ) (hi : i ≤ N + 1) : xext x h k 0 ≤ xext x h k i := by
  have := hk_le hx
  have hk' : (h : ℕ) ≤ k := this
  rw [xext_zero]
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rw [xext_zero]
  · rcases Nat.lt_or_ge N i with hlt | hge
    · rw [show i = N + 1 by omega, xext_top]; omega
    · have := xext_mid_range hx h0 hge; omega

theorem xext_hi (i : ℕ) (hi : i ≤ N + 1) : xext x h k i ≤ xext x h k (N + 1) := by
  have := hk_le hx
  have hk' : (h : ℕ) ≤ k := this
  rw [xext_top]
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rw [xext_zero]; omega
  · rcases Nat.lt_or_ge N i with hlt | hge
    · rw [show i = N + 1 by omega, xext_top]
    · have := xext_mid_range hx h0 hge; omega

theorem xext_eq_low {i : ℕ} (hi : i ≤ N + 1) (he : xext x h k i = (h : ℤ) - 1) : i = 0 := by
  have hk' : (h : ℕ) ≤ k := hk_le hx
  by_contra h0
  rcases Nat.lt_or_ge N i with hlt | hge
  · rw [show i = N + 1 by omega, xext_top] at he; omega
  · have := xext_mid_range hx (by omega) hge; omega

theorem xext_eq_high {i : ℕ} (hi : i ≤ N + 1) (he : xext x h k i = (k : ℤ) + 1) : i = N + 1 := by
  have hk' : (h : ℕ) ≤ k := hk_le hx
  by_contra h0
  rcases Nat.eq_zero_or_pos i with hz | hz
  · subst hz; rw [xext_zero] at he; omega
  · have := xext_mid_range hx hz (by omega); omega

end Pattern

/-- Discrete intermediate values between two times. -/
theorem ivt_times (σ : ℕ → ℤ) (hσ : ∀ f, |σ (f + 1) - σ f| ≤ 1) (t1 t2 : ℕ) (d : ℤ)
    (hd : (σ t1 ≤ d ∧ d ≤ σ t2) ∨ (σ t2 ≤ d ∧ d ≤ σ t1)) :
    ∃ g, min t1 t2 ≤ g ∧ g ≤ max t1 t2 ∧ σ g = d := by
  rcases le_total t1 t2 with h12 | h12
  · obtain ⟨j, hj, hj'⟩ := PatCore.ivt_nat (fun i => σ (t1 + i))
      (fun i => by simpa [add_assoc] using hσ (t1 + i)) (t2 - t1) d
      (by simp only [add_zero]; rw [show t1 + (t2 - t1) = t2 by omega]; exact hd)
    exact ⟨t1 + j, by omega, by omega, hj'⟩
  · obtain ⟨j, hj, hj'⟩ := PatCore.ivt_nat (fun i => σ (t2 + i))
      (fun i => by simpa [add_assoc] using hσ (t2 + i)) (t1 - t2) d
      (by simp only [add_zero]; rw [show t2 + (t1 - t2) = t1 by omega]; tauto)
    exact ⟨t2 + j, by omega, by omega, hj'⟩

variable {D0 : Chain X n0} {D1 : Chain X n1} {R : Chain X nR} {F : Chain X nF}
  {h k : Fin n0} {u v : Fin n1} {W : ℕ} {σ0 : Fin nF → Fin nR} {τ1 : Fin nR → Fin n1}
  {ρ : Fin n1 → Fin n0}

/-- The fine reading, as a function of times `ℕ`. -/
def sigN (σ0 : Fin nF → Fin nR) (hnF : 0 < nF) (f : ℕ) : ℤ :=
  (σ0 ⟨min f (nF - 1), by omega⟩ : ℕ)

theorem sigN_eq (σ0 : Fin nF → Fin nR) (hnF : 0 < nF) {f : ℕ} (hf : f < nF) :
    sigN σ0 hnF f = (σ0 ⟨f, hf⟩ : ℕ) := by
  simp only [sigN]
  rw [show (⟨min f (nF - 1), by omega⟩ : Fin nF) = ⟨f, hf⟩ from Fin.ext (by simp; omega)]

/-- A link of `F` *touches* the end zones: it meets `d(2)_u` or `d(2)_v`. -/
def Touch (D1 : Chain X n1) (F : Chain X nF) (u v : Fin n1) (t : Fin nF) : Prop :=
  (F.link t ∩ D1.link u).Nonempty ∨ (F.link t ∩ D1.link v).Nonempty

/-- **Lift over a run.** -/
theorem run_lift_geom (H : Setup D0 D1 R F h k u v W σ0 τ1 ρ) (hnF : 0 < nF)
    (hS : PatCore.Setting (sigN σ0 hnF) (nF - 1)) {N : ℕ} {x : Fin N → Fin n0}
    (hx : Pat x h k) (hW : 4 * (N + 2) + 10 ≤ W) {a b : ℕ} (hab : a ≤ b) (hb : b < nF)
    (hrun : ∀ g (hg : g < nF), a ≤ g → g ≤ b → InS D1 F u v ⟨g, hg⟩)
    (hta : Touch D1 F u v ⟨a, by omega⟩) (htb : Touch D1 F u v ⟨b, hb⟩) :
    ∃ φ : ℕ → ℕ, (∀ f, a ≤ f → f < b → (φ (f + 1) : ℤ) - φ f ≤ 1 ∧ (φ f : ℤ) - φ (f + 1) ≤ 1) ∧
      ∀ f (hf : f < nF), a ≤ f → f ≤ b → φ f ≤ N + 1 ∧
        ∃ p : Fin nR, ((p : ℤ) - σ0 ⟨f, hf⟩).natAbs ≤ W ∧
          rd D1 R h k u v W τ1 ρ p = xext x h k (φ f) := by
  set σ := sigN σ0 hnF with hσdef
  have hnR : 0 < nR := (σ0 ⟨0, hnF⟩).pos
  obtain ⟨tl, htl, htlmin⟩ := (Finset.Icc a b).exists_min_image σ
    ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  obtain ⟨th, hth, hthmax⟩ := (Finset.Icc a b).exists_max_image σ
    ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  simp only [Finset.mem_Icc] at htl hth htlmin hthmax
  set lo := σ tl
  set hi := σ th
  have hσv : ∀ f (hf : f < nF), σ f = (σ0 ⟨f, hf⟩ : ℕ) := fun f hf => sigN_eq σ0 hnF hf
  have hσR : ∀ f, 0 ≤ σ f ∧ σ f ≤ (nR : ℤ) - 1 := by
    intro f; simp only [hσdef, sigN]
    refine ⟨by positivity, ?_⟩
    have := (σ0 ⟨min f (nF - 1), by omega⟩).isLt
    omega
  let cl : ℤ → Fin nR := fun p => ⟨min (max (lo - W) (min p (hi + W))).toNat (nR - 1), by omega⟩
  have hcl_near : ∀ f, a ≤ f → f ≤ b → ∀ p : ℤ, |p - σ f| ≤ W →
      (((cl p : Fin nR) : ℤ) - σ f).natAbs ≤ W := by
    intro f h1 h2 p hp
    have := htlmin f ⟨h1, h2⟩
    have := hthmax f ⟨h1, h2⟩
    have := hσR f
    rw [abs_le] at hp
    simp only [cl]; omega
  have hcl_fix : ∀ f, a ≤ f → f ≤ b → ((cl (σ f) : Fin nR) : ℤ) = σ f := by
    intro f h1 h2
    have := htlmin f ⟨h1, h2⟩
    have := hthmax f ⟨h1, h2⟩
    have := hσR f
    simp only [cl]; omega
  have hrel : ∀ p : ℤ, Setup.Rel D1 F u v W σ0 (cl p) := by
    intro p
    set c : ℤ := ((cl p : Fin nR) : ℤ) with hc
    have hc1 : lo - W ≤ c ∧ c ≤ hi + W := by
      have := hσR tl; have := hσR th; have := htlmin th ⟨hth.1, hth.2⟩
      simp only [hc, cl]; omega
    obtain ⟨g, hg1, hg2, hg⟩ := ivt_times σ hS.lip tl th (max lo (min c hi))
      (Or.inl ⟨by omega, by
        have := htlmin th ⟨hth.1, hth.2⟩
        omega⟩)
    have hgb : g < nF := by omega
    refine ⟨⟨g, hgb⟩, hrun g hgb (by omega) (by omega), ?_⟩
    rw [← hσv g hgb, hg]
    have := htlmin th ⟨hth.1, hth.2⟩
    omega
  let τK : ℤ → ℤ := fun p => rd D1 R h k u v W τ1 ρ (cl p)
  have hslow : PatCore.Slow W τK := by
    intro p p' hpp
    refine H.slow_rel ?_ (hrel p) (hrel p')
    rw [abs_le] at hpp
    simp only [cl]; omega
  have hend : ∀ f (hf : f < nF), a ≤ f → f ≤ b → Touch D1 F u v ⟨f, hf⟩ →
      τK (σ f) = xext x h k 0 ∨ τK (σ f) = xext x h k (N + 1) := by
    intro f hf h1 h2 ht
    have hp : (((cl (σ f) : Fin nR) : ℤ) - (σ0 ⟨f, hf⟩ : ℕ)).natAbs ≤ W := by
      rw [hcl_fix f h1 h2, hσv f hf]; simp
    rw [xext_zero, xext_top]
    rcases ht with ht | ht
    · exact Or.inl (H.force_u ht hp)
    · exact Or.inr (H.force_v ht hp)
  have hrange : ∀ f, a ≤ f → f ≤ b → xext x h k 0 ≤ τK (σ f) ∧ τK (σ f) ≤ xext x h k (N + 1) := by
    intro f _ _
    rw [xext_zero, xext_top]
    exact H.range _
  obtain ⟨i, j, φ, -, -, hstep, hφ⟩ := PatCore.run_lift (x := xext x h k) (M := N + 1) hS hslow
    (by omega) (by omega) hab (by omega) (fun i hi => xext_step hx i hi)
    (fun i hi => xext_lo hx i hi) (fun i hi => xext_hi hx i hi)
    (by rw [xext_zero, xext_mid le_rfl (by have := hx.pos; omega)]
        simp only [Nat.sub_self]; rw [hx.first]; ring)
    (by rw [xext_top, show N + 1 - 1 = N by omega, xext_mid (by have := hx.pos; omega)
          le_rfl, hx.last])
    (by rw [xext_zero, xext_top]; have := hk_le hx; have : (h : ℕ) ≤ k := this; omega)
    (fun f h1 h2 => (hrange f h1 h2).1) (fun f h1 h2 => (hrange f h1 h2).2)
    (hend a (by omega) le_rfl hab hta) (hend b hb hab le_rfl htb)
  refine ⟨φ, hstep, fun f hf h1 h2 => ?_⟩
  obtain ⟨-, hle, p, hp, hpv⟩ := hφ f h1 h2
  refine ⟨hle, cl p, ?_, hpv⟩
  have := hcl_near f h1 h2 p hp
  rw [hσv f hf] at this
  exact this

end HPC.T5
