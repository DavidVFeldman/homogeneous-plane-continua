import HPC.BJ59.CircStd
import HPC.BJ59.CircJoints

/-!
# Batch 202: the circular planar step (`circ_step`)

Commission 202 §5. The joint positions `CircJ.jointZ` of a lifted pattern are interpolated by the
ramps `Ramp.phat`; the shear `cover` of the universal cover commutes with the deck translations
and descends (`Descent.descHomeo`) to a homeomorphism `ψ` of the plane with
`ψ (circExp (Q N) p) = circExp N (cover p)`. The four properties are read off on the cover.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

namespace CircStepAux

/-- Images under `Φ ∘ circExp N` of small sets of the strip `ℝ × [0, 1]` are small. -/
theorem small_images (Φ : Pt ≃ₜ Pt) {N : ℕ} (hN : N ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ A : Set Pt, (∀ p ∈ A, 0 ≤ p.2 ∧ p.2 ≤ 1) →
      (∀ p ∈ A, ∀ q ∈ A, |p.1 - q.1| ≤ δ ∧ |p.2 - q.2| ≤ δ) →
      diam (Φ '' (circExp N '' A)) ≤ ε := by
  set K₀ : Set Pt := Icc (-1 : ℝ) (2 * N + 1) ×ˢ Icc 0 1
  have hK : IsCompact K₀ := isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (Φ ∘ circExp N) K₀ :=
    hK.uniformContinuousOn_of_continuous
      (Φ.continuous.comp (CircStd.continuous_circExp N)).continuousOn
  obtain ⟨δ₁, hδ₁, hδε⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min (δ₁ / 2) 1, by positivity, min_le_right _ _, fun A hA hd => ?_⟩
  refine diam_le_of_forall_dist_le hε.le ?_
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩ _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set k : ℤ := ⌊p.1 / (2 * N)⌋
  have hk1 : (k : ℝ) ≤ p.1 / (2 * N) := Int.floor_le _
  have hk2 : p.1 / (2 * N) < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ (by positivity)] at hk1
  rw [div_lt_iff₀ (by positivity)] at hk2
  obtain ⟨d1, d2⟩ := hd p hp q hq
  have hm : min (δ₁ / 2) 1 ≤ δ₁ / 2 := min_le_left _ _
  have hm' : min (δ₁ / 2) 1 ≤ 1 := min_le_right _ _
  have ep : circExp N p = circExp N (p.1 + 2 * N * (-k : ℤ), p.2) :=
    (CircStd.circExp_add_int hN p (-k)).symm
  have eq : circExp N q = circExp N (q.1 + 2 * N * (-k : ℤ), q.2) :=
    (CircStd.circExp_add_int hN q (-k)).symm
  rw [ep, eq]
  have h := hδε (p.1 + 2 * N * (-k : ℤ), p.2) ?_ (q.1 + 2 * N * (-k : ℤ), q.2) ?_ ?_
  · exact h.le
  · refine ⟨⟨?_, ?_⟩, (hA p hp).1, (hA p hp).2⟩ <;> push_cast <;> nlinarith
  · rw [abs_le] at d1
    refine ⟨⟨?_, ?_⟩, (hA q hq).1, (hA q hq).2⟩ <;> push_cast <;> nlinarith
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only
    rw [show p.1 + 2 * N * ((-k : ℤ) : ℝ) - (q.1 + 2 * N * ((-k : ℤ) : ℝ)) = p.1 - q.1 by ring]
    refine max_lt (by linarith) (by linarith)

/-- The heights of the shear: `|P̂ u − u/Q − 2y₀ − 3/2| ≤ 2B + 2`. -/
theorem phat_height (P : ℤ → ℝ) (x : ℤ → ℤ) {Q : ℝ} (hQ : 2 ≤ Q) (y₀ B : ℝ)
    (hA : ∀ t, 2 * (x t : ℝ) + 1 / 2 ≤ min (P t) (P (t + 1)) ∧
      max (P t) (P (t + 1)) ≤ 2 * (x t : ℝ) + 5 / 2)
    (hB : ∀ t, |(x t : ℝ) - (y₀ + (t : ℝ) / Q)| ≤ B) (u : ℝ) :
    |Ramp.phat P u - u / Q - (2 * y₀ + 3 / 2)| ≤ 2 * B + 2 := by
  obtain ⟨m1, m2⟩ := Ramp.phat_mem P u
  obtain ⟨a1, a2⟩ := hA (Ramp.piece u)
  obtain ⟨s1, s2⟩ := Ramp.piece_spec u
  have hb := hB (Ramp.piece u)
  rw [abs_le] at hb
  have hw : |(2 * (Ramp.piece u : ℝ) - u) / Q| ≤ 4 / 5 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Q), div_le_iff₀ (by linarith), abs_le]
    constructor <;> nlinarith
  rw [abs_le] at hw ⊢
  have e : Ramp.phat P u - u / Q - (2 * y₀ + 3 / 2) =
      (Ramp.phat P u - 2 * x (Ramp.piece u) - 3 / 2) +
        2 * ((x (Ramp.piece u) : ℝ) - (y₀ + (Ramp.piece u : ℝ) / Q)) +
        (2 * (Ramp.piece u : ℝ) - u) / Q := by
    field_simp; ring
  rw [e]
  have l1 := min_le_left (P (Ramp.piece u)) (P (Ramp.piece u + 1))
  have l2 := le_max_left (P (Ramp.piece u)) (P (Ramp.piece u + 1))
  constructor
  · linarith [min_le_left (P (Ramp.piece u)) (P (Ramp.piece u + 1))]
  · linarith

end CircStepAux

set_option maxHeartbeats 1600000 in
/-- **The circular planar step** (commission §5), the analogue of `real_step`: a slow lifted
pattern of degree one with bounded drift is realized by a tame circular chain, with closures
nested, tightness, and small links or links inside old zones. -/
theorem circ_step (Φ : Pt ≃ₜ Pt) {N : ℕ} (hN : 4 ≤ N) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ S : ℕ, 12 ≤ S ∧ ∀ (Q : ℕ) (x : ℤ → ℤ) (y₀ : ℝ), 2 ≤ Q →
      (∀ t : ℤ, x (t + Q) = x t + 1) → (∀ t, |x (t + 1) - x t| ≤ 1) →
      (∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) →
      (∀ t, |(x t : ℝ) - (y₀ + (t : ℝ) / Q)| ≤ B) →
      ∃ ψ : Pt ≃ₜ Pt,
        (∀ t : ℤ,
          closure ((ψ.trans Φ) '' stdCircLink (Q * N) t) ⊆ Φ '' stdCircLink N (x t)) ∧
        (∀ t l : ℤ, ((ψ.trans Φ) '' stdCircLink (Q * N) t ∩ Φ '' stdCircLink N l).Nonempty →
          ∃ t' n : ℤ, |t' - t| ≤ 1 ∧ x t' = l + n * (N : ℤ)) ∧
        (∀ t : ℤ, diam ((ψ.trans Φ) '' stdCircLink (Q * N) t) ≤ ε ∨
          ∃ k : ℤ, (ψ.trans Φ) '' stdCircLink (Q * N) t ⊆ Φ '' stdCircZone N k) ∧
        (∀ t : ℤ, diam ((ψ.trans Φ) '' stdCircZone (Q * N) t) ≤ ε) := by
  have hN0 : N ≠ 0 := by omega
  obtain ⟨δ, hδ, hδ1, hsmall⟩ := CircStepAux.small_images Φ hN0 hε
  refine ⟨max 12 ⌈1 / δ⌉₊, le_max_left _ _, fun Q x y₀ hQ hper hstep hslow hB => ?_⟩
  set S := max 12 ⌈1 / δ⌉₊ with hSdef
  have hS : 12 ≤ S := le_max_left _ _
  have hSδ : 1 / (2 * (S : ℝ)) ≤ δ / 2 := by
    have h1 : 1 / δ ≤ (S : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 12 ⌈1 / δ⌉₊)
    have hSpos : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hD : 0 < CircJ.wD Q N := by unfold CircJ.wD; positivity
  -- constants
  set ε₀ : ℝ := min (1 / 20) (δ / 2) with hε₀def
  set C : ℝ := min (1 / (8 * B + 12)) (δ / 4) with hCdef
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀a : ε₀ ≤ 1 / 20 := min_le_left _ _
  have hε₀b : ε₀ ≤ δ / 2 := min_le_right _ _
  have hCpos : 0 < C := by positivity
  have hCa : C * (2 * B + 3) ≤ 1 / 4 := by
    have : C ≤ 1 / (8 * B + 12) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  have hCb : C ≤ δ / 4 := min_le_right _ _
  -- joints and the ramp
  have hlf := fun t => CircJ.link_facts_Z Q N S hstep hper hS hD hslow t
  set P : ℤ → ℝ := CircJ.jointZ Q N S hstep with hPdef
  have hP : ∀ t, P (t + ((Q * N : ℕ) : ℤ)) = P t + 2 * N := fun t =>
    CircJ.jointZ_add Q N S hstep t hD
  set g : ℝ → ℝ := Ramp.phat P with hgdef
  have hg : Continuous g := Ramp.continuous_phat P
  set c : ℝ := 2 * y₀ + 3 / 2 with hcdef
  have hH : ∀ u, |g u - u / Q - c| ≤ 2 * B + 2 :=
    CircStepAux.phat_height P x hQr y₀ B (fun t => (hlf t).1) hB
  set N₁ : ℝ := ((Q * N : ℕ) : ℝ) with hN₁def
  have hN₁ : N₁ ≠ 0 := by rw [hN₁def]; exact_mod_cast (show Q * N ≠ 0 by positivity)
  have hN₂ : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hgD : ∀ u, g (u + 2 * N₁) = g u + 2 * N := fun u => by
    have := Ramp.phat_add P hP u
    rw [Int.cast_natCast] at this
    exact this
  have hDA : 2 * N₁ / Q = 2 * N := by
    rw [hN₁def]; push_cast; field_simp
  set G : ℝ × ℝ ≃ₜ ℝ × ℝ := cover g c hg hε₀pos.ne' hCpos.ne' hQ0 with hGdef
  have hGa : ∀ p, G p = (g p.1 + ε₀ * p.2, 1 / 2 + C * (g p.1 - p.1 / Q - c) + C * ε₀ * p.2) :=
    fun p => rfl
  have hG : ∀ p : ℝ × ℝ, G (p.1 + 2 * N₁, p.2) = G p + (2 * (N : ℝ), 0) :=
    cover_add g hg c hgD hDA hε₀pos.ne' hCpos.ne' hQ0
  have hG' : ∀ q : ℝ × ℝ, G.symm (q.1 + 2 * (N : ℝ), q.2) = G.symm q + (2 * N₁, 0) :=
    cover_symm_add g hg c hgD hDA hε₀pos.ne' hCpos.ne' hQ0
  have hb : ∃ a K : ℝ, 0 < a ∧ ∀ p, (G p).2 ≤ a * p.2 + K := by
    refine ⟨C * ε₀, 1 / 2 + C * (2 * B + 2), by positivity, fun p => ?_⟩
    rw [hGa]
    have := (abs_le.mp (hH p.1)).2
    simp only
    nlinarith
  have hb' : ∃ a K : ℝ, 0 < a ∧ ∀ q, (G.symm q).2 ≤ a * q.2 + K := by
    refine ⟨1 / (C * ε₀), (2 * B + 2 - 1 / (2 * C)) / ε₀, by positivity, fun q => ?_⟩
    rw [hGdef, cover_symm_apply]
    simp only
    have := (abs_le.mp (hH (Q * (q.1 - (q.2 - 1 / 2) / C - c)))).1
    rw [show Q * (q.1 - (q.2 - 1 / 2) / C - c) / (Q : ℝ) = q.1 - (q.2 - 1 / 2) / C - c by
      field_simp] at this
    rw [div_le_iff₀ hε₀pos]
    have e : (1 / (C * ε₀) * q.2 + (2 * B + 2 - 1 / (2 * C)) / ε₀) * ε₀ =
        (q.2 - 1 / 2) / C + (2 * B + 2) := by field_simp; ring
    rw [e]; linarith
  set ψ₀ : ℂ ≃ₜ ℂ := Descent.descHomeo hN₁ hN₂ hG hG' hb hb' with hψ₀def
  set ψ : Pt ≃ₜ Pt := CircStd.cpx.symm.trans (ψ₀.trans CircStd.cpx) with hψdef
  have hψ : ∀ p, ψ (circExp (Q * N) p) = circExp N (G p) := fun p => by
    rw [CircStd.circExp_eq, CircStd.circExp_eq, hψdef]
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [hψ₀def, Descent.descHomeo_E]
  have himg : ∀ A : Set Pt, (ψ.trans Φ) '' (circExp (Q * N) '' A) = Φ '' (circExp N '' (G '' A)) :=
    fun A => by
      rw [image_image, image_image, image_image]
      exact image_congr fun p _ => by rw [Homeomorph.trans_apply, hψ]
  -- facts on the cover
  have hfst : ∀ (t : ℤ) (p : Pt), 2 * (t : ℝ) ≤ p.1 → p.1 ≤ 2 * t + 3 → 0 ≤ p.2 → p.2 ≤ 1 →
      min (P t) (P (t + 1)) ≤ (G p).1 ∧ (G p).1 ≤ max (P t) (P (t + 1)) + ε₀ := by
    intro t p h1 h2 h3 h4
    obtain ⟨m1, m2⟩ := Ramp.phat_mem_link P h1 h2
    rw [hGa]; simp only
    have : ε₀ * p.2 ≤ ε₀ := mul_le_of_le_one_right hε₀pos.le h4
    have : 0 ≤ ε₀ * p.2 := mul_nonneg hε₀pos.le h3
    constructor <;> linarith
  have hsnd : ∀ p : Pt, 0 ≤ p.2 → p.2 ≤ 1 → 1 / 4 ≤ (G p).2 ∧ (G p).2 ≤ 3 / 4 := by
    intro p h3 h4
    obtain ⟨k1, k2⟩ := abs_le.mp (hH p.1)
    have e1 := mul_le_mul_of_nonneg_left k2 hCpos.le
    have e2 := mul_le_mul_of_nonneg_left k1 hCpos.le
    have e3 : ε₀ * p.2 ≤ 1 / 20 := (mul_le_of_le_one_right hε₀pos.le h4).trans hε₀a
    have e4 : 0 ≤ ε₀ * p.2 := mul_nonneg hε₀pos.le h3
    have e5 := mul_le_mul_of_nonneg_left e3 hCpos.le
    have e6 := mul_nonneg hCpos.le e4
    rw [hGa]; simp only
    constructor <;> nlinarith
  have hdiff : ∀ (p p' : Pt) (a : ℝ), 0 ≤ p.2 → p.2 ≤ 1 → 0 ≤ p'.2 → p'.2 ≤ 1 →
      |g p.1 - g p'.1| ≤ a → a ≤ 1 / 2 → |p.1 - p'.1| ≤ 3 →
      |(G p).1 - (G p').1| ≤ a + ε₀ ∧ |(G p).2 - (G p').2| ≤ δ := by
    intro p p' a h1 h2 h3 h4 hg ha hu
    rw [hGa, hGa]; simp only
    have hv : |ε₀ * (p.2 - p'.2)| ≤ ε₀ := by
      rw [abs_mul, abs_of_pos hε₀pos]
      exact mul_le_of_le_one_right hε₀pos.le (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hq : |(p.1 - p'.1) / Q| ≤ 3 / 2 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Q), div_le_iff₀ (by linarith)]
      nlinarith
    constructor
    · rw [show g p.1 + ε₀ * p.2 - (g p'.1 + ε₀ * p'.2) = (g p.1 - g p'.1) + ε₀ * (p.2 - p'.2) by
        ring]
      exact (abs_add_le _ _).trans (by linarith)
    · rw [show 1 / 2 + C * (g p.1 - p.1 / Q - c) + C * ε₀ * p.2 -
          (1 / 2 + C * (g p'.1 - p'.1 / Q - c) + C * ε₀ * p'.2) =
          C * ((g p.1 - g p'.1) - (p.1 - p'.1) / Q + ε₀ * (p.2 - p'.2)) by ring,
        abs_mul, abs_of_pos hCpos]
      have hX : |(g p.1 - g p'.1) - (p.1 - p'.1) / Q + ε₀ * (p.2 - p'.2)| ≤ 4 := by
        obtain ⟨a1, a2⟩ := abs_le.mp hg
        obtain ⟨b1, b2⟩ := abs_le.mp hq
        obtain ⟨c1, c2⟩ := abs_le.mp hv
        rw [abs_le]; constructor <;> linarith
      have := mul_le_mul_of_nonneg_left hX hCpos.le
      linarith
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · -- closures nested
    intro t
    rw [stdCircLink, himg, ← Φ.image_closure]
    apply image_mono
    have hcK : IsCompact (closure (stdRectZ t)) := by
      rw [CircStd.closure_stdRectZ]; exact isCompact_Icc.prod isCompact_Icc
    have hcl : closure (circExp N '' (G '' stdRectZ t)) ⊆ circExp N '' (G '' closure (stdRectZ t)) :=
      closure_minimal (image_mono (image_mono subset_closure))
        ((hcK.image G.continuous).image (CircStd.continuous_circExp N)).isClosed
    refine hcl.trans (image_mono ?_)
    rintro _ ⟨p, hp, rfl⟩
    rw [CircStd.closure_stdRectZ] at hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    obtain ⟨f1, f2⟩ := hfst t p h1 h2 h3 h4
    obtain ⟨s1, s2⟩ := hsnd p h3 h4
    obtain ⟨⟨a1, a2⟩, -, -⟩ := hlf t
    rw [stdRectZ, mem_prod, mem_Ioo, mem_Ioo]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith only [f1, a1]
    · linarith only [f2, a2, hε₀a]
    · linarith only [s1]
    · linarith only [s2]
  · -- tightness
    intro t l h
    rw [stdCircLink, himg] at h
    obtain ⟨_, ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩, ⟨_, ⟨q, hq, rfl⟩, hb⟩⟩ := h
    obtain ⟨k, hk⟩ := CircStd.circExp_eq_imp hN0 (Φ.injective hb).symm
    have hk1 := congrArg Prod.fst hk
    simp only at hk1
    obtain ⟨⟨p1, p2⟩, p3, p4⟩ := hp
    obtain ⟨⟨q1, q2⟩, -, -⟩ := hq
    obtain ⟨f1, f2⟩ := hfst t p p1.le p2.le p3.le p4.le
    obtain ⟨t', ht', e⟩ := (hlf t).2.1 (l + k * N) (by push_cast; linarith)
      (by push_cast; linarith)
    exact ⟨t', k, ht', e⟩
  · -- small links or links in old zones
    intro t
    rw [stdCircLink, himg]
    rcases (hlf t).2.2 with hsm | ⟨k, k1, k2⟩
    · left
      apply hsmall
      · rintro _ ⟨p, ⟨-, p3, p4⟩, rfl⟩
        obtain ⟨s1, s2⟩ := hsnd p p3.le p4.le
        constructor <;> linarith
      · rintro _ ⟨p, ⟨⟨p1, p2⟩, p3, p4⟩, rfl⟩ _ ⟨p', ⟨⟨p1', p2'⟩, p3', p4'⟩, rfl⟩
        obtain ⟨m1, m2⟩ := Ramp.phat_mem_link P p1.le p2.le
        obtain ⟨m1', m2'⟩ := Ramp.phat_mem_link P p1'.le p2'.le
        have hS2 : 1 / (2 * (S : ℝ)) ≤ 1 / 2 := by
          have : (1 : ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        obtain ⟨d1, d2⟩ := hdiff p p' (1 / (2 * S)) p3.le p4.le p3'.le p4'.le
          (abs_le.mpr ⟨by linarith, by linarith⟩) hS2 (abs_le.mpr ⟨by linarith, by linarith⟩)
        exact ⟨d1.trans (by linarith), d2⟩
    · right
      refine ⟨k, ?_⟩
      rw [stdCircZone]
      apply image_mono; apply image_mono
      rintro _ ⟨p, ⟨⟨p1, p2⟩, p3, p4⟩, rfl⟩
      obtain ⟨f1, f2⟩ := hfst t p p1.le p2.le p3.le p4.le
      obtain ⟨s1, s2⟩ := hsnd p p3.le p4.le
      rw [zoneZ, mem_prod, mem_Icc, mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · linarith only [f1, k1]
      · linarith only [f2, k2, hε₀a]
      · linarith only [s1]
      · linarith only [s2]
  · -- small zones
    intro t
    rw [stdCircZone, himg]
    apply hsmall
    · rintro _ ⟨p, ⟨-, p3, p4⟩, rfl⟩
      obtain ⟨s1, s2⟩ := hsnd p p3 p4
      constructor <;> linarith
    · rintro _ ⟨p, ⟨⟨p1, p2⟩, p3, p4⟩, rfl⟩ _ ⟨p', ⟨⟨p1', p2'⟩, p3', p4'⟩, rfl⟩
      have z1 : g p.1 = P (t + 1) := Ramp.phat_zone P p1 p2
      have z2 : g p'.1 = P (t + 1) := Ramp.phat_zone P p1' p2'
      obtain ⟨d1, d2⟩ := hdiff p p' 0 p3 p4 p3' p4' (by rw [z1, z2]; simp) (by norm_num)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
      exact ⟨d1.trans (by linarith), d2⟩

end HPC.BJ59
