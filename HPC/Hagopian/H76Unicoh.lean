import HPC.Moore.Borsuk
import HPC.Plane.Fugate66BMiller
import HPC.Hagopian.H76ChainSep

/-!
# Batch 178, §5: unicoherence of the plane in separation form; separation in a domain

* `separatesPlane_union_of_inter_disconnected_aux`: if `A`, `B` are compact and connected and
  `A ∩ B = K₁ ∪ K₂` with `K₁`, `K₂` closed, disjoint and nonempty, then `A ∪ B` separates the plane.
  Route (commission 178 §5): `f = exp(πiφ)` on `A`, `exp(−πiφ)` on `B`, with `φ` an Urysohn
  function (`0` on `K₁`, `1` on `K₂`); if `(A ∪ B)ᶜ` were connected, `borsuk_exists_log` would give
  a logarithm `g` of `f` on `A ∪ B`, and the integer-valued functions `(g − πiφ)/2πi` on `A`,
  `(g + πiφ)/2πi` on `B` would be constant, equal at a point of `K₁` and differing by `1` at a point
  of `K₂`.
* `sepIn_iff_separatesPts_union_aux`: for `Y` disjoint from the open `O` and containing `Fr O`,
  separation in `O` by `X` is separation in the plane by `X ∪ Y` (for points of `O − X`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane

/-- **Two continua with disconnected intersection separate the plane.** -/
theorem separatesPlane_union_of_inter_disconnected_aux {A B K₁ K₂ : Set Pt} (hA : IsCompact A)
    (hAc : IsConnected A) (hB : IsCompact B) (hBc : IsConnected B) (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hAB : A ∩ B = K₁ ∪ K₂) (hK : Disjoint K₁ K₂) (hK₁n : K₁.Nonempty)
    (hK₂n : K₂.Nonempty) : SeparatesPlane (A ∪ B) := by
  intro hconn
  obtain ⟨φ, hφ1, hφ2, -⟩ := exists_continuous_zero_one_of_isClosed hK₁ hK₂ hK
  have hφ01 : ∀ z ∈ A ∩ B, φ z = 0 ∨ φ z = 1 := by
    intro z hz
    rw [hAB] at hz
    rcases hz with h | h
    · exact Or.inl (hφ1 h)
    · exact Or.inr (hφ2 h)
  set fA : Pt → ℂ := fun z => Complex.exp (Real.pi * Complex.I * (φ z : ℂ)) with hfA
  set fB : Pt → ℂ := fun z => Complex.exp (-(Real.pi * Complex.I * (φ z : ℂ))) with hfB
  have hAgree : ∀ z ∈ A ∩ B, fA z = fB z := by
    intro z hz
    rcases hφ01 z hz with h | h
    · simp [hfA, hfB, h]
    · simp only [hfA, hfB, h, Complex.ofReal_one, mul_one]
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  classical
  set f : Pt → ℂ := A.piecewise fA fB with hf
  have hfAeq : ∀ z ∈ A, f z = fA z := fun z hz => by simp [hf, hz]
  have hfBeq : ∀ z ∈ B, f z = fB z := fun z hz => by
    by_cases hzA : z ∈ A
    · rw [hfAeq z hzA]; exact hAgree z ⟨hzA, hz⟩
    · simp [hf, hzA]
  have hfAc : Continuous fA := by fun_prop
  have hfBc : Continuous fB := by fun_prop
  have hfc : ContinuousOn f (A ∪ B) :=
    ContinuousOn.union_of_isClosed (hfAc.continuousOn.congr hfAeq)
      (hfBc.continuousOn.congr hfBeq) hA.isClosed hB.isClosed
  have hne : ∀ z ∈ A ∪ B, f z ≠ 0 := by
    rintro z (hz | hz)
    · rw [hfAeq z hz]; exact Complex.exp_ne_zero _
    · rw [hfBeq z hz]; exact Complex.exp_ne_zero _
  obtain ⟨g, hgc, hge⟩ := HPC.Moore.borsuk_exists_log (hA.union hB) hconn hfc hne
  set uA : Pt → ℝ := fun z => ((g z).im - Real.pi * φ z) / (2 * Real.pi) with huA
  set uB : Pt → ℝ := fun z => ((g z).im + Real.pi * φ z) / (2 * Real.pi) with huB
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have huAint : ∀ z ∈ A, ∃ n : ℤ, uA z = n := by
    intro z hz
    have h := (hge z (Or.inl hz)).trans (hfAeq z hz)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat] at him
    simp only [huA]
    field_simp
    linarith
  have huBint : ∀ z ∈ B, ∃ n : ℤ, uB z = n := by
    intro z hz
    have h := (hge z (Or.inr hz)).trans (hfBeq z hz)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat] at him
    simp only [huB]
    field_simp
    linarith
  have hgim : ContinuousOn (fun z => (g z).im) (A ∪ B) :=
    Complex.continuous_im.comp_continuousOn hgc
  have huAc : ContinuousOn uA A :=
    ((hgim.mono subset_union_left).sub (continuous_const.mul φ.continuous).continuousOn).div_const _
  have huBc : ContinuousOn uB B :=
    ((hgim.mono subset_union_right).add (continuous_const.mul φ.continuous).continuousOn).div_const _
  obtain ⟨p, hp⟩ := hK₁n
  obtain ⟨q, hq⟩ := hK₂n
  have hpAB : p ∈ A ∩ B := by rw [hAB]; exact Or.inl hp
  have hqAB : q ∈ A ∩ B := by rw [hAB]; exact Or.inr hq
  have e1 := eq_of_isPreconnected_int_valued hAc.isPreconnected huAc huAint hpAB.1 hqAB.1
  have e2 := eq_of_isPreconnected_int_valued hBc.isPreconnected huBc huBint hpAB.2 hqAB.2
  simp only [huA, huB, hφ1 hp, hφ2 hq, Pi.zero_apply, Pi.one_apply, mul_zero, mul_one,
    sub_zero, add_zero] at e1 e2
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  rw [div_left_inj' h2pi] at e1 e2
  linarith [Real.pi_pos]

/-- A connected set missing the frontier of an open set `O` and meeting `O` lies in `O`. -/
theorem subset_of_preconnected_of_frontier {O C : Set Pt} (hO : IsOpen O)
    (hC : IsPreconnected C) (hCf : Disjoint C (frontier O)) (hCO : (C ∩ O).Nonempty) :
    C ⊆ O := by
  refine hC.subset_left_of_subset_union hO isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) ?_ hCO
  intro z hz
  by_cases hzO : z ∈ O
  · exact Or.inl hzO
  · refine Or.inr fun hzc => disjoint_left.1 hCf hz ?_
    rw [frontier, hO.interior_eq]
    exact ⟨hzc, hzO⟩

/-- **Separation in a domain is separation in the plane with the frontier continuum adjoined**
(commission 178 §3a step 3, §5). -/
theorem sepIn_iff_separatesPts_union_aux {O X Y : Set Pt} (hO : IsOpen O) (hYO : Disjoint Y O)
    (hfr : frontier O ⊆ Y) {p q : Pt} (hp : p ∈ O \ X) (hq : q ∈ O \ X) :
    SepIn O X p q ↔ SeparatesPts (X ∪ Y) p q := by
  have hpY : p ∉ Y := fun h => disjoint_left.1 hYO h hp.1
  have hqY : q ∉ Y := fun h => disjoint_left.1 hYO h hq.1
  have hpXY : p ∉ X ∪ Y := fun h => h.elim hp.2 hpY
  have hqXY : q ∉ X ∪ Y := fun h => h.elim hq.2 hqY
  constructor
  · rintro ⟨-, -, hS⟩
    refine ⟨hpXY, hqXY, fun hqC => ?_⟩
    set C := connectedComponentIn (X ∪ Y)ᶜ p
    have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsub : C ⊆ (X ∪ Y)ᶜ := connectedComponentIn_subset _ _
    have hpC : p ∈ C := mem_connectedComponentIn hpXY
    have hCO : C ⊆ O := subset_of_preconnected_of_frontier hO hCc
      (disjoint_left.2 fun z hz hzf => hCsub hz (Or.inr (hfr hzf))) ⟨p, hpC, hp.1⟩
    exact hS C hCc (fun z hz => ⟨hCO hz, fun h => hCsub hz (Or.inl h)⟩) hpC hqC
  · rintro ⟨-, -, hsep⟩
    refine ⟨hp, hq, fun S hS hSO hpS hqS => hsep ?_⟩
    have : S ⊆ (X ∪ Y)ᶜ := fun z hz h =>
      h.elim (hSO hz).2 fun hY => disjoint_left.1 hYO hY (hSO hz).1
    exact hS.subset_connectedComponentIn hpS this hqS

end HPC.Hagopian
