import HPC.Moore.Borsuk

/-!
# Batch 155: a non-unicoherent plane continuum separates the plane (Moore 1962, Theorem 22, p. 175)

`separatesPlane_of_not_isPreconnected_inter`: if `A`, `B` are compact and preconnected and `A ∩ B` is
not preconnected, then `(A ∪ B)ᶜ` is not connected.

Proof (Eilenberg's argument, as in `plane_unicoherent`, with Borsuk's theorem in place of the
logarithm on the whole plane): split `A ∩ B = P ∪ Q`, take `φ` with `φ = 0` on `P` and `1` on `Q`, and
let `f = exp (2πiφ)` on `A`, `f = 1` on `B`. If `(A ∪ B)ᶜ` were connected, `f` would have a
logarithm on `A ∪ B` (`borsuk_exists_log`, batch 146); comparing it with `2πiφ` on `A` and with a
constant on `B` at a point of `P` and a point of `Q` gives `0 = 1`.
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane HPC.Moore

theorem separatesPlane_of_not_isPreconnected_inter {A B : Set Pt} (hA : IsCompact A)
    (hB : IsCompact B) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    (hcon : ¬ IsPreconnected (A ∩ B)) : ¬ IsConnected (A ∪ B)ᶜ := by
  intro hW
  obtain ⟨P, Q, hP, hQ, hPQ, hdisj, ⟨p, hp⟩, ⟨q, hq⟩⟩ :=
    exists_closed_pieces_of_not_isPreconnected (hA.isClosed.inter hB.isClosed) hcon
  obtain ⟨φ, hφP, hφQ, -⟩ := exists_continuous_zero_one_of_isClosed hP hQ hdisj
  have hHKPQ : ∀ x, x ∈ A → x ∈ B → x ∈ P ∪ Q := fun x hxH hxK => by rw [hPQ]; exact ⟨hxH, hxK⟩
  set e : Pt → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ)) with he
  have he1 : ∀ x, x ∈ A → x ∈ B → e x = 1 := fun x hxH hxK => by
    rcases hHKPQ x hxH hxK with h | h
    · simp [he, hφP h]
    · simp only [he, hφQ h, Pi.one_apply, Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I
  classical
  set g0 : Pt → ℂ := A.piecewise e (fun _ => 1) with hg0
  have hg0K : ∀ x ∈ B, g0 x = 1 := fun x hx => by
    by_cases hxH : x ∈ A
    · rw [hg0, Set.piecewise_eq_of_mem _ _ _ hxH]; exact he1 x hxH hx
    · rw [hg0, Set.piecewise_eq_of_notMem _ _ _ hxH]
  have hg0H : ∀ x ∈ A, g0 x = e x := fun x hx => by
    rw [hg0, Set.piecewise_eq_of_mem _ _ _ hx]
  have hg0c : ContinuousOn g0 (A ∪ B) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA.isClosed hB.isClosed
    · exact (by fun_prop : Continuous e).continuousOn.congr hg0H
    · exact continuousOn_const.congr hg0K
  have hg0ne : ∀ x ∈ A ∪ B, g0 x ≠ 0 := fun x hx => by
    by_cases hxH : x ∈ A
    · rw [hg0H x hxH]; exact Complex.exp_ne_zero _
    · rw [hg0K x (hx.resolve_left hxH)]; exact one_ne_zero
  obtain ⟨G, hGc, hG'⟩ := borsuk_exists_log (hA.union hB) hW hg0c hg0ne
  set u : Pt → ℝ := fun x => (G x).im / (2 * Real.pi) with hu
  have huc : ContinuousOn u (A ∪ B) := (Complex.continuous_im.comp_continuousOn hGc).div_const _
  have hK_int : ∀ x ∈ B, ∃ n : ℤ, u x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ((hG' x (Or.inr hx)).trans (hg0K x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hH_int : ∀ x ∈ A, ∃ n : ℤ, u x - φ x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ((hG' x (Or.inl hx)).trans (hg0H x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hpHK : p ∈ A ∩ B := by rw [← hPQ]; exact Or.inl hp
  have hqHK : q ∈ A ∩ B := by rw [← hPQ]; exact Or.inr hq
  have e1 := eq_of_isPreconnected_int_valued hBc (huc.mono subset_union_right) hK_int hpHK.2
    hqHK.2
  have e2 := eq_of_isPreconnected_int_valued (f := fun x => u x - φ x) hAc
    ((huc.mono subset_union_left).sub φ.continuous.continuousOn) hH_int hpHK.1 hqHK.1
  simp only [hφP hp, hφQ hq, Pi.zero_apply, Pi.one_apply] at e2
  linarith

end HPC.Hagopian
