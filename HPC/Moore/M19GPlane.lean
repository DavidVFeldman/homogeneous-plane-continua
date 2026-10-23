import HPC.Moore.M19GCollar
import HPC.Moore.M19F

/-!
# Moore 1919: a space satisfying Axioms 1–8 is a number plane (batch 144, item C)

Theorem F gives closed curves `Jₙ` with `Jₙ ∪ Iₙ ⊆ Iₙ₊₁` and `⋃ Iₙ = S`. The disc `J₀ ∪ I₀` is a
square (`exists_square_of_interior`), each annulus `Jₙ₊₁ ∪ Iₙ₊₁ − Iₙ` is a collar of `Jₙ`
(`exists_collar`), and the radial extensions are pasted (`HPC.Sq.plane_of_collars`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Plane

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **A space satisfying Axioms 1–8 is homeomorphic to `ℝ²`**, by a homeomorphism sending the
squares `[-(n+1), n+1]²` onto the discs `Jₙ ∪ Iₙ` of an exhaustion as in Theorem F.
*Axioms used: 1–8.* -/
theorem m19_plane_exhaust :
    ∃ (Jn In : ℕ → Set S) (e : @Homeomorph (ℝ × ℝ) S _ σ.topology),
      (∀ n, σ.IsInteriorOf (Jn n) (In n)) ∧ (∀ P, ∃ n, P ∈ In n) ∧
      (∀ n, Jn n ∪ In n ⊆ In (n + 1)) ∧
      ∀ n : ℕ, e '' HPC.Sq.Bsq ((n : ℝ) + 1) = Jn n ∪ In n := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨Jn, In, hI, hcov, hsub⟩ := m19_theoremF_proof h1 h3 h2 h4 h5 h6 h7 h8
  have J := fun n => jordan h1 h2 h3 h4 h51 h7 (hI n)
  obtain ⟨f, hf, hfr, hbd⟩ := exists_square_of_interior h1 h2 h3 h4 h5 h6 h7 h8 (hI 0)
  obtain ⟨e, Ψ, hΨ, he⟩ := HPC.Sq.plane_of_collars Jn In (fun n => (J n).2.2.2.2.2.2.2.2.2.1.symm)
    hsub (fun n => (J n).1) hcov (HPC.Sq.stage_of_square f hf hfr hbd)
    (fun n => exists_collar h1 h2 h3 h4 h5 h6 h7 h8 (hI n) (hI (n + 1)) (hsub n))
  refine ⟨Jn, In, e, hI, hcov, hsub, fun n => ?_⟩
  rw [← (hΨ n).2.2.1]
  exact image_congr (he n)

/-- **Main theorem** (Moore 1919). A space satisfying Axioms 1–8 of F.A. is homeomorphic, in the
region topology, to `ℝ²`. *Axioms used: 1–8.* -/
theorem m19_plane_proof : Nonempty (@Homeomorph S (ℝ × ℝ) σ.topology _) := by
  obtain ⟨-, -, e, -⟩ := m19_plane_exhaust h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨@Homeomorph.symm _ _ _ σ.topology e⟩

end Plane

end HPC.Moore

namespace HPC.Moore

open Set Topology Gen Metric

variable {S : Type*} {σ : Space S}

section AnnulusSquare

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The annulus lemma, square form.** If `J₂` encloses `J₁` and `Ψ` embeds the square of radius
`r` onto `J₁ ∪ I₁`, its boundary going onto `J₁`, then `Ψ` extends to an embedding `Ψ'` of the
square of radius `r + 1` onto `J₂ ∪ I₂`, its boundary going onto `J₂`, which maps the square annulus
`r ≤ ‖p‖ ≤ r + 1` onto the closed annulus `J₂ ∪ I₂ − I₁`. *Axioms used: 1–8.* -/
theorem annulus_square {J₁ I₁ J₂ I₂ : Set S} (hI₁ : σ.IsInteriorOf J₁ I₁)
    (hI₂ : σ.IsInteriorOf J₂ I₂) (hsub : J₁ ∪ I₁ ⊆ I₂) {r : ℝ} (hr : 0 < r) {Ψ : ℝ × ℝ → S}
    (hΨc : @ContinuousOn _ _ _ σ.topology Ψ (closedBall 0 r)) (hΨi : InjOn Ψ (closedBall 0 r))
    (hΨimg : Ψ '' closedBall 0 r = J₁ ∪ I₁) (hΨsph : Ψ '' sphere 0 r = J₁) :
    ∃ Ψ' : ℝ × ℝ → S, @ContinuousOn _ _ _ σ.topology Ψ' (closedBall 0 (r + 1)) ∧
      InjOn Ψ' (closedBall 0 (r + 1)) ∧ EqOn Ψ' Ψ (closedBall 0 r) ∧
      Ψ' '' closedBall 0 (r + 1) = J₂ ∪ I₂ ∧ Ψ' '' sphere 0 (r + 1) = J₂ ∧
      Ψ' '' {p | r ≤ ‖p‖ ∧ ‖p‖ ≤ r + 1} = (J₂ ∪ I₂) \ I₁ := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, -, -, -, -, -, -, hIJ₁, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₁
  obtain ⟨H, hH⟩ := exists_collar h1 h2 h3 h4 h5 h6 h7 h8 hI₁ hI₂ hsub
  have hID : I₁ ⊆ J₂ ∪ I₂ := fun x hx => Or.inr (hsub (Or.inr hx))
  obtain ⟨Ψ', ⟨hc, hi, -, hsph⟩, heq, himg⟩ :=
    HPC.Sq.radial_step hr ⟨hΨc, hΨi, hΨimg, hΨsph⟩ hID hH
  have hB : ∀ (p : ℝ × ℝ) (t : ℝ), p ∈ closedBall (0 : ℝ × ℝ) t ↔ ‖p‖ ≤ t := by
    intro p t; rw [mem_closedBall, dist_zero_right]
  -- the open square goes onto `I₁`
  have inner : ∀ p : ℝ × ℝ, ‖p‖ ≤ r → (Ψ p ∈ I₁ ↔ ‖p‖ < r) := by
    intro p hp
    constructor
    · intro hpI
      refine lt_of_le_of_ne hp fun e => ?_
      have : Ψ p ∈ J₁ := hΨsph ▸ mem_image_of_mem Ψ (by rw [mem_sphere, dist_zero_right]; exact e)
      exact disjoint_left.mp hIJ₁ hpI this
    · intro hlt
      have : Ψ p ∈ J₁ ∪ I₁ := hΨimg ▸ mem_image_of_mem Ψ ((hB p r).mpr hp)
      refine this.resolve_left fun hJ => ?_
      rw [← hΨsph] at hJ
      obtain ⟨q, hq, hqp⟩ := hJ
      have := hΨi (sphere_subset_closedBall hq) ((hB p r).mpr hp) hqp
      rw [mem_sphere, dist_zero_right] at hq
      rw [← this, hq] at hlt
      exact lt_irrefl _ hlt
  refine ⟨Ψ', hc, hi, heq, himg, hsph, ?_⟩
  apply subset_antisymm
  · rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    refine ⟨himg ▸ mem_image_of_mem Ψ' ((hB p _).mpr hp2), fun hpI => ?_⟩
    have : Ψ' p ∈ J₁ ∪ I₁ := Or.inr hpI
    rw [← hΨimg] at this
    obtain ⟨q, hq, hqp⟩ := this
    have hqI : Ψ q ∈ I₁ := hqp ▸ hpI
    have hlt := (inner q ((hB q r).mp hq)).mp hqI
    have hqp' : Ψ' q = Ψ' p := (heq hq).trans hqp
    have hpq := hi (closedBall_subset_closedBall (by linarith) hq) ((hB p _).mpr hp2) hqp'
    rw [hpq] at hlt
    linarith
  · rintro x ⟨hxD, hxI⟩
    rw [← himg] at hxD
    obtain ⟨p, hp, rfl⟩ := hxD
    refine ⟨p, ⟨?_, (hB p _).mp hp⟩, rfl⟩
    by_contra hlt
    push_neg at hlt
    exact hxI (heq ((hB p r).mpr hlt.le) ▸ (inner p hlt.le).mpr hlt)

end AnnulusSquare

end HPC.Moore
