import HPC.Hagopian.Hagopian76T

/-!
# Batch 176, item A: positions by `ε₃`

Commission 176 §1.A: points of `K` lie over the abscissa `11/22 = 1/2`; `π` is uniformly continuous
on `M`, and the collar `F` is an embedding of the closed rectangle; so for `ε₃` small, every point
within `ε₃` of a point of `M` over the abscissa `1/2` (for instance its image under an
`ε₃`-homeomorphism) lies over abscissae in `(3/8, 5/8)`. Shrinking `ε₃` keeps Property 2.

* `collar_abscissa_sep` — on a compact set where `F` is an embedding, `F`-close points have close
  abscissae;
* `pi_abscissa_close` — `M`-close points have close abscissae under `π` and `F`;
* `Property2At`, `Property2At.mono` — Property 2 at a given `ε₃`, inherited by smaller `ε₃`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- On a compact set `R` on which `F` is an embedding, points with `F`-images closer than some
`η > 0` have abscissae closer than `μ`. -/
theorem collar_abscissa_sep {F : ℝ × ℝ → Pt} {R : Set (ℝ × ℝ)} (hR : IsCompact R)
    (hF : IsEmbedding (R.restrict F)) {μ : ℝ} (hμ : 0 < μ) :
    ∃ η > 0, ∀ z ∈ R, ∀ z' ∈ R, dist (F z) (F z') < η → |z.1 - z'.1| < μ := by
  have hFc : ContinuousOn F R := continuousOn_iff_continuous_restrict.2 hF.continuous
  have hinj : InjOn F R := fun a ha b hb e => by
    have := hF.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) e
    simpa using this
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (R ×ˢ R) ∩ {w | μ ≤ |w.1.1 - w.2.1|}
  have hS : IsCompact S := (hR.prod hR).inter_right
    (isClosed_le continuous_const ((continuous_fst.comp continuous_fst).sub
      (continuous_fst.comp continuous_snd)).abs)
  have hg : ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) => dist (F w.1) (F w.2)) S :=
    continuous_dist.comp_continuousOn
      ((hFc.comp continuous_fst.continuousOn (fun _ hw => hw.1.1)).prodMk
        (hFc.comp continuous_snd.continuousOn (fun _ hw => hw.1.2)))
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz z' hz' _ => ?_⟩
    by_contra hc
    have : (z, z') ∈ S := ⟨⟨hz, hz'⟩, not_lt.1 hc⟩
    rw [hSe] at this; exact this
  obtain ⟨w₀, hw₀, hmin⟩ := hS.exists_isMinOn hSne hg
  have hpos : 0 < dist (F w₀.1) (F w₀.2) := by
    apply dist_pos.2
    intro e
    have := hinj hw₀.1.1 hw₀.1.2 e
    have h2 := hw₀.2
    simp only [mem_setOf_eq, this, sub_self, abs_zero] at h2
    linarith
  refine ⟨_, hpos, fun z hz z' hz' hd => ?_⟩
  by_contra hc
  have : (z, z') ∈ S := ⟨⟨hz, hz'⟩, not_lt.1 hc⟩
  have := hmin this
  simp only [mem_setOf_eq] at this
  linarith

/-- **Close points of `M` lie over close abscissae.** For `M` compact, `π` continuous and `F` an
embedding of the compact `R`: for every `μ > 0` there is `δ > 0` such that points `y`, `w` of `M`
within `δ` of each other, over `F(z)` and `F(z′)` with `z, z′ ∈ R`, have `|z₁ − z′₁| < μ`. -/
theorem pi_abscissa_close {M : Set Pt} [CompactSpace M] {π : Pt → Pt} (hπ : Continuous π)
    {F : ℝ × ℝ → Pt} {R : Set (ℝ × ℝ)} (hR : IsCompact R) (hF : IsEmbedding (R.restrict F))
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ δ > 0, ∀ y w : M, ∀ z ∈ R, ∀ z' ∈ R, π (y : Pt) = F z → π (w : Pt) = F z' →
      dist (y : Pt) w < δ → |z.1 - z'.1| < μ := by
  obtain ⟨η, hη, hsep⟩ := collar_abscissa_sep hR hF hμ
  have hu : UniformContinuous (fun y : M => π y) :=
    CompactSpace.uniformContinuous_of_continuous (hπ.comp continuous_subtype_val)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hu η hη
  refine ⟨δ, hδ, fun y w z hz z' hz' hy hw hd => hsep z hz z' hz' ?_⟩
  rw [← hy, ← hw]
  exact hδu (by simpa [Subtype.dist_eq] using hd)

section Prop2

variable {M : Set Pt}

/-- **Property 2 at `ε₃`** (p. 346), the conclusion of `hagopian76_property2`: for every
`ε₃`-homeomorphism `h`, every continuum `H` essential to `h[R(E)]` with end sets within `ε₃` of each
other and an element of its decomposition farther than `ε₂` from its first end set comes within
`ε₂` of each point of `R(E)`. -/
def Property2At {E : Set M} (k : E → unitInterval) (ε₂ ε₃ : ℝ) : Prop :=
  ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₃) →
    ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
      (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < ε₃) →
      (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε₂ < dist t w) →
      ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε₂

/-- **Shrinking `ε₃` keeps Property 2** (commission 176 §1.A: "both its hypothesis on `h` and its
condition `ρ(T, V) < ε₃` become stronger"). -/
theorem Property2At.mono {E : Set M} {k : E → unitInterval} {ε₂ ε₃ ε₃' : ℝ}
    (h : Property2At k ε₂ ε₃) (hle : ε₃' ≤ ε₃) : Property2At k ε₂ ε₃' :=
  fun g hg H hH d hd ⟨t, ht, v, hv, htv⟩ hU =>
    h g (fun w => (hg w).trans_le hle) H hH d hd ⟨t, ht, v, hv, htv.trans_le hle⟩ hU

end Prop2

end HPC.Hagopian
