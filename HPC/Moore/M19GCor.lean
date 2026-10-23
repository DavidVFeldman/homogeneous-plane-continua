import HPC.Moore.M19GPlane

/-!
# Moore 1919: Theorem G and the final paragraph as corollaries (batch 144, item D)

From a homeomorphism `h : S ≃ₜ ℝ²` (`m19_plane_proof`):

* **Theorem G** (`theoremG_of_homeomorph`): `G₁` is the set of images of the horizontal lines and
  `G₂` the set of images of the vertical lines.
* **Open curves in F.A.'s sense** (p. 159, `Space.IsOpenCurveFA`): the image of a closed embedding
  of `ℝ` is one (`isOpenCurveFA_of_isClosedEmbedding`).
* **The final paragraph** (`final_of_homeomorph`): Moore's sequential limits are the limits of the
  region topology (`isSeqLimit_iff_tendsto`), which `h` carries to limits in `ℝ²`.
-/

namespace HPC.Moore

open Set Topology Filter Gen

variable {S : Type*} {σ : Space S}

/-- An *open curve* in the sense of F.A., p. 159: *"a closed, connected set of points `M` such that
if `P` is a point of `M` then `M − P` is the sum of two mutually exclusive connected point-sets,
neither of which contains a limit point of the other one"*. The two point-sets are taken nonempty
(as in Moore's definition of connectedness, `Space.IsConn`). -/
def Space.IsOpenCurveFA (σ : Space S) (M : Set S) : Prop :=
  σ.IsClosedM M ∧ σ.IsConn M ∧ ∀ P ∈ M, ∃ A B : Set S, A ∪ B = M \ {P} ∧ Disjoint A B ∧
    A.Nonempty ∧ B.Nonempty ∧ σ.IsConn A ∧ σ.IsConn B ∧ (∀ x ∈ A, ¬ σ.IsLimitPt x B) ∧
    (∀ x ∈ B, ¬ σ.IsLimitPt x A)

section Cor

variable (h1 : σ.Axiom1)
include h1

/-- **The image of a closed embedding of `ℝ` is an open curve in F.A.'s sense.** *Axioms used:
1.* -/
theorem isOpenCurveFA_of_isClosedEmbedding {e : ℝ → S} (he : @IsClosedEmbedding _ _ _ σ.topology e) :
    σ.IsOpenCurveFA (range e) := by
  letI := σ.topology
  have limit : ∀ {x : S} {T : Set ℝ}, σ.IsLimitPt x (e '' T) → x ∈ e '' closure T := by
    intro x T hx
    have hx' : x ∈ closure (e '' T) := closure_mono diff_subset (mem_closure_iff_clusterPt.mpr
      (accPt_principal_iff_clusterPt.mp ((isLimitPt_iff h1).mp hx)))
    rwa [he.closure_image_eq] at hx'
  refine ⟨(isClosedM_iff h1).mpr he.isClosed_range, (isConn_iff h1).mpr
    (isPreconnected_range he.continuous), ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨e '' Iio t, e '' Ioi t, ?_, ?_, ⟨e (t - 1), t - 1, by simp, rfl⟩,
    ⟨e (t + 1), t + 1, by simp, rfl⟩, (isConn_iff h1).mpr
    (isPreconnected_Iio.image _ he.continuous.continuousOn), (isConn_iff h1).mpr
    (isPreconnected_Ioi.image _ he.continuous.continuousOn), ?_, ?_⟩
  · ext x
    simp only [mem_union, mem_image, mem_diff, mem_range, mem_singleton_iff, mem_Iio, mem_Ioi]
    constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨⟨s, rfl⟩, fun h => hs.ne (he.injective h)⟩
      · exact ⟨⟨s, rfl⟩, fun h => hs.ne' (he.injective h)⟩
    · rintro ⟨⟨s, rfl⟩, hs⟩
      rcases lt_trichotomy s t with h | h | h
      · exact Or.inl ⟨s, h, rfl⟩
      · exact absurd (congrArg e h) hs
      · exact Or.inr ⟨s, h, rfl⟩
  · rw [disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', e'⟩
    have := he.injective e'
    rw [mem_Iio] at hs; rw [mem_Ioi] at hs'
    linarith
  · rintro _ ⟨s, hs, rfl⟩ hl
    obtain ⟨s', hs', e'⟩ := limit hl
    rw [closure_Ioi, mem_Ici] at hs'
    rw [mem_Iio] at hs
    have := he.injective e'
    linarith
  · rintro _ ⟨s, hs, rfl⟩ hl
    obtain ⟨s', hs', e'⟩ := limit hl
    rw [closure_Iio, mem_Iic] at hs'
    rw [mem_Ioi] at hs
    have := he.injective e'
    linarith

/-- Moore's sequential limit points are the limits of the region topology. *Axioms used: 1.* -/
theorem isSeqLimit_iff_tendsto {P : S} {u : ℕ → S} :
    σ.IsSeqLimit P u ↔ Tendsto u atTop (@nhds S σ.topology P) := by
  letI := σ.topology
  rw [(isTopologicalBasis_region h1).nhds_hasBasis.tendsto_right_iff]
  constructor
  · rintro h R ⟨hR, hPR⟩
    obtain ⟨δ, hδ⟩ := h R hR hPR
    exact eventually_atTop.mpr ⟨δ + 1, fun n hn => hδ n (by omega)⟩
  · intro h R hR hPR
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h R ⟨hR, hPR⟩)
    exact ⟨N, fun n hn => hN n hn.le⟩

omit h1 in
/-- **Theorem G from a homeomorphism with the plane.** -/
theorem theoremG_of_homeomorph (h : @Homeomorph S (ℝ × ℝ) σ.topology _) :
    ∃ G₁ G₂ : Set (Set S),
      (∀ k ∈ G₁ ∪ G₂, ∃ e : ℝ → S, @IsClosedEmbedding _ _ _ σ.topology e ∧ range e = k) ∧
      (∀ P, (∃! k, k ∈ G₁ ∧ P ∈ k) ∧ (∃! k, k ∈ G₂ ∧ P ∈ k)) ∧
      (∀ k ∈ G₁, ∀ l ∈ G₂, ∃! P, P ∈ k ∩ l) := by
  letI := σ.topology
  set G₁ : Set (Set S) := range fun c : ℝ => h.symm '' {p | p.2 = c}
  set G₂ : Set (Set S) := range fun c : ℝ => h.symm '' {p | p.1 = c}
  have mem₁ : ∀ {P : S} {c : ℝ}, P ∈ h.symm '' {p : ℝ × ℝ | p.2 = c} ↔ (h P).2 = c := by
    intro P c
    constructor
    · rintro ⟨p, hp, rfl⟩; rw [h.apply_symm_apply]; exact hp
    · intro hc; exact ⟨h P, hc, h.symm_apply_apply P⟩
  have mem₂ : ∀ {P : S} {c : ℝ}, P ∈ h.symm '' {p : ℝ × ℝ | p.1 = c} ↔ (h P).1 = c := by
    intro P c
    constructor
    · rintro ⟨p, hp, rfl⟩; rw [h.apply_symm_apply]; exact hp
    · intro hc; exact ⟨h P, hc, h.symm_apply_apply P⟩
  have closedEmb : ∀ {g : ℝ → ℝ × ℝ}, IsClosedEmbedding g → IsClosedEmbedding (h.symm ∘ g) :=
    fun hg => h.symm.isClosedEmbedding.comp hg
  refine ⟨G₁, G₂, ?_, fun P => ⟨?_, ?_⟩, ?_⟩
  · rintro k (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨h.symm ∘ fun x => (x, c), closedEmb ⟨isEmbedding_prodMkLeft c, ?_⟩, ?_⟩
      · have : range (fun x : ℝ => (x, c)) = univ ×ˢ {c} := by
          ext ⟨a, b⟩; simp [eq_comm]
        rw [this]; exact isClosed_univ.prod isClosed_singleton
      · rw [range_comp]; congr 1; ext ⟨a, b⟩; simp [eq_comm]
    · refine ⟨h.symm ∘ fun y => (c, y), closedEmb ⟨isEmbedding_prodMkRight c, ?_⟩, ?_⟩
      · have : range (fun y : ℝ => (c, y)) = {c} ×ˢ univ := by
          ext ⟨a, b⟩; simp [eq_comm]
        rw [this]; exact isClosed_singleton.prod isClosed_univ
      · rw [range_comp]; congr 1; ext ⟨a, b⟩; simp [eq_comm]
  · refine ⟨_, ⟨⟨(h P).2, rfl⟩, mem₁.mpr rfl⟩, ?_⟩
    rintro k ⟨⟨c, rfl⟩, hk⟩
    rw [mem₁.mp hk]
  · refine ⟨_, ⟨⟨(h P).1, rfl⟩, mem₂.mpr rfl⟩, ?_⟩
    rintro k ⟨⟨c, rfl⟩, hk⟩
    rw [mem₂.mp hk]
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    refine ⟨h.symm (d, c), ⟨mem₁.mpr (by simp), mem₂.mpr (by simp)⟩, ?_⟩
    rintro P ⟨hP₁, hP₂⟩
    rw [← mem₁.mp hP₁, ← mem₂.mp hP₂, h.symm_apply_apply]

/-- **The final paragraph from a homeomorphism with the plane.** *Axioms used: 1.* -/
theorem final_of_homeomorph (h : @Homeomorph S (ℝ × ℝ) σ.topology _) :
    ∃ e : S ≃ ℝ × ℝ, ∀ (P : S) (u : ℕ → S),
      σ.IsSeqLimit P u ↔ Tendsto (fun n => e (u n)) atTop (𝓝 (e P)) := by
  letI := σ.topology
  refine ⟨h.toEquiv, fun P u => ?_⟩
  rw [isSeqLimit_iff_tendsto h1]
  constructor
  · intro hu; exact (h.continuous.tendsto P).comp hu
  · intro hu
    have := (h.symm.continuous.tendsto (h P)).comp hu
    simpa [Function.comp_def] using this

end Cor

end HPC.Moore
