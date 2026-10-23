import HPC.Hagopian.Hagopian76Z

/-!
# Batch 182, §1.1, §2.1, §3.2: the case split fails at `i = 2`; the mirror cap without the
# bottom-edge hypothesis; the closure of `F − E`

Commission 182.

* `Thm1Setup.layer_x2_eq` (§1.1, steps 1–2): for a block sequence, `F ≠ E` and
  `d⁻¹(x₂) = k⁻¹(1)`.
* `blockLayersMeetSides_false` (§1.1, the certificate): the named `Prop` `BlockLayersMeetSides` of
  batch 181 fails at `i = 2` for every set-up with blocks: `d⁻¹(x₂) = k⁻¹(1)` lies over
  `γ(1) = F(1, 0)`, which is on neither side segment.
* `Thm1Setup.segment_misses_closure_above` and `cross_strand_near_above` (§2.1): the mirror of the
  cap lemma, with no hypothesis on the bottom edge. The segment `[a, b]` meets the frontier of the
  region *above* `W` (not the region below), and that frontier misses the open bottom edge.
* `closure_G_diff_E` (§3.2): the closure of `F − E` meets `E` only in `k⁻¹(1)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section B182Last

variable {M : Set Pt}

/-- Over a surjective map, `d⁻¹[[0, a]] = d⁻¹[[0, b]]` forces `a = b`. -/
theorem layerSet_Icc_zero_inj {G : Set M} {d : G → unitInterval} (hd : Function.Surjective d)
    {a b : unitInterval} (h : layerSet d (Icc 0 a) = layerSet d (Icc 0 b)) : a = b := by
  have key : ∀ a b : unitInterval, layerSet d (Icc 0 a) = layerSet d (Icc 0 b) → a ≤ b := by
    intro a b h
    obtain ⟨g, hg⟩ := hd a
    have hmem : (g : M) ∈ layerSet d (Icc 0 b) := by
      rw [← h]; exact ⟨g, ⟨unitInterval.nonneg', hg.le⟩, rfl⟩
    obtain ⟨g', hg', hgg⟩ := hmem
    rw [Subtype.ext hgg] at hg'
    exact hg ▸ hg'.2
  exact le_antisymm (key a b h) (key b a h.symm)

variable [CompactSpace M] [ConnectedSpace M]

/-- The decomposition map `d` of `F` is onto. -/
theorem Thm1Setup.d_surjective (S : Thm1Setup M) : Function.Surjective S.D.d :=
  S.D.hG.2.1.2.1

/-- For a block sequence, `x₂ < 1`. -/
theorem Thm1Setup.IsBlocks.x2_lt_one (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : x 2 < 1 := by
  obtain ⟨hm, hmono, -, -, -, -⟩ := hx
  have h24 : x 2 < x 4 :=
    hmono ⟨by norm_num, by omega⟩ ⟨by norm_num, by omega⟩ (by norm_num)
  exact h24.trans_le unitInterval.le_one'

/-- **§1.1, step 1**: for a block sequence, `F ≠ E` (otherwise `d⁻¹((x₂, 1]) = ∅`). -/
theorem Thm1Setup.IsBlocks.G_ne_E (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : S.D.G ≠ S.E := by
  intro hGE
  obtain ⟨g, hg⟩ := S.d_surjective 1
  have hmem : (g : M) ∈ layerSet S.D.d (Icc 0 (x 2)) := by
    rw [hx.2.2.2.1]; exact (Set.ext_iff.1 hGE (g : M)).1 g.2
  obtain ⟨g', hg', hgg⟩ := hmem
  have h2 : S.D.d g ∈ Icc 0 (x 2) := Subtype.ext hgg ▸ hg'
  rw [hg] at h2
  exact absurd h2.2 (not_le.2 (Thm1Setup.IsBlocks.x2_lt_one S hx))

/-- **§1.1, step 2**: for a block sequence, `d⁻¹(x₂) = k⁻¹(1)` (`ext_layers`, then the surjectivity
of `d`). -/
theorem Thm1Setup.IsBlocks.layer_x2_eq (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : layer S.D.d (x 2) = layer S.k 1 := by
  obtain ⟨s, -, -, hW, hsE, -, -⟩ := ext_layers S.hX S.hi S.hE S.D.hG S.D.hEG S.D.hX0
    (Thm1Setup.IsBlocks.G_ne_E S hx)
  have : x 2 = s := layerSet_Icc_zero_inj S.d_surjective (hx.2.2.2.1.trans hsE.symm)
  rw [this, hW]

/-- `k⁻¹(1)` lies over `F(1, 0)`, which is on neither closed side segment (`F` is injective on the
rectangle). -/
theorem Thm1Setup.not_layerMeetsSide_of_layer_eq_one (S : Thm1Setup M) {u : unitInterval}
    (hu : layer S.D.d u = layer S.k 1) {a : ℝ} (ha : a ∈ ({3 / 22, 19 / 22} : Set ℝ)) :
    ¬ S.LayerMeetsSide u a := by
  rintro ⟨z, hz, q, ⟨hq1, hq2⟩, hqz⟩
  rw [hu] at hz
  have hz1 : S.π z = S.γ 1 := S.hγπ 1 z hz
  have hF1 : S.F (((1 : unitInterval) : ℝ), 0) = S.γ 1 := S.hF.2.1 1
  rw [mem_singleton_iff] at hq1
  have hqR : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rcases ha with ha | ha <;>
      exact ⟨⟨by rw [hq1, ha]; norm_num, by rw [hq1, ha]; norm_num⟩, by linarith [hq2.1],
        hq2.2.trans S.c₁_le_one⟩
  have h10 : ((((1 : unitInterval) : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have hqe := collar_injOn S.hF hqR h10 (by rw [hqz, hz1, hF1])
  have : q.1 = 1 := by rw [hqe]; rfl
  rw [hq1] at this
  rcases ha with ha | ha <;> rw [ha] at this <;> norm_num at this

/-- **§1.1, the certificate** (commission 182 §1.1): the case split of p. 348 fails at `i = 2`.
`d⁻¹(x₂) = d⁻¹(e) = k⁻¹(1)` lies over `γ(1) = F(1, 0)` and meets neither side segment. So the
named `Prop` `BlockLayersMeetSides` of batch 181 is false for every set-up with blocks, and
`hagopian76_theorem1_of_cases` (batch 181) is a vacuous reduction. -/
theorem blockLayersMeetSides_false (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : ¬ BlockLayersMeetSides S x m := by
  intro h
  obtain ⟨-, b, hb, hlb⟩ := h 2 le_rfl hx.1
  have e : (2 * 2 - 2 : ℕ) = 2 := rfl
  rw [e] at hlb
  exact Thm1Setup.not_layerMeetsSide_of_layer_eq_one S (Thm1Setup.IsBlocks.layer_x2_eq S hx) hb hlb

/-! ## §2.1: the mirror cap without the bottom-edge hypothesis -/

/-- **The segment misses `Cl(B(W)) − O`** (the exclusions of `cross_strand_near`, which use only
`a ∈ Mid` and `ρ(a, b) < ε₃`, not the side of `W` on which `a` lies): for a crossing piece `W` with
disjoint sides, `a ∈ Mid` and `ρ(a, b) < ε₃`, the segment `[a, b]` misses the part of the closure
of the region above `W` outside `π⁻¹[D]`. -/
theorem Thm1Setup.segment_misses_closure_above (S : Thm1Setup M) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (hab : dist a b < S.ε₃) :
    Disjoint (segment ℝ a b) (closure (S.V.above W) \ S.V.O) := by
  rw [disjoint_left]
  rintro c hc ⟨hcl, hcO⟩
  have hca : dist a c < S.ε₃ := (VFrame.dist_le_of_mem_segment hc).trans_lt hab
  have hcfr : c ∈ frontier (S.π ⁻¹' (S.F '' S.D')) := by
    refine ⟨closure_mono (fun P hP => (VFrame.above_subset W hP).1) hcl, ?_⟩
    rw [(S.hR.isOpen.preimage S.hπ.continuous).interior_eq]
    exact hcO
  have hcf := S.hπ.continuous.frontier_preimage_subset _ hcfr
  rw [mem_preimage, S.hFDf] at hcf
  have hside : ∀ q : ℝ × ℝ, q ∈ (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) →
      S.π c = S.F q → False := fun q hq hcq => by
    have := S.hε₃S a ha c ⟨q, hq, hcq.symm⟩
    linarith
  rcases hcf with ((hI | ⟨⟨t, y⟩, ⟨ht, hy⟩, hFt⟩) | ⟨q, ⟨hq1, hq2⟩, hFq⟩) | ⟨q, ⟨hq1, hq2⟩, hFq⟩
  · have := S.hε₂I a ha.1 c (Or.inr hI)
    linarith [S.hε₂₃]
  · rw [mem_singleton_iff] at hy
    subst hy
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · exact hside (t, 0) ⟨Or.inl h1.symm, le_rfl, S.c₁_pos.le⟩ hFt.symm
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · exact hside (t, 0) ⟨Or.inr h2, le_rfl, S.c₁_pos.le⟩ hFt.symm
    have hmiss := above_closure_misses_bottom S.hπ S.hπS S.hγπ S.hF (by norm_num : (0 : ℝ) < 3 / 22)
      (by norm_num : (19 / 22 : ℝ) < 1) S.c₁_le_one S.hR.sub S.exists_low
      (t₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ ⟨S.hw₂.1, S.hw₂.2.trans S.c₁_le_one⟩
      (S.hR.isOpen.preimage S.hπ.continuous) S.lowFrame_hyps.1 S.hsub S.injOn_O S.hπ.surjective
      S.lowFrame_hyps.2 hW.compact
      (hW.miss.mono_right (preimage_mono subset_union_right)) hWs
    exact disjoint_left.1 hmiss hcl ⟨(t, 0), ⟨⟨h1, h2⟩, rfl⟩, hFt⟩
  · exact hside q ⟨Or.inl hq1, hq2.1, hq2.2.trans S.r₂_le⟩ hFq.symm
  · exact hside q ⟨Or.inr hq1, hq2.1, hq2.2.trans S.s₂_le⟩ hFq.symm

/-- **§2.1, the mirror cap** (commission 182 §2.1; replaces `cross_strand_near_mirror` of batch 181,
which needed `a` to be `ε₃`-far from the bottom edge). Let `W` be a crossing piece with disjoint
sides, `a ∈ Mid` above `W`, `b` below `W`, `ρ(a, b) < ε₃`. Then `ρ(a, Cl W) < ε₃`.

*Proof:* the segment `[a, b]` is preconnected, contains `b ∈ A(W)` and `a ∈ B(W)`, and misses
`Cl(B(W)) − O` (`segment_misses_closure_above`); so it meets `Cl W`
(`VFrame.exists_mem_closure_of_preconnected`, with the roles of the endpoints exchanged). -/
theorem cross_strand_near_above (S : Thm1Setup M) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.V.above W) (hbW : b ∈ S.V.below W) (hab : dist a b < S.ε₃) :
    infDist a (closure W) < S.ε₃ := by
  obtain ⟨c, hc, hcW⟩ := VFrame.exists_mem_closure_of_preconnected hWs
    (convex_segment a b).isPreconnected (right_mem_segment ℝ a b) (left_mem_segment ℝ a b) hbW haW
    (S.segment_misses_closure_above hW hWs ha hab)
  exact ((infDist_le_dist_of_mem hcW).trans (VFrame.dist_le_of_mem_segment hc)).trans_lt hab

/-! ## §3.2: the closure of `F − E` -/

/-- **§3.2** (commission 181 §1.1, step 3; commission 182 §3.2): the closure of `F − E` meets `E`
only in `k⁻¹(1)`.

*Proof:* if `F = E` there is nothing to show. Otherwise `ext_layers` gives `s` with
`d⁻¹[[0, s]] = E` and `d⁻¹(s) = k⁻¹(1)`. Then `F − E ⊆ d⁻¹[[s, 1]]`, which is closed in the plane,
and a point of `d⁻¹[[s, 1]] ∩ E = d⁻¹[[s, 1]] ∩ d⁻¹[[0, s]]` is in `d⁻¹(s)`. -/
theorem closure_G_diff_E (S : Thm1Setup M) :
    closure (toPt S.D.G \ toPt S.E) ∩ toPt S.E ⊆ toPt (layer S.k 1) := by
  by_cases hne : S.D.G = S.E
  · rw [hne, diff_self, closure_empty, empty_inter]; exact empty_subset _
  obtain ⟨s, -, -, hW, hsE, -, -⟩ := ext_layers S.hX S.hi S.hE S.D.hG S.D.hEG S.D.hX0 hne
  have hsub : toPt S.D.G \ toPt S.E ⊆ toPt (layerSet S.D.d (Icc s 1)) := by
    rintro _ ⟨⟨m, hmG, rfl⟩, hmE⟩
    refine ⟨m, ⟨⟨m, hmG⟩, ⟨?_, unitInterval.le_one'⟩, rfl⟩, rfl⟩
    by_contra hlt
    rw [not_le] at hlt
    refine hmE ⟨m, ?_, rfl⟩
    rw [← hsE]
    exact ⟨⟨m, hmG⟩, ⟨unitInterval.nonneg', hlt.le⟩, rfl⟩
  rintro z ⟨hzc, ⟨m, hmE, rfl⟩⟩
  obtain ⟨m', ⟨g, hg, rfl⟩, hm'⟩ := closure_minimal hsub (S.isClosed_toPt_layerSet s 1) hzc
  have hmm : (g : M) = m := Subtype.ext hm'
  have hmE' : (g : M) ∈ layerSet S.D.d (Icc 0 s) := by rw [hsE, hmm]; exact hmE
  obtain ⟨g', hg', hgg⟩ := hmE'
  rw [Subtype.ext hgg] at hg'
  have hgs : S.D.d g = s := le_antisymm hg'.2 hg.1
  have : (g : M) ∈ layer S.D.d s := ⟨g, hgs, rfl⟩
  rw [hW] at this
  exact ⟨g, this, hm'⟩

end B182Last

end HPC.Hagopian
