import HPC.HO16.Defs
import HPC.Span.Defs
import HPC.Plane.Ingram68Star
import HPC.Plane.Most51

/-!
# Batch 193, §5: H–O Theorem 4, path form

Commission 193, §5; skeleton `HO16A.lean`, statement `ho16_theorem4` (unchanged).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Span

/-! ## §5. H–O Theorem 4, path form (commission §5) -/

/-- **Step 1** (commission §5): if `M` does not separate, the cut-wire theorem in
`G × [0, 1]` gives a continuum in `{ε ≤ dist x (γ t)}` meeting both end rows. -/
theorem thm4_continuum_of_not_separates {E : Type*} [MetricSpace E] {G : Set E} (hG : IsCompact G)
    {γ : ℝ → E} (hγ : Continuous γ) {ε : ℝ}
    (hns : ¬ SeparatesIn (G ×ˢ Icc (0 : ℝ) 1)
      {p : E × ℝ | p.1 ∈ G ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ dist p.1 (γ p.2) < ε}
      (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ))) :
    ∃ Z : Set (E × ℝ), Fold.Q78.IsContinuum Z ∧ Z ⊆ G ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ p ∈ Z, ε ≤ dist p.1 (γ p.2)) ∧ (∃ p ∈ Z, p.2 = 0) ∧ ∃ p ∈ Z, p.2 = 1 := by
  set K : Set (E × ℝ) := G ×ˢ Icc (0 : ℝ) 1 with hKdef
  have hK : IsCompact K := hG.prod isCompact_Icc
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set D : Set (E × ℝ) := K ∩ {p | ε ≤ dist p.1 (γ p.2)} with hDdef
  have hDc : IsClosed D := hK.isClosed.inter
    (isClosed_le continuous_const (continuous_fst.dist (hγ.comp continuous_snd)))
  by_contra hno
  apply hns
  set F : Set K := Subtype.val ⁻¹' D
  set E₁ : Set K := Subtype.val ⁻¹' (D ∩ {p | p.2 = 0})
  set E₂ : Set K := Subtype.val ⁻¹' (D ∩ {p | p.2 = 1})
  have hc0 : IsClosed (D ∩ {p : E × ℝ | p.2 = 0}) :=
    hDc.inter (isClosed_eq continuous_snd continuous_const)
  have hc1 : IsClosed (D ∩ {p : E × ℝ | p.2 = 1}) :=
    hDc.inter (isClosed_eq continuous_snd continuous_const)
  obtain ⟨F₁, F₂, hF₁, hF₂, hF12, hFeq, hE₁, hE₂⟩ :=
    exists_split_of_no_continuum (S := K) (F := F) (E₁ := E₁) (E₂ := E₂)
      (hDc.preimage continuous_subtype_val) (fun p hp => hp.1) (fun p hp => hp.1)
      (hc0.preimage continuous_subtype_val) (hc1.preimage continuous_subtype_val)
      (fun C hC hCF h1 h2 => by
        apply hno
        obtain ⟨a, haC, ha⟩ := h1
        obtain ⟨b, hbC, hb⟩ := h2
        refine ⟨Subtype.val '' C, ⟨hC.1.image continuous_subtype_val,
          hC.2.image _ continuous_subtype_val.continuousOn⟩, ?_, ?_, ⟨a, ⟨a, haC, rfl⟩, ha.2⟩,
          ⟨b, ⟨b, hbC, rfl⟩, hb.2⟩⟩
        · rintro _ ⟨q, -, rfl⟩
          exact q.2
        · rintro _ ⟨q, hq, rfl⟩
          exact (hCF hq).2)
  have hF₁F : F₁ ⊆ F := hFeq ▸ subset_union_left
  have hF₂F : F₂ ⊆ F := hFeq ▸ subset_union_right
  refine separatesIn_of_closed (R₀ := Subtype.val '' F₁ ∪ G ×ˢ {0})
    (R₁ := Subtype.val '' F₂ ∪ G ×ˢ {1})
    ((hF₁.isCompact.image continuous_subtype_val).isClosed.union
      (hG.isClosed.prod isClosed_singleton))
    ((hF₂.isCompact.image continuous_subtype_val).isClosed.union
      (hG.isClosed.prod isClosed_singleton)) ?_ ?_ subset_union_right subset_union_right
  · rw [Set.disjoint_left]
    rintro p (⟨a, ha, rfl⟩ | ⟨-, hp0⟩) (⟨b, hb, hab⟩ | ⟨-, hp1⟩)
    · have : b = a := Subtype.ext hab
      subst this
      exact Set.disjoint_left.1 hF12 ha hb
    · have haE : a ∈ E₂ := ⟨hF₁F ha, hp1⟩
      exact Set.disjoint_left.1 hF12 ha (hE₂ haE)
    · have hbE : b ∈ E₁ := ⟨hF₂F hb, by rw [hab]; exact hp0⟩
      exact Set.disjoint_left.1 hF12 (hE₁ hbE) hb
    · rw [mem_singleton_iff] at hp0 hp1
      rw [hp0] at hp1
      exact zero_ne_one hp1
  · rintro p ⟨hpK, hpM⟩
    obtain ⟨hpG, hp01⟩ := hpK
    by_cases h0 : p.2 = 0
    · exact Or.inl (Or.inr ⟨hpG, h0⟩)
    by_cases h1 : p.2 = 1
    · exact Or.inr (Or.inr ⟨hpG, h1⟩)
    have hpI : p.2 ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hp01.1 (Ne.symm h0), lt_of_le_of_ne hp01.2 h1⟩
    have hd : ε ≤ dist p.1 (γ p.2) := by
      by_contra h
      exact hpM ⟨hpG, hpI, lt_of_not_ge h⟩
    have hpF : (⟨p, hpG, hp01⟩ : K) ∈ F := ⟨⟨hpG, hp01⟩, hd⟩
    rw [hFeq] at hpF
    rcases hpF with h | h
    · exact Or.inl (Or.inl ⟨_, h, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, h, rfl⟩)

/-- A Hausdorff limit of compacta that eventually lie in a closed set lies in it. -/
theorem subset_of_tendsto_of_eventually {S : Type*} [MetricSpace S]
    {P : ℕ → TopologicalSpace.NonemptyCompacts S} {P₀ : TopologicalSpace.NonemptyCompacts S}
    (hP : Tendsto P atTop (𝓝 P₀)) {C : Set S} (hC : IsClosed C)
    (h : ∀ᶠ n in atTop, (P n : Set S) ⊆ C) : (P₀ : Set S) ⊆ C := by
  intro z hz
  rw [← hC.closure_eq, Metric.mem_closure_iff]
  intro r hr
  obtain ⟨n, hn1, hn2⟩ :=
    (((tendsto_iff_dist_tendsto_zero.1 hP).eventually (gt_mem_nhds hr)).and h).exists
  rw [Metric.NonemptyCompacts.dist_eq, hausdorffDist_comm] at hn1
  obtain ⟨y, hy, hzy⟩ := exists_dist_lt_of_hausdorffDist_lt hz hn1 (edist_ne_top P₀ (P n))
  exact ⟨y, hn2 hy, hzy⟩

/-- **Steps 2–4** (commission §5): continua `Wₙ ⊆ E × E` with `dist ≥ ε` on them, first and
second coordinates within `1/(n+1)` of `X`, and second coordinates `1/(n+1)`-dense in `X`, have a
Hausdorff limit contradicting `HOSpanZero X`. -/
theorem thm4_limit_contra {E : Type*} [MetricSpace E] [ProperSpace E] {X : Set E}
    (hX : IsCompact X) (hspan : HOSpanZero X) {ε : ℝ} (hε : 0 < ε) (W : ℕ → Set (E × E))
    (hWc : ∀ n, Fold.Q78.IsContinuum (W n))
    (hW1 : ∀ n, ∀ p ∈ W n, p.1 ∈ thickening (1 / ((n : ℝ) + 1)) X)
    (hW2 : ∀ n, ∀ p ∈ W n, p.2 ∈ thickening (1 / ((n : ℝ) + 1)) X)
    (hWd : ∀ n, ∀ p ∈ W n, ε ≤ dist p.1 p.2)
    (hWX : ∀ n, ∀ x ∈ X, ∃ p ∈ W n, dist x p.2 < 1 / ((n : ℝ) + 1)) : False := by
  obtain ⟨p0, hp0⟩ := (hWc 0).2.nonempty
  have hXne : X.Nonempty := by
    obtain ⟨z, hz, -⟩ := mem_thickening_iff.1 (hW1 0 p0 hp0)
    exact ⟨z, hz⟩
  set K := closure (thickening 1 X)
  have hKc : IsCompact K := hX.isBounded.thickening.isCompact_closure
  have hthick : ∀ n : ℕ, thickening (1 / ((n : ℝ) + 1)) X ⊆ K := fun n =>
    (thickening_mono (by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]) X).trans
      subset_closure
  set W' : ℕ → TopologicalSpace.NonemptyCompacts (E × E) :=
    fun n => ⟨⟨W n, (hWc n).1⟩, (hWc n).2.nonempty⟩
  have hWK : ∀ n, W' n ∈ {L : TopologicalSpace.NonemptyCompacts (E × E) |
      (L : Set (E × E)) ⊆ K ×ˢ K} := fun n p hp =>
    ⟨hthick n (hW1 n p hp), hthick n (hW2 n p hp)⟩
  obtain ⟨W₀, -, φ, hφ, hlim⟩ :=
    (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact (hKc.prod hKc)).tendsto_subseq
      hWK
  have hW₀c : IsConnected (W₀ : Set (E × E)) :=
    Most.isConnected_of_tendsto hlim fun n => (hWc (φ n)).2
  have hle : ∀ m n : ℕ, m ≤ n → 1 / ((φ n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    intro m n hmn
    have : (m : ℝ) ≤ φ n := by exact_mod_cast hmn.trans (hφ.id_le n)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hW₀X : ∀ p ∈ (W₀ : Set (E × E)), p.1 ∈ X ∧ p.2 ∈ X := by
    have hm : ∀ m : ℕ, (W₀ : Set (E × E)) ⊆
        {p | infDist p.1 X ≤ 1 / ((m : ℝ) + 1) ∧ infDist p.2 X ≤ 1 / ((m : ℝ) + 1)} := by
      intro m
      refine subset_of_tendsto_of_eventually hlim
        ((isClosed_le ((continuous_infDist_pt X).comp continuous_fst) continuous_const).inter
          (isClosed_le ((continuous_infDist_pt X).comp continuous_snd) continuous_const)) ?_
      filter_upwards [eventually_ge_atTop m] with n hn p hp
      exact ⟨((mem_thickening_iff_infDist_lt hXne).1 (hW1 _ p hp)).le.trans (hle m n hn),
        ((mem_thickening_iff_infDist_lt hXne).1 (hW2 _ p hp)).le.trans (hle m n hn)⟩
    have h0 : ∀ q : E, (∀ m : ℕ, infDist q X ≤ 1 / ((m : ℝ) + 1)) → q ∈ X := by
      intro q hq
      rw [← hX.isClosed.closure_eq, mem_closure_iff_infDist_zero hXne]
      exact le_antisymm (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hq) infDist_nonneg
    intro p hp
    exact ⟨h0 _ fun m => (hm m hp).1, h0 _ fun m => (hm m hp).2⟩
  have hW₀d : ∀ p ∈ (W₀ : Set (E × E)), ε ≤ dist p.1 p.2 :=
    subset_of_tendsto_of_eventually hlim
      (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
      (Eventually.of_forall fun n p hp => hWd _ p hp)
  have hXW : ∀ x ∈ X, ∃ p ∈ (W₀ : Set (E × E)), p.2 = x := by
    intro x hx
    choose q hqW hqd using fun n => hWX (φ n) x hx
    have hqK : ∀ n, q n ∈ K ×ˢ K := fun n => hWK (φ n) (hqW n)
    obtain ⟨q₀, -, ψ, hψ, hqlim⟩ := (hKc.prod hKc).tendsto_subseq hqK
    have hmem : q₀ ∈ (W₀ : Set (E × E)) :=
      Most.mem_of_tendsto hqlim (hlim.comp hψ.tendsto_atTop) (fun n => hqW (ψ n))
    refine ⟨q₀, hmem, ?_⟩
    have h2 : Tendsto (fun n => (q (ψ n)).2) atTop (𝓝 q₀.2) :=
      (continuous_snd.tendsto _).comp hqlim
    have h3 : Tendsto (fun n => (q (ψ n)).2) atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [dist_comm]
      exact (hqd (ψ n)).le.trans (hle n (ψ n) (hψ.id_le n))
    exact tendsto_nhds_unique h2 h3
  set Z : Set (X × X) := {p | ((p.1 : E), (p.2 : E)) ∈ (W₀ : Set (E × E))}
  set ι : X × X → E × E := fun p => ((p.1 : E), (p.2 : E))
  have hι : IsInducing ι := IsInducing.subtypeVal.prodMap IsInducing.subtypeVal
  have himg : ι '' Z = W₀ := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨(⟨p.1, (hW₀X p hp).1⟩, ⟨p.2, (hW₀X p hp).2⟩), hp, rfl⟩
  have hZ : Fold.Q78.IsContinuum Z := by
    refine ⟨by rw [hι.isCompact_iff, himg]; exact W₀.isCompact, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hW₀c.nonempty
      exact ⟨(⟨p.1, (hW₀X p hp).1⟩, ⟨p.2, (hW₀X p hp).2⟩), hp⟩
    · rw [← hι.isPreconnected_image, himg]
      exact hW₀c.isPreconnected
  obtain ⟨p, hpZ, hpd⟩ := hspan Z hZ (by
    rintro _ ⟨p, -, rfl⟩
    obtain ⟨q, hq, hq2⟩ := hXW p.1 p.1.2
    refine ⟨(⟨q.1, (hW₀X q hq).1⟩, p.1), ?_, rfl⟩
    show ((q.1 : E), ((p.1 : X) : E)) ∈ (W₀ : Set (E × E))
    rw [← hq2]
    exact hq)
  have := hW₀d _ hpZ
  simp only [hpd, dist_self] at this
  linarith

/-- **H–O Theorem 4** (p. 184), with the arc `I` replaced by a path `γ` on `[0, 1]` and
`I \ {p, q}` by `(0, 1)`; of `G` only `G ⊆ thickening δ X` is assumed; `X` need not be connected,
and `E` is any proper metric space. -/
theorem ho16_theorem4 {E : Type*} [MetricSpace E] [ProperSpace E] {X : Set E} (hX : IsCompact X)
    (hspan : HOSpanZero X) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ G : Set E, IsCompact G → G ⊆ thickening δ X →
      ∀ γ : ℝ → E, Continuous γ → γ '' Icc (0 : ℝ) 1 ⊆ thickening δ X →
        X ⊆ thickening δ (γ '' Icc (0 : ℝ) 1) →
        SeparatesIn (G ×ˢ Icc (0 : ℝ) 1)
          {p : E × ℝ | p.1 ∈ G ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ dist p.1 (γ p.2) < ε}
          (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)) := by
  by_contra hcon
  push_neg at hcon
  choose G hGc hGX γ hγc hγX hXγ hns using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose Z hZc hZK hZd hZ0 hZ1 using fun n =>
    thm4_continuum_of_not_separates (hGc n) (hγc n) (hns n)
  have hcont : ∀ n, Continuous fun p : E × ℝ => (p.1, γ n p.2) := fun n =>
    continuous_fst.prodMk ((hγc n).comp continuous_snd)
  refine thm4_limit_contra hX hspan hε (fun n => (fun p : E × ℝ => (p.1, γ n p.2)) '' Z n)
    (fun n => ⟨(hZc n).1.image (hcont n), (hZc n).2.image _ (hcont n).continuousOn⟩) ?_ ?_ ?_ ?_
  · rintro n _ ⟨a, ha, rfl⟩
    exact hGX n (hZK n ha).1
  · rintro n _ ⟨a, ha, rfl⟩
    exact hγX n ⟨a.2, (hZK n ha).2, rfl⟩
  · rintro n _ ⟨a, ha, rfl⟩
    exact hZd n a ha
  · intro n x hx
    obtain ⟨y, ⟨t, ht, rfl⟩, hxy⟩ := mem_thickening_iff.1 (hXγ n hx)
    have hconn : IsPreconnected (Prod.snd '' Z n) :=
      (hZc n).2.isPreconnected.image _ continuous_snd.continuousOn
    obtain ⟨a, ha, ha0⟩ := hZ0 n
    obtain ⟨b, hb, hb1⟩ := hZ1 n
    obtain ⟨c, hc, hct⟩ := hconn.Icc_subset ⟨a, ha, ha0⟩ ⟨b, hb, hb1⟩ ht
    exact ⟨(c.1, γ n c.2), ⟨c, hc, rfl⟩, by simpa [hct] using hxy⟩

end HPC.HO16
