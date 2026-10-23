import HPC.HO16.P19Defs

/-!
# Batch 196, §2: ordinary points of a fold

H–O p. 208: "Since ∂π(P₂) is disjoint from the set Z of branch points and endpoints of G, we
have that the set of branch points and endpoints of F is φ⁻¹(Z)." `IsSimpleFoldOf.isOrdinaryPt_iff`.

* `IsOrdinaryPt.of_local`: ordinary points are a local notion;
* `isOrdinaryPt_image_fst_iff`: they are preserved by `π` on a PL graph on which `π` is injective
  (through the order count `isOrdinaryPt_iff_order` of batch 195);
* `exists_single_spoke`: a PL graph on which `π` is injective and whose points near `z` all lie
  over one side of `π(z)` is a single segment near `z`;
* the glueing points `F₁ ∩ F₂` (commission §2, second bullet).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section OrdFold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Segments -/

/-- A point of `[y, a]` no farther from `y` than `w`, where `w - y` is a positive multiple of
`a - y`, lies on `[y, w]`. -/
theorem mem_segment_of_posPar_of_dist_le {y a w p : E} {c : ℝ} (hc : 0 < c)
    (hw : w - y = c • (a - y)) (hp : p ∈ segment ℝ y a) (hd : dist p y ≤ dist w y) :
    p ∈ segment ℝ y w := by
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := mem_segment_iff_param.1 hp
  by_cases hay : a = y
  · subst hay
    simp only [sub_self, smul_zero, add_zero]
    exact left_mem_segment ℝ _ _
  have hay' : 0 < ‖a - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hay)
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, hw, norm_smul, norm_smul,
    Real.norm_of_nonneg hs0, Real.norm_of_nonneg hc.le] at hd
  have hsc : s ≤ c := le_of_mul_le_mul_right hd hay'
  refine mem_segment_iff_param.2 ⟨s / c, ⟨div_nonneg hs0 hc.le, (div_le_one hc).2 hsc⟩, ?_⟩
  rw [hw, smul_smul, div_mul_cancel₀ s hc.ne']

/-- Shrinking a segment `[z, a]` towards `z`. -/
theorem lineMap_mem_segment {z a : E} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap z a t ∈ segment ℝ z a := by
  rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩

theorem dist_lineMap_left' {z a : E} {t : ℝ} (ht : 0 ≤ t) :
    dist (AffineMap.lineMap z a t) z = t * dist a z := by
  rw [dist_lineMap_left, Real.norm_of_nonneg ht, dist_comm]

/-- **Ordinary points are local**: if `K` and `K'` agree near `z`, then `z` is ordinary in `K`
iff in `K'` (one direction; apply twice). -/
theorem IsOrdinaryPt.of_local {K K' : Set E} {z : E} {U : Set E} (hU : U ∈ 𝓝 z)
    (hKK' : K ∩ U ⊆ K') (hK'K : K' ∩ U ⊆ K) (h : IsOrdinaryPt K z) : IsOrdinaryPt K' z := by
  obtain ⟨a, b, ha, hb, hab, hsub, hnhds⟩ := h
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨r', hr', hr'K⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
  have hda : 0 < dist a z := dist_pos.2 ha
  have hdb : 0 < dist b z := dist_pos.2 hb
  set t : ℝ := min 1 (r / (2 * (dist a z + dist b z))) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hr (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htr : t * (dist a z + dist b z) < r := by
    have h1 : t ≤ r / (2 * (dist a z + dist b z)) := min_le_right _ _
    have h2 : r / (2 * (dist a z + dist b z)) * (dist a z + dist b z) = r / 2 := by
      field_simp
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ dist a z + dist b z)
    linarith
  set a' := AffineMap.lineMap z a t
  set b' := AffineMap.lineMap z b t
  have ha'z : dist a' z = t * dist a z := dist_lineMap_left' ht0.le
  have hb'z : dist b' z = t * dist b z := dist_lineMap_left' ht0.le
  have ha'seg : a' ∈ segment ℝ z a := lineMap_mem_segment ⟨ht0.le, ht1⟩
  have hb'seg : b' ∈ segment ℝ z b := lineMap_mem_segment ⟨ht0.le, ht1⟩
  have hsa : segment ℝ a' z ⊆ segment ℝ a z :=
    (convex_segment a z).segment_subset (by rw [segment_symm]; exact ha'seg)
      (right_mem_segment ℝ _ _)
  have hsb : segment ℝ z b' ⊆ segment ℝ z b :=
    (convex_segment z b).segment_subset (left_mem_segment ℝ _ _) hb'seg
  have hball_a : segment ℝ a' z ⊆ ball z r := by
    intro p hp
    rw [mem_ball]
    have : dist p z ≤ dist a' z := by
      rw [segment_symm] at hp
      obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := mem_segment_iff_param.1 hp
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1
    nlinarith [dist_nonneg (x := b) (y := z)]
  have hball_b : segment ℝ z b' ⊆ ball z r := by
    intro p hp
    rw [mem_ball]
    have : dist p z ≤ dist b' z := by
      obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := mem_segment_iff_param.1 hp
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1
    nlinarith [dist_nonneg (x := a) (y := z)]
  refine ⟨a', b', ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, dist_self] at ha'z; nlinarith
  · intro h
    rw [h, dist_self] at hb'z; nlinarith
  · apply Subset.antisymm
    · exact (inter_subset_inter hsa hsb).trans hab.subset
    · rintro p rfl; exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · rintro p (hp | hp)
    · exact hKK' ⟨hsub (Or.inl (hsa hp)), hrU (hball_a hp)⟩
    · exact hKK' ⟨hsub (Or.inr (hsb hp)), hrU (hball_b hp)⟩
  · refine Metric.mem_nhdsWithin_iff.2 ⟨min r (min r' (min (dist a' z) (dist b' z))),
      lt_min hr (lt_min hr' (lt_min (by rw [ha'z]; positivity) (by rw [hb'z]; positivity))), ?_⟩
    rintro p ⟨hp, hpK'⟩
    rw [mem_ball] at hp
    have hp1 : dist p z < r := hp.trans_le (min_le_left _ _)
    have hp2 : dist p z < r' := hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hp3 : dist p z < dist a' z :=
      hp.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hp4 : dist p z < dist b' z :=
      hp.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hpK : p ∈ K := hK'K ⟨hpK', hrU (mem_ball.2 hp1)⟩
    rcases hr'K ⟨mem_ball.2 hp2, hpK⟩ with hpa | hpb
    · left
      rw [segment_symm] at hpa ⊢
      refine mem_segment_of_posPar_of_dist_le ht0 ?_ hpa hp3.le
      simp only [a', AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
    · right
      refine mem_segment_of_posPar_of_dist_le ht0 ?_ hpb hp4.le
      simp only [b', AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]

theorem isOrdinaryPt_congr_local {K K' : Set E} {z : E} {U : Set E} (hU : U ∈ 𝓝 z)
    (h : K ∩ U = K' ∩ U) : IsOrdinaryPt K z ↔ IsOrdinaryPt K' z :=
  have h1 : K ∩ U ⊆ K' := fun p hp => (h ▸ hp : p ∈ K' ∩ U).1
  have h2 : K' ∩ U ⊆ K := fun p hp => (h.symm ▸ hp : p ∈ K ∩ U).1
  ⟨IsOrdinaryPt.of_local hU h1 h2, IsOrdinaryPt.of_local hU h2 h1⟩

/-! ## Transfer along `π` -/

omit [NormedSpace ℝ E] in
theorem image_fst_openSegment [NormedSpace ℝ E] (p q : E × ℝ) :
    Prod.fst '' openSegment ℝ p q = openSegment ℝ p.1 q.1 :=
  image_openSegment ℝ (LinearMap.fst ℝ E ℝ).toAffineMap p q

/-- **Ordinary points and `π`**: on a PL graph `K` on which `π` is injective, `z` is ordinary in
`K` iff `π(z)` is ordinary in `π(K)` (order count, `isOrdinaryPt_iff_order`). -/
theorem isOrdinaryPt_image_fst_iff {K : Set (E × ℝ)} (hK : IsPLGraph K)
    (hinj : InjOn Prod.fst K) {z : E × ℝ} (hz : z ∈ K) :
    IsOrdinaryPt (Prod.fst '' K) z.1 ↔ IsOrdinaryPt K z := by
  classical
  obtain ⟨S, hne, hKS, hdis⟩ := hK
  have hmem : ∀ s ∈ S, ∀ x ∈ segment ℝ s.1 s.2, x ∈ K := fun s hs x hx => by
    rw [hKS]; exact mem_biUnion hs hx
  have hl : ∀ s ∈ S, s.1 ∈ K := fun s hs => hmem s hs _ (left_mem_segment ℝ _ _)
  have hr : ∀ s ∈ S, s.2 ∈ K := fun s hs => hmem s hs _ (right_mem_segment ℝ _ _)
  set f : (E × ℝ) × (E × ℝ) → E × E := fun s => (s.1.1, s.2.1) with hf
  set S' := S.image f with hS'
  have hne' : ∀ s ∈ S', s.1 ≠ s.2 := by
    simp only [hS', Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ h
    exact hne s hs (hinj (hl s hs) (hr s hs) h)
  have hKS' : Prod.fst '' K = ⋃ s ∈ S', segment ℝ s.1 s.2 := by
    rw [hKS, image_iUnion₂]
    simp only [image_fst_segment]
    ext x
    simp only [mem_iUnion, hS', Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hx⟩; exact ⟨_, ⟨s, hs, rfl⟩, hx⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩; exact ⟨s, hs, hx⟩
  have hdis' : PairwiseEndpoints S' := by
    simp only [PairwiseEndpoints, hS', Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hne'' y ⟨hy, hy'⟩
    rw [← image_fst_segment] at hy hy'
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', hxx⟩ := hy'
    have hxe : x' = x := hinj (hmem s' hs' x' hx') (hmem s hs x hx) hxx
    subst hxe
    have hss : s ≠ s' := by rintro rfl; exact hne'' rfl
    obtain ⟨h1, h2⟩ := hdis s hs s' hs' hss ⟨hx, hx'⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · rw [h]; exact Or.inl rfl
      · rw [Set.mem_singleton_iff.1 h]; exact Or.inr rfl
    · rcases h2 with h | h
      · rw [h]; exact Or.inl rfl
      · rw [Set.mem_singleton_iff.1 h]; exact Or.inr rfl
  rw [isOrdinaryPt_iff_order hne' hKS' hdis', isOrdinaryPt_iff_order hne hKS hdis]
  have hfinj : InjOn f S := by
    intro s hs t ht hst
    simp only [hf, Prod.mk.injEq] at hst
    exact Prod.ext (hinj (hl s hs) (hl t ht) hst.1) (hinj (hr s hs) (hr t ht) hst.2)
  have hopen : (∃ s ∈ S', z.1 ∈ openSegment ℝ s.1 s.2) ↔
      ∃ s ∈ S, z ∈ openSegment ℝ s.1 s.2 := by
    constructor
    · rintro ⟨_, hs', hzs⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hs'
      have hzs' : z.1 ∈ Prod.fst '' openSegment ℝ s.1 s.2 := by
        rw [image_fst_openSegment]; exact hzs
      obtain ⟨w, hw, hwz⟩ := hzs'
      have : w = z := hinj (hmem s hs w (openSegment_subset_segment ℝ _ _ hw)) hz hwz
      exact ⟨s, hs, this ▸ hw⟩
    · rintro ⟨s, hs, hzs⟩
      refine ⟨f s, Finset.mem_image_of_mem f hs, ?_⟩
      show z.1 ∈ openSegment ℝ s.1.1 s.2.1
      rw [← image_fst_openSegment]; exact ⟨z, hzs, rfl⟩
  have hcount : {s : E × E | s ∈ S' ∧ (s.1 = z.1 ∨ s.2 = z.1)} =
      f '' {s | s ∈ S ∧ (s.1 = z ∨ s.2 = z)} := by
    ext s'
    constructor
    · rintro ⟨hs', h⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hs'
      refine ⟨s, ⟨hs, ?_⟩, rfl⟩
      rcases h with h | h
      · exact Or.inl (hinj (hl s hs) hz h)
      · exact Or.inr (hinj (hr s hs) hz h)
    · rintro ⟨s, ⟨hs, h⟩, rfl⟩
      refine ⟨Finset.mem_image_of_mem f hs, ?_⟩
      rcases h with h | h
      · exact Or.inl (by simp only [hf, h])
      · exact Or.inr (by simp only [hf, h])
  rw [hopen, hcount, (hfinj.mono fun s hs => hs.1).ncard_image]

/-- Ordinary points of a sheet `Fᵢ` near which `F = Fᵢ` and `G = Gᵢ`. -/
theorem isOrdinaryPt_one_sheet {G Gi : Set E} {F Fi : Set (E × ℝ)} (hFi : IsPLGraph Fi)
    (hinj : InjOn Prod.fst Fi) (himg : Prod.fst '' Fi = Gi) {z : E × ℝ} (hz : z ∈ Fi)
    {U : Set (E × ℝ)} {V : Set E} (hU : U ∈ 𝓝 z) (hUF : F ∩ U = Fi ∩ U) (hV : V ∈ 𝓝 z.1)
    (hVG : G ∩ V = Gi ∩ V) : IsOrdinaryPt F z ↔ IsOrdinaryPt G z.1 := by
  rw [isOrdinaryPt_congr_local hU hUF, isOrdinaryPt_congr_local hV hVG, ← himg,
    isOrdinaryPt_image_fst_iff hFi hinj hz]

/-! ## A single spoke -/

/-- A PL graph `K` on which `π` is injective, all of whose points near `z` lie over the ray from
`π(z)` in direction `d`, is a single segment `[z, w]` near `z`. -/
theorem exists_single_spoke {K : Set (E × ℝ)} (hK : IsPLGraph K) (hinj : InjOn Prod.fst K)
    {z : E × ℝ} (hz : z ∈ K) {d : E} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ p ∈ K, dist p z < ρ → p ≠ z → ∃ μ : ℝ, 0 < μ ∧ p.1 - z.1 = μ • d) :
    ∃ w, w ≠ z ∧ segment ℝ z w ⊆ K ∧ ∃ ρ' > 0, ∀ p ∈ K, dist p z < ρ' → p ∈ segment ℝ z w := by
  obtain ⟨Y, hY⟩ := hK.exists_fan hz hρ
  obtain ⟨-, hYK, -, hYn, hYball⟩ := hY.props
  obtain ⟨n, w, hwz, rfl, -, hdisj, -, -⟩ := hY
  have hspoke : ∀ k, segment ℝ z (w k) ⊆ insert z (⋃ k, segment ℝ z (w k)) := fun k p hp =>
    Or.inr (mem_iUnion.2 ⟨k, hp⟩)
  have hwK : ∀ k, w k ∈ K := fun k => hYK (hspoke k (right_mem_segment ℝ _ _))
  have hwd : ∀ k, dist (w k) z < ρ := fun k =>
    mem_ball.1 (hYball (hspoke k (right_mem_segment ℝ _ _)))
  have hn1 : n ≠ 0 := by
    rintro rfl
    have hY1 : insert z (⋃ k : Fin 0, segment ℝ z (w k)) = {z} := by simp
    rw [hY1] at hYn
    obtain ⟨u, hu, hzu, hsub⟩ := mem_nhdsWithin.1 hYn
    have hcl := hK.mem_closure_diff_finite hz (finite_singleton z)
    obtain ⟨p, hpu, hpK, hpz⟩ := mem_closure_iff.1 hcl u hu hzu
    exact hpz (hsub ⟨hpu, hpK⟩)
  have key : ∀ k l : Fin n, k ≠ l → ∀ μk μl : ℝ, 0 < μk → 0 < μl → μk ≤ μl →
      (w k).1 - z.1 = μk • d → (w l).1 - z.1 = μl • d → False := by
    intro k l hkl μk μl hμk hμl hle hk hl
    set q := z + (μk / μl) • (w l - z) with hqdef
    have hq : q ∈ segment ℝ z (w l) := mem_segment_iff_param.2
      ⟨μk / μl, ⟨div_nonneg hμk.le hμl.le, (div_le_one hμl).2 hle⟩, rfl⟩
    have hqK : q ∈ K := hYK (hspoke l hq)
    have hq1 : q.1 = (w k).1 := by
      have e1 : q.1 = z.1 + (μk / μl) • ((w l).1 - z.1) := rfl
      rw [e1, hl, smul_smul, div_mul_cancel₀ _ hμl.ne', ← hk]
      abel
    have hqw : q = w k := hinj hqK (hwK k) hq1
    have hmem : w k ∈ segment ℝ z (w k) ∩ segment ℝ z (w l) :=
      ⟨right_mem_segment ℝ _ _, hqw ▸ hq⟩
    rw [hdisj k l hkl] at hmem
    exact hwz k hmem
  have hn2 : ∀ k l : Fin n, k = l := by
    intro k l
    by_contra hkl
    obtain ⟨μk, hμk, hk⟩ := h _ (hwK k) (hwd k) (hwz k)
    obtain ⟨μl, hμl, hl⟩ := h _ (hwK l) (hwd l) (hwz l)
    rcases le_total μk μl with hle | hle
    · exact key k l hkl μk μl hμk hμl hle hk hl
    · exact key l k (Ne.symm hkl) μl μk hμl hμk hle hl hk
  set k₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn1⟩
  have hYeq : insert z (⋃ k, segment ℝ z (w k)) = segment ℝ z (w k₀) := by
    apply Subset.antisymm
    · rintro p (rfl | hp)
      · exact left_mem_segment ℝ _ _
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hp
        rwa [hn2 k k₀] at hk
    · exact hspoke k₀
  rw [hYeq] at hYK hYn
  obtain ⟨ρ', hρ', hsub⟩ := Metric.mem_nhdsWithin_iff.1 hYn
  exact ⟨w k₀, hwz k₀, hYK, ρ', hρ', fun p hp hd => hsub ⟨mem_ball.2 hd, hp⟩⟩

/-- A point `u ≠ y` of `[y, a]` is `y + c • (a - y)` with `c > 0`. -/
theorem posPar_of_mem_segment' {y a u : E} (hu : u ∈ segment ℝ y a) (huy : u ≠ y) :
    ∃ c : ℝ, 0 < c ∧ u - y = c • (a - y) := by
  obtain ⟨c, ⟨hc0, -⟩, rfl⟩ := mem_segment_iff_param.1 hu
  refine ⟨c, lt_of_le_of_ne hc0 ?_, by rw [add_sub_cancel_left]⟩
  rintro rfl
  exact huy (by simp)

/-- A segment `[z, p]` with `p ≠ z` is infinite. -/
theorem segment_infinite_of_ne {z p : E} (h : p ≠ z) : (segment ℝ z p).Infinite := by
  rw [segment_eq_image_lineMap]
  exact (Icc_infinite zero_lt_one).image
    ((AffineMap.lineMap_injective ℝ (Ne.symm h)).injOn)

/-- **Commission §2, second bullet**: over an ordinary point `y ∈ ∂G₁` of `G`, the sheet `G₁` lies
on one side of `y`: there is a direction `d` such that every point of `G₁` near `y` is
`y + μ • d` with `μ > 0`. -/
theorem one_side_of_relFrontier {G G₁ : Set E} (hG₁ : IsPLGraph G₁) (hG₁G : G₁ ⊆ G) {y : E}
    (hy : IsOrdinaryPt G y) (hy1 : y ∈ G₁) (hyc : y ∈ closure (G \ G₁)) :
    ∃ d : E, ∃ ρ > 0, ∀ p ∈ G₁, dist p y < ρ → p ≠ y → ∃ μ : ℝ, 0 < μ ∧ p - y = μ • d := by
  obtain ⟨a, b, ha, hb, hab, -, hnhds⟩ := hy
  obtain ⟨r₀, hr₀, hr₀G⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
  obtain ⟨Y, hY⟩ := hG₁.exists_fan hy1 hr₀
  obtain ⟨-, hYK, -, hYn, hYball⟩ := hY.props
  obtain ⟨n, u, huy, rfl, -, -, -, -⟩ := hY
  obtain ⟨ρ, hρ, hρY⟩ := Metric.mem_nhdsWithin_iff.1 hYn
  have hspoke : ∀ k, segment ℝ y (u k) ⊆ insert y (⋃ k, segment ℝ y (u k)) := fun k p hp =>
    Or.inr (mem_iUnion.2 ⟨k, hp⟩)
  have hside : ∀ k, u k ∈ segment ℝ y a ∨ u k ∈ segment ℝ y b := by
    intro k
    have hu : u k ∈ ball y r₀ ∩ G :=
      ⟨hYball (hspoke k (right_mem_segment ℝ _ _)), hG₁G (hYK (hspoke k (right_mem_segment ℝ _ _)))⟩
    rcases hr₀G hu with h | h
    · left; rw [segment_symm]; exact h
    · right; exact h
  -- the points of `Y` other than `y` lie on spokes
  have hYpts : ∀ p ∈ G₁, dist p y < ρ → p ≠ y → ∃ k, p ∈ segment ℝ y (u k) := by
    intro p hp hpd hpy
    rcases hρY ⟨mem_ball.2 hpd, hp⟩ with h | h
    · exact absurd h hpy
    · exact mem_iUnion.1 h
  have hray : ∀ {c : E} (k : Fin n), u k ∈ segment ℝ y c → ∀ p ∈ segment ℝ y (u k), p ≠ y →
      ∃ μ : ℝ, 0 < μ ∧ p - y = μ • (c - y) := by
    intro c k hk p hp hpy
    obtain ⟨c₁, hc₁, h₁⟩ := posPar_of_mem_segment' hk (huy k)
    obtain ⟨c₂, hc₂, h₂⟩ := posPar_of_mem_segment' hp hpy
    exact ⟨c₂ * c₁, mul_pos hc₂ hc₁, by rw [h₂, h₁, smul_smul]⟩
  by_cases hA : ∀ k, u k ∈ segment ℝ y a
  · refine ⟨a - y, ρ, hρ, fun p hp hpd hpy => ?_⟩
    obtain ⟨k, hk⟩ := hYpts p hp hpd hpy
    exact hray k (hA k) p hk hpy
  by_cases hB : ∀ k, u k ∈ segment ℝ y b
  · refine ⟨b - y, ρ, hρ, fun p hp hpd hpy => ?_⟩
    obtain ⟨k, hk⟩ := hYpts p hp hpd hpy
    exact hray k (hB k) p hk hpy
  exfalso
  push_neg at hA hB
  obtain ⟨l, hl⟩ := hA
  obtain ⟨k, hk⟩ := hB
  have hka : u k ∈ segment ℝ y a := (hside k).resolve_right hk
  have hlb : u l ∈ segment ℝ y b := (hside l).resolve_left hl
  obtain ⟨ca, hca, hua⟩ := posPar_of_mem_segment' hka (huy k)
  obtain ⟨cb, hcb, hub⟩ := posPar_of_mem_segment' hlb (huy l)
  set ρ'' := min r₀ (min (dist (u k) y) (dist (u l) y))
  have hρ'' : 0 < ρ'' := lt_min hr₀ (lt_min (dist_pos.2 (huy k)) (dist_pos.2 (huy l)))
  obtain ⟨p, ⟨hpG, hpG₁⟩, hpball⟩ := Metric.mem_closure_iff.1 hyc ρ'' hρ''
  have hp0 : dist p y < r₀ := by rw [dist_comm]; exact hpball.trans_le (min_le_left _ _)
  have hp1 : dist p y ≤ dist (u k) y := by
    rw [dist_comm]; exact hpball.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hp2 : dist p y ≤ dist (u l) y := by
    rw [dist_comm]; exact hpball.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply hpG₁
  rcases hr₀G ⟨mem_ball.2 hp0, hpG⟩ with h | h
  · rw [segment_symm] at h
    exact hYK (hspoke k (mem_segment_of_posPar_of_dist_le hca hua h hp1))
  · exact hYK (hspoke l (mem_segment_of_posPar_of_dist_le hcb hub h hp2))

/-- **Commission §2, second bullet**: a glueing point `z ∈ F₁ ∩ F₂` over an ordinary point of `G`
is ordinary in `F`: near `z`, `F₁` and `F₂` are one spoke each, meeting only at `z`. -/
theorem IsSimpleFoldOf.isOrdinaryPt_of_mem_inter {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {z : E × ℝ} (hz : z ∈ F₁ ∩ F₂)
    (hy : IsOrdinaryPt G z.1) : IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) z := by
  have hfin12 := (ho16_lemma6 hF).2.2.2.2.1
  obtain ⟨hT, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, -, -, h12, -, h13⟩ := hF
  obtain ⟨-, -, -, hG₁, -, -, hcov, hG₂, -⟩ := hT
  have hG₁G : G₁ ⊆ G := hcov ▸ subset_union_left
  have hyfr : z.1 ∈ relFrontier G G₁ := by rw [← h12]; exact ⟨z, hz, rfl⟩
  have hy1 : z.1 ∈ G₁ := by rw [← he₁]; exact ⟨z, hz.1, rfl⟩
  obtain ⟨d, ρ, hρ, hd⟩ := one_side_of_relFrontier hG₁ hG₁G hy hy1 hyfr.2
  have hsheet : ∀ {Fi : Set (E × ℝ)}, InjOn Prod.fst Fi → z ∈ Fi → Prod.fst '' Fi ⊆ G₁ →
      ∀ p ∈ Fi, dist p z < ρ → p ≠ z → ∃ μ : ℝ, 0 < μ ∧ p.1 - z.1 = μ • d := by
    intro Fi hinj hzF hsub p hp hpd hpz
    refine hd p.1 (hsub ⟨p, hp, rfl⟩)
      ((show dist p.1 z.1 ≤ dist p z by rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hpd)
      fun h => hpz ?_
    exact hinj hp hzF h
  have hG₂₁ : Prod.fst '' F₂ ⊆ G₁ := by rw [he₂, hG₂]; exact inter_subset_left
  obtain ⟨w₁, hw₁, hs₁, ρ₁, hρ₁, hρ₁s⟩ :=
    exists_single_spoke hP₁ hi₁ hz.1 hρ (hsheet hi₁ hz.1 he₁.subset)
  obtain ⟨w₂, hw₂, hs₂, ρ₂, hρ₂, hρ₂s⟩ :=
    exists_single_spoke hP₂ hi₂ hz.2 hρ (hsheet hi₂ hz.2 hG₂₁)
  have hz3 : z ∉ F₃ := fun h => Set.disjoint_left.1 h13 hz.1 h
  obtain ⟨ρ₃, hρ₃, hρ₃s⟩ := Metric.isOpen_iff.1 hP₃.isCompact.isClosed.isOpen_compl z hz3
  refine ⟨w₁, w₂, hw₁, hw₂, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro p ⟨hp1, hp2⟩
      by_contra hpz
      rw [segment_symm] at hp1
      have hsub : segment ℝ z p ⊆ F₁ ∩ F₂ := fun q hq =>
        ⟨hs₁ ((convex_segment z w₁).segment_subset (left_mem_segment ℝ _ _) hp1 hq),
          hs₂ ((convex_segment z w₂).segment_subset (left_mem_segment ℝ _ _) hp2 hq)⟩
      exact segment_infinite_of_ne hpz (hfin12.subset hsub)
    · rintro p rfl; exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · rintro p (hp | hp)
    · rw [segment_symm] at hp; exact Or.inl (Or.inl (hs₁ hp))
    · exact Or.inl (Or.inr (hs₂ hp))
  · refine Metric.mem_nhdsWithin_iff.2 ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), ?_⟩
    rintro p ⟨hp, (hp1 | hp2) | hp3⟩
    · left; rw [segment_symm]
      exact hρ₁s p hp1 ((mem_ball.1 hp).trans_le (min_le_left _ _))
    · right
      exact hρ₂s p hp2 ((mem_ball.1 hp).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    · exact absurd hp3 (hρ₃s (mem_ball.2
        ((mem_ball.1 hp).trans_le ((min_le_right _ _).trans (min_le_right _ _)))))

/-! ## The theorem -/

/-- **p. 208**: "Since ∂π(P₂) is disjoint from the set Z of branch points and endpoints of G, we
have that the set of branch points and endpoints of F is φ⁻¹(Z)". -/
theorem IsSimpleFoldOf.isOrdinaryPt_iff {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hZ : ∀ y ∈ relFrontier G G₂, IsOrdinaryPt G y)
    {z : E × ℝ} (hz : z ∈ F₁ ∪ F₂ ∪ F₃) :
    IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) z ↔ IsOrdinaryPt G z.1 := by
  have L6 := ho16_lemma6 hF
  obtain ⟨hT, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃, h12, h23, h13⟩ := id hF
  obtain ⟨-, -, -, -, -, -, hcov, hG₂, -⟩ := hT
  have hG₁G : G₁ ⊆ G := hcov ▸ subset_union_left
  have hG₃G : G₃ ⊆ G := hcov ▸ subset_union_right
  have hc₁ := hP₁.isCompact.isClosed
  have hc₂ := hP₂.isCompact.isClosed
  have hc₃ := hP₃.isCompact.isClosed
  by_cases hz12 : z ∈ F₁ ∩ F₂
  · have hy : IsOrdinaryPt G z.1 := hZ _ (by rw [L6.1, ← h12]; exact Or.inl ⟨z, hz12, rfl⟩)
    exact iff_of_true (hF.isOrdinaryPt_of_mem_inter hz12 hy) hy
  by_cases hz23 : z ∈ F₂ ∩ F₃
  · have hy : IsOrdinaryPt G z.1 := hZ _ (by rw [L6.1, ← h23]; exact Or.inr ⟨z, hz23, rfl⟩)
    have := hF.symm.isOrdinaryPt_of_mem_inter ⟨hz23.2, hz23.1⟩ (by exact hy)
    rw [fold_union_symm] at this
    exact iff_of_true this hy
  -- a point over which `G` is `Gᵢ` near `π(z)`
  have hnear : ∀ {Fi : Set (E × ℝ)} {Gi : Set E}, InjOn Prod.fst Fi → z ∈ Fi →
      Prod.fst '' Fi = Gi → Gi ⊆ G → (z.1 ∈ closure (G \ Gi) → False) →
      (closure (G \ Gi))ᶜ ∈ 𝓝 z.1 ∧ G ∩ (closure (G \ Gi))ᶜ = Gi ∩ (closure (G \ Gi))ᶜ := by
    intro Fi Gi _ _ _ hGi hnot
    refine ⟨isClosed_closure.isOpen_compl.mem_nhds hnot, ?_⟩
    ext p
    constructor
    · rintro ⟨hpG, hp⟩
      refine ⟨?_, hp⟩
      by_contra hpi
      exact hp (subset_closure ⟨hpG, hpi⟩)
    · rintro ⟨hpi, hp⟩; exact ⟨hGi hpi, hp⟩
  rcases hz with (h1 | h2) | h3
  · have hz2 : z ∉ F₂ := fun h => hz12 ⟨h1, h⟩
    have hz3 : z ∉ F₃ := fun h => Set.disjoint_left.1 h13 h1 h
    have hnot : z.1 ∈ closure (G \ G₁) → False := by
      intro hc
      have hfr : z.1 ∈ relFrontier G G₁ :=
        ⟨subset_closure (by rw [← he₁]; exact ⟨z, h1, rfl⟩), hc⟩
      rw [← h12] at hfr
      obtain ⟨q, hq, hqz⟩ := hfr
      exact hz2 (hi₁ hq.1 h1 hqz ▸ hq.2)
    obtain ⟨hV, hVG⟩ := hnear hi₁ h1 he₁ hG₁G hnot
    refine isOrdinaryPt_one_sheet hP₁ hi₁ he₁ h1 ((hc₂.union hc₃).isOpen_compl.mem_nhds ?_) ?_
      hV hVG
    · rintro (h | h)
      · exact hz2 h
      · exact hz3 h
    · ext p; simp only [mem_inter_iff, mem_union, mem_compl_iff, not_or]; tauto
  · have hz1 : z ∉ F₁ := fun h => hz12 ⟨h, h2⟩
    have hz3 : z ∉ F₃ := fun h => hz23 ⟨h2, h⟩
    have hy2 : z.1 ∈ G₂ := by rw [← he₂]; exact ⟨z, h2, rfl⟩
    have hG₂G : G₂ ⊆ G := hG₂ ▸ inter_subset_left.trans hG₁G
    have hnot : z.1 ∈ closure (G \ G₂) → False := by
      intro hc
      have hsplit : G \ G₂ = (G \ G₁) ∪ (G \ G₃) := by
        rw [hG₂, diff_inter]
      rw [hsplit, closure_union] at hc
      rcases hc with hc | hc
      · have hfr : z.1 ∈ relFrontier G G₁ :=
          ⟨subset_closure (by rw [hG₂] at hy2; exact hy2.1), hc⟩
        rw [← h12] at hfr
        obtain ⟨q, hq, hqz⟩ := hfr
        exact hz1 (hi₂ hq.2 h2 hqz ▸ hq.1)
      · have hfr : z.1 ∈ relFrontier G G₃ :=
          ⟨subset_closure (by rw [hG₂] at hy2; exact hy2.2), hc⟩
        rw [← h23] at hfr
        obtain ⟨q, hq, hqz⟩ := hfr
        exact hz3 (hi₂ hq.1 h2 hqz ▸ hq.2)
    obtain ⟨hV, hVG⟩ := hnear hi₂ h2 he₂ hG₂G hnot
    refine isOrdinaryPt_one_sheet hP₂ hi₂ he₂ h2 ((hc₁.union hc₃).isOpen_compl.mem_nhds ?_) ?_
      hV hVG
    · rintro (h | h)
      · exact hz1 h
      · exact hz3 h
    · ext p; simp only [mem_inter_iff, mem_union, mem_compl_iff, not_or]; tauto
  · have hz2 : z ∉ F₂ := fun h => hz23 ⟨h, h3⟩
    have hz1 : z ∉ F₁ := fun h => Set.disjoint_left.1 h13 h h3
    have hnot : z.1 ∈ closure (G \ G₃) → False := by
      intro hc
      have hfr : z.1 ∈ relFrontier G G₃ :=
        ⟨subset_closure (by rw [← he₃]; exact ⟨z, h3, rfl⟩), hc⟩
      rw [← h23] at hfr
      obtain ⟨q, hq, hqz⟩ := hfr
      exact hz2 (hi₃ hq.2 h3 hqz ▸ hq.1)
    obtain ⟨hV, hVG⟩ := hnear hi₃ h3 he₃ hG₃G hnot
    refine isOrdinaryPt_one_sheet hP₃ hi₃ he₃ h3 ((hc₁.union hc₂).isOpen_compl.mem_nhds ?_) ?_
      hV hVG
    · rintro (h | h)
      · exact hz1 h
      · exact hz2 h
    · ext p; simp only [mem_inter_iff, mem_union, mem_compl_iff, not_or]; tauto

end OrdFold

end HPC.HO16
