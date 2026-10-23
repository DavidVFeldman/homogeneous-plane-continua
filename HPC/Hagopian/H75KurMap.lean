import HPC.Hagopian.H75Kur

/-!
# Batch 155: from Kuratowski's family `D` to a type A′ map (Kuratowski §48 IV, VII Theorems 3–5)

Let `Y` be a compact metric space, irreducible between `a` and `b`. A *scale* is a family
`E : ℚ → Set Y` of members of `D` (`IsDElt a`), increasing, strictly on `(0, 1)`, empty at `q ≤ 0`, everything at
`q ≥ 1`, and dense in `D`: between two members `D₁ ⊊ D₂` of `D` lies some `E q`. From a scale we
build `k y = inf {q : y ∈ E q}` and prove (`scaleMap_spec`) that `k` is a continuous map onto
`[0, 1]` with connected fibres (each fibre is the directed intersection of the continua
`cl (E q' − E q)`, `q < t < q'`) whose fibres have empty interior (if a fibre had interior, the
closure of `⋃_{q < t} E q` and the closure of the interior of `⋂_{q > t} E q` would be two members of
`D`, the first strictly inside the second, and two members of the scale between them would both have
index `t`).

This is how Kuratowski's Theorem 3 (the order type of `D`) passes to a monotone map onto `[0, 1]`
with nowhere dense layers.
-/

namespace HPC.Hagopian

open Set Topology

section Map

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- A directed intersection of closed preconnected sets of a compact metric space is
preconnected. -/
theorem isPreconnected_iInter_directed {ι : Type*} [Nonempty ι] (K : ι → Set Y)
    (hd : Directed (· ⊇ ·) K) (hc : ∀ i, IsClosed (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    IsPreconnected (⋂ i, K i) := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov ⟨x, hxK, hxt⟩ ⟨y, hyK, hyt'⟩
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  have hA : IsClosed ((⋂ i, K i) ∩ t) := (isClosed_iInter hc).inter ht
  have hB : IsClosed ((⋂ i, K i) ∩ t') := (isClosed_iInter hc).inter ht'
  have hAB : Disjoint ((⋂ i, K i) ∩ t) ((⋂ i, K i) ∩ t') := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have : z ∈ (⋂ i, K i) ∩ (t ∩ t') := ⟨hz.1, hz.2, hz'.2⟩
    rw [hemp] at this; exact this
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hAB
  have hsub : (⋂ i, K i) ⊆ U ∪ V := fun z hz => by
    rcases hcov hz with h | h
    · exact Or.inl (hAU ⟨hz, h⟩)
    · exact Or.inr (hBV ⟨hz, h⟩)
  obtain ⟨i, hi⟩ := (hU.union hV).isClosed_compl.isCompact.elim_directed_family_closed K hc
    (by rw [eq_empty_iff_forall_notMem]; rintro z ⟨hz1, hz2⟩; exact hz1 (hsub hz2)) hd
  have hKi : K i ⊆ U ∪ V := fun z hz => by
    by_contra h
    have : z ∈ (U ∪ V)ᶜ ∩ K i := ⟨h, hz⟩
    rw [hi] at this; exact this
  rcases isPreconnected_iff_subset_of_disjoint.1 (hp i) U V hU hV hKi
    (by rw [hUV.inter_eq, inter_empty]) with h | h
  · exact disjoint_left.1 hUV (h (mem_iInter.1 hyK i)) (hBV ⟨hyK, hyt'⟩)
  · exact disjoint_left.1 hUV (hAU ⟨hxK, hxt⟩) (h (mem_iInter.1 hxK i))

/-- A map to `ℝ` with open sub- and superlevel sets is continuous. -/
theorem continuous_of_Iio_Ioi {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (h1 : ∀ t, IsOpen (f ⁻¹' Iio t)) (h2 : ∀ t, IsOpen (f ⁻¹' Ioi t)) : Continuous f := by
  have := OrderTopology.topology_eq_generate_intervals (α := ℝ)
  rw [continuous_def]
  intro s hs
  rw [this] at hs
  induction hs with
  | basic s hs => obtain ⟨a, rfl | rfl⟩ := hs; exact h2 a; exact h1 a
  | univ => simp
  | inter s t _ _ hs ht => exact hs.inter ht
  | sUnion S _ hS => rw [preimage_sUnion]; exact isOpen_biUnion hS

/-- A *scale* in Kuratowski's family `D`: increasing, strictly where it is not `∅` or `Y`, `∅` at `q ≤ 0`, `Y` at `q ≥ 1`,
dense in `D`. -/
def IsDScale (a : Y) (E : ℚ → Set Y) : Prop :=
  (∀ q, IsDElt a (E q)) ∧ Monotone E ∧ (∀ q q', q < q' → q < 1 → 0 < q' → E q ≠ E q') ∧
    (∀ q, q ≤ 0 → E q = ∅) ∧ (∀ q, 1 ≤ q → E q = univ) ∧
    (∀ D₁ D₂, IsDElt a D₁ → IsDElt a D₂ → D₁ ⊆ D₂ → D₁ ≠ D₂ →
      ∃ q, D₁ ⊆ E q ∧ E q ≠ D₁ ∧ E q ⊆ D₂ ∧ E q ≠ D₂)

/-- The function `y ↦ inf {q : y ∈ E q}`. -/
noncomputable def scaleFun (E : ℚ → Set Y) (y : Y) : ℝ :=
  sInf ((fun q : ℚ => (q : ℝ)) '' {q | y ∈ E q})

variable [ConnectedSpace Y] {a b : Y} {E : ℚ → Set Y}

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem IsDScale.mono (hE : IsDScale a E) {q q' : ℚ} (h : q ≤ q') : E q ⊆ E q' := hE.2.1 h

theorem IsDScale.sub_int (hirr : IrrBetween a b) (hE : IsDScale a E) {q q' : ℚ} (h : q < q') :
    E q ⊆ interior (E q') := by
  by_cases h1 : q < 1
  · by_cases h0 : 0 < q'
    · exact IsDElt.subset_interior hirr (hE.1 q) (hE.1 q') (hE.mono h.le) (hE.2.2.1 q q' h h1 h0)
    · rw [hE.2.2.2.1 q (by push_neg at h0; exact h.le.trans h0)]; exact empty_subset _
  · rw [hE.2.2.2.2.1 q' (by push_neg at h1; exact h1.trans h.le), interior_univ]
    exact subset_univ _

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem IsDScale.a_mem (hE : IsDScale a E) {q : ℚ} (h : 0 < q) : a ∈ E q := by
  refine (hE.1 q).2.2 ?_
  rw [nonempty_iff_ne_empty]
  intro he
  exact hE.2.2.1 0 q h zero_lt_one h (by rw [he, hE.2.2.2.1 0 le_rfl])

omit [ConnectedSpace Y] in
theorem IsDScale.b_not_mem (hirr : IrrBetween a b) (hE : IsDScale a E) {q : ℚ} (h : q < 1) :
    b ∉ E q :=
  (hE.1 q).not_mem_b hirr (fun hu => hE.2.2.1 q 1 h h zero_lt_one
    (by rw [hu, hE.2.2.2.2.1 1 le_rfl]))

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem IsDScale.pos_of_mem (hE : IsDScale a E) {q : ℚ} {y : Y} (hy : y ∈ E q) : 0 < q := by
  by_contra h
  push_neg at h
  rw [hE.2.2.2.1 q h] at hy; exact hy

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scale_nonempty (hE : IsDScale a E) (y : Y) :
    ((fun q : ℚ => (q : ℝ)) '' {q | y ∈ E q}).Nonempty :=
  ⟨1, 1, by simp [hE.2.2.2.2.1 1 le_rfl], by simp⟩

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scale_bdd (hE : IsDScale a E) (y : Y) :
    BddBelow ((fun q : ℚ => (q : ℝ)) '' {q | y ∈ E q}) :=
  ⟨0, by rintro _ ⟨q, hq, rfl⟩; show (0 : ℝ) ≤ (q : ℝ); exact_mod_cast (hE.pos_of_mem hq).le⟩

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scaleFun_le (hE : IsDScale a E) {y : Y} {q : ℚ} (hy : y ∈ E q) : scaleFun E y ≤ q :=
  csInf_le (scale_bdd hE y) ⟨q, hy, rfl⟩

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scaleFun_nonneg (hE : IsDScale a E) (y : Y) : 0 ≤ scaleFun E y :=
  le_csInf (scale_nonempty hE y) (by
    rintro _ ⟨q, hq, rfl⟩; show (0 : ℝ) ≤ (q : ℝ); exact_mod_cast (hE.pos_of_mem hq).le)

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scaleFun_le_one (hE : IsDScale a E) (y : Y) : scaleFun E y ≤ 1 := by
  have := scaleFun_le hE (q := 1) (y := y) (by rw [hE.2.2.2.2.1 1 le_rfl]; exact mem_univ _)
  exact_mod_cast this

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scaleFun_lt_iff (hE : IsDScale a E) {y : Y} {t : ℝ} :
    scaleFun E y < t ↔ ∃ q : ℚ, (q : ℝ) < t ∧ y ∈ E q := by
  constructor
  · intro h
    obtain ⟨_, ⟨q, hq, rfl⟩, hlt⟩ := (csInf_lt_iff (scale_bdd hE y) (scale_nonempty hE y)).1 h
    exact ⟨q, hlt, hq⟩
  · rintro ⟨q, hqt, hy⟩
    exact (scaleFun_le hE hy).trans_lt hqt

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem lt_scaleFun_iff (hE : IsDScale a E) {y : Y} {t : ℝ} :
    t < scaleFun E y ↔ ∃ q : ℚ, t < q ∧ y ∉ E q := by
  constructor
  · intro h
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
    exact ⟨q, h1, fun hy => absurd (scaleFun_le hE hy) (not_le.2 h2)⟩
  · rintro ⟨q, hq, hy⟩
    refine lt_of_lt_of_le hq (le_csInf (scale_nonempty hE y) ?_)
    rintro _ ⟨q', hq', rfl⟩
    by_contra h
    push_neg at h
    exact hy (hE.mono (le_of_lt (by exact_mod_cast h)) hq')

omit [CompactSpace Y] [ConnectedSpace Y] in
theorem scaleFun_eq_iff (hE : IsDScale a E) {y : Y} {t : ℝ} :
    scaleFun E y = t ↔ (∀ q : ℚ, t < q → y ∈ E q) ∧ (∀ q : ℚ, (q : ℝ) < t → y ∉ E q) := by
  constructor
  · rintro rfl
    refine ⟨fun q hq => ?_, fun q hq hy => ?_⟩
    · by_contra hy
      exact lt_irrefl _ ((lt_scaleFun_iff hE).2 ⟨q, hq, hy⟩)
    · exact lt_irrefl _ ((scaleFun_lt_iff hE).2 ⟨q, hq, hy⟩)
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ ?_
    · by_contra h
      push_neg at h
      obtain ⟨q, hq, hy⟩ := (lt_scaleFun_iff hE).1 h
      exact hy (h1 q hq)
    · by_contra h
      push_neg at h
      obtain ⟨q, hq, hy⟩ := (scaleFun_lt_iff hE).1 h
      exact h2 q hq hy

theorem continuous_scaleFun (hirr : IrrBetween a b) (hE : IsDScale a E) :
    Continuous (scaleFun E) := by
  refine continuous_of_Iio_Ioi _ (fun t => ?_) (fun t => ?_)
  · have : scaleFun E ⁻¹' Iio t = ⋃ q : ℚ, ⋃ (_ : (q : ℝ) < t), interior (E q) := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_iUnion, exists_prop]
      constructor
      · intro h
        obtain ⟨q, hq, hy⟩ := (scaleFun_lt_iff hE).1 h
        obtain ⟨q'', h1, h2⟩ := exists_rat_btwn hq
        exact ⟨q'', h2, hE.sub_int hirr (by exact_mod_cast h1) hy⟩
      · rintro ⟨q, hq, hy⟩
        exact (scaleFun_lt_iff hE).2 ⟨q, hq, interior_subset hy⟩
    rw [this]
    exact isOpen_biUnion fun _ _ => isOpen_interior
  · have : scaleFun E ⁻¹' Ioi t = ⋃ q : ℚ, ⋃ (_ : t < (q : ℝ)), (E q)ᶜ := by
      ext y
      simp only [mem_preimage, mem_Ioi, mem_iUnion, exists_prop, mem_compl_iff]
      exact lt_scaleFun_iff hE
    rw [this]
    exact isOpen_biUnion fun q _ => (hE.1 q).isClosed.isOpen_compl

/-- A fibre of `scaleFun` is the directed intersection of the continua `cl (E q' − E q)`. -/
theorem isPreconnected_scaleFun_fibre (hirr : IrrBetween a b) (hE : IsDScale a E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    IsPreconnected {y | scaleFun E y = t} := by
  set ι := {p : ℚ × ℚ // (p.1 : ℝ) < t ∧ t < p.2}
  have hne : Nonempty ι := by
    obtain ⟨q, hq⟩ := exists_rat_lt t
    obtain ⟨q', hq'⟩ := exists_rat_gt t
    exact ⟨⟨(q, q'), hq, hq'⟩⟩
  set K : ι → Set Y := fun p => closure (E p.1.2 \ E p.1.1)
  have heq : {y | scaleFun E y = t} = ⋂ p, K p := by
    ext y
    simp only [mem_setOf_eq, mem_iInter]
    rw [scaleFun_eq_iff hE]
    constructor
    · rintro ⟨h1, h2⟩ p
      exact subset_closure ⟨h1 _ p.2.2, h2 _ p.2.1⟩
    · intro h
      refine ⟨fun q hq => ?_, fun q hq hy => ?_⟩
      · obtain ⟨q₀, hq₀⟩ := exists_rat_lt t
        exact closure_minimal diff_subset (hE.1 q).isClosed (h ⟨(q₀, q), hq₀, hq⟩)
      · obtain ⟨q'', h1, h2⟩ := exists_rat_btwn hq
        obtain ⟨q', hq'⟩ := exists_rat_gt t
        have := h ⟨(q'', q'), h2, hq'⟩
        have hsub : closure (E q' \ E q'') ⊆ closure (E q'')ᶜ :=
          closure_mono (diff_subset_compl _ _)
        have := hsub this
        rw [closure_compl] at this
        exact this (hE.sub_int hirr (by exact_mod_cast h1) hy)
  rw [heq]
  refine isPreconnected_iInter_directed K ?_ (fun _ => isClosed_closure) (fun p => ?_)
  · intro p p'
    refine ⟨⟨(max p.1.1 p'.1.1, min p.1.2 p'.1.2), ?_, ?_⟩, ?_, ?_⟩
    · simp only [Rat.cast_max]; exact max_lt p.2.1 p'.2.1
    · simp only [Rat.cast_min]; exact lt_min p.2.2 p'.2.2
    · exact closure_mono (diff_subset_diff (hE.mono (min_le_left _ _))
        (hE.mono (le_max_left _ _)))
    · exact closure_mono (diff_subset_diff (hE.mono (min_le_right _ _))
        (hE.mono (le_max_right _ _)))
  · have hlt : p.1.1 < p.1.2 := by exact_mod_cast p.2.1.trans p.2.2
    have h1 : p.1.1 < 1 := by exact_mod_cast p.2.1.trans_le ht.2
    have h0 : 0 < p.1.2 := by exact_mod_cast ht.1.trans_lt p.2.2
    exact (IsDElt.closure_diff hirr (hE.1 _) (hE.1 _) (hE.mono hlt.le)
      (hE.2.2.1 _ _ hlt h1 h0)).2.isPreconnected

/-- The fibres of `scaleFun` have empty interior. -/
theorem interior_scaleFun_fibre (hirr : IrrBetween a b) (hE : IsDScale a E) (t : ℝ) :
    interior {y | scaleFun E y = t} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro u hu
  set U := interior {y | scaleFun E y = t}
  have hUsub : U ⊆ {y | scaleFun E y = t} := interior_subset
  have hUfib : ∀ y ∈ U, scaleFun E y = t := fun y hy => hUsub hy
  set Lm := ⋃ q : ℚ, ⋃ (_ : (q : ℝ) < t), E q with hLm
  set Dm := closure Lm with hDm
  set Dp := ⋂ q : ℚ, ⋂ (_ : t < (q : ℝ)), E q with hDp
  have ht0 : 0 ≤ t := hUfib u hu ▸ scaleFun_nonneg hE u
  have hLm_int : Lm ⊆ interior Dp := by
    intro y hy
    simp only [hLm, mem_iUnion] at hy
    obtain ⟨q, hq, hy⟩ := hy
    obtain ⟨q'', h1, h2⟩ := exists_rat_btwn hq
    refine interior_mono ?_ (hE.sub_int hirr (by exact_mod_cast h1) hy)
    intro z hz
    simp only [hDp, mem_iInter]
    intro q' hq'
    exact hE.mono (by exact_mod_cast (h2.trans hq').le) hz
  -- `Dm ∈ D`
  have hDm_elt : IsDElt a Dm := by
    refine ⟨Subset.antisymm (closure_minimal interior_subset isClosed_closure) (closure_mono ?_),
      ?_, ?_⟩
    · intro y hy
      simp only [hLm, mem_iUnion] at hy
      obtain ⟨q, hq, hy⟩ := hy
      obtain ⟨q'', h1, h2⟩ := exists_rat_btwn hq
      refine interior_mono ?_ (hE.sub_int hirr (by exact_mod_cast h1) hy)
      exact (subset_iUnion₂ (s := fun (q : ℚ) (_ : (q : ℝ) < t) => E q) q'' h2).trans subset_closure
    · refine IsPreconnected.closure (isPreconnected_of_forall a fun y hy => ?_)
      simp only [hLm, mem_iUnion] at hy
      obtain ⟨q, hq, hy⟩ := hy
      exact ⟨E q, subset_iUnion₂ (s := fun (q : ℚ) (_ : (q : ℝ) < t) => E q) q hq,
        hE.a_mem (hE.pos_of_mem hy), hy, (hE.1 q).2.1⟩
    · intro hne
      have : Lm.Nonempty := by
        by_contra h
        rw [not_nonempty_iff_eq_empty] at h
        rw [hDm, h, closure_empty] at hne
        exact not_nonempty_empty hne
      obtain ⟨y, hy⟩ := this
      simp only [hLm, mem_iUnion] at hy
      obtain ⟨q, hq, hy⟩ := hy
      exact subset_closure (mem_iUnion₂.2 ⟨q, hq, hE.a_mem (hE.pos_of_mem hy)⟩)
  -- `Dp` is a continuum containing `a`, with `u` interior to it
  have hDp_cl : IsClosed Dp := isClosed_iInter fun q => isClosed_iInter fun _ => (hE.1 q).isClosed
  have haDp : a ∈ Dp := by
    simp only [hDp, mem_iInter]
    intro q hq
    exact hE.a_mem (by exact_mod_cast ht0.trans_lt hq)
  have hDp_pre : IsPreconnected Dp := by
    have : Dp = ⋂ q : {q : ℚ // t < q}, E q.1 := by
      ext y; simp [hDp]
    rw [this]
    haveI : Nonempty {q : ℚ // t < q} := by
      obtain ⟨q, hq⟩ := exists_rat_gt t; exact ⟨⟨q, hq⟩⟩
    refine isPreconnected_iInter_directed _ ?_ (fun q => (hE.1 q.1).isClosed)
      (fun q => (hE.1 q.1).2.1)
    intro q q'
    refine ⟨⟨min q.1 q'.1, ?_⟩, hE.mono (min_le_left _ _), hE.mono (min_le_right _ _)⟩
    simp only [Rat.cast_min]; exact lt_min q.2 q'.2
  have hDp_cont : Fold.Q78.IsContinuum Dp := ⟨hDp_cl.isCompact, ⟨a, haDp⟩, hDp_pre⟩
  have hUDp : U ⊆ interior Dp := by
    refine interior_mono fun y hy => ?_
    simp only [hDp, mem_iInter]
    exact fun q hq => ((scaleFun_eq_iff hE).1 hy).1 q hq
  set W := closure (interior Dp) with hW
  have hW_elt : IsDElt a W := isDElt_closure_interior hirr hDp_cont haDp ⟨u, hUDp hu⟩
  have hDmW : Dm ⊆ W := closure_mono hLm_int
  have huW : u ∈ W := subset_closure (hUDp hu)
  have huDm : u ∉ Dm := by
    have hdis : Disjoint U Lm := by
      rw [disjoint_left]
      intro y hyU hyL
      simp only [hLm, mem_iUnion] at hyL
      obtain ⟨q, hq, hy⟩ := hyL
      exact ((scaleFun_eq_iff hE).1 (hUfib y hyU)).2 q hq hy
    exact fun h => disjoint_left.1 (hdis.closure_right isOpen_interior) hu h
  have hne : Dm ≠ W := fun h => huDm (h ▸ huW)
  have hWDp : W ⊆ Dp := closure_minimal interior_subset hDp_cl
  -- every member of the scale strictly between `Dm` and `W` has index `t`
  have idx : ∀ q : ℚ, Dm ⊆ E q → E q ≠ Dm → E q ⊆ W → E q ≠ W → (q : ℝ) = t := by
    intro q h1 h2 h3 h4
    rcases lt_trichotomy (q : ℝ) t with h | h | h
    · exact (h2 (Subset.antisymm (subset_closure.trans' (subset_iUnion₂
        (s := fun (q : ℚ) (_ : (q : ℝ) < t) => E q) q h)) h1)).elim
    · exact h
    · refine (h4 (Subset.antisymm h3 (hWDp.trans ?_))).elim
      exact iInter₂_subset (s := fun (q : ℚ) (_ : t < (q : ℝ)) => E q) q h
  obtain ⟨q₁, h11, h12, h13, h14⟩ := hE.2.2.2.2.2 Dm W hDm_elt hW_elt hDmW hne
  obtain ⟨q₂, h21, h22, h23, h24⟩ := hE.2.2.2.2.2 (E q₁) W (hE.1 q₁) hW_elt h13 h14
  have e1 := idx q₁ h11 h12 h13 h14
  have e2 := idx q₂ (h11.trans h21) (fun h => h12 (Subset.antisymm (h ▸ h21) h11)) h23 h24
  have : q₁ = q₂ := by exact_mod_cast e1.trans e2.symm
  exact h22 (this ▸ rfl)

/-- **From a scale to a type A′ map.** -/
theorem scaleMap_spec (hirr : IrrBetween a b) (hE : IsDScale a E) :
    ∃ k : Y → unitInterval, Continuous k ∧ Function.Surjective k ∧
      (∀ t, IsConnected (k ⁻¹' {t})) ∧ ∀ t, interior (k ⁻¹' {t}) = ∅ := by
  set k : Y → unitInterval := fun y => ⟨scaleFun E y, scaleFun_nonneg hE y, scaleFun_le_one hE y⟩
  have hk : Continuous k := (continuous_scaleFun hirr hE).subtype_mk _
  have hfib : ∀ t : unitInterval, k ⁻¹' {t} = {y | scaleFun E y = t} := by
    intro t; ext y
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, k, Subtype.ext_iff]
  have hsurj : Function.Surjective k := by
    have ha : k a = 0 := by
      refine Subtype.ext (le_antisymm ?_ (scaleFun_nonneg hE a))
      show scaleFun E a ≤ 0
      by_contra h
      push_neg at h
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
      exact absurd (scaleFun_le hE (hE.a_mem (by exact_mod_cast h1))) (not_le.2 h2)
    have hb : k b = 1 := by
      refine Subtype.ext (le_antisymm (scaleFun_le_one hE b) ?_)
      show (1 : ℝ) ≤ scaleFun E b
      by_contra h
      push_neg at h
      obtain ⟨q, hq, hy⟩ := (scaleFun_lt_iff hE).1 h
      exact hE.b_not_mem hirr (by exact_mod_cast hq) hy
    intro t
    have := intermediate_value_univ a b hk (show t ∈ Icc (k a) (k b) by
      rw [ha, hb]; exact ⟨t.2.1, t.2.2⟩)
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  refine ⟨k, hk, hsurj, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨y, hy⟩ := hsurj t; exact ⟨y, hy⟩
  · rw [hfib]; exact isPreconnected_scaleFun_fibre hirr hE ⟨t.2.1, t.2.2⟩
  · rw [hfib]; exact interior_scaleFun_fibre hirr hE t

end Map

end HPC.Hagopian
