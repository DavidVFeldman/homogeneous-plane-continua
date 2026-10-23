import HPC.Plane.StdChain

/-!
# Batch 129: polygonal sets

`IsPolygonal A`: `A` is a finite union of closed segments (degenerate segments, i.e. points,
allowed). This file is imported by `HPC/Plane/Tree67.lean`, so that the `janiszewski` field of
`PlaneFacts` can be stated for polygonal sets; it needs nothing beyond `Pt = ℝ × ℝ`.

Besides the basic closure properties, the file proves the polygonality lemma that the new proof of
`exists_theta_point` needs, in a general form that uses no Jordan curve theorem:
`isPolygonal_inter_closure_inter` — if `Γ₁`, `Γ₂` are polygonal and `W₁ ⊆ Γ₁ᶜ`, `W₂ ⊆ Γ₂ᶜ` are
*saturated* (a preconnected set missing `Γᵢ` and meeting `Wᵢ` lies in `Wᵢ`; e.g. any union of
components of `Γᵢᶜ`, such as `polyInterior Γᵢ`), then `Γ₁ ∩ closure (W₁ ∩ W₂)` is polygonal.

Proof: per segment `[a, b]` of `Γ₁`, parametrised by `f t = a + t • (b - a)`, let `T` be the set of
parameters `t ∈ [0, 1]` with `f t ∈ closure (W₁ ∩ W₂)`, and `F` the finite set of parameters
consisting of `0`, `1` and the infimum and supremum of `{t ∈ [0, 1] | f t ∈ σ}` for every segment
`σ` of `Γ₁` or `Γ₂`. At a parameter `t ∈ (0, 1) ∖ F`, every segment through `f t` contains a
nondegenerate piece of `[a, b]` around `f t`, hence lies on the line `L` of `[a, b]`; so a small ball
about `f t` meets `Γ₁ ∪ Γ₂` only on `L`, and on `L` only in `[a, b] ⊆ Γ₁`. The two open half-disks
are convex and miss `Γ₁ ∪ Γ₂`, so each lies in or misses `W₁` and in or misses `W₂`; if
`f t ∈ closure (W₁ ∩ W₂)` one of them lies in `W₁ ∩ W₂`, and its closure contains the whole chord.
So `T` is open (and closed) in each open interval between consecutive points of `F`, and
`T` is the union of the intervals `[α, β]` (`α ≤ β` in `F`) it contains.
-/

namespace HPC.Plane

open Set Metric Filter Topology

/-- A **polygonal set**: a finite union of closed segments, degenerate segments (points) allowed.
(Stated with pairs of points, so that it is literally `∃ S, A = graphSet S` for the `graphSet` of
`HPC/Plane/Cyc1.lean`, which is defined later in the import order.) -/
def IsPolygonal (A : Set Pt) : Prop := ∃ S : Finset (Pt × Pt), A = ⋃ s ∈ S, segment ℝ s.1 s.2

theorem isCompact_segment_pt (a b : Pt) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

theorem IsPolygonal.isCompact {A : Set Pt} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨S, rfl⟩ := h
  exact S.isCompact_biUnion fun s _ => isCompact_segment_pt _ _

theorem IsPolygonal.isClosed {A : Set Pt} (h : IsPolygonal A) : IsClosed A :=
  h.isCompact.isClosed

theorem IsPolygonal.union {A B : Set Pt} (hA : IsPolygonal A) (hB : IsPolygonal B) :
    IsPolygonal (A ∪ B) := by
  classical
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  exact ⟨S ∪ T, (Finset.set_biUnion_union S T _).symm⟩

theorem isPolygonal_empty : IsPolygonal (∅ : Set Pt) := ⟨∅, by simp⟩

theorem isPolygonal_segment (a b : Pt) : IsPolygonal (segment ℝ a b) := ⟨{(a, b)}, by simp⟩

theorem isPolygonal_singleton (a : Pt) : IsPolygonal ({a} : Set Pt) := by
  rw [← segment_same ℝ a]; exact isPolygonal_segment a a

/-- A finite union of polygonal sets is polygonal. -/
theorem isPolygonal_biUnion {ι : Type*} (s : Finset ι) {A : ι → Set Pt}
    (h : ∀ i ∈ s, IsPolygonal (A i)) : IsPolygonal (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolygonal_empty
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self _ _)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isPolygonal_iUnion_finset_of_pairs {S : Finset (Pt × Pt)} :
    IsPolygonal (⋃ s ∈ S, segment ℝ s.1 s.2) := ⟨S, rfl⟩

/-! ### The line through two points -/

/-- `crossG a b z = 0` iff `z` lies on the line through `a` and `b` (for `a ≠ b`). -/
def crossG (a b z : Pt) : ℝ := (b.1 - a.1) * (z.2 - a.2) - (b.2 - a.2) * (z.1 - a.1)

theorem continuous_crossG (a b : Pt) : Continuous (crossG a b) := by
  unfold crossG; fun_prop

/-- The parametrisation of the line through `a` and `b`. -/
def linePt (a b : Pt) (t : ℝ) : Pt := a + t • (b - a)

theorem continuous_linePt (a b : Pt) : Continuous (linePt a b) := by
  unfold linePt; fun_prop

theorem crossG_linePt (a b : Pt) (t : ℝ) : crossG a b (linePt a b t) = 0 := by
  simp only [crossG, linePt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem dist_linePt (a b : Pt) (s t : ℝ) :
    dist (linePt a b s) (linePt a b t) = |s - t| * ‖b - a‖ := by
  rw [dist_eq_norm, show linePt a b s - linePt a b t = (s - t) • (b - a) by
    simp only [linePt]; rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs]

theorem linePt_injective {a b : Pt} (hab : a ≠ b) : Function.Injective (linePt a b) := by
  intro s t h
  have h' := dist_linePt a b s t
  rw [h, dist_self] at h'
  have hn : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hab.symm)
  have : |s - t| = 0 := by
    rcases mul_eq_zero.1 h'.symm with h | h
    · exact h
    · exact absurd h hn
  linarith [abs_eq_zero.1 this]

/-- A point on the line through `a ≠ b` is `linePt a b s` for some `s`. -/
theorem exists_linePt_of_crossG {a b z : Pt} (hab : a ≠ b) (hz : crossG a b z = 0) :
    ∃ s, z = linePt a b s := by
  have hu : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h
    apply hab
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    exact Prod.ext (by linarith) (by linarith)
  refine ⟨((b.1 - a.1) * (z.1 - a.1) + (b.2 - a.2) * (z.2 - a.2)) /
    ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2), ?_⟩
  simp only [crossG] at hz
  refine Prod.ext ?_ ?_
  · simp only [linePt, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    linear_combination (-(b.2 - a.2)) * hz
  · simp only [linePt, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    field_simp
    linear_combination (b.1 - a.1) * hz

/-- A segment containing two distinct points of a line lies on it. -/
theorem crossG_eq_zero_of_two {a b c d q₁ q₂ : Pt} (h₁ : q₁ ∈ segment ℝ c d)
    (h₂ : q₂ ∈ segment ℝ c d) (hq : q₁ ≠ q₂) (hg₁ : crossG a b q₁ = 0) (hg₂ : crossG a b q₂ = 0)
    {z : Pt} (hz : z ∈ segment ℝ c d) : crossG a b z = 0 := by
  have key : ∀ {u v : ℝ}, u + v = 1 → crossG a b (u • c + v • d) =
      u * crossG a b c + v * crossG a b d := by
    intro u v huv
    have : u = 1 - v := by linarith
    subst this
    simp only [crossG, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  obtain ⟨u₁, v₁, -, -, huv₁, rfl⟩ := h₁
  obtain ⟨u₂, v₂, -, -, huv₂, rfl⟩ := h₂
  obtain ⟨u, v, -, -, huv, rfl⟩ := hz
  rw [key huv₁] at hg₁
  rw [key huv₂] at hg₂
  rw [key huv]
  have hv : v₁ ≠ v₂ := by
    rintro rfl
    exact hq (by rw [show u₁ = u₂ by linarith])
  have hcd : crossG a b c = crossG a b d := by
    have : (v₁ - v₂) * (crossG a b d - crossG a b c) = 0 := by
      rw [show u₁ = 1 - v₁ by linarith] at hg₁
      rw [show u₂ = 1 - v₂ by linarith] at hg₂
      linear_combination hg₁ - hg₂
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith) hv
    · linarith
  have hc : crossG a b c = 0 := by
    rw [← hcd] at hg₁
    have : (u₁ + v₁) * crossG a b c = 0 := by linear_combination hg₁
    rwa [huv₁, one_mul] at this
  rw [← hcd, hc]; ring

/-- The image of a parameter interval is a segment. -/
theorem linePt_image_Icc (a b : Pt) {α β : ℝ} (h : α ≤ β) :
    linePt a b '' Icc α β = segment ℝ (linePt a b α) (linePt a b β) := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
    rcases eq_or_lt_of_le h with h' | h'
    · subst h'
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        rw [show s = α by linarith]; simp⟩
    · refine ⟨(s - α) / (β - α), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      simp only [linePt]
      rw [show a + β • (b - a) - (a + α • (b - a)) = (β - α) • (b - a) by rw [sub_smul]; abel,
        smul_smul, div_mul_cancel₀ _ (by linarith : β - α ≠ 0), sub_smul]
      abel
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨α + θ * (β - α), ⟨by nlinarith, by nlinarith⟩, ?_⟩
    simp only [linePt]
    rw [show a + β • (b - a) - (a + α • (b - a)) = (β - α) • (b - a) by rw [sub_smul]; abel,
      smul_smul, add_smul, mul_comm θ]
    abel

/-! ### The polygonality lemma -/

/-- A set `W` is **saturated** for `Γ` if `W ⊆ Γᶜ` and every preconnected set missing `Γ` that
meets `W` lies in `W` (e.g. any union of components of `Γᶜ`). -/
def IsSaturated (Γ W : Set Pt) : Prop :=
  W ⊆ Γᶜ ∧ ∀ S : Set Pt, IsPreconnected S → S ⊆ Γᶜ → (S ∩ W).Nonempty → S ⊆ W

/-- The parameters of the points of a segment `σ` on `[a, b]`. -/
def segParams (a b : Pt) (σ : Pt × Pt) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ linePt a b t ∈ segment ℝ σ.1 σ.2}

/-- The special parameters. -/
noncomputable def specialParams (a b : Pt) (S : Finset (Pt × Pt)) : Finset ℝ :=
  {0, 1} ∪ S.image (fun σ => sInf (segParams a b σ)) ∪ S.image (fun σ => sSup (segParams a b σ))

theorem zero_mem_specialParams (a b : Pt) (S : Finset (Pt × Pt)) : (0 : ℝ) ∈ specialParams a b S := by
  simp [specialParams]

theorem one_mem_specialParams (a b : Pt) (S : Finset (Pt × Pt)) : (1 : ℝ) ∈ specialParams a b S := by
  simp [specialParams]

/-- At a non-special parameter, every segment of `S` through the point lies on the line. -/
theorem crossG_of_not_special {a b : Pt} (hab : a ≠ b) {S : Finset (Pt × Pt)} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (htF : t ∉ specialParams a b S) {σ : Pt × Pt} (hσ : σ ∈ S)
    (hp : linePt a b t ∈ segment ℝ σ.1 σ.2) {z : Pt} (hz : z ∈ segment ℝ σ.1 σ.2) :
    crossG a b z = 0 := by
  have hP : t ∈ segParams a b σ := ⟨Ioo_subset_Icc_self ht, hp⟩
  have hbdd : BddBelow (segParams a b σ) := ⟨0, fun s hs => hs.1.1⟩
  have hbdd' : BddAbove (segParams a b σ) := ⟨1, fun s hs => hs.1.2⟩
  have hlo : sInf (segParams a b σ) < t := by
    refine lt_of_le_of_ne (csInf_le hbdd hP) fun h => htF ?_
    simp only [specialParams, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨σ, hσ, h⟩)
  have hhi : t < sSup (segParams a b σ) := by
    refine lt_of_le_of_ne (le_csSup hbdd' hP) fun h => htF ?_
    simp only [specialParams, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨σ, hσ, h.symm⟩
  obtain ⟨x, hx, hxt⟩ := exists_lt_of_csInf_lt ⟨t, hP⟩ hlo
  obtain ⟨y, hy, hyt⟩ := exists_lt_of_lt_csSup ⟨t, hP⟩ hhi
  refine crossG_eq_zero_of_two hx.2 hy.2 (fun h => ?_) (crossG_linePt a b x)
    (crossG_linePt a b y) hz
  have := linePt_injective hab h
  linarith

/-- Points of the closed segment are the `linePt` of `[0, 1]`. -/
theorem mem_segment_iff_linePt {a b z : Pt} :
    z ∈ segment ℝ a b ↔ ∃ t ∈ Icc (0 : ℝ) 1, linePt a b t = z := by
  rw [segment_eq_image']; rfl

/-- On the line, inside a ball, a point is in the closure of both open half-disks. -/
theorem mem_closure_halfDisks {a b : Pt} (hab : a ≠ b) {p z : Pt} {ρ : ℝ} (hz : z ∈ ball p ρ)
    (hcz : crossG a b z = 0) :
    z ∈ closure (ball p ρ ∩ {w | 0 < crossG a b w}) ∧
      z ∈ closure (ball p ρ ∩ {w | crossG a b w < 0}) := by
  have hu : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_contra h
    apply hab
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    exact Prod.ext (by linarith) (by linarith)
  set n : Pt := (-(b.2 - a.2), b.1 - a.1) with hn
  have hcomp : ∀ c : ℝ, crossG a b (z + c • n) = c * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    intro c
    simp only [crossG, hn, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hcz ⊢
    linear_combination hcz
  have ht : Tendsto (fun c : ℝ => z + c • n) (𝓝 0) (𝓝 z) := by
    have : Continuous (fun c : ℝ => z + c • n) := by fun_prop
    simpa using this.tendsto 0
  have hb : ∀ᶠ c in 𝓝 (0 : ℝ), z + c • n ∈ ball p ρ := ht.eventually (isOpen_ball.mem_nhds hz)
  constructor
  · refine mem_closure_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with c hc hc0
    exact ⟨hc, by rw [mem_setOf_eq, hcomp]; exact mul_pos hc0 hu⟩
  · refine mem_closure_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Iio 0))) ?_
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with c hc hc0
    exact ⟨hc, by rw [mem_setOf_eq, hcomp]; exact mul_neg_of_neg_of_pos hc0 hu⟩

/-- The open half-planes are convex. -/
theorem convex_crossG_pos (a b : Pt) : Convex ℝ {w : Pt | 0 < crossG a b w} := by
  have hlin : IsLinearMap ℝ (fun z : Pt => (b.1 - a.1) * z.2 - (b.2 - a.2) * z.1) :=
    ⟨fun x y => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c x => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  convert convex_halfSpace_gt hlin ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) using 1
  ext z; simp only [crossG, mem_setOf_eq]; constructor <;> intro h <;> linarith

theorem convex_crossG_neg (a b : Pt) : Convex ℝ {w : Pt | crossG a b w < 0} := by
  have hlin : IsLinearMap ℝ (fun z : Pt => (b.1 - a.1) * z.2 - (b.2 - a.2) * z.1) :=
    ⟨fun x y => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c x => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  convert convex_halfSpace_lt hlin ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) using 1
  ext z; simp only [crossG, mem_setOf_eq]; constructor <;> intro h <;> linarith

/-- **The local step.** At a non-special parameter `t ∈ (0, 1)`, if `linePt a b t` lies in
`closure (W₁ ∩ W₂)`, so do the points at all nearby parameters. -/
theorem eventually_mem_closure_of_not_special {a b : Pt} (hab : a ≠ b) {S₁ S₂ : Finset (Pt × Pt)}
    (hS : (a, b) ∈ S₁) {W₁ W₂ : Set Pt}
    (hW₁ : IsSaturated (⋃ s ∈ S₁, segment ℝ s.1 s.2) W₁)
    (hW₂ : IsSaturated (⋃ s ∈ S₂, segment ℝ s.1 s.2) W₂) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (htF : t ∉ specialParams a b (S₁ ∪ S₂)) (hK : linePt a b t ∈ closure (W₁ ∩ W₂)) :
    ∀ᶠ t' in 𝓝 t, linePt a b t' ∈ closure (W₁ ∩ W₂) := by
  classical
  set p := linePt a b t with hp
  set N := ⋂ σ ∈ (S₁ ∪ S₂).filter (fun σ => p ∉ segment ℝ σ.1 σ.2), (segment ℝ σ.1 σ.2)ᶜ
  have hNo : IsOpen N :=
    isOpen_biInter_finset fun σ _ => (isCompact_segment_pt _ _).isClosed.isOpen_compl
  have hpN : p ∈ N := mem_iInter₂.2 fun σ hσ => (Finset.mem_filter.1 hσ).2
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 hNo p hpN
  have hn : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  set ρ := min ρ₀ (min t (1 - t) * ‖b - a‖) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (mul_pos (lt_min ht.1 (by linarith [ht.2])) hn)
  have hline : ∀ z ∈ ball p ρ, ∀ σ ∈ S₁ ∪ S₂, z ∈ segment ℝ σ.1 σ.2 → crossG a b z = 0 := by
    intro z hz σ hσ hzσ
    by_cases hpσ : p ∈ segment ℝ σ.1 σ.2
    · exact crossG_of_not_special hab ht htF hσ hpσ hzσ
    · exfalso
      have := hball (ball_subset_ball (min_le_left _ _) hz)
      exact (mem_iInter₂.1 this σ (Finset.mem_filter.2 ⟨hσ, hpσ⟩)) hzσ
  have hseg : ∀ z ∈ ball p ρ, crossG a b z = 0 → z ∈ ⋃ s ∈ S₁, segment ℝ s.1 s.2 := by
    intro z hz hcz
    obtain ⟨s, rfl⟩ := exists_linePt_of_crossG hab hcz
    have hd : |s - t| * ‖b - a‖ < min t (1 - t) * ‖b - a‖ := by
      rw [← dist_linePt]; exact (mem_ball.1 hz).trans_le (min_le_right _ _)
    have hst : |s - t| < min t (1 - t) := lt_of_mul_lt_mul_right hd hn.le
    have h1 := abs_lt.1 hst
    refine mem_iUnion₂.2 ⟨(a, b), hS, mem_segment_iff_linePt.2 ⟨s, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [min_le_left t (1 - t)]
    · linarith [min_le_right t (1 - t)]
  have havoid : ∀ (D : Set Pt), D ⊆ ball p ρ → (∀ z ∈ D, crossG a b z ≠ 0) →
      D ⊆ (⋃ s ∈ S₁, segment ℝ s.1 s.2)ᶜ ∧ D ⊆ (⋃ s ∈ S₂, segment ℝ s.1 s.2)ᶜ := by
    intro D hD hD0
    constructor
    · intro z hz hzΓ
      obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hzΓ
      exact hD0 z hz (hline z (hD hz) σ (Finset.mem_union_left _ hσ) hzσ)
    · intro z hz hzΓ
      obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hzΓ
      exact hD0 z hz (hline z (hD hz) σ (Finset.mem_union_right _ hσ) hzσ)
  have hfinal : ∀ (D : Set Pt), D ⊆ W₁ ∩ W₂ →
      (∀ z ∈ ball p ρ, crossG a b z = 0 → z ∈ closure D) →
      ∀ᶠ t' in 𝓝 t, linePt a b t' ∈ closure (W₁ ∩ W₂) := by
    intro D hDW hcl
    filter_upwards [(continuous_linePt a b).continuousAt.eventually
      (isOpen_ball.mem_nhds (mem_ball_self hρ))] with t' ht'
    exact closure_mono hDW (hcl _ ht' (crossG_linePt a b t'))
  obtain ⟨w, hwW, hwd⟩ := Metric.mem_closure_iff.1 hK ρ hρ
  have hwb : w ∈ ball p ρ := by rw [mem_ball, dist_comm]; exact hwd
  have hw0 : crossG a b w ≠ 0 := fun h => hW₁.1 hwW.1 (hseg w hwb h)
  rcases lt_or_gt_of_ne hw0 with hneg | hpos
  · set D := ball p ρ ∩ {w | crossG a b w < 0}
    have hDc : IsPreconnected D := ((convex_ball p ρ).inter (convex_crossG_neg a b)).isPreconnected
    obtain ⟨hD1, hD2⟩ := havoid D inter_subset_left fun z hz => hz.2.ne
    have hsub : D ⊆ W₁ ∩ W₂ := fun z hz =>
      ⟨hW₁.2 D hDc hD1 ⟨w, ⟨hwb, hneg⟩, hwW.1⟩ hz, hW₂.2 D hDc hD2 ⟨w, ⟨hwb, hneg⟩, hwW.2⟩ hz⟩
    exact hfinal D hsub fun z hz hcz => (mem_closure_halfDisks hab hz hcz).2
  · set D := ball p ρ ∩ {w | 0 < crossG a b w}
    have hDc : IsPreconnected D := ((convex_ball p ρ).inter (convex_crossG_pos a b)).isPreconnected
    obtain ⟨hD1, hD2⟩ := havoid D inter_subset_left fun z hz => hz.2.ne'
    have hsub : D ⊆ W₁ ∩ W₂ := fun z hz =>
      ⟨hW₁.2 D hDc hD1 ⟨w, ⟨hwb, hpos⟩, hwW.1⟩ hz, hW₂.2 D hDc hD2 ⟨w, ⟨hwb, hpos⟩, hwW.2⟩ hz⟩
    exact hfinal D hsub fun z hz hcz => (mem_closure_halfDisks hab hz hcz).1

/-- **Polygonality of one segment's part.** -/
theorem isPolygonal_segment_inter_closure {a b : Pt} {S₁ S₂ : Finset (Pt × Pt)}
    (hS : (a, b) ∈ S₁) {W₁ W₂ : Set Pt}
    (hW₁ : IsSaturated (⋃ s ∈ S₁, segment ℝ s.1 s.2) W₁)
    (hW₂ : IsSaturated (⋃ s ∈ S₂, segment ℝ s.1 s.2) W₂) :
    IsPolygonal (segment ℝ a b ∩ closure (W₁ ∩ W₂)) := by
  classical
  set K := closure (W₁ ∩ W₂) with hK
  by_cases hab : a = b
  · subst hab
    rw [segment_same]
    by_cases ha : a ∈ K
    · rw [singleton_inter_of_mem ha]; exact isPolygonal_singleton a
    · rw [singleton_inter_of_notMem ha]; exact isPolygonal_empty
  set F := specialParams a b (S₁ ∪ S₂) with hF
  set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ linePt a b t ∈ K} with hTdef
  have hTc : IsClosed T :=
    isClosed_Icc.inter (isClosed_closure.preimage (continuous_linePt a b))
  set Q := (F ×ˢ F).filter (fun q => q.1 ≤ q.2 ∧ Icc q.1 q.2 ⊆ T) with hQ
  have hT : T = ⋃ q ∈ Q, Icc q.1 q.2 := by
    apply subset_antisymm
    · intro t ht
      by_cases htF : t ∈ F
      · exact mem_iUnion₂.2 ⟨(t, t), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨htF, htF⟩,
          le_rfl, by intro s hs; rw [show s = t by linarith [hs.1, hs.2]]; exact ht⟩,
          ⟨le_rfl, le_rfl⟩⟩
      have h0 : t ≠ 0 := fun h => htF (h ▸ zero_mem_specialParams a b _)
      have h1 : t ≠ 1 := fun h => htF (h ▸ one_mem_specialParams a b _)
      have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1.1 (Ne.symm h0),
        lt_of_le_of_ne ht.1.2 h1⟩
      have hL : (F.filter (· < t)).Nonempty :=
        ⟨0, Finset.mem_filter.2 ⟨zero_mem_specialParams a b _, ht01.1⟩⟩
      have hR : (F.filter (t < ·)).Nonempty :=
        ⟨1, Finset.mem_filter.2 ⟨one_mem_specialParams a b _, ht01.2⟩⟩
      set α := (F.filter (· < t)).max' hL with hα
      set β := (F.filter (t < ·)).min' hR with hβ
      have hαm := Finset.mem_filter.1 (Finset.max'_mem _ hL)
      have hβm := Finset.mem_filter.1 (Finset.min'_mem _ hR)
      have hα0 : 0 ≤ α := Finset.le_max' _ 0
        (Finset.mem_filter.2 ⟨zero_mem_specialParams a b _, ht01.1⟩)
      have hβ1 : β ≤ 1 := Finset.min'_le _ 1
        (Finset.mem_filter.2 ⟨one_mem_specialParams a b _, ht01.2⟩)
      have hgap : ∀ s ∈ Ioo α β, s ∉ F := by
        intro s hs hsF
        rcases lt_trichotomy s t with h | h | h
        · exact absurd (Finset.le_max' _ s (Finset.mem_filter.2 ⟨hsF, h⟩)) (not_le.2 hs.1)
        · exact htF (h ▸ hsF)
        · exact absurd (Finset.min'_le _ s (Finset.mem_filter.2 ⟨hsF, h⟩)) (not_le.2 hs.2)
      set u := Ioo α β ∩ {s | linePt a b s ∈ K} with hu
      have huo : IsOpen u := by
        rw [isOpen_iff_mem_nhds]
        intro s hs
        have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hα0.trans_lt hs.1.1, hs.1.2.trans_le hβ1⟩
        exact inter_mem (isOpen_Ioo.mem_nhds hs.1)
          (eventually_mem_closure_of_not_special hab hS hW₁ hW₂ hs01 (hgap s hs.1) hs.2)
      have hsub : Ioo α β ⊆ u := isPreconnected_Ioo.subset_of_closure_inter_subset huo
        ⟨t, ⟨hαm.2, hβm.2⟩, ⟨hαm.2, hβm.2⟩, ht.2⟩ (fun s ⟨hs, hs'⟩ =>
          ⟨hs', (isClosed_closure.preimage (continuous_linePt a b)).closure_subset
            (closure_mono inter_subset_right hs)⟩)
      have hIoo : Ioo α β ⊆ T := fun s hs =>
        ⟨⟨(hα0.trans hs.1.le), hs.2.le.trans hβ1⟩, (hsub hs).2⟩
      have hαβ : α < β := hαm.2.trans hβm.2
      refine mem_iUnion₂.2 ⟨(α, β), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hαm.1, hβm.1⟩,
        hαβ.le, ?_⟩, ⟨hαm.2.le, hβm.2.le⟩⟩
      rw [← closure_Ioo hαβ.ne]
      exact hTc.closure_subset_iff.2 hIoo
    · exact iUnion₂_subset fun q hq => (Finset.mem_filter.1 hq).2.2
  have himg : segment ℝ a b ∩ K = linePt a b '' T := by
    ext z
    constructor
    · rintro ⟨hz, hzK⟩
      obtain ⟨t, ht, rfl⟩ := mem_segment_iff_linePt.1 hz
      exact ⟨t, ⟨ht, hzK⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htK⟩, rfl⟩
      exact ⟨mem_segment_iff_linePt.2 ⟨t, ht, rfl⟩, htK⟩
  rw [himg, hT, image_iUnion₂]
  refine isPolygonal_biUnion Q fun q hq => ?_
  rw [linePt_image_Icc a b (Finset.mem_filter.1 hq).2.1]
  exact isPolygonal_segment _ _

/-- **`Γ₁ ∩ closure (W₁ ∩ W₂)` is polygonal** for polygonal `Γ₁`, `Γ₂` and saturated `W₁`, `W₂`.
No Jordan curve theorem is used. -/
theorem isPolygonal_inter_closure_inter {Γ₁ Γ₂ W₁ W₂ : Set Pt} (h₁ : IsPolygonal Γ₁)
    (h₂ : IsPolygonal Γ₂) (hW₁ : IsSaturated Γ₁ W₁) (hW₂ : IsSaturated Γ₂ W₂) :
    IsPolygonal (Γ₁ ∩ closure (W₁ ∩ W₂)) := by
  obtain ⟨S₁, rfl⟩ := h₁
  obtain ⟨S₂, rfl⟩ := h₂
  rw [iUnion₂_inter]
  exact isPolygonal_biUnion S₁ fun s hs =>
    isPolygonal_segment_inter_closure (a := s.1) (b := s.2) hs hW₁ hW₂

/-! ### Intersections -/

theorem linePt_affine (a b : Pt) {s t u v : ℝ} (huv : u + v = 1) :
    linePt a b (u * s + v * t) = u • linePt a b s + v • linePt a b t := by
  have h : a = (u + v) • a := by rw [huv, one_smul]
  simp only [linePt, smul_add, smul_smul, add_smul]
  nth_rewrite 1 [h]
  rw [add_smul]; abel

theorem convex_segParams (a b : Pt) (σ : Pt × Pt) : Convex ℝ (segParams a b σ) := by
  intro s hs t ht u v hu hv huv
  refine ⟨(convex_Icc (0 : ℝ) 1) hs.1 ht.1 hu hv huv, ?_⟩
  simp only [smul_eq_mul]
  rw [linePt_affine a b huv]
  exact (convex_segment _ _) hs.2 ht.2 hu hv huv

theorem isClosed_segParams (a b : Pt) (σ : Pt × Pt) : IsClosed (segParams a b σ) :=
  isClosed_Icc.inter ((isCompact_segment_pt _ _).isClosed.preimage (continuous_linePt a b))

/-- The intersection of two segments is polygonal (a segment, a point or empty). -/
theorem isPolygonal_segment_inter_segment (a b c d : Pt) :
    IsPolygonal (segment ℝ a b ∩ segment ℝ c d) := by
  set P := segParams a b (c, d) with hP
  have himg : segment ℝ a b ∩ segment ℝ c d = linePt a b '' P := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      obtain ⟨t, ht, rfl⟩ := mem_segment_iff_linePt.1 hz
      exact ⟨t, ⟨ht, hz'⟩, rfl⟩
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨mem_segment_iff_linePt.2 ⟨t, ht, rfl⟩, ht'⟩
  rw [himg]
  rcases P.eq_empty_or_nonempty with h | h
  · rw [h, image_empty]; exact isPolygonal_empty
  have hc : IsCompact P := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (isClosed_segParams a b _) fun t ht => ht.1
  have hPI : P = Icc (sInf P) (sSup P) := by
    apply subset_antisymm
    · exact fun t ht => ⟨csInf_le hc.bddBelow ht, le_csSup hc.bddAbove ht⟩
    · exact (convex_iff_ordConnected.1 (convex_segParams a b _)).out (hc.sInf_mem h)
        (hc.sSup_mem h)
  rw [hPI, linePt_image_Icc a b (csInf_le_csSup hc.bddBelow hc.bddAbove h)]
  exact isPolygonal_segment _ _

/-- The intersection of two polygonal sets is polygonal. -/
theorem IsPolygonal.inter {A B : Set Pt} (hA : IsPolygonal A) (hB : IsPolygonal B) :
    IsPolygonal (A ∩ B) := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  rw [iUnion₂_inter]
  refine isPolygonal_biUnion S fun s _ => ?_
  rw [inter_iUnion₂]
  exact isPolygonal_biUnion T fun t _ => isPolygonal_segment_inter_segment _ _ _ _

/-- A segment meets a polygonal set in a polygonal set. -/
theorem isPolygonal_segment_inter {A : Set Pt} (a b : Pt) (hA : IsPolygonal A) :
    IsPolygonal (segment ℝ a b ∩ A) :=
  (isPolygonal_segment a b).inter hA

theorem specialParams_subset (a b : Pt) (S : Finset (Pt × Pt)) :
    ∀ t ∈ specialParams a b S, t ∈ Icc (0 : ℝ) 1 := by
  intro t ht
  simp only [specialParams, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at ht
  rcases ht with ((rfl | rfl) | ⟨σ, -, rfl⟩) | ⟨σ, -, rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · rcases (segParams a b σ).eq_empty_or_nonempty with h | h
    · rw [h, Real.sInf_empty]; exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨le_csInf h fun s hs => hs.1.1, (csInf_le ⟨0, fun s hs => hs.1.1⟩ h.some_mem).trans
        h.some_mem.1.2⟩
  · rcases (segParams a b σ).eq_empty_or_nonempty with h | h
    · rw [h, Real.sSup_empty]; exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨h.some_mem.1.1.trans (le_csSup ⟨1, fun s hs => hs.1.2⟩ h.some_mem),
        csSup_le h fun s hs => hs.1.2⟩

/-- Between consecutive special parameters, the points of `[a, b]` are either all on a given
segment of `S` or all off it. -/
theorem mem_segment_of_gap {a b : Pt} {S : Finset (Pt × Pt)} {α β : ℝ}
    (hgap : ∀ s ∈ Ioo α β, s ∉ specialParams a b S) {σ : Pt × Pt} (hσ : σ ∈ S) {t t' : ℝ}
    (ht : t ∈ Ioo α β) (ht' : t' ∈ Ioo α β) (hα : 0 ≤ α) (hβ : β ≤ 1)
    (hp : linePt a b t ∈ segment ℝ σ.1 σ.2) : linePt a b t' ∈ segment ℝ σ.1 σ.2 := by
  have hP : t ∈ segParams a b σ := ⟨⟨hα.trans ht.1.le, ht.2.le.trans hβ⟩, hp⟩
  have hbdd : BddBelow (segParams a b σ) := ⟨0, fun s hs => hs.1.1⟩
  have hbdd' : BddAbove (segParams a b σ) := ⟨1, fun s hs => hs.1.2⟩
  have hInf : sInf (segParams a b σ) ∈ specialParams a b S := by
    simp only [specialParams, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨σ, hσ, rfl⟩)
  have hSup : sSup (segParams a b σ) ∈ specialParams a b S := by
    simp only [specialParams, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨σ, hσ, rfl⟩
  have hlo : sInf (segParams a b σ) < t' := by
    have h1 := csInf_le hbdd hP
    by_contra h
    push_neg at h
    exact hgap _ ⟨ht'.1.trans_le h, h1.trans_lt ht.2⟩ hInf
  have hhi : t' < sSup (segParams a b σ) := by
    have h1 := le_csSup hbdd' hP
    by_contra h
    push_neg at h
    exact hgap _ ⟨ht.1.trans_le h1, h.trans_lt ht'.2⟩ hSup
  obtain ⟨x, hx, hxt⟩ := exists_lt_of_csInf_lt ⟨t, hP⟩ hlo
  obtain ⟨y, hy, hyt⟩ := exists_lt_of_lt_csSup ⟨t, hP⟩ hhi
  exact ((convex_iff_ordConnected.1 (convex_segParams a b σ)).out hx hy
    ⟨hxt.le, hyt.le⟩).2

/-- The image of an open parameter interval is an open segment. -/
theorem linePt_image_Ioo (a b : Pt) {α β : ℝ} (h : α < β) :
    linePt a b '' Ioo α β = openSegment ℝ (linePt a b α) (linePt a b β) := by
  rw [openSegment_eq_image']
  have hd : linePt a b β - linePt a b α = (β - α) • (b - a) := by
    simp only [linePt]; rw [sub_smul]; abel
  ext z
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
    refine ⟨(s - α) / (β - α), ⟨div_pos (by linarith) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith)⟩, ?_⟩
    beta_reduce
    rw [hd, smul_smul, div_mul_cancel₀ _ (by linarith : β - α ≠ 0)]
    simp only [linePt]; rw [sub_smul]; abel
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨α + θ * (β - α), ⟨by nlinarith, by nlinarith⟩, ?_⟩
    beta_reduce
    rw [hd, smul_smul]
    simp only [linePt]; rw [add_smul, mul_comm θ]; abel

/-- A parameter in `[0, 1]` that is not special lies strictly between two consecutive special
parameters. -/
theorem exists_special_gap (a b : Pt) (S : Finset (Pt × Pt)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htF : t ∉ specialParams a b S) :
    ∃ α ∈ specialParams a b S, ∃ β ∈ specialParams a b S, α < t ∧ t < β ∧ 0 ≤ α ∧ β ≤ 1 ∧
      ∀ s ∈ Ioo α β, s ∉ specialParams a b S := by
  classical
  set F := specialParams a b S
  have h0 : t ≠ 0 := fun h => htF (h ▸ zero_mem_specialParams a b _)
  have h1 : t ≠ 1 := fun h => htF (h ▸ one_mem_specialParams a b _)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have hL : (F.filter (· < t)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨zero_mem_specialParams a b _, ht01.1⟩⟩
  have hR : (F.filter (t < ·)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨one_mem_specialParams a b _, ht01.2⟩⟩
  have hαm := Finset.mem_filter.1 (Finset.max'_mem _ hL)
  have hβm := Finset.mem_filter.1 (Finset.min'_mem _ hR)
  refine ⟨_, hαm.1, _, hβm.1, hαm.2, hβm.2, Finset.le_max' _ 0
    (Finset.mem_filter.2 ⟨zero_mem_specialParams a b _, ht01.1⟩), Finset.min'_le _ 1
    (Finset.mem_filter.2 ⟨one_mem_specialParams a b _, ht01.2⟩), ?_⟩
  intro s hs hsF
  rcases lt_trichotomy s t with h | h | h
  · exact absurd (Finset.le_max' _ s (Finset.mem_filter.2 ⟨hsF, h⟩)) (not_le.2 hs.1)
  · exact htF (h ▸ hsF)
  · exact absurd (Finset.min'_le _ s (Finset.mem_filter.2 ⟨hsF, h⟩)) (not_le.2 hs.2)

/-- **Open pieces.** For a polygonal `Γ` and a saturated `W` (e.g. `polyInterior Γ`), a segment
meets `W` in a finite union of open subsegments (degenerate ones, i.e. points, allowed:
`openSegment ℝ q q = {q}`) with ends on the segment. Between consecutive special parameters the
open piece of `[a, b]` either meets `Γ` — and then lies in it (`mem_segment_of_gap`) — or is a
preconnected set missing `Γ`, hence inside or outside `W`. -/
theorem exists_open_pieces_of_saturated (a b : Pt) {Γ W : Set Pt} (hΓ : IsPolygonal Γ)
    (hW : IsSaturated Γ W) :
    ∃ P : Finset (Pt × Pt), (∀ q ∈ P, q.1 ∈ segment ℝ a b ∧ q.2 ∈ segment ℝ a b) ∧
      segment ℝ a b ∩ W = ⋃ q ∈ P, openSegment ℝ q.1 q.2 := by
  classical
  obtain ⟨S, rfl⟩ := hΓ
  by_cases hab : a = b
  · subst hab
    by_cases ha : a ∈ W
    · refine ⟨{(a, a)}, by simp, ?_⟩
      rw [segment_same, singleton_inter_of_mem ha]; simp
    · refine ⟨∅, by simp, ?_⟩
      rw [segment_same, singleton_inter_of_notMem ha]; simp
  set F := specialParams a b S with hF
  set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ linePt a b t ∈ W} with hT
  have hgapT : ∀ α β : ℝ, (∀ s ∈ Ioo α β, s ∉ F) → 0 ≤ α → β ≤ 1 → ∀ t ∈ Ioo α β, t ∈ T →
      Ioo α β ⊆ T := by
    intro α β hgap hα hβ t ht htT
    have hoff : linePt a b '' Ioo α β ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2)ᶜ := by
      rintro _ ⟨s, hs, rfl⟩ hsΓ
      obtain ⟨σ, hσ, hsσ⟩ := mem_iUnion₂.1 hsΓ
      exact hW.1 htT.2 (mem_iUnion₂.2 ⟨σ, hσ, mem_segment_of_gap hgap hσ hs ht hα hβ hsσ⟩)
    have hsub := hW.2 _ (isPreconnected_Ioo.image _ (continuous_linePt a b).continuousOn) hoff
      ⟨_, ⟨t, ht, rfl⟩, htT.2⟩
    exact fun s hs => ⟨⟨hα.trans hs.1.le, hs.2.le.trans hβ⟩, hsub ⟨s, hs, rfl⟩⟩
  set Q := (F ×ˢ F).filter (fun q => (q.1 = q.2 ∧ q.1 ∈ T) ∨ (q.1 < q.2 ∧ Ioo q.1 q.2 ⊆ T))
    with hQ
  refine ⟨Q.image (fun q => (linePt a b q.1, linePt a b q.2)), ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hq
    have h := Finset.mem_product.1 (Finset.mem_filter.1 hq').1
    exact ⟨mem_segment_iff_linePt.2 ⟨_, specialParams_subset a b S _ h.1, rfl⟩,
      mem_segment_iff_linePt.2 ⟨_, specialParams_subset a b S _ h.2, rfl⟩⟩
  rw [Finset.set_biUnion_finset_image]
  ext z
  simp only [mem_inter_iff, mem_iUnion₂]
  constructor
  · rintro ⟨hz, hzW⟩
    obtain ⟨t, ht, rfl⟩ := mem_segment_iff_linePt.1 hz
    by_cases htF : t ∈ F
    · exact ⟨(t, t), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨htF, htF⟩,
        Or.inl ⟨rfl, ht, hzW⟩⟩, by simp⟩
    obtain ⟨α, hαF, β, hβF, hαt, htβ, hα0, hβ1, hgap⟩ := exists_special_gap a b S ht htF
    refine ⟨(α, β), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hαF, hβF⟩,
      Or.inr ⟨hαt.trans htβ, hgapT α β hgap hα0 hβ1 t ⟨hαt, htβ⟩ ⟨ht, hzW⟩⟩⟩, ?_⟩
    rw [← linePt_image_Ioo a b (hαt.trans htβ)]
    exact ⟨t, ⟨hαt, htβ⟩, rfl⟩
  · rintro ⟨q, hq, hz⟩
    rcases (Finset.mem_filter.1 hq).2 with ⟨hqe, hqT⟩ | ⟨hqlt, hqT⟩
    · obtain ⟨q1, q2⟩ := q
      simp only at hqe hqT hz
      subst hqe
      rw [openSegment_same, mem_singleton_iff] at hz
      subst hz
      exact ⟨mem_segment_iff_linePt.2 ⟨_, hqT.1, rfl⟩, hqT.2⟩
    · rw [← linePt_image_Ioo a b hqlt] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact ⟨mem_segment_iff_linePt.2 ⟨s, (hqT hs).1, rfl⟩, (hqT hs).2⟩

end HPC.Plane
