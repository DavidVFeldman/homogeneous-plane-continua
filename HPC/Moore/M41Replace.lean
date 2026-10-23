import HPC.Moore.Sec6Lim
import HPC.Moore.Sec7Chord

/-!
# Theorem 41, Case II: replacing a null family of sub-arcs of an arc (batch 140, item A)

`arc_replace`: given an arc `f : [0, 1] → X` in a metric space and a family of arcs `Zᵢ` from
`f uᵢ` to `f vᵢ`, with the open intervals `(uᵢ, vᵢ)` pairwise disjoint, the open arcs `Zᵢ` pairwise
disjoint and disjoint from `f`, and only finitely many `Zᵢ` of size `≥ ε` for every `ε > 0`, the
set obtained from `f` by replacing each `f [uᵢ, vᵢ]` by `Zᵢ` is an arc from `f 0` to `f 1`.
This is the commission's "replacement of a null family of arcs" (§2, item A).
-/

namespace HPC.Moore

open Set Topology Filter unitInterval

namespace Gen

/-- The affine map `[s, t] → [0, 1]`, clamped outside `[s, t]`. -/
noncomputable def unaffI (s t : I) (x : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (((x : ℝ) - s) / ((t : ℝ) - s))

theorem continuous_unaffI (s t : I) : Continuous (unaffI s t) :=
  continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

theorem unaffI_left (s t : I) : unaffI s t s = 0 := by
  apply Subtype.ext
  simp [unaffI]

theorem unaffI_right {s t : I} (hst : s < t) : unaffI s t t = 1 := by
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  apply Subtype.ext
  simp [unaffI, div_self hts.ne']

theorem unaffI_val {s t : I} (hst : s < t) {x : I} (hx : x ∈ Icc s t) :
    (unaffI s t x : ℝ) = ((x : ℝ) - s) / ((t : ℝ) - s) := by
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  have h1 : (s : ℝ) ≤ x := hx.1
  have h2 : (x : ℝ) ≤ t := hx.2
  have hmem : ((x : ℝ) - s) / ((t : ℝ) - s) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hts.le, (div_le_one hts).mpr (by linarith)⟩
  simp only [unaffI, Set.projIcc_of_mem _ hmem]

theorem unaffI_injOn {s t : I} (hst : s < t) : InjOn (unaffI s t) (Icc s t) := by
  intro x hx y hy hxy
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  have h := congrArg Subtype.val hxy
  rw [unaffI_val hst hx, unaffI_val hst hy] at h
  have := (div_left_inj' hts.ne').mp h
  exact Subtype.ext (by linarith)

theorem unaffI_mem_Ioo {s t : I} (hst : s < t) {x : I} (hx : x ∈ Ioo s t) :
    unaffI s t x ∈ Ioo (0 : I) 1 := by
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  have hv := unaffI_val hst (Ioo_subset_Icc_self hx)
  have h1 : (s : ℝ) < x := hx.1
  have h2 : (x : ℝ) < t := hx.2
  constructor
  · show (0 : ℝ) < unaffI s t x; rw [hv]; exact div_pos (by linarith) hts
  · show (unaffI s t x : ℝ) < 1; rw [hv]; exact (div_lt_one hts).mpr (by linarith)

theorem unaffI_affI {s t : I} (hst : s < t) (r : I) : unaffI s t (affI s t hst.le r) = r := by
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  have hmem : affI s t hst.le r ∈ Icc s t := by
    rw [← range_affI hst]; exact mem_range_self _
  apply Subtype.ext
  rw [unaffI_val hst hmem]
  simp only [affI]
  field_simp
  ring

theorem affI_mem_Ioo {s t : I} (hst : s < t) {r : I} (hr : r ∈ Ioo (0 : I) 1) :
    affI s t hst.le r ∈ Ioo s t := by
  have hts : (0 : ℝ) < t - s := sub_pos.mpr hst
  have h0 : (0 : ℝ) < r := hr.1
  have h1 : (r : ℝ) < 1 := hr.2
  constructor
  · show (s : ℝ) < s + r * (t - s); nlinarith
  · show (s : ℝ) + r * (t - s) < t; nlinarith

/-- Pairwise disjoint open intervals of `[0, 1]` of length at least `δ > 0` are finitely many. -/
theorem finite_long_intervals {ι : Type*} (u v : ι → I) (huv : ∀ i, u i < v i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j))) {δ : ℝ}
    (hδ : 0 < δ) : {i | δ ≤ (v i : ℝ) - u i}.Finite := by
  refine finite_of_separated hδ (fun i => (u i : ℝ)) (fun i _ => ⟨(u i).2.1, (u i).2.2⟩) ?_
  intro i hi j hj hij
  have hd := Set.Ioo_disjoint_Ioo.mp (hdisj i j hij)
  have hi' : δ ≤ (v i : ℝ) - u i := hi
  have hj' : δ ≤ (v j : ℝ) - u j := hj
  have hui : (u i : ℝ) < v i := huv i
  have huj : (u j : ℝ) < v j := huv j
  rcases le_total (u i) (u j) with h | h
  · rw [max_eq_right h] at hd
    have hd' : (min (v i) (v j) : ℝ) ≤ u j := by exact_mod_cast hd
    have h' : (u i : ℝ) ≤ u j := h
    rcases min_le_iff.mp (show min (v i : ℝ) (v j) ≤ u j by
      simpa [← Subtype.coe_le_coe] using hd) with h2 | h2
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · linarith
  · rw [max_eq_left h] at hd
    have h' : (u j : ℝ) ≤ u i := h
    rcases min_le_iff.mp (show min (v i : ℝ) (v j) ≤ u i by
      simpa [← Subtype.coe_le_coe] using hd) with h2 | h2
    · linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

variable {X : Type*} [MetricSpace X]

/-- **Replacement of a null family of arcs.** -/
theorem arc_replace {f : I → X} (hf : IsEmbedding f) {ι : Type*} (u v : ι → I)
    (Z : ι → Set X) (huv : ∀ i, u i < v i) (hZ : ∀ i, TArc (f (u i)) (f (v i)) (Z i))
    (hZf : ∀ i, Disjoint (Z i \ {f (u i), f (v i)}) (range f))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j)))
    (hZdisj : ∀ i j, i ≠ j →
      Disjoint (Z i \ {f (u i), f (v i)}) (Z j \ {f (u j), f (v j)}))
    (hnull : ∀ ε > 0, {i | ∃ x ∈ Z i, ε ≤ dist x (f (u i))}.Finite) :
    ∃ D, TArc (f 0) (f 1) D ∧ D ⊆ range f ∪ ⋃ i, Z i ∧ (∀ i, Z i ⊆ D) ∧
      ∀ t, (∀ i, t ∉ Ioo (u i) (v i)) → f t ∈ D := by
  classical
  choose z hz hzr hz0 hz1 using fun i => (hZ i).2
  set φ : ι → I → X := fun i t => z i (unaffI (u i) (v i) t) with hφdef
  set h : I → X := fun t => if hx : ∃ i, t ∈ Ioo (u i) (v i) then φ hx.choose t else f t
    with hhdef
  have huniq : ∀ i t, t ∈ Ioo (u i) (v i) → h t = φ i t := by
    intro i t ht
    have hx : ∃ i, t ∈ Ioo (u i) (v i) := ⟨i, ht⟩
    simp only [hhdef, dif_pos hx]
    by_cases e : hx.choose = i
    · rw [e]
    · exact absurd (hdisj _ _ e) (not_disjoint_iff.mpr ⟨t, hx.choose_spec, ht⟩)
  have hout : ∀ t, (∀ i, t ∉ Ioo (u i) (v i)) → h t = f t := by
    intro t ht
    have hx : ¬ ∃ i, t ∈ Ioo (u i) (v i) := fun ⟨i, hi⟩ => ht i hi
    simp only [hhdef, dif_neg hx]
  have hφc : ∀ i, Continuous (φ i) := fun i => (hz i).continuous.comp (continuous_unaffI _ _)
  have hφu : ∀ i, φ i (u i) = f (u i) := fun i => by
    simp only [hφdef, unaffI_left, hz0]
  have hφv : ∀ i, φ i (v i) = f (v i) := fun i => by
    simp only [hφdef, unaffI_right (huv i), hz1]
  have hφZ : ∀ i t, φ i t ∈ Z i := fun i t => hzr i ▸ mem_range_self _
  have hφmem : ∀ i t, t ∈ Ioo (u i) (v i) → φ i t ∈ Z i \ {f (u i), f (v i)} := by
    intro i t ht
    refine ⟨hφZ i t, ?_⟩
    have hr := unaffI_mem_Ioo (huv i) ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro e
      rw [← hz0 i] at e
      exact hr.1.ne' ((hz i).injective e)
    · intro e
      rw [← hz1 i] at e
      exact hr.2.ne ((hz i).injective e)
  have hφinj : ∀ i, InjOn (φ i) (Icc (u i) (v i)) := fun i a ha b hb hab =>
    unaffI_injOn (huv i) ha hb ((hz i).injective hab)
  have hend : ∀ i j, u i ∉ Ioo (u j) (v j) ∧ v i ∉ Ioo (u j) (v j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact ⟨fun h => lt_irrefl _ h.1, fun h => lt_irrefl _ h.2⟩
    have hd := Set.Ioo_disjoint_Ioo.mp (hdisj i j hij)
    have hui := huv i
    have huj := huv j
    constructor
    · rintro ⟨h1, h2⟩
      have : max (u i) (u j) = u i := max_eq_left h1.le
      rw [this] at hd
      rcases min_le_iff.mp hd with h3 | h3
      · exact absurd h3 (not_le.mpr hui)
      · exact absurd h3 (not_le.mpr h2)
    · rintro ⟨h1, h2⟩
      have : min (v i) (v j) = v i := min_eq_left h2.le
      rw [this] at hd
      rcases le_max_iff.mp hd with h3 | h3
      · exact absurd h3 (not_le.mpr hui)
      · exact absurd h3 (not_le.mpr h1)
  -- continuity
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ∃ i, t ∈ Ioo (u i) (v i)
    · obtain ⟨i, hi⟩ := ht
      have hev : h =ᶠ[𝓝 t] φ i := by
        filter_upwards [isOpen_Ioo.mem_nhds hi] with s hs using huniq i s hs
      exact ((hφc i).continuousAt).congr hev.symm
    · push_neg at ht
      rw [ContinuousAt, hout t ht, Metric.tendsto_nhds]
      intro ε hε
      have hε3 : 0 < ε / 3 := by positivity
      obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
        (CompactSpace.uniformContinuous_of_continuous hf.continuous) (ε / 3) hε3
      set G := {i | ∃ s ∈ Icc (u i) (v i), ε / 3 ≤ dist (f s) (f (u i))} with hG
      have hGfin : G.Finite := by
        refine (finite_long_intervals u v huv hdisj hδ).subset ?_
        rintro i ⟨s, hs, hsd⟩
        have h1 : δ ≤ dist s (u i) := by
          by_contra hlt
          exact absurd (hδf (not_le.mp hlt)) (not_lt.mpr hsd)
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (u i : ℝ) ≤ s from hs.1))] at h1
        have : (s : ℝ) ≤ v i := hs.2
        show δ ≤ (v i : ℝ) - u i
        linarith
      set F := G ∪ {i | ∃ x ∈ Z i, ε / 3 ≤ dist x (f (u i))} with hF
      have hFfin : F.Finite := hGfin.union (hnull _ hε3)
      have E1 : ∀ᶠ s in 𝓝 t, dist (f s) (f t) < ε / 3 :=
        Metric.tendsto_nhds.mp hf.continuous.continuousAt _ hε3
      have E2 : ∀ᶠ s in 𝓝 t, ∀ i ∈ F, s ∈ Ioo (u i) (v i) → dist (φ i s) (f t) < ε := by
        rw [Filter.eventually_all_finite hFfin]
        intro i _
        rcases lt_trichotomy t (u i) with h1 | h1 | h1
        · filter_upwards [isOpen_Iio.mem_nhds h1] with s hs hs'
          exact absurd hs'.1 (not_lt.mpr (le_of_lt hs))
        · have := Metric.tendsto_nhds.mp ((hφc i).continuousAt (x := t)) ε hε
          filter_upwards [this] with s hs _
          rw [h1, hφu i] at hs; rw [h1]; exact hs
        · have h2 : v i ≤ t := by
            by_contra h3
            exact ht i ⟨h1, not_le.mp h3⟩
          rcases h2.lt_or_eq with h2 | h2
          · filter_upwards [isOpen_Ioi.mem_nhds h2] with s hs hs'
            exact absurd hs'.2 (not_lt.mpr (le_of_lt hs))
          · have := Metric.tendsto_nhds.mp ((hφc i).continuousAt (x := t)) ε hε
            filter_upwards [this] with s hs _
            rw [← h2, hφv i] at hs; rw [← h2]; exact hs
      filter_upwards [E1, E2] with s hs1 hs2
      by_cases hs : ∃ i, s ∈ Ioo (u i) (v i)
      · obtain ⟨i, hi⟩ := hs
        rw [huniq i s hi]
        by_cases hiF : i ∈ F
        · exact hs2 i hiF hi
        · have hiG : i ∉ G := fun h => hiF (Or.inl h)
          have hiZ : i ∉ {i | ∃ x ∈ Z i, ε / 3 ≤ dist x (f (u i))} := fun h => hiF (Or.inr h)
          have d1 : dist (φ i s) (f (u i)) < ε / 3 := by
            by_contra hc; exact hiZ ⟨_, hφZ i s, not_lt.mp hc⟩
          have d2 : dist (f s) (f (u i)) < ε / 3 := by
            by_contra hc; exact hiG ⟨s, Ioo_subset_Icc_self hi, not_lt.mp hc⟩
          calc dist (φ i s) (f t) ≤ dist (φ i s) (f (u i)) + dist (f (u i)) (f t) :=
                dist_triangle _ _ _
            _ ≤ dist (φ i s) (f (u i)) + (dist (f (u i)) (f s) + dist (f s) (f t)) := by
                gcongr; exact dist_triangle _ _ _
            _ < ε / 3 + (ε / 3 + ε / 3) := by
                rw [dist_comm (f (u i))]; gcongr
            _ = ε := by ring
      · push_neg at hs
        rw [hout s hs]
        linarith
  -- injectivity
  have hinj : Function.Injective h := by
    intro a b hab
    by_cases ha : ∃ i, a ∈ Ioo (u i) (v i) <;> by_cases hb : ∃ i, b ∈ Ioo (u i) (v i)
    · obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      rw [huniq i a hi, huniq j b hj] at hab
      by_cases hij : i = j
      · subst hij
        exact hφinj i (Ioo_subset_Icc_self hi) (Ioo_subset_Icc_self hj) hab
      · exact absurd (hZdisj i j hij)
          (not_disjoint_iff.mpr ⟨_, hφmem i a hi, hab ▸ hφmem j b hj⟩)
    · obtain ⟨i, hi⟩ := ha
      push_neg at hb
      rw [huniq i a hi, hout b hb] at hab
      exact absurd (hZf i) (not_disjoint_iff.mpr ⟨_, hφmem i a hi, hab ▸ mem_range_self _⟩)
    · obtain ⟨j, hj⟩ := hb
      push_neg at ha
      rw [hout a ha, huniq j b hj] at hab
      exact absurd (hZf j)
        (not_disjoint_iff.mpr ⟨_, hφmem j b hj, hab ▸ mem_range_self _⟩)
    · push_neg at ha hb
      rw [hout a ha, hout b hb] at hab
      exact hf.injective hab
  have h0 : h 0 = f 0 := hout 0 fun i hi => not_lt.mpr nonneg' hi.1
  have h1 : h 1 = f 1 := hout 1 fun i hi => not_lt.mpr le_one' hi.2
  refine ⟨range h, ?_, ?_, ?_, ?_⟩
  · have := TArc.of_inj hcont hinj
    rwa [h0, h1] at this
  · rintro _ ⟨t, rfl⟩
    by_cases ht : ∃ i, t ∈ Ioo (u i) (v i)
    · obtain ⟨i, hi⟩ := ht
      rw [huniq i t hi]
      exact Or.inr (mem_iUnion.mpr ⟨i, hφZ i t⟩)
    · push_neg at ht
      rw [hout t ht]
      exact Or.inl (mem_range_self _)
  · intro i x hx
    rw [← hzr i] at hx
    obtain ⟨r, rfl⟩ := hx
    by_cases hr0 : r = 0
    · subst hr0
      rw [hz0 i, ← hout (u i) fun j => (hend i j).1]
      exact mem_range_self _
    by_cases hr1 : r = 1
    · subst hr1
      rw [hz1 i, ← hout (v i) fun j => (hend i j).2]
      exact mem_range_self _
    have hr : r ∈ Ioo (0 : I) 1 :=
      ⟨lt_of_le_of_ne nonneg' (Ne.symm hr0), lt_of_le_of_ne le_one' hr1⟩
    have hs := affI_mem_Ioo (huv i) hr
    refine ⟨affI (u i) (v i) (huv i).le r, ?_⟩
    rw [huniq i _ hs]
    simp only [hφdef, unaffI_affI (huv i)]
  · intro t ht
    rw [← hout t ht]
    exact mem_range_self _

end Gen

end HPC.Moore
