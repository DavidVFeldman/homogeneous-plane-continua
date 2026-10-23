import HPC.Hagopian.H75Defs

/-!
# Batch 155: `arc_of_degenerate_layers` is false as stated — the `sin (1/x)`-continuum

The skeleton's `arc_of_degenerate_layers` (Kuratowski §48 VII, Theorem 6, in the form Thomas's
Theorem 21 is cited) asks: if every *interior* layer of a type A′ map is degenerate, the continuum is
an arc. The `sin (1/x)`-continuum

  `sinCurve = {(x, sin (1/x)) : 0 < x ≤ 1} ∪ ({0} × [−1, 1])`

is a counterexample (`not_arc_of_degenerate_layers`):
* it is irreducible between `(1, sin 1)` and `(0, 0)` (`isIrreducibleBetween_sinCurve`);
* the first projection `sinProj` is admissible (`isAdmissibleMap_sinProj`), its layers have void
  interior (`interior_sinProj_fibre`), and its layers over `(0, 1]` are points;
* but its layer over `0` is a nondegenerate subcontinuum with void interior, and a nondegenerate
  connected subset of an arc has interior (`not_nonempty_homeomorph_sinCurve`).
-/

namespace HPC.Hagopian

open Set Topology Filter Real

/-- The graph part `{(x, sin (1/x)) : 0 < x ≤ 1}`. -/
def sinGraph : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = Real.sin (1 / p.1)}

/-- The limit segment `{0} × [−1, 1]`. -/
def sinBar : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1}

/-- The `sin (1/x)`-continuum. -/
def sinCurve : Set (ℝ × ℝ) := sinGraph ∪ sinBar

theorem mem_sinGraph_of_pos {p : ℝ × ℝ} (hp : p ∈ sinCurve) (h : 0 < p.1) : p ∈ sinGraph := by
  rcases hp with hp | hp
  · exact hp
  · exact absurd hp.1 h.ne'

theorem sinCurve_fst_mem {p : ℝ × ℝ} (hp : p ∈ sinCurve) : 0 ≤ p.1 ∧ p.1 ≤ 1 := by
  rcases hp with hp | hp
  · exact ⟨hp.1.le, hp.2.1⟩
  · exact ⟨hp.1.ge, hp.1.le.trans zero_le_one⟩

/-- Points of the graph converging to a point `(0, y)` of the bar, with first coordinates `> 0`. -/
theorem exists_seq_to_bar {y : ℝ} (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    ∃ x : ℕ → ℝ, (∀ n, (x n, y) ∈ sinGraph) ∧ Tendsto (fun n => (x n, y)) atTop (𝓝 (0, y)) := by
  set D : ℕ → ℝ := fun n => Real.arcsin y + ((n + 1 : ℕ) : ℝ) * (2 * π) with hD
  have hpi := Real.pi_gt_three
  have hDge : ∀ n : ℕ, (n : ℝ) + 1 ≤ D n := by
    intro n
    have h1 := Real.neg_pi_div_two_le_arcsin y
    simp only [hD]
    push_cast
    nlinarith
  have hDpos : ∀ n, 0 < D n := fun n => lt_of_lt_of_le (by positivity) (hDge n)
  refine ⟨fun n => 1 / D n, fun n => ⟨by have := hDpos n; positivity, ?_, ?_⟩, ?_⟩
  · rw [div_le_one (hDpos n)]
    have := hDge n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · simp only [one_div_one_div, hD]
    rw [Real.sin_add_nat_mul_two_pi, Real.sin_arcsin hy1 hy2]
  · refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
    refine squeeze_zero (fun n => (one_div_pos.2 (hDpos n)).le) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity) (hDge n)

theorem sinBar_subset_closure : sinBar ⊆ closure sinGraph := by
  rintro ⟨p1, p2⟩ ⟨h0, hy1, hy2⟩
  simp only at h0 hy1 hy2
  subst h0
  obtain ⟨x, hx, hlim⟩ := exists_seq_to_bar hy1 hy2
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hx)

theorem closure_sinGraph_subset : closure sinGraph ⊆ sinCurve := by
  intro p hp
  have hK : IsClosed {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1} := by
    refine (isClosed_le continuous_const continuous_fst).inter ?_
    refine (isClosed_le continuous_fst continuous_const).inter ?_
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)
  have hGK : sinGraph ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1} := by
    rintro q ⟨h1, h2, h3⟩
    refine ⟨h1.le, h2, ?_, ?_⟩ <;> rw [h3]
    · exact Real.neg_one_le_sin _
    · exact Real.sin_le_one _
  obtain ⟨h1, h2, h3, h4⟩ := hK.closure_subset_iff.2 hGK hp
  rcases h1.lt_or_eq with h1 | h1
  · left
    refine ⟨h1, h2, ?_⟩
    -- `q ↦ q.2 - sin (1 / q.1)` is continuous at `p` and vanishes on the graph
    set φ : ℝ × ℝ → ℝ := fun q => q.2 - Real.sin (1 / q.1)
    have hφ : ContinuousAt φ p :=
      continuousAt_snd.sub (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div continuousAt_fst h1.ne'))
    have hzero : φ p = 0 := by
      have hcl : p ∈ closure (sinGraph ∩ {q | φ q = 0}) := by
        have : sinGraph ∩ {q | φ q = 0} = sinGraph := by
          ext q; constructor
          · exact fun h => h.1
          · intro hq; exact ⟨hq, by simp [φ, hq.2.2]⟩
        rw [this]; exact hp
      by_contra hne
      have hopen : ∀ᶠ q in 𝓝 p, φ q ≠ 0 := hφ.eventually_ne hne
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff_nhds.1 hcl _ hopen
      exact hq1 hq2.2
    simpa [φ, sub_eq_zero] using hzero
  · right
    exact ⟨h1.symm, h3, h4⟩

theorem closure_sinGraph : closure sinGraph = sinCurve :=
  subset_antisymm closure_sinGraph_subset
    (union_subset subset_closure sinBar_subset_closure)

theorem isConnected_sinGraph : IsConnected sinGraph := by
  have : sinGraph = (fun x : ℝ => (x, Real.sin (1 / x))) '' Ioc 0 1 := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨a, ⟨h1, h2⟩, by simp only at h3; rw [h3]⟩
    · rintro ⟨x, ⟨h1, h2⟩, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨h1, h2, rfl⟩
  rw [this]
  refine (isConnected_Ioc zero_lt_one).image _ ?_
  intro x hx
  exact (continuousAt_id.prodMk (Real.continuous_sin.continuousAt.comp
    (continuousAt_const.div continuousAt_id hx.1.ne'))).continuousWithinAt

theorem isContinuum_sinCurve : Fold.Q78.IsContinuum sinCurve := by
  rw [← closure_sinGraph]
  refine ⟨?_, isConnected_sinGraph.closure⟩
  refine (isCompact_Icc (a := ((0 : ℝ), (-1 : ℝ))) (b := (1, 1))).of_isClosed_subset
    isClosed_closure ?_
  rw [closure_sinGraph]
  intro q hq
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨⟨h1.le, ?_⟩, ⟨h2, ?_⟩⟩
    · show -1 ≤ q.2; rw [h3]; exact Real.neg_one_le_sin _
    · show q.2 ≤ 1; rw [h3]; exact Real.sin_le_one _
  · exact ⟨⟨h1.ge, h2⟩, ⟨h1.le.trans zero_le_one, h3⟩⟩

/-- The first projection of the `sin (1/x)`-continuum onto `[0, 1]`. -/
noncomputable def sinProj : sinCurve → unitInterval := fun p =>
  ⟨p.1.1, sinCurve_fst_mem p.2⟩

theorem sinProj_val (p : sinCurve) : (sinProj p : ℝ) = p.1.1 := rfl

theorem sinGraph_eq {p q : ℝ × ℝ} (hp : p ∈ sinGraph) (hq : q ∈ sinGraph) (h : p.1 = q.1) :
    p = q := Prod.ext h (by rw [hp.2.2, hq.2.2, h])

theorem isAdmissibleMap_sinProj : IsAdmissibleMap sinCurve sinProj := by
  refine ⟨Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _, ?_, ?_⟩
  · intro t
    rcases t.2.1.lt_or_eq with ht | ht
    · exact ⟨⟨(t.1, Real.sin (1 / t.1)), Or.inl ⟨ht, t.2.2, rfl⟩⟩, Subtype.ext rfl⟩
    · exact ⟨⟨(0, 0), Or.inr ⟨rfl, by norm_num, by norm_num⟩⟩, Subtype.ext (by
        rw [sinProj_val]; exact ht)⟩
  · intro t
    rcases t.2.1.lt_or_eq with ht | ht
    · -- a single point
      have hmem : (t.1, Real.sin (1 / t.1)) ∈ sinCurve := Or.inl ⟨ht, t.2.2, rfl⟩
      have : sinProj ⁻¹' {t} = {⟨_, hmem⟩} := by
        ext p; constructor
        · intro hp
          have h1 : p.1.1 = t.1 := congrArg Subtype.val (mem_singleton_iff.1 hp)
          have hpG := mem_sinGraph_of_pos p.2 (h1 ▸ ht)
          exact mem_singleton_iff.2 (Subtype.ext (sinGraph_eq hpG ⟨ht, t.2.2, rfl⟩ h1))
        · intro hp
          rw [mem_singleton_iff.1 hp]
          exact Subtype.ext rfl
      rw [this]; exact isConnected_singleton
    · -- the bar
      have hb : ((0 : ℝ), (0 : ℝ)) ∈ sinCurve := Or.inr ⟨rfl, by norm_num, by norm_num⟩
      refine ⟨⟨⟨_, hb⟩, Subtype.ext (by rw [sinProj_val]; exact ht)⟩, ?_⟩
      rw [← IsInducing.subtypeVal.isPreconnected_image]
      have : Subtype.val '' (sinProj ⁻¹' {t}) = sinBar := by
        ext q; constructor
        · rintro ⟨p, hp, rfl⟩
          have h1 : p.1.1 = t.1 := congrArg Subtype.val (mem_singleton_iff.1 hp)
          rcases p.2 with hpG | hpS
          · exact absurd (h1 ▸ hpG.1) (by rw [← ht]; exact lt_irrefl 0)
          · exact hpS
        · intro hq
          exact ⟨⟨q, Or.inr hq⟩, mem_singleton_iff.2 (Subtype.ext (by
            rw [sinProj_val]; exact hq.1.trans ht)), rfl⟩
      rw [this]
      have : sinBar = {(0 : ℝ)} ×ˢ Icc (-1 : ℝ) 1 := by
        ext q; simp [sinBar]
      rw [this]
      exact (convex_singleton _).prod (convex_Icc _ _) |>.isPreconnected

/-- Every point of the `sin (1/x)`-continuum is a limit of points with a different first
coordinate. -/
theorem exists_seq_fst_ne (p : sinCurve) :
    ∃ u : ℕ → sinCurve, Tendsto u atTop (𝓝 p) ∧ ∀ n, (u n).1.1 ≠ p.1.1 := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only at h1 h2 h3
    set x : ℕ → ℝ := fun n => a - a / ((n + 2 : ℕ) : ℝ) with hx
    have hxlt : ∀ n, x n < a := fun n => by
      simp only [hx]
      have : 0 < a / ((n + 2 : ℕ) : ℝ) := by positivity
      linarith
    have hxpos : ∀ n, 0 < x n := fun n => by
      simp only [hx]
      have h2' : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have : a / ((n + 2 : ℕ) : ℝ) < a := div_lt_self h1 h2'
      linarith
    have hmem : ∀ n, (x n, Real.sin (1 / x n)) ∈ sinCurve := fun n =>
      Or.inl ⟨hxpos n, (hxlt n).le.trans h2, rfl⟩
    refine ⟨fun n => ⟨_, hmem n⟩, ?_, fun n => (hxlt n).ne⟩
    rw [tendsto_subtype_rng]
    have hxt : Tendsto x atTop (𝓝 a) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat a).comp (tendsto_add_atTop_nat 2)
      simpa [hx] using (tendsto_const_nhds (x := a)).sub this
    have hc : ContinuousAt (fun x : ℝ => (x, Real.sin (1 / x))) a :=
      continuousAt_id.prodMk (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div continuousAt_id h1.ne'))
    have := hc.tendsto.comp hxt
    simp only at this ⊢
    rw [h3]
    exact this
  · simp only at h1 h2 h3
    subst h1
    obtain ⟨x, hx, hlim⟩ := exists_seq_to_bar h2 h3
    refine ⟨fun n => ⟨_, Or.inl (hx n)⟩, ?_, fun n => (hx n).1.ne'⟩
    rw [tendsto_subtype_rng]
    exact hlim

theorem interior_sinProj_fibre (t : unitInterval) : interior (sinProj ⁻¹' {t}) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  have hpt : sinProj p = t := mem_singleton_iff.1 (interior_subset hp : p ∈ sinProj ⁻¹' {t})
  obtain ⟨u, hu, hne⟩ := exists_seq_fst_ne p
  obtain ⟨n, hn⟩ := (hu.eventually (mem_interior_iff_mem_nhds.1 hp)).exists
  apply hne n
  have : sinProj (u n) = sinProj p := (mem_singleton_iff.1 hn).trans hpt.symm
  exact congrArg Subtype.val this

theorem isIrreducibleBetween_sinCurve :
    IsIrreducibleBetween sinCurve (1, Real.sin 1) (0, 0) := by
  refine ⟨isContinuum_sinCurve, Or.inl ⟨one_pos, le_rfl, by simp⟩,
    Or.inr ⟨rfl, by norm_num, by norm_num⟩, fun K hK hKE ha hb => subset_antisymm hKE ?_⟩
  rw [← closure_sinGraph]
  refine hK.1.isClosed.closure_subset_iff.2 fun p hp => ?_
  have hpre : IsPreconnected (Prod.fst '' K) := hK.2.isPreconnected.image _
    continuous_fst.continuousOn
  have hsub := hpre.Icc_subset (a := 0) (b := 1) ⟨_, hb, rfl⟩ ⟨_, ha, rfl⟩
  obtain ⟨q, hqK, hq⟩ := hsub ⟨hp.1.le, hp.2.1⟩
  have hqG := mem_sinGraph_of_pos (hKE hqK) (hq ▸ hp.1)
  rw [← sinGraph_eq hqG hp hq]
  exact hqK

theorem layer_sinProj_subsingleton (s : unitInterval) (hs : 0 < s) :
    (layer sinProj s).Subsingleton := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hp1 : p.1.1 = s.1 := congrArg Subtype.val (mem_singleton_iff.1 hp)
  have hq1 : q.1.1 = s.1 := congrArg Subtype.val (mem_singleton_iff.1 hq)
  have hs' : (0 : ℝ) < s.1 := hs
  exact sinGraph_eq (mem_sinGraph_of_pos p.2 (hp1 ▸ hs')) (mem_sinGraph_of_pos q.2 (hq1 ▸ hs'))
    (hp1.trans hq1.symm)

/-- The `sin (1/x)`-continuum is not an arc: its bar is a nondegenerate connected set with void
interior, while a nondegenerate connected subset of `[0, 1]` has interior. -/
theorem not_nonempty_homeomorph_sinCurve : ¬ Nonempty (sinCurve ≃ₜ unitInterval) := by
  rintro ⟨φ⟩
  set F := sinProj ⁻¹' {(0 : unitInterval)} with hF
  have hFc : IsConnected F := isAdmissibleMap_sinProj.2.2 0
  have hm1 : ((0 : ℝ), (1 : ℝ)) ∈ sinCurve := Or.inr ⟨rfl, by norm_num, le_rfl⟩
  have hm2 : ((0 : ℝ), (-1 : ℝ)) ∈ sinCurve := Or.inr ⟨rfl, le_rfl, by norm_num⟩
  have hF1 : (⟨_, hm1⟩ : sinCurve) ∈ F := mem_singleton_iff.2 (Subtype.ext rfl)
  have hF2 : (⟨_, hm2⟩ : sinCurve) ∈ F := mem_singleton_iff.2 (Subtype.ext rfl)
  set ψ : sinCurve → ℝ := fun z => (φ z : ℝ) with hψ
  have hψc : Continuous ψ := continuous_subtype_val.comp φ.continuous
  have hψi : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hne : ψ ⟨_, hm1⟩ ≠ ψ ⟨_, hm2⟩ := fun h => by
    have := congrArg (fun z : sinCurve => z.1.2) (hψi h)
    norm_num at this
  set u := min (ψ ⟨_, hm1⟩) (ψ ⟨_, hm2⟩)
  set v := max (ψ ⟨_, hm1⟩) (ψ ⟨_, hm2⟩)
  have huv : u < v := min_lt_max.2 hne
  have hpre : IsPreconnected (ψ '' F) := hFc.isPreconnected.image _ hψc.continuousOn
  have hIcc : Icc u v ⊆ ψ '' F := by
    rcases le_total (ψ ⟨_, hm1⟩) (ψ ⟨_, hm2⟩) with h | h
    · simp only [u, v, min_eq_left h, max_eq_right h]
      exact hpre.Icc_subset ⟨_, hF1, rfl⟩ ⟨_, hF2, rfl⟩
    · simp only [u, v, min_eq_right h, max_eq_left h]
      exact hpre.Icc_subset ⟨_, hF2, rfl⟩ ⟨_, hF1, rfl⟩
  set W := ψ ⁻¹' Ioo u v with hW
  have hWo : IsOpen W := isOpen_Ioo.preimage hψc
  have hWF : W ⊆ F := by
    intro z hz
    obtain ⟨w, hwF, hw⟩ := hIcc (Ioo_subset_Icc_self hz)
    rw [← hψi hw]; exact hwF
  have hu0 : 0 ≤ u := le_min (φ _).2.1 (φ _).2.1
  have hv1 : v ≤ 1 := max_le (φ _).2.2 (φ _).2.2
  set m : unitInterval := ⟨(u + v) / 2, by linarith, by linarith⟩
  have hmW : φ.symm m ∈ W := by
    show ((φ (φ.symm m)) : ℝ) ∈ Ioo u v
    rw [φ.apply_symm_apply]
    exact ⟨by show u < (u + v) / 2; linarith, by show (u + v) / 2 < v; linarith⟩
  have : φ.symm m ∈ interior F := interior_maximal hWF hWo hmW
  rw [hF, interior_sinProj_fibre] at this
  exact this

/-- **`arc_of_degenerate_layers` is false as stated**: the `sin (1/x)`-continuum is irreducible
between `(1, sin 1)` and `(0, 0)`, its first projection is admissible with layers of void interior
and degenerate interior layers, and it is not an arc. -/
theorem not_arc_of_degenerate_layers :
    ¬ ∀ (E : Set (ℝ × ℝ)) (a b : ℝ × ℝ), IsIrreducibleBetween E a b → a ≠ b →
      ∀ k : E → unitInterval, IsAdmissibleMap E k → (∀ t, interior (k ⁻¹' {t}) = ∅) →
        (∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton) →
          Nonempty (E ≃ₜ unitInterval) := by
  intro h
  apply not_nonempty_homeomorph_sinCurve
  refine h sinCurve _ _ isIrreducibleBetween_sinCurve ?_ sinProj isAdmissibleMap_sinProj
    interior_sinProj_fibre fun s hs _ => layer_sinProj_subsingleton s hs
  intro he
  have := congrArg Prod.fst he
  norm_num at this

end HPC.Hagopian
