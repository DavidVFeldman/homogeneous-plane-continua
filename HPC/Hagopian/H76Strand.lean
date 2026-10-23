import HPC.Hagopian.Hagopian76U

/-!
# Batch 177: the strand lemma (commission 177 §2, S0–S3, S5, S6)

The resolution near `E` is fixed **before** `D`: an integer `n`, then `θ(n)` (`exists_param_sep`),
then `δ′` from uniform Effros for `θ/4`, then `η = min(δ′, θ/4, 1/n)`, then the height `c(n)` of a
thin strip from `pi_thin_near_layer`. The package of the outputs is the structure `StrandConst`.

* `strand_fine_translate` (S0–S1): fine monotonicity of `θ/4`-translates over the thin strip, and
  every point of `M` over the thin strip is `h(e)` with `|k(e) − s| < 1/n`.
* `strand_closure_subset` (S2): the closure of the component of `M ∩ π⁻¹[D]` through `h(e)` lies in
  `h[E]`.
* `strand_crossing` (S3): if `3/22 + 2/n ≤ k(e) ≤ 19/22 − 2/n`, that component is a crossing
  component, and its closure contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`.
* `strand_inner_middle`: S1 + S3 over the inner middle `[3/22 + 3/n, 19/22 − 3/n]`.
* `strand_fine_positions` (S6), `typeA'_strand` (S5, the whole-strand part).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Strand

variable {M : Set Pt}

/-- **θ(n)** (commission 177 §2, step 2): points of `E` whose parameters differ by at least `1/n`
are at least `θ` apart. -/
theorem exists_param_sep_aux {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (n : ℕ) (hn : 0 < n) :
    ∃ θ > 0, ∀ a b : E, 1 / (n : ℝ) ≤ |(k a : ℝ) - (k b : ℝ)| →
      θ ≤ dist ((a : M) : Pt) ((b : M) : Pt) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  have hk : Continuous k := hE.2.1.1
  set S : Set (E × E) := {p | 1 / (n : ℝ) ≤ |(k p.1 : ℝ) - (k p.2 : ℝ)|} with hS
  have hSc : IsClosed S := isClosed_le continuous_const
    (((continuous_subtype_val.comp (hk.comp continuous_fst))).sub
      (continuous_subtype_val.comp (hk.comp continuous_snd))).abs
  have hg : Continuous fun p : E × E => dist ((p.1 : M) : Pt) ((p.2 : M) : Pt) :=
    ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).dist
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)
  have hpos : ∀ p ∈ S, 0 < dist ((p.1 : M) : Pt) ((p.2 : M) : Pt) := by
    rintro ⟨a, b⟩ hp
    refine dist_pos.2 fun hab => ?_
    have : a = b := Subtype.ext (Subtype.ext hab)
    subst this
    have h1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    simp only [hS, mem_setOf_eq, sub_self, abs_zero] at hp
    linarith
  obtain ⟨c, hc, -, hcS⟩ := exists_pos_lt_on_compact hSc.isCompact hg hpos
  exact ⟨c, hc, fun a b hab => (hcS (a, b) hab).le⟩

/-- **The strand constants** (commission 177 §2, steps 1–4). `θ > 0` separates parameters `1/n`
apart; `c ∈ (0, 1]` is the height of the thin strip `F[[0, 1] × [−c, c]]`;
* `fine` (S0): a `θ/4`-homeomorphism moves a point `z ∈ E` to a point over the thin strip at an
  abscissa within `2/n` of `k(z)`;
* `translate` (S1): every point of `M` over the thin strip at abscissa `s` is `h(e)` for a
  `θ/4`-homeomorphism `h` and `e ∈ E` with `|k(e) − s| < 1/n`. -/
structure StrandConst (E : Set M) (k : E → unitInterval) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (n : ℕ)
    (θ c : ℝ) : Prop where
  θ_pos : 0 < θ
  c_pos : 0 < c
  c_le : c ≤ 1
  fine : ∀ h : M ≃ₜ M, (∀ v, dist (h v) v < θ / 4) → ∀ (z : E) (w : ℝ × ℝ),
    w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c → π (h z : Pt) = F w → |(k z : ℝ) - w.1| < 2 / n
  translate : ∀ (y : M) (w : ℝ × ℝ), w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c → π (y : Pt) = F w →
    ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < θ / 4) ∧ ∃ e : E, h e = y ∧ |(k e : ℝ) - w.1| < 1 / n

/-- **S0–S1** (commission 177 §2). The strand constants exist, for every `n ≥ 1`; none of them
depends on `D`. -/
theorem strand_fine_translate_aux [CompactSpace M] (hX : IsHomogeneous M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    (n : ℕ) (hn : 0 < n) : ∃ θ c, StrandConst E k π F n θ c := by
  obtain ⟨θ, hθ, hsep⟩ := exists_param_sep_aux hE n hn
  have hMc : IsCompact M := isCompact_iff_compactSpace.mpr ‹_›
  obtain ⟨δ, hδ, heff⟩ := HPC.Effros.effros_homogeneous_set hMc hX (ε := θ / 4) (by positivity)
  have hn' : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  set η := min δ (min (θ / 4) (1 / (n : ℝ))) with hη
  have hη0 : 0 < η := lt_min hδ (lt_min (by positivity) hn')
  have hηδ : η ≤ δ := min_le_left _ _
  have hηθ : η ≤ θ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηn : η ≤ 1 / (n : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c, hc, hc1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 0) (b := 1) le_rfl
    le_rfl hη0
  refine ⟨θ, c, ⟨hθ, hc, hc1, ?_, ?_⟩⟩
  · intro h hh z w hw hzw
    obtain ⟨e', -, he'1, he'2⟩ := hthin (h z) w hw hzw
    have hd : dist ((z : M) : Pt) ((e' : M) : Pt) < θ := by
      have h1 := hh (z : M)
      rw [Subtype.dist_eq] at h1
      have := dist_triangle ((z : M) : Pt) ((h z : M) : Pt) ((e' : M) : Pt)
      rw [dist_comm] at h1
      linarith
    have hk : |(k z : ℝ) - (k e' : ℝ)| < 1 / (n : ℝ) := by
      by_contra hcon
      push_neg at hcon
      linarith [hsep z e' hcon]
    have : |(k z : ℝ) - w.1| ≤ |(k z : ℝ) - (k e' : ℝ)| + |(k e' : ℝ) - w.1| := abs_sub_le _ _ _
    have h2 : (2 : ℝ) / n = 1 / n + 1 / n := by ring
    rw [h2]
    linarith
  · intro y w hw hyw
    obtain ⟨e', -, he'1, he'2⟩ := hthin y w hw hyw
    obtain ⟨h, hhe, hh⟩ := heff (e' : M) y (by rw [Subtype.dist_eq, dist_comm]; linarith)
    exact ⟨h, hh, e', hhe, he'1.trans_le hηn⟩

end Strand

/-! ## S2–S3: strands -/

section Strands

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- Over the closure of a crossing domain of height `c₁ ≤ c`, a `θ/4`-translate of `z ∈ E` lies at
an abscissa in `[3/22, 19/22]` within `2/n` of `k(z)` (S0 applied to `Cl D`). -/
theorem strand_off_ends {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {γ : unitInterval → Pt}
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c)
    {c₁ : ℝ} (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (z : E) (hz : π (h z : Pt) ∈ closure (F '' D')) :
    3 / 22 - 2 / (n : ℝ) < (k z : ℝ) ∧ (k z : ℝ) < 19 / 22 + 2 / (n : ℝ) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc1)).isClosed
  obtain ⟨w, ⟨⟨hw1, hw2⟩, hw3, hw4⟩, hFw⟩ := hclD hz
  have := hS.fine h hh z w ⟨⟨by linarith, by linarith⟩, by linarith [hS.c_pos], by linarith⟩
    hFw.symm
  obtain ⟨h1, h2⟩ := abs_lt.1 this
  constructor <;> linarith

/-- **S2: the closure of a component lies in the translate** (commission 177 §2, S2). With the
strand constants, `n ≥ 15` and a crossing domain `D = F[D′]` of height `c₁ ≤ c`: for every
`θ/4`-homeomorphism `h` and `e ∈ E`, the closure of the component of `M ∩ π⁻¹[D]` through `h(e)`
lies in `h[E]`.

*Proof:* the closure is a continuum over `Cl D`; by S0 it misses `h[k⁻¹(0)]` and `h[k⁻¹(1)]`; no hair
for the type A′ continuum `h[E]` (with the transported decomposition, `exists_image_map`). -/
theorem strand_closure_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ}
    (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)}
    (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < θ / 4) (e : E) :
    closure (connectedComponentIn (crossSet univ π F D') (h e)) ⊆ h '' E := by
  set C := connectedComponentIn (crossSet univ π F D') (h e) with hCdef
  by_cases hy : h e ∈ crossSet univ π F D'
  swap
  · rw [hCdef, connectedComponentIn_eq_empty hy, closure_empty]; exact empty_subset _
  have hn' : (2 : ℝ) / n ≤ 2 / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hclO : closure C ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    closure_minimal (fun m hm => subset_closure (connectedComponentIn_subset _ _ hm).2)
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
  have hQ : Fold.Q78.IsContinuum (closure C) :=
    ⟨isClosed_closure.isCompact, ⟨h e, subset_closure (mem_connectedComponentIn hy)⟩,
      isPreconnected_connectedComponentIn.closure⟩
  obtain ⟨b, hb, hbl⟩ := exists_image_map h hE
  have hl : ∀ t, layer b t = h '' layer k t := fun t => hbl {t}
  have hend : ∀ t : unitInterval, ((t : ℝ) = 0 ∨ (t : ℝ) = 1) → Disjoint (closure C) (layer b t) := by
    intro t ht
    rw [hl, disjoint_left]
    rintro _ hq ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hkz : k z = t := hz
    obtain ⟨h1, h2⟩ := strand_off_ends hF hS hc₁ hR h hh z (hclO hq)
    rw [hkz] at h1 h2
    rcases ht with ht | ht <;> rw [ht] at h1 h2 <;> linarith
  exact hagopian76_no_hair hX hi hb hQ
    ⟨h e, subset_closure (mem_connectedComponentIn hy), ⟨e, e.2, rfl⟩⟩
    (hend 0 (Or.inl rfl)) (hend 1 (Or.inr rfl))

/-- **S3: strands cross** (commission 177 §2, S3). Set-up of `strand_closure_subset`. If `h(e)` is
over `D` and `3/22 + 2/n ≤ k(e) ≤ 19/22 − 2/n`, the component `C` of `M ∩ π⁻¹[D]` through `h(e)` is a
crossing component; its closure contains `h(y_L)`, `h(y_R)` with `k(y_L) ≤ k(e) ≤ k(y_R)`,
`|k(y_L) − 3/22| < 2/n`, `|k(y_R) − 19/22| < 2/n`, and the translated middle
`h[k⁻¹((k(y_L), k(y_R)))]`.

*Proof:* boundary bumping in the halves `h[k⁻¹[[0, k(e)]]]`, `h[k⁻¹[[k(e), 1]]]` (their ends are not
over `Cl D`, by S0); a frontier point over the axis is excluded by no hair for `E`, one over the far
side by S0; the middle by `layerSet_Ioo_subset` in `h⁻¹[Cl C] ⊆ E` (S2). -/
theorem strand_crossing (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e : E) (hy : h e ∈ crossSet univ π F D')
    (he1 : 3 / 22 + 2 / (n : ℝ) ≤ (k e : ℝ)) (he2 : (k e : ℝ) ≤ 19 / 22 - 2 / (n : ℝ)) :
    IsCrossingComponent univ π F c₁ D' (connectedComponentIn (crossSet univ π F D') (h e)) ∧
      ∃ yL yR : E, k yL ≤ k e ∧ k e ≤ k yR ∧ |(k yL : ℝ) - 3 / 22| < 2 / (n : ℝ) ∧
        |(k yR : ℝ) - 19 / 22| < 2 / (n : ℝ) ∧
        h yL ∈ closure (connectedComponentIn (crossSet univ π F D') (h e)) ∧
        h yR ∈ closure (connectedComponentIn (crossSet univ π F D') (h e)) ∧
        h '' layerSet k (Ioo (k yL) (k yR)) ⊆
          closure (connectedComponentIn (crossSet univ π F D') (h e)) := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hn' : (2 : ℝ) / n ≤ 2 / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set y : M := h e with hydef
  set C := connectedComponentIn (crossSet univ π F D') y with hCdef
  set O : Set M := {m | π (m : Pt) ∈ F '' D'} with hOdef
  have hOo : IsOpen O := hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  have hcrO : crossSet univ π F D' = O := by
    ext m; simp [crossSet, hOdef]
  have hyO : y ∈ O := by rw [← hcrO]; exact hy
  obtain ⟨z, hzD, hyz⟩ := hyO
  have hzS := hR.sub hzD
  have hclO : ∀ C ⊆ O, closure C ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := fun C hC =>
    closure_minimal (fun m hm => subset_closure (hC hm))
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc1)).isClosed
  have hfr : ∀ q : M, π (q : Pt) ∈ closure (F '' D') → q ∉ O →
      (∃ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) = F (t, 0)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (3 / 22, w)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (19 / 22, w)) := by
    intro q hq hqO
    have hfront : π (q : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hq, hqO⟩
    rcases hR.frontier_sub ⟨hfront, ⟨q, q.2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact Or.inl ⟨z₁, hz1, hFz.symm⟩
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inl ⟨z₂, hz2, hFz.symm⟩)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inr ⟨z₂, hz2, hFz.symm⟩)
  have hside : ∀ (y' : E) (t w : ℝ), t ∈ Icc (0 : ℝ) 1 → w ∈ Icc 0 c₁ →
      π (h y' : Pt) = F (t, w) → |(k y' : ℝ) - t| < 2 / n := fun y' t w ht hw hq =>
    hS.fine h hh y' (t, w) ⟨ht, by linarith [hw.1, hS.c_pos], hw.2.trans hc₁⟩ hq
  /- Points of `E` outside `[3/22, 19/22]` are not over `Cl D`. -/
  have hEout : ∀ e : E, ((k e : ℝ) < 3 / 22 ∨ 19 / 22 < (k e : ℝ)) →
      π ((e : M) : Pt) ∉ closure (F '' D') := by
    intro e hke hcl
    obtain ⟨w, hw, hFw⟩ := hclD hcl
    have := collar_injOn hF ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩
      ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      ((pi_E_eq hγπ hF e).symm.trans hFw.symm)
    have h1 : (k e : ℝ) = w.1 := congrArg Prod.fst this
    rcases hke with hke | hke <;> linarith [hw.1.1, hw.1.2]
  /- `y` is not in `E` (it is over `D`, above the axis). -/
  have hyE : y ∉ E := by
    intro hyE
    have := collar_injOn hF ⟨⟨(k ⟨y, hyE⟩).2.1, (k ⟨y, hyE⟩).2.2⟩, by norm_num, by norm_num⟩
      ⟨⟨by linarith [hzS.1.1], by linarith [hzS.1.2]⟩, by linarith [hzS.2.1],
        by linarith [hzS.2.2]⟩ ((pi_E_eq hγπ hF ⟨y, hyE⟩).symm.trans hyz.symm)
    have h2 : (0 : ℝ) = z.2 := congrArg Prod.snd this
    linarith [hzS.2.1]
  have hnoaxis : ∀ Z : Set M, IsPreconnected Z → y ∈ Z → Z ⊆ O → ∀ q ∈ closure Z,
      ∀ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) ≠ F (t, 0) := by
    intro Z hZ hyZ hZO q hq t ht hqt
    have hqE := mem_E_of_axis hE hπS hγπ hF ⟨by linarith [ht.1], by linarith [ht.2]⟩ hqt
    have hZc : Fold.Q78.IsContinuum (closure Z) :=
      ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyZ⟩, hZ.closure⟩
    have hend' : ∀ s : unitInterval, ((s : ℝ) < 3 / 22 ∨ 19 / 22 < (s : ℝ)) →
        Disjoint (closure Z) (layer k s) := by
      intro s hs
      rw [disjoint_left]
      rintro p hp ⟨e, hes, rfl⟩
      have hke : k e = s := by rwa [mem_preimage, mem_singleton_iff] at hes
      exact hEout e (by rw [hke]; exact hs) (hclO Z hZO hp)
    have hsub := hagopian76_no_hair hX hi hE hZc ⟨q, hq, hqE⟩
      (hend' 0 (Or.inl (by norm_num))) (hend' 1 (Or.inr (by norm_num)))
    exact hyE (hsub (subset_closure hyZ))
  /- The two halves of the translate, bumped. -/
  have hhalf : ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → k e ∈ S →
      ∀ y' : E, k y' ∈ S → h y' ∉ O →
      ∃ Z : Set M, IsPreconnected Z ∧ y ∈ Z ∧ Z ⊆ C ∧ Z ⊆ O ∧
        ∃ y'' : E, k y'' ∈ S ∧ h y'' ∉ O ∧ h y'' ∈ closure Z := by
    intro S hS' hSp hxS y' hy'S hy'O
    have hK : Fold.Q78.IsContinuum (h '' layerSet k S) :=
      isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1 hS' hSp ⟨_, hxS⟩)
    have hyK : y ∈ h '' layerSet k S := ⟨e, ⟨e, hxS, rfl⟩, rfl⟩
    have hKO : ¬ h '' layerSet k S ⊆ O := fun hsub =>
      hy'O (hsub ⟨y', ⟨y', hy'S, rfl⟩, rfl⟩)
    obtain ⟨q, hqK, hqO, hqcl⟩ := exists_mem_closure_component_notMem hK.1 hK.2.isPreconnected
      hOo hyK (by rw [← hcrO]; exact hy) hKO
    set Z := connectedComponentIn (h '' layerSet k S ∩ O) y
    have hZO : Z ⊆ O := (connectedComponentIn_subset _ _).trans inter_subset_right
    have hZC : Z ⊆ C := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hyK, by rw [← hcrO]; exact hy⟩) (by rw [hcrO]; exact hZO)
    obtain ⟨_, ⟨y'', hy'', rfl⟩, rfl⟩ := hqK
    exact ⟨Z, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn ⟨hyK, by rw [← hcrO]; exact hy⟩, hZC, hZO, y'', hy'', hqO, hqcl⟩
  obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
  have hk₀ : (k y₀ : ℝ) = 0 := by rw [hy₀]; rfl
  have hk₁ : (k y₁ : ℝ) = 1 := by rw [hy₁]; rfl
  have hy₀O : h y₀ ∉ O := fun hO => by
    have := (strand_off_ends hF hS hc₁ hR h hh y₀ (subset_closure hO)).1
    linarith
  have hy₁O : h y₁ ∉ O := fun hO => by
    have := (strand_off_ends hF hS hc₁ hR h hh y₁ (subset_closure hO)).2
    linarith
  obtain ⟨ZL, hZL, hyZL, hZLC, hZLO, yL, hyL, hyLO, hyLcl⟩ := hhalf (Iic (k e)) isClosed_Iic
    isPreconnected_Iic (mem_Iic.2 le_rfl) y₀
    (show k y₀ ≤ k e by rw [hy₀]; exact unitInterval.nonneg') hy₀O
  obtain ⟨ZR, hZR, hyZR, hZRC, hZRO, yR, hyR, hyRO, hyRcl⟩ := hhalf (Ici (k e)) isClosed_Ici
    isPreconnected_Ici (mem_Ici.2 le_rfl) y₁
    (show k e ≤ k y₁ by rw [hy₁]; exact unitInterval.le_one') hy₁O
  have hkyL : (k yL : ℝ) ≤ k e := Subtype.coe_le_coe.2 (mem_Iic.1 hyL)
  have hkyR : (k e : ℝ) ≤ k yR := Subtype.coe_le_coe.2 (mem_Ici.1 hyR)
  have hL : ∃ w ∈ Icc 0 c₁, π (h yL : Pt) = F (3 / 22, w) := by
    rcases hfr _ (hclO _ hZLO hyLcl) hyLO with ⟨t, ht, hq⟩ | hq | ⟨w, hw, hq⟩
    · exact absurd hq (hnoaxis ZL hZL hyZL hZLO _ hyLcl t ht)
    · exact hq
    · have := (abs_lt.1 (hside yL _ w (by norm_num) hw hq)).1
      linarith
  have hRt : ∃ w ∈ Icc 0 c₁, π (h yR : Pt) = F (19 / 22, w) := by
    rcases hfr _ (hclO _ hZRO hyRcl) hyRO with ⟨t, ht, hq⟩ | ⟨w, hw, hq⟩ | hq
    · exact absurd hq (hnoaxis ZR hZR hyZR hZRO _ hyRcl t ht)
    · have := (abs_lt.1 (hside yR _ w (by norm_num) hw hq)).2
      linarith
    · exact hq
  obtain ⟨wL, hwL, hFL⟩ := hL
  obtain ⟨wR, hwR, hFR⟩ := hRt
  have hyLC : h yL ∈ closure C := closure_mono hZLC hyLcl
  have hyRC : h yR ∈ closure C := closure_mono hZRC hyRcl
  refine ⟨⟨⟨y, hy, rfl⟩, ⟨h yL, hyLC, ⟨(3 / 22, wL), ⟨rfl, hwL⟩, hFL.symm⟩⟩,
    ⟨h yR, hyRC, ⟨(19 / 22, wR), ⟨rfl, hwR⟩, hFR.symm⟩⟩⟩, yL, yR, mem_Iic.1 hyL, mem_Ici.1 hyR,
    hside yL _ wL (by norm_num) hwL hFL, hside yR _ wR (by norm_num) hwR hFR, hyLC, hyRC, ?_⟩
  /- The translated middle. -/
  have hsub := strand_closure_subset hX hi hE hπc hF hS hn hc₁ hR h hh e
  set K := h.symm '' closure C with hKdef
  have hKE : K ⊆ E := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hsub hq
    simpa using hx
  have hKc : Fold.Q78.IsContinuum K :=
    isContinuum_homeo_image h.symm ⟨isClosed_closure.isCompact,
      ⟨y, subset_closure (mem_connectedComponentIn hy)⟩,
      isPreconnected_connectedComponentIn.closure⟩
  have hmem : ∀ x : E, h x ∈ closure C → (K ∩ layer k (k x)).Nonempty := fun x hx =>
    ⟨x, ⟨h x, hx, h.symm_apply_apply _⟩, ⟨x, rfl, rfl⟩⟩
  have := layerSet_Ioo_subset hE hKE hKc (hmem yL hyLC) (hmem yR hyRC)
  calc h '' layerSet k (Ioo (k yL) (k yR)) ⊆ h '' K := image_mono this
    _ = closure C := by rw [hKdef, image_image]; simp

end Strands

end HPC.Hagopian
