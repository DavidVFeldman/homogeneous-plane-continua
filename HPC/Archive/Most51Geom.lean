import HPC.Plane.Most51

/-!
# Batch 90, item 7: partial constructions for the geometric lemma

COMMISSION-batch90.md §3.7. This file holds what was proved towards the batch-90 geometric lemma
`exists_tame_chain_near` (the conclusion of `GeomLemma E` for `dim E ≥ 2`). That statement was
deleted in batch 111 (`LEDGER.md` §2) and replaced by the weaker `geomLemma'_of_two_le_rank`, now
proved in every dimension `≥ 2` (batch 113, `HPC/Plane/CubeCycle.lean`; in the plane already as
`geomLemma'_of_finrank_two`, batch 110). The names
below that mention `exists_tame_chain_near` refer to the conclusion of `GeomLemma`.

* **Tame chains in `E`** (`stdBoxChain`, `Chain.mapHomeo`, `tameChainE`): the standard boxes form
  a chain, and the image of a chain under a homeomorphism is a chain, so every homeomorphism of
  `E` and orthonormal pair gives a tame chain of any length.
* **Shears** (`shear`): `x ↦ x + f ⟪x, e₁⟫` with `f ⊥ e₁` is a homeomorphism of `E`.
* **The tube around an unbent arc** (`exists_tame_chain_near_graph`): for an arc
  `t ↦ p + t e₁ + f t` (`0 ≤ t ≤ L`, `f ⊥ e₁`) — a graph over the line `p + ℝ e₁` — the
  conclusion of the geometric lemma holds, with the homeomorphism a scaling, a shear and a
  translation. Corollaries: the geometric lemma for every continuum Hausdorff-approximable by such
  graph arcs (`exists_tame_chain_near_of_graph_approx`), in particular for points and straight
  segments (`exists_tame_chain_near_segment`), in every real inner product space of dimension
  `≥ 2`.
* **Bing's broken line** (`exists_eps_walk`, `exists_broken_line_near`): a compact connected set
  is within `ε` (both ways) of a polygonal path through finitely many of its points, in any
  normed space. The path is not simple.

What is not done (the obstruction): making the broken line simple (plane topology in dimension 2,
general position in dimension `≥ 3`), and bending the tube at its corners by a homeomorphism of
`E`. A graph over a line cannot turn back, so the shear construction covers only continua that are
close to such graphs (a circle is not).
-/

namespace HPC.Plane

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Most

theorem isOpen_stdBox (e₁ e₂ : E) (j : ℕ) : IsOpen (stdBox e₁ e₂ j) := by
  have c1 : Continuous fun x : E => inner ℝ x e₁ := continuous_id.inner continuous_const
  have c2 : Continuous fun x : E => inner ℝ x e₂ := continuous_id.inner continuous_const
  have c3 : Continuous fun x : E => ‖x - (inner ℝ x e₁) • e₁ - (inner ℝ x e₂) • e₂‖ :=
    ((continuous_id.sub (c1.smul continuous_const)).sub (c2.smul continuous_const)).norm
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt c1 continuous_const).inter
    ((isOpen_lt continuous_const c2).inter ((isOpen_lt c2 continuous_const).inter
      (isOpen_lt c3 continuous_const))))

theorem stdBox_inter_nonempty_iff {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (j k : ℕ) :
    (stdBox e₁ e₂ j ∩ stdBox e₁ e₂ k).Nonempty ↔ ((j : ℤ) - (k : ℤ)).natAbs ≤ 1 := by
  constructor
  · rintro ⟨x, ⟨h1, h2, -⟩, ⟨k1, k2, -⟩⟩
    have hjk : j ≤ k + 1 := by
      by_contra h
      push_neg at h
      have : (k : ℝ) + 2 ≤ j := by exact_mod_cast h
      linarith
    have hkj : k ≤ j + 1 := by
      by_contra h
      push_neg at h
      have : (j : ℝ) + 2 ≤ k := by exact_mod_cast h
      linarith
    omega
  · intro h
    have hjk : j ≤ k + 1 ∧ k ≤ j + 1 := by omega
    refine ⟨planeMap e₁ e₂ (2 * (max j k : ℕ) + 1 / 2, 1 / 2), planeMap_stdRect hon j ⟨_, ?_, rfl⟩,
      planeMap_stdRect hon k ⟨_, ?_, rfl⟩⟩
    · rcases le_total j k with h' | h'
      · rw [max_eq_right h']
        have : (k : ℝ) ≤ j + 1 := by exact_mod_cast hjk.2
        have : (j : ℝ) ≤ k := by exact_mod_cast h'
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith
      · rw [max_eq_left h']
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith
    · rcases le_total j k with h' | h'
      · rw [max_eq_right h']
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith
      · rw [max_eq_left h']
        have : (j : ℝ) ≤ k + 1 := by exact_mod_cast hjk.1
        have : (k : ℝ) ≤ j := by exact_mod_cast h'
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith

/-- The standard box chain of `E` with `m` links. -/
def stdBoxChain {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (m : ℕ) : Chain E m where
  link j := stdBox e₁ e₂ j
  isOpen j := isOpen_stdBox e₁ e₂ j
  adjacent i j := stdBox_inter_nonempty_iff hon i j

end Most

/-- The image of a chain under a homeomorphism. -/
def _root_.HPC.Chain.mapHomeo {X Y : Type*} [MetricSpace X] [MetricSpace Y] {m : ℕ} (Φ : X ≃ₜ Y)
    (D : Chain X m) : Chain Y m where
  link j := Φ '' D.link j
  isOpen j := Φ.isOpenMap _ (D.isOpen j)
  adjacent i j := by
    rw [← image_inter Φ.injective, image_nonempty]
    exact D.adjacent i j

namespace Most

/-- The tame chain `Φ(stdBox j)`, `j < m`. -/
def tameChainE {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (Φ : E ≃ₜ E) (m : ℕ) : Chain E m :=
  (stdBoxChain hon m).mapHomeo Φ

theorem isTameChain_tameChainE {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (Φ : E ≃ₜ E)
    (m : ℕ) : IsTameChain (tameChainE hon Φ m) :=
  ⟨e₁, e₂, hon, Φ, fun _ => rfl⟩

/-- A shear `x ↦ x + f ⟪x, e₁⟫` along a continuous `f` orthogonal to `e₁` is a homeomorphism. -/
def shear (e₁ : E) (f : ℝ → E) (hf : Continuous f) (hperp : ∀ t, inner ℝ (f t) e₁ = 0) :
    E ≃ₜ E where
  toFun x := x + f (inner ℝ x e₁)
  invFun y := y - f (inner ℝ y e₁)
  left_inv x := by
    simp only [inner_add_left, hperp, add_zero, add_sub_cancel_right]
  right_inv y := by
    simp only [inner_sub_left, hperp, sub_zero, sub_add_cancel]
  continuous_toFun := continuous_id.add (hf.comp (continuous_id.inner continuous_const))
  continuous_invFun := continuous_id.sub (hf.comp (continuous_id.inner continuous_const))

theorem norm_sub_inner_smul_lt {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {j : ℕ} {x : E}
    (hx : x ∈ stdBox e₁ e₂ j) : ‖x - (inner ℝ x e₁) • e₁‖ < 2 := by
  obtain ⟨-, -, h3, h4, h5⟩ := hx
  have h2 : ‖e₂‖ = 1 := by simpa using hon.1 1
  have e : x - (inner ℝ x e₁) • e₁ =
      (x - (inner ℝ x e₁) • e₁ - (inner ℝ x e₂) • e₂) + (inner ℝ x e₂) • e₂ := by abel
  rw [e]
  calc _ ≤ ‖x - (inner ℝ x e₁) • e₁ - (inner ℝ x e₂) • e₂‖ + ‖(inner ℝ x e₂) • e₂‖ :=
        norm_add_le _ _
    _ < 1 + 1 := by
        rw [norm_smul, h2, mul_one, Real.norm_eq_abs, abs_of_pos h3]
        linarith
    _ = 2 := by norm_num

/-- **The tube around an unbent arc.** For the arc `γ t = p + t e₁ + f t`, `0 ≤ t ≤ L`, with `f`
continuous and orthogonal to `e₁` (a graph over the line `p + ℝ e₁`), there are tame chains of
arbitrarily small mesh whose union is within `ε` of the arc and within `ε` of which the arc lies.
The homeomorphism is `x ↦ p + c x + f (c ⟪x, e₁⟫)`. -/
theorem exists_tame_chain_near_graph {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) (f : ℝ → E)
    (hf : Continuous f) (hperp : ∀ t, inner ℝ (f t) e₁ = 0) (p : E) {L : ℝ} (hL : 0 < L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsTameChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε ((fun t => p + t • e₁ + f t) '' Icc 0 L) ∧
      (fun t => p + t • e₁ + f t) '' Icc 0 L ⊆ thickening ε D.union := by
  have h1 : ‖e₁‖ = 1 := by simpa using hon.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using hon.1 1
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (L * (16 / ε) + L * (3 / δ))
  set m : ℕ := max 3 N with hm_def
  have hm3 : 3 ≤ m := le_max_left _ _
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast le_max_right 3 N
  have hM : (0 : ℝ) < 2 * m + 1 := by positivity
  set c : ℝ := L / (2 * m + 1) with hc_def
  have hc : 0 < c := div_pos hL hM
  have hcL : c * (2 * m + 1) = L := by rw [hc_def]; field_simp
  have hA : L * (16 / ε) ≤ 2 * m + 1 := by
    have : 0 ≤ L * (3 / δ) := by positivity
    linarith
  have hB : L * (3 / δ) ≤ 2 * m + 1 := by
    have : 0 ≤ L * (16 / ε) := by positivity
    linarith
  have hcε : c ≤ ε / 16 := by
    rw [hc_def, div_le_iff₀ hM]
    calc L = (ε / 16) * (L * (16 / ε)) := by field_simp
      _ ≤ (ε / 16) * (2 * m + 1) := by gcongr
  have hcδ : 3 * c ≤ δ := by
    rw [hc_def, ← mul_div_assoc, div_le_iff₀ hM]
    calc 3 * L = δ * (L * (3 / δ)) := by field_simp
      _ ≤ δ * (2 * m + 1) := by gcongr
  set Φ : E ≃ₜ E := (Homeomorph.smulOfNeZero c hc.ne').trans
    ((shear e₁ f hf hperp).trans (Homeomorph.addLeft p)) with hΦ
  have hΦx : ∀ x, Φ x = p + (c • x + f (c * inner ℝ x e₁)) := by
    intro x
    simp [Φ, shear, real_inner_smul_left]
  set γ : ℝ → E := fun t => p + t • e₁ + f t with hγ
  set D := tameChainE hon Φ m
  have hlink : ∀ j, D.link j = Φ '' stdBox e₁ e₂ j := fun j => rfl
  have hunion : D.union = ⋃ j : Fin m, Φ '' stdBox e₁ e₂ j := rfl
  have hsj : ∀ (j : Fin m) (x : E), x ∈ stdBox e₁ e₂ j →
      0 < c * inner ℝ x e₁ ∧ c * inner ℝ x e₁ < L := by
    intro j x hx
    obtain ⟨k1, k2, -⟩ := hx
    have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    constructor
    · exact mul_pos hc (by linarith)
    · rw [← hcL]; exact mul_lt_mul_of_pos_left (by linarith) hc
  have hΦγ : ∀ x, Φ x - γ (c * inner ℝ x e₁) = c • (x - (inner ℝ x e₁) • e₁) := by
    intro x
    rw [hΦx, smul_sub, smul_smul]
    simp only [γ]
    abel
  refine ⟨m, D, hm3, isTameChain_tameChainE hon Φ m, fun j => ?_, ?_, ?_⟩
  · -- the links are small
    have hle : diam (D.link j) ≤ 11 * ε / 16 := by
      rw [hlink]
      refine diam_le_of_forall_dist_le (by positivity) ?_
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨hx0, hxL⟩ := hsj j x hx
      obtain ⟨hy0, hyL⟩ := hsj j y hy
      have hxy : |c * inner ℝ x e₁ - c * inner ℝ y e₁| ≤ δ := by
        obtain ⟨k1, k2, -⟩ := hx
        obtain ⟨l1, l2, -⟩ := hy
        rw [← mul_sub, abs_mul, abs_of_pos hc]
        have : |inner ℝ x e₁ - inner ℝ y e₁| ≤ 3 := by rw [abs_le]; constructor <;> linarith
        nlinarith
      have hfxy := hδf _ ⟨hx0.le, hxL.le⟩ _ ⟨hy0.le, hyL.le⟩ (by rwa [Real.dist_eq])
      have hnx := norm_sub_inner_smul_lt hon hx
      have hny := norm_sub_inner_smul_lt hon hy
      have hxy' : ‖x - y‖ ≤ 7 := by
        have e : x - y = (x - (inner ℝ x e₁) • e₁) - (y - (inner ℝ y e₁) • e₁) +
            (inner ℝ x e₁ - inner ℝ y e₁) • e₁ := by rw [sub_smul]; abel
        rw [e]
        have hd : |inner ℝ x e₁ - inner ℝ y e₁| ≤ 3 := by
          obtain ⟨k1, k2, -⟩ := hx
          obtain ⟨l1, l2, -⟩ := hy
          rw [abs_le]; constructor <;> linarith
        calc _ ≤ ‖(x - (inner ℝ x e₁) • e₁) - (y - (inner ℝ y e₁) • e₁)‖ +
              ‖(inner ℝ x e₁ - inner ℝ y e₁) • e₁‖ := norm_add_le _ _
          _ ≤ (‖x - (inner ℝ x e₁) • e₁‖ + ‖y - (inner ℝ y e₁) • e₁‖) + 3 := by
              gcongr
              · exact norm_sub_le _ _
              · rw [norm_smul, h1, mul_one, Real.norm_eq_abs]; exact hd
          _ ≤ 7 := by linarith
      rw [dist_eq_norm, hΦx, hΦx]
      have e : p + (c • x + f (c * inner ℝ x e₁)) - (p + (c • y + f (c * inner ℝ y e₁))) =
          c • (x - y) + (f (c * inner ℝ x e₁) - f (c * inner ℝ y e₁)) := by
        rw [smul_sub]; abel
      rw [e]
      calc _ ≤ ‖c • (x - y)‖ + ‖f (c * inner ℝ x e₁) - f (c * inner ℝ y e₁)‖ := norm_add_le _ _
        _ ≤ c * 7 + ε / 4 := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]; gcongr
            · rw [← dist_eq_norm]; exact hfxy
        _ ≤ 11 * ε / 16 := by linarith
    calc diam (D.link j) ≤ 11 * ε / 16 := hle
      _ < ε := by linarith
  · -- the union is near the arc
    intro z hz
    rw [hunion] at hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := hj
    obtain ⟨hx0, hxL⟩ := hsj j x hx
    rw [mem_thickening_iff]
    refine ⟨γ (c * inner ℝ x e₁), ⟨_, ⟨hx0.le, hxL.le⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm, hΦγ, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have := norm_sub_inner_smul_lt hon hx
    nlinarith
  · -- the arc is near the union
    rintro _ ⟨t, ⟨ht0, htL⟩, rfl⟩
    set s₀ : ℝ := t / c with hs₀
    have hs₀0 : 0 ≤ s₀ := div_nonneg ht0 hc.le
    have hs₀M : s₀ ≤ 2 * m + 1 := by
      rw [hs₀, div_le_iff₀ hc]; linarith
    set q : ℕ := ⌊s₀ / 2⌋₊ with hq
    have hq1 : (q : ℝ) ≤ s₀ / 2 := Nat.floor_le (by positivity)
    have hq2 : s₀ / 2 < q + 1 := Nat.lt_floor_add_one _
    set j : ℕ := min q (m - 1) with hj_def
    have hjm : j < m := by omega
    set s : ℝ := 2 * (j : ℝ) + 3 / 2 with hs_def
    have hss : |s - s₀| ≤ 3 / 2 := by
      rcases le_total q (m - 1) with h | h
      · have : j = q := min_eq_left h
        rw [hs_def, this, abs_le]; constructor <;> linarith
      · have hj' : j = m - 1 := min_eq_right h
        have hm1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
        have hqm : (m : ℝ) - 1 ≤ q := by rw [← hm1]; exact_mod_cast h
        rw [hs_def, hj', hm1, abs_le]; constructor <;> linarith
    set x : E := planeMap e₁ e₂ (s, 1 / 2) with hx_def
    have hx : x ∈ stdBox e₁ e₂ j := planeMap_stdRect hon j ⟨_, by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num [hs_def], rfl⟩
    obtain ⟨hxs, hx2⟩ := inner_planeMap hon (s, 1 / 2)
    rw [← hx_def] at hxs
    simp only at hxs
    have hmem : Φ x ∈ D.union := hunion ▸ mem_iUnion.mpr ⟨⟨j, hjm⟩, ⟨x, hx, rfl⟩⟩
    rw [mem_thickening_iff]
    refine ⟨Φ x, hmem, ?_⟩
    obtain ⟨hcs0, hcsL⟩ := hsj ⟨j, hjm⟩ x hx
    rw [hxs] at hcs0 hcsL
    have hcst : |c * s - t| ≤ 3 * c / 2 := by
      have : c * s - t = c * (s - s₀) := by rw [hs₀]; field_simp
      rw [this, abs_mul, abs_of_pos hc]; nlinarith
    have hf' := hδf _ ⟨hcs0.le, hcsL.le⟩ t ⟨ht0, htL⟩ (by rw [Real.dist_eq]; linarith)
    have e : γ t - Φ x = ((t - c * s) • e₁ - (c / 2) • e₂) + (f t - f (c * s)) := by
      rw [hΦx, hxs, hx_def]
      simp only [γ, planeMap, smul_add, smul_smul, sub_smul]
      ring_nf
      abel
    rw [dist_eq_norm, e]
    calc _ ≤ ‖(t - c * s) • e₁ - (c / 2) • e₂‖ + ‖f t - f (c * s)‖ := norm_add_le _ _
      _ ≤ (‖(t - c * s) • e₁‖ + ‖(c / 2) • e₂‖) + ε / 4 := by
          gcongr
          · exact norm_sub_le _ _
          · rw [← dist_eq_norm, dist_comm]; exact hf'
      _ = (|t - c * s| + c / 2) + ε / 4 := by
          rw [norm_smul, norm_smul, h1, h2, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < c / 2)]
          ring
      _ < ε := by
          rw [abs_sub_comm]
          linarith

/-- In dimension `≥ 2`, every vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal (hdim : 2 ≤ Module.rank ℝ E) (v : E) :
    ∃ u : E, ‖u‖ = 1 ∧ inner ℝ v u = 0 := by
  by_contra h
  push_neg at h
  have hK : (ℝ ∙ v)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    by_contra hw0
    apply h (‖w‖⁻¹ • w)
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
    · rw [real_inner_smul_right, hw, mul_zero]
  rw [Submodule.orthogonal_eq_bot_iff] at hK
  have h1 : Module.rank ℝ E ≤ 1 := by
    rw [← rank_top ℝ E, ← hK]
    calc Module.rank ℝ (ℝ ∙ v) ≤ Cardinal.mk ({v} : Set E) := rank_span_le _
      _ = 1 := Cardinal.mk_singleton v
  have : (2 : Cardinal) ≤ 1 := hdim.trans h1
  norm_num at this

theorem orthonormal_pair {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : inner ℝ e₁ e₂ = 0) :
    Orthonormal ℝ ![e₁, e₂] := by
  have h21 : inner ℝ e₂ e₁ = 0 := by rw [real_inner_comm]; exact h12
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simpa
  · fin_cases i <;> fin_cases j <;> simp_all

/-- In dimension `≥ 2`, every unit vector is the first vector of an orthonormal pair. -/
theorem exists_orthonormal_pair (hdim : 2 ≤ Module.rank ℝ E) {e₁ : E} (h1 : ‖e₁‖ = 1) :
    ∃ e₂ : E, Orthonormal ℝ ![e₁, e₂] := by
  obtain ⟨e₂, h2, h12⟩ := exists_unit_orthogonal hdim e₁
  exact ⟨e₂, orthonormal_pair h1 h2 h12⟩

/-- **The geometric lemma for continua close to unbent arcs.** If `g` lies within `ε/2` of an arc
`t ↦ p + t e₁ + f t` (`0 ≤ t ≤ L`, `f ⊥ e₁`) and that arc lies within `ε/2` of `g`, the
conclusion of `exists_tame_chain_near` holds for `g` and `ε`. -/
theorem exists_tame_chain_near_of_graph_approx {g : Set E} {ε : ℝ} (hε : 0 < ε) {e₁ e₂ : E}
    (hon : Orthonormal ℝ ![e₁, e₂]) (f : ℝ → E) (hf : Continuous f)
    (hperp : ∀ t, inner ℝ (f t) e₁ = 0) (p : E) {L : ℝ} (hL : 0 < L)
    (hgK : g ⊆ thickening (ε / 2) ((fun t => p + t • e₁ + f t) '' Icc 0 L))
    (hKg : (fun t => p + t • e₁ + f t) '' Icc 0 L ⊆ thickening (ε / 2) g) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsTameChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε g ∧ g ⊆ thickening ε D.union := by
  obtain ⟨m, D, hm, hD, hdiam, hDK, hKD⟩ :=
    exists_tame_chain_near_graph hon f hf hperp p hL (half_pos hε)
  refine ⟨m, D, hm, hD, fun j => (hdiam j).trans (half_lt_self hε), ?_, ?_⟩
  · refine hDK.trans ((thickening_subset_of_subset _ hKg).trans ?_)
    refine (thickening_thickening_subset _ _ _).trans (le_of_eq ?_)
    rw [add_halves]
  · refine hgK.trans ((thickening_subset_of_subset _ hKD).trans ?_)
    refine (thickening_thickening_subset _ _ _).trans (le_of_eq ?_)
    rw [add_halves]

/-- **The geometric lemma for points and straight segments**, in every real inner product space of
dimension at least two. -/
theorem exists_tame_chain_near_segment (hdim : 2 ≤ Module.rank ℝ E) (p q : E) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsTameChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε (segment ℝ p q) ∧ segment ℝ p q ⊆ thickening ε D.union := by
  have hperp : ∀ (e : E) (t : ℝ), inner ℝ ((fun _ : ℝ => (0 : E)) t) e = 0 := fun e t => by
    simp
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq
    obtain ⟨e₁, h1, -⟩ := exists_unit_orthogonal hdim (0 : E)
    obtain ⟨e₂, hon⟩ := exists_orthonormal_pair hdim h1
    refine exists_tame_chain_near_of_graph_approx hε hon (fun _ => 0) continuous_const
      (hperp e₁) p (L := ε / 4) (by positivity) ?_ ?_
    · rw [segment_same]
      rintro _ rfl
      refine mem_thickening_iff.mpr ⟨_, ⟨0, ⟨le_rfl, by positivity⟩, rfl⟩, ?_⟩
      simp [hε]
    · rintro _ ⟨t, ⟨ht0, htL⟩, rfl⟩
      rw [segment_same]
      refine mem_thickening_iff.mpr ⟨p, rfl, ?_⟩
      simp only [add_zero, dist_eq_norm, add_sub_cancel_left, norm_smul, h1, mul_one,
        Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith
  · set L := ‖q - p‖ with hL_def
    have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
    set e₁ : E := L⁻¹ • (q - p) with he₁
    have h1 : ‖e₁‖ = 1 := by
      rw [he₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hL.ne']
    obtain ⟨e₂, hon⟩ := exists_orthonormal_pair hdim h1
    have hK : (fun t => p + t • e₁ + (fun _ : ℝ => (0 : E)) t) '' Icc 0 L = segment ℝ p q := by
      rw [segment_eq_image']
      ext z
      simp only [mem_image, mem_Icc, add_zero]
      constructor
      · rintro ⟨t, ⟨ht0, htL⟩, rfl⟩
        refine ⟨t / L, ⟨div_nonneg ht0 hL.le, (div_le_one hL).mpr htL⟩, ?_⟩
        rw [he₁, smul_smul, div_eq_mul_inv]
      · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
        refine ⟨θ * L, ⟨mul_nonneg h0 hL.le, by nlinarith⟩, ?_⟩
        rw [he₁, smul_smul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
    have := exists_tame_chain_near_of_graph_approx hε hon (fun _ => 0) continuous_const
      (hperp e₁) p hL (g := segment ℝ p q)
      (by rw [hK]; exact self_subset_thickening (half_pos hε) _)
      (by rw [hK]; exact self_subset_thickening (half_pos hε) _)
    exact this

/-! ### Bing's broken line (not simple) -/

section Walk

variable {X : Type*} [MetricSpace X]

/-- An `ε`-walk of length `N` in `g`: points `x 0, …, x N` of `g`, consecutive ones closer than
`ε`. -/
def IsWalk (g : Set X) (ε : ℝ) (N : ℕ) (x : ℕ → X) : Prop :=
  (∀ k ≤ N, x k ∈ g) ∧ ∀ k < N, dist (x k) (x (k + 1)) < ε

theorem IsWalk.append {g : Set X} {ε : ℝ} {M N : ℕ} {c w : ℕ → X} (hc : IsWalk g ε M c)
    (hw : IsWalk g ε N w) (hcw : c M = w 0) :
    IsWalk g ε (M + N) (fun k => if k ≤ M then c k else w (k - M)) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · by_cases h : k ≤ M
    · simp only [h, if_true]; exact hc.1 k h
    · simp only [h, if_false]; exact hw.1 _ (by omega)
  · by_cases h : k + 1 ≤ M
    · simp only [h, show k ≤ M by omega, if_true]; exact hc.2 k (by omega)
    · by_cases h' : k = M
      · subst h'
        simp only [le_refl, if_true, h, if_false, Nat.add_sub_cancel_left, hcw]
        have := hw.2 0 (by omega)
        simpa using this
      · simp only [h, show ¬ k ≤ M by omega, if_false]
        have := hw.2 (k - M) (by omega)
        rwa [show k + 1 - M = k - M + 1 by omega]

/-- **Bing's broken line, combinatorial part.** A compact connected set `g` admits, for every
`ε > 0`, an `ε`-walk through finitely many of its points whose `ε`-balls cover `g`. -/
theorem exists_eps_walk {g : Set X} (hc : IsCompact g) (hconn : IsConnected g) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (x : ℕ → X), IsWalk g ε N x ∧ g ⊆ ⋃ k ∈ Finset.range (N + 1), ball (x k) ε := by
  classical
  -- any two points of `g` are joined by an `ε`-walk
  set R : X → X → Prop := fun a b => ∃ (N : ℕ) (x : ℕ → X), IsWalk g ε N x ∧ x 0 = a ∧ x N = b
  have hR : ∀ a ∈ g, ∀ b ∈ g, R a b := by
    intro a ha b hb
    refine hconn.isPreconnected.induction₂' R (fun x hx => ?_) (fun x y z hx hy hz => ?_) ha hb
    · filter_upwards [inter_mem_nhdsWithin g (ball_mem_nhds x hε), self_mem_nhdsWithin]
        with y hy hyg
      refine ⟨⟨1, fun k => if k = 0 then x else y, ⟨fun k hk => ?_, fun k hk => ?_⟩, rfl, rfl⟩,
        ⟨1, fun k => if k = 0 then y else x, ⟨fun k hk => ?_, fun k hk => ?_⟩, rfl, rfl⟩⟩
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl <;> simp [hx, hyg]
      · have : k = 0 := by omega
        subst this; simpa [dist_comm] using hy.2
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl <;> simp [hx, hyg]
      · have : k = 0 := by omega
        subst this; simpa using hy.2
    · rintro ⟨M, c, hc, hc0, hcM⟩ ⟨N, w, hw, hw0, hwN⟩
      refine ⟨M + N, _, hc.append hw (hcM.trans hw0.symm), by simp [hc0], ?_⟩
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp only [add_zero, le_refl, if_true]; rw [hcM, ← hw0, hwN]
      · simp only [show ¬ M + N ≤ M by omega, if_false, Nat.add_sub_cancel_left, hwN]
  -- a walk through every point of a finite list
  have hlist : ∀ l : List X, (∀ y ∈ l, y ∈ g) → ∀ a ∈ g, ∃ (N : ℕ) (x : ℕ → X),
      IsWalk g ε N x ∧ x 0 = a ∧ ∀ y ∈ l, ∃ k ≤ N, x k = y := by
    intro l
    induction l with
    | nil =>
        intro _ a ha
        exact ⟨0, fun _ => a, ⟨fun _ _ => ha, fun k hk => absurd hk (Nat.not_lt_zero _)⟩, rfl,
          by simp⟩
    | cons y l ih =>
        intro hl a ha
        obtain ⟨M, c, hc, hc0, hcM⟩ := hR a ha y (hl y (List.mem_cons_self))
        obtain ⟨N, w, hw, hw0, hwl⟩ := ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) y
          (hl y List.mem_cons_self)
        refine ⟨M + N, _, hc.append hw (hcM.trans hw0.symm), by simp [hc0], fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨M, by omega, by simp [hcM]⟩
        · obtain ⟨k, hk, rfl⟩ := hwl z hz
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · exact ⟨M, by omega, by simp [hcM, hw0]⟩
          · refine ⟨M + k, by omega, ?_⟩
            simp only [show ¬ M + k ≤ M by omega, if_false, Nat.add_sub_cancel_left]
  obtain ⟨t, htg, htf, hgt⟩ := finite_cover_balls_of_compact hc hε
  obtain ⟨a, ha⟩ := hconn.nonempty
  obtain ⟨N, x, hx, -, hxl⟩ := hlist htf.toFinset.toList
    (fun y hy => htg (by simpa using hy)) a ha
  refine ⟨N, x, hx, fun z hz => ?_⟩
  obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.mp (hgt hz)
  obtain ⟨k, hk, rfl⟩ := hxl y (by simpa using hyt)
  exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by omega), hzy⟩

end Walk

/-- **Bing's broken line** (not simple): a compact connected subset `g` of a normed space is within
`ε`, both ways, of the polygonal path `x 0 x 1 ⋯ x N` through the points of an `ε`-walk in `g`. -/
theorem exists_broken_line_near {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Set F} (hc : IsCompact g) (hconn : IsConnected g) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : ℕ → F), (∀ k ≤ N, x k ∈ g) ∧
      insert (x 0) (⋃ k ∈ Finset.range N, segment ℝ (x k) (x (k + 1))) ⊆ thickening ε g ∧
      g ⊆ thickening ε (insert (x 0) (⋃ k ∈ Finset.range N, segment ℝ (x k) (x (k + 1)))) := by
  obtain ⟨N, x, ⟨hxg, hxd⟩, hcov⟩ := exists_eps_walk hc hconn hε
  refine ⟨N, x, hxg, fun z hz => ?_, fun z hz => ?_⟩
  · rw [mem_thickening_iff]
    rcases hz with rfl | hz
    · exact ⟨x 0, hxg 0 (Nat.zero_le _), by rw [dist_self]; exact hε⟩
    · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
      rw [Finset.mem_range] at hk
      have hseg : segment ℝ (x k) (x (k + 1)) ⊆ ball (x k) ε :=
        (convex_ball (x k) ε).segment_subset (mem_ball_self hε)
          (by rw [mem_ball, dist_comm]; exact hxd k hk)
      exact ⟨x k, hxg k hk.le, hseg hzk⟩
  · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp (hcov hz)
    rw [Finset.mem_range] at hk
    rw [mem_thickening_iff]
    refine ⟨x k, ?_, by rw [mem_ball] at hzk; exact hzk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact mem_insert _ _
    · refine mem_insert_of_mem _ (mem_iUnion₂.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩)
      rw [show k - 1 + 1 = k by omega]
      exact right_mem_segment ℝ _ _

end Most

end HPC.Plane
