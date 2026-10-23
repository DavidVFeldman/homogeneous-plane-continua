import HPC.Hagopian.Hagopian76E

/-!
# Batch 161, item 7: Lemma 7 — the triod, and the reduction to the existence of `F`

Hagopian 1976, pp. 343–344, proof of Lemma 7: "By Lemma 2, an integer `i` and a homeomorphism `f` of
`M` onto `M` exist such that a continuum `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and
intersects `A`. Define `ε′` to be the minimum of `ε/4` and `ρ(t, F)`. It follows from Lemma 2 that an
integer `j` and an `ε′`-homeomorphism `g` of `M` onto `M` exist such that `g(u) = uⱼ` and
`{tⱼ, vⱼ} ∩ g[F] = ∅`. Note that `g[F] ∪ Hⱼ` is a triod in `M`."

* `lemma7_triod`: the triod sentence, written out. Let `H` be type A′ (map `d`), `uⱼ ∈ H` in a
  layer `d⁻¹(c)` with `0 < c < 1`, `tⱼ ∈ d⁻¹(0)`, `vⱼ ∈ d⁻¹(1)`, and `F′` a continuum through `uⱼ`
  missing `tⱼ`, `vⱼ`, not inside `H`. The three continua `d⁻¹[[0, c]]`, `d⁻¹[[c, 1]]`, `F′` pass through
  `uⱼ` and none lies in the union of the other two (`tⱼ`, `vⱼ` and a point of `F′ − H` witness it),
  against `three_continua`. **No case analysis on `g[F] ∩ Hⱼ` is needed** (commission §1 asked for
  the case where `g[F] ∩ Hⱼ` reaches an end layer without containing `tⱼ` or `vⱼ`): the arms are
  taken from the layer of `uⱼ`, not from `g[F] ∩ Hⱼ`.
* `Lemma7F R`: the existence statement Hagopian asserts — for `p`, `u`, `t` in `Cl R` with `u ≠ t`
  and `r > 0`, a continuum of `M` contains `u`, misses `t`, and meets the `r`-ball about `p`. The
  proof uses neither that `F` is essential nor that it lies in a translate of `R(E)`.
* `lemma7_of_F`: **Lemma 7 follows from `Lemma7F (R(E))`**, by Hagopian's argument (sequences,
  compactness, Lemma 2, and `lemma7_triod`).
* `lemma7F_of_not_mem_composant`: the case of `Lemma7F` in which `t` is not in the composant of
  `u` in `Cl R(E)` (composants are dense). The case of one composant is open.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Lemma7

variable {M : Set Pt}

/-- **The triod of Lemma 7.** -/
theorem lemma7_triod (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {H : Set M} {d : H → unitInterval}
    (hH : IsMinimalAdmissible H d) {F : Set M} (hF : Fold.Q78.IsContinuum F) {u t v : M}
    (huH : u ∈ H) (hu0 : u ∉ layer d 0) (hu1 : u ∉ layer d 1) (huF : u ∈ F)
    (ht : t ∈ layer d 0) (hv : v ∈ layer d 1) (htF : t ∉ F) (hvF : v ∉ F) (hFH : ¬ F ⊆ H) :
    False := by
  set c := d ⟨u, huH⟩ with hc
  have hHc := hH.isCompact
  have hd := hH.2.1
  have hK₁ : Fold.Q78.IsContinuum (layerSet d (Icc 0 c)) :=
    isContinuum_img hHc hd isClosed_Icc isPreconnected_Icc ⟨0, le_rfl, unitInterval.nonneg'⟩
  have hK₂ : Fold.Q78.IsContinuum (layerSet d (Icc c 1)) :=
    isContinuum_img hHc hd isClosed_Icc isPreconnected_Icc ⟨1, unitInterval.le_one', le_rfl⟩
  have huK₁ : u ∈ layerSet d (Icc 0 c) := ⟨⟨u, huH⟩, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩
  have huK₂ : u ∈ layerSet d (Icc c 1) := ⟨⟨u, huH⟩, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩
  have hc0 : c ≠ 0 := fun h => hu0 ⟨⟨u, huH⟩, h, rfl⟩
  have hc1 : c ≠ 1 := fun h => hu1 ⟨⟨u, huH⟩, h, rfl⟩
  obtain ⟨t', ht', rfl⟩ := ht
  obtain ⟨v', hv', rfl⟩ := hv
  have ht0 : d t' = 0 := ht'
  have hv1 : d v' = 1 := hv'
  have htK₁ : (t' : M) ∈ layerSet d (Icc 0 c) :=
    ⟨t', show d t' ∈ Icc 0 c by rw [ht0]; exact ⟨le_rfl, unitInterval.nonneg'⟩, rfl⟩
  have hvK₂ : (v' : M) ∈ layerSet d (Icc c 1) :=
    ⟨v', show d v' ∈ Icc c 1 by rw [hv1]; exact ⟨unitInterval.le_one', le_rfl⟩, rfl⟩
  have htK₂ : (t' : M) ∉ layerSet d (Icc c 1) := by
    rintro ⟨t'', h1, h2⟩
    have := Subtype.val_injective h2
    subst this
    have : c ≤ d t'' := h1.1
    rw [ht0] at this
    exact hc0 (le_antisymm this unitInterval.nonneg')
  have hvK₁ : (v' : M) ∉ layerSet d (Icc 0 c) := by
    rintro ⟨v'', h1, h2⟩
    have := Subtype.val_injective h2
    subst this
    have : d v'' ≤ c := h1.2
    rw [hv1] at this
    exact hc1 (le_antisymm unitInterval.le_one' this)
  rcases three_continua hHU hAT hK₁ hK₂ hF huK₁ huK₂ huF with h | h | h
  · rcases h htK₁ with h' | h'
    · exact htK₂ h'
    · exact htF h'
  · rcases h hvK₂ with h' | h'
    · exact hvK₁ h'
    · exact hvF h'
  · apply hFH
    intro x hx
    rcases h hx with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩ <;> exact y.2

/-- **The existence of `F`** (p. 343), as a property of a set `R` of `M`: for `p`, `u`, `t` in `Cl R`
with `u ≠ t` and every `r > 0`, some continuum of `M` contains `u`, misses `t`, and meets the `r`-ball
about `p`. -/
def Lemma7F (R : Set M) : Prop :=
  ∀ p ∈ closure R, ∀ u ∈ closure R, ∀ t ∈ closure R, u ≠ t → ∀ r > 0,
    ∃ F : Set M, Fold.Q78.IsContinuum F ∧ u ∈ F ∧ t ∉ F ∧ ∃ a ∈ F, dist a p < r

/-- A limit of points that are `1/(n + 1)`-close to points of `S` lies in `Cl S`. -/
theorem mem_closure_of_near {S : Set M} {x : ℕ → M} {X : M} (hx : Tendsto x atTop (𝓝 X))
    {y : ℕ → M} (hy : ∀ n, y n ∈ S) (hxy : ∀ n, dist (y n) (x n) < 1 / ((n : ℝ) + 1)) :
    X ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hx) (r / 2) (by positivity)
  obtain ⟨N', hN'⟩ := exists_nat_one_div_lt (show 0 < r / 2 by positivity)
  set n := max N N'
  refine ⟨y n, hy n, ?_⟩
  have h1 := hN n (le_max_left _ _)
  have h2 := hxy n
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N' : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N' : ℝ) ≤ n := by exact_mod_cast le_max_right N N'
    linarith
  have h4 := dist_triangle X (x n) (y n)
  rw [dist_comm X (x n), dist_comm (x n) (y n)] at h4
  linarith

/-- **Lemma 7 from the existence of `F`.** -/
theorem lemma7_of_F [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hF : Lemma7F (Rset k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  by_contra hcon
  have key : ∀ n : ℕ, ∃ (h : M ≃ₜ M) (H : Set M) (d : H → unitInterval) (t v u p : M)
      (uu : unitInterval), (∀ w, dist w (h w) < 1 / ((n : ℝ) + 1)) ∧ IsEssential k (h ⁻¹' H) ∧
      IsMinimalAdmissible H d ∧ t ∈ layer d 0 ∧ v ∈ layer d 1 ∧ dist t v < 1 / ((n : ℝ) + 1) ∧
      u ∈ layer d uu ∧ (∀ t' ∈ layer d 0, ∀ w ∈ layer d uu, ε < dist t' w) ∧ p ∈ Rset k ∧
      ∀ q ∈ H, ε ≤ dist p q := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨1 / ((n : ℝ) + 1), by positivity, fun h hh H hHe d hd ⟨t, ht, v, hv, htv⟩
      ⟨uu, huu⟩ p hp => ?_⟩
    by_contra hq
    push_neg at hq
    obtain ⟨e, he⟩ := hd.2.1.2.1 uu
    exact hn ⟨h, H, d, t, v, e, p, uu, hh, hHe, hd, ht, hv, htv, ⟨e, he, rfl⟩, huu, hp, hq⟩
  choose h H d t v u p uu hh hHe hd ht hv htv hu hfar hp hpq using key
  have huH : ∀ n, u n ∈ H n := fun n => by
    obtain ⟨e, -, he⟩ := hu n
    rw [← he]; exact e.2
  have htH : ∀ n, t n ∈ H n := fun n => by
    obtain ⟨e, -, he⟩ := ht n
    rw [← he]; exact e.2
  -- convergent subsequences
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_univ : IsCompact (univ : Set (M × M × M))).tendsto_subseq
    (x := fun n => (t n, u n, p n)) (fun n => mem_univ _)
  set T := a.1
  set U := a.2.1
  set P := a.2.2
  have hT : Tendsto (fun n => t (φ n)) atTop (𝓝 T) := (continuous_fst.tendsto a).comp hlim
  have hU : Tendsto (fun n => u (φ n)) atTop (𝓝 U) :=
    ((continuous_fst.comp continuous_snd).tendsto a).comp hlim
  have hP : Tendsto (fun n => p (φ n)) atTop (𝓝 P) :=
    ((continuous_snd.comp continuous_snd).tendsto a).comp hlim
  have hφle : ∀ n, 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    apply one_div_le_one_div_of_le (by positivity)
    have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith
  -- the limits lie in `Cl R(E)`
  have hnear : ∀ (z : ℕ → M), (∀ n, z n ∈ H n) → ∀ n,
      (h (φ n)).symm (z (φ n)) ∈ Rset k ∧
        dist ((h (φ n)).symm (z (φ n))) (z (φ n)) < 1 / ((n : ℝ) + 1) := by
    intro z hz n
    refine ⟨(hHe (φ n)).1 (show h (φ n) ((h (φ n)).symm (z (φ n))) ∈ H (φ n) by simpa using hz _),
      ?_⟩
    have := hh (φ n) ((h (φ n)).symm (z (φ n)))
    simp only [Homeomorph.apply_symm_apply] at this
    exact this.trans_le (hφle n)
  have hTcl : T ∈ closure (Rset k) :=
    mem_closure_of_near hT (fun n => (hnear t htH n).1) (fun n => (hnear t htH n).2)
  have hUcl : U ∈ closure (Rset k) :=
    mem_closure_of_near hU (fun n => (hnear u huH n).1) (fun n => (hnear u huH n).2)
  have hPcl : P ∈ closure (Rset k) :=
    mem_closure_of_tendsto hP (Eventually.of_forall fun n => hp (φ n))
  -- `ρ(t, u) ≥ ε`
  have htu : ∀ n, ε < dist (t n) (u n) := fun n => hfar n _ (ht n) _ (hu n)
  have hTU : ε ≤ dist T U :=
    ge_of_tendsto (hT.dist hU) (Eventually.of_forall fun n => (htu (φ n)).le)
  have hTU' : U ≠ T := fun h' => by rw [h', dist_self] at hTU; linarith
  -- the continuum `F`
  obtain ⟨F, hFc, hUF, hTF, a', ha'F, ha'P⟩ :=
    hF P hPcl U hUcl T hTcl hTU' (ε / 4) (by positivity)
  have hFne : F.Nonempty := ⟨U, hUF⟩
  have hρ : 0 < infDist T F := (hFc.1.isClosed.notMem_iff_infDist_pos hFne).1 hTF
  set ρ := infDist T F
  set ε' := min (ε / 4) (ρ / 2)
  have hε' : 0 < ε' := lt_min (by positivity) (by positivity)
  obtain ⟨hWo, hUW⟩ := lemma2_aux hX hε' U
  -- choose `j`
  have hev : ∀ᶠ n in atTop, u (φ n) ∈ {y : M | ∃ g : M ≃ₜ M, g U = y ∧ ∀ v, dist v (g v) < ε'} ∧
      dist (t (φ n)) T < ρ / 4 ∧ dist (p (φ n)) P < ε / 4 ∧
      1 / ((n : ℝ) + 1) < min (ρ / 4) ε := by
    refine ((hU.eventually (hWo.mem_nhds hUW)).and ((Metric.tendsto_nhds.1 hT) _
      (by positivity))).and (((Metric.tendsto_nhds.1 hP) _ (by positivity)).and ?_) |>.mono
      fun n hn => ⟨hn.1.1, hn.1.2, hn.2.1, hn.2.2⟩
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact this.eventually (gt_mem_nhds (lt_min (by positivity) hε))
  obtain ⟨n, ⟨g, hgU, hg⟩, htT, hpP, hn⟩ := hev.exists
  set j := φ n
  have hj : 1 / ((j : ℝ) + 1) < min (ρ / 4) ε := (hφle n).trans_lt hn
  have hjρ : 1 / ((j : ℝ) + 1) < ρ / 4 := hj.trans_le (min_le_left _ _)
  have hjε : 1 / ((j : ℝ) + 1) < ε := hj.trans_le (min_le_right _ _)
  have hρF : ∀ x ∈ F, ρ ≤ dist T x := fun x hx => infDist_le_dist_of_mem hx
  have hgε' : ∀ x, dist x (g x) < ρ / 2 := fun x => (hg x).trans_le (min_le_right _ _)
  -- `g[F]` misses `tⱼ` and `vⱼ`
  have hfar' : ∀ z : M, dist z T < ρ / 2 → z ∉ g '' F := by
    rintro z hz ⟨x, hx, rfl⟩
    have h1 := hρF x hx
    have h2 := hgε' x
    have h3 := dist_triangle T (g x) x
    rw [dist_comm T (g x), dist_comm (g x) x] at h3
    linarith
  have htj : t j ∉ g '' F := hfar' _ (by linarith)
  have hvj : v j ∉ g '' F := by
    apply hfar'
    have := dist_triangle (v j) (t j) T
    have := htv j
    rw [dist_comm (t j) (v j)] at this
    linarith
  -- `g[F]` is not inside `Hⱼ`
  have hFH : ¬ g '' F ⊆ H j := by
    intro hsub
    have := hpq j (g a') (hsub ⟨a', ha'F, rfl⟩)
    have h1 := dist_triangle4 (p j) P a' (g a')
    have h2 := (hg a').trans_le (min_le_left _ _)
    have h3 := dist_comm a' P
    linarith
  -- `uⱼ` is in no end layer
  have hu0 : u j ∉ layer (d j) 0 := fun h0 => by
    have := hfar j _ h0 _ (hu j)
    rw [dist_self] at this
    linarith
  have hu1 : u j ∉ layer (d j) 1 := by
    intro h1
    obtain ⟨e₁, he₁, hee₁⟩ := h1
    obtain ⟨e₂, he₂, hee₂⟩ := hu j
    have : e₁ = e₂ := Subtype.val_injective (hee₁.trans hee₂.symm)
    subst this
    have hu1' : uu j = 1 := (mem_singleton_iff.1 he₂).symm.trans (mem_singleton_iff.1 he₁)
    have := hfar j _ (ht j) _ (hu1' ▸ hv j)
    have := htv j
    linarith
  exact lemma7_triod hHU hAT (hd j) (isContinuum_homeo_image g hFc) (huH j) hu0 hu1
    ⟨U, hUF, hgU⟩ (ht j) (hv j) htj hvj hFH

/-- **`F` across composants.** In a continuum `K`, if `t ≠ u` and `t` is not in the composant of
`u`, then for every `p ∈ K` and `r > 0` a proper subcontinuum of `K` contains `u`, misses `t`, and
meets the `r`-ball about `p` (boundary bumping in `K − B(p, r/2)`). -/
theorem exists_F_of_not_mem_composant [CompactSpace M] {K : Set M} (hK : Fold.Q78.IsContinuum K) {u t p : M}
    (huK : u ∈ K) (hpK : p ∈ K) (hut : u ≠ t) (ht : t ∉ HPC.composant K u) {r : ℝ}
    (hr : 0 < r) :
    ∃ F : Set M, Fold.Q78.IsContinuum F ∧ u ∈ F ∧ t ∉ F ∧ ∃ a ∈ F, dist a p < r := by
  by_cases hup : dist u p < r
  · exact ⟨{u}, isContinuum_singleton' u, rfl, fun h => hut (mem_singleton_iff.1 h).symm, u, rfl,
      hup⟩
  push_neg at hup
  set F₀ := K \ ball p (r / 2)
  have hF₀ : IsClosed F₀ := hK.1.isClosed.sdiff isOpen_ball
  have hpF₀ : p ∉ F₀ := fun h => h.2 (mem_ball_self (by positivity))
  have huF₀ : u ∈ F₀ := ⟨huK, fun h => by rw [mem_ball] at h; linarith⟩
  obtain ⟨L, hL, hLF₀, huL, a, haL, hacl⟩ :=
    exists_continuum_bump_closed hK hF₀ diff_subset (fun h => hpF₀ (h ▸ hpK)) huF₀
  have hcl : closure (K \ F₀) ⊆ closedBall p (r / 2) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra hx'
    exact hx.2 ⟨hx.1, fun h => hx' (ball_subset_closedBall h)⟩
  refine ⟨L, hL, huL, fun htL => ht ⟨L, ⟨hL, hLF₀.trans diff_subset, fun h => ?_, huL⟩, htL⟩, a,
    haL, ?_⟩
  · exact hpF₀ (hLF₀ (h ▸ hpK))
  · have := hcl hacl
    rw [mem_closedBall] at this
    linarith

/-- **Lemma 7, reduced to one composant**: Lemma 7 holds as soon as the continuum `F` exists for
`u`, `t` in the same composant of `Cl R(E)` (the other case is `exists_F_of_not_mem_composant`). -/
theorem lemma7_of_F_composant [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k)
    (hF : ∀ p ∈ closure (Rset k), ∀ u ∈ closure (Rset k), ∀ t ∈ closure (Rset k), u ≠ t →
      t ∈ HPC.composant (closure (Rset k)) u → ∀ r > 0,
        ∃ F : Set M, Fold.Q78.IsContinuum F ∧ u ∈ F ∧ t ∉ F ∧ ∃ a ∈ F, dist a p < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  refine lemma7_of_F hX hi (fun p hp u hu t ht hut r hr => ?_) hε
  by_cases htc : t ∈ HPC.composant (closure (Rset k)) u
  · exact hF p hp u hu t ht hut htc r hr
  · exact exists_F_of_not_mem_composant (lemma6_aux hX hi hE).1 hu hp hut htc hr

end Lemma7

end HPC.Hagopian
