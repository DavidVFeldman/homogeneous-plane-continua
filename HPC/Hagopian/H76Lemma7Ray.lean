import HPC.Hagopian.H76HalfRay

/-!
# Batch 162, item A: Lemma 7 by half-ray density

Hagopian 1976, pp. 343–344: "By Lemma 2, an integer `i` and a homeomorphism `f` of `M` onto `M` exist
such that a continuum `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`."

The construction (commission 162, §1, steps 1–5):
1. Lemma 2 gives a small `f` with `f(uᵢ) = u`, `i` large.
2. `t ∉ f[Uᵢ]`, since `ρ(Tᵢ, Uᵢ) > ε`.
3. The two half-rays of the line `hᵢ[R(E)]` from the layer `Uᵢ` meet only in `Uᵢ`
   (`halfray_inter_subset`); one of them misses `f⁻¹(t)`.
4. Each half-ray is dense in `Cl R(E)` (`halfray_dense_aux`), so one extension in it reaches near `p`.
5. `lemma7_triod`, as in `lemma7_of_F`.

* `exists_F_halfray`: steps 3–4, in the coordinates of `G = hᵢ⁻¹[Hᵢ]`.
* `lemma7_aux`: Lemma 7 (the skeleton's statement).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Lemma7

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Steps 3–4.** For `G` essential to `R(E)`, an interior layer `b⁻¹(u)`, a point `w` of it, a point
`y` off it, and `P ∈ Cl R(E)`: an extension of one of the two halves of `G` from `b⁻¹(u)` contains
`w`, misses `y`, and comes within `η` of `P`. -/
theorem exists_F_halfray (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} (hGE : IsEssential k G)
    {b : G → unitInterval} (hb : IsMinimalAdmissible G b) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) {w y : M} (hw : w ∈ layer b u) (hy : y ∉ layer b u) {P : M}
    (hP : P ∈ closure (Rset k)) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set M, Fold.Q78.IsContinuum K ∧ w ∈ K ∧ y ∉ K ∧ ∃ z ∈ K, dist z P < η := by
  obtain ⟨hup, hdn⟩ := halfray_dense_aux hX hi hE hb hGE hu0 hu1
  have hwu : ∀ S : Set unitInterval, u ∈ S → w ∈ layerSet b S := fun S hS => by
    obtain ⟨w', hw', rfl⟩ := hw; exact ⟨w', by rw [mem_preimage, show b w' = u from hw']; exact hS, rfl⟩
  rw [← hup] at hP
  obtain ⟨zup, ⟨Kup, hKup, hzKup⟩, hzup⟩ := Metric.mem_closure_iff.1 hP η hη
  rw [hup, ← hdn] at hP
  obtain ⟨zdn, ⟨Kdn, hKdn, hzKdn⟩, hzdn⟩ := Metric.mem_closure_iff.1 hP η hη
  have hsep := halfray_inter_subset hX hi hb hu0 hu1 hKup hKdn
  by_cases hyup : y ∈ Kup
  · refine ⟨Kdn, IsExtensionAway.isContinuum hKdn, hKdn.1 (hwu _ ⟨unitInterval.nonneg', le_rfl⟩),
      fun hydn => hy (hsep ⟨hyup, hydn⟩), zdn, hzKdn, ?_⟩
    rw [dist_comm]; exact hzdn
  · exact ⟨Kup, IsExtensionAway.isContinuum hKup, hKup.1 (hwu _ ⟨le_rfl, unitInterval.le_one'⟩), hyup,
      zup, hzKup, by rw [dist_comm]; exact hzup⟩

/-- **Lemma 7** (p. 343), by half-ray density. -/
theorem lemma7_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
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
  have hPcl : P ∈ closure (Rset k) :=
    mem_closure_of_tendsto hP (Eventually.of_forall fun n => hp (φ n))
  have htu : ∀ n, ε < dist (t n) (u n) := fun n => hfar n _ (ht n) _ (hu n)
  have hTU : ε ≤ dist T U :=
    ge_of_tendsto (hT.dist hU) (Eventually.of_forall fun n => (htu (φ n)).le)
  have hTU' : U ≠ T := fun h' => by rw [h', dist_self] at hTU; linarith
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- the continuum `F` (steps 1–4)
  obtain ⟨F, hFc, hUF, hTF, a', ha'F, ha'P⟩ : ∃ F : Set M, Fold.Q78.IsContinuum F ∧ U ∈ F ∧
      T ∉ F ∧ ∃ a ∈ F, dist a P < ε / 4 := by
    set η := ε / 12 with hηdef
    have hη : 0 < η := by positivity
    obtain ⟨hWo, hUW⟩ := lemma2_aux hX hη U
    have hev : ∀ᶠ n in atTop, u (φ n) ∈ {y : M | ∃ g : M ≃ₜ M, g U = y ∧ ∀ v, dist v (g v) < η} ∧
        dist (t (φ n)) T < ε / 2 ∧ 1 / ((n : ℝ) + 1) < η :=
      (hU.eventually (hWo.mem_nhds hUW)).and (((Metric.tendsto_nhds.1 hT) _
        (by positivity)).and (h1n.eventually (gt_mem_nhds hη)))
    obtain ⟨n, ⟨g, hgU, hg⟩, htT, hn⟩ := hev.exists
    set i := φ n
    have hi1 : 1 / ((i : ℝ) + 1) < η := (hφle n).trans_lt hn
    -- step 1: `G = hᵢ⁻¹[Hᵢ]` with the transported map
    obtain ⟨bb, hbb, hbbS⟩ := exists_image_map (h i).symm (hd i)
    have hGeq : (h i).symm '' H i = h i ⁻¹' H i := congrFun (h i).image_symm _
    have hGE : IsEssential k ((h i).symm '' H i) := by rw [hGeq]; exact hHe i
    have hlay : ∀ s, layer bb s = (h i).symm '' layer (d i) s := fun s => hbbS {s}
    -- the parameter `uᵢ` is interior
    have hpar0 : 0 < uu i := lt_of_le_of_ne unitInterval.nonneg' fun h0 => by
      have := hfar i _ (h0 ▸ hu i) _ (hu i)
      rw [dist_self] at this; linarith
    have hpar1 : uu i < 1 := lt_of_le_of_ne unitInterval.le_one' fun h1 => by
      have := hfar i _ (ht i) _ (h1 ▸ hv i)
      have := htv i
      linarith
    -- step 2: `y = hᵢ⁻¹(g(t))` is off the layer
    have hy : (h i).symm (g T) ∉ layer bb (uu i) := by
      rw [hlay]
      rintro ⟨x, hx, hxe⟩
      have hxg : x = g T := (h i).symm.injective hxe
      have h1 := hfar i _ (ht i) _ hx
      have h2 := hg T
      have h3 := dist_triangle (t i) T x
      rw [hxg] at h1 h3
      linarith
    have hw : (h i).symm (u i) ∈ layer bb (uu i) := by rw [hlay]; exact mem_image_of_mem _ (hu i)
    -- steps 3–4
    obtain ⟨K, hKc, hwK, hyK, z, hzK, hzP⟩ :=
      exists_F_halfray hX hi hE hGE hbb hpar0 hpar1 hw hy hPcl hη
    refine ⟨g.symm '' (h i '' K), isContinuum_homeo_image _ (isContinuum_homeo_image _ hKc),
      ⟨h i ((h i).symm (u i)), mem_image_of_mem _ hwK, ?_⟩, ?_, g.symm (h i z),
      mem_image_of_mem _ (mem_image_of_mem _ hzK), ?_⟩
    · rw [Homeomorph.apply_symm_apply, ← hgU, Homeomorph.symm_apply_apply]
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxT⟩
      apply hyK
      have : h i x = g T := by rw [← hxT, Homeomorph.apply_symm_apply]
      rw [← this, Homeomorph.symm_apply_apply]
      exact hx
    · have h1 : dist (g.symm (h i z)) (h i z) < η := by
        have := hg (g.symm (h i z)); rwa [Homeomorph.apply_symm_apply] at this
      have h2 : dist (h i z) z < η := by rw [dist_comm]; exact (hh i z).trans hi1
      have h3 := dist_triangle4 (g.symm (h i z)) (h i z) z P
      linarith
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
    exact h1n.eventually (gt_mem_nhds (lt_min (by positivity) hε))
  obtain ⟨n, ⟨g, hgU, hg⟩, htT, hpP, hn⟩ := hev.exists
  set j := φ n
  have hj : 1 / ((j : ℝ) + 1) < min (ρ / 4) ε := (hφle n).trans_lt hn
  have hjρ : 1 / ((j : ℝ) + 1) < ρ / 4 := hj.trans_le (min_le_left _ _)
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
    have := hj.trans_le (min_le_right _ _)
    linarith
  exact lemma7_triod hHU hAT (hd j) (isContinuum_homeo_image g hFc) (huH j) hu0 hu1
    ⟨U, hUF, hgU⟩ (ht j) (hv j) htj hvj hFH

end Lemma7

end HPC.Hagopian
