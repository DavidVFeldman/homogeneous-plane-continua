import HPC.Hagopian.H84Chain13

/-!
# Batch 187, §2: Lemma 13, conditions (3)–(5) of "runs straight"

Commission 187 §2.1–§2.3. Throughout, `x` is strictly increasing with `x 0 = 0`, `x 15 = 1`, and
`δ` satisfies the fifteen gap bounds `2δ < ρ(k⁻¹[[0, xⱼ]], k⁻¹[[xⱼ₊₁, 1]])` (`exists_gap84`; the
paper uses thirteen of them, `1 ≤ j ≤ 13`).

* `link_dichotomy84`: Hagopian's (3), for every `δ`-homeomorphism `h` (commission 187 §2.1: the
  positions of `r` and `s` come from the gap bounds, no uniform continuity).
* `layer_frontier84`: Hagopian's (4) (commission 187 §2.2: Effros with the room
  `δ − max dist(v, h v)`).
* `no_fold84`, `layer_convex84`: Hagopian's (5) (the fold of `exists_fold`, kinds D and U,
  commission 187 §2.3).
* `translate_runsStraight84`: every `δ`-translate of `E` runs straight through the links.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Gap

variable {M : Set Pt}

theorem xle84 {x : Fin 16 → unitInterval} (hx : StrictMono x) {m n : ℕ} (hm : m < 16) (hn : n < 16)
    (h : m ≤ n) : x ⟨m, hm⟩ ≤ x ⟨n, hn⟩ :=
  hx.monotone (Fin.mk_le_mk.2 h)

theorem xlt84 {x : Fin 16 → unitInterval} (hx : StrictMono x) {m n : ℕ} (hm : m < 16) (hn : n < 16)
    (h : m < n) : x ⟨m, hm⟩ < x ⟨n, hn⟩ :=
  hx (Fin.mk_lt_mk.2 h)

/-- **The gap bounds** (p. 339: "the minimum of `{½ρ(k⁻¹[[0, xᵢ]], k⁻¹[[xᵢ₊₁, 1]]): 1 ≤ i ≤ 13}`"),
here for all `0 ≤ j ≤ 14`. -/
theorem exists_gap84 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {x : Fin 16 → unitInterval} (hx : StrictMono x) :
    ∃ ρ > 0, ∀ (j : ℕ) (hj : j + 1 < 16) (a b : E), k a ≤ x ⟨j, by omega⟩ →
      x ⟨j + 1, hj⟩ ≤ k b → ρ < dist a.1 b.1 := by
  have hk := hE.2.1
  have hEc := hE.isCompact
  have hj : ∀ j : Fin 15, ∃ r > 0, ∀ a b : E, k a ≤ x ⟨j, by omega⟩ →
      x ⟨j + 1, by omega⟩ ≤ k b → r < dist a.1 b.1 := by
    intro j
    have hlt := xlt84 hx (m := j) (n := j + 1) (by omega) (by omega) (by omega)
    have hd : Disjoint (Subtype.val '' (k ⁻¹' Icc 0 (x ⟨j, by omega⟩)))
        (Subtype.val '' (k ⁻¹' Icc (x ⟨j + 1, by omega⟩) 1)) := by
      rw [disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      subst this
      exact absurd (hw'.1.trans hw.2) (not_le.2 hlt)
    obtain ⟨r, hr, hdr⟩ := exists_sep_radius (isCompact_img hEc hk.1 isClosed_Icc)
      (isCompact_img hEc hk.1 isClosed_Icc) hd
    refine ⟨r, hr, fun a b ha hb => ?_⟩
    by_contra hc
    rw [not_lt] at hc
    have h1 : b.1 ∈ cthickening r (Subtype.val '' (k ⁻¹' Icc 0 (x ⟨j, by omega⟩))) :=
      mem_cthickening_of_dist_le _ a.1 r _ ⟨a, ⟨unitInterval.nonneg', ha⟩, rfl⟩
        (by rw [dist_comm]; exact hc)
    have h2 : b.1 ∈ cthickening r (Subtype.val '' (k ⁻¹' Icc (x ⟨j + 1, by omega⟩) 1)) :=
      self_subset_cthickening _ ⟨b, ⟨hb, unitInterval.le_one'⟩, rfl⟩
    exact disjoint_left.1 hdr h1 h2
  choose r hr hrd using hj
  set ρ : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  refine ⟨ρ, (Finset.lt_inf'_iff _).2 fun j _ => hr j, fun j hj a b ha hb => ?_⟩
  exact (Finset.inf'_le _ (Finset.mem_univ (⟨j, by omega⟩ : Fin 15))).trans_lt
    (hrd ⟨j, by omega⟩ a b ha hb)

/-- Two points identified by `δ`-homeomorphisms are less than `2δ` apart. -/
theorem close84 {h g : M ≃ₜ M} {δ : ℝ} (hh : ∀ v, dist v (h v) < δ) (hg : ∀ v, dist v (g v) < δ)
    {z w : M} (hzw : h z = g w) : dist z w < 2 * δ := by
  have := dist_triangle z (h z) w
  have e : dist (h z) w = dist w (g w) := by rw [hzw, dist_comm]
  linarith [hh z, hg w]

/-- The order part of commission 187 §2.1: if `s ∈ [x₃ᵢ, x₃ᵢ₊₃]`, `r ∉ [x₃ᵢ, x₃ᵢ₊₃]` and no gap
`[xⱼ, xⱼ₊₁]` separates `r` from `s`, then `r, s ∈ [x₁, x₁₄]`. -/
theorem params_inner84 {x : Fin 16 → unitInterval} (hx : StrictMono x) (hx0 : x 0 = 0)
    (hx15 : x 15 = 1) {r s : unitInterval} (i : Fin 5)
    (hnear : ∀ (j : ℕ) (hj : j + 1 < 16), ¬ (r ≤ x ⟨j, by omega⟩ ∧ x ⟨j + 1, hj⟩ ≤ s) ∧
      ¬ (s ≤ x ⟨j, by omega⟩ ∧ x ⟨j + 1, hj⟩ ≤ r))
    (hs : s ∈ Icc (x ⟨3 * i.val, by omega⟩) (x ⟨3 * i.val + 3, by omega⟩))
    (hr : r ∉ Icc (x ⟨3 * i.val, by omega⟩) (x ⟨3 * i.val + 3, by omega⟩)) :
    x ⟨1, by omega⟩ ≤ r ∧ r ≤ x ⟨14, by omega⟩ ∧ x ⟨1, by omega⟩ ≤ s ∧ s ≤ x ⟨14, by omega⟩ := by
  have hi := i.isLt
  rw [mem_Icc, not_and_or, not_le, not_le] at hr
  rcases hr with hr | hr
  · have hI : 1 ≤ i.val := by
      by_contra h0
      have h0' : i.val = 0 := by omega
      have : x ⟨3 * i.val, by omega⟩ = 0 := by
        rw [← hx0]; congr 1; ext; simp [h0']
      rw [this] at hr
      exact absurd hr (not_lt.2 unitInterval.nonneg')
    have hs3 : x ⟨3, by omega⟩ ≤ s := (xle84 hx _ _ (by omega)).trans hs.1
    have hr12 : r ≤ x ⟨12, by omega⟩ := hr.le.trans (xle84 hx _ _ (by omega))
    refine ⟨?_, hr12.trans (xle84 hx _ _ (by omega)), (xle84 hx _ _ (by omega)).trans hs3, ?_⟩
    · by_contra h
      exact (hnear 1 (by omega)).1 ⟨(not_le.1 h).le, (xle84 hx _ _ (by omega)).trans hs3⟩
    · by_contra h
      exact (hnear 12 (by omega)).1 ⟨hr12, (xle84 hx _ _ (by omega)).trans (not_le.1 h).le⟩
  · have hI : i.val ≤ 3 := by
      by_contra h0
      have h0' : i.val = 4 := by omega
      have : x ⟨3 * i.val + 3, by omega⟩ = 1 := by
        rw [← hx15]; congr 1; ext; simp [h0']
      rw [this] at hr
      exact absurd hr (not_lt.2 unitInterval.le_one')
    have hr3 : x ⟨3, by omega⟩ ≤ r := (xle84 hx _ _ (by omega)).trans hr.le
    have hs12 : s ≤ x ⟨12, by omega⟩ := hs.2.trans (xle84 hx _ _ (by omega))
    refine ⟨(xle84 hx _ _ (by omega)).trans hr3, ?_, ?_, hs12.trans (xle84 hx _ _ (by omega))⟩
    · by_contra h
      exact (hnear 13 (by omega)).2 ⟨hs12.trans (xle84 hx _ _ (by omega)), (not_le.1 h).le⟩
    · by_contra h
      exact (hnear 2 (by omega)).2 ⟨(not_le.1 h).le.trans (xle84 hx _ _ (by omega)),
        (xle84 hx _ _ (by omega)).trans hr3⟩

end Gap

section Dichotomy

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The gap bounds for `δ`: `2δ < ρ(k⁻¹[[0, xⱼ]], k⁻¹[[xⱼ₊₁, 1]])` for `0 ≤ j ≤ 14`. -/
def GapBound84 {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (δ : ℝ) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < 16) (a b : E), k a ≤ x ⟨j, by omega⟩ → x ⟨j + 1, hj⟩ ≤ k b →
    2 * δ < dist a.1 b.1

omit [CompactSpace M] [ConnectedSpace M] in
theorem gapBound84_near {E : Set M} {k : E → unitInterval} {x : Fin 16 → unitInterval} {δ : ℝ}
    (hgap : GapBound84 k x δ) {a b : E} (hab : dist a.1 b.1 < 2 * δ) (j : ℕ) (hj : j + 1 < 16) :
    ¬ (k a ≤ x ⟨j, by omega⟩ ∧ x ⟨j + 1, hj⟩ ≤ k b) ∧
      ¬ (k b ≤ x ⟨j, by omega⟩ ∧ x ⟨j + 1, hj⟩ ≤ k a) :=
  ⟨fun h => absurd hab (not_lt.2 (hgap j hj a b h.1 h.2).le),
    fun h => absurd hab (not_lt.2 (by rw [dist_comm]; exact (hgap j hj b a h.1 h.2).le))⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- A `δ`-translate of a layer over `[x₃ᵢ, x₃ᵢ₊₃]` lies in `L i`. -/
theorem image_layer_subset_link84 {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval)
    {δ : ℝ} (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ) {r : unitInterval} (i : Fin 5)
    (hr : r ∈ Icc (x ⟨3 * i.val, by omega⟩) (x ⟨3 * i.val + 3, by omega⟩)) :
    h '' layer k r ⊆ chainLinks84 k x δ i := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hw' : k w = r := hw
  rw [chainLinks84_eq]
  exact image_subset_wsetOf _ h hh ⟨w.1, ⟨w, by rw [mem_preimage, hw']; exact hr, rfl⟩, rfl⟩

/-- **Hagopian's (3)** (p. 340: "if `h[k⁻¹(r)] ∩ Lᵢ ≠ ∅`, then `h[k⁻¹(r)] ⊆ Lᵢ`"), for every
`δ`-homeomorphism `h`. *Proof* (commission 187 §2.1): a point `h(z) = g(w)` with `k z = r` and
`w ∈ k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]]` gives `dist(z, w) < 2δ`; the gap bounds put `r` and `s = k w` in
`[x₁, x₁₄]` (`params_inner84`) and give the end-set hypotheses of Lemma 3 for `h⁻¹ ∘ g`; Lemma 3
gives `g[k⁻¹(s)] = h[k⁻¹(r)]`, which lies in `L i`. -/
theorem link_dichotomy84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (hgap : GapBound84 k x δ)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ) (r : unitInterval) (i : Fin 5) :
    h '' layer k r ⊆ chainLinks84 k x δ i ∨ Disjoint (h '' layer k r) (chainLinks84 k x δ i) := by
  by_cases hr : r ∈ Icc (x ⟨3 * i.val, by omega⟩) (x ⟨3 * i.val + 3, by omega⟩)
  · exact Or.inl (image_layer_subset_link84 k x h hh i hr)
  rw [or_iff_not_imp_right]
  intro hnd
  rw [not_disjoint_iff] at hnd
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, hzL⟩ := hnd
  have hz' : k z = r := hz
  rw [chainLinks84_eq] at hzL
  simp only [WsetOf, mem_iUnion] at hzL
  obtain ⟨_, ⟨w, hw, rfl⟩, g, hg, hgw⟩ := hzL
  have hzw : dist z.1 w.1 < 2 * δ := close84 hh hg hgw.symm
  set s := k w with hsdef
  have hnear := gapBound84_near hgap hzw
  rw [hz'] at hnear
  obtain ⟨hr1, hr14, hs1, hs14⟩ := params_inner84 hx hx0 hx15 i hnear hw hr
  have hs0 : 0 < s := by
    have := (xlt84 hx (m := 0) (n := 1) (by omega) (by omega) (by omega)).trans_le hs1
    rwa [show x ⟨0, by omega⟩ = 0 from hx0] at this
  have hs1' : s < 1 := by
    have := hs14.trans_lt (xlt84 hx (m := 14) (n := 15) (by omega) (by omega) (by omega))
    rwa [show x ⟨15, by omega⟩ = 1 from hx15] at this
  set φ : M ≃ₜ M := g.trans h.symm with hφ
  have hφv : ∀ v, h (φ v) = g v := fun v => by simp [hφ]
  have hlt1 : (0 : unitInterval) < x ⟨1, by omega⟩ := by
    have := xlt84 hx (m := 0) (n := 1) (by omega) (by omega) (by omega)
    rwa [show x ⟨0, by omega⟩ = 0 from hx0] at this
  have hlt14 : x ⟨14, by omega⟩ < 1 := by
    have := xlt84 hx (m := 14) (n := 15) (by omega) (by omega) (by omega)
    rwa [show x ⟨15, by omega⟩ = 1 from hx15] at this
  -- the end-set hypotheses: no point of an end layer is within `2δ` of a point over `[x₁, x₁₄]`
  have hend : ∀ a b : E, dist a.1 b.1 < 2 * δ → (k a = 0 ∨ k a = 1) → x ⟨1, by omega⟩ ≤ k b →
      k b ≤ x ⟨14, by omega⟩ → False := by
    intro a b hab h01 hb1 hb14
    have hn := gapBound84_near hgap hab
    rcases h01 with h0 | h0
    · exact (hn 0 (by omega)).1 ⟨by rw [h0, show x ⟨0, by omega⟩ = 0 from hx0], hb1⟩
    · exact (hn 14 (by omega)).2 ⟨hb14, by rw [h0, show x ⟨15, by omega⟩ = 1 from hx15]⟩
  have hφw : φ w.1 = z.1 := h.injective (by rw [hφv, hgw])
  have h1 : (layer k r ∩ φ '' layer k s).Nonempty :=
    ⟨z.1, ⟨z, hz, rfl⟩, ⟨w.1, ⟨w, rfl, rfl⟩, hφw⟩⟩
  have h2 : Disjoint (layer k r) (φ '' (layer k 0 ∪ layer k 1)) := by
    rw [disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ ⟨y, hy, hyv⟩
    have hv' : k v = r := hv
    have hyE : y ∈ E := by rcases hy with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ <;> exact a.2
    have hya : h v.1 = g y := by rw [← hyv, hφv]
    have hd : dist y v.1 < 2 * δ := by rw [dist_comm]; exact close84 hh hg hya
    rcases hy with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact hend a v hd (Or.inl ha) (hv' ▸ hr1) (hv' ▸ hr14)
    · exact hend a v hd (Or.inr ha) (hv' ▸ hr1) (hv' ▸ hr14)
  have h3 : Disjoint (φ '' layer k s) (layer k 0 ∪ layer k 1) := by
    rw [disjoint_left]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ hmem
    have ha' : k a = s := ha
    have key : ∀ v : E, φ a.1 = v.1 → (k v = 0 ∨ k v = 1) → False := by
      intro v hva h01
      have hva' : h v.1 = g a.1 := by rw [← hva, hφv]
      exact hend v a (close84 hh hg hva') h01 (ha' ▸ hs1) (ha' ▸ hs14)
    rcases hmem with ⟨v, hv, hva⟩ | ⟨v, hv, hva⟩
    · exact key v hva.symm (Or.inl hv)
    · exact key v hva.symm (Or.inr hv)
  have hL3 := hagopian76_lemma3 hX hi hE hE hs0 hs1' φ h1 h2 h3
  rw [← hL3, image_image]
  have : (fun v => h (φ v)) = g := funext hφv
  rw [this]
  exact image_layer_subset_link84 k x g hg i hw

/-- **Hagopian's (4)** (p. 340: "if `h[k⁻¹(r)] ∩ Bd Lᵢ ≠ ∅`, then `h[k⁻¹(r)] ⊆ Bd Lᵢ`").
*Proof* (commission 187 §2.2): if `p ∈ h[k⁻¹(r)] ∩ Bd Lᵢ` and `q ∈ h[k⁻¹(r)] ∖ Cl Lᵢ`, Effros
(`effros_homogeneous`) with `η` the smaller of `ρ(q, Lᵢ)` and the room `δ − max dist(v, h v)` gives
`f` moving points less than `η` with `f(p) ∈ Lᵢ`; `f ∘ h` is a `δ`-homeomorphism, so (3) puts
`f(q)` in `Lᵢ`, too close to `q`. -/
theorem layer_frontier84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (hgap : GapBound84 k x δ)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ) (r : unitInterval) (i : Fin 5)
    (hp : (h '' layer k r ∩ frontier (chainLinks84 k x δ i)).Nonempty) :
    h '' layer k r ⊆ frontier (chainLinks84 k x δ i) := by
  have hLo : IsOpen (chainLinks84 k x δ i) := by rw [chainLinks84_eq]; exact isOpen_wsetOf hX _ δ
  rw [hLo.frontier_eq] at hp ⊢
  obtain ⟨p, hpl, hpc, hpL⟩ := hp
  have hdis : Disjoint (h '' layer k r) (chainLinks84 k x δ i) :=
    (link_dichotomy84 hX hi hE hx hx0 hx15 hgap h hh r i).resolve_left (fun hs => hpL (hs hpl))
  intro q hq
  refine ⟨?_, disjoint_left.1 hdis hq⟩
  by_contra hqc
  have hne : (chainLinks84 k x δ i).Nonempty := closure_nonempty_iff.1 ⟨p, hpc⟩
  have hμ : 0 < infDist q (chainLinks84 k x δ i) := (infDist_pos_iff_notMem_closure hne).1 hqc
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (f := fun v => dist v (h v)) (continuous_id.dist h.continuous).continuousOn
  have hη' : 0 < δ - dist v₀ (h v₀) := sub_pos.2 (hh v₀)
  obtain ⟨δ', hδ', hf⟩ := HPC.Effros.effros_homogeneous hX (lt_min hμ hη')
  obtain ⟨p', hp'L, hpp'⟩ := Metric.mem_closure_iff.1 hpc δ' hδ'
  obtain ⟨f, hfp, hfm⟩ := hf p p' hpp'
  have hF : ∀ v, dist v ((h.trans f) v) < δ := by
    intro v
    have h1 : dist v (h v) ≤ dist v₀ (h v₀) := hv₀ (mem_univ v)
    have h2 : dist (h v) (f (h v)) < min (infDist q (chainLinks84 k x δ i))
        (δ - dist v₀ (h v₀)) := by rw [dist_comm]; exact hfm (h v)
    have h3 := dist_triangle v (h v) (f (h v))
    have h4 := min_le_right (infDist q (chainLinks84 k x δ i)) (δ - dist v₀ (h v₀))
    simp only [Homeomorph.trans_apply]
    linarith
  have hsub : (h.trans f) '' layer k r ⊆ chainLinks84 k x δ i := by
    refine (link_dichotomy84 hX hi hE hx hx0 hx15 hgap (h.trans f) hF r i).resolve_right ?_
    rw [not_disjoint_iff]
    obtain ⟨p₀, hp₀, rfl⟩ := hpl
    exact ⟨p', ⟨p₀, hp₀, by simp [hfp]⟩, hp'L⟩
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  have hfq : f (h q₀) ∈ chainLinks84 k x δ i := hsub ⟨q₀, hq₀, by simp⟩
  have h5 := infDist_le_dist_of_mem (x := h q₀) hfq
  have h6 := hfm (h q₀)
  rw [dist_comm] at h5
  have h7 := min_le_left (infDist (h q₀) (chainLinks84 k x δ i)) (δ - dist v₀ (h v₀))
  linarith

omit [CompactSpace M] [ConnectedSpace M] in
theorem mem_seg84_iff {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (j : Fin 5)
    (w : E) : w.1 ∈ seg84 k x j ↔
      k w ∈ Icc (x ⟨3 * j.val, by omega⟩) (x ⟨3 * j.val + 3, by omega⟩) := by
  constructor
  · rintro ⟨w', hw', hww'⟩
    have : w' = w := Subtype.ext hww'
    subst this
    exact hw'
  · intro hw
    exact ⟨w, hw, rfl⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- A `δ`-translate of a point over `[0, x₃ₚ₊₃]` lies in some `L j` with `j ≤ p`. -/
theorem mem_link_le84 {E : Set M} {k : E → unitInterval} {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (g : M ≃ₜ M)
    (hg : ∀ v, dist v (g v) < δ) (w : E) (p : Fin 5) (hw : k w ≤ x ⟨3 * p.val + 3, by omega⟩) :
    ∃ j : Fin 5, j ≤ p ∧ g w.1 ∈ chainLinks84 k x δ j := by
  obtain ⟨j, hj⟩ := mem_some_seg84 k hx0 hx15 w
  by_cases hjp : j ≤ p
  · exact ⟨j, hjp, by rw [chainLinks84_eq]; exact image_subset_wsetOf _ g hg ⟨w.1, hj, rfl⟩⟩
  · rw [not_le] at hjp
    have hj' := (mem_seg84_iff k x j w).1 hj
    have hle : x ⟨3 * p.val + 3, by omega⟩ ≤ x ⟨3 * j.val, by omega⟩ :=
      xle84 hx _ _ (by have := Fin.lt_def.1 hjp; omega)
    have heq : k w = x ⟨3 * p.val + 3, by omega⟩ := le_antisymm hw (hle.trans hj'.1)
    refine ⟨p, le_rfl, ?_⟩
    rw [chainLinks84_eq]
    refine image_subset_wsetOf _ g hg ⟨w.1, (mem_seg84_iff k x p w).2 ⟨?_, heq.le⟩, rfl⟩
    rw [heq]; exact xle84 hx _ _ (by omega)

omit [CompactSpace M] [ConnectedSpace M] in
/-- A `δ`-translate of a point over `[x₃ₚ, 1]` lies in some `L j` with `p ≤ j`. -/
theorem mem_link_ge84 {E : Set M} {k : E → unitInterval} {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (g : M ≃ₜ M)
    (hg : ∀ v, dist v (g v) < δ) (w : E) (p : Fin 5) (hw : x ⟨3 * p.val, by omega⟩ ≤ k w) :
    ∃ j : Fin 5, p ≤ j ∧ g w.1 ∈ chainLinks84 k x δ j := by
  obtain ⟨j, hj⟩ := mem_some_seg84 k hx0 hx15 w
  by_cases hjp : p ≤ j
  · exact ⟨j, hjp, by rw [chainLinks84_eq]; exact image_subset_wsetOf _ g hg ⟨w.1, hj, rfl⟩⟩
  · rw [not_le] at hjp
    have hj' := (mem_seg84_iff k x j w).1 hj
    have hle : x ⟨3 * j.val + 3, by omega⟩ ≤ x ⟨3 * p.val, by omega⟩ :=
      xle84 hx _ _ (by have := Fin.lt_def.1 hjp; omega)
    have heq : k w = x ⟨3 * p.val, by omega⟩ := le_antisymm (hj'.2.trans hle) hw
    refine ⟨p, le_rfl, ?_⟩
    rw [chainLinks84_eq]
    refine image_subset_wsetOf _ g hg ⟨w.1, (mem_seg84_iff k x p w).2 ⟨heq.ge, ?_⟩, rfl⟩
    rw [heq]; exact xle84 hx _ _ (by omega)

/-- **The fold is impossible** (p. 340, the proof of (5); commission 187 §2.3, kinds D and U).
Suppose `r < s < t`, `h[k⁻¹(s)] ⊆ L p`, and `h[k⁻¹(r)]`, `h[k⁻¹(t)]` lie in a neighbour `L q`
but not in `L p`. Take `g` with `g(w) = h(z)`, `k z = s`, `w` over `[x₃ₚ, x₃ₚ₊₃]`. In kind D
(`q = p + 1`) the continuum `C = g[k⁻¹[[0, x₃ₚ₊₃]]]` lies in `L 0 ∪ ⋯ ∪ L p`, so it misses the end
layers of `F = h[k⁻¹[[r, t]]]` (restricted map, Lemma 6) and meets `F`; by atriodicity
(`subset_of_meets_avoids`) `C ⊆ F`. Then a point of `g[k⁻¹(0)]` is `h(z')` with `r ≤ k z'`, and the
gap bound `j = 0` gives `k z' < x₁`; so `h[k⁻¹(r)] ⊆ L 0`, which forces `p = 0`, against
`h[k⁻¹(r)] ⊄ L p`. Kind U (`p = q + 1`) is the mirror image with `g[k⁻¹[[x₃ₚ, 1]]]`. -/
theorem no_fold84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (hgap : GapBound84 k x δ)
    (hL : IsChain5 (chainLinks84 k x δ)) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ)
    {r s t : unitInterval} (hrs : r < s) (hst : s < t) {p q : Fin 5}
    (hpq : (p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p) (hs : h '' layer k s ⊆ chainLinks84 k x δ p)
    (hr : h '' layer k r ⊆ chainLinks84 k x δ q) (hrp : ¬ h '' layer k r ⊆ chainLinks84 k x δ p)
    (ht : h '' layer k t ⊆ chainLinks84 k x δ q) (htp : ¬ h '' layer k t ⊆ chainLinks84 k x δ p) :
    False := by
  have hk := hE.2.1
  have hrd := (link_dichotomy84 hX hi hE hx hx0 hx15 hgap h hh r p).resolve_left hrp
  have htd := (link_dichotomy84 hX hi hE hx hx0 hx15 hgap h hh t p).resolve_left htp
  obtain ⟨z, hz⟩ := hk.2.1 s
  have hzL : h z.1 ∈ chainLinks84 k x δ p := hs ⟨z.1, ⟨z, hz, rfl⟩, rfl⟩
  rw [chainLinks84_eq] at hzL
  simp only [WsetOf, mem_iUnion] at hzL
  obtain ⟨_, ⟨w, hw, rfl⟩, g, hg, hgw⟩ := hzL
  have hw' : k w ∈ Icc (x ⟨3 * p.val, by omega⟩) (x ⟨3 * p.val + 3, by omega⟩) := hw
  -- the continuum `F = h[k⁻¹[[r, t]]]`
  have hrt : r < t := hrs.trans hst
  obtain ⟨e, he, hlay⟩ := minimalAdmissible_restrict hX hi hE hrt
  obtain ⟨bF, hbF, hlayF⟩ := exists_image_map h he
  have hF0 : layer bF 0 = h '' layer k r := by
    show layerSet bF {0} = _
    rw [hlayF]
    show h '' layer e 0 = _
    rw [hlay, restrictParam_zero]
  have hF1 : layer bF 1 = h '' layer k t := by
    show layerSet bF {1} = _
    rw [hlayF]
    show h '' layer e 1 = _
    rw [hlay, restrictParam_one]
  obtain ⟨⟨a₀, b₀, hab⟩, hbFa, -⟩ := hbF
  have hFc := hab.1
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hFmem : ∀ y ∈ h '' layerSet k (Icc r t), ∃ zz : E, k zz ∈ Icc r t ∧ h zz.1 = y := by
    rintro _ ⟨_, ⟨zz, hzz, rfl⟩, rfl⟩
    exact ⟨zz, hzz, rfl⟩
  have hzF : h z.1 ∈ h '' layerSet k (Icc r t) :=
    ⟨z.1, ⟨z, ⟨(show k z = s from hz) ▸ hrs.le, (show k z = s from hz) ▸ hst.le⟩, rfl⟩, rfl⟩
  have hrne : (h '' layer k r).Nonempty := (layer_nonempty' hk r).image h
  have htne : (h '' layer k t).Nonempty := (layer_nonempty' hk t).image h
  rcases hpq with hq | hq
  · -- kind D
    set C := g '' layerSet k (Icc 0 (x ⟨3 * p.val + 3, by omega⟩)) with hC
    have hCc : Fold.Q78.IsContinuum C := isContinuum_homeo_image g
      (isContinuum_img hE.isCompact hk isClosed_Icc isPreconnected_Icc
        ⟨0, left_mem_Icc.2 unitInterval.nonneg'⟩)
    have hmeet : (h '' layerSet k (Icc r t) ∩ C).Nonempty :=
      ⟨h z.1, hzF, ⟨w.1, ⟨w, ⟨unitInterval.nonneg', hw'.2⟩, rfl⟩, hgw⟩⟩
    have havoid : Disjoint C (layer bF 0 ∪ layer bF 1) := by
      rw [hF0, hF1, disjoint_left]
      rintro _ ⟨_, ⟨w', hw'', rfl⟩, rfl⟩ hmem
      obtain ⟨j, hjp, hjL⟩ := mem_link_le84 hx hx0 hx15 g hg w' p hw''.2
      have key : ∀ Y : Set M, Y ⊆ chainLinks84 k x δ q → Disjoint Y (chainLinks84 k x δ p) →
          g w'.1 ∈ Y → False := by
        intro Y hYq hYp hgY
        by_cases hjp' : j = p
        · subst hjp'; exact disjoint_left.1 hYp hgY hjL
        · have hj : (j : ℕ) + 1 < q := by
            have h1 := Fin.le_def.1 hjp
            have h2 : (j : ℕ) ≠ p := fun h => hjp' (Fin.ext h)
            omega
          exact disjoint_left.1 (chain5_disjoint hL j q hj) hjL (hYq hgY)
      rcases hmem with hm | hm
      · exact key _ hr hrd hm
      · exact key _ ht htd hm
    have hCF := subset_of_meets_avoids hHU hAT hFc hbFa hCc hmeet havoid
    obtain ⟨a, ha⟩ := hk.2.1 0
    have hgaC : g a.1 ∈ C := ⟨a.1, ⟨a, ⟨unitInterval.nonneg', by
      rw [ha]; exact unitInterval.nonneg'⟩, rfl⟩, rfl⟩
    obtain ⟨zz, hzz, hzzeq⟩ := hFmem _ (hCF hgaC)
    have hd := close84 hh hg hzzeq
    have hzz1 : k zz < x ⟨1, by omega⟩ := by
      by_contra hc
      exact (gapBound84_near hgap hd 0 (by omega)).2
        ⟨by rw [ha, show x ⟨0, by omega⟩ = 0 from hx0], not_lt.1 hc⟩
    have hr0 : h '' layer k r ⊆ chainLinks84 k x δ 0 := by
      refine image_layer_subset_link84 k x h hh 0 ⟨?_, ?_⟩
      · show x ⟨0, by omega⟩ ≤ r
        rw [show x ⟨0, by omega⟩ = 0 from hx0]; exact unitInterval.nonneg'
      · show r ≤ x ⟨3, by omega⟩
        exact (hzz.1.trans hzz1.le).trans (xle84 hx _ _ (by omega))
    obtain ⟨y, hy⟩ := hrne
    have hq1 := ((hL.inter_iff 0 q).1 ⟨y, hr0 hy, hr hy⟩).2
    have hp0 : p = 0 := Fin.ext (by simp at hq1; omega)
    subst hp0
    exact hrp hr0
  · -- kind U
    set C := g '' layerSet k (Icc (x ⟨3 * p.val, by omega⟩) 1) with hC
    have hCc : Fold.Q78.IsContinuum C := isContinuum_homeo_image g
      (isContinuum_img hE.isCompact hk isClosed_Icc isPreconnected_Icc
        ⟨1, right_mem_Icc.2 unitInterval.le_one'⟩)
    have hmeet : (h '' layerSet k (Icc r t) ∩ C).Nonempty :=
      ⟨h z.1, hzF, ⟨w.1, ⟨w, ⟨hw'.1, unitInterval.le_one'⟩, rfl⟩, hgw⟩⟩
    have havoid : Disjoint C (layer bF 0 ∪ layer bF 1) := by
      rw [hF0, hF1, disjoint_left]
      rintro _ ⟨_, ⟨w', hw'', rfl⟩, rfl⟩ hmem
      obtain ⟨j, hjp, hjL⟩ := mem_link_ge84 hx hx0 hx15 g hg w' p hw''.1
      have key : ∀ Y : Set M, Y ⊆ chainLinks84 k x δ q → Disjoint Y (chainLinks84 k x δ p) →
          g w'.1 ∈ Y → False := by
        intro Y hYq hYp hgY
        by_cases hjp' : j = p
        · subst hjp'; exact disjoint_left.1 hYp hgY hjL
        · have hj : (q : ℕ) + 1 < j := by
            have h1 := Fin.le_def.1 hjp
            have h2 : (j : ℕ) ≠ p := fun h => hjp' (Fin.ext h)
            omega
          exact disjoint_left.1 (chain5_disjoint hL q j hj) (hYq hgY) hjL
      rcases hmem with hm | hm
      · exact key _ hr hrd hm
      · exact key _ ht htd hm
    have hCF := subset_of_meets_avoids hHU hAT hFc hbFa hCc hmeet havoid
    obtain ⟨a, ha⟩ := hk.2.1 1
    have hgaC : g a.1 ∈ C := ⟨a.1, ⟨a, ⟨by rw [ha]; exact unitInterval.le_one',
      unitInterval.le_one'⟩, rfl⟩, rfl⟩
    obtain ⟨zz, hzz, hzzeq⟩ := hFmem _ (hCF hgaC)
    have hd := close84 hh hg hzzeq
    have hzz14 : x ⟨14, by omega⟩ < k zz := by
      by_contra hc
      exact (gapBound84_near hgap hd 14 (by omega)).1
        ⟨not_lt.1 hc, by rw [ha, show x ⟨15, by omega⟩ = 1 from hx15]⟩
    have ht4 : h '' layer k t ⊆ chainLinks84 k x δ 4 := by
      refine image_layer_subset_link84 k x h hh 4 ⟨?_, ?_⟩
      · show x ⟨12, by omega⟩ ≤ t
        exact (xle84 hx _ _ (by omega)).trans (hzz14.le.trans hzz.2)
      · show t ≤ x ⟨15, by omega⟩
        rw [show x ⟨15, by omega⟩ = 1 from hx15]; exact unitInterval.le_one'
    obtain ⟨y, hy⟩ := htne
    have hq3 := ((hL.inter_iff 4 q).1 ⟨y, ht4 hy, ht hy⟩).1
    have hp4 : p = 4 := Fin.ext (by simp at hq3; have := q.isLt; omega)
    subst hp4
    exact htp ht4

/-- **Hagopian's (5)** in parameter form: the parameters `u` with `h[k⁻¹(u)] ⊆ L i` form an
interval. *Proof*: these sets are open (`isOpen_params_meeting`, through (3)), cover `[0, 1]`,
non-adjacent ones are disjoint, and `0 ∈ V 0 ∖ V 1`, `1 ∈ V 4 ∖ V 3`; a non-interval among them gives
a fold (`exists_fold`), which `no_fold84` excludes. -/
theorem layer_convex84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (hgap : GapBound84 k x δ)
    (hL : IsChain5 (chainLinks84 k x δ)) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ)
    (hcov : h '' E ⊆ ⋃ i, chainLinks84 k x δ i)
    (h0 : h '' layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1))
    (h1 : h '' layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3)) (i : Fin 5) :
    {u | h '' layer k u ⊆ chainLinks84 k x δ i}.OrdConnected := by
  by_contra hnc
  have hk := hE.2.1
  set V : Fin 5 → Set unitInterval := fun j => {u | h '' layer k u ⊆ chainLinks84 k x δ j}
    with hVdef
  have hVeq : ∀ j, V j = {u | (layer k u ∩ h ⁻¹' chainLinks84 k x δ j).Nonempty} := by
    intro j
    ext u
    constructor
    · intro hu
      obtain ⟨y, hy⟩ := layer_nonempty' hk u
      exact ⟨y, hy, hu ⟨y, hy, rfl⟩⟩
    · rintro ⟨y, hy, hyL⟩
      refine (link_dichotomy84 hX hi hE hx hx0 hx15 hgap h hh u j).resolve_right ?_
      exact not_disjoint_iff.2 ⟨h y, ⟨y, hy, rfl⟩, hyL⟩
  have hV : ∀ j, IsOpen (V j) := fun j => by
    rw [hVeq]
    exact isOpen_params_meeting hX hi hE ((hL.isOpen j).preimage h.continuous)
  have hcov' : ∀ u, ∃ j, u ∈ V j := by
    intro u
    obtain ⟨y, hy⟩ := layer_nonempty' hk u
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ⟨y, layer_subset_set k u hy, rfl⟩)
    exact ⟨j, by rw [hVeq]; exact ⟨y, hy, hj⟩⟩
  have hdisj : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [disjoint_left]
    intro u hu hu'
    obtain ⟨y, hy⟩ := layer_nonempty' hk u
    exact disjoint_left.1 (chain5_disjoint hL i j hij) (hu ⟨y, hy, rfl⟩) (hu' ⟨y, hy, rfl⟩)
  have h0' : (0 : unitInterval) ∈ V 0 \ V 1 := by
    refine ⟨fun y hy => (h0 hy).1, fun hsub => ?_⟩
    obtain ⟨y, hy⟩ := (layer_nonempty' hk 0).image h
    exact (h0 hy).2 (subset_closure (hsub hy))
  have h1' : (1 : unitInterval) ∈ V 4 \ V 3 := by
    refine ⟨fun y hy => (h1 hy).1, fun hsub => ?_⟩
    obtain ⟨y, hy⟩ := (layer_nonempty' hk 1).image h
    exact (h1 hy).2 (subset_closure (hsub hy))
  obtain ⟨r, s, t, hrs, hst, p, q, hpq, hs, ⟨hr, hrp⟩, ⟨ht, htp⟩⟩ :=
    exists_fold hV hcov' hdisj h0' h1' ⟨i, hnc⟩
  exact no_fold84 hX hi hE hx hx0 hx15 hgap hL h hh hrs hst hpq hs hr hrp ht htp

/-- **Hagopian's (6)** (p. 340: "It follows from (1), (2), (4), and (5) that (6) `h[E]` runs
straight through `𝔏`"), for any map `b` of `G = h[E]` whose layers are the images of those of
`k`. -/
theorem translate_runsStraight84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) (hx0 : x 0 = 0) (hx15 : x 15 = 1) {δ : ℝ} (hgap : GapBound84 k x δ)
    (hL : IsChain5 (chainLinks84 k x δ)) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ)
    (hcov : h '' E ⊆ ⋃ i, chainLinks84 k x δ i)
    (h0 : h '' layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1))
    (h1 : h '' layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3))
    {G : Set M} (hG : G = h '' E) {b : G → unitInterval}
    (hb : ∀ S, layerSet b S = h '' layerSet k S) : RunsStraight b (chainLinks84 k x δ) := by
  subst hG
  have hbl : ∀ u, layer b u = h '' layer k u := fun u => hb {u}
  refine ⟨hcov, ?_, ?_, ?_, ?_⟩
  · rw [hbl]
    exact fun y hy => ⟨(h0 hy).1, fun h' => (h0 hy).2 (subset_closure h')⟩
  · rw [hbl]
    exact fun y hy => ⟨(h1 hy).1, fun h' => (h1 hy).2 (subset_closure h')⟩
  · intro r i hr
    rw [hbl] at hr ⊢
    exact layer_frontier84 hX hi hE hx hx0 hx15 hgap h hh r i hr
  · intro r t i _ hrt
    rw [hbl, hbl] at hrt
    rw [hb]
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hc := layer_convex84 hX hi hE hx hx0 hx15 hgap hL h hh hcov h0 h1 i
    have hmem : k w ∈ {u | h '' layer k u ⊆ chainLinks84 k x δ i} :=
      hc.out (show r ∈ _ from fun y hy => hrt (Or.inl hy))
        (show t ∈ _ from fun y hy => hrt (Or.inr hy)) hw
    exact hmem ⟨w.1, mem_layer_self84 k w, rfl⟩

end Dichotomy

end HPC.Hagopian
