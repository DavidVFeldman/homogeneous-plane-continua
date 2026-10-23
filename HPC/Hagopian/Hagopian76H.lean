import HPC.Hagopian.H76NoBelowMain

/-!
# Batch 163: Hagopian 1976, the collar geometry — an adapted collar; "no `π[M]` just below
# `π[E]`" (the core of Lemma 9's proof); Lemma 9; T3 and T6

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 344–346. The route is commission 163 §1:
Lemma 9's argument run for an arbitrary point of `M − E` just below `π[E]`, with the collar in place
of "`π[E]` horizontal" and an open rectangle of the collar in place of Theorem 28's simple domain.

The proofs are split over `H76Rect`, `H76Glue`, `H76Adapt`, `H76AdaptHalf`, `H76AdaptMain` (item A)
and `H76NoBelow`, `H76NoBelowCore`, `H76NoBelowMain` (item B). Shape changes against the skeleton
(`doc/batches/skeletons/Hagopian76H.lean`), recorded at the statements and in
`doc/batches/REPORT-batch163.md`: `no_M_below` drops the hypothesis `a ≤ b` and `hagopian76_T6`
drops `a ≤ b →` (both unused: for `a > b` the strip is empty). `hagopian76_T3` (T3 at the interior
points) is added.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A. An adapted collar -/

/-- **A collar in which a given transverse arc is vertical** (Hagopian p. 345: "We assume without
loss of generality that `π[E]` is lying on a horizontal line `B` in `R²` and `π[I − {y}]` is below
`B` on a vertical line"). `β` is an arc ending at the interior point `γ y` and meeting `range γ` only
there. From `plane_schoenflies₂` and the construction of `exists_collar`. -/
theorem exists_collar_adapted {γ : unitInterval → Pt} (hγ : IsEmbedding γ) {y : unitInterval}
    (hy0 : 0 < y) (hy1 : y < 1) {b : Pt} {β : Set Pt} (hβ : TArc b (γ y) β)
    (hβγ : β ∩ range γ = {γ y}) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Icc (-c) 0) ⊆ β :=
  exists_collar_adapted_aux hγ hy0 hy1 hβ hβγ

section Core

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## B. The core of Lemma 9 -/

/-- **No point of `π[M]` just below `π[E]`, away from the accessing vertical** (the argument of
pp. 344–345, run for an arbitrary point; commission 163 §1). Let `F` be a collar of `γ` in which the
vertical below `γ y` (`0 < y < 1`) meets `π[M]` only at its foot. Then for every closed interval
`[a, b] ⊆ (0, 1)` not containing `y`, some open strip below `γ([a, b])` in collar coordinates misses
`π[M]`. (Shape change: the skeleton's unused hypothesis `hab : a ≤ b` is dropped.) -/
theorem no_M_below (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hvert : ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Ico (-c) 0) ∩ π '' M = ∅)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hy : (y : ℝ) ∉ Icc a b) :
    ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  obtain ⟨c₀, hc₀, hv⟩ := hvert
  obtain ⟨G, hGc, hG, hGF⟩ := hF.exists_continuous
  have hK : ∀ {S : Set (ℝ × ℝ)}, S ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → G '' S = F '' S :=
    fun hS => image_congr fun q hq => hGF q (hS hq)
  have hsub : ∀ {S : Set ℝ} {c : ℝ}, S ⊆ Icc 0 1 → c ≤ 1 →
      S ×ˢ Ico (-c) 0 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun hS hc =>
    prod_mono hS fun s hs => ⟨by linarith [hs.1], hs.2.le.trans zero_le_one⟩
  have hv' : G '' ({(y : ℝ)} ×ˢ Ico (-min c₀ 1) 0) ∩ π '' M = ∅ := by
    rw [hK (hsub (singleton_subset_iff.2 y.2) (min_le_right _ _))]
    exact subset_eq_empty (inter_subset_inter_left _ (image_mono (prod_mono subset_rfl
      (Ico_subset_Ico_left (neg_le_neg (min_le_left _ _)))))) hv
  obtain ⟨c, hc, hd⟩ := no_M_below_aux hX hi hE hπ hπS hγ hγπ hG hGc hy0 hy1
    (lt_min hc₀ one_pos) hv' ha hb hy
  refine ⟨min c 1, lt_min hc one_pos, ?_⟩
  rw [← hK (hsub (fun x hx => ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩) (min_le_right _ _))]
  exact hd.mono_left (image_mono (prod_mono subset_rfl
    (Ico_subset_Ico_left (neg_le_neg (min_le_left _ _)))))

/-! ## C. Lemma 9 -/

/-- **Lemma 9** (p. 344), collar form (restated from `Hagopian76G.lean`). From `exists_collar_adapted`
applied to `π[I]` (`π` is injective on `I`, which meets `E` only at its end) and `no_M_below` on a
small interval about `u`. -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessibleC (π '' M) γ u y := by
  obtain ⟨F, hF, c, hc, hv⟩ := exists_collar_vertical hE hπ hπS hγ hγπ hy0 hy1 hacc
  have hu0' : (0 : ℝ) < u := hu0
  have hu1' : (u : ℝ) < 1 := hu1
  have huy' : (u : ℝ) ≠ y := fun h => huy (Subtype.ext h)
  set d := min (|(u : ℝ) - y| / 2) (min (u : ℝ) (1 - u) / 2) with hd
  have hd0 : 0 < d := lt_min (half_pos (abs_pos.2 (sub_ne_zero.2 huy')))
    (half_pos (lt_min hu0' (by linarith)))
  have hd1 : d ≤ |(u : ℝ) - y| / 2 := min_le_left _ _
  have hd2 : d ≤ min (u : ℝ) (1 - u) / 2 := min_le_right _ _
  have hd3 : d < u := lt_of_le_of_lt hd2 (by linarith [min_le_left (u : ℝ) (1 - u)])
  have hd4 : d < 1 - u := lt_of_le_of_lt hd2 (by linarith [min_le_right (u : ℝ) (1 - u)])
  obtain ⟨c', hc', hd'⟩ := no_M_below hX hi hE hπ hπS hγ hγπ hF hy0 hy1 ⟨c, hc, hv⟩
    (a := u - d) (b := u + d) (by linarith) (by linarith) (by
      rintro ⟨h1, h2⟩
      rcases le_total (u : ℝ) y with h | h
      · rw [abs_of_nonpos (by linarith)] at hd1; linarith
      · rw [abs_of_nonneg (by linarith)] at hd1; linarith)
  refine ⟨hu0, hu1, hy0, hy1, huy, F, -1, min c' 1, min c 1, hF, Or.inr rfl,
    lt_min hc' one_pos, min_le_right _ _, lt_min hc one_pos, min_le_right _ _, ?_, ?_⟩
  · refine hd'.mono_left (image_mono ?_)
    rintro _ ⟨r, ⟨hr0, hr1⟩, rfl⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith [min_le_left c' 1], by linarith⟩
  · rw [Set.disjoint_iff_inter_eq_empty]
    refine subset_eq_empty (inter_subset_inter_left _ (image_mono ?_)) hv
    rintro _ ⟨r, ⟨hr0, hr1⟩, rfl⟩
    exact ⟨rfl, by linarith [min_le_left c 1], by linarith⟩

/-! ## D. T3 and T6 -/

/-- **T3, T6** (pp. 345–346): "each point of `π[E]` is an end point of an arc segment in
`R² − π[M]` below `π[E]` (Lemma 9)"; "It follows from the proof of Lemma 9 that there exists a
horizontal interval `I₁` below `⟨p₁, p₅⟩` in `R² − π[M]` such that the end points of `I₁` are in
`⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩` and no point of `π[M]` lies between `I₁` and `⟨p₁, p₅⟩`." In collar
coordinates: given an accessible interior layer `k⁻¹(y)`, there is a collar and, for every
`[a, b] ⊆ (0, 1)` avoiding `y`, a strip below `γ([a, b])` free of `π[M]`. Hagopian's
`⟨p₁, p₅⟩` is to be placed away from the accessible layer; as stated (any `[a, b]` avoiding `y`) no
reparametrization of `k` is needed. (Shape change: the skeleton's unused premise `a ≤ b →` is
dropped.) -/
theorem hagopian76_T6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∀ a b : ℝ, 0 < a → b < 1 → (y : ℝ) ∉ Icc a b →
      ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  obtain ⟨F, hF, c, hc, hv⟩ := exists_collar_vertical hE hπ hπS hγ hγπ hy0 hy1 hacc
  exact ⟨F, hF, fun a b ha hb hy =>
    no_M_below hX hi hE hπ hπS hγ hγπ hF hy0 hy1 ⟨c, hc, hv⟩ ha hb hy⟩

/-- **T3** (p. 345, interior points): "each point of `π[E]` is an end point of an arc segment in
`R² − π[M]` below `π[E]` (Lemma 9)". In collar coordinates, for one collar `F`: for every interior
parameter `t`, the vertical below `γ t` misses `π[M]` near its foot. (Not in the skeleton; added. The
end points `γ 0`, `γ 1` are not covered.) -/
theorem hagopian76_T3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∀ t : unitInterval, 0 < t → t < 1 →
      ∃ c > 0, F '' ({(t : ℝ)} ×ˢ Ico (-c) 0) ∩ π '' M = ∅ := by
  obtain ⟨F, hF, c, hc, hv⟩ := exists_collar_vertical hE hπ hπS hγ hγπ hy0 hy1 hacc
  refine ⟨F, hF, fun t ht0 ht1 => ?_⟩
  by_cases hty : t = y
  · subst hty; exact ⟨c, hc, hv⟩
  · obtain ⟨c', hc', hd⟩ := no_M_below hX hi hE hπ hπS hγ hγπ hF hy0 hy1 ⟨c, hc, hv⟩
      (a := t) (b := t) ht0 ht1 (fun h => hty (Subtype.ext (le_antisymm h.1 h.2)))
    refine ⟨c', hc', ?_⟩
    rw [← disjoint_iff_inter_eq_empty]
    exact hd.mono_left (image_mono (prod_mono (singleton_subset_iff.2 (left_mem_Icc.2 le_rfl))
      subset_rfl))

end Core

end HPC.Hagopian
