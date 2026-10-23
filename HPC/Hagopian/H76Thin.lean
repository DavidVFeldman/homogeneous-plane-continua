import HPC.Hagopian.H76T7

/-!
# Batch 165, item B: link control in a thin strip

* `pi_thin_near_layer`: upper semicontinuity of the layers in collar coordinates. A point of `M`
  whose `π`-image lies in a thin enough collar rectangle over `[a, b]` is close to a point of `E`
  with parameter in `[a, b]` close to its abscissa. (Compactness of `M × rectangle`.)
* `EndCtl` (moved here unchanged from the skeleton `Hagopian76J.lean`) and
  `exists_isEps1_endCtl_aux`.
* `link_control_aux`: for an ordered refinement `L` of `chainG k ε₁` at an `ε₁` with `EndCtl`, a point
  of `M` over a thin rectangle over `[3/22, 19/22]` lies in none of `L₁`, `L₁₁`, and a point of
  `Lⱼ` (Lean index `j`, `0 ≤ j ≤ 10`) over it has abscissa in `((j − 1)/11 − η, (j + 2)/11 + η)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thin

variable {M : Set Pt}

/-- A continuous function positive on a compact set is bounded below there by some `c ∈ (0, 1]`. -/
theorem exists_pos_lt_on_compact {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {g : X → ℝ} (hg : Continuous g) (hpos : ∀ p ∈ S, 0 < g p) :
    ∃ c > 0, c ≤ 1 ∧ ∀ p ∈ S, c < g p := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, le_rfl, fun p hp => by rw [h] at hp; exact hp.elim⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn h hg.continuousOn
    have h0 := hpos p₀ hp₀
    refine ⟨min 1 (g p₀ / 2), lt_min one_pos (by linarith), min_le_left _ _, fun p hp => ?_⟩
    have := isMinOn_iff.1 hmin p hp
    have := min_le_right 1 (g p₀ / 2)
    linarith

/-- A point of `M` over the axis lies in the layer of its abscissa. -/
theorem mem_layer_of_pi_eq_gamma {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {x : M} {t : unitInterval}
    (hx : π (x : Pt) = γ t) : ∃ y : E, (y : M) = x ∧ k y = t := by
  obtain ⟨x₀, hx₀⟩ := layer_nonempty hE.2.1.2.1 t
  obtain ⟨e, he, hex⟩ := hx₀
  have h1 : π (x : Pt) = π ((e : M) : Pt) := by
    rw [hx, hγπ t _ ⟨(e : M), ⟨e, he, rfl⟩, rfl⟩]
  have h2 := (hπS _ _).1 h1
  change (x : Pt) ∈ HPC.Moore.elt (layerSetoid k) ((e : M) : Pt) at h2
  rw [elt_layerSetoid_of_mem, toPt_layer_eq] at h2
  obtain ⟨y, hy, hyx⟩ := h2
  exact ⟨y, Subtype.ext hyx, hy.trans he⟩

/-- **Upper semicontinuity of the layers in collar coordinates.** -/
theorem pi_thin_near_layer [CompactSpace M] {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (x : M) (z : ℝ × ℝ), z ∈ Icc a b ×ˢ Icc (-c) c → π (x : Pt) = F z →
      ∃ y : E, (k y : ℝ) ∈ Icc a b ∧ |(k y : ℝ) - z.1| < η ∧ dist (x : Pt) ((y : M) : Pt) < η := by
  obtain ⟨hFemb, hF0, -⟩ := hF
  set R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 : ℝ) 1 with hRd
  have hR1 : R ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z ⟨⟨h1, h2⟩, h3⟩ =>
    ⟨⟨by linarith, by linarith⟩, h3⟩
  have hFc : ContinuousOn F R :=
    (continuousOn_iff_continuous_restrict.2 hFemb.continuous).mono hR1
  haveI : CompactSpace R := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  set Z : Set (M × R) := {p | π ((p.1 : M) : Pt) = F (p.2 : ℝ × ℝ)} with hZd
  have hZc : IsClosed Z := isClosed_eq (hπc.comp (continuous_subtype_val.comp continuous_fst))
    (hFc.comp_continuous (continuous_subtype_val.comp continuous_snd) fun p => p.2.2)
  set W : Set (M × R) := {p | ∃ y : E, (k y : ℝ) ∈ Icc a b ∧
    |(k y : ℝ) - (p.2 : ℝ × ℝ).1| < η ∧ dist ((p.1 : M) : Pt) ((y : M) : Pt) < η} with hWd
  have hWo : IsOpen W := by
    have : W = ⋃ y : E, ({_p : M × R | (k y : ℝ) ∈ Icc a b} ∩
        ({p : M × R | |(k y : ℝ) - (p.2 : ℝ × ℝ).1| < η} ∩
          {p : M × R | dist ((p.1 : M) : Pt) ((y : M) : Pt) < η})) := by
      ext p; simp only [hWd, mem_iUnion, mem_setOf_eq, mem_inter_iff]
    rw [this]
    refine isOpen_iUnion fun y => isOpen_const.inter ((isOpen_lt ?_ continuous_const).inter
      (isOpen_lt ?_ continuous_const))
    · exact (continuous_const.sub (continuous_fst.comp (continuous_subtype_val.comp
        continuous_snd))).abs
    · exact (continuous_subtype_val.comp continuous_fst).dist continuous_const
  have hS : IsCompact (Z \ W) := (hZc.sdiff hWo).isCompact
  have hpos : ∀ p ∈ Z \ W, 0 < |((p.2 : ℝ × ℝ)).2| := by
    rintro ⟨x, ⟨⟨t, h⟩, ⟨ht, hh⟩⟩⟩ ⟨hZ, hW⟩
    rcases (abs_nonneg h).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have h0 : h = 0 := abs_eq_zero.1 h'.symm
      subst h0
      set t' : unitInterval := ⟨t, by linarith [ht.1], by linarith [ht.2]⟩
      have hxt : π (x : Pt) = γ t' := by rw [← hF0 t']; exact hZ
      obtain ⟨y, hyx, hyt⟩ := mem_layer_of_pi_eq_gamma hE hπS hγπ hxt
      apply hW
      refine ⟨y, by rw [hyt]; exact ht, ?_, ?_⟩
      · rw [hyt]; simp [t', hη]
      · rw [hyx, dist_self]; exact hη
  obtain ⟨c, hc, hc1, hcS⟩ := exists_pos_lt_on_compact hS
    (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).abs hpos
  refine ⟨c, hc, hc1, fun x z hz hxz => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hzR : z ∈ R := ⟨⟨h1, h2⟩, by linarith, by linarith⟩
  by_contra hn
  have hp : ((x, ⟨z, hzR⟩) : M × R) ∈ Z \ W := ⟨hxz, fun ⟨y, hy⟩ => hn ⟨y, hy⟩⟩
  have h6 : c < |z.2| := hcS _ hp
  have h5 : |z.2| ≤ c := abs_le.2 ⟨h3, h4⟩
  linarith

/-- **End control for `ε₁`** (commission 165 §1, item B): the end links `L₁`, `L₁₁` stay away from
the parameters over `⟨p₁, p₅⟩`. A further term of the minimum defining `ε₁`. (Moved here unchanged
from the skeleton `Hagopian76J.lean`.) -/
def EndCtl {E : Set M} (k : E → unitInterval) (ε₁ : ℝ) : Prop :=
  (∀ x ∈ layerSet k {t : unitInterval | (t : ℝ) ≤ 2 / 22},
    ∀ y ∈ layerSet k {t : unitInterval | 3 / 22 ≤ (t : ℝ)}, 4 * ε₁ ≤ dist x y) ∧
  (∀ x ∈ layerSet k {t : unitInterval | 20 / 22 ≤ (t : ℝ)},
    ∀ y ∈ layerSet k {t : unitInterval | (t : ℝ) ≤ 19 / 22}, 4 * ε₁ ≤ dist x y)

/-- **`ε₁` with end control exists.** -/
theorem exists_isEps1_endCtl_aux {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : ∃ ε₁, IsEps1 k ε₁ ∧ EndCtl k ε₁ := by
  obtain ⟨ε, he⟩ := exists_isEps1 hE
  have hEc := hE.isCompact
  have hk := hE.2.1.1
  have hcl1 : IsClosed {t : unitInterval | (t : ℝ) ≤ 2 / 22} :=
    isClosed_le continuous_subtype_val continuous_const
  have hcl2 : IsClosed {t : unitInterval | 3 / 22 ≤ (t : ℝ)} :=
    isClosed_le continuous_const continuous_subtype_val
  have hcl3 : IsClosed {t : unitInterval | 20 / 22 ≤ (t : ℝ)} :=
    isClosed_le continuous_const continuous_subtype_val
  have hcl4 : IsClosed {t : unitInterval | (t : ℝ) ≤ 19 / 22} :=
    isClosed_le continuous_subtype_val continuous_const
  have hdis : ∀ {A B : Set unitInterval}, Disjoint A B → Disjoint (layerSet k A) (layerSet k B) := by
    intro A B hAB
    rw [disjoint_left]
    rintro _ ⟨e, he, rfl⟩ ⟨e', he', hee'⟩
    have : e' = e := Subtype.val_injective hee'
    subst this
    exact disjoint_left.1 hAB he he'
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_pos_le_dist (isCompact_img hEc hk hcl1)
    (isCompact_img hEc hk hcl2).isClosed
    (hdis (disjoint_left.2 fun t (h1 : (t : ℝ) ≤ 2 / 22) (h2 : 3 / 22 ≤ (t : ℝ)) => by linarith))
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_pos_le_dist (isCompact_img hEc hk hcl3)
    (isCompact_img hEc hk hcl4).isClosed
    (hdis (disjoint_left.2 fun t (h1 : 20 / 22 ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ 19 / 22) => by linarith))
  set ε₁ := min ε (min (δ₁ / 4) (δ₂ / 4)) with hε₁
  have hle : ε₁ ≤ ε := min_le_left _ _
  have hle1 : ε₁ ≤ δ₁ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hle2 : ε₁ ≤ δ₂ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hpos : 0 < ε₁ := lt_min he.pos (lt_min (by positivity) (by positivity))
  refine ⟨ε₁, ⟨hpos, fun i j hij hj x hx y hy => ?_, fun x hx y hy => ?_⟩, ?_, ?_⟩
  · have := he.sep i j hij hj x hx y hy; linarith
  · have := he.ends x hx y hy; linarith
  · intro x hx y hy; have := h₁ x hx y hy; linarith
  · intro x hx y hy; have := h₂ x hx y hy; linarith

/-- The piece containing a point of `E`. -/
theorem mem_piece_ceil {E : Set M} (k : E → unitInterval) (y : E) :
    (y : M) ∈ piece k ⌈11 * (k y : ℝ)⌉₊ ∧ ⌈11 * (k y : ℝ)⌉₊ ≤ 11 := by
  have h0 : 0 ≤ (k y : ℝ) := (k y).2.1
  have h1 : (k y : ℝ) ≤ 1 := (k y).2.2
  refine ⟨⟨y, ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · have := Nat.ceil_lt_add_one (show 0 ≤ 11 * (k y : ℝ) by positivity)
    show ((⌈11 * (k y : ℝ)⌉₊ : ℝ) - 1) / 11 ≤ (k y : ℝ)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 11)]; linarith
  · have := Nat.le_ceil (11 * (k y : ℝ))
    show (k y : ℝ) ≤ (⌈11 * (k y : ℝ)⌉₊ : ℝ) / 11
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 11)]; linarith
  · apply Nat.ceil_le.2; push_cast; linarith

/-- **Link control in a thin strip** (commission 165 §2, item B). -/
theorem link_control_aux [CompactSpace M] {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) (hend : EndCtl k ε₁)
    {π : Pt → Pt} (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLG : ∀ j, L j ⊆ chainG k ε₁ j) {η : ℝ}
    (hη : 0 < η) (hηε : η ≤ ε₁) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (x : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22) (19 / 22) ×ˢ Icc (-c) c →
      π (x : Pt) = F z → ∀ j : Fin 11, (x : Pt) ∈ L j →
        1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ ((j : ℝ) - 1) / 11 - η < z.1 ∧ z.1 < ((j : ℝ) + 2) / 11 + η := by
  obtain ⟨c, hc, hc1, hcz⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (by norm_num : (0 : ℝ) ≤ 3 / 22)
    (by norm_num : (19 / 22 : ℝ) ≤ 1) hη
  refine ⟨c, hc, hc1, fun x z hz hxz j hxj => ?_⟩
  obtain ⟨y, hyab, hyz, hxy⟩ := hcz x z hz hxz
  -- the point `p` of the piece `j + 1` near `x`
  obtain ⟨q, ⟨m, ⟨e, ⟨he1, he2⟩, rfl⟩, rfl⟩, hxq⟩ :=
    mem_thickening_iff.1 (chainG_subset_thickening k ε₁ j (hLG j hxj))
  have hpy : dist (e : M) (y : M) < 2 * ε₁ := by
    have h := dist_triangle ((e : M) : Pt) (x : Pt) ((y : M) : Pt)
    rw [dist_comm] at hxq
    show dist ((e : M) : Pt) ((y : M) : Pt) < 2 * ε₁
    linarith
  have hj10 : (j : ℕ) ≤ 10 := Nat.lt_succ_iff.1 j.2
  have hj10' : ((j : ℕ) : ℝ) ≤ 10 := by exact_mod_cast hj10
  obtain ⟨hy1, hy2⟩ := hyab
  have hyz' := abs_lt.1 hyz
  -- not the first link
  have hj1 : 1 ≤ (j : ℕ) := by
    by_contra h0
    have h0' : (j : ℕ) = 0 := by omega
    have hek : (k e : ℝ) ≤ 2 / 22 := by
      have := he2; rw [h0'] at this; push_cast at this; linarith
    have := hend.1 (e : M) ⟨e, hek, rfl⟩ (y : M) ⟨y, hy1, rfl⟩
    linarith
  -- not the last link
  have hj9 : (j : ℕ) ≤ 9 := by
    by_contra h0
    have h0' : (j : ℕ) = 10 := by omega
    have hek : 20 / 22 ≤ (k e : ℝ) := by
      have := he1; rw [h0'] at this; push_cast at this; linarith
    have := hend.2 (e : M) ⟨e, hek, rfl⟩ (y : M) ⟨y, hy2, rfl⟩
    linarith
  obtain ⟨hym, hm11⟩ := mem_piece_ceil k y
  set m := ⌈11 * (k y : ℝ)⌉₊ with hm
  have hmle : (m : ℝ) < 11 * (k y : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by have := (k y).2.1; positivity)
  have hmge : 11 * (k y : ℝ) ≤ m := Nat.le_ceil _
  have hepiece : (e : M) ∈ piece k ((j : ℕ) + 1) := ⟨e, ⟨he1, he2⟩, rfl⟩
  refine ⟨hj1, hj9, ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have hky : (k y : ℝ) < ((j : ℝ) - 1) / 11 := by linarith
    have hmj : m + 1 < (j : ℕ) + 1 := by
      have : (m : ℝ) < (j : ℝ) := by
        have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11)).1 hky; linarith
      have hmj' : m < (j : ℕ) := by exact_mod_cast this
      omega
    have := he.sep m ((j : ℕ) + 1) hmj (by omega) (y : M) hym (e : M) hepiece
    rw [dist_comm] at this
    linarith
  · by_contra hlt
    push_neg at hlt
    have hky : ((j : ℝ) + 2) / 11 < (k y : ℝ) := by linarith
    have hmj : (j : ℕ) + 1 + 1 < m := by
      have : (j : ℝ) + 2 < (m : ℝ) := by
        have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 11)).1 hky; linarith
      have : (j : ℕ) + 2 < m := by exact_mod_cast this
      omega
    have := he.sep ((j : ℕ) + 1) m hmj hm11 (e : M) hepiece (y : M) hym
    linarith

end Thin

end HPC.Hagopian
