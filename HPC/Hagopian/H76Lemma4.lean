import HPC.Hagopian.H76Lemma3

/-!
# Batch 156, item D: Lemma 4 of Hagopian 1976 (linear order; the countable form)

* `ext_chain` (**the extensions away from `X` form a chain**). Let `F`, `H` be extensions of `E`
  away from `X` (maps `d`, `e`, both with `X` as the layer over `0`), neither containing the other.
  `J = F ∩ H` is a continuum (hereditary unicoherence) containing `E`; it meets neither `d⁻¹(1)` nor
  `e⁻¹(1)` (a subcontinuum meeting both end sets is everything, `eq_of_meets_ends`). Pick `z ∈ E` with
  `k(z) = 1`, so `d(z), e(z) > 0`; let `ρ > 0` be the least value of `d` on the compact set
  `F ∩ e⁻¹[e(z), 1]` (which misses `X`), `r = ρ / 2`, and `σ` the greatest value of `d` on `J`.
  Then `N = J ∩ d⁻¹[r, 1]`, `X₁ = d⁻¹[0, r]`, `X₂ = d⁻¹[σ, 1]`, `X₃ = e⁻¹[e(z), 1]` satisfy the
  hypotheses of `isTriod_of_core`: a triod in `M`, against atriodicity. This is Hagopian's
  "the continuum `H ∩ d⁻¹[[s, 1]]` would separate `F ∪ H` into three nonempty disjoint open sets",
  with the three pieces `X₁ ∖ N`, `X₂ ∖ N`, `X₃ ∖ N`; the first paragraph of the proof is not used.
* `exists_strictMono_seq_of_chain` (**the countable form**): in a second-countable space, a nonempty
  chain of closed sets with no largest element has a strictly increasing cofinal sequence. For each
  basic open set `Bₙ` met by some member choose such a member `Fₙ`; every member `F` lies in some
  `Fₙ`, for otherwise every `Fₙ ⊆ F`, and a member `G ⊋ F` would have a point `x ∉ F` with a basic
  neighbourhood `Bₙ` missing `F`, met by `G`, hence by `Fₙ ⊆ F`, which is absurd (so `F` would be
  largest). Then `Gₘ₊₁ ⊋ Gₘ ∪ Fₘ` is chosen by the absence of a largest element.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma4

variable {M : Set Pt}

/-- **Lemma 4, linear order.** Two extensions of `E` away from `X` are comparable. -/
theorem ext_chain (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {F H : Set M} (hF : IsExtensionAway E (layer k 0) F)
    (hH : IsExtensionAway E (layer k 0) H) : F ⊆ H ∨ H ⊆ F := by
  obtain ⟨hEF, d, ⟨⟨a, b, hab⟩, hd, hd0⟩, hdX⟩ := hF
  obtain ⟨hEH, e, ⟨⟨a', b', hab'⟩, he, he0⟩, heX⟩ := hH
  obtain ⟨⟨a₀, b₀, hab₀⟩, hk, -⟩ := hE
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hFH, hHF⟩ := hcon
  have hFc := hab.1
  have hHc := hab'.1
  have hEc := hab₀.1
  -- `J = F ∩ H`
  obtain ⟨x₀, hx₀⟩ := hk.2.1 0
  have hx₀X : (x₀ : M) ∈ layer k 0 := ⟨x₀, hx₀, rfl⟩
  set J := F ∩ H with hJdef
  have hJ : Fold.Q78.IsContinuum J :=
    isContinuum_inter_of_HU hHU hFc hHc ⟨x₀, hEF x₀.2, hEH x₀.2⟩
  have hEJ : E ⊆ J := fun x hx => ⟨hEF hx, hEH hx⟩
  have hXJ : layer k 0 ⊆ J := (img_subset _).trans hEJ
  -- `J` misses the far end sets
  have hJV : ∀ w : F, d w = 1 → (w : M) ∉ J := by
    intro w hw hwJ
    apply hFH
    have := eq_of_meets_ends hab hd hd0 inter_subset_left hJ
      ⟨x₀, hXJ hx₀X, by rw [hdX]; exact hx₀X⟩ ⟨w, hwJ, w, hw, rfl⟩
    rw [← this]; exact inter_subset_right
  have hJW : ∀ w : H, e w = 1 → (w : M) ∉ J := by
    intro w hw hwJ
    apply hHF
    have := eq_of_meets_ends hab' he he0 inter_subset_right hJ
      ⟨x₀, hXJ hx₀X, by rw [heX]; exact hx₀X⟩ ⟨w, hwJ, w, hw, rfl⟩
    rw [← this]; exact inter_subset_left
  -- the point `z`
  obtain ⟨z, hz⟩ := hk.2.1 1
  have hzX : (z : M) ∉ layer k 0 := by
    rintro ⟨z', hz', hzz⟩
    have : z' = z := Subtype.ext hzz
    have h0 : k z' = 0 := hz'
    rw [this, hz] at h0
    exact one_ne_zero h0
  set zF : F := ⟨z, hEF z.2⟩
  set zH : H := ⟨z, hEH z.2⟩
  have hdz : 0 < d zF := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hzX ?_
    rw [← hdX]; exact ⟨zF, h0.symm, rfl⟩
  have hez : 0 < e zH := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hzX ?_
    rw [← heX]; exact ⟨zH, h0.symm, rfl⟩
  -- `ρ`: the least value of `d` on `F ∩ e⁻¹[e(z), 1]`
  set X₃ := Subtype.val '' (e ⁻¹' Icc (e zH) 1) with hX₃def
  have hX₃ : Fold.Q78.IsContinuum X₃ :=
    isContinuum_img hHc.1 he isClosed_Icc isPreconnected_Icc ⟨e zH, le_rfl, unitInterval.le_one'⟩
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc.1
  set S₃ : Set F := Subtype.val ⁻¹' X₃
  have hS₃c : IsCompact S₃ := (hX₃.1.isClosed.preimage continuous_subtype_val).isCompact
  have hzS₃ : zF ∈ S₃ := ⟨zH, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩
  obtain ⟨w₀, hw₀, hw₀min⟩ := hS₃c.exists_isMinOn ⟨zF, hzS₃⟩ hd.1.continuousOn
  have hρ : 0 < d w₀ := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => ?_
    have hw₀X : (w₀ : M) ∈ layer k 0 := by rw [← hdX]; exact ⟨w₀, h0.symm, rfl⟩
    obtain ⟨v, hv, hve⟩ := hw₀
    rw [← heX] at hw₀X
    obtain ⟨v', hv', hve'⟩ := hw₀X
    have : v' = v := Subtype.ext (hve'.trans hve.symm)
    rw [this] at hv'
    have : e zH ≤ 0 := (mem_singleton_iff.1 hv') ▸ hv.1
    exact absurd this (not_le.2 hez)
  -- `r = ρ / 2`
  set r : unitInterval := ⟨(d w₀ : ℝ) / 2, by
    constructor
    · have := (d w₀).2.1; linarith
    · have := (d w₀).2.2; linarith⟩ with hrdef
  have hr0 : 0 < r := by
    show (0 : ℝ) < (d w₀ : ℝ) / 2
    have : (0 : ℝ) < d w₀ := hρ
    linarith
  have hrρ : r < d w₀ := by
    show (d w₀ : ℝ) / 2 < d w₀
    have : (0 : ℝ) < d w₀ := hρ
    linarith
  have hS₃r : ∀ w ∈ S₃, r < d w := fun w hw => hrρ.trans_le (hw₀min hw)
  -- `σ`: the greatest value of `d` on `J`
  set SJ : Set F := Subtype.val ⁻¹' J
  have hSJc : IsCompact SJ := (hJ.1.isClosed.preimage continuous_subtype_val).isCompact
  have hzSJ : zF ∈ SJ := hEJ z.2
  obtain ⟨w₁, hw₁, hw₁max⟩ := hSJc.exists_isMaxOn ⟨zF, hzSJ⟩ hd.1.continuousOn
  set σ := d w₁
  have hrσ : r < σ := (hS₃r zF hzS₃).trans_le (hw₁max hzSJ)
  -- the four continua
  set N := J ∩ Subtype.val '' (d ⁻¹' Icc r 1) with hNdef
  set X₁ := Subtype.val '' (d ⁻¹' Icc 0 r) with hX₁def
  set X₂ := Subtype.val '' (d ⁻¹' Icc σ 1) with hX₂def
  have hD : Fold.Q78.IsContinuum (Subtype.val '' (d ⁻¹' Icc r 1)) :=
    isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc ⟨r, le_rfl, unitInterval.le_one'⟩
  have hzN : (z : M) ∈ N := ⟨hEJ z.2, zF, ⟨(hS₃r zF hzS₃).le, unitInterval.le_one'⟩, rfl⟩
  have hN : Fold.Q78.IsContinuum N := isContinuum_inter_of_HU hHU hJ hD ⟨z, hzN⟩
  have hX₁ : Fold.Q78.IsContinuum X₁ :=
    isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc ⟨0, le_rfl, unitInterval.nonneg'⟩
  have hX₂ : Fold.Q78.IsContinuum X₂ :=
    isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc ⟨σ, le_rfl, unitInterval.le_one'⟩
  -- the layer over `r` lies in `J`
  obtain ⟨wr, hwr⟩ := hd.2.1 r
  have hrJ : layer d r ⊆ J := by
    refine layer_subset_of_meets' hab hd inter_subset_left hJ
      ⟨x₀, hXJ hx₀X, by rw [hdX]; exact hx₀X⟩ ⟨w₁, hw₁, w₁, rfl, rfl⟩ hr0 hrσ
  have hwrJ : (wr : M) ∈ J := hrJ ⟨wr, hwr, rfl⟩
  obtain ⟨v₁, hv₁⟩ := hd.2.1 1
  obtain ⟨v₂, hv₂⟩ := he.2.1 1
  have hT := isTriod_of_core hN hX₁ hX₂ hX₃
    ⟨wr, ⟨wr, ⟨unitInterval.nonneg', hwr.le⟩, rfl⟩, hwrJ, wr, ⟨hwr.ge, unitInterval.le_one'⟩, rfl⟩
    ⟨w₁, ⟨w₁, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, hw₁, w₁, ⟨hrσ.le, unitInterval.le_one'⟩, rfl⟩
    ⟨z, ⟨zH, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, hzN⟩
    (by
      rintro x ⟨⟨w, hw, rfl⟩, ⟨w', hw', hww⟩⟩
      have : w' = w := Subtype.ext hww
      rw [this] at hw'
      exact absurd (hw'.1.trans hw.2) (not_le.2 hrσ))
    (by
      rintro x ⟨⟨w, hw, rfl⟩, hx3⟩
      exact absurd hw.2 (not_le.2 (hS₃r w hx3)))
    (by
      rintro x ⟨⟨w, hw, rfl⟩, hx3⟩
      refine ⟨⟨w.2, img_subset _ hx3⟩, w, ⟨hrσ.le.trans hw.1, hw.2⟩, rfl⟩)
    (fun hsub => by
      have hmem : (⟨x₀, hEF x₀.2⟩ : F) ∈ d ⁻¹' Icc 0 r := by
        obtain ⟨w', hw', hw'e⟩ : (x₀ : M) ∈ layer d 0 := by rw [hdX]; exact hx₀X
        have : (⟨x₀, hEF x₀.2⟩ : F) = w' := Subtype.ext hw'e.symm
        rw [this]
        show d w' ∈ Icc 0 r
        rw [show d w' = 0 from hw']
        exact ⟨le_rfl, hr0.le⟩
      obtain ⟨-, w, hw, hwe⟩ := @hsub (x₀ : M) ⟨⟨x₀, hEF x₀.2⟩, hmem, rfl⟩
      have hw0 : d w = 0 := by
        have hx₀d : (x₀ : M) ∈ layer d 0 := by rw [hdX]; exact hx₀X
        obtain ⟨w', hw', hw'e⟩ := hx₀d
        have : w' = w := Subtype.ext (hw'e.trans hwe.symm)
        rw [← this]; exact hw'
      have hw1 : d w ∈ Icc r 1 := hw
      rw [hw0] at hw1
      exact absurd hw1.1 (not_le.2 hr0))
    (fun hsub => hJV v₁ hv₁ (hsub ⟨v₁, ⟨by rw [hv₁]; exact unitInterval.le_one', unitInterval.le_one'⟩, rfl⟩).1)
    (fun hsub => hJW v₂ hv₂
      (hsub ⟨v₂, ⟨by rw [hv₂]; exact unitInterval.le_one', unitInterval.le_one'⟩, rfl⟩).1)
  exact hAT _ (subset_univ _) hT

/-- **The countable form.** In a second-countable space, a nonempty chain of closed sets with no
largest element has a strictly increasing sequence of members with the same union. -/
theorem exists_strictMono_seq_of_chain {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] {𝓕 : Set (Set Y)} (hch : IsChain (· ⊆ ·) 𝓕)
    (hcl : ∀ F ∈ 𝓕, IsClosed F) (hne : 𝓕.Nonempty) (hnomax : ∀ F ∈ 𝓕, ∃ H ∈ 𝓕, F ⊂ H) :
    ∃ Fs : ℕ → Set Y, StrictMono Fs ∧ (∀ i, Fs i ∈ 𝓕) ∧ ⋃₀ 𝓕 = ⋃ i, Fs i := by
  classical
  obtain ⟨F₀, hF₀⟩ := hne
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Y
  -- one member for each basic set it meets
  have hpick : ∀ B : Set Y, ∃ F ∈ 𝓕, (∃ G ∈ 𝓕, (G ∩ B).Nonempty) → (F ∩ B).Nonempty := by
    intro B
    by_cases h : ∃ G ∈ 𝓕, (G ∩ B).Nonempty
    · obtain ⟨G, hG, hGB⟩ := h
      exact ⟨G, hG, fun _ => hGB⟩
    · exact ⟨F₀, hF₀, fun h' => absurd h' h⟩
  choose pick hpick𝓕 hpickB using hpick
  -- cofinality
  have hcof : ∀ F ∈ 𝓕, ∃ B ∈ b, F ⊆ pick B := by
    intro F hF
    by_contra hcon
    push_neg at hcon
    have hall : ∀ B ∈ b, pick B ⊆ F := fun B hB => by
      rcases hch.total (hpick𝓕 B) hF with h | h
      · exact h
      · exact absurd h (hcon B hB)
    obtain ⟨G, hG, hFG⟩ := hnomax F hF
    obtain ⟨x, hxG, hxF⟩ := not_subset.1 hFG.2
    obtain ⟨B, hB, hxB, hBF⟩ := hb.isOpen_iff.1 (hcl F hF).isOpen_compl x hxF
    obtain ⟨y, hyF, hyB⟩ := hpickB B ⟨G, hG, x, hxG, hxB⟩
    exact hBF hyB (hall B hB hyF)
  -- an enumeration of the chosen members (with `F₀` as a default)
  have hcount : (pick '' b ∪ {F₀}).Countable := (hbc.image _).union (countable_singleton _)
  obtain ⟨f, hf⟩ := hcount.exists_eq_range ⟨F₀, Or.inr rfl⟩
  have hf𝓕 : ∀ n, f n ∈ 𝓕 := by
    intro n
    have : f n ∈ range f := mem_range_self n
    rw [← hf] at this
    rcases this with ⟨B, -, hB⟩ | h
    · rw [← hB]; exact hpick𝓕 B
    · rw [mem_singleton_iff.1 h]; exact hF₀
  -- the larger of two members
  have hmax2 : ∀ F ∈ 𝓕, ∀ G ∈ 𝓕, ∃ H ∈ 𝓕, F ∪ G ⊂ H := by
    intro F hF G hG
    rcases hch.total hF hG with h | h
    · obtain ⟨H, hH, hGH⟩ := hnomax G hG
      exact ⟨H, hH, by rwa [union_eq_right.2 h]⟩
    · obtain ⟨H, hH, hFH⟩ := hnomax F hF
      exact ⟨H, hH, by rwa [union_eq_left.2 h]⟩
  choose! nxt hnxt𝓕 hnxt using hmax2
  let Fs : ℕ → {F // F ∈ 𝓕} := fun n => Nat.rec ⟨f 0, hf𝓕 0⟩
    (fun m G => ⟨nxt G.1 (f (m + 1)), hnxt𝓕 _ G.2 _ (hf𝓕 _)⟩) n
  have hstep : ∀ m, (Fs m).1 ∪ f (m + 1) ⊂ (Fs (m + 1)).1 := fun m =>
    hnxt _ (Fs m).2 _ (hf𝓕 _)
  have hfsub : ∀ m, f m ⊆ (Fs m).1 := by
    intro m
    cases m with
    | zero => exact subset_rfl
    | succ m => exact subset_union_right.trans (hstep m).1
  refine ⟨fun n => (Fs n).1, strictMono_nat_of_lt_succ fun m =>
    lt_of_le_of_lt subset_union_left (hstep m), fun n => (Fs n).2, ?_⟩
  apply subset_antisymm
  · rintro x ⟨F, hF, hxF⟩
    obtain ⟨B, hB, hFB⟩ := hcof F hF
    have : pick B ∈ range f := hf ▸ Or.inl ⟨B, hB, rfl⟩
    obtain ⟨n, hn⟩ := this
    exact mem_iUnion.2 ⟨n, hfsub n (hn ▸ hFB hxF)⟩
  · exact iUnion_subset fun n => subset_sUnion_of_mem (Fs n).2

end Lemma4

end HPC.Hagopian
