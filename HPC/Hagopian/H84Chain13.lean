import HPC.Hagopian.H84Strand

/-!
# Batch 187, §2: Lemma 13, the chain part

Commission 187 §2, the part of `chainLinks84_runsStraight` that needs neither Lemma 3 nor the fold:
Hagopian's "Note that `𝔏` is a normal chain in `M∖A`" (p. 339, unargued; ledger H84.18),
`Cl(L 0 ∪ L 4) ⊆ B`, and conditions (1)–(2) of "runs straight" (with the closure form of the end
condition) for every `δ`-translate of `E`. Every bound holds for all small `δ`, so later steps may
shrink `δ` further.

* `wsetOf_subset_thickening`, `subset_wsetOf`, `isOpen_wsetOf`, `closure_wsetOf_subset`.
* `seg84`: the segments `k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]]`; `seg84_disjoint`.
* `exists_x84`: numbers `x` with `k⁻¹[[0, x₃]] ∪ k⁻¹[[x₁₂, 1]] ⊆ B` (commission 187 §2.4).
* `chainLinks84_chain_aux`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section WsetOf

variable {M : Set Pt}

/-- `W(S, δ)` lies in the `δ`-thickening of `S`. -/
theorem wsetOf_subset_thickening (S : Set M) (δ : ℝ) : WsetOf S δ ⊆ thickening δ S := by
  intro y hy
  simp only [WsetOf, mem_iUnion] at hy
  obtain ⟨v, hv, h, hh, rfl⟩ := hy
  rw [mem_thickening_iff]
  exact ⟨v, hv, by rw [dist_comm]; exact hh v⟩

/-- `S ⊆ W(S, δ)` for `δ > 0`. -/
theorem subset_wsetOf (S : Set M) {δ : ℝ} (hδ : 0 < δ) : S ⊆ WsetOf S δ := fun v hv =>
  mem_iUnion₂.2 ⟨v, hv, Homeomorph.refl M, fun w => by simpa using hδ, rfl⟩

/-- A `δ`-homeomorphism maps `S` into `W(S, δ)`. -/
theorem image_subset_wsetOf (S : Set M) {δ : ℝ} (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ) :
    h '' S ⊆ WsetOf S δ := by
  rintro _ ⟨v, hv, rfl⟩
  exact mem_iUnion₂.2 ⟨v, hv, h, hh, rfl⟩

/-- `W(S, δ)` is open (Lemma 1). -/
theorem isOpen_wsetOf [CompactSpace M] (hX : IsHomogeneous M) (S : Set M) (δ : ℝ) :
    IsOpen (WsetOf S δ) :=
  isOpen_biUnion fun v _ => hagopian84_lemma1 hX v δ

/-- `Cl W(S, δ)` lies in the closed `δ`-thickening of `S`. -/
theorem closure_wsetOf_subset (S : Set M) (δ : ℝ) : closure (WsetOf S δ) ⊆ cthickening δ S :=
  (closure_mono (wsetOf_subset_thickening S δ)).trans (closure_thickening_subset_cthickening δ S)

/-- A `δ`-homeomorphism maps `S` into the `δ`-thickening of `S`. -/
theorem image_subset_thickening (S : Set M) {δ : ℝ} (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < δ) :
    h '' S ⊆ thickening δ S :=
  (image_subset_wsetOf S h hh).trans (wsetOf_subset_thickening S δ)

end WsetOf

section Seg

variable {M : Set Pt}

/-- The segment `k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]]` of the link `L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`. -/
def seg84 {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (i : Fin 5) : Set M :=
  layerSet k (Icc (x ⟨3 * i.val, by have := i.isLt; omega⟩)
    (x ⟨3 * i.val + 3, by have := i.isLt; omega⟩))

theorem chainLinks84_eq {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (δ : ℝ)
    (i : Fin 5) : chainLinks84 k x δ i = WsetOf (seg84 k x i) δ := rfl

theorem isCompact_seg84 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (x : Fin 16 → unitInterval) (i : Fin 5) : IsCompact (seg84 k x i) :=
  isCompact_img hE.isCompact hE.2.1.1 isClosed_Icc

/-- Segments of non-adjacent links are disjoint. -/
theorem seg84_disjoint {E : Set M} (k : E → unitInterval) {x : Fin 16 → unitInterval}
    (hx : StrictMono x) {i j : Fin 5} (hij : (i : ℕ) + 1 < j) :
    Disjoint (seg84 k x i) (seg84 k x j) := by
  rw [disjoint_left]
  rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
  have : w' = w := Subtype.ext hww'
  subst this
  have hlt : x ⟨3 * i.val + 3, by have := i.isLt; omega⟩ <
      x ⟨3 * j.val, by have := j.isLt; omega⟩ :=
    hx (by rw [Fin.mk_lt_mk]; omega)
  exact absurd (hw.2.trans_lt (hlt.trans_le hw'.1)) (lt_irrefl _)

/-- Adjacent segments meet (in `k⁻¹(x₃ᵢ₊₃)`). -/
theorem seg84_meet {E : Set M} {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    {x : Fin 16 → unitInterval} (hx : StrictMono x) (i : Fin 5) (hi : (i : ℕ) < 4) :
    (seg84 k x i ∩ seg84 k x ⟨i + 1, by omega⟩).Nonempty := by
  obtain ⟨w, hw⟩ := hk.2.1 (x ⟨3 * i.val + 3, by have := i.isLt; omega⟩)
  refine ⟨w.1, ⟨w, ?_, rfl⟩, ⟨w, ?_, rfl⟩⟩
  · refine ⟨?_, le_of_eq hw⟩
    rw [hw]
    exact hx.monotone (by rw [Fin.mk_le_mk]; omega)
  · refine ⟨?_, ?_⟩
    · rw [hw]
      exact le_of_eq (congrArg x (Fin.ext (by simp only []; ring)))
    · rw [hw]
      exact hx.monotone (by rw [Fin.mk_le_mk]; simp)

theorem seg84_nonempty {E : Set M} {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    {x : Fin 16 → unitInterval} (hx : StrictMono x) (i : Fin 5) : (seg84 k x i).Nonempty := by
  obtain ⟨w, hw⟩ := hk.2.1 (x ⟨3 * i.val, by have := i.isLt; omega⟩)
  refine ⟨w.1, w, ⟨le_of_eq hw.symm, ?_⟩, rfl⟩
  rw [hw]
  exact hx.monotone (by rw [Fin.mk_le_mk]; omega)

theorem layer_zero_subset_seg84 {E : Set M} (k : E → unitInterval) {x : Fin 16 → unitInterval}
    (hx0 : x 0 = 0) : layer k 0 ⊆ seg84 k x 0 := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · exact (le_of_eq hx0).trans unitInterval.nonneg'
  · have hw' : k w = 0 := hw
    rw [hw']
    exact unitInterval.nonneg'

theorem layer_one_subset_seg84 {E : Set M} (k : E → unitInterval) {x : Fin 16 → unitInterval}
    (hx15 : x 15 = 1) : layer k 1 ⊆ seg84 k x 4 := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · have hw' : k w = 1 := hw
    rw [hw']
    exact unitInterval.le_one'
  · exact unitInterval.le_one'.trans (le_of_eq hx15.symm)

/-- `E` is covered by the segments. -/
theorem mem_some_seg84 {E : Set M} (k : E → unitInterval) {x : Fin 16 → unitInterval}
    (hx0 : x 0 = 0) (hx15 : x 15 = 1) (w : E) : ∃ i, w.1 ∈ seg84 k x i := by
  have h0 : x ⟨0, by omega⟩ = 0 := hx0
  have h15 : x ⟨15, by omega⟩ = 1 := hx15
  by_cases h1 : k w ≤ x 3
  · exact ⟨0, w, ⟨by simp only [Fin.val_zero, mul_zero]; rw [h0]; exact unitInterval.nonneg', h1⟩,
      rfl⟩
  by_cases h2 : k w ≤ x 6
  · exact ⟨1, w, ⟨le_of_lt (not_le.1 h1), h2⟩, rfl⟩
  by_cases h3 : k w ≤ x 9
  · exact ⟨2, w, ⟨le_of_lt (not_le.1 h2), h3⟩, rfl⟩
  by_cases h4 : k w ≤ x 12
  · exact ⟨3, w, ⟨le_of_lt (not_le.1 h3), h4⟩, rfl⟩
  · exact ⟨4, w, ⟨le_of_lt (not_le.1 h4), by
      show k w ≤ x ⟨15, by omega⟩
      rw [h15]; exact unitInterval.le_one'⟩, rfl⟩

end Seg

section Numbers

/-- The numbers `x₀, …, x₁₅` of `exists_x84`, with margin `c`: steps of `c/3` on `[0, c]` and on
`[1 − c, 1]`, of `(1 − 2c)/9` in between. -/
noncomputable def xf84 (c : ℝ) (i : ℕ) : ℝ :=
  if i ≤ 3 then c * i / 3 else if i ≤ 12 then c + (i - 3) * (1 - 2 * c) / 9 else
    1 - c + (i - 12) * c / 3

theorem xf84_strictMono {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) :
    StrictMono (fun i : Fin 16 => xf84 c i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [xf84] <;> norm_num <;> nlinarith

theorem xf84_mem {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 4) (i : Fin 16) :
    xf84 c i ∈ Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [xf84] <;> norm_num <;> constructor <;> nlinarith

theorem xf84_zero (c : ℝ) : xf84 c 0 = 0 := by simp [xf84]

theorem xf84_fifteen (c : ℝ) : xf84 c 15 = 1 := by simp [xf84]; norm_num

theorem xf84_three (c : ℝ) : xf84 c 3 = c := by simp [xf84]

theorem xf84_twelve (c : ℝ) : xf84 c 12 = 1 - c := by simp [xf84]; ring

end Numbers

section Chain

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- A separation radius for two disjoint compact sets. -/
theorem exists_sep_radius {K₁ K₂ : Set M} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (h : Disjoint K₁ K₂) : ∃ r > 0, Disjoint (cthickening r K₁) (cthickening r K₂) := by
  obtain ⟨r, hr, hd⟩ := h.exists_cthickenings h₁ h₂.isClosed
  exact ⟨r, hr, hd⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§2.4, the choice of `x`.** Upper semicontinuity gives `η > 0` with
`k⁻¹[[0, η] ∪ [1 − η, 1]] ⊆ B`; take `x₃ ≤ η` and `x₁₂ ≥ 1 − η`. -/
theorem exists_x84 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {B : Set M}
    (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ x : Fin 16 → unitInterval, StrictMono x ∧ x 0 = 0 ∧ x 15 = 1 ∧
      seg84 k x 0 ∪ seg84 k x 4 ⊆ B := by
  set T : Set unitInterval := {u | Disjoint (layer k u) Bᶜ} with hT
  have hTo : IsOpen T := isOpen_params_disjoint hE hB.isClosed_compl
  have h0T : (0 : unitInterval) ∈ T := by
    show Disjoint _ _
    rw [disjoint_compl_right_iff_subset]
    exact subset_union_left.trans hBE
  have h1T : (1 : unitInterval) ∈ T := by
    show Disjoint _ _
    rw [disjoint_compl_right_iff_subset]
    exact subset_union_right.trans hBE
  obtain ⟨l, hl, hl0⟩ := exists_Ico_subset_of_mem_nhds (hTo.mem_nhds h0T) ⟨1, zero_lt_one⟩
  obtain ⟨l', hl', hl1⟩ := exists_Ioc_subset_of_mem_nhds (hTo.mem_nhds h1T) ⟨0, zero_lt_one⟩
  -- a margin `c`
  set c : ℝ := min (min ((l : ℝ) / 2) ((1 - (l' : ℝ)) / 2)) (1 / 4) with hc
  have hl0' : (0 : ℝ) < l := hl
  have hl1' : (l' : ℝ) < 1 := hl'
  have hc0 : 0 < c := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hc1 : c ≤ 1 / 4 := min_le_right _ _
  have hcl : c < l := by
    have : c ≤ (l : ℝ) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hcl' : c < 1 - l' := by
    have : c ≤ (1 - (l' : ℝ)) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  let x : Fin 16 → unitInterval := fun i => ⟨xf84 c i, xf84_mem hc0 hc1 i⟩
  have hxs : StrictMono x := fun i j hij => xf84_strictMono hc0 hc1 hij
  have hx0 : x 0 = 0 := Subtype.ext (xf84_zero c)
  have hx15 : x 15 = 1 := Subtype.ext (xf84_fifteen c)
  have hx3 : (x 3 : ℝ) = c := xf84_three c
  have hx12 : (x 12 : ℝ) = 1 - c := xf84_twelve c
  refine ⟨x, hxs, hx0, hx15, ?_⟩
  rintro _ (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
  · have hwT : k w ∈ T := by
      refine hl0 ⟨unitInterval.nonneg', ?_⟩
      have : (k w : ℝ) ≤ x 3 := hw.2
      show (k w : ℝ) < l
      linarith
    by_contra hwB
    exact disjoint_left.1 hwT ⟨w, rfl, rfl⟩ hwB
  · have hwT : k w ∈ T := by
      refine hl1 ⟨?_, unitInterval.le_one'⟩
      have : (x 12 : ℝ) ≤ k w := hw.1
      show (l' : ℝ) < k w
      linarith
    by_contra hwB
    exact disjoint_left.1 hwT ⟨w, rfl, rfl⟩ hwB

omit [ConnectedSpace M] in
/-- **§2, the chain part of Lemma 13.** For `x` strictly increasing with `x 0 = 0`, `x 15 = 1` and
`k⁻¹[[0, x₃]] ∪ k⁻¹[[x₁₂, 1]] ⊆ B`, every small enough `δ` makes the links
`L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)` a normal chain in `M ∖ A` with `Cl(L 0 ∪ L 4) ⊆ B`, and every
`δ`-homeomorphism maps `E` into `⋃𝔏`, `k⁻¹(0)` into `L 0 ∖ Cl L 1` and `k⁻¹(1)` into
`L 4 ∖ Cl L 3`. -/
theorem chainLinks84_chain_aux (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {A B : Set M} (hA : IsClosed A) (hAE : Disjoint A E)
    (hB : IsOpen B) {x : Fin 16 → unitInterval} (hx : StrictMono x) (hx0 : x 0 = 0)
    (hx15 : x 15 = 1) (hxB : seg84 k x 0 ∪ seg84 k x 4 ⊆ B) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ →
      IsChain5 (chainLinks84 k x δ) ∧ IsNormal5 (chainLinks84 k x δ) ∧
      (⋃ i, chainLinks84 k x δ i) ⊆ Aᶜ ∧
      closure (chainLinks84 k x δ 0 ∪ chainLinks84 k x δ 4) ⊆ B ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
        h '' E ⊆ ⋃ i, chainLinks84 k x δ i ∧
        h '' layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        h '' layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
  have hk := hE.2.1
  have hEc := hE.isCompact
  -- radii for the non-adjacent pairs
  have hpair : ∀ p : Fin 5 × Fin 5, ∃ r > 0, (p.1 : ℕ) + 1 < p.2 →
      Disjoint (cthickening r (seg84 k x p.1)) (cthickening r (seg84 k x p.2)) := by
    intro p
    by_cases hp : (p.1 : ℕ) + 1 < p.2
    · obtain ⟨r, hr, hd⟩ := exists_sep_radius (isCompact_seg84 hE x p.1) (isCompact_seg84 hE x p.2)
        (seg84_disjoint k hx hp)
      exact ⟨r, hr, fun _ => hd⟩
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  choose r hr hrd using hpair
  -- radii for the end layers
  have hl0c : IsCompact (layer k 0) := isCompact_img hEc hk.1 isClosed_singleton
  have hl1c : IsCompact (layer k 1) := isCompact_img hEc hk.1 isClosed_singleton
  have hd01 : Disjoint (layer k 0) (seg84 k x 1) := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
    have : w' = w := Subtype.ext hww'
    subst this
    have hw0 : k w' = 0 := hw
    have hlt : x 0 < x ⟨3, by omega⟩ := hx (by rw [Fin.lt_def]; simp)
    have h3 : x ⟨3 * (1 : Fin 5).val, by omega⟩ ≤ k w' := hw'.1
    rw [hw0] at h3
    rw [hx0] at hlt
    exact absurd (hlt.trans_le h3) (lt_irrefl _)
  have hd43 : Disjoint (layer k 1) (seg84 k x 3) := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
    have : w' = w := Subtype.ext hww'
    subst this
    have hw1 : k w' = 1 := hw
    have hlt : x ⟨12, by omega⟩ < x 15 := hx (by rw [Fin.lt_def]; simp)
    have h12 : k w' ≤ x ⟨3 * (3 : Fin 5).val + 3, by omega⟩ := hw'.2
    rw [hw1] at h12
    rw [hx15] at hlt
    exact absurd (h12.trans_lt hlt) (lt_irrefl _)
  obtain ⟨r₀, hr₀, hdr₀⟩ := exists_sep_radius hl0c (isCompact_seg84 hE x 1) hd01
  obtain ⟨r₄, hr₄, hdr₄⟩ := exists_sep_radius hl1c (isCompact_seg84 hE x 3) hd43
  -- radius for `A`
  obtain ⟨rA, hrA, hrAs⟩ := hEc.exists_thickening_subset_open hA.isOpen_compl
    (fun v hv hvA => disjoint_left.1 hAE hvA hv)
  -- radius for `B`
  have hS04c : IsCompact (seg84 k x 0 ∪ seg84 k x 4) :=
    (isCompact_seg84 hE x 0).union (isCompact_seg84 hE x 4)
  obtain ⟨rB, hrB, hrBs⟩ := hS04c.exists_thickening_subset_open hB hxB
  -- `δ₀`
  set rP : ℝ := Finset.univ.inf' Finset.univ_nonempty r with hrP
  have hrP0 : 0 < rP := (Finset.lt_inf'_iff _).2 fun p _ => hr p
  have hrPle : ∀ p, rP ≤ r p := fun p => Finset.inf'_le _ (Finset.mem_univ p)
  set δ₀ : ℝ := min (min rP (min r₀ r₄)) (min rA (rB / 2)) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (lt_min hrP0 (lt_min hr₀ hr₄)) (lt_min hrA (by linarith))
  refine ⟨δ₀, hδ₀0, fun δ hδ hδle => ?_⟩
  have hδP : ∀ p, δ ≤ r p := fun p =>
    hδle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (hrPle p)))
  have hδ0 : δ ≤ r₀ := hδle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδ4 : δ ≤ r₄ := hδle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδA : δ ≤ rA := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB : δ ≤ rB / 2 := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- closures of non-adjacent links are disjoint
  have hnorm : IsNormal5 (chainLinks84 k x δ) := by
    intro i j hij
    rw [chainLinks84_eq, chainLinks84_eq]
    exact ((hrd (i, j) hij).mono (cthickening_mono (hδP (i, j)) _)
      (cthickening_mono (hδP (i, j)) _)).mono (closure_wsetOf_subset _ _)
      (closure_wsetOf_subset _ _)
  have hchain : IsChain5 (chainLinks84 k x δ) := by
    refine ⟨fun i => isOpen_wsetOf hX _ δ, fun i j => ⟨fun hne => ?_, fun hij => ?_⟩⟩
    · by_contra hc
      rw [not_and_or, not_le, not_le] at hc
      rcases hc with hc | hc
      · exact not_disjoint_iff_nonempty_inter.2 hne
          (((hnorm j i (by omega)).symm).mono subset_closure subset_closure)
      · exact not_disjoint_iff_nonempty_inter.2 hne
          ((hnorm i j (by omega)).mono subset_closure subset_closure)
    · rcases lt_trichotomy (i : ℕ) j with h | h | h
      · have hj : j = ⟨i + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hj]
        obtain ⟨v, hv1, hv2⟩ := seg84_meet hk hx i (by omega)
        exact ⟨v, subset_wsetOf _ hδ hv1, subset_wsetOf _ hδ hv2⟩
      · have hj : j = i := Fin.ext h.symm
        rw [hj]
        obtain ⟨v, hv⟩ := seg84_nonempty hk hx i
        exact ⟨v, subset_wsetOf _ hδ hv, subset_wsetOf _ hδ hv⟩
      · have hi : i = ⟨j + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hi]
        obtain ⟨v, hv1, hv2⟩ := seg84_meet hk hx j (by omega)
        exact ⟨v, subset_wsetOf _ hδ hv2, subset_wsetOf _ hδ hv1⟩
  refine ⟨hchain, hnorm, ?_, ?_, fun h hh => ⟨?_, ?_, ?_⟩⟩
  · -- `⋃𝔏 ⊆ M ∖ A`
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    rw [chainLinks84_eq] at hi
    refine hrAs (thickening_mono hδA _ ?_)
    refine thickening_subset_of_subset δ ?_ (wsetOf_subset_thickening _ δ hi)
    exact layerSet_subset' k _
  · -- `Cl(L 0 ∪ L 4) ⊆ B`
    rw [closure_union, chainLinks84_eq, chainLinks84_eq]
    refine (union_subset_union (closure_wsetOf_subset _ _) (closure_wsetOf_subset _ _)).trans ?_
    refine (union_subset (cthickening_subset_of_subset δ subset_union_left)
      (cthickening_subset_of_subset δ subset_union_right)).trans ?_
    exact (cthickening_subset_thickening' hrB (by linarith) _).trans hrBs
  · -- `h[E] ⊆ ⋃𝔏`
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨i, hi⟩ := mem_some_seg84 k hx0 hx15 ⟨v, hv⟩
    exact mem_iUnion.2 ⟨i, image_subset_wsetOf _ h hh ⟨v, hi, rfl⟩⟩
  · -- `h[k⁻¹(0)] ⊆ L 0 ∖ Cl L 1`
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨image_subset_wsetOf _ h hh ⟨v, layer_zero_subset_seg84 k hx0 hv, rfl⟩, fun hc => ?_⟩
    have h1 : h v ∈ cthickening δ (layer k 0) :=
      thickening_subset_cthickening δ _ (image_subset_thickening _ h hh ⟨v, hv, rfl⟩)
    rw [chainLinks84_eq] at hc
    exact disjoint_left.1 hdr₀ (cthickening_mono hδ0 _ h1)
      (cthickening_mono hδ0 _ (closure_wsetOf_subset _ _ hc))
  · -- `h[k⁻¹(1)] ⊆ L 4 ∖ Cl L 3`
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨image_subset_wsetOf _ h hh ⟨v, layer_one_subset_seg84 k hx15 hv, rfl⟩,
      fun hc => ?_⟩
    have h1 : h v ∈ cthickening δ (layer k 1) :=
      thickening_subset_cthickening δ _ (image_subset_thickening _ h hh ⟨v, hv, rfl⟩)
    rw [chainLinks84_eq] at hc
    exact disjoint_left.1 hdr₄ (cthickening_mono hδ4 _ h1)
      (cthickening_mono hδ4 _ (closure_wsetOf_subset _ _ hc))

end Chain

end HPC.Hagopian
