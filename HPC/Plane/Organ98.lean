import HPC.Plane.Layers51
import HPC.Plane.OrganZig98
import HPC.Plane.EpsMap98

/-!
# Batch 98: the Cantor organ as a test of Theorem 11

Skeleton of the batch-98 commission (`COMMISSION-batch98.md`), saved as `HPC/Plane/Organ98.lean`
and imported at the end of the root `HPC.lean`.

The Cantor organ `Org.Organ` (batch 97) satisfies `BingS` and has no degenerate element. Bing's
Theorem 11 asserts that every `BingS` space is snake-like. The organ is therefore either a
counterexample to Theorem 11 or a space whose chainability Bing's proof cannot reach.

**Outcome.**
* §1: **the organ is snake-like** (`organ_isSnakeLike`), so it is *not* a counterexample to
  Theorem 11. Proof: the zigzag maps `Org.organZig n` (`HPC/Plane/OrganZig98.lean`) are
  continuous with fibres of diameter `≤ 2 · 2⁻ⁿ`, and a compact connected metric space with such
  `ε`-maps into the line is snake-like (`isSnakeLike_univ_of_epsMap`, `HPC/Plane/EpsMap98.lean`).
* §2: `organ_condA_layer` and `organ_condA_H_or_K` are proved. Condition A holds at `p'` on
  **both** sides (`organ_condA_H`, `organ_condA_K`): at a good layer the neighbouring strands
  accumulate on the whole layer from both sides, so every subcontinuum of a side that leaves the
  layer contains it, and is irreducible from `p'` to its extreme point.
* §3: `organ_layer_terminal` is proved (the good layer is terminal in the whole organ,
  `good_layer_terminal`); the organ's two sides and their union are snake-like
  (`organ_sides_glue`). The general gluing question `isSnakeLike_union_of_terminal` is
  **refuted** (`isSnakeLike_union_of_terminal_refuted`), even with `T` a nondegenerate arc and
  `H ∪ K` a continuum (`two_organs_counterexample`): in `Organ × [0,1]`, the organ and a lifted copy
  of its left half meet exactly in the good layer, which is terminal in both, and their union is a
  triod.

**Shape changes.** `isSnakeLike_union_of_terminal` is commented out (false) and replaced by its
negation over `Type`, `isSnakeLike_union_of_terminal_refuted`. Added: `organ_condA_H`,
`organ_condA_K`, `good_layer_terminal`, `organ_sides_glue`, `two_organs_counterexample` and the
helpers of §0 and §3.
-/

namespace HPC.Plane

open Set Topology Metric Org

/-! ## §0. The good layer -/

theorem goodC_mem : lam goodC ∈ Icc (0 : ℝ) 1 := ⟨lam_nonneg _, lam_le_one _⟩

theorem lft_goodC : lft (lam goodC) = goodC :=
  (eq_lft goodC_mem rfl goodC_good.not_rightEnd).symm

theorem rgt_goodC : rgt (lam goodC) = goodC :=
  (eq_rgt goodC_mem rfl goodC_good.not_leftEnd).symm

/-- The good layer is the single strand of `goodC`. -/
theorem layer_goodC : layer (lam goodC) = strand goodC := by
  rw [layer_eq goodC_mem, lft_goodC, rgt_goodC, union_self]

theorem eq_pt_height {c : Cs} {s : Organ} (hs : s ∈ strand c) : s = pt c (s : ℝ × ℝ).2 := by
  obtain ⟨y, hy, rfl⟩ := hs
  rw [pt_height c hy]

theorem continuous_height : Continuous fun s : Organ => (s : ℝ × ℝ).2 :=
  continuous_snd.comp continuous_subtype_val

/-- On a strand, the top point satisfies condition A (the strand is an arc). -/
theorem condA_strand_top {c : Cs} {W : Set Organ} (hW : W ⊆ strand c)
    (hWc : Fold.Q78.IsContinuum W) (hnt : W.Nontrivial) (hp : pt c 1 ∈ W) :
    ∃ q, q ≠ pt c 1 ∧ IsIrreducibleBetween W (pt c 1) q := by
  set ht : Organ → ℝ := fun s => (s : ℝ × ℝ).2
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp1 : ht (pt c 1) = 1 := pt_height c h1mem
  set A := ht '' W
  have hAc : IsCompact A := hWc.1.image continuous_height
  have h1A : (1 : ℝ) ∈ A := ⟨_, hp, hp1⟩
  have hAle : ∀ s ∈ W, ht s ∈ Icc (0 : ℝ) 1 := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := hW hs
    show (pt c y : ℝ × ℝ).2 ∈ _
    rw [pt_height c hy]; exact hy
  set a := sInf A
  have haA : a ∈ A := hAc.sInf_mem ⟨1, h1A⟩
  have hamin : ∀ x ∈ A, a ≤ x := fun x hx => csInf_le hAc.bddBelow hx
  have ha1 : a < 1 := by
    obtain ⟨u, hu, v, hv, huv⟩ := hnt
    have hne : ht u ≠ ht v := by
      intro h
      apply huv
      rw [eq_pt_height (hW hu), eq_pt_height (hW hv)]
      exact congrArg (pt c) h
    have hu1 := (hAle u hu).2
    have hv1 := (hAle v hv).2
    rcases hu1.lt_or_eq with h | h
    · exact (hamin _ ⟨u, hu, rfl⟩).trans_lt h
    · rcases hv1.lt_or_eq with h' | h'
      · exact (hamin _ ⟨v, hv, rfl⟩).trans_lt h'
      · exact absurd (h.trans h'.symm) hne
  obtain ⟨w, hw, hwa⟩ := haA
  refine ⟨w, fun h => ?_, hWc, hp, hw, fun K hK hKW hpK hwK => ?_⟩
  · have : ht w = ht (pt c 1) := by rw [h]
    rw [hwa, hp1] at this; linarith
  · refine Subset.antisymm hKW fun s hs => ?_
    have hsI : ht s ∈ Icc a 1 := ⟨hamin _ ⟨s, hs, rfl⟩, (hAle s hs).2⟩
    have hKI : Icc a 1 ⊆ ht '' K :=
      (hK.2.isPreconnected.image _ continuous_height.continuousOn).Icc_subset
        ⟨w, hwK, hwa⟩ ⟨_, hpK, hp1⟩
    obtain ⟨k, hk, hks⟩ := hKI hsI
    have : k = s := by
      rw [eq_pt_height (hW (hKW hk)), eq_pt_height (hW hs)]
      exact congrArg (pt c) hks
    exact this ▸ hk

/-- **The good layer is terminal in the organ.** A closed connected set meeting it lies in it or
contains it. -/
theorem good_layer_terminal {L : Set Organ} (hL : IsClosed L) (hLc : IsPreconnected L)
    (hmeet : (L ∩ layer (lam goodC)).Nonempty) :
    L ⊆ layer (lam goodC) ∨ layer (lam goodC) ⊆ L := by
  by_cases hsub : L ⊆ layer (lam goodC)
  · exact Or.inl hsub
  right
  obtain ⟨s, hsL, hs⟩ := not_subset.mp hsub
  obtain ⟨h, hhL, hh⟩ := hmeet
  have hh' : F h = lam goodC := hh
  have hs' : F s ≠ lam goodC := hs
  rw [layer_goodC]
  rcases lt_or_gt_of_ne hs' with hlt | hgt
  · have := strand_lft_subset hL hLc goodC_mem hsL hhL hlt hh'
    rwa [lft_goodC] at this
  · have := strand_rgt_subset hL hLc goodC_mem hsL hhL hgt hh'
    rwa [rgt_goodC] at this

theorem F_pt_goodC_top : F (pt goodC 1) = lam goodC := F_pt _ _

theorem pt_goodC_top_mem_layer : pt goodC 1 ∈ layer (lam goodC) := F_pt_goodC_top

/-! ## §1. Is the organ snake-like? -/

/-- **Decisive question — answered: the organ is snake-like.** For every `n`, the zigzag map
`organZig n` is a continuous real function on the organ whose fibres have diameter at most
`2 · 2⁻ⁿ` (`dist_le_of_organZig_eq`); the `ε`-map criterion `isSnakeLike_univ_of_epsMap` turns
these into `ε`-chains. Hence the organ is not a counterexample to Theorem 11. -/
theorem organ_isSnakeLike : IsSnakeLike (univ : Set Organ) := by
  haveI := organ_connected
  apply isSnakeLike_univ_of_epsMap
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨organZig n, continuous_organZig n, fun x y h =>
    (dist_le_of_organZig_eq n h).trans_lt (by linarith)⟩

/-! ## §2. Bing's nondegenerate branch on the organ -/

/-- In the organ, at a good non-dyadic layer `g' = layer (lam goodC)`: the top point of the
strand satisfies condition A for `M = g'` (the layer is an arc; its end points satisfy A). -/
theorem organ_condA_layer :
    CondA (layer (lam goodC)) (pt goodC 1) := by
  refine ⟨pt_goodC_top_mem_layer, fun W hWM hWc hnt hpW => ?_⟩
  rw [layer_goodC] at hWM
  exact condA_strand_top hWM hWc hnt hpW

/-- Condition A at `p'` for the left side `H = F⁻¹[0, lam goodC]`. -/
theorem organ_condA_H : CondA (F ⁻¹' Icc 0 (lam goodC)) (pt goodC 1) := by
  set t0 := lam goodC
  have hp : F (pt goodC 1) = t0 := F_pt_goodC_top
  refine ⟨⟨by rw [hp]; exact lam_nonneg _, by rw [hp]⟩, fun W hWM hWc hnt hpW => ?_⟩
  by_cases hsub : W ⊆ layer t0
  · rw [layer_goodC] at hsub
    exact condA_strand_top hsub hWc hnt hpW
  obtain ⟨s, hsW, hs⟩ := not_subset.mp hsub
  have hs' : F s < t0 := lt_of_le_of_ne (hWM hsW).2 hs
  obtain ⟨m, hmW, hmin⟩ := hWc.1.exists_isMinOn ⟨s, hsW⟩ continuous_F.continuousOn
  set t1 := F m
  have ht1 : t1 ∈ Icc (0 : ℝ) 1 := F_mem m
  have ht10 : t1 < t0 := lt_of_le_of_lt (hmin hsW) hs'
  set S := {τ ∈ Icc (0 : ℝ) 2 | gam t1 τ ∈ W}
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (hWc.1.isClosed.preimage (continuous_gam ht1))
  have hSne : S.Nonempty := ⟨pos m, (pos_spec m).1, by rw [(pos_spec m).2]; exact hmW⟩
  set τ0 := sInf S
  have hτ0 : τ0 ∈ S := hSc.sInf_mem hSne
  set q := gam t1 τ0
  have hqW : q ∈ W := hτ0.2
  have hFq : F q = t1 := F_gam ht1 τ0
  have hposq : pos q = τ0 := pos_gam ht1 hτ0.1
  have hqmin : ∀ x ∈ W, key q ≤ key x := by
    intro x hx
    rw [key_le_iff]
    rcases (show t1 ≤ F x from hmin hx).lt_or_eq with h | h
    · left; rw [hFq]; exact h
    · right
      refine ⟨by rw [hFq]; exact h, ?_⟩
      rw [hposq]
      refine csInf_le hSc.bddBelow ⟨(pos_spec x).1, ?_⟩
      rw [h, (pos_spec x).2]; exact hx
  refine ⟨q, fun h => ?_, hWc, hpW, hqW, fun L hL hLW hpL hqL => ?_⟩
  · have := congrArg F h; rw [hFq, hp] at this; linarith
  · refine Subset.antisymm hLW fun x hx => ?_
    have hlayer : layer t0 ⊆ L := by
      have := strand_lft_subset hL.1.isClosed hL.2.isPreconnected goodC_mem hqL hpL
        (by rw [hFq]; exact ht10) hp
      rwa [lft_goodC, ← layer_goodC] at this
    rcases ((hWM hx).2).lt_or_eq with h | h
    · refine ordConvex_of_isContinuum hL q hqL _ hpL x (hqmin x hx) ?_
      rw [key_le_iff]; left; rw [hp]; exact h
    · exact hlayer h

/-- Condition A at `p'` for the right side `K = F⁻¹[lam goodC, 1]`. -/
theorem organ_condA_K : CondA (F ⁻¹' Icc (lam goodC) 1) (pt goodC 1) := by
  set t0 := lam goodC
  have hp : F (pt goodC 1) = t0 := F_pt_goodC_top
  refine ⟨⟨by rw [hp], by rw [hp]; exact lam_le_one _⟩, fun W hWM hWc hnt hpW => ?_⟩
  by_cases hsub : W ⊆ layer t0
  · rw [layer_goodC] at hsub
    exact condA_strand_top hsub hWc hnt hpW
  obtain ⟨s, hsW, hs⟩ := not_subset.mp hsub
  have hs' : t0 < F s := lt_of_le_of_ne (hWM hsW).1 (Ne.symm hs)
  obtain ⟨m, hmW, hmax⟩ := hWc.1.exists_isMaxOn ⟨s, hsW⟩ continuous_F.continuousOn
  set t1 := F m
  have ht1 : t1 ∈ Icc (0 : ℝ) 1 := F_mem m
  have ht10 : t0 < t1 := lt_of_lt_of_le hs' (hmax hsW)
  set S := {τ ∈ Icc (0 : ℝ) 2 | gam t1 τ ∈ W}
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (hWc.1.isClosed.preimage (continuous_gam ht1))
  have hSne : S.Nonempty := ⟨pos m, (pos_spec m).1, by rw [(pos_spec m).2]; exact hmW⟩
  set τ0 := sSup S
  have hτ0 : τ0 ∈ S := hSc.sSup_mem hSne
  set q := gam t1 τ0
  have hqW : q ∈ W := hτ0.2
  have hFq : F q = t1 := F_gam ht1 τ0
  have hposq : pos q = τ0 := pos_gam ht1 hτ0.1
  have hqmax : ∀ x ∈ W, key x ≤ key q := by
    intro x hx
    rw [key_le_iff]
    rcases (show F x ≤ t1 from hmax hx).lt_or_eq with h | h
    · left; rw [hFq]; exact h
    · right
      refine ⟨by rw [hFq]; exact h, ?_⟩
      rw [hposq]
      refine le_csSup hSc.bddAbove ⟨(pos_spec x).1, ?_⟩
      rw [← h, (pos_spec x).2]; exact hx
  refine ⟨q, fun h => ?_, hWc, hpW, hqW, fun L hL hLW hpL hqL => ?_⟩
  · have := congrArg F h; rw [hFq, hp] at this; linarith
  · refine Subset.antisymm hLW fun x hx => ?_
    have hlayer : layer t0 ⊆ L := by
      have := strand_rgt_subset hL.1.isClosed hL.2.isPreconnected goodC_mem hqL hpL
        (by rw [hFq]; exact ht10) hp
      rwa [rgt_goodC, ← layer_goodC] at this
    rcases ((hWM hx).1).lt_or_eq with h | h
    · refine ordConvex_of_isContinuum hL _ hpL q hqL x ?_ (hqmax x hx)
      rw [key_le_iff]; left; rw [hp]; exact h
    · exact hlayer h.symm

/-- **Bing's claim \"`p'` satisfies condition A for `M` equal to either `H` or `K`\"**, tested on the
organ at the good layer with `p'` the top point: `H = F⁻¹[0, lam goodC]`, `K = F⁻¹[lam goodC, 1]`.
Both sides satisfy it (`organ_condA_H`, `organ_condA_K`). -/
theorem organ_condA_H_or_K :
    CondA (F ⁻¹' Icc 0 (lam goodC)) (pt goodC 1) ∨ CondA (F ⁻¹' Icc (lam goodC) 1) (pt goodC 1) :=
  Or.inl organ_condA_H

/-! ## §3. What gluing along a nondegenerate layer requires -/

/-- **Terminal subcontinuum.** `T ⊆ M` is terminal in `M` when every subcontinuum of `M` meeting
`T` lies in `T` or contains `T`. -/
def IsTerminalIn (M T : Set Organ) : Prop :=
  ∀ L : Set Organ, Fold.Q78.IsContinuum L → L ⊆ M → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L

/-- The good layer is terminal in both sides. -/
theorem organ_layer_terminal :
    IsTerminalIn (F ⁻¹' Icc 0 (lam goodC)) (layer (lam goodC)) ∧
    IsTerminalIn (F ⁻¹' Icc (lam goodC) 1) (layer (lam goodC)) :=
  ⟨fun _ hL _ hmeet => good_layer_terminal hL.1.isClosed hL.2.isPreconnected hmeet,
    fun _ hL _ hmeet => good_layer_terminal hL.1.isClosed hL.2.isPreconnected hmeet⟩

/-- **The organ instance of the gluing question.** The two sides of the good layer are snake-like,
meet exactly in the good layer, and their union (the organ) is snake-like. (In general the gluing
fails: `two_organs_counterexample`.) -/
theorem organ_sides_glue :
    IsSnakeLike (F ⁻¹' Icc 0 (lam goodC)) ∧ IsSnakeLike (F ⁻¹' Icc (lam goodC) 1) ∧
    F ⁻¹' Icc 0 (lam goodC) ∩ F ⁻¹' Icc (lam goodC) 1 = layer (lam goodC) ∧
    IsSnakeLike (F ⁻¹' Icc 0 (lam goodC) ∪ F ⁻¹' Icc (lam goodC) 1) := by
  have hp : F (pt goodC 1) = lam goodC := F_pt_goodC_top
  have hH : Fold.Q78.IsContinuum (F ⁻¹' Icc 0 (lam goodC)) :=
    isContinuum_preimage_Icc (s := pt goodC 1) ⟨by rw [hp]; exact lam_nonneg _, by rw [hp]⟩
  have hK : Fold.Q78.IsContinuum (F ⁻¹' Icc (lam goodC) 1) :=
    isContinuum_preimage_Icc (s := pt goodC 1) ⟨by rw [hp], by rw [hp]; exact lam_le_one _⟩
  have hU : F ⁻¹' Icc 0 (lam goodC) ∪ F ⁻¹' Icc (lam goodC) 1 = univ := by
    ext s
    simp only [mem_union, mem_preimage, mem_Icc, mem_univ, iff_true]
    have := F_mem s
    rcases le_total (F s) (lam goodC) with h | h
    · exact Or.inl ⟨this.1, h⟩
    · exact Or.inr ⟨h, this.2⟩
  refine ⟨isSnakeLike_of_subcontinuum organ_isSnakeLike hH (subset_univ _),
    isSnakeLike_of_subcontinuum organ_isSnakeLike hK (subset_univ _), ?_, ?_⟩
  · ext s
    simp only [mem_inter_iff, mem_preimage, mem_Icc, layer, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, h1⟩, h2, -⟩; exact le_antisymm h1 h2
    · intro h; have := F_mem s; refine ⟨⟨this.1, h.le⟩, h.ge, this.2⟩
  · rw [hU]; exact organ_isSnakeLike

-- Commented-out statement `isSnakeLike_union_of_terminal` removed in batch 103; see `LEDGER.md`.

/-! ### The two-organ counterexample

In `Organ × [0,1]`: `H₂` is the organ at level `0`; `K₂` is the left half `F⁻¹[0, t₀]` of the
organ lifted by the height `t₀ - F` (`t₀ = lam goodC`), a homeomorphic copy meeting `H₂` exactly
in the good layer `T₂` (at level `0`). Both are snake-like and `T₂` is terminal in both, but
`H₂ ∪ K₂ \ T₂` falls into three mutually separated pieces (left of `T₂` in `H₂`, right of `T₂` in
`H₂`, and `K₂ \ T₂`), so `H₂ ∪ K₂` is a triod and is not snake-like. -/

/-- The ambient compact space. -/
abbrev Organ2 := Organ × Icc (0 : ℝ) 1

/-- `H₂`: the organ at level `0`. -/
def H2 : Set Organ2 := {q | (q.2 : ℝ) = 0}

/-- `K₂`: the left half of the organ, lifted by `lam goodC - F`. -/
def K2 : Set Organ2 := {q | F q.1 ≤ lam goodC ∧ (q.2 : ℝ) = lam goodC - F q.1}

/-- `T₂`: the good layer at level `0`. -/
def T2 : Set Organ2 := {q | F q.1 = lam goodC ∧ (q.2 : ℝ) = 0}

theorem continuous_lev : Continuous fun q : Organ2 => (q.2 : ℝ) :=
  continuous_subtype_val.comp continuous_snd

theorem continuous_F1 : Continuous fun q : Organ2 => F q.1 := continuous_F.comp continuous_fst

theorem H2_inter_K2 : H2 ∩ K2 = T2 := by
  ext q
  simp only [H2, K2, T2, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h0, -, h⟩; exact ⟨by linarith, h0⟩
  · rintro ⟨hF, h0⟩; exact ⟨h0, hF.le, by rw [h0, hF]; ring⟩

/-- Level `0`. -/
noncomputable def emb0 (s : Organ) : Organ2 := (s, ⟨0, le_rfl, zero_le_one⟩)

theorem continuous_emb0 : Continuous emb0 := continuous_id.prodMk continuous_const

/-- The lift. -/
noncomputable def embK (s : Organ) : Organ2 := (s, projIcc 0 1 zero_le_one (lam goodC - F s))

theorem continuous_embK : Continuous embK :=
  continuous_id.prodMk (continuous_projIcc.comp (continuous_const.sub continuous_F))

theorem H2_eq : H2 = range emb0 := by
  ext q
  constructor
  · intro h; exact ⟨q.1, Prod.ext rfl (Subtype.ext h.symm)⟩
  · rintro ⟨s, rfl⟩; rfl

theorem K2_eq : K2 = embK '' (F ⁻¹' Icc 0 (lam goodC)) := by
  ext q
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨q.1, ⟨(F_mem _).1, hle⟩, Prod.ext rfl (Subtype.ext ?_)⟩
    simp only [embK]
    rw [projIcc_of_mem _ ⟨by linarith, by linarith [(F_mem q.1).1, lam_le_one goodC]⟩, heq]
  · rintro ⟨s, hs, rfl⟩
    have hv : ((projIcc 0 1 zero_le_one (lam goodC - F s) : Icc (0 : ℝ) 1) : ℝ) =
        lam goodC - F s := by
      rw [projIcc_of_mem _ ⟨by linarith [hs.2], by linarith [hs.1, lam_le_one goodC]⟩]
    exact ⟨hs.2, hv⟩

theorem T2_eq : T2 = emb0 '' layer (lam goodC) := by
  ext q
  constructor
  · rintro ⟨hF, h0⟩; exact ⟨q.1, hF, Prod.ext rfl (Subtype.ext h0.symm)⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨hs, rfl⟩

theorem isContinuum_H2 : Fold.Q78.IsContinuum H2 := by
  haveI := organ_connected
  rw [H2_eq]
  exact ⟨isCompact_range continuous_emb0, isConnected_range continuous_emb0⟩

theorem isContinuum_left_half : Fold.Q78.IsContinuum (F ⁻¹' Icc 0 (lam goodC)) :=
  isContinuum_preimage_Icc (s := pt goodC 1)
    ⟨by rw [F_pt_goodC_top]; exact lam_nonneg _, by rw [F_pt_goodC_top]⟩

theorem isContinuum_K2 : Fold.Q78.IsContinuum K2 := by
  rw [K2_eq]
  exact ⟨isContinuum_left_half.1.image continuous_embK,
    isContinuum_left_half.2.image _ continuous_embK.continuousOn⟩

theorem isContinuum_T2 : Fold.Q78.IsContinuum T2 := by
  rw [T2_eq]
  have hc : Fold.Q78.IsContinuum (layer (lam goodC)) :=
    ⟨(isClosed_layer _).isCompact, layer_nonempty goodC_mem, isPreconnected_layer goodC_mem⟩
  exact ⟨hc.1.image continuous_emb0, hc.2.image _ continuous_emb0.continuousOn⟩

/-- `T₂` is a nondegenerate arc. -/
theorem T2_nontrivial : T2.Nontrivial := by
  refine ⟨emb0 (pt goodC 0), ⟨F_pt _ _, rfl⟩, emb0 (pt goodC 1), ⟨F_pt _ _, rfl⟩, fun h => ?_⟩
  exact pt_zero_ne_one goodC (congrArg Prod.fst h)

theorem dist_organ2 (x y : Organ2) : dist x y = max (dist x.1 y.1) |(x.2 : ℝ) - y.2| := by
  rw [Prod.dist_eq, Subtype.dist_eq x.2 y.2, Real.dist_eq]

theorem exists_n_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, 2 * (1 / 2 : ℝ) ^ n < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨n, by linarith⟩

theorem isSnakeLike_H2 : IsSnakeLike H2 := by
  apply isSnakeLike_of_epsMap isContinuum_H2
  intro ε hε
  obtain ⟨n, hn⟩ := exists_n_lt hε
  refine ⟨fun q => organZig n q.1, (continuous_organZig n).comp continuous_fst,
    fun x hx y hy h => ?_⟩
  have hx0 : (x.2 : ℝ) = 0 := hx
  have hy0 : (y.2 : ℝ) = 0 := hy
  rw [dist_organ2, hx0, hy0, sub_self, abs_zero]
  exact lt_of_le_of_lt (max_le (dist_le_of_organZig_eq n h) (by positivity)) hn

theorem isSnakeLike_K2 : IsSnakeLike K2 := by
  apply isSnakeLike_of_epsMap isContinuum_K2
  intro ε hε
  obtain ⟨η, hη, hF⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_F) ε hε
  obtain ⟨n, hn⟩ := exists_n_lt (lt_min hε hη)
  refine ⟨fun q => organZig n q.1, (continuous_organZig n).comp continuous_fst,
    fun x hx y hy h => ?_⟩
  have hd := lt_of_le_of_lt (dist_le_of_organZig_eq n h) hn
  have hd1 : dist x.1 y.1 < ε := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 := hF (lt_of_lt_of_le hd (min_le_right _ _))
  rw [Real.dist_eq] at hd2
  rw [dist_organ2, hx.2, hy.2]
  refine max_lt hd1 ?_
  rw [show lam goodC - F x.1 - (lam goodC - F y.1) = -(F x.1 - F y.1) by ring, abs_neg]
  exact hd2

/-- Terminality for sets on which a point is determined by its first coordinate. -/
theorem terminal_of_graph {G : Set Organ2} (hT : T2 ⊆ G)
    (hTG : ∀ q ∈ G, F q.1 = lam goodC → q ∈ T2)
    (hinj : ∀ q ∈ G, ∀ q' ∈ G, q.1 = q'.1 → q = q') :
    ∀ L : Set Organ2, Fold.Q78.IsContinuum L → L ⊆ G → (L ∩ T2).Nonempty → L ⊆ T2 ∨ T2 ⊆ L := by
  intro L hL hLG hmeet
  have hc : Continuous (Prod.fst : Organ2 → Organ) := continuous_fst
  have hL1c : IsCompact (Prod.fst '' L) := hL.1.image hc
  have hL1p : IsPreconnected (Prod.fst '' L) := hL.2.isPreconnected.image _ hc.continuousOn
  obtain ⟨q, hqL, hqT⟩ := hmeet
  rcases good_layer_terminal hL1c.isClosed hL1p ⟨q.1, ⟨q, hqL, rfl⟩, hqT.1⟩ with h | h
  · left
    intro x hx
    exact hTG x (hLG hx) (h ⟨x, hx, rfl⟩)
  · right
    intro x hx
    obtain ⟨y, hyL, hyx⟩ := h (show x.1 ∈ layer (lam goodC) from hx.1)
    rw [hinj y (hLG hyL) x (hT hx) hyx] at hyL
    exact hyL

theorem terminal_H2 :
    ∀ L : Set Organ2, Fold.Q78.IsContinuum L → L ⊆ H2 → (L ∩ T2).Nonempty → L ⊆ T2 ∨ T2 ⊆ L :=
  terminal_of_graph (fun _ hq => hq.2) (fun _ hq hF => ⟨hF, hq⟩)
    (fun q hq q' hq' h => Prod.ext h (Subtype.ext ((show (q.2 : ℝ) = 0 from hq).trans
      (show (q'.2 : ℝ) = 0 from hq').symm)))

theorem terminal_K2 :
    ∀ L : Set Organ2, Fold.Q78.IsContinuum L → L ⊆ K2 → (L ∩ T2).Nonempty → L ⊆ T2 ∨ T2 ⊆ L :=
  terminal_of_graph (fun q hq => ⟨hq.1.le, by rw [hq.2, hq.1]; ring⟩)
    (fun q hq hF => ⟨hF, by rw [hq.2, hF]; ring⟩)
    (fun q hq q' hq' h => Prod.ext h (Subtype.ext (by rw [hq.2, hq'.2, h])))

/-- **Two organs glued along the good layer form a triod.** -/
theorem two_organs_isTriod : IsTriod (H2 ∪ K2) := by
  set t0 := lam goodC
  have hM : Fold.Q78.IsContinuum (H2 ∪ K2) :=
    ⟨isContinuum_H2.1.union isContinuum_K2.1,
      IsConnected.union (by rw [H2_inter_K2]; exact isContinuum_T2.2.nonempty)
        isContinuum_H2.2 isContinuum_K2.2⟩
  obtain ⟨s0, hs0⟩ := F_surj (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  obtain ⟨s1, hs1⟩ := F_surj (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  have ht0 : 0 < t0 := lam_goodC_pos
  have ht1 : t0 < 1 := lam_goodC_lt_one
  have hA0 : F s0 < t0 := by rw [hs0]; exact ht0
  have hB1 : t0 < F s1 := by rw [hs1]; exact ht1
  have hTM : T2 ⊆ H2 ∪ K2 := by
    rw [← H2_inter_K2]; exact inter_subset_left.trans subset_union_left
  refine ⟨hM, T2, isContinuum_T2, hTM, {q | (q.2 : ℝ) = 0 ∧ F q.1 < t0}, {q | (q.2 : ℝ) = 0 ∧ t0 < F q.1},
    {q | F q.1 < t0 ∧ (q.2 : ℝ) = t0 - F q.1}, ⟨emb0 s0, rfl, hA0⟩,
    ⟨emb0 s1, rfl, hB1⟩, ⟨embK s0, ?_⟩, ?_, ?_⟩
  · have hv : ((projIcc 0 1 zero_le_one (t0 - F s0) : Icc (0 : ℝ) 1) : ℝ) = t0 - F s0 := by
      rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
    exact ⟨hA0, hv⟩
  · ext q
    simp only [mem_diff, mem_union, H2, K2, T2, mem_setOf_eq, not_and]
    constructor
    · rintro ⟨h | ⟨hle, heq⟩, hnT⟩
      · rcases lt_trichotomy (F q.1) t0 with hlt | heq' | hgt
        · exact Or.inl (Or.inl ⟨h, hlt⟩)
        · exact absurd h (hnT heq')
        · exact Or.inl (Or.inr ⟨h, hgt⟩)
      · rcases hle.lt_or_eq with hlt | heq'
        · exact Or.inr ⟨hlt, heq⟩
        · exact absurd (by rw [heq, heq']; ring) (hnT heq')
    · rintro ((⟨h0, hlt⟩ | ⟨h0, hgt⟩) | ⟨hlt, heq⟩)
      · exact ⟨Or.inl h0, fun h => absurd h hlt.ne⟩
      · exact ⟨Or.inl h0, fun h => absurd h hgt.ne'⟩
      · exact ⟨Or.inr ⟨hlt.le, heq⟩, fun h => absurd h hlt.ne⟩
  · -- the six separation conditions, via closed supersets of the closures
    have cA : closure {q : Organ2 | (q.2 : ℝ) = 0 ∧ F q.1 < t0} ⊆
        {q | (q.2 : ℝ) = 0 ∧ F q.1 ≤ t0} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.le⟩)
        ((isClosed_eq continuous_lev continuous_const).inter
          (isClosed_le continuous_F1 continuous_const))
    have cB : closure {q : Organ2 | (q.2 : ℝ) = 0 ∧ t0 < F q.1} ⊆
        {q | (q.2 : ℝ) = 0 ∧ t0 ≤ F q.1} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.le⟩)
        ((isClosed_eq continuous_lev continuous_const).inter
          (isClosed_le continuous_const continuous_F1))
    have cC : closure {q : Organ2 | F q.1 < t0 ∧ (q.2 : ℝ) = t0 - F q.1} ⊆
        {q | F q.1 ≤ t0 ∧ (q.2 : ℝ) = t0 - F q.1} :=
      closure_minimal (fun q hq => ⟨hq.1.le, hq.2⟩)
        ((isClosed_le continuous_F1 continuous_const).inter
          (isClosed_eq continuous_lev (continuous_const.sub continuous_F1)))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Set.disjoint_left]
    · intro q hq hq'; have := cA hq; linarith [this.2, hq'.2]
    · intro q hq hq'; have := cB hq'; linarith [this.2, hq.2]
    · intro q hq hq'; have := cA hq; linarith [this.1, hq'.1, hq'.2]
    · intro q hq hq'; have := cC hq'; linarith [this.1, this.2, hq.1, hq.2]
    · intro q hq hq'; have := cB hq; linarith [this.2, hq'.1]
    · intro q hq hq'; have := cC hq'; linarith [this.1, hq.2]

/-- **The two-organ counterexample to the gluing question.** In the compact metric space
`Organ × [0,1]`: `H₂`, `K₂` are snake-like continua, `H₂ ∩ K₂ = T₂` is a nondegenerate arc (the good
layer) terminal in both, `H₂ ∪ K₂` is a continuum, and `H₂ ∪ K₂` is **not** snake-like. -/
theorem two_organs_counterexample :
    IsSnakeLike H2 ∧ IsSnakeLike K2 ∧ H2 ∩ K2 = T2 ∧ T2.Nontrivial ∧
    (∀ L : Set Organ2, Fold.Q78.IsContinuum L → L ⊆ H2 → (L ∩ T2).Nonempty → L ⊆ T2 ∨ T2 ⊆ L) ∧
    (∀ L : Set Organ2, Fold.Q78.IsContinuum L → L ⊆ K2 → (L ∩ T2).Nonempty → L ⊆ T2 ∨ T2 ⊆ L) ∧
    Fold.Q78.IsContinuum (H2 ∪ K2) ∧ ¬ IsSnakeLike (H2 ∪ K2) :=
  ⟨isSnakeLike_H2, isSnakeLike_K2, H2_inter_K2, T2_nontrivial, terminal_H2, terminal_K2,
    two_organs_isTriod.1, fun h => not_isTriod_of_isSnakeLike h two_organs_isTriod⟩

/-- **The gluing question, refuted** (the skeleton's `isSnakeLike_union_of_terminal`, negated over
`Type`). -/
theorem isSnakeLike_union_of_terminal_refuted :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] (H K T : Set X), IsSnakeLike H →
      IsSnakeLike K → H ∩ K = T →
      (∀ L : Set X, Fold.Q78.IsContinuum L → L ⊆ H → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L) →
      (∀ L : Set X, Fold.Q78.IsContinuum L → L ⊆ K → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L) →
      T.Nonempty → IsSnakeLike (H ∪ K) := by
  intro h
  obtain ⟨hH, hK, hHK, hTnt, hTH, hTK, -, hnot⟩ := two_organs_counterexample
  exact hnot (h Organ2 H2 K2 T2 hH hK hHK hTH hTK hTnt.nonempty)

/-! ### The degenerate case: a simple triod

With `T` a single point the gluing question fails trivially: in the square `[-1,1]²`, the
horizontal diameter `Hs` and the upper vertical radius `Ks` are arcs (snake-like) meeting in the
origin, a point is terminal in anything, and `Hs ∪ Ks` is a simple triod. -/

/-- The square `[-1,1]²`. -/
abbrev Sq := Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1

/-- The horizontal diameter. -/
def Hs : Set Sq := {q | (q.2 : ℝ) = 0}

/-- The upper vertical radius. -/
def Ks : Set Sq := {q | (q.1 : ℝ) = 0 ∧ 0 ≤ (q.2 : ℝ)}

/-- The origin. -/
def Ts : Set Sq := {q | (q.1 : ℝ) = 0 ∧ (q.2 : ℝ) = 0}

theorem continuous_sqx : Continuous fun q : Sq => (q.1 : ℝ) :=
  continuous_subtype_val.comp continuous_fst

theorem continuous_sqy : Continuous fun q : Sq => (q.2 : ℝ) :=
  continuous_subtype_val.comp continuous_snd

/-- The zero of `[-1,1]`. -/
def sq0 : Icc (-1 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩

theorem Hs_inter_Ks : Hs ∩ Ks = Ts := by
  ext q
  simp only [Hs, Ks, Ts, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1, -⟩; exact ⟨h1, h0⟩
  · rintro ⟨h1, h0⟩; exact ⟨h0, h1, h0.ge⟩

theorem Ts_nonempty : Ts.Nonempty := ⟨(sq0, sq0), rfl, rfl⟩

theorem isContinuum_Hs : Fold.Q78.IsContinuum Hs := by
  let e : ℝ → Sq := fun t => (projIcc (-1) 1 (by norm_num) t, sq0)
  have he : Continuous e := continuous_projIcc.prodMk continuous_const
  have heq : Hs = e '' Icc (-1) 1 := by
    ext q
    constructor
    · intro h
      refine ⟨q.1, q.1.2, Prod.ext ?_ (Subtype.ext h.symm)⟩
      simp only [e, projIcc_val]
    · rintro ⟨t, -, rfl⟩; rfl
  rw [heq]
  exact ⟨isCompact_Icc.image he, (isConnected_Icc (by norm_num)).image _ he.continuousOn⟩

theorem isContinuum_Ks : Fold.Q78.IsContinuum Ks := by
  let e : ℝ → Sq := fun t => (sq0, projIcc (-1) 1 (by norm_num) t)
  have he : Continuous e := continuous_const.prodMk continuous_projIcc
  have heq : Ks = e '' Icc 0 1 := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨q.2, ⟨h2, q.2.2.2⟩, Prod.ext (Subtype.ext h1.symm) ?_⟩
      simp only [e, projIcc_val]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨rfl, ?_⟩
      simp only [e]
      rw [projIcc_of_mem _ ⟨by linarith [ht.1], ht.2⟩]
      exact ht.1
  rw [heq]
  exact ⟨isCompact_Icc.image he, (isConnected_Icc (by norm_num)).image _ he.continuousOn⟩

theorem isSnakeLike_Hs : IsSnakeLike Hs := by
  refine isSnakeLike_of_epsMap isContinuum_Hs fun ε hε => ⟨_, continuous_sqx, ?_⟩
  intro x hx y hy h
  have : x = y := Prod.ext (Subtype.ext h)
    (Subtype.ext ((show (x.2 : ℝ) = 0 from hx).trans (show (y.2 : ℝ) = 0 from hy).symm))
  rw [this, dist_self]; exact hε

theorem isSnakeLike_Ks : IsSnakeLike Ks := by
  refine isSnakeLike_of_epsMap isContinuum_Ks fun ε hε => ⟨_, continuous_sqy, ?_⟩
  intro x hx y hy h
  have : x = y := Prod.ext (Subtype.ext (hx.1.trans hy.1.symm)) (Subtype.ext h)
  rw [this, dist_self]; exact hε

/-- A one-point set is terminal in anything. -/
theorem terminal_Ts (M : Set Sq) :
    ∀ L : Set Sq, Fold.Q78.IsContinuum L → L ⊆ M → (L ∩ Ts).Nonempty → L ⊆ Ts ∨ Ts ⊆ L := by
  rintro L - - ⟨q, hqL, hqT⟩
  right
  intro p hp
  have : p = q := Prod.ext (Subtype.ext (hp.1.trans hqT.1.symm))
    (Subtype.ext (hp.2.trans hqT.2.symm))
  rw [this]; exact hqL

/-- **Two arcs through a point form a triod.** -/
theorem arcs_isTriod : IsTriod (Hs ∪ Ks) := by
  have hM : Fold.Q78.IsContinuum (Hs ∪ Ks) :=
    ⟨isContinuum_Hs.1.union isContinuum_Ks.1,
      IsConnected.union (by rw [Hs_inter_Ks]; exact Ts_nonempty)
        isContinuum_Hs.2 isContinuum_Ks.2⟩
  have hT : Fold.Q78.IsContinuum Ts := by
    have : Ts = {(sq0, sq0)} := by
      ext q
      simp only [Ts, mem_setOf_eq, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
      · rintro rfl; exact ⟨rfl, rfl⟩
    rw [this]; exact ⟨isCompact_singleton, isConnected_singleton⟩
  have hTM : Ts ⊆ Hs ∪ Ks := by
    rw [← Hs_inter_Ks]; exact inter_subset_left.trans subset_union_left
  let m1 : Icc (-1 : ℝ) 1 := ⟨-1, le_rfl, by norm_num⟩
  let p1 : Icc (-1 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩
  refine ⟨hM, Ts, hT, hTM, {q | (q.2 : ℝ) = 0 ∧ (q.1 : ℝ) < 0},
    {q | (q.2 : ℝ) = 0 ∧ 0 < (q.1 : ℝ)}, {q | (q.1 : ℝ) = 0 ∧ 0 < (q.2 : ℝ)},
    ⟨(m1, sq0), rfl, show (-1 : ℝ) < 0 by norm_num⟩,
    ⟨(p1, sq0), rfl, show (0 : ℝ) < 1 by norm_num⟩,
    ⟨(sq0, p1), rfl, show (0 : ℝ) < 1 by norm_num⟩, ?_, ?_⟩
  · ext q
    simp only [mem_diff, mem_union, Hs, Ks, Ts, mem_setOf_eq, not_and]
    constructor
    · rintro ⟨h | ⟨h1, h2⟩, hnT⟩
      · rcases lt_trichotomy (q.1 : ℝ) 0 with hlt | heq | hgt
        · exact Or.inl (Or.inl ⟨h, hlt⟩)
        · exact absurd h (hnT heq)
        · exact Or.inl (Or.inr ⟨h, hgt⟩)
      · rcases h2.lt_or_eq with hlt | heq
        · exact Or.inr ⟨h1, hlt⟩
        · exact absurd heq.symm (hnT h1)
    · rintro ((⟨h0, hlt⟩ | ⟨h0, hgt⟩) | ⟨h1, hgt⟩)
      · exact ⟨Or.inl h0, fun h => absurd h hlt.ne⟩
      · exact ⟨Or.inl h0, fun h => absurd h hgt.ne'⟩
      · exact ⟨Or.inr ⟨h1, hgt.le⟩, fun _ h => absurd h hgt.ne'⟩
  · have cA : closure {q : Sq | (q.2 : ℝ) = 0 ∧ (q.1 : ℝ) < 0} ⊆
        {q | (q.2 : ℝ) = 0 ∧ (q.1 : ℝ) ≤ 0} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.le⟩)
        ((isClosed_eq continuous_sqy continuous_const).inter
          (isClosed_le continuous_sqx continuous_const))
    have cB : closure {q : Sq | (q.2 : ℝ) = 0 ∧ 0 < (q.1 : ℝ)} ⊆
        {q | (q.2 : ℝ) = 0 ∧ 0 ≤ (q.1 : ℝ)} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.le⟩)
        ((isClosed_eq continuous_sqy continuous_const).inter
          (isClosed_le continuous_const continuous_sqx))
    have cC : closure {q : Sq | (q.1 : ℝ) = 0 ∧ 0 < (q.2 : ℝ)} ⊆
        {q | (q.1 : ℝ) = 0 ∧ 0 ≤ (q.2 : ℝ)} :=
      closure_minimal (fun q hq => ⟨hq.1, hq.2.le⟩)
        ((isClosed_eq continuous_sqx continuous_const).inter
          (isClosed_le continuous_const continuous_sqy))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Set.disjoint_left]
    · intro q hq hq'; have := cA hq; linarith [this.2, hq'.2]
    · intro q hq hq'; have := cB hq'; linarith [this.2, hq.2]
    · intro q hq hq'; have := cA hq; linarith [this.1, hq'.2]
    · intro q hq hq'; have := cC hq'; linarith [this.1, hq.2]
    · intro q hq hq'; have := cB hq; linarith [this.1, hq'.2]
    · intro q hq hq'; have := cC hq'; linarith [this.1, hq.2]

/-- **The degenerate counterexample.** Two snake-like arcs in `[-1,1]²` meeting in one point
(terminal in both), whose union is a continuum that is not snake-like. -/
theorem arcs_counterexample :
    IsSnakeLike Hs ∧ IsSnakeLike Ks ∧ Hs ∩ Ks = Ts ∧ Ts.Nonempty ∧
    (∀ L : Set Sq, Fold.Q78.IsContinuum L → L ⊆ Hs → (L ∩ Ts).Nonempty → L ⊆ Ts ∨ Ts ⊆ L) ∧
    (∀ L : Set Sq, Fold.Q78.IsContinuum L → L ⊆ Ks → (L ∩ Ts).Nonempty → L ⊆ Ts ∨ Ts ⊆ L) ∧
    Fold.Q78.IsContinuum (Hs ∪ Ks) ∧ ¬ IsSnakeLike (Hs ∪ Ks) :=
  ⟨isSnakeLike_Hs, isSnakeLike_Ks, Hs_inter_Ks, Ts_nonempty, terminal_Ts Hs, terminal_Ts Ks,
    arcs_isTriod.1, fun h => not_isTriod_of_isSnakeLike h arcs_isTriod⟩

end HPC.Plane
