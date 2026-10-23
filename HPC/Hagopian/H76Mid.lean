import HPC.Hagopian.H76Cond4

/-!
# Batch 181, §3.1: the middle set `Mid` and the two bounds on `ε₃`

Commission 181 §3.1. `Mid` (`midSet`) is the set of points of `M ∩ π⁻¹[D]` over abscissae in
`[1/2 − 2/n, 1/2 + 2/n]`. Both bounds depend only on data chosen before `ε₃` (the collar, `D`,
the strip, `n`), so they can be imposed on `ε₃` in `exists_thm1Setup`.

* `exists_eps_mid_sides` (field `hε₃S`): some `δ > 0` bounds the distance from `Mid` to the
  preimage `π⁻¹F[{3/22, 19/22} × [0, c₁]]` of the closed side segments (two disjoint compacta).
* `exists_eps_mid_O` (field `hε₃O`): some `δ > 0` such that every point of `M − E` within `δ` of a
  point of `Mid` lies in `π⁻¹[D]`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **`Mid`** (commission 181 §3.1): the points of `M ∩ π⁻¹[D]` over abscissae in
`[1/2 − 2/n, 1/2 + 2/n]`. -/
def midSet (M : Set Pt) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (n : ℕ) : Set Pt :=
  {a | a ∈ M ∧ ∃ q ∈ D', π a = F q ∧ q.1 ∈ Icc (1 / 2 - 2 / (n : ℝ)) (1 / 2 + 2 / (n : ℝ))}

section Mid

variable {M : Set Pt} [CompactSpace M]

theorem two_div_le_of_forty {n : ℕ} (hn : 40 ≤ n) : 2 / (n : ℝ) ≤ 1 / 20 := by
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The closure of `Mid` lies in `M`, over `Cl D`, and over the closed middle rectangle
`[1/2 − 2/n, 1/2 + 2/n] × [0, c₁]`. -/
theorem closure_midSet_sub {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hDR : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁) {n : ℕ} (hn : 40 ≤ n) :
    ∀ a ∈ closure (midSet M π F D' n), a ∈ M ∧ π a ∈ closure (F '' D') ∧
      π a ∈ F '' (Icc (1 / 2 - 2 / (n : ℝ)) (1 / 2 + 2 / (n : ℝ)) ×ˢ Icc 0 c₁) := by
  have h2n := two_div_le_of_forty hn
  have hRc : IsCompact (F '' (Icc (1 / 2 - 2 / (n : ℝ)) (1 / 2 + 2 / (n : ℝ)) ×ˢ Icc 0 c₁)) :=
    isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by linarith) (by linarith) hc₁)
  have hcl : IsClosed {a : Pt | a ∈ M ∧ π a ∈ closure (F '' D') ∧
      π a ∈ F '' (Icc (1 / 2 - 2 / (n : ℝ)) (1 / 2 + 2 / (n : ℝ)) ×ˢ Icc 0 c₁)} :=
    (isClosed_M_of_compact (M := M)).inter ((isClosed_closure.preimage hπc).inter
      (hRc.isClosed.preimage hπc))
  refine fun a ha => closure_minimal ?_ hcl ha
  rintro b ⟨hbM, q, hqD, hbq, hq1⟩
  refine ⟨hbM, subset_closure ⟨q, hqD, hbq.symm⟩, q, ⟨hq1, (hDR hqD).2.1.le, (hDR hqD).2.2.le⟩,
    hbq.symm⟩

theorem isCompact_closure_midSet (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) (n : ℕ) :
    IsCompact (closure (midSet M π F D' n)) :=
  (isCompact_iff_compactSpace.2 ‹CompactSpace M›).of_isClosed_subset isClosed_closure
    (closure_minimal (fun _ ha => ha.1) isClosed_M_of_compact)

/-- A point over the closed middle rectangle is not over a side segment. -/
theorem mid_not_side {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ}
    (hc₁ : c₁ ≤ 1) {n : ℕ} (hn : 40 ≤ n) {q q' : ℝ × ℝ}
    (hq : q ∈ Icc (1 / 2 - 2 / (n : ℝ)) (1 / 2 + 2 / (n : ℝ)) ×ˢ Icc 0 c₁)
    (hq' : q' ∈ (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) : F q ≠ F q' := by
  have h2n := two_div_le_of_forty hn
  intro h
  have hqR : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, by linarith [hq.2.1], by linarith [hq.2.2]⟩
  have hq'R : q' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    obtain ⟨h1, h2⟩ := hq'
    refine ⟨?_, by linarith [h2.1], by linarith [h2.2]⟩
    rcases h1 with h1 | h1 <;> rw [h1] <;> constructor <;> norm_num
  have heq := congrArg Prod.fst (collar_injOn hF hqR hq'R h)
  obtain ⟨⟨h1, h2⟩, -⟩ := hq
  rcases hq'.1 with h3 | h3 <;> rw [h3] at heq <;> rw [heq] at h1 h2 <;> linarith

/-- **`hε₃S`** (commission 181 §3.1.2): the distance from `Mid` to the preimage of the closed side
segments `π⁻¹F[{3/22, 19/22} × [0, c₁]]` is positive (the closure of `Mid` and that preimage are
disjoint, one compact, the other closed). -/
theorem exists_eps_mid_sides {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hDR : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁) {n : ℕ} (hn : 40 ≤ n) :
    ∃ δ > 0, ∀ a ∈ midSet M π F D' n, ∀ z : Pt,
      π z ∈ F '' (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) → δ ≤ dist a z := by
  set K := closure (midSet M π F D' n) with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closure_midSet π F D' n)
  have hside : IsCompact (F '' (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) := by
    refine isCompact_collar_image hF (((finite_singleton _).insert _).isCompact.prod isCompact_Icc)
      ?_
    rintro q ⟨h1, h2⟩
    refine ⟨?_, by linarith [h2.1], by linarith [h2.2]⟩
    rcases h1 with h1 | h1 <;> rw [h1] <;> constructor <;> norm_num
  have hdisj : Disjoint (F '' (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) (π '' K) := by
    rw [disjoint_left]
    rintro _ ⟨q', hq', rfl⟩ ⟨a, haK, hπa⟩
    obtain ⟨-, -, q, hq, hFq⟩ := closure_midSet_sub hπc hF hc₁ hDR hn a haK
    exact mid_not_side hF hc₁ hn hq hq' (hFq.trans hπa)
  obtain ⟨δ, hδ, hδd⟩ := exists_pos_dist_preimage (M := K) hπc hside.isClosed hdisj
  exact ⟨δ, hδ, fun a ha z hz => hδd a (subset_closure ha) z hz⟩

/-- **`hε₃O`** (commission 181 §3.1.1): some `δ > 0` such that every point of `M − E` within `δ`
of a point of `Mid` lies in `π⁻¹[D]`.

*Proof:* let `Bad` be the points of `M − E` off `π⁻¹[D]`. A common point `a` of `Cl Bad` and
`Cl Mid` lies in `M`, over `Fr D` (it is over `Cl D` but not over `D`, which is open), so over the
bottom edge or a closed side segment (`IsCrossRegion.frontier_sub`). The sides are excluded by the
abscissa. Over the bottom edge, `a` has the open neighbourhood `π⁻¹F[(3/22, 19/22) × (−cs, c₀)]`;
a point of `Bad` in it lies over the strip (`hstrip`), over the axis (then it is in `E`), or over the
low rectangle `(3/22, 19/22) × (0, c₀) ⊆ D′`; each is impossible. So `Cl Bad` and the compact
`Cl Mid` are disjoint, and have disjoint `δ`-thickenings. -/
theorem exists_eps_mid_O {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hR : IsCrossRegion M π F c₁ D') {n : ℕ} (hn : 40 ≤ n) {cs : ℝ} (hcs : 0 < cs) (hcs1 : cs ≤ 1)
    (hstrip : Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-cs) 0)) (π '' M)) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hlow : Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c₀ ⊆ D') :
    ∃ δ > 0, ∀ m ∈ M, m ∉ toPt E → ∀ a ∈ midSet M π F D' n, dist m a < δ → π m ∈ F '' D' := by
  have h2n := two_div_le_of_forty hn
  set Bad : Set Pt := {m | m ∈ M ∧ m ∉ toPt E ∧ π m ∉ F '' D'} with hBad
  set K := closure (midSet M π F D' n) with hK
  have hKc : IsCompact K := isCompact_closure_midSet π F D' n
  have hBadsub : closure Bad ⊆ {m | π m ∉ F '' D'} :=
    closure_minimal (fun m hm => hm.2.2) (hR.isOpen.isClosed_compl.preimage hπc)
  -- the neighbourhood of the bottom edge
  set B : Set (ℝ × ℝ) := Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo (-cs) c₀ with hB
  have hBo : IsOpen (F '' B) := isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
    (prod_mono (Ioo_subset_Ioo (by norm_num) (by norm_num)) (Ioo_subset_Ioo (by linarith) (by
      linarith)))
  have hdisj : Disjoint K (closure Bad) := by
    rw [disjoint_left]
    intro a haK haB
    obtain ⟨haM, hacl, q, hq, hFq⟩ := closure_midSet_sub hπc hF hc₁ hR.sub hn a haK
    have hanot : π a ∉ F '' D' := hBadsub haB
    have hfr : π a ∈ frontier (F '' D') ∩ π '' M :=
      ⟨⟨hacl, by rw [hR.isOpen.interior_eq]; exact hanot⟩, a, haM, rfl⟩
    rcases hR.frontier_sub hfr with (⟨q', ⟨hq'1, hq'2⟩, hFq'⟩ | ⟨q', ⟨hq'1, hq'2⟩, hFq'⟩) |
        ⟨q', ⟨hq'1, hq'2⟩, hFq'⟩
    · -- over the bottom edge
      rw [mem_singleton_iff] at hq'2
      have hqR : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, by linarith [hq.2.1], by linarith [hq.2.2]⟩
      have hq'R : q' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hq'1.1], by linarith [hq'1.2]⟩, (by rw [hq'2]; norm_num),
          (by rw [hq'2]; norm_num)⟩
      have hqq := collar_injOn hF hqR hq'R (hFq.trans hFq'.symm)
      have haU : a ∈ π ⁻¹' (F '' B) := by
        refine ⟨q, ⟨⟨?_, ?_⟩, ?_, ?_⟩, hFq⟩
        · linarith [hq.1.1]
        · linarith [hq.1.2]
        · rw [hqq, hq'2]; linarith
        · rw [hqq, hq'2]; exact hc₀
      obtain ⟨m, hmU, hmB⟩ := mem_closure_iff.1 haB _ (hBo.preimage hπc) haU
      obtain ⟨hmM, hmE, hmD⟩ := hmB
      obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, hFuv⟩ := hmU
      rcases lt_trichotomy v 0 with hv0 | hv0 | hv0
      · exact disjoint_left.1 hstrip ⟨(u, v), ⟨⟨hu.1.le, hu.2.le⟩, hv.1.le, hv0⟩, hFuv⟩
          ⟨m, hmM, rfl⟩
      · subst hv0
        exact hmE ⟨⟨m, hmM⟩, mem_E_of_axis hE hπS hγπ hF (q := ⟨m, hmM⟩) (t := u)
          ⟨by linarith [hu.1], by linarith [hu.2]⟩ hFuv.symm, rfl⟩
      · exact hmD ⟨(u, v), hlow ⟨hu, hv0, hv.2⟩, hFuv⟩
    · exact mid_not_side hF hc₁ hn hq ⟨Or.inl hq'1, hq'2⟩ (hFq.trans hFq'.symm)
    · exact mid_not_side hF hc₁ hn hq ⟨Or.inr hq'1, hq'2⟩ (hFq.trans hFq'.symm)
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_cthickenings hKc isClosed_closure
  refine ⟨δ, hδ, fun m hmM hmE a ha hma => ?_⟩
  by_contra hmD
  have hmBad : m ∈ closure Bad := subset_closure ⟨hmM, hmE, hmD⟩
  refine disjoint_left.1 hδd (mem_cthickening_of_dist_le m a δ K (subset_closure ha) hma.le)
    (self_subset_cthickening _ hmBad)

end Mid

end HPC.Hagopian
