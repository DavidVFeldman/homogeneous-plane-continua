import HPC.PseudoArc.LehnerCore
import HPC.Plane.PseudoArc51

/-!
# Batch 114: the covering step of Bing 1948, Theorem 14, by Lehner's Lemma 3

Source: G. R. Lehner, *Extending homeomorphisms on the pseudo-arc*, Trans. Amer. Math. Soc. 98
(1961) 369–394 (a dissertation under Bing). Its Lemma 3 (p. 375), in the case `n = 2`, is the
one-level covering claim `CoveringStep` to which Bing's Theorem 14 was reduced in batch 83; its
proof (p. 376) uses crookedness of one level in the previous one directly, not Bing's Theorem 9.
The transcription is in COMMISSION-batch114.md §1. Lehner's `W_m` are the levels `Δ.D m`; his
Theorem 2 is Moise's (subcontinua of a pseudo-arc are pseudo-arcs); his Theorem 3 is Bing's
Theorem 13 (`exists_description_from'`).

*Batch 114 status.* Every statement is proved. Shape changes from the skeleton:

* `not_mem_composant_of_irreducible`: the hypothesis `A ≠ B` is dropped (not used: a proper
  subcontinuum through `A` and `B` would contradict irreducibility).
* `exists_epsChain_of_irreducible`: the conclusion also states that the links are bounded (a
  diameter bound alone does not give boundedness in Mathlib, where an unbounded set has diameter
  `0`; boundedness is needed to pass from links to the closures of links).

The proof of `lehner_lemma3_two` does not go through a second description `Δ'`: the chains `F`
and `G` of Lehner's proof are two successive steps of Bing's Theorem 13 (`Description.exists_step`)
from `P'` to `Q'`, and `G` is crooked in `F` because `G` refines the level after the one that `F`
consolidates. The second continuum `H_2` and its chain `E_2` are not needed in the covering step:
the last link of `G` already contains `Q'` only. The combinatorics is in `LehnerCore.lean`.

*Batch 115.* The proof of `lehner_lemma3_two` is now the proof of `lehner_lemma3_twoA`, which also
records Lehner's return point `g_{y_1} ⊆ f_2 ⊆ e_1` and the tightness of the covering part (the
`A`-covering step of `Thm14.lean`); `lehner_lemma3_two` (statement unchanged) is derived from it.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A nondegenerate subcontinuum of a pseudo-arc is a pseudo-arc (Moise; here from the
hereditary properties, as `Plane.isPseudoArc_of_subcontinuum`). -/
theorem isPseudoArc_of_subcontinuum {M W : Set X} (hM : Plane.IsPseudoArc M) (hW : W ⊆ M)
    (hWc : Fold.Q78.IsContinuum W) (hnt : W.Nontrivial) : Plane.IsPseudoArc W :=
  Plane.isPseudoArc_of_subcontinuum hM hW hWc hnt

/-- The end points of an irreducible continuum lie in different composants of it. (Batch 114:
the skeleton's hypothesis `A ≠ B` is not needed and has been removed.) -/
theorem not_mem_composant_of_irreducible {W : Set X} {A B : X} (h : IsIrreducibleBetween W A B) :
    B ∉ composant W A := by
  intro hB
  obtain ⟨K, ⟨hK, hKW, hKne, hAK⟩, hBK⟩ := mem_sUnion.mp hB
  exact hKne (h.2.2.2 K hK hKW hAK hBK)

/-- **An `ε`-chain of a sub-pseudo-arc from one end to the other**: for `W ⊆ M` irreducible
between `P'` and `R`, a chain from `P'` to `R` covering `W`, every link meeting `W`, with bounded
links of diameter `< ε`. (A deep level of a description of `W` from `P'` to `R`,
`exists_description_of_chainable_HI`; the links of a level meet the described continuum by
`Description.link_inter_M_nonempty`, so no link has to be removed.) -/
theorem exists_epsChain_of_irreducible [CompactSpace X] {M W : Set X} (hM : Plane.IsPseudoArc M)
    (hW : W ⊆ M) {P' R : X} (hirr : IsIrreducibleBetween W P' R) (hne : P' ≠ R) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (E : Chain X m), 2 ≤ m ∧ E.IsFrom P' R ∧ W ⊆ E.union ∧
      (∀ i, (E.link i ∩ W).Nonempty) ∧ (∀ i, Bornology.IsBounded (E.link i)) ∧
      ∀ i, diam (E.link i) < ε := by
  have hWpa := isPseudoArc_of_subcontinuum hM hW hirr.1 ⟨P', hirr.2.1, R, hirr.2.2.1, hne⟩
  obtain ⟨ΔW, hΔW⟩ := Plane.exists_description_of_chainable_HI hWpa hirr.2.1 hirr.2.2.1
    (not_mem_composant_of_irreducible hirr)
  obtain ⟨i, hi⟩ := (ΔW.ε_tendsto.eventually (gt_mem_nhds (lt_min hε (dist_pos.mpr hne)))).exists
  refine ⟨ΔW.n i, ΔW.D i, ΔW.two_le_n_of_lt i (hi.trans_le (min_le_right _ _)), ΔW.isFrom i,
    hΔW ▸ ΔW.M_subset_union i, fun t => hΔW ▸ ΔW.link_inter_M_nonempty i t, fun t => ΔW.bdd i t,
    fun t => (ΔW.diam_le i t).trans_lt (hi.trans_le (min_le_left _ _))⟩

/-- A consolidation of a consolidation is a consolidation. -/
theorem Chain.IsConsolidationOf.trans {l m n : ℕ} {F : Chain X l} {G : Chain X m}
    {D : Chain X n} (h₁ : F.IsConsolidationOf G) (h₂ : G.IsConsolidationOf D) :
    F.IsConsolidationOf D := by
  refine ⟨h₂.1.trans h₁.1, fun t => ?_⟩
  obtain ⟨S, hS⟩ := h₁.2 t
  choose T hT using h₂.2
  refine ⟨{j | ∃ i ∈ S, j ∈ T i}, ?_⟩
  rw [hS]
  ext q
  simp only [hT, mem_iUnion, mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨i, hi, j, hj, hq⟩
    exact ⟨j, ⟨i, hi, hj⟩, hq⟩
  · rintro ⟨j, ⟨i, hi, hj⟩, hq⟩
    exact ⟨i, hi, j, hj, hq⟩

/-- **A description of `M` from `P'` to `Q'` whose levels are consolidations of levels of `Δ`**
(Bing's Theorem 13 through `exists_description_of_steps` with the property carried). -/
theorem exists_description_consolidating [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hQc : Q' ∉ composant Δ.M P') :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧ ∀ i, ∃ k, (Δ'.D i).IsConsolidationOf (Δ.D k) :=
  Δ.exists_description_of_steps (fun _ F => ∃ k, F.IsConsolidationOf (Δ.D k)) fun L => by
    obtain ⟨k, hk, N, F, h1, h2, h3, h4⟩ := Δ.exists_step hPQ hP' hQ' hQc L
    exact ⟨k, hk, N, F, h1, h2, h3, h4, k, h2⟩

/-- **Lehner's Lemma 3, `n = 2`** (Trans. AMS 98 (1961), p. 375–376), in the form of the covering
step, with the tightness and return point of batch 115: for a description `Δ` of `M`, points `P'`,
`Q'` of `M` in different composants, `R ≠ P'` in the composant of `P'`, and `W` irreducible between
`P'` and `R`, every level `L` admits a deeper consolidation `F` of a level of `Δ`, a chain from `P'`
to `Q'` with closures of links inside links of `D_L` and mesh `≤ 1/(L+1)`, whose initial subchain
`F(0..b)` from `P'` to `R` covers `W`, and an index `a ≥ b` (the block of Lehner's `g_{y_1}`) such
that `F(0..a)` lies within `1/(L+1)` of `W` and the link `a` within `1/(L+1)` of `P'`. (This is
`Description.CoveringStepA` of `Thm14.lean`, unfolded.) -/
theorem lehner_lemma3_twoA [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom P' Q' ∧ F.IsConsolidationOf (Δ.D k) ∧
      (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧
      ∃ hN : 0 < N, ∃ b a : Fin N, ∃ h0b : (⟨0, hN⟩ : Fin N) ≤ b, b ≤ a ∧
        (F.sub ⟨0, hN⟩ b h0b).IsFrom P' R ∧ W ⊆ F.span ⟨0, hN⟩ b ∧
        F.span ⟨0, hN⟩ a ⊆ thickening (1 / ((L : ℝ) + 1)) W ∧
        F.link a ⊆ ball P' (1 / ((L : ℝ) + 1)) := by
  intro L
  have hP'W := hWirr.2.1
  have hRW := hWirr.2.2.1
  obtain ⟨-, hQW⟩ := Description.IsIrreducibleBetween.ne_M_and_not_mem Δ hP' hR hRc hQc hPR hW hWirr
  -- the Lebesgue number of `D_L` on `M`
  obtain ⟨lL, hlL, hlebL⟩ := lebesgue_number_lemma_of_metric Δ.isCompact_M
    (fun t => (Δ.D L).isOpen t) (Δ.M_subset_union L)
  -- a ball about `Q'` missing `W`
  obtain ⟨η, hη, hηW⟩ := Metric.isOpen_iff.mp (isOpen_compl_iff.mpr hWirr.1.1.isClosed) Q' hQW
  set ε := min (min lL η) (1 / ((L : ℝ) + 1)) / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεL : ε < lL := by
    have := min_le_left (min lL η) (1 / ((L : ℝ) + 1)); have := min_le_left lL η; linarith
  have hεη : ε < η := by
    have := min_le_left (min lL η) (1 / ((L : ℝ) + 1)); have := min_le_right lL η; linarith
  have hε1 : ε ≤ 1 / ((L : ℝ) + 1) := by
    have := min_le_right (min lL η) (1 / ((L : ℝ) + 1)); have : (0 : ℝ) < 1 / ((L : ℝ) + 1) :=
      by positivity
    linarith
  -- Lehner's `E_1`
  obtain ⟨m, E, hm, hE, hWE, hEW, hEbdd, hEd⟩ :=
    exists_epsChain_of_irreducible (Plane.isPseudoArc_of_description' Δ hPQ) hW hWirr hPR hε
  -- the Lebesgue number of `E_1` on `W`
  obtain ⟨l₁, hl₁, hleb₁⟩ := lebesgue_number_lemma_of_metric hWirr.1.1 (fun i => E.isOpen i) hWE
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (3 / l₁)
  set L₁ := max L₀ L with hL₁
  -- Lehner's `F` and `G`: two successive steps of Theorem 13 from `P'` to `Q'`
  obtain ⟨k₁, hk₁, u, F, hF, hFc, hFcl, hFd⟩ := Δ.exists_step hPQ hP' hQ' hQc L₁
  obtain ⟨k₂, hk₂, v, G, hG, hGc, hGcl, hGd⟩ := Δ.exists_step hPQ hP' hQ' hQc (k₁ + 1)
  have hGref : G.Refines (Δ.D (k₁ + 1)) := fun l => by
    obtain ⟨t, ht⟩ := hGcl l
    exact ⟨t, subset_closure.trans ht⟩
  have hGF : G.IsCrookedIn' F :=
    Chain.isCrookedIn'_of_refines hGref (Chain.isCrookedIn'_of_isConsolidationOf hFc (Δ.crooked k₁))
  have hWF : W ⊆ F.union := by rw [hFc.union_eq]; exact hW.trans (Δ.M_subset_union k₁)
  have hWG : W ⊆ G.union := by rw [hGc.union_eq]; exact hW.trans (Δ.M_subset_union k₂)
  -- `Q'` is not in `E_1`
  have hQE : Q' ∉ E.union := by
    intro hQ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hQ
    obtain ⟨y, hy, hyW⟩ := hEW i
    have h1 := (dist_le_diam_of_mem (hEbdd i) hy hi).trans (hEd i).le
    exact hηW (mem_ball.mpr (by linarith)) hyW
  -- Lehner's "4-linked subchain" condition (here: links within two of a link meeting `W`)
  have hFbdd : ∀ l, Bornology.IsBounded (F.link l) := fun l => by
    obtain ⟨t, ht⟩ := hFcl l
    exact (Δ.bdd L₁ t).subset (subset_closure.trans ht)
  have h3 : 3 * (1 / ((L₁ : ℝ) + 1)) < l₁ := by
    have h1 : (L₀ : ℝ) ≤ L₁ := by exact_mod_cast le_max_left L₀ L
    have h2 : 3 < l₁ * L₀ := by rwa [div_lt_iff₀ hl₁, mul_comm] at hL₀
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hwin : ∀ l l' : Fin u, l.val ≤ l'.val + 2 → l'.val ≤ l.val + 2 →
      (F.link l' ∩ W).Nonempty → ∃ i, F.link l ⊆ E.link i := by
    intro l l' h1 h2 ⟨y, hy, hyW⟩
    obtain ⟨i, hi⟩ := hleb₁ y hyW
    refine ⟨i, fun q hq => hi (mem_ball.mpr ?_)⟩
    have := Lehner.dist_le_of_near F hFbdd hFd h1 h2 hq hy
    linarith
  -- batch 115: the second link of `F` lies in the first link of `E_1` (Lehner's `f_2 ⊆ e_1`)
  have hF1 : ∀ h1 : 1 < u, F.link ⟨1, h1⟩ ⊆ E.link ⟨0, by omega⟩ := by
    intro h1 q hq
    obtain ⟨i, hi⟩ := hleb₁ P' hP'W
    have hi0 : i = ⟨0, by omega⟩ := hE.2.2.2.1 i (hi (mem_ball_self hl₁))
    rw [← hi0]
    refine hi (mem_ball.mpr ?_)
    have := Lehner.dist_le_of_near F hFbdd hFd (l := ⟨1, h1⟩) (l' := ⟨0, hF.1⟩)
      (by simp) (by simp) hq hF.2.1
    linarith
  -- Lehner's construction
  obtain ⟨p, β, hβ, hFrom, hCov, hblk, ⟨hp, hRm⟩, a, hma, haE, haP⟩ :=
    Lehner.core hWirr.1.2.isPreconnected hP'W hRW E hm hE hQE F hF hWF hwin G hG hGF hWG hF1
  have hLk : L ≤ k₁ + 1 := by have := le_max_right L₀ L; omega
  refine ⟨k₂, by omega, p, G.ofBlocks β hβ, hFrom,
    (Chain.ofBlocks_isConsolidationOf G β hβ).trans hGc, fun w => ?_, fun w => ?_, ?_⟩
  rotate_left 2
  · -- batch 115: the `A`-covering data
    obtain ⟨hN, b, h0b, hsub, hWspan⟩ := hCov
    have hba : b ≤ a := by
      by_contra hcon
      have hb : m - 1 < b.val := by have := Fin.not_le.mp hcon; simp only [Fin.lt_def] at this; omega
      have := hsub.2.2.2.2 ⟨m - 1, by show m - 1 < b.val - 0 + 1; omega⟩ (by
        show R ∈ (G.ofBlocks β hβ).link ⟨0 + (m - 1), _⟩
        rwa [show (⟨0 + (m - 1), _⟩ : Fin p) = ⟨m - 1, hp⟩ from Fin.ext (by simp only; omega)])
      have := congrArg Fin.val this
      simp only at this
      omega
    refine ⟨hN, b, a, h0b, hba, hsub, hWspan, fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨w, -, hwa, hqw⟩ := Chain.mem_span.mp hq
      obtain ⟨i, hi⟩ := haE w hwa
      obtain ⟨y, hy, hyW⟩ := hEW i
      refine thickening_mono hε1 W (mem_thickening_iff.mpr ⟨y, hyW, ?_⟩)
      exact (dist_le_diam_of_mem (hEbdd i) (hi hqw) hy).trans_lt (hEd i)
    · refine mem_ball.mpr (lt_of_lt_of_le ?_ hε1)
      exact (dist_le_diam_of_mem (hEbdd _) (haP hq) hE.2.1).trans_lt (hEd _)
  · rcases hblk w with ⟨i, hi⟩ | ⟨l, hl⟩
    · obtain ⟨y, hy, hyW⟩ := hEW i
      obtain ⟨t, ht⟩ := hlebL y (hW hyW)
      refine ⟨t, (closure_mono hi).trans (Subset.trans ?_ ((closedBall_subset_ball
        ((hEd i).trans hεL)).trans ht))⟩
      exact closure_minimal (fun q hq => mem_closedBall.mpr (dist_le_diam_of_mem (hEbdd i) hq hy))
        isClosed_closedBall
    · rw [hl]
      obtain ⟨t, ht⟩ := hGcl l
      obtain ⟨s, hs⟩ := Δ.refines_of_le hLk t
      exact ⟨s, ht.trans hs⟩
  · rcases hblk w with ⟨i, hi⟩ | ⟨l, hl⟩
    · exact (diam_mono hi (hEbdd i)).trans ((hEd i).le.trans hε1)
    · rw [hl]
      refine (hGd l).trans ?_
      gcongr

/-- **Lehner's Lemma 3, `n = 2`**, in the form of the covering step (statement unchanged from batch
114; since batch 115 a consequence of `lehner_lemma3_twoA`). -/
theorem lehner_lemma3_two [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Description.CoveringStep Δ P' Q' R W := by
  intro L
  obtain ⟨k, hk, N, F, h1, h2, h3, h4, hN, b, -, h0b, -, h5, h6, -, -⟩ :=
    lehner_lemma3_twoA Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr L
  exact ⟨k, hk, N, F, h1, h2, h3, h4, hN, b, h0b, h5, h6⟩

/-- **The covering step** (formerly the open `Description.covering_step` of `Theorem14.lean`;
statement unchanged from batch 83). -/
theorem Description.covering_step [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Description.CoveringStep Δ P' Q' R W :=
  lehner_lemma3_two Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr

/-- **The covering description** (Bing's `X_{i,1}, X_{i,2}, …` in the proof of Theorem 14; formerly
conditional on `covering_step`): a description of `M` from `P'` to `Q'` each of whose levels covers
`W` by its initial subchain from `P'` to `R`. -/
theorem Description.exists_description_covering [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, ∃ b : Fin (Δ'.n i), ∃ h0b : (⟨0, (Δ'.isFrom i).1⟩ : Fin (Δ'.n i)) ≤ b,
        ((Δ'.D i).sub ⟨0, (Δ'.isFrom i).1⟩ b h0b).IsFrom P' R ∧
        W ⊆ (Δ'.D i).span ⟨0, (Δ'.isFrom i).1⟩ b :=
  Description.exists_description_covering_of_step Δ
    (Description.covering_step Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr)

end HPC
