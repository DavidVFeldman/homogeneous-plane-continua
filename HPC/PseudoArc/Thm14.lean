import HPC.PseudoArc.Lehner
import HPC.PseudoArc.Uniqueness
import HPC.PseudoArc.T5Gen
import HPC.PseudoArc.T14Glue

/-!
# Batch 115: Bing 1948, Theorem 14 — the alternating construction with the position of `R` carried

Plan (COMMISSION-batch115.md §1). Bing's proof of Theorem 14 (p. 741) runs the alternating
construction of Theorem 12 on two descriptions `X_{i,·}` from `P_i` to `Q_i` whose levels cover
`W_i` by their initial subchains up to `R_i`, keeping `R_1`, `R_2` in corresponding links; each
half-step on the following side uses Theorem 5 three times, on the stretches `P → R`, `R → A`,
`A → Q` of a deep level, where `A` is a point beyond `R` at which the level has come back into
the first link of the coarse chain. Two facts his sketch asserts without proof are supplied by
Lehner's construction (batch 114): the level's initial part up to `R`, and on to the return
point `A`, lies within `ε` of `W` (it is made of links of an `ε`-chain of `W`), and the return
point exists (crookedness of `G` in `F` sends `G` from `f_{t_1−1}` back to `f_2 ⊆ e_1`, inside
the first link of the `ε`-chain). These are packaged as an **`A`-covering description**
(`CoveringStepA`, `exists_description_coveringA`). Tightness makes the fine covering part refine
the coarse covering part, which is what lets the patterns of the two sides be chosen with the
same `R`-index and with values `≤ ρ` on the covering part (`IsTrackedPattern`); the return point
lets the stretch `R → A` follow the reversed covering pattern and the stretch `A → Q` the whole
pattern, both within Theorem 5's value constraints. Theorem 11 with its tracking clause then
carries `P`, `Q` and `R`.

*Batch 115 status.* Every statement is proved; `theorem14` and `theorem15` (statements unchanged)
have moved here from `Theorem14.lean`. Auxiliary files: `T5Gen.lean` (Theorem 5 with an arbitrary
coarse chain, a level `∀ᶠ j`, and the end clauses; it replaces the thinned description),
`T14Glue.lean` (the gluing of the three pieces), and the extensions of `LehnerCore.lean` /
`Lehner.lean` (Lehner's `y_1`, `lehner_lemma3_twoA`). Shape changes from the skeleton
(REPORT-batch115.md):

* `exists_trackedPattern_of_refines`: the unused hypothesis `0 < η` is removed.
* `exists_tracked_follower`: hypotheses `IsCompact W` and `0 < ρ` added; the conclusion is stated
  as `Δ.TCanFollow R W lv (Δ.D lv) ρ` (the skeleton's conclusion for every `N'`, `x`, `ρ'`).
* `TRung.follow`: the skeleton's `C₁ = Δ₁.D lv₁` does not typecheck (`Chain X N` against
  `Chain X (Δ₁.n lv₁)`); it is replaced by `Δ₁.TCanFollow R₁ W₁ lv₁ C₁ ρ`, which is what the
  construction uses of the following side.
* `TRung.exists_base`, `TRung.exists_next`, `exists_homeomorph_tracked`: hypotheses `P_i ≠ R_i`,
  `R₁ ≠ Q₁`, `IsCompact W_i` added (all available in `theorem14`).
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

/-! ### The `A`-covering step and description -/

/-- `F` covers `W` up to `R` *tightly and with a return point*: an initial subchain
`F(0..b)` from `P'` to `R` whose span contains `W`; an index `a ≥ b` such that the span of
`F(0..a)` lies within `η` of `W` and the link `a` lies within `η` of `P'`. -/
def CoversUpToA {N : ℕ} (F : Chain X N) (P' R : X) (W : Set X) (η : ℝ) : Prop :=
  ∃ hN : 0 < N, ∃ b a : Fin N, ∃ h0b : (⟨0, hN⟩ : Fin N) ≤ b, b ≤ a ∧
    (F.sub ⟨0, hN⟩ b h0b).IsFrom P' R ∧ W ⊆ F.span ⟨0, hN⟩ b ∧
    F.span ⟨0, hN⟩ a ⊆ thickening η W ∧ F.link a ⊆ ball P' η

/-- **The `A`-covering step**: `CoveringStep` with `CoversUpToA` at radius `1/(L+1)`. -/
def Description.CoveringStepA {P Q : X} (Δ : Description X P Q) (P' Q' R : X) (W : Set X) :
    Prop :=
  ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom P' Q' ∧ F.IsConsolidationOf (Δ.D k) ∧
    (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
    (∀ u, Metric.diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧
    CoversUpToA F P' R W (1 / ((L : ℝ) + 1))

/-- **Lehner's construction gives the `A`-covering step.** In `lehner_lemma3_two`: the blocks
`d_1, …, d_{m_1}` lie in links of the `ε`-chain `E` of `W`, each of which meets `W` and has
diameter `< ε`; so do the links `g_{z_1+1}, …, g_{y_1}` (they lie in links of `F(1, t_1 − 1)`,
which lie in links of `E`); and `g_{y_1} ⊆ f_2 ⊆ e_1 ⊆ ball P' ε` (the second link of `F` lies
within `3/(L_1+1)` of `P'`, below the Lebesgue number of `E` on `W`, so in the link `e_1` of `E`
containing `P'`). Take `a` = the index of `g_{y_1}` in `D` and `ε ≤ 1/(L+1)`. The proof is
`lehner_lemma3_twoA` (`Lehner.lean`, batch 115). -/
theorem Description.covering_stepA [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Δ.CoveringStepA P' Q' R W :=
  lehner_lemma3_twoA Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr

/-- `exists_description_of_steps` with a property depending on the level `L` of the step: the
level `i` of the description is built by the step at some `L ≥ i`. -/
theorem Description.exists_description_of_steps' [CompactSpace X] {P Q : X}
    (Δ : Description X P Q) {R S : X} (G : ℕ → (N : ℕ) → Chain X N → Prop)
    (hstep : ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom R S ∧ F.IsConsolidationOf (Δ.D k) ∧
      (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧ G L N F) :
    ∃ Δ' : Description X R S, Δ'.M = Δ.M ∧ ∀ i, ∃ L, i ≤ L ∧ G L (Δ'.n i) (Δ'.D i) := by
  choose K hK N F hF1 hF2 hF3 hF4 hG using hstep
  let lev : ℕ → ℕ := fun i => Nat.rec 0 (fun _ l => K l + 1) i
  have hlev0 : lev 0 = 0 := rfl
  have hlevs : ∀ i, lev (i + 1) = K (lev i) + 1 := fun i => rfl
  have hlevge : ∀ i, i ≤ lev i := by
    intro i
    induction i with
    | zero => simp [hlev0]
    | succ i ih => rw [hlevs]; have := hK (lev i); omega
  have hbdd : ∀ L (u : Fin (N L)), Bornology.IsBounded ((F L).link u) := by
    intro L u
    obtain ⟨t, ht⟩ := hF3 L u
    exact (Δ.bdd L t).subset (subset_closure.trans ht)
  refine ⟨{
    n := fun i => N (lev i)
    D := fun i => F (lev i)
    isFrom := fun i => hF1 (lev i)
    crooked := fun i => ?_
    closure_subset := fun i t => ?_
    ε := fun i => 1 / ((i : ℝ) + 1)
    ε_pos := fun i => by positivity
    ε_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
    bdd := fun i t => hbdd (lev i) t
    diam_le := fun i t => ?_ }, ?_, fun i => ⟨lev i, hlevge i, hG (lev i)⟩⟩
  · show (F (lev (i + 1))).IsCrookedIn' (F (lev i))
    have href : (F (lev (i + 1))).Refines (Δ.D (K (lev i) + 1)) := by
      intro u
      obtain ⟨t, ht⟩ := hF3 (lev (i + 1)) u
      exact ⟨t, subset_closure.trans ht⟩
    exact Chain.isCrookedIn'_of_refines href
      (Chain.isCrookedIn'_of_isConsolidationOf (hF2 (lev i)) (Δ.crooked (K (lev i))))
  · show ∃ s, closure ((F (lev (i + 1))).link t) ⊆ (F (lev i)).link s
    obtain ⟨s1, hs1⟩ := hF3 (lev (i + 1)) t
    obtain ⟨s2, hs2⟩ := Δ.closure_subset (K (lev i)) s1
    obtain ⟨s3, hs3⟩ := (hF2 (lev i)).1 s2
    exact ⟨s3, hs1.trans (subset_closure.trans (hs2.trans hs3))⟩
  · show diam ((F (lev i)).link t) ≤ 1 / ((i : ℝ) + 1)
    refine (hF4 (lev i) t).trans ?_
    gcongr
    exact_mod_cast hlevge i
  · show (⋂ i, (F (lev i)).union) = Δ.M
    refine Subset.antisymm ?_ ?_
    · intro z hz
      simp only [mem_iInter] at hz
      simp only [Description.M, mem_iInter]
      intro j
      have := hz j
      rw [(hF2 (lev j)).union_eq] at this
      exact Chain.union_subset_of_refines (Δ.refines_of_le
        (le_trans (hlevge j) (hK (lev j)).le)) this
    · intro z hz
      simp only [mem_iInter]
      intro i
      rw [(hF2 (lev i)).union_eq]
      exact Δ.M_subset_union _ hz

/-- **The `A`-covering description**: a description of `M` from `P'` to `Q'` every level `i` of
which covers `W` up to `R` tightly, at radius `≤ 1/(i+1)`, with a return point. -/
theorem Description.exists_description_coveringA [CompactSpace X] {P Q : X}
    (Δ : Description X P Q) (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M)
    (hR : R ∈ Δ.M) (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, CoversUpToA (Δ'.D i) P' R W (1 / ((i : ℝ) + 1)) := by
  obtain ⟨Δ', hM, hG⟩ := Δ.exists_description_of_steps'
    (fun L N F => CoversUpToA F P' R W (1 / ((L : ℝ) + 1)))
    (Δ.covering_stepA hPQ hP' hQ' hR hRc hQc hPR hW hWirr)
  refine ⟨Δ', hM, fun i => ?_⟩
  obtain ⟨L, hiL, hN, b, a, h0b, hba, h1, h2, h3, h4⟩ := hG i
  have hmono : 1 / ((L : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    gcongr
  exact ⟨hN, b, a, h0b, hba, h1, h2, h3.trans (thickening_mono hmono W),
    h4.trans (ball_subset_ball hmono)⟩

/-! ### Tracked patterns and the three-piece follower -/

/-- A pattern `x` on `N'` links into `N` links *tracks* `ρ' ↦ ρ`: `x ρ' = ρ` and `x t ≤ ρ` for
`t ≤ ρ'`. -/
def IsTrackedPattern {N' N : ℕ} (x : Fin N' → Fin N) (ρ' : Fin N') (ρ : Fin N) : Prop :=
  Description.IsPattern x ∧ x ρ' = ρ ∧ ∀ t, t ≤ ρ' → x t ≤ ρ

/-- A chain `C` *carries* `(P, R, W)` at `ρ`: `C(0..ρ)` is from `P` to `R` and its span contains
`W`. -/
def Carries {N : ℕ} (C : Chain X N) (P R : X) (W : Set X) (ρ : Fin N) : Prop :=
  ∃ hN : 0 < N, ∃ h0 : (⟨0, hN⟩ : Fin N) ≤ ρ, (C.sub ⟨0, hN⟩ ρ h0).IsFrom P R ∧
    W ⊆ C.span ⟨0, hN⟩ ρ

/-- `R` lies in the link `ρ` of a chain carrying `(P, R, W)` at `ρ`. -/
theorem Carries.mem_link {N : ℕ} {C : Chain X N} {P R : X} {W : Set X} {ρ : Fin N}
    (h : Carries C P R W ρ) : R ∈ C.link ρ := by
  obtain ⟨hN, h0, hsub, -⟩ := h
  have := hsub.2.2.1
  have hidx : (⟨0 + (ρ.val - 0 + 1 - 1), by omega⟩ : Fin N) = ρ := Fin.ext (by simp)
  exact hidx ▸ this

/-- `R` is not in the first link of a chain carrying `(P, R, W)` at `ρ ≥ 1`. -/
theorem Carries.not_mem_first {N : ℕ} {C : Chain X N} {P R : X} {W : Set X} {ρ : Fin N}
    (h : Carries C P R W ρ) (hρ : 0 < ρ.val) : R ∉ C.link ⟨0, h.1⟩ := by
  obtain ⟨hN, h0, hsub, -⟩ := h
  intro hR
  have := hsub.2.2.2.2 ⟨0, by omega⟩ (by simpa using hR)
  have := congrArg Fin.val this
  simp only at this
  omega

/-- A set lying in a link of a chain and in the span of its links `0..ρ` lies in a link of index
`≤ ρ`. (If the link is `j > ρ`, every point of the set is in `C.link j` and in a link `≤ ρ`,
which must be `ρ`.) -/
theorem Chain.exists_link_le_of_subset_span {N : ℕ} (C : Chain X N) {S : Set X} {j a ρ : Fin N}
    (hj : S ⊆ C.link j) (hS : S ⊆ C.span a ρ) : ∃ s, s ≤ ρ ∧ S ⊆ C.link s := by
  by_cases hjρ : j ≤ ρ
  · exact ⟨j, hjρ, hj⟩
  · refine ⟨ρ, le_rfl, fun q hq => ?_⟩
    obtain ⟨s, -, hsρ, hqs⟩ := Chain.mem_span.mp (hS hq)
    have := (C.adjacent_iff j s).mp ⟨q, hj hq, hqs⟩
    have h1 := Fin.not_le.mp hjρ
    rw [Fin.lt_def] at h1
    have h2 : s.val ≤ ρ.val := hsρ
    rwa [show ρ = s from Fin.ext (by omega)]

/-- **The refinement pattern of a tight level tracks.** If `C` carries `(P, R, W)` at `ρ` and a
fine level `D` of an `A`-covering description (radius `η`, with `thickening η W ⊆ C.span 0 ρ` and
the link of `R` in `D` inside `C.link ρ`) refines `C`, then there is a pattern `x` with
`D.FollowsPattern x C` tracking `ρ_D ↦ ρ`, where `ρ_D` is the `R`-index of `D`. (A link of `D` in
`C.span 0 ρ` and in `C.link j` with `j > ρ` lies in `C.link (j) ∩ C.link ρ`, so `ρ` may be chosen.)

(Batch 115: the skeleton's hypothesis `0 < η` is not used and has been removed.) -/
theorem exists_trackedPattern_of_refines {N N' : ℕ} {C : Chain X N} {D : Chain X N'}
    {P Q R : X} {W : Set X} (hC : C.IsFrom P Q) (hD : D.IsFrom P Q) (href : D.Refines C)
    {ρ : Fin N} (hcar : Carries C P R W ρ) {η : ℝ}
    (hDA : CoversUpToA D P R W η)
    (hthick : thickening η W ⊆ C.span ⟨0, hcar.1⟩ ρ)
    (hRlink : ∀ t, R ∈ D.link t → D.link t ⊆ C.link ρ) :
    ∃ ρ' : Fin N', ∃ x : Fin N' → Fin N, IsTrackedPattern x ρ' ρ ∧ D.FollowsPattern x C ∧
      Carries D P R W ρ' := by
  classical
  obtain ⟨hN', b, a, h0b, hba, hsub, hWb, hspan, -⟩ := hDA
  have hcarD : Carries D P R W b := ⟨hN', h0b, hsub, hWb⟩
  have hRb : R ∈ D.link b := hcarD.mem_link
  -- the links up to `b` lie in links of `C` of index `≤ ρ`
  have htight : ∀ t, t ≤ b → ∃ s, s ≤ ρ ∧ D.link t ⊆ C.link s := by
    intro t htb
    refine C.exists_link_le_of_subset_span (a := ⟨0, hcar.1⟩) (Chain.refineIdx_subset href t) ?_
    intro q hq
    refine hthick (hspan (Chain.mem_span.mpr ⟨t, Fin.le_def.mpr (Nat.zero_le _),
      le_trans htb hba, hq⟩))
  choose σ hσ using htight
  let x : Fin N' → Fin N := fun t =>
    if t = b then ρ else if h : t ≤ b then σ t h else Chain.refineIdx href t
  have hfollow : D.FollowsPattern x C := by
    intro t
    by_cases htb : t = b
    · simp only [x, if_pos htb]
      exact hRlink t (htb ▸ hRb)
    · by_cases hle : t ≤ b
      · simp only [x, if_neg htb, dif_pos hle]
        exact (hσ t hle).2
      · simp only [x, if_neg htb, dif_neg hle]
        exact Chain.refineIdx_subset href t
  refine ⟨b, x, ⟨⟨hD.1, hC.1, hC.2.2.2.1 _ (hfollow _ hD.2.1),
    hC.2.2.2.2 _ (hfollow _ hD.2.2.1), fun t t' ht => Chain.pattern_lipschitz hfollow t' t
      (by rw [D.adjacent_iff]; omega)⟩, by simp [x], fun t ht => ?_⟩, hfollow, hcarD⟩
  by_cases htb : t = b
  · simp [x, htb]
  · simp only [x, if_neg htb, dif_pos ht]
    exact (hσ t ht).1

/-- The span of a run of links is open. -/
theorem Chain.isOpen_span {N : ℕ} (C : Chain X N) (a b : Fin N) : IsOpen (C.span a b) :=
  isOpen_iUnion fun t => isOpen_iUnion fun _ => C.isOpen t

/-- The closure of a bounded set containing `c` lies in the closed ball about `c` of radius its
diameter. -/
theorem closure_subset_closedBall_diam {s : Set X} {c : X} (hb : Bornology.IsBounded s)
    (hc : c ∈ s) {r : ℝ} (hr : diam s ≤ r) : closure s ⊆ closedBall c r :=
  closure_minimal (fun _ hq => mem_closedBall.mpr ((dist_le_diam_of_mem hb hq hc).trans hr))
    isClosed_closedBall

/-- `Δ.TCanFollow R W lv C ρ`: every pattern into `C` tracking some `ρ'` to `ρ` is followed by a
consolidation of a level of `Δ` deeper than `lv` that carries `(P, R, W)` at `ρ'`. The tracked
analogue of `Description.CanFollow`; `exists_tracked_follower` gives it for the levels of an
`A`-covering description. -/
def Description.TCanFollow {P Q : X} (Δ : Description X P Q) (R : X) (W : Set X) (lv : ℕ)
    {N : ℕ} (C : Chain X N) (ρ : Fin N) : Prop :=
  ∀ (N' : ℕ) (x : Fin N' → Fin N) (ρ' : Fin N'), IsTrackedPattern x ρ' ρ →
    ∃ a, lv < a ∧ ∃ E : Chain X N', E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D a) ∧
      E.FollowsPattern x C ∧ Carries E P R W ρ'

/-- **The three-piece follower** (Bing's `E_1 + E_2 + E_3`). Let `Δ` be an `A`-covering
description of `M` from `P` to `Q` for `(R, W)` (every level `i` satisfies `CoversUpToA` at
radius `1/(i+1)`), `C = Δ.D lv` a level carrying `(P, R, W)` at `ρ ≥ 1`, and `x` a pattern on
`N'` links into `C` tracking `ρ' ↦ ρ`. Then some deeper level has a consolidation `E` from `P` to
`Q` following `x` in `C` and carrying `(P, R, W)` at `ρ'`.

Construction: a deep level `D_a` (tight: its span up to its return index `α` lies in
`C.span 0 ρ`; its `R`-link inside `C.link ρ`; its return link inside `C.link 0`), a deeper level
`D_b`, and Theorem 5 (`theorem5_gen`, with coarse chain `C`, or `C` reversed for the middle
stretch) three times: on `D_a(0..ρ_a)` with the pattern `x|[0, ρ']` (from `0` to `ρ`, values in
`[0, ρ]`); on `D_a(ρ_a..α)` with the reversed pattern `t ↦ x (ρ' − t)` (from `ρ` to `0`, values
in `[0, ρ]`); on `D_a(α..last)` with the whole `x` (from `0` to `N − 1`). `E` has `N'` links: link
`n` is `E_1(n) ∪ E_2(ρ' − n) ∪ E_3(n)` for `n ≤ ρ'` and `E_3(n)` for `n > ρ'`
(`Chain.threePiece`).

(Batch 115: the hypotheses `IsCompact W` and `0 < ρ` are added; the conclusion is stated as
`TCanFollow`, which is the skeleton's conclusion for every `N'`, `x`, `ρ'`.) -/
theorem exists_tracked_follower [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {R : X} {W : Set X} (hWc : IsCompact W)
    (hA : ∀ i, CoversUpToA (Δ.D i) P R W (1 / ((i : ℝ) + 1)))
    (lv : ℕ) {ρ : Fin (Δ.n lv)} (hρ : 0 < ρ.val) (hcar : Carries (Δ.D lv) P R W ρ) :
    Δ.TCanFollow R W lv (Δ.D lv) ρ := by
  classical
  intro N' x ρ' hx
  obtain ⟨⟨hN'0, hN0, hx0, hxl, hxs⟩, hxρ, hxle⟩ := hx
  have hC : (Δ.D lv).IsFrom P Q := Δ.isFrom lv
  have hRC : R ∈ (Δ.D lv).link ρ := hcar.mem_link
  have hRC0 : R ∉ (Δ.D lv).link ⟨0, hC.1⟩ := hcar.not_mem_first hρ
  have hPR : P ≠ R := fun h => hRC0 (h ▸ hC.2.1)
  have hdPR : 0 < dist P R := dist_pos.mpr hPR
  have hdPQ : 0 < dist P Q := dist_pos.mpr hPQ
  have hρN := ρ.isLt
  -- neighbourhoods in the coarse chain
  obtain ⟨δ₁, hδ₁, hthick⟩ := hWc.exists_thickening_subset_open
    ((Δ.D lv).isOpen_span ⟨0, hC.1⟩ ρ) hcar.2.2.2
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.mp ((Δ.D lv).isOpen ⟨0, hC.1⟩) P hC.2.1
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.mp ((Δ.D lv).isOpen ρ) R hRC
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.mp ((Δ.D lv).isOpen ⟨Δ.n lv - 1, by omega⟩) Q
    hC.2.2.1
  set μ := min (min (min r₀ r₁) (min r₂ δ₁)) (min (dist P R) (dist P Q)) with hμ
  have hμ0 : 0 < μ := by positivity
  have k₀ : μ ≤ r₀ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have k₁ : μ ≤ r₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have k₂ : μ ≤ r₂ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have k₃ : μ ≤ δ₁ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have k₄ : μ ≤ dist P R := (min_le_right _ _).trans (min_le_left _ _)
  have k₅ : μ ≤ dist P Q := (min_le_right _ _).trans (min_le_right _ _)
  -- the deep level `D_a`
  obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := (((Δ.ε_tendsto.eventually_lt_const (by positivity :
    (0 : ℝ) < μ / 4)).and (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const
    (by positivity : (0 : ℝ) < μ / 4))).and (Filter.eventually_gt_atTop lv)).exists
  set ε := Δ.ε a with hεdef
  set η : ℝ := 1 / ((a : ℝ) + 1) with hηdef
  have hε0 : 0 < ε := Δ.ε_pos a
  have hη0 : 0 < η := by positivity
  have hDa : (Δ.D a).IsFrom P Q := Δ.isFrom a
  obtain ⟨hNa, rr, α, h0r, hrα, hsubA, hWA, hspanA, hballA⟩ := hA a
  have hRDa : R ∈ (Δ.D a).link rr := (show Carries (Δ.D a) P R W rr from
    ⟨hNa, h0r, hsubA, hWA⟩).mem_link
  have hcl : ∀ (t : Fin (Δ.n a)) {c : X}, c ∈ (Δ.D a).link t →
      closure ((Δ.D a).link t) ⊆ closedBall c ε :=
    fun t c hc => closure_subset_closedBall_diam (Δ.bdd a t) hc (Δ.diam_le a t)
  have cl0 : closure ((Δ.D a).link ⟨0, hNa⟩) ⊆ closedBall P ε := hcl _ hDa.2.1
  have clr : closure ((Δ.D a).link rr) ⊆ closedBall R ε := hcl _ hRDa
  have clα : closure ((Δ.D a).link α) ⊆ closedBall P η :=
    (closure_mono hballA).trans closure_ball_subset_closedBall
  have cll : closure ((Δ.D a).link ⟨Δ.n a - 1, by omega⟩) ⊆ closedBall Q ε := hcl _ hDa.2.2.1
  have cl0C : closure ((Δ.D a).link ⟨0, hNa⟩) ⊆ (Δ.D lv).link ⟨0, hC.1⟩ :=
    cl0.trans ((closedBall_subset_ball (by linarith)).trans hb₀)
  have clrC : closure ((Δ.D a).link rr) ⊆ (Δ.D lv).link ρ :=
    clr.trans ((closedBall_subset_ball (by linarith)).trans hb₁)
  have clαC : closure ((Δ.D a).link α) ⊆ (Δ.D lv).link ⟨0, hC.1⟩ :=
    clα.trans ((closedBall_subset_ball (by linarith)).trans hb₀)
  have cllC : closure ((Δ.D a).link ⟨Δ.n a - 1, by omega⟩) ⊆
      (Δ.D lv).link ⟨Δ.n lv - 1, by omega⟩ :=
    cll.trans ((closedBall_subset_ball (by linarith)).trans hb₂)
  have disj1 : Disjoint (closure ((Δ.D a).link ⟨0, hNa⟩)) (closure ((Δ.D a).link rr)) :=
    (closedBall_disjoint_closedBall (by linarith)).mono cl0 clr
  have disj2 : Disjoint (closure ((Δ.D a).link rr)) (closure ((Δ.D a).link α)) :=
    (closedBall_disjoint_closedBall (by rw [dist_comm]; linarith)).mono clr clα
  have disj3 : Disjoint (closure ((Δ.D a).link α))
      (closure ((Δ.D a).link ⟨Δ.n a - 1, by omega⟩)) :=
    (closedBall_disjoint_closedBall (by linarith)).mono clα cll
  -- the junction indices
  have hr : 0 < rr.val := by
    by_contra hcon
    have hr0 : rr = ⟨0, hNa⟩ := Fin.ext (by omega)
    rw [hr0] at hRDa
    have := mem_closedBall.mp (cl0 (subset_closure hRDa))
    rw [dist_comm] at this
    linarith
  have hrα2 : rr.val + 2 ≤ α.val := by
    by_contra hcon
    have hle : rr.val ≤ α.val := hrα
    obtain ⟨y, hyα, hyr⟩ := ((Δ.D a).adjacent_iff α rr).mpr (by omega)
    have h1 := mem_closedBall.mp (clr (subset_closure hyr))
    have h2 := mem_ball.mp (hballA hyα)
    have := dist_triangle P y R
    rw [dist_comm] at h2
    linarith
  have hαn : α.val + 1 < Δ.n a := by
    by_contra hcon
    have hαl : α = ⟨Δ.n a - 1, by omega⟩ := Fin.ext (by have := α.isLt; simp only; omega)
    have := mem_ball.mp (hballA (hαl ▸ hDa.2.2.1))
    rw [dist_comm] at this
    linarith
  -- tightness: the links of `D_a` up to `α` lie in links of `C` of index `≤ ρ`
  have tight : ∀ t : Fin (Δ.n a), t ≤ α → ∃ s, s ≤ ρ ∧ (Δ.D a).link t ⊆ (Δ.D lv).link s := by
    intro t htα
    obtain ⟨j, hj⟩ := Δ.refines_of_le ha3.le t
    refine (Δ.D lv).exists_link_le_of_subset_span (a := ⟨0, hC.1⟩) hj fun q hq => hthick ?_
    exact thickening_mono (by linarith) W
      (hspanA (Chain.mem_span.mpr ⟨t, Fin.le_def.mpr (Nat.zero_le _), htα, hq⟩))
  -- Theorem 5 on the three stretches
  have hρ'1 : ∀ e : Fin (ρ'.val + 1), e.val < N' := fun e => by have := e.isLt; omega
  let x₁ : Fin (ρ'.val + 1) → Fin (Δ.n lv) := fun e => x ⟨e.val, hρ'1 e⟩
  have hx₁ : Description.IsPatternFromTo x₁ ⟨0, hN0⟩ ρ := by
    refine ⟨by omega, hx0, ?_, fun t => ⟨Fin.le_def.mpr (Nat.zero_le _),
      hxle _ (Fin.le_def.mpr (by have := t.isLt; simp only; omega))⟩,
      fun t t' h => hxs _ _ (by simp only; omega)⟩
    show x ⟨ρ'.val + 1 - 1, _⟩ = ρ
    rw [show (⟨ρ'.val + 1 - 1, _⟩ : Fin N') = ρ' from Fin.ext (by simp)]
    exact hxρ
  let z : Fin (ρ'.val + 1) → Fin (Δ.n lv) := fun e => Fin.rev (x ⟨ρ'.val - e.val, by omega⟩)
  have hz : Description.IsPatternFromTo z (Fin.rev ρ) (Fin.rev ⟨0, hN0⟩) := by
    refine ⟨by omega, ?_, ?_, fun t => ⟨?_, ?_⟩, fun t t' h => ?_⟩
    · show Fin.rev (x ⟨ρ'.val - 0, _⟩) = Fin.rev ρ
      rw [show (⟨ρ'.val - 0, _⟩ : Fin N') = ρ' from Fin.ext (by simp), hxρ]
    · show Fin.rev (x ⟨ρ'.val - (ρ'.val + 1 - 1), _⟩) = Fin.rev ⟨0, hN0⟩
      rw [show (⟨ρ'.val - (ρ'.val + 1 - 1), _⟩ : Fin N') = ⟨0, hN'0⟩ from Fin.ext (by simp),
        hx0]
    · exact Fin.rev_le_rev.mpr (hxle _ (Fin.le_def.mpr (by simp only; omega)))
    · exact Fin.rev_le_rev.mpr (Fin.le_def.mpr (Nat.zero_le _))
    · have := hxs ⟨ρ'.val - t'.val, by omega⟩ ⟨ρ'.val - t.val, by omega⟩ (by
        simp only; have := t'.isLt; omega)
      simp only [z, Fin.val_rev]
      have := (x ⟨ρ'.val - t.val, by omega⟩).isLt
      have := (x ⟨ρ'.val - t'.val, by omega⟩).isLt
      omega
  have hrevC : ∀ s : Fin (Δ.n lv), (Δ.D lv).reverse.link (Fin.rev s) = (Δ.D lv).link s := by
    intro s
    rw [Chain.reverse_link, Fin.rev_rev]
  have T1 := Δ.theorem5_gen (Δ.D lv) a x₁ ⟨0, hN0⟩ ρ ⟨0, hNa⟩ rr hx₁ h0r
    (fun t _ ht => by
      obtain ⟨s, hs, hts⟩ := tight t (ht.trans hrα)
      exact ⟨s, Fin.le_def.mpr (Nat.zero_le _), hs, hts⟩) cl0C clrC disj1
  have T2 := Δ.theorem5_gen (Δ.D lv).reverse a z (Fin.rev ρ) (Fin.rev ⟨0, hN0⟩) rr α hz hrα
    (fun t _ ht => by
      obtain ⟨s, hs, hts⟩ := tight t ht
      exact ⟨Fin.rev s, Fin.rev_le_rev.mpr hs, Fin.rev_le_rev.mpr (Fin.le_def.mpr
        (Nat.zero_le _)), by rw [hrevC]; exact hts⟩)
    (by rw [hrevC]; exact clrC) (by rw [hrevC]; exact clαC) disj2
  have T3 := Δ.theorem5_gen (Δ.D lv) a x ⟨0, hN0⟩ ⟨Δ.n lv - 1, by omega⟩ α
    ⟨Δ.n a - 1, by omega⟩ ⟨hN'0, hx0, hxl, fun t => ⟨Fin.le_def.mpr (Nat.zero_le _),
      Fin.le_def.mpr (by have := (x t).isLt; simp only; omega)⟩, hxs⟩
    (Fin.le_def.mpr (by simp only; omega))
    (fun t _ _ => by
      obtain ⟨s, hs⟩ := Δ.refines_of_le ha3.le t
      exact ⟨s, Fin.le_def.mpr (Nat.zero_le _), Fin.le_def.mpr (by
        have := s.isLt; simp only; omega), hs⟩) clαC cllC disj3
  obtain ⟨j, ⟨⟨⟨E₁, f₁, c₁, d₁, e₁u, e₁v⟩, ⟨E₂, f₂, c₂, d₂, e₂u, e₂v⟩⟩,
    ⟨E₃, f₃, c₃, d₃, e₃u, e₃v⟩⟩, hja⟩ :=
    (((T1.and T2).and T3).and (Filter.eventually_gt_atTop a)).exists
  -- the deeper level `D_j` covers `R` and `W`
  obtain ⟨hNj, rj, -, h0rj, -, hsubj, hWj, -, -⟩ := hA j
  have hRF : R ∈ (Δ.D j).union := mem_iUnion.mpr ⟨rj, (show Carries (Δ.D j) P R W rj from
    ⟨hNj, h0rj, hsubj, hWj⟩).mem_link⟩
  have hWF : W ⊆ (Δ.D j).union := hWj.trans ((Δ.D j).span_subset_union _ _)
  obtain ⟨E, hE1, hE2, hE3, h0, hE4, hE5⟩ := Chain.threePiece (Δ.D lv) hC ρ hρ hRC0 x ρ'
    (fun _ => hx0) hxρ (Δ.D a) hDa rr α hr hrα2 hαn hRDa
    (fun w hw => by
      obtain ⟨s, -, hs, hws⟩ := Chain.mem_span.mp (hWA hw)
      exact ⟨s, hs, hws⟩)
    (Δ.D j) (Δ.isFrom j) (Δ.refines_of_le hja.le) hRF hWF E₁ E₂ E₃ f₁
    (fun e => (f₂ e).trans (by show (Δ.D lv).reverse.link (Fin.rev (x _)) ⊆ _; rw [hrevC]))
    f₃ c₁ c₂ c₃ d₁ d₂ d₃ e₁u e₁v e₂u e₂v e₃u e₃v
  exact ⟨j, lt_trans ha3 hja, E, hE1, hE2, hE3, ρ'.pos, h0, hE4, hE5⟩

/-! ### The tracked alternating construction and Theorem 14 -/

/-- A rung of the tracked construction: as `Rung`, with a common `R`-index `ρ` at which both
chains carry their `(P_i, R_i, W_i)`, and with the following side able to follow tracked
patterns (`TCanFollow`). -/
structure TRung {P₁ Q₁ P₂ Q₂ : X} (Δ₁ : Description X P₁ Q₁) (Δ₂ : Description X P₂ Q₂)
    (R₁ R₂ : X) (W₁ W₂ : Set X) where
  N : ℕ
  C₁ : Chain X N
  C₂ : Chain X N
  isFrom₁ : C₁.IsFrom P₁ Q₁
  isFrom₂ : C₂.IsFrom P₂ Q₂
  lv₁ : ℕ
  lv₂ : ℕ
  cons₁ : C₁.IsConsolidationOf (Δ₁.D lv₁)
  cons₂ : C₂.IsConsolidationOf (Δ₂.D lv₂)
  ρ : Fin N
  carries₁ : Carries C₁ P₁ R₁ W₁ ρ
  carries₂ : Carries C₂ P₂ R₂ W₂ ρ
  mesh : ℝ
  mfollow : ℝ
  mesh_pos : 0 < mesh
  mfollow_pos : 0 < mfollow
  diam₁ : ∀ t, Metric.diam (C₁.link t) ≤ mesh
  diam₂ : ∀ t, Metric.diam (C₂.link t) ≤ mesh
  /-- the side that will follow can follow tracked patterns, with the sharper mesh bound -/
  follow : (Δ₁.TCanFollow R₁ W₁ lv₁ C₁ ρ ∧ ∀ t, Metric.diam (C₁.link t) ≤ mfollow) ∨
           (Δ₂.TCanFollow R₂ W₂ lv₂ C₂ ρ ∧ ∀ t, Metric.diam (C₂.link t) ≤ mfollow)

/-- A level of an `A`-covering description whose mesh is below `dist P R` has its `R`-index
positive. -/
theorem Carries.pos_of_lt {N : ℕ} {C : Chain X N} {P Q R : X} {W : Set X} {ρ : Fin N}
    (h : Carries C P R W ρ) (hC : C.IsFrom P Q) {ε : ℝ} (hb : ∀ t, Bornology.IsBounded (C.link t))
    (hd : ∀ t, diam (C.link t) ≤ ε) (hε : ε < dist P R) : 0 < ρ.val := by
  by_contra hcon
  have hR := h.mem_link
  rw [show ρ = ⟨0, hC.1⟩ from Fin.ext (by simp only; omega)] at hR
  have := (dist_le_diam_of_mem (hb _) hC.2.1 hR).trans (hd _)
  linarith

/-- **The refining half-step.** A consolidation `C` of a level of an `A`-covering description,
carrying `(P, R, W)` at `ρ`, is refined by a deeper level of mesh `≤ δ` along a pattern tracking
the `R`-index of that level (positive) to `ρ`. -/
theorem exists_tracked_refinement [CompactSpace X] {P Q : X} (Δ : Description X P Q) {R : X}
    {W : Set X} (hPR : P ≠ R) (hWc : IsCompact W)
    (hA : ∀ i, CoversUpToA (Δ.D i) P R W (1 / ((i : ℝ) + 1)))
    {N lv : ℕ} {C : Chain X N} (hC : C.IsFrom P Q) (hcons : C.IsConsolidationOf (Δ.D lv))
    {ρ : Fin N} (hcar : Carries C P R W ρ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c, lv ≤ c ∧ Δ.ε c ≤ δ ∧ ∃ ρc : Fin (Δ.n c), ∃ x : Fin (Δ.n c) → Fin N,
      IsTrackedPattern x ρc ρ ∧ (Δ.D c).FollowsPattern x C ∧ Carries (Δ.D c) P R W ρc ∧
      0 < ρc.val := by
  have hdPR : 0 < dist P R := dist_pos.mpr hPR
  obtain ⟨δ₂, hδ₂, hthick⟩ := hWc.exists_thickening_subset_open
    (C.isOpen_span ⟨0, hcar.1⟩ ρ) hcar.2.2.2
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.mp (C.isOpen ρ) R hcar.mem_link
  obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := (((Δ.ε_tendsto.eventually_lt_const (by positivity :
    (0 : ℝ) < min (min δ r₁) (dist P R))).and
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ₂)).and
    (Filter.eventually_ge_atTop lv)).exists
  have hcδ : Δ.ε c ≤ δ := hc1.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcr : Δ.ε c < r₁ := hc1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcd : Δ.ε c < dist P R := hc1.trans_le (min_le_right _ _)
  obtain ⟨ρc, x, hxt, hfol, hcarc⟩ := exists_trackedPattern_of_refines hC (Δ.isFrom c)
    ((Δ.refines_of_le hc3).trans hcons.1) hcar (hA c) ((thickening_mono hc2.le W).trans hthick)
    (fun t hRt q hq => hb₁ (mem_ball.mpr ((dist_le_diam_of_mem (Δ.bdd c t) hq hRt).trans_lt
      ((Δ.diam_le c t).trans_lt hcr))))
  exact ⟨c, hc3, hcδ, ρc, x, hxt, hfol, hcarc,
    hcarc.pos_of_lt (Δ.isFrom c) (Δ.bdd c) (Δ.diam_le c) hcd⟩

/-- The base rung: a level of `Δ₁` of small mesh, matched on side 2 by the tracked follower
applied to a coarse level of `Δ₂` with an explicit pattern tracking the `R`-indices.

(Batch 115: the hypotheses `P_i ≠ R_i`, `R₁ ≠ Q₁` and compactness of `W_i` are added.) -/
theorem TRung.exists_base [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X} (Δ₁ : Description X P₁ Q₁)
    (Δ₂ : Description X P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) {R₁ R₂ : X} {W₁ W₂ : Set X}
    (hPR₁ : P₁ ≠ R₁) (hPR₂ : P₂ ≠ R₂) (hRQ₁ : R₁ ≠ Q₁) (hW₁c : IsCompact W₁)
    (hW₂c : IsCompact W₂)
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1))) :
    ∃ r : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂, r.mfollow = 1 / 2 := by
  classical
  have hdPR₁ : 0 < dist P₁ R₁ := dist_pos.mpr hPR₁
  have hdPR₂ : 0 < dist P₂ R₂ := dist_pos.mpr hPR₂
  have hdRQ₁ : 0 < dist R₁ Q₁ := dist_pos.mpr hRQ₁
  -- a coarse level of `Δ₂` with positive `R`-index
  obtain ⟨b, hb⟩ := (Δ₂.ε_tendsto.eventually_lt_const hdPR₂).exists
  obtain ⟨hNb, ρb, -, h0b, -, hsubb, hWb, -, -⟩ := hA₂ b
  have hcarb : Carries (Δ₂.D b) P₂ R₂ W₂ ρb := ⟨hNb, h0b, hsubb, hWb⟩
  have hρb := hcarb.pos_of_lt (Δ₂.isFrom b) (Δ₂.bdd b) (Δ₂.diam_le b) hb
  -- a fine level of `Δ₁` with more links before and after its `R`-link
  obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := (((Δ₁.ε_tendsto.eventually_lt_const (by norm_num :
    (0 : ℝ) < 1 / 2)).and (Δ₁.ε_tendsto.eventually_lt_const (by positivity :
    (0 : ℝ) < dist P₁ R₁ / (ρb.val + 2)))).and (Δ₁.ε_tendsto.eventually_lt_const
    (by positivity : (0 : ℝ) < dist R₁ Q₁ / (Δ₂.n b + 1)))).exists
  have hεa := Δ₁.ε_pos a
  obtain ⟨hNa, ρa, -, h0a, -, hsuba, hWa, -, -⟩ := hA₁ a
  have hcara : Carries (Δ₁.D a) P₁ R₁ W₁ ρa := ⟨hNa, h0a, hsuba, hWa⟩
  have hDa := Δ₁.isFrom a
  have hρab : ρb.val < ρa.val := by
    by_contra hcon
    have h1 := (Δ₁.D a).dist_le_of_mem_links' (Δ₁.bdd a) (Δ₁.diam_le a) ρb.val ⟨0, hNa⟩ ρa
      (by simp only; omega) hDa.2.1 hcara.mem_link
    have h2 : Δ₁.ε a * (ρb.val + 2) < dist P₁ R₁ := (lt_div_iff₀ (by positivity)).mp ha2
    have h3 : ((ρb.val : ℕ) : ℝ) + 1 ≤ ρb.val + 2 := by linarith
    nlinarith
  have hna : Δ₂.n b < Δ₁.n a - ρa.val := by
    by_contra hcon
    have := ρa.isLt
    have h1 := (Δ₁.D a).dist_le_of_mem_links' (Δ₁.bdd a) (Δ₁.diam_le a) (Δ₂.n b - 1) ρa
      ⟨Δ₁.n a - 1, by omega⟩ (by simp only; omega) hcara.mem_link hDa.2.2.1
    have h2 : Δ₁.ε a * (Δ₂.n b + 1) < dist R₁ Q₁ := (lt_div_iff₀ (by positivity)).mp ha3
    have h3 : (((Δ₂.n b - 1 : ℕ) : ℝ) + 1) ≤ Δ₂.n b + 1 := by
      have : ((Δ₂.n b - 1 : ℕ) : ℝ) ≤ Δ₂.n b := by exact_mod_cast Nat.sub_le _ _
      linarith
    nlinarith
  -- the pattern of `Δ₁.D a` into `Δ₂.D b`
  have hρbN := ρb.isLt
  let y : Fin (Δ₁.n a) → Fin (Δ₂.n b) := fun t =>
    ⟨if t.val ≤ ρa.val then min t.val ρb.val else min (ρb.val + (t.val - ρa.val)) (Δ₂.n b - 1),
      by split_ifs <;> omega⟩
  have hy : IsTrackedPattern y ρa ρb := by
    refine ⟨⟨hNa, hNb, Fin.ext (by simp [y]), Fin.ext ?_, fun t t' htt => ?_⟩,
      Fin.ext (by simp only [y, le_refl, if_true]; omega), fun t ht => ?_⟩
    · have := ρa.isLt
      simp only [y]
      split_ifs <;> omega
    · simp only [y]
      split_ifs <;> omega
    · have ht' : t.val ≤ ρa.val := ht
      show (y t).val ≤ ρb.val
      simp only [y, if_pos ht']
      omega
  obtain ⟨a', -, E, hE1, hE2, hE3, hE4⟩ :=
    exists_tracked_follower Δ₂ hPQ₂ hW₂c hA₂ b hρb hcarb _ y ρa hy
  have huniv : ∀ t, Metric.diam (E.link t) ≤ Metric.diam (Set.univ : Set X) + 1 := by
    intro t
    have := Metric.diam_mono (Set.subset_univ (E.link t)) isBounded_of_compactSpace
    linarith
  exact ⟨{ N := Δ₁.n a
           C₁ := Δ₁.D a
           C₂ := E
           isFrom₁ := hDa
           isFrom₂ := hE1
           lv₁ := a
           lv₂ := a'
           cons₁ := Chain.isConsolidationOf_self _
           cons₂ := hE2
           ρ := ρa
           carries₁ := hcara
           carries₂ := hE4
           mesh := max (1 / 2) (Metric.diam (Set.univ : Set X) + 1)
           mfollow := 1 / 2
           mesh_pos := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
           mfollow_pos := by norm_num
           diam₁ := fun t => ((Δ₁.diam_le a t).trans ha1.le).trans (le_max_left _ _)
           diam₂ := fun t => (huniv t).trans (le_max_right _ _)
           follow := Or.inl ⟨exists_tracked_follower Δ₁ hPQ₁ hW₁c hA₁ a (by omega) hcara,
             fun t => (Δ₁.diam_le a t).trans ha1.le⟩ }, rfl⟩

/-- The next rung: the consolidated side is refined by a tight deep level of its description
(`exists_tracked_refinement`, from `exists_trackedPattern_of_refines`), the level side follows
with `exists_tracked_follower`.

(Batch 115: the hypotheses `P_i ≠ R_i` and compactness of `W_i` are added.) -/
theorem TRung.exists_next [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X} {Δ₁ : Description X P₁ Q₁}
    {Δ₂ : Description X P₂ Q₂} (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) {R₁ R₂ : X} {W₁ W₂ : Set X}
    (hPR₁ : P₁ ≠ R₁) (hPR₂ : P₂ ≠ R₂) (hW₁c : IsCompact W₁) (hW₂c : IsCompact W₂)
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1)))
    (r : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂, r'.mfollow = δ ∧ r'.mesh = max δ r.mfollow ∧
      ∃ x : Fin r'.N → Fin r.N, r'.C₁.FollowsPattern x r.C₁ ∧ r'.C₂.FollowsPattern x r.C₂ ∧
        x r'.ρ = r.ρ := by
  have hmax : 0 < max δ r.mfollow := lt_of_lt_of_le hδ (le_max_left _ _)
  rcases r.follow with ⟨hcan, hdf⟩ | ⟨hcan, hdf⟩
  · obtain ⟨c, -, hεc, ρc, x, hxt, hfB, hcarc, hρc⟩ :=
      exists_tracked_refinement Δ₂ hPR₂ hW₂c hA₂ r.isFrom₂ r.cons₂ r.carries₂ hδ
    obtain ⟨lv, -, CA, hCA1, hCA2, hfA, hcarA⟩ := hcan _ x ρc hxt
    exact ⟨{ N := Δ₂.n c
             C₁ := CA
             C₂ := Δ₂.D c
             isFrom₁ := hCA1
             isFrom₂ := Δ₂.isFrom c
             lv₁ := lv
             lv₂ := c
             cons₁ := hCA2
             cons₂ := Chain.isConsolidationOf_self _
             ρ := ρc
             carries₁ := hcarA
             carries₂ := hcarc
             mesh := max δ r.mfollow
             mfollow := δ
             mesh_pos := hmax
             mfollow_pos := hδ
             diam₁ := fun t => (Chain.diam_le_of_followsPattern x hfA hdf
               (fun _ => isBounded_of_compactSpace) t).trans (le_max_right _ _)
             diam₂ := fun t => ((Δ₂.diam_le c t).trans hεc).trans (le_max_left _ _)
             follow := Or.inr ⟨exists_tracked_follower Δ₂ hPQ₂ hW₂c hA₂ c hρc hcarc,
               fun t => (Δ₂.diam_le c t).trans hεc⟩ }, rfl, rfl, x, hfA, hfB, hxt.2.1⟩
  · obtain ⟨c, -, hεc, ρc, x, hxt, hfB, hcarc, hρc⟩ :=
      exists_tracked_refinement Δ₁ hPR₁ hW₁c hA₁ r.isFrom₁ r.cons₁ r.carries₁ hδ
    obtain ⟨lv, -, CA, hCA1, hCA2, hfA, hcarA⟩ := hcan _ x ρc hxt
    exact ⟨{ N := Δ₁.n c
             C₁ := Δ₁.D c
             C₂ := CA
             isFrom₁ := Δ₁.isFrom c
             isFrom₂ := hCA1
             lv₁ := c
             lv₂ := lv
             cons₁ := Chain.isConsolidationOf_self _
             cons₂ := hCA2
             ρ := ρc
             carries₁ := hcarc
             carries₂ := hcarA
             mesh := max δ r.mfollow
             mfollow := δ
             mesh_pos := hmax
             mfollow_pos := hδ
             diam₁ := fun t => ((Δ₁.diam_le c t).trans hεc).trans (le_max_left _ _)
             diam₂ := fun t => (Chain.diam_le_of_followsPattern x hfA hdf
               (fun _ => isBounded_of_compactSpace) t).trans (le_max_right _ _)
             follow := Or.inl ⟨exists_tracked_follower Δ₁ hPQ₁ hW₁c hA₁ c hρc hcarc,
               fun t => (Δ₁.diam_le c t).trans hεc⟩ }, rfl, rfl, x, hfB, hfA, hxt.2.1⟩

/-- **Theorem 12 with a tracked point**: two `A`-covering descriptions give a homeomorphism
carrying `P₁, Q₁, R₁` to `P₂, Q₂, R₂` (the construction of `Description.exists_homeomorph` on
`TRung`s; `MatchingCovers.exists_homeomorph`'s tracking clause with the index sequence `k ↦ ρ_k`
for `R₁`, `R₂`).

(Batch 115: the hypotheses `P_i ≠ R_i`, `R₁ ≠ Q₁` and compactness of `W_i` are added.) -/
theorem exists_homeomorph_tracked [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X}
    (Δ₁ : Description X P₁ Q₁) (Δ₂ : Description X P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂)
    {R₁ R₂ : X} {W₁ W₂ : Set X} (hR₁ : R₁ ∈ Δ₁.M) (hR₂ : R₂ ∈ Δ₂.M)
    (hPR₁ : P₁ ≠ R₁) (hPR₂ : P₂ ≠ R₂) (hRQ₁ : R₁ ≠ Q₁) (hW₁c : IsCompact W₁)
    (hW₂c : IsCompact W₂)
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1))) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M, T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧
      T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ ∧ T ⟨R₁, hR₁⟩ = ⟨R₂, hR₂⟩ := by
  classical
  -- the tracked alternating construction
  obtain ⟨r₀, hr₀⟩ := TRung.exists_base Δ₁ Δ₂ hPQ₁ hPQ₂ hPR₁ hPR₂ hRQ₁ hW₁c hW₂c hA₁ hA₂
  have hnext : ∀ (k : ℕ) (r : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂), ∃ r' : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂,
      r'.mfollow = (1 / 2 : ℝ) ^ (k + 2) ∧ r'.mesh = max ((1 / 2 : ℝ) ^ (k + 2)) r.mfollow ∧
      ∃ x : Fin r'.N → Fin r.N, r'.C₁.FollowsPattern x r.C₁ ∧ r'.C₂.FollowsPattern x r.C₂ ∧
        x r'.ρ = r.ρ :=
    fun k r => TRung.exists_next hPQ₁ hPQ₂ hPR₁ hPR₂ hW₁c hW₂c hA₁ hA₂ r (by positivity)
  choose nxt hmf hmesh hlink using hnext
  set Rg : ℕ → TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂ := fun k => Nat.rec r₀ (fun k r => nxt k r) k
  -- the mesh bookkeeping
  have hmfollow : ∀ k, (Rg k).mfollow = (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    cases k with
    | zero => simpa using hr₀
    | succ k => exact hmf k (Rg k)
  have hmeshk : ∀ k, (Rg (k + 1)).mesh = (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    rw [show (Rg (k + 1)).mesh = max ((1 / 2 : ℝ) ^ (k + 2)) (Rg k).mfollow from hmesh k (Rg k),
      hmfollow k]
    refine max_eq_right ?_
    have : (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) := by ring
    rw [this]
    nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) (k + 1)]
  have hεpos : ∀ i, 0 < 2 * (Rg i).mesh := fun i => by
    have := (Rg i).mesh_pos; linarith
  have hsum : Summable (fun i => 2 * (Rg i).mesh) := by
    rw [← summable_nat_add_iff 1]
    have hfun : (fun k => 2 * (Rg (k + 1)).mesh) = fun k => (1 / 2 : ℝ) ^ k := by
      funext k
      rw [hmeshk k]
      ring
    rw [hfun]
    exact summable_geometric_two
  -- the matching covers
  have hN : ∀ i, 0 < (Rg i).N := fun i => (Rg i).isFrom₁.1
  have hdiam₁ : ∀ i (k : Fin (Rg i).N), Metric.diam ((Rg i).C₁.link k) ≤ 2 * (Rg i).mesh := by
    intro i k
    have := (Rg i).diam₁ k
    have := (Rg i).mesh_pos
    linarith
  have hdiam₂ : ∀ i (k : Fin (Rg i).N), Metric.diam ((Rg i).C₂.link k) ≤ 2 * (Rg i).mesh := by
    intro i k
    have := (Rg i).diam₂ k
    have := (Rg i).mesh_pos
    linarith
  have hlt₁ : ∀ i (k : Fin (Rg i).N), Metric.diam ((Rg i).C₁.link k) < 2 * (Rg i).mesh := by
    intro i k
    have := (Rg i).diam₁ k
    have := (Rg i).mesh_pos
    linarith
  have hlt₂ : ∀ i (k : Fin (Rg i).N), Metric.diam ((Rg i).C₂.link k) < 2 * (Rg i).mesh := by
    intro i k
    have := (Rg i).diam₂ k
    have := (Rg i).mesh_pos
    linarith
  obtain ⟨T, hT⟩ := MatchingCovers.exists_homeomorph
    (M₁ := Δ₁.M) (M₂ := Δ₂.M) (ε := fun i => 2 * (Rg i).mesh)
    { N := fun i => (Rg i).N
      x₁ := fun i => (Rg i).C₁.link
      x₂ := fun i => (Rg i).C₂.link
      open₁ := fun i => (Rg i).C₁.isOpen
      open₂ := fun i => (Rg i).C₂.isOpen
      cover₁ := fun i => Δ₁.M_subset_consolidation (Rg i).cons₁
      cover₂ := fun i => Δ₂.M_subset_consolidation (Rg i).cons₂
      meet₁ := fun i => Δ₁.consolidation_link_inter_M_nonempty (Rg i).cons₁
      meet₂ := fun i => Δ₂.consolidation_link_inter_M_nonempty (Rg i).cons₂
      bdd₁ := fun _ _ => isBounded_of_compactSpace
      bdd₂ := fun _ _ => isBounded_of_compactSpace
      diam₁ := hdiam₁
      diam₂ := hdiam₂
      match₁ := by
        intro i j k hjk
        obtain ⟨x, hx₁, hx₂, -⟩ := hlink i (Rg i)
        exact Chain.pattern_matching x hx₁ hx₂ (hlt₂ i)
          (fun _ => isBounded_of_compactSpace) j k hjk
      match₂ := by
        intro i j k hjk
        obtain ⟨x, hx₁, hx₂, -⟩ := hlink i (Rg i)
        exact Chain.pattern_matching x hx₂ hx₁ (hlt₁ i)
          (fun _ => isBounded_of_compactSpace) j k hjk }
    Δ₁.isCompact_M Δ₂.isCompact_M hεpos hsum
  -- `P`, `Q` are tracked by the constant index sequences, `R` by the `R`-indices
  refine ⟨T, ?_, ?_, ?_⟩
  · exact hT (fun i => ⟨0, hN i⟩) _ _ (fun i => (Rg i).isFrom₁.2.1)
      (fun i => (Rg i).isFrom₂.2.1)
  · exact hT (fun i => ⟨(Rg i).N - 1, by show (Rg i).N - 1 < (Rg i).N; have := hN i; omega⟩) _ _
      (fun i => (Rg i).isFrom₁.2.2.1) (fun i => (Rg i).isFrom₂.2.2.1)
  · exact hT (fun i => (Rg i).ρ) _ _ (fun i => (Rg i).carries₁.mem_link)
      (fun i => (Rg i).carries₂.mem_link)

namespace Description

variable {P Q : X}

/-- **Bing 1948, Theorem 14** (formerly the open `Description.theorem14` of `Theorem14.lean`,
statement unchanged): `W_i` irreducible between `P_i` and `R_i` (`exists_irreducible`, inside a
proper subcontinuum through both), the two `A`-covering descriptions
(`exists_description_coveringA`), and the tracked homeomorphism (`exists_homeomorph_tracked`),
transported to `Δ.M` through `Δ'_i.M = Δ.M`. -/
theorem theorem14 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem14Statement Δ := by
  intro P₁ Q₁ R₁ P₂ Q₂ R₂ hP₁ hQ₁ hR₁ hP₂ hQ₂ hR₂ hR₁c hR₂c hQ₁c hQ₂c hPR₁ hPR₂
  -- the irreducible subcontinua
  have hW : ∀ {P' R : X}, R ∈ composant Δ.M P' → ∃ W, W ⊆ Δ.M ∧ IsIrreducibleBetween W P' R := by
    intro P' R hRc
    obtain ⟨K, ⟨hK, hKM, -, hPK⟩, hRK⟩ := mem_sUnion.mp hRc
    obtain ⟨W, hWK, hWirr⟩ := exists_irreducible hK hPK hRK
    exact ⟨W, hWK.trans hKM, hWirr⟩
  -- `P' ≠ Q'`: `{P'}` is a proper subcontinuum through `P'`
  have hPQ' : ∀ {P' Q' R : X}, P' ∈ Δ.M → R ∈ Δ.M → P' ≠ R → Q' ∉ composant Δ.M P' →
      P' ≠ Q' := by
    rintro P' Q' R hP' hR hPR hQc rfl
    refine hQc (mem_sUnion.mpr ⟨{P'}, ⟨⟨isCompact_singleton, isConnected_singleton⟩,
      singleton_subset_iff.mpr hP', fun h => hPR ?_, rfl⟩, rfl⟩)
    have : R ∈ ({P'} : Set X) := h ▸ hR
    exact (mem_singleton_iff.mp this).symm
  obtain ⟨W₁, hW₁M, hW₁⟩ := hW hR₁c
  obtain ⟨W₂, hW₂M, hW₂⟩ := hW hR₂c
  obtain ⟨Δ₁, hM₁, hA₁⟩ :=
    Δ.exists_description_coveringA hPQ hP₁ hQ₁ hR₁ hR₁c hQ₁c hPR₁ hW₁M hW₁
  obtain ⟨Δ₂, hM₂, hA₂⟩ :=
    Δ.exists_description_coveringA hPQ hP₂ hQ₂ hR₂ hR₂c hQ₂c hPR₂ hW₂M hW₂
  obtain ⟨T, hTP, hTQ, hTR⟩ := exists_homeomorph_tracked Δ₁ Δ₂ (hPQ' hP₁ hR₁ hPR₁ hQ₁c)
    (hPQ' hP₂ hR₂ hPR₂ hQ₂c) (R₁ := R₁) (R₂ := R₂) (hM₁ ▸ hR₁) (hM₂ ▸ hR₂) hPR₁ hPR₂
    (fun h => hQ₁c (h ▸ hR₁c)) hW₁.1.1 hW₂.1.1 hA₁ hA₂
  refine ⟨(Homeomorph.setCongr hM₁.symm).trans (T.trans (Homeomorph.setCongr hM₂)), ?_, ?_, ?_⟩
  · exact Subtype.ext (by have := congrArg Subtype.val hTP; exact this)
  · exact Subtype.ext (by have := congrArg Subtype.val hTQ; exact this)
  · exact Subtype.ext (by have := congrArg Subtype.val hTR; exact this)

/-- **Bing 1948, Theorem 15** (formerly conditional on the open `theorem14`, statement
unchanged): `theorem15_of_theorem14` with `theorem14`. -/
theorem theorem15 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {W₁ W₂ : Set X} (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂)
    (hW₁M : W₁ ⊆ Δ.M) (hW₂M : W₂ ⊆ Δ.M) (hW₁ne : W₁ ≠ Δ.M) (hW₂ne : W₂ ≠ Δ.M)
    (hnd₁ : W₁.Nontrivial) (hnd₂ : W₂.Nontrivial)
    {P₁ P₂ Q₁ Q₂ : X} (hP₁ : P₁ ∈ W₁) (hP₂ : P₂ ∈ W₂) (hQ₁ : Q₁ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M)
    (hQ₁c : Q₁ ∉ composant Δ.M P₁) (hQ₂c : Q₂ ∉ composant Δ.M P₂) :
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hW₁M hP₁⟩ = ⟨P₂, hW₂M hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧
      (fun w : Δ.M => (T w : X)) '' {w | (w : X) ∈ W₁} = W₂ :=
  theorem15_of_theorem14 Δ hPQ (theorem14 Δ hPQ) hW₁ hW₂ hW₁M hW₂M hW₁ne hW₂ne hnd₁ hnd₂
    hP₁ hP₂ hQ₁ hQ₂ hQ₁c hQ₂c

end Description

end HPC
