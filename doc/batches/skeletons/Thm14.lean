import HPC.PseudoArc.Lehner
import HPC.PseudoArc.Uniqueness

/-!
# Batch 115: Bing 1948, Theorem 14 — the alternating construction with the position of `R` carried

Skeleton (save as `HPC/PseudoArc/Thm14.lean`; add `import HPC.PseudoArc.Thm14` at the end of the
root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with
the change recorded. Existing files edited only as the commission says (the open `theorem14` and
the conditional `theorem15` move here from `Theorem14.lean` once proved).

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
which lie in links of `E`); and `g_{y_1} ⊆ f_2 ⊆ e_1 ⊆ ball P' ε` once the window condition is
taken with four links (`F(1,4)` in one link of `E`, which contains `P'`, hence is `e_1`). Take
`a` = the index of `g_{y_1}` in `D` and `ε ≤ 1/(L+1)`. -/
theorem Description.covering_stepA [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Δ.CoveringStepA P' Q' R W := by
  sorry

/-- `exists_description_of_steps` with a property depending on the level `L` of the step: the
level `i` of the description is built by the step at some `L ≥ i`. -/
theorem Description.exists_description_of_steps' [CompactSpace X] {P Q : X}
    (Δ : Description X P Q) {R S : X} (G : ℕ → (N : ℕ) → Chain X N → Prop)
    (hstep : ∀ L, ∃ k, L < k ∧ ∃ N, ∃ F : Chain X N, F.IsFrom R S ∧ F.IsConsolidationOf (Δ.D k) ∧
      (∀ u, ∃ t, closure (F.link u) ⊆ (Δ.D L).link t) ∧
      (∀ u, diam (F.link u) ≤ 1 / ((L : ℝ) + 1)) ∧ G L N F) :
    ∃ Δ' : Description X R S, Δ'.M = Δ.M ∧ ∀ i, ∃ L, i ≤ L ∧ G L (Δ'.n i) (Δ'.D i) := by
  sorry

/-- **The `A`-covering description**: a description of `M` from `P'` to `Q'` every level `i` of
which covers `W` up to `R` tightly, at radius `≤ 1/(i+1)`, with a return point. -/
theorem Description.exists_description_coveringA [CompactSpace X] {P Q : X}
    (Δ : Description X P Q) (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M)
    (hR : R ∈ Δ.M) (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, CoversUpToA (Δ'.D i) P' R W (1 / ((i : ℝ) + 1)) := by
  sorry

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

/-- **The refinement pattern of a tight level tracks.** If `C` carries `(P, R, W)` at `ρ` and a
fine level `D` of an `A`-covering description (radius `η`, with `thickening η W ⊆ C.span 0 ρ` and
the link of `R` in `D` inside `C.link ρ`) refines `C`, then there is a pattern `x` with
`D.FollowsPattern x C` tracking `ρ_D ↦ ρ`, where `ρ_D` is the `R`-index of `D`. (A link of `D` in
`C.span 0 ρ` and in `C.link j` with `j > ρ` lies in `C.link (j) ∩ C.link ρ`, so `ρ` may be chosen.) -/
theorem exists_trackedPattern_of_refines {N N' : ℕ} {C : Chain X N} {D : Chain X N'}
    {P Q R : X} {W : Set X} (hC : C.IsFrom P Q) (hD : D.IsFrom P Q) (href : D.Refines C)
    {ρ : Fin N} (hcar : Carries C P R W ρ) {η : ℝ} (hη : 0 < η)
    (hDA : CoversUpToA D P R W η)
    (hthick : thickening η W ⊆ C.span ⟨0, hcar.1⟩ ρ)
    (hRlink : ∀ t, R ∈ D.link t → D.link t ⊆ C.link ρ) :
    ∃ ρ' : Fin N', ∃ x : Fin N' → Fin N, IsTrackedPattern x ρ' ρ ∧ D.FollowsPattern x C ∧
      Carries D P R W ρ' := by
  sorry

/-- **The three-piece follower** (Bing's `E_1 + E_2 + E_3`). Let `Δ` be an `A`-covering
description of `M` from `P` to `Q` for `(R, W)` (every level `i` satisfies `CoversUpToA` at
radius `1/(i+1)`), `C = Δ.D lv` a level carrying `(P, R, W)` at `ρ`, and `x` a pattern on `N'`
links into `C` tracking `ρ' ↦ ρ`. Then some deeper level has a consolidation `E` from `P` to
`Q` following `x` in `C` and carrying `(P, R, W)` at `ρ'`.

Construction: a deep level `D_a` (tight: its span up to its return index `α` lies in
`C.span 0 ρ`; its `R`-link inside `C.link ρ`; its return link inside `C.link 0`), a deeper level
`D_b`, and Theorem 5 (`Theorem5Statement`, on the thinned description with levels `C, D_a, …`)
three times: on `D_a(0..ρ_a)` with the pattern `x|[0, ρ']` (from `0` to `ρ`, values in `[0, ρ]`);
on `D_a(ρ_a..α)` with the reversed pattern `t ↦ x (ρ' − t)` (from `ρ` to `0`, values in
`[0, ρ]`); on `D_a(α..last)` with the whole `x` (from `0` to `N − 1`). `E` has `N'` links: link
`n` is `E_1(n) ∪ E_2(ρ' − n) ∪ E_3(n)` for `n ≤ ρ'` and `E_3(n)` for `n > ρ'`. Cross-intersections
occur only at the two junction links (the `R`-link of `D_a`, at index `ρ'` on both sides; the
return link, at index `0` on both sides), by Theorem 5's end clause. -/
theorem exists_tracked_follower [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {R : X} {W : Set X}
    (hA : ∀ i, CoversUpToA (Δ.D i) P R W (1 / ((i : ℝ) + 1)))
    (lv : ℕ) {ρ : Fin (Δ.n lv)} (hcar : Carries (Δ.D lv) P R W ρ)
    {N' : ℕ} (x : Fin N' → Fin (Δ.n lv)) (ρ' : Fin N') (hx : IsTrackedPattern x ρ' ρ) :
    ∃ a, lv < a ∧ ∃ E : Chain X N', E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D a) ∧
      E.FollowsPattern x (Δ.D lv) ∧ Carries E P R W ρ' := by
  sorry

/-! ### The tracked alternating construction and Theorem 14 -/

/-- A rung of the tracked construction: as `Rung`, with a common `R`-index `ρ` at which both
chains carry their `(P_i, R_i, W_i)`, and with the following side a *level* of its description. -/
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
  /-- the side that will follow is a level, with the sharper mesh bound -/
  follow : (C₁ = Δ₁.D lv₁ ∧ ∀ t, Metric.diam (C₁.link t) ≤ mfollow) ∨
           (C₂ = Δ₂.D lv₂ ∧ ∀ t, Metric.diam (C₂.link t) ≤ mfollow)

/-- The base rung: a level of `Δ₁` of small mesh, matched on side 2 by the follower (Bing's
`Y_{2,1}`: the tracked follower applied to `Δ₂` with the pattern of the identity on `Δ₁`'s level —
or any pattern tracking the `R`-indices; say which). -/
theorem TRung.exists_base [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X} (Δ₁ : Description X P₁ Q₁)
    (Δ₂ : Description X P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) {R₁ R₂ : X} {W₁ W₂ : Set X}
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1))) :
    ∃ r : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂, r.mfollow = 1 / 2 := by
  sorry

/-- The next rung: the consolidated side is refined by a tight deep level of its description
(`exists_trackedPattern_of_refines`), the level side follows with `exists_tracked_follower`. -/
theorem TRung.exists_next [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X} {Δ₁ : Description X P₁ Q₁}
    {Δ₂ : Description X P₂ Q₂} (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) {R₁ R₂ : X} {W₁ W₂ : Set X}
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1)))
    (r : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : TRung Δ₁ Δ₂ R₁ R₂ W₁ W₂, r'.mfollow = δ ∧ r'.mesh = max δ r.mfollow ∧
      ∃ x : Fin r'.N → Fin r.N, r'.C₁.FollowsPattern x r.C₁ ∧ r'.C₂.FollowsPattern x r.C₂ ∧
        x r'.ρ = r.ρ := by
  sorry

/-- **Theorem 12 with a tracked point**: two `A`-covering descriptions give a homeomorphism
carrying `P₁, Q₁, R₁` to `P₂, Q₂, R₂` (the construction of `Description.exists_homeomorph` on
`TRung`s; `MatchingCovers.exists_homeomorph`'s tracking clause with the index sequence `k ↦ ρ_k`
for `R₁`, `R₂`). -/
theorem exists_homeomorph_tracked [CompactSpace X] {P₁ Q₁ P₂ Q₂ : X}
    (Δ₁ : Description X P₁ Q₁) (Δ₂ : Description X P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂)
    {R₁ R₂ : X} {W₁ W₂ : Set X} (hR₁ : R₁ ∈ Δ₁.M) (hR₂ : R₂ ∈ Δ₂.M)
    (hA₁ : ∀ i, CoversUpToA (Δ₁.D i) P₁ R₁ W₁ (1 / ((i : ℝ) + 1)))
    (hA₂ : ∀ i, CoversUpToA (Δ₂.D i) P₂ R₂ W₂ (1 / ((i : ℝ) + 1))) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M, T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧
      T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ ∧ T ⟨R₁, hR₁⟩ = ⟨R₂, hR₂⟩ := by
  sorry

/-- **Bing 1948, Theorem 14** (formerly the open `Description.theorem14`): `W_i` irreducible
between `P_i` and `R_i` (`exists_irreducible`), the two `A`-covering descriptions, and the tracked
homeomorphism, transported to `Δ.M` through `Δ'.M = Δ.M`. -/
theorem Description.theorem14 [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Description.Theorem14Statement Δ := by
  sorry

end HPC
