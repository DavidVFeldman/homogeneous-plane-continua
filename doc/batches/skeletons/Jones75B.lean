import HPC.Jones.Jones75A

/-!
# Batch 190 skeleton: Jones 1975 II — the planar core; `NoArcIndecHomPlane`; Theorem 1 of 1976

Save as `HPC/Jones/Jones75B.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones75B` at the end of `HPC.lean`. Every `sorry` is a work item. Items stated as
`True` are *shape left to you*; record each shape in the report. Unproved items are commented out
with an `OPEN` note, as before.

Source: report 189 §6.3, as repaired in commission 190 §2–§6 (the shadow lemma and the flow box
hold only in the middle band; the trap is rebuilt in the column `3/8 ≤ X ≤ 5/8`). Collar
coordinates: `F` a collar (`IsCollar`) of `γ = ℓ|[0,1]`, `F(t, 0) = ℓ(t)`; boxes
`F([¼, ¾] × [−η, η])`; `κ = 1/32`; middle band `[9/32, 23/32]`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Passes

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §2. Passes -/

/-- A *pass* of the box of height `η`: `ℓ[a, b]` from the left edge `F({¼} × [−η, η])` to the right
edge `F({¾} × [−η, η])`, its interior in the open box `F((¼, ¾) × (−η, η))`. -/
def IsPass (F : ℝ × ℝ → Pt) (η : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  a < b ∧ (∃ y ∈ Icc (-η) η, (ℓ a : Pt) = F (1 / 4, y)) ∧
    (∃ y ∈ Icc (-η) η, (ℓ b : Pt) = F (3 / 4, y)) ∧
    ∀ s ∈ Ioo a b, (ℓ s : Pt) ∈ F '' (Ioo (1 / 4) (3 / 4) ×ˢ Ioo (-η) η)

/-- *(Mon)*: along `ℓ[a, b]` the first collar coordinate never falls back by `2κ` or more. -/
def PassMon (F : ℝ × ℝ → Pt) (κ : ℝ) (ℓ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ v' v, a ≤ v' → v' < v → v ≤ b → ∀ p' p : ℝ × ℝ,
    p' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
      (ℓ v' : Pt) = F p' → (ℓ v : Pt) = F p → p'.1 - 2 * κ < p.1

/-- **§2.1, (P1)**: distinct passes have disjoint closed parameter intervals. -/
theorem IsPass.disjoint {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {η : ℝ}
    (hη : η ≤ 1) {ℓ : ℝ → M} {a b a' b' : ℝ} (h : IsPass F η ℓ a b) (h' : IsPass F η ℓ a' b')
    (hne : (a, b) ≠ (a', b')) : Disjoint (Icc a b) (Icc a' b') := by
  sorry

/-- **§2.1, (P2)**: only finitely many passes meet a bounded parameter interval. -/
theorem IsPass.finite {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1) {ℓ : ℝ → M} (hℓ : Continuous ℓ) (N : ℝ) :
    {ab : ℝ × ℝ | IsPass F η ℓ ab.1 ab.2 ∧ ab.1 ≤ N ∧ -N ≤ ab.2}.Finite := by
  sorry

/-- **§2.1, (P4)**: a pass other than the base pass lies, end points included, strictly above or
strictly below it. *Shape left to you.* -/
theorem IsPass.above_or_below : True := by
  sorry

/-! ## §3. Shadow lemma, flow box, late thin passes -/

/-- **§3.1, the shadow lemma** (Effros + (O)), in the middle band only. -/
theorem shadow_pass (S : JonesSetting M) {ℓ : ℝ → M} (hℓ : IsLine ℓ) {γ : unitInterval → Pt}
    (hγ : ∀ t : unitInterval, γ t = ℓ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {η' : ℝ}
    (hη' : 0 < η') :
    ∃ δ > 0, ∀ x ∈ Icc (9 / 32 : ℝ) (23 / 32), ∀ u, dist (ℓ u) (ℓ x) < δ →
      ∃ a b, IsPass F η' ℓ a b ∧ PassMon F (1 / 32) ℓ a b ∧ u ∈ Ioo a b := by
  sorry

/-- **§3.2, the flow box (FB)**, in the middle band only: for the box of height `η ≤ ½` there is
`η₂ ∈ (0, η)` such that every point of `ℓ` in `F([9/32, 23/32] × [−η₂, η₂])` lies inside a pass of
the box of height `η` satisfying (Mon). -/
theorem flow_box (S : JonesSetting M) {ℓ : ℝ → M} (hℓ : IsLine ℓ) {γ : unitInterval → Pt}
    (hγ : ∀ t : unitInterval, γ t = ℓ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ η₂ > 0, η₂ < η ∧ ∀ u, (ℓ u : Pt) ∈ F '' (Icc (9 / 32) (23 / 32) ×ˢ Icc (-η₂) η₂) →
      ∃ a b, IsPass F η ℓ a b ∧ PassMon F (1 / 32) ℓ a b ∧ u ∈ Ioo a b := by
  sorry

/-- **§3.3, late thin passes** (recurrence): passes inside the thin box start arbitrarily late.
`η₂` as in `flow_box`; *shape adjustable* (you may bundle the two scales). -/
theorem exists_late_thin_pass (S : JonesSetting M) {ℓ : ℝ → M} (hℓ : IsLine ℓ)
    {γ : unitInterval → Pt} (hγ : ∀ t : unitInterval, γ t = ℓ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {η η₂ : ℝ} (hη₂ : 0 < η₂) (hη₂η : η₂ < η) (T : ℝ) :
    ∃ a b, T < a ∧ IsPass F η ℓ a b ∧
      ∀ s ∈ Icc a b, (ℓ s : Pt) ∈ F '' (Icc (1 / 4) (3 / 4) ×ˢ Icc (-η₂) η₂) := by
  sorry

end Passes

/-! ## §4–§5. The region and the trap (shapes left to you; commission 190 §4–§5)

New small lemmas N1–N4 of commission 190 §7 go here, then (R1)–(R3), Lemma A and the trapping
lemma. -/

/-- **§4, (R1)–(R3)**: the region `R_m = F(D_m)` of a thin pass above the base (`rect_domain_aux`),
its low segments and low strip. *Shape left to you.* -/
theorem region_of_thin_pass : True := by
  sorry

/-- **§5, the trapping lemma** (commission 190 §5). *Shape left to you.* -/
theorem trap_pass : True := by
  sorry

/-! ## §6. The Theorem and its corollaries -/

/-- **§6.1, the arc step** (Bing 1960, indecomposable case; Jones 1975, Theorem, by the route of
commission 190). -/
theorem jones75_noArc : NoArcIndecHomPlane := by
  sorry

/-- **§6.2, Theorem 1 of Hagopian 1976** ("Every indecomposable homogeneous plane continuum is
hereditarily indecomposable"), unconditional. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 :=
  hagopian76_theorem1_jones jones75_noArc

section Corollaries

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§6.3, Bing 1960 for plane continua**, unconditional: "A simple closed curve is the only
homogeneous bounded plane continuum that contains an arc." -/
theorem bing60_plane_uncond (hX : IsHomogeneous M) {α : Set M}
    (hα : Nonempty (α ≃ₜ unitInterval)) : Nonempty (M ≃ₜ Circle) :=
  bing60_plane hagopian76_theorem1 hX hα

/-- **§6.3, Hagopian 1976, Theorem 2**, unconditional: every homogeneous plane continuum that does
not separate the plane is hereditarily indecomposable. -/
theorem hagopian76_theorem2_uncond (hX : IsHomogeneous M) (hns : ¬ SeparatesPlane M) :
    IsHereditarilyIndecomposable (univ : Set M) :=
  hagopian76_theorem2 hagopian76_theorem1 hX hns

end Corollaries

end HPC.Hagopian
