import HPC.Hagopian.Hagopian84D

/-!
# Batch 189 skeleton: Jones 1975 I — arcs and lines; no small reversal; recurrence

Save as `HPC/Jones/Jones75A.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones75A` at the end of `HPC.lean`. Every `sorry` is a work item. Items stated as
`True` are *shape left to you*; record each shape in the report. Unproved items are commented out
with an `OPEN` note, as before.

Source: F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math. 1 (1975),
57–61 (`doc/sources/jones1975.pdf`; notes `doc/notes/jones75.md`). Route: commission 189.

§2–§4 are stated for a compact metric space `Y` under the hypotheses that Jones's (a)–(c) and the
Effros corollary provide (`JonesSetting`), not for a plane continuum. Planarity is used only from §5
on. The dyadic solenoid satisfies `JonesSetting` (not formalized), so §2–§4 are not vacuous.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §1. The setting -/

/-- The hypotheses used by Jones 1975 (a)–(c), (d), (f) and by §2–§4 below: homogeneous,
hereditarily unicoherent, atriodic, and containing an arc. A bundle of hypotheses, not open work;
non-vacuity note required all the same. -/
structure JonesSetting (Y : Type*) [MetricSpace Y] [CompactSpace Y] : Prop where
  hom : IsHomogeneous Y
  hu : IsHereditarilyUnicoherent (univ : Set Y)
  atr : IsAtriodic (univ : Set Y)
  arc : ∃ (a b : Y) (A : Set Y), TArc a b A

section PlaneInstance

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§1**: a homogeneous indecomposable plane continuum containing an arc is a `JonesSetting`
(Jones's (a) and (b) are `hagopian75_lemma1`). -/
theorem jonesSetting_of_plane (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hα : ∃ (a b : M) (A : Set M), TArc a b A) : JonesSetting M := by
  sorry

end PlaneInstance

section General

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-! ## §2. Arcs and lines -/

/-- **§2.1, Jones (c), first half** (p. 57: "If two arcs `A` and `B` of `M` intersect then
`A ∪ B` is an arc"). -/
theorem JonesSetting.union_arc (S : JonesSetting Y) {A B : Set Y} {a b a' b' : Y}
    (hA : TArc a b A) (hB : TArc a' b' B) (hAB : (A ∩ B).Nonempty) :
    ∃ p q : Y, TArc p q (A ∪ B) := by
  sorry

/-- **§2.1, Jones (c), second half** ("where they have a common end point and intersect somewhere
else, then one of them is a subset of the other"). -/
theorem JonesSetting.nested (S : JonesSetting Y) {A B : Set Y} {a b c : Y} (hA : TArc a b A)
    (hB : TArc a c B) (hAB : (A ∩ B).Nontrivial) : A ⊆ B ∨ B ⊆ A := by
  sorry

/-- **§2.2**: every point is an interior point of an arc (homogeneity). -/
theorem JonesSetting.exists_arc_through (S : JonesSetting Y) (x : Y) :
    ∃ (a b : Y) (A : Set Y), TArc a b A ∧ x ∈ A ∧ x ≠ a ∧ x ≠ b := by
  sorry

/-- The arc component of `x`: `x` together with every arc containing `x`. -/
def arcComp (x : Y) : Set Y :=
  insert x (⋃₀ {A | (∃ a b : Y, TArc a b A) ∧ x ∈ A})

/-- A *line*: a continuous injection of `ℝ` onto an arc component. -/
def IsLine (ℓ : ℝ → Y) : Prop :=
  Continuous ℓ ∧ Function.Injective ℓ ∧ range ℓ = arcComp (ℓ 0)

/-- **§2.3, every arc component is a line** (Jones (d), first sentence, for both rays at a
point). -/
theorem JonesSetting.exists_line (S : JonesSetting Y) (x : Y) :
    ∃ ℓ : ℝ → Y, IsLine ℓ ∧ ℓ 0 = x := by
  sorry

/-- **§2.4**: the arcs inside a line are its parameter intervals. -/
theorem JonesSetting.line_arc (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) {s t : ℝ}
    (hst : s < t) : TArc (ℓ s) (ℓ t) (ℓ '' Icc s t) := by
  sorry

/-- **§2.4**: a homeomorphism acts on lines by monotone continuous bijections of the
parameters. -/
theorem JonesSetting.homeo_on_line (S : JonesSetting Y) {ℓ ℓ' : ℝ → Y} (hℓ : IsLine ℓ)
    (hℓ' : IsLine ℓ') (h : Y ≃ₜ Y) (h0 : h (ℓ 0) ∈ range ℓ') :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Bijective ψ ∧ (StrictMono ψ ∨ StrictAnti ψ) ∧
      ∀ s, h (ℓ s) = ℓ' (ψ s) := by
  sorry

/-! ## §3. No small reversal (replaces Jones (f)) -/

/-- **§3.1, (R0)**: a homeomorphism fixing an interior point `p` of an arc `A ∪ C` and moving no
point by `min(ρ(a, C), ρ(c, A))` or more does not fold `A` onto the side of `C`. -/
theorem JonesSetting.no_reversal_arc (S : JonesSetting Y) {a p c : Y} {A C : Set Y}
    (hA : TArc a p A) (hC : TArc p c C) (hAC : A ∩ C = {p}) {h : Y ≃ₜ Y} (hp : h p = p)
    (hsmall : ∀ x, dist x (h x) < min (infDist a C) (infDist c A)) : h '' A ∩ C = {p} := by
  sorry

/-- **§3.2, (R), uniform**: one `ε` for all fixed points and all lines. -/
theorem JonesSetting.exists_no_reversal (S : JonesSetting Y) :
    ∃ ε > 0, ∀ h : Y ≃ₜ Y, (∀ x, dist x (h x) < ε) → ∀ ℓ : ℝ → Y, IsLine ℓ → ∀ s, h (ℓ s) = ℓ s →
      ∀ t, s < t → ∃ t', s < t' ∧ h (ℓ t) = ℓ t' := by
  sorry

/-- **§3.3, (O), orientation**: a small homeomorphism that carries a point of a line into the same
line preserves the line's orientation (`ψ` continuous and onto as well, for §5). -/
theorem JonesSetting.orientation (S : JonesSetting Y) :
    ∃ ε > 0, ∀ h : Y ≃ₜ Y, (∀ x, dist x (h x) < ε) → ∀ ℓ : ℝ → Y, IsLine ℓ →
      h (ℓ 0) ∈ range ℓ → ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ Continuous ψ ∧ Function.Surjective ψ ∧
        ∀ s, h (ℓ s) = ℓ (ψ s) := by
  sorry

/-! ## §4. Recurrence (replaces the second half of Jones (d)) -/

/-- The forward limit set of a line. -/
def omegaLim (ℓ : ℝ → Y) : Set Y := ⋂ t : ℝ, closure (ℓ '' Ici t)

/-- A set is *arc-saturated* if it contains the arc component of each of its points. -/
def IsArcSaturated (Z : Set Y) : Prop := ∀ x ∈ Z, arcComp x ⊆ Z

/-- **§4.1**: limit sets are arc-saturated (Effros). -/
theorem JonesSetting.omegaLim_saturated (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) :
    IsArcSaturated (omegaLim ℓ) := by
  sorry

/-- **§4.2**: every line lies in its own forward limit set (commission 189 §4.2: Effros with
`ε = ½ d(ℓ(0), ω(ℓ))`). -/
theorem JonesSetting.line_recurrent (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) :
    range ℓ ⊆ omegaLim ℓ := by
  sorry

/-- **§4.3, Jones (d), second sentence** ("every point of `ab` is a limit point of `T − ab`"), for
every line and both directions. -/
theorem JonesSetting.jones75_d (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) (s : ℝ) :
    ℓ '' Iic s ⊆ closure (ℓ '' Ioi s) ∧ ℓ '' Ici s ⊆ closure (ℓ '' Iio s) := by
  sorry

end General

/-! ## §5. In the plane: no backtracking near an arc (shape left to you)

Commission 189 §5: in collar coordinates `F` around an arc `ℓ[0, 1]` of a line (`exists_collar`),
for every `κ > 0` there is `η > 0` such that a piece `ℓ[u, β]` lying in the collar strip of height
`η` never has its first coordinate decrease by `κ` or more. -/

section Plane

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§5, (L)**. *Shape left to you.* -/
theorem no_backtrack_in_collar : True := by
  sorry

end Plane

/-! ## §6. The planar contradiction: reconnaissance only (commission 189 §6)

Target, for a later batch: `jones75_noArc : NoArcIndecHomPlane`. -/

end HPC.Hagopian
