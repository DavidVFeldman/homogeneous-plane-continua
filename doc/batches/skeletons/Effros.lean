import Mathlib

/-!
# Batch 134: the Effros theorem (van Mill's elementary proof) and Ungar's corollary

This is Part C of CLASSIFICATION-OUTLINE.md. Skeleton. Save as `HPC/Effros/Effros.lean` (a new
directory) and add `import HPC.Effros.Effros` at the end of the root `HPC.lean`. Every `sorry` is a
work item. Shapes may be adjusted, with each change recorded. Splitting into several files is
expected.

Source: J. van Mill, *A note on the Effros theorem*, Amer. Math. Monthly 111 (2004), 801–806.
Save it as `doc/sources/vanmill2004.pdf`. COMMISSION-batch134.md §3 transcribes §§2–3. That
transcription includes a reconstruction of the inductive invariant (3) of Proposition 2.2, which
the scan garbles.

## Plan

* §A. Meager and fat sets: Lemma 2.1, and Proposition 2.2 for analytic sets (Mathlib's
  `MeasureTheory.AnalyticSet`: a continuous image of `ℕ → ℕ`, or empty).
* §B. The open mapping principle (van Mill, Theorem 1.2, for a Polish group). Lemmas 3.1, 3.2,
  Corollary 3.3, Lemma 3.4, Proposition 3.5 and Corollary 3.6. Main result:
  `effros_open_mapping`.
* §C. The homeomorphism group of a compact metric space: a Polish topological group acting
  continuously.
* §D. Ungar's corollary for homogeneous compacta (`effros_homogeneous`). This is the form used by
  Jones, Hagopian, Rogers and Oversteegen–Tymchatyn.
-/

namespace HPC.Effros

open Set Topology Filter Metric MeasureTheory

/-! ### §A. Meager and fat sets -/

section MeagerFat

variable {X : Type*} [TopologicalSpace X]

/-- `A` is **nowhere meager** in `X`: no nonempty relatively open subset of `A` is meager in
`X`. -/
def NowhereMeagre (A : Set X) : Prop :=
  ∀ V : Set X, IsOpen V → (V ∩ A).Nonempty → ¬ IsMeagre (V ∩ A)

/-- `A` is **fat** in `X`: dense and nowhere meager. Every superset of a fat set is fat. -/
def IsFat (A : Set X) : Prop := Dense A ∧ NowhereMeagre A

theorem IsFat.mono {A B : Set X} (hA : IsFat A) (hAB : A ⊆ B) : IsFat B := by
  sorry

/-- **van Mill, Lemma 2.1.** A fat set minus a meager set is fat. -/
theorem IsFat.diff_meagre {S A : Set X} (hS : IsFat S) (hA : IsMeagre A) : IsFat (S \ A) := by
  sorry

/-- A subset that is not meager is not nowhere dense: its closure has nonempty interior. -/
theorem nonempty_interior_closure_of_not_meagre {A : Set X} (hA : ¬ IsMeagre A) :
    (interior (closure A)).Nonempty := by
  sorry

/-- **van Mill, Proposition 2.2.** Two analytic fat subsets of a nonempty metric space meet.
(COMMISSION-batch134.md §3.1. First the reduction: the parametrizations are restricted so that
the image of every nonempty open set is non-meager. Then the nested construction with invariant
`α(U_n) ⊆ closure β(V_n)`.) -/
theorem inter_nonempty_of_isFat {Y : Type*} [MetricSpace Y] [Nonempty Y] {S T : Set Y}
    (hSa : AnalyticSet S) (hTa : AnalyticSet T) (hS : IsFat S) (hT : IsFat T) :
    (S ∩ T).Nonempty := by
  sorry

end MeagerFat

/-! ### §B. The open mapping principle (van Mill, Theorem 1.2, Polish group) -/

section OpenMapping

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
  [MetricSpace X] [MulAction G X] [ContinuousSMul G X]

/-- A neighbourhood base `U n` of `1` with van Mill's properties:
(i) each `U n` is open and symmetric, and `U 0 = univ`;
(ii) `U (n+1) * U (n+1) ⊆ U n`;
and the `U n` form a basis of `𝓝 1`. (In a first countable group; Polish groups are.) -/
theorem exists_vanMill_basis :
    ∃ U : ℕ → Set G, U 0 = univ ∧ (∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n) ∧
      (∀ n, U (n + 1) * U (n + 1) ⊆ U n) ∧ (𝓝 (1 : G)).HasBasis (fun _ => True) U := by
  sorry

/-- `U • x := {g • x | g ∈ U}`. -/
def orbitPart (U : Set G) (x : X) : Set X := (fun g : G => g • x) '' U

/-- **van Mill, Lemma 3.1.** Suppose `V` is open and `z ∈ V ∩ U n • x`. Then
`U m • z ⊆ V ∩ U n • x` for some `m`. -/
theorem vanMill_3_1 {U : ℕ → Set G} (hU0 : U 0 = univ)
    (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U) (x : X) (n : ℕ) {V : Set X} (hV : IsOpen V)
    {z : X} (hz : z ∈ V ∩ orbitPart (U n) x) :
    ∃ m, orbitPart (U m) z ⊆ V ∩ orbitPart (U n) x := by
  sorry

/-- **van Mill, Lemma 3.2.** If the action is transitive and `X` is a nonempty Baire space, then
`U n • x` is not meager. (Lindelöf: countably many translates of `U n` cover `G`.) -/
theorem vanMill_3_2 [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (x : X) : ¬ IsMeagre (orbitPart U x) := by
  sorry

/-- **van Mill, Corollary 3.3.** `U n • x` is nowhere meager. -/
theorem vanMill_3_3 [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU0 : U 0 = univ) (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U) (x : X) (n : ℕ) :
    NowhereMeagre (orbitPart (U n) x) := by
  sorry

/-- **van Mill, Lemma 3.4, repaired form.** `x` lies in the interior of the *closure* of
`U n • x`. Van Mill asserts that the interior of `U n • x` itself is dense in `U n • x`, from
"not meager, hence not nowhere dense (i.e. has nonempty interior)". But "not nowhere dense" only
gives a closure with nonempty interior; see COMMISSION-batch134.md §3.2. This closure form is what
Proposition 3.5 needs. Proof: `V := interior (closure (U (n+1) • x))` is nonempty (3.2) and
meets `U (n+1) • x`, say at `h • x`. Then `x ∈ h⁻¹ • V`, which is open and contained in
`closure (U n • x)` by (i) and (ii). -/
theorem vanMill_3_4 [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU0 : U 0 = univ) (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hUU : ∀ n, U (n + 1) * U (n + 1) ⊆ U n) (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U)
    (x : X) (n : ℕ) :
    x ∈ interior (closure (orbitPart (U n) x)) := by
  sorry

/-- **van Mill, Proposition 3.5, closure form.** `interior (closure (U (n+1) • x)) ⊆ U n • x`.
For `z` in the left side, put `E := interior (closure (U (n+1) • x)) ∩ interior (closure
(U (n+1) • z))`, an open neighbourhood of `z` by 3.4. The sets `U (n+1) • x ∩ E` and
`U (n+1) • z ∩ E` are dense in `E` (`E` lies in both closures), nowhere meager (3.3), and analytic
(continuous images of the open, hence Polish, `U (n+1)`). By Proposition 2.2 in `E` they meet at
`g • x = h • z`, so `z = (h⁻¹ * g) • x` with `h⁻¹ * g ∈ U n`. -/
theorem vanMill_3_5 [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    {U : ℕ → Set G} (hU0 : U 0 = univ) (hU : ∀ n, IsOpen (U n) ∧ (1 : G) ∈ U n ∧ (U n)⁻¹ = U n)
    (hUU : ∀ n, U (n + 1) * U (n + 1) ⊆ U n) (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) U)
    (x : X) (n : ℕ) :
    interior (closure (orbitPart (U (n + 1)) x)) ⊆ orbitPart (U n) x := by
  sorry

/-- **The open mapping principle** (Effros 1965; van Mill 2004, Theorem 1.2 for a Polish group).
Suppose a Polish group acts continuously and transitively on a nonempty metric Baire space. Then
for every `x` and every neighbourhood `U` of `1`, the set `U • x` is a neighbourhood of `x`. That
is, the action is micro-transitive, and `g ↦ g • x` is open. -/
theorem effros_open_mapping [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    (x : X) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : orbitPart U x ∈ 𝓝 x := by
  sorry

/-- The orbit map `g ↦ g • x` is open. -/
theorem isOpenMap_smul_left [MulAction.IsPretransitive G X] [BaireSpace X] [Nonempty X]
    (x : X) : IsOpenMap (fun g : G => g • x) := by
  sorry

end OpenMapping

/-! ### §C. The homeomorphism group of a compact metric space

Design item (COMMISSION-batch134.md §2, item C). Give `Y ≃ₜ Y`, for a compact metric `Y`, the
structure of a Polish topological group acting continuously on `Y`. Use Mathlib's instances where
they exist. Otherwise:
* topologize `Y ≃ₜ Y` by the embedding `h ↦ (h, h⁻¹)` into `C(Y, Y) × C(Y, Y)`, using uniform
  convergence (= compact-open, `Y` compact);
* show the image is closed (`f ∘ g = id`, `g ∘ f = id`);
* `C(Y, Y)` is Polish (complete; second countable for compact metric `Y`).

A useful explicit form: `N h := sup_z dist (h z) z` satisfies `N h⁻¹ = N h` and
`N (h⁻¹ * g) ≤ N h + N g`. The sets `{h | N h < r}` form a basis at `1`.
-/

section Homeo

variable (Y : Type*) [MetricSpace Y] [CompactSpace Y]

/-- The sup-distance of a homeomorphism from the identity. -/
noncomputable def supMove (h : Y ≃ₜ Y) : ℝ := ⨆ z : Y, dist (h z) z

/-- `supMove h⁻¹ = supMove h`, and `supMove (h⁻¹ ∘ g) ≤ supMove h + supMove g`. -/
theorem supMove_symm (h : Y ≃ₜ Y) : supMove Y h.symm = supMove Y h := by
  sorry

theorem supMove_symm_trans_le (g h : Y ≃ₜ Y) :
    supMove Y (g.trans h.symm) ≤ supMove Y h + supMove Y g := by
  sorry

/- Items C.1–C.3 (shapes yours):
* C.1 `Group (Y ≃ₜ Y)` (Mathlib's, if present), `TopologicalSpace`, `IsTopologicalGroup`.
* C.2 `PolishSpace (Y ≃ₜ Y)`.
* C.3 `MulAction (Y ≃ₜ Y) Y`, `ContinuousSMul (Y ≃ₜ Y) Y`, and
  `{h | supMove Y h < r} ∈ 𝓝 1` for every `r > 0`.
Put them in this section, or in a separate file. -/

end Homeo

/-! ### §D. Ungar's corollary -/

/-- **Effros–Ungar.** Let `Y` be a homogeneous compact metric space. For every `ε > 0` there is
`δ > 0` such that any two points at distance `< δ` are carried one to the other by a
homeomorphism moving no point by `ε` or more.

Proof: §B for the Polish group of §C; `orbitPart {h | supMove h < ε/2} x` is an open neighbourhood
of `x` (Lemma 3.1 and Corollary 3.6). Take a Lebesgue number of the cover by these sets. If
`x, y ∈ U • z`, then `y = (h * g⁻¹) • x` with `supMove (h * g⁻¹) < ε`. -/
theorem effros_homogeneous {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    (hom : ∀ x y : Y, ∃ h : Y ≃ₜ Y, h x = y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : Y, dist x y < δ → ∃ h : Y ≃ₜ Y, h x = y ∧ ∀ z, dist (h z) z < ε := by
  sorry

/-- The same for a compact subset of a metric space, homogeneous in its own topology (the form
needed for plane continua `M ⊆ Pt`). -/
theorem effros_homogeneous_set {E : Type*} [MetricSpace E] {M : Set E} (hM : IsCompact M)
    (hom : ∀ x y : M, ∃ h : M ≃ₜ M, h x = y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : M, dist x y < δ → ∃ h : M ≃ₜ M, h x = y ∧ ∀ z, dist (h z) z < ε := by
  sorry

end HPC.Effros
