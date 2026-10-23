import HPC.PseudoArc.Statements79
import HPC.PseudoArc.Uniqueness
import HPC.PseudoArc.PatGeom
import HPC.PseudoArc.T5Main

/-!
# Bing 1948, Theorems 5 and 6, and Theorem 12 unconditional

Skeleton for batch 80 (save as `HPC/PseudoArc/Theorem5.lean`; add `import HPC.PseudoArc.Theorem5`
to the root `HPC.lean`). Statements only; every proof is `sorry` and is a work item.
(Batch 80: every proof below is now filled in; the only `sorry` left is inside the commented-out
false skeleton statement.)

The statements `Theorem5Statement`, `Theorem6Statement`, `Theorem6PosStatement` are those of
`Statements79.lean`. Bing's induction (COMMISSION-batch80.md §3) applies "the theorem" to
configurations its own statement does not cover, so the proof is expected to go through a
generalised statement `Theorem5'` of the prover's design (§4 of the commission), from which the
three theorems below follow. That statement is to be added to this file with its docstring saying
exactly how it specialises to `Theorem5Statement`.

## Batch-80 changes to the skeleton

* `theorem6Pos_shift` and `patternFollowing` as written in the skeleton (no hypothesis `P ≠ Q`)
  are **false**: see `not_theorem6Pos_shift_unconditional` and
  `not_patternFollowing_unconditional` below (one-point space, `P = Q`, one link per level,
  pattern of length two). The skeleton's two statements are kept, commented out, and replaced
  by the same statements with the hypothesis `hPQ : P ≠ Q`. Theorem 12 already assumes `P ≠ Q`;
  its statement is unchanged and its proof now passes `hPQ₁`, `hPQ₂` along.
* Theorem 6 is proved directly (`HPC.Description.theorem6Pos_of_ne`, file `PatGeom.lean`, from
  the combinatorial core `HPC.PatCore.realize`, files `PatCore.lean`, `PatMain.lean`), not via
  Theorem 5.
* Theorem 5 is proved as stated in `Statements79.lean` (`HPC.Description.theorem5_of`, file
  `T5Main.lean`), from the same combinatorial core: `PatRuns.lean` (lifts over runs, including
  excursions), `T5Read.lean` (the coarse reading with end zones), `T5Runs.lean`,
  `T5Assemble.lean`, `T5Chain.lean` (runs of links in `D_2(u, v)` and the chain `E`).
  The statement that inducts is not a geometric `Theorem5'` but the combinatorial
  `HPC.PatCore.IH` / `HPC.PatCore.realize` (see the report).
-/

namespace HPC.Description

variable {X : Type*} [MetricSpace X] {P Q : X}

/-- **Bing 1948, Theorem 5.**

Batch 80: proved as stated (`HPC.Description.theorem5_of`, file `T5Main.lean`). -/
theorem theorem5 [CompactSpace X] (Δ : Description X P Q) : Theorem5Statement Δ :=
  Δ.theorem5_of

-- Commented-out statement `theorem6Pos_shift` removed in batch 103; see `LEDGER.md`.

/-- **Bing 1948, Theorem 6**, with the deep level Bing's proof produces, for every tail of the
description. This is the hypothesis of Theorem 12.

Batch 80: the hypothesis `hPQ : P ≠ Q` is added to the skeleton's statement, which is false
without it (`not_theorem6Pos_shift_unconditional`). -/
theorem theorem6Pos_shift [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) (i : ℕ) :
    Theorem6PosStatement (Δ.shift i) :=
  (Δ.shift i).theorem6Pos_of_ne hPQ

/-- **Bing 1948, Theorem 6** as stated in `Statements79.lean` (some level `j`, possibly `0`),
for descriptions with `P ≠ Q`. -/
theorem theorem6 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem6Statement Δ := by
  intro N x hx
  obtain ⟨j, -, E, hE⟩ := Δ.theorem6Pos_of_ne hPQ N x hx
  exact ⟨j, E, hE⟩

-- Commented-out statement `patternFollowing` (without `P ≠ Q`) removed in batch 103; see `LEDGER.md`.

/-- Pattern following holds for every description with `P ≠ Q`.

Batch 80: the hypothesis `hPQ : P ≠ Q` is added to the skeleton's statement, which is false
without it (`not_patternFollowing_unconditional`). -/
theorem patternFollowing [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Δ.PatternFollowing :=
  patternFollowing_of_theorem6Pos Δ (theorem6Pos_shift Δ hPQ)

/-! ## The counterexample to the statements without `P ≠ Q` -/

/-- The chain with one link, the whole one-point space. -/
def unitChain : Chain PUnit 1 where
  link _ := Set.univ
  isOpen _ := isOpen_univ
  adjacent i j := by
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp

/-- A description of the one-point space with `P = Q`: one link at every level. -/
noncomputable def unitDescription : Description PUnit PUnit.unit PUnit.unit where
  n _ := 1
  D _ := unitChain
  isFrom _ := ⟨one_pos, trivial, trivial, fun _ _ => Subsingleton.elim _ _,
    fun _ _ => Subsingleton.elim _ _⟩
  crooked _ := ⟨fun _ => ⟨0, subset_rfl⟩, fun h k hk => absurd hk (by omega)⟩
  closure_subset _ _ := ⟨0, Set.subset_univ _⟩
  ε i := 1 / ((i : ℝ) + 1)
  ε_pos i := by positivity
  ε_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  bdd _ _ := Metric.isBounded_iff.mpr ⟨0, fun a _ b _ => by simp⟩
  diam_le i _ := by
    rw [Metric.diam_subsingleton Set.subsingleton_of_subsingleton]
    positivity

/-- No chain with two links is a chain from a point to itself. -/
theorem not_isFrom_self_two {Y : Type*} [MetricSpace Y] (E : Chain Y 2) (y : Y) :
    ¬ E.IsFrom y y := by
  rintro ⟨_, _, hQ, hPu, _⟩
  have := hPu _ hQ
  simp at this

/-- In the one-point description, the pattern `0, 0` in the first level is not followed by any
chain from `P` to `Q`. -/
theorem unitDescription_not_theorem6Pos (i : ℕ) :
    ¬ Theorem6PosStatement (unitDescription.shift i) := by
  intro h
  obtain ⟨-, -, E, hE, -⟩ := h 2 (fun _ => ⟨0, one_pos⟩)
    ⟨two_pos, one_pos, rfl, rfl, fun _ _ _ => by simp⟩
  exact not_isFrom_self_two E _ hE

/-- In the one-point description, Theorem 6 as stated in `Statements79.lean` (any level `j`)
fails as well: the hypothesis `P ≠ Q` of `theorem6` cannot be dropped. -/
theorem unitDescription_not_theorem6 : ¬ Theorem6Statement unitDescription := by
  intro h
  obtain ⟨-, E, hE, -⟩ := h 2 (fun _ => ⟨0, one_pos⟩)
    ⟨two_pos, one_pos, rfl, rfl, fun _ _ _ => by simp⟩
  exact not_isFrom_self_two E _ hE

/-- **The skeleton's `theorem6Pos_shift` is false** without the hypothesis `P ≠ Q`. -/
theorem not_theorem6Pos_shift_unconditional :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] (P Q : X) (Δ : Description X P Q) (i : ℕ),
      Theorem6PosStatement (Δ.shift i) :=
  fun h => unitDescription_not_theorem6Pos 0 (h PUnit PUnit.unit PUnit.unit unitDescription 0)

/-- **The skeleton's `patternFollowing` is false** without the hypothesis `P ≠ Q`. -/
theorem not_patternFollowing_unconditional :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] (P Q : X) (Δ : Description X P Q),
      Δ.PatternFollowing := fun h =>
  unitDescription_not_theorem6Pos 0
    (theorem6_shift_of_patternFollowing _ (h PUnit PUnit.unit PUnit.unit unitDescription) 0)

end HPC.Description

namespace HPC

variable {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂]

/-- **Bing 1948, Theorem 12**, unconditional: two descriptions give homeomorphic continua, with
the end points corresponding.

Batch 80: statement unchanged; the proof passes `hPQ₁`, `hPQ₂` to `patternFollowing`. -/
theorem theorem12 [CompactSpace X₁] [CompactSpace X₂] {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M,
      T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ :=
  Description.exists_homeomorph Δ₁ Δ₂ hPQ₁ hPQ₂ (Δ₁.patternFollowing hPQ₁)
    (Δ₂.patternFollowing hPQ₂)

end HPC
