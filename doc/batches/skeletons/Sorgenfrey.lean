import HPC.Plane.Fugate66B

/-!
# Batch 102: Sorgenfrey's theorem (Nadler 11.23–11.35)

Skeleton (save as `HPC/Plane/Sorgenfrey.lean`; add `import HPC.Plane.Sorgenfrey` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. Nothing in an existing file is to be edited; batch 100's
`exists_irreducibleBetween_of_atriodic` (`Fugate66.lean`) keeps its `sorry` by import order, and
`sorgenfrey_irreducible_of_atriodic_hu` here is its sorry-free form (pruning list).

Source: S. B. Nadler, *Continuum Theory* (1992), Chapter XI §§4–5: 11.22–11.35 (text extract
`nadler-11-26-to-11-35.txt` accompanies the commission). Nadler's "triod" (11.22) is batch 92's
`IsTriod`; "unicoherent" is `IsUnicoherent`. Everything here is for a compact metric space `S`
and continua `X ⊆ S` (`Fold.Q78.IsContinuum`).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## 11.23–11.24: essential sums, weak triods -/

/-- **Nadler 11.23**, three summands: `X = X₁ ⊕ X₂ ⊕ X₃` — continua whose union is `X`, none
contained in the union of the other two. -/
def IsEssentialSum₃ (X X₁ X₂ X₃ : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ Fold.Q78.IsContinuum X₁ ∧ Fold.Q78.IsContinuum X₂ ∧
    Fold.Q78.IsContinuum X₃ ∧ X = X₁ ∪ X₂ ∪ X₃ ∧
    ¬ X₁ ⊆ X₂ ∪ X₃ ∧ ¬ X₂ ⊆ X₁ ∪ X₃ ∧ ¬ X₃ ⊆ X₁ ∪ X₂

/-- Two summands: `X = Y ⊕ Z`, i.e. a decomposition into proper subcontinua. -/
def IsEssentialSum₂ (X Y Z : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ Fold.Q78.IsContinuum Y ∧ Fold.Q78.IsContinuum Z ∧ X = Y ∪ Z ∧
    Y ≠ X ∧ Z ≠ X

/-- **Nadler 11.24.** A *weak triod*: an essential sum of three continua with a common point. -/
def IsWeakTriod (X : Set S) : Prop :=
  ∃ X₁ X₂ X₃ : Set S, IsEssentialSum₃ X X₁ X₂ X₃ ∧ (X₁ ∩ X₂ ∩ X₃).Nonempty

/-- **11.25.** Every triod is a weak triod. -/
theorem isWeakTriod_of_isTriod {X : Set S} (h : IsTriod X) : IsWeakTriod X := by
  sorry

/-- **11.26.** For a unicoherent continuum, triod ⇔ weak triod. -/
theorem isTriod_iff_isWeakTriod {X : Set S} (hX : Fold.Q78.IsContinuum X) (hu : IsUnicoherent X) :
    IsTriod X ↔ IsWeakTriod X := by
  sorry

/-- A weak triod is not irreducible between any two points (Nadler, after 11.24, "using 11.5"). -/
theorem not_irreducible_of_isWeakTriod {X : Set S} (h : IsWeakTriod X) (p q : S) :
    ¬ IsIrreducibleBetween X p q := by
  sorry

/-! ## 11.27–11.28 -/

/-- **11.27.** If `X = Y ⊕ Z` and `X` is not a weak triod, then `X ∖ Y` and `X ∖ Z` are connected. -/
theorem isConnected_diff_of_not_weakTriod {X Y Z : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) : IsConnected (X \ Y) ∧ IsConnected (X \ Z) := by
  sorry

/-- **11.28.** With `U = X ∖ Z` (open) and `Ū` its closure: if `H` is a subcontinuum of `Ū`
containing `Ū ∩ Z`, then `U ∖ H` is connected. -/
theorem isConnected_diff_of_superset {X Y Z H : Set S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) (hH : Fold.Q78.IsContinuum H) (hHU : H ⊆ closure (X \ Z))
    (hHZ : closure (X \ Z) ∩ Z ⊆ H) : IsConnected ((X \ Z) \ H) := by
  sorry

/-! ## 11.29–11.30: irreducible from a set to a set -/

/-- **11.29.** `C = irr(A, B)`: `C` meets `A` and `B`, and no proper subcontinuum of `C` does. -/
def IrrFromTo (C A B : Set S) : Prop :=
  Fold.Q78.IsContinuum C ∧ (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ C → (K ∩ A).Nonempty → (K ∩ B).Nonempty → K = C

/-- **11.30.** For nonempty compact `A`, `B` in a continuum `X` there is a subcontinuum
`C = irr(A, B)` (Zorn / Brouwer reduction; batch 93's `exists_minimal_of_seq`). -/
theorem exists_irrFromTo {X A B : Set S} (hX : Fold.Q78.IsContinuum X) (hA : IsCompact A)
    (hB : IsCompact B) (hAX : (A ∩ X).Nonempty) (hBX : (B ∩ X).Nonempty) :
    ∃ C ⊆ X, IrrFromTo C A B := by
  sorry

/-! ## 11.31–11.33 -/

/-- **11.31.** `X = Y ⊕ Z` not a weak triod, `U = X ∖ Z`; `A`, `B` subcontinua of `Ū`,
`p ∈ U ∖ A`, `A ⊇ Ū ∩ Z`, `B = irr(p, A)`, `A ∪ B ⊇ U`. Then `Ū = irr(p, Ū ∩ Z)`. -/
theorem nadler_11_31 {X Y Z A B : Set S} {p : S} (h : IsEssentialSum₂ X Y Z)
    (hnt : ¬ IsWeakTriod X) (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAU : A ⊆ closure (X \ Z)) (hBU : B ⊆ closure (X \ Z)) (hp : p ∈ (X \ Z) \ A)
    (hAZ : closure (X \ Z) ∩ Z ⊆ A) (hBirr : IrrFromTo B {p} A) (hcov : X \ Z ⊆ A ∪ B) :
    IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z) := by
  sorry

/-- **11.32.** `X = Y ⊕ Z` unicoherent, not a weak triod, `U = X ∖ Z`, `A ⊊ Ū` a subcontinuum
with `A ⊇ Ū ∩ Z`, `W = U ∖ A`. If `W̄ = E ⊕ F` then exactly one of `E`, `F` misses `A`. -/
theorem nadler_11_32 {X Y Z A E F : Set S} (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X) (hA : Fold.Q78.IsContinuum A) (hAU : A ⊆ closure (X \ Z))
    (hAne : A ≠ closure (X \ Z)) (hAZ : closure (X \ Z) ∩ Z ⊆ A)
    (hEF : IsEssentialSum₂ (closure ((X \ Z) \ A)) E F) :
    (E ∩ A = ∅ ∧ (F ∩ A).Nonempty) ∨ (F ∩ A = ∅ ∧ (E ∩ A).Nonempty) := by
  sorry

/-- **11.33.** `X = Y ⊕ Z` unicoherent, not a weak triod, `U = X ∖ Z`, `V = X ∖ Y`, `p ∈ U`,
`q ∈ V`. If `Ū = irr(p, Ū ∩ Z)` and `V̄ = irr(q, V̄ ∩ Y)` then `X` is irreducible between `p` and
`q`. -/
theorem nadler_11_33 {X Y Z : Set S} {p q : S} (h : IsEssentialSum₂ X Y Z) (hu : IsUnicoherent X)
    (hnt : ¬ IsWeakTriod X) (hp : p ∈ X \ Z) (hq : q ∈ X \ Y)
    (hU : IrrFromTo (closure (X \ Z)) {p} (closure (X \ Z) ∩ Z))
    (hV : IrrFromTo (closure (X \ Y)) {q} (closure (X \ Y) ∩ Y)) :
    IsIrreducibleBetween X p q := by
  sorry

/-! ## 11.34–11.35 -/

/-- **Sorgenfrey's theorem (Nadler 11.34).** A nondegenerate unicoherent continuum which is not a
triod is irreducible between two of its points. -/
theorem sorgenfrey {X : Set S} (hX : Fold.Q78.IsContinuum X) (hnd : X.Nontrivial)
    (hu : IsUnicoherent X) (hnt : ¬ IsTriod X) : ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween X p q := by
  sorry

/-- **11.35.** A nondegenerate unicoherent continuum is irreducible iff it is not a triod. -/
theorem irreducible_iff_not_isTriod {X : Set S} (hX : Fold.Q78.IsContinuum X) (hnd : X.Nontrivial)
    (hu : IsUnicoherent X) :
    (∃ p q : S, p ≠ q ∧ IsIrreducibleBetween X p q) ↔ ¬ IsTriod X := by
  sorry

/-- Batch 100's `exists_irreducibleBetween_of_atriodic`, sorry-free: atriodic + hereditarily
unicoherent ⇒ irreducible. -/
theorem sorgenfrey_irreducible_of_atriodic_hu {M : Set S} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) :
    ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween M p q := by
  sorry

/-- Fugate's Lemma 3 (⇒), sorry-free (batch 100's `irreducible_of_isTerminalSub` with
`sorgenfrey_irreducible_of_atriodic_hu` discharging its irreducibility hypothesis). -/
theorem isTerminalSub_iff_irreducible' {M A : Set S} (hat : IsAtriodic M)
    (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A) (hAM : A ⊆ M) :
    IsTerminalSub M A ↔ ∀ B : Set S, Fold.Q78.IsContinuum B → B ⊆ M → (B ∩ A).Nonempty →
      ∃ p q : S, p ∈ A ∧ IsIrreducibleBetween (A ∪ B) p q := by
  sorry

end HPC.Plane
