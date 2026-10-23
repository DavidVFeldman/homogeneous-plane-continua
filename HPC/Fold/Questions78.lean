import HPC.Fold.Theorem4
import HPC.PseudoArc.Description

/-!
# Batch 78, §4 questions 3 and 4: statements

Question 3 (a chain from `R` to `S`). `isFrom_ofBlocks_iff` says exactly what Theorem 13 needs
from Theorem 4's consolidation: the block chain is a chain from `R` to `S` iff every fine link
containing `R` is in the first block and every fine link containing `S` is in the last one.
`isFrom_ofBlocks_of_theorem4` is the case in which `R` lies in `E.link r` alone and `S` in
`E.link s` alone; then `theorem4`'s conclusion suffices.

Question 4 (Theorem 10). There is no continuum/indecomposability vocabulary in the repository;
`IsContinuum`, `IsIndecomposable` and the statement `Theorem10Statement` are introduced here
as definitions only (no proof is claimed).
-/

namespace HPC.Fold.Q78

open HPC HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- Theorem 13's hypothesis on the consolidation, exactly: the block chain is a chain from `R`
to `S` iff `R` is in some fine link, every fine link containing `R` is in block `0`, `S` is in
some fine link, and every fine link containing `S` is in the last block. -/
theorem isFrom_ofBlocks_iff {n q : ℕ} (E : Chain X n) (β : Fin n → Fin q) (hβ : IsBlockMap β)
    (hq : 0 < q) (R S : X) :
    (E.ofBlocks β hβ).IsFrom R S ↔
      ((∃ t, R ∈ E.link t) ∧ (∀ t, R ∈ E.link t → (β t).val = 0) ∧
       (∃ t, S ∈ E.link t) ∧ (∀ t, S ∈ E.link t → (β t).val = q - 1)) := by
  constructor
  · rintro ⟨hq', hR, hS, hR1, hS1⟩
    simp only [ofBlocks_link, Set.mem_iUnion, Set.mem_setOf_eq] at hR hS hR1 hS1
    obtain ⟨t, -, ht⟩ := hR
    obtain ⟨t', -, ht'⟩ := hS
    refine ⟨⟨t, ht⟩, fun u hu => ?_, ⟨t', ht'⟩, fun u hu => ?_⟩
    · have := hR1 (β u) ⟨u, rfl, hu⟩
      rw [this]
    · have := hS1 (β u) ⟨u, rfl, hu⟩
      rw [this]
  · rintro ⟨⟨t, ht⟩, hR1, ⟨t', ht'⟩, hS1⟩
    refine ⟨hq, ?_, ?_, ?_, ?_⟩
    · simp only [ofBlocks_link, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨t, Fin.ext (hR1 t ht), ht⟩
    · simp only [ofBlocks_link, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨t', Fin.ext (hS1 t' ht'), ht'⟩
    · intro u hu
      simp only [ofBlocks_link, Set.mem_iUnion, Set.mem_setOf_eq] at hu
      obtain ⟨v, hv, hRv⟩ := hu
      rw [← hv]
      exact Fin.ext (hR1 v hRv)
    · intro u hu
      simp only [ofBlocks_link, Set.mem_iUnion, Set.mem_setOf_eq] at hu
      obtain ⟨v, hv, hSv⟩ := hu
      rw [← hv]
      exact Fin.ext (hS1 v hSv)

/-- When `R` lies in `E.link r` alone and `S` in `E.link s` alone, the conclusion of `theorem4`
(`β r = 0`, `β s = q - 1`) makes the consolidation a chain from `R` to `S`. -/
theorem isFrom_ofBlocks_of_theorem4 {n q : ℕ} (E : Chain X n) (β : Fin n → Fin q)
    (hβ : IsBlockMap β) (r s : Fin n) (hr : (β r).val = 0) (hs : (β s).val = q - 1) (R S : X)
    (hR : R ∈ E.link r) (hRonly : ∀ t, R ∈ E.link t → t = r)
    (hS : S ∈ E.link s) (hSonly : ∀ t, S ∈ E.link t → t = s) :
    (E.ofBlocks β hβ).IsFrom R S := by
  have hq : 0 < q := Fin.pos (β r)
  rw [isFrom_ofBlocks_iff E β hβ hq]
  refine ⟨⟨r, hR⟩, fun t ht => ?_, ⟨s, hS⟩, fun t ht => ?_⟩
  · rw [hRonly t ht, hr]
  · rw [hSonly t ht, hs]

/-- A continuum: a nonempty compact connected set. -/
def IsContinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K

/-- An indecomposable continuum: not the union of two proper subcontinua. -/
def IsIndecomposable (K : Set X) : Prop :=
  IsContinuum K ∧ ∀ A B : Set X, IsContinuum A → IsContinuum B → A ⊆ K → B ⊆ K →
    A ∪ B = K → A = K ∨ B = K

/-- **Bing 1948, Theorem 10** (statement only): every subcontinuum of the described
continuum `M` is indecomposable. -/
def Theorem10Statement {P Q : X} (Δ : Description X P Q) : Prop :=
  ∀ K : Set X, K ⊆ Δ.M → IsContinuum K → IsIndecomposable K

end HPC.Fold.Q78
