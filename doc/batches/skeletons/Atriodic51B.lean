import HPC.Plane.Atriodic51CounterArc

/-!
# Bing 1951 (*Snake-like continua*), §4, part two: Theorem 8 with Bing's own elements, and Theorem 9

Skeleton for batch 93 (save as `HPC/Plane/Atriodic51B.lean`; add `import HPC.Plane.Atriodic51B` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded; `theorem8_1951'` keeps its conclusion.

**Correction to batch 92.** Bing's definition (p. 658) is: "for each point `p` let `g_p` denote the
intersection of all continua which contain *interiorly a continuum that* contains `p` interiorly."
The batch-92 skeleton (and §5 of its commission) dropped the inner layer and defined `gElt p` as the
intersection of all continua containing `p` interiorly. `Counter92` refutes the one-layer variant;
it does not touch Bing's. `bingElt` below is Bing's definition. Nothing in the batch-92 files is to
be changed except the ledger note of item 4 of the commission.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- `H` *contains interiorly a continuum that contains `p` interiorly*. -/
def ContainsNested (H : Set S) (p : S) : Prop :=
  ∃ H' : Set S, Fold.Q78.IsContinuum H' ∧ H' ⊆ interior H ∧ p ∈ interior H'

/-- **Bing's elements** (p. 658): the intersection of all continua which contain interiorly a
continuum that contains `p` interiorly. -/
def bingElt (p : S) : Set S := ⋂₀ {H : Set S | Fold.Q78.IsContinuum H ∧ ContainsNested H p}

/-- The one-layer element of batch 92 is contained in Bing's. -/
theorem gElt_subset_bingElt (p : S) : gElt p ⊆ bingElt p := by
  sorry

/-- **Theorem 8** (Bing 1951, p. 658) with Bing's elements; conclusion as in batch 92's
`theorem8_1951`, now for `bingElt`. -/
theorem theorem8_1951' (hS : BingS S) :
    (∀ p : S, Fold.Q78.IsContinuum (bingElt p)) ∧
    (∀ p : S, p ∈ bingElt p) ∧ (∀ p q : S, q ∈ bingElt p → bingElt p = bingElt q) ∧
    (∀ (p : S) (U : Set S), IsOpen U → bingElt p ⊆ U →
      IsOpen (⋃ q ∈ {q | bingElt q ⊆ U}, bingElt q)) ∧
    (∀ p q r : S, bingElt p ≠ bingElt q → bingElt q ≠ bingElt r → bingElt p ≠ bingElt r →
      Separates (bingElt p) (bingElt q) (bingElt r) ∨
        Separates (bingElt q) (bingElt p) (bingElt r) ∨
        Separates (bingElt r) (bingElt p) (bingElt q)) ∧
    (∀ p : S, interior (bingElt p) = ∅) ∧
    (∀ r s : S, (∀ q q' : S, bingElt q ≠ bingElt r → bingElt q' ≠ bingElt r →
          bingElt q ≠ bingElt q' → ¬ Separates (bingElt r) (bingElt q) (bingElt q')) →
      (∀ q q' : S, bingElt q ≠ bingElt s → bingElt q' ≠ bingElt s → bingElt q ≠ bingElt q' →
          ¬ Separates (bingElt s) (bingElt q) (bingElt q')) →
      bingElt r ≠ bingElt s →
      ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) := by
  sorry

namespace Counter92

/-- **The corrected elements on the counterexample**: every bar point's element is the whole bar
`[0, 2] × {0}` (so `G` = {curve points} ∪ {bar}, and the one-layer failure disappears). -/
theorem bingElt_bar {b : S₀} (hb0 : b.1.2 = 0) : bingElt b = {z : S₀ | z.1.2 = 0} := by
  sorry

/-- A curve point's element is itself. -/
theorem bingElt_curve {c : S₀} (hc : c.1.2 ≠ 0) : bingElt c = {c} := by
  sorry

end Counter92

/-- An *end element* of `G`: one that separates no two others. -/
def IsEndElt (hS : BingS S) (r : S) : Prop :=
  ∀ q q' : S, bingElt q ≠ bingElt r → bingElt q' ≠ bingElt r → bingElt q ≠ bingElt q' →
    ¬ Separates (bingElt r) (bingElt q) (bingElt q')

/-- **Bing's collection `H`** (proof of Theorem 9, p. 659): proper subcontinua `h` of `S` such
that whenever `h` is a proper subcontinuum of a subcontinuum `S'`, `S'` is irreducible from `h` to
some point (`IsIrreducibleBetween` is batch 83's `Theorem14.lean` notion, from a point to a point;
irreducibility from a *set* `h` to a point `p` means: `S'` contains `h ∪ {p}` and no proper
subcontinuum of `S'` does). -/
def IrredFromSet (S' h : Set S) (p : S) : Prop :=
  Fold.Q78.IsContinuum S' ∧ h ⊆ S' ∧ p ∈ S' ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ S' → h ⊆ K → p ∈ K → K = S'

def BingH (h : Set S) : Prop :=
  Fold.Q78.IsContinuum h ∧ h ≠ univ ∧
    ∀ S' : Set S, Fold.Q78.IsContinuum S' → h ⊆ S' → h ≠ S' → ∃ p : S, IrredFromSet S' h p

/-- **Step 1 of Theorem 9**: end elements of `G` belong to `H`. -/
theorem endElt_mem_bingH (hS : BingS S) {r : S} (hr : IsEndElt hS r) : BingH (bingElt r) := by
  sorry

/-- **Step 2**: `H` is inductive — the intersection of a decreasing sequence of members is a
member. -/
theorem bingH_iInter (hS : BingS S) {h : ℕ → Set S} (hh : ∀ n, BingH (h n))
    (hanti : Antitone h) : BingH (⋂ n, h n) := by
  sorry

/-- **Step 3**: an irreducible member of `H` (containing no proper sub-member) is a point. -/
theorem bingH_irreducible_singleton (hS : BingS S) {h : Set S} (hh : BingH h)
    (hmin : ∀ h' : Set S, BingH h' → h' ⊆ h → h' = h) : ∃ p : S, h = {p} := by
  sorry

/-- A point `{p}` in `H` satisfies condition A for `S`. -/
theorem condA_of_bingH_singleton (hS : BingS S) {p : S} (hp : BingH {p}) : CondA (univ : Set S) p := by
  sorry

/-- **Theorem 9** (Bing 1951, p. 659): each end element of `G` contains a point satisfying
condition A for `S`. -/
theorem theorem9_1951 (hS : BingS S) {r : S} (hr : IsEndElt hS r) :
    ∃ p ∈ bingElt r, CondA (univ : Set S) p := by
  sorry

end HPC.Plane
