import HPC.Plane.Fugate66Cor1Proof
import HPC.Plane.Sorgenfrey
import HPC.Plane.Arcs48
import HPC.Plane.Fugate66Lemma1

/-!
# Batch 132, Part II: Ingram 1968 (decomposable circle-like continua) and the property (∗);
# Fugate's Corollary 1 proved

Skeleton. Save as `HPC/Plane/Ingram68.lean`, add `import HPC.Plane.Ingram68` at the end of the
root `HPC.lean` (after `Fugate66Cor1Proof`). Every `sorry` is a work item; shapes may be adjusted
with the change recorded. Fix the imports to whatever the declarations below need.

Source: W. T. Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198
(uploaded with this commission; save it as `doc/sources/ingram1968.pdf`). The statements below
are Ingram's; COMMISSION-batch132.md §3 transcribes his proofs.

## Route

(∗) = `IngramStar S`. Ingram's route has five steps.
1. Sorgenfrey: a weak triod contains a triod.
2. Ingram's Lemmas 1–3.
3. Ingram's Theorem 1: an ε-chain whose two end links meet two given terminal subcontinua.
4. Theorem 2(2), sufficiency: `Y ∪ A` is circle-like.
5. A proper subcontinuum of a circle-like continuum is chainable (Nadler 12.51: drop the link
   containing a point outside it), hence unicoherent.

A direct proof of (∗) that does not pass through circle-likeness is equally acceptable (report
which route was taken). The deliverable is `ingramStar_holds`, and then `fugate_cor1` without
`sorry`.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ### Circular chains and circle-likeness -/

/-- Cyclic distance on `Fin n`. -/
def cycDist {n : ℕ} (i j : Fin n) : ℕ := min ((i : ℤ) - j).natAbs (n - ((i : ℤ) - j).natAbs)

/-- A **circular chain** of length `n`: open links, `link i` meeting `link j` iff their cyclic
distance is at most `1` (Bing 1951, §1; Ingram's "circular chain"). For `n ≤ 3` every two links
meet. -/
structure CircChain (X : Type*) [MetricSpace X] (n : ℕ) where
  link : Fin n → Set X
  isOpen : ∀ i, IsOpen (link i)
  adjacent : ∀ i j : Fin n, (link i ∩ link j).Nonempty ↔ cycDist i j ≤ 1

/-- The union of the links. -/
def CircChain.union {X : Type*} [MetricSpace X] {n : ℕ} (D : CircChain X n) : Set X :=
  ⋃ i, D.link i

/-- An `ε`-circular chain: bounded links of diameter `< ε`. -/
def IsCircEpsChain {X : Type*} [MetricSpace X] {n : ℕ} (D : CircChain X n) (ε : ℝ) : Prop :=
  ∀ i, Bornology.IsBounded (D.link i) ∧ Metric.diam (D.link i) < ε

/-- **Circle-like** (circularly chainable): a continuum covered by an `ε`-circular chain for every
`ε > 0`. -/
def IsCircleLike {X : Type*} [MetricSpace X] (M : Set X) : Prop :=
  Fold.Q78.IsContinuum M ∧
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : CircChain X n), IsCircEpsChain D ε ∧ M ⊆ D.union

/-- **Nadler 12.51.** A proper subcontinuum of a circle-like continuum is chainable. Pick
`x ∈ C ∖ Z` and `ε < infDist x Z`. In an `ε`-circular chain covering `C`, a link containing `x`
misses `Z`. The remaining links, read cyclically from the next index, form a chain covering `Z`
(the two neighbours of the removed link have cyclic distance `2` when `n ≥ 4`, and are
consecutive when `n = 3`). Degenerate `Z` is a point and is chainable directly. -/
theorem isSnakeLike_of_subset_circleLike {C Z : Set S} (hC : IsCircleLike C)
    (hZ : Fold.Q78.IsContinuum Z) (hZC : Z ⊆ C) (hne : Z ≠ C) : IsSnakeLike Z := by
  sorry

/-! ### Sorgenfrey: a weak triod contains a triod -/

/-- **Sorgenfrey 1944, Theorem 1.8** (Ingram's "[7], Theorem 1.8, p. 443"; Bennett–Fugate 1977,
p. 20: "each type 1 triod contains a type 3 triod"). Three continua with a common point, none
contained in the union of the other two: their union contains a triod. `IsWeakTriod` is
`SorgenfreyDefs.lean`'s (Nadler 11.24). Refutation candidate: check the hypotheses against
`isTriod_union_of_three` (which needs hereditary unicoherence and gives the union itself as the
triod); here only *containment* of a triod is claimed. -/
theorem exists_isTriod_of_isWeakTriod {X : Set S} (h : IsWeakTriod X) :
    ∃ T ⊆ X, IsTriod T := by
  sorry

/-- Restated for use: in an atriodic continuum, three subcontinua with a common point cannot all
be outside the union of the other two. -/
theorem not_three_of_isAtriodic {X P Q R : Set S} (hX : IsAtriodic X)
    (hP : Fold.Q78.IsContinuum P) (hQ : Fold.Q78.IsContinuum Q) (hR : Fold.Q78.IsContinuum R)
    (hPX : P ⊆ X) (hQX : Q ⊆ X) (hRX : R ⊆ X) (hcommon : (P ∩ Q ∩ R).Nonempty) :
    P ⊆ Q ∪ R ∨ Q ⊆ P ∪ R ∨ R ⊆ P ∪ Q := by
  sorry

/-! ### Ingram's lemmas -/

/-- **Ingram, Lemma 1.** If `A ∩ B` has at least three components, then `A ∪ B` contains a triod.
Used form: in an atriodic `A ∪ B`, a nonempty disconnected `A ∩ B` is the union of two disjoint
continua. -/
theorem ingram_lemma1 {A B : Set S} (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hat : IsAtriodic (A ∪ B)) (hne : (A ∩ B).Nonempty) (hnc : ¬ IsConnected (A ∩ B)) :
    ∃ H K : Set S, Fold.Q78.IsContinuum H ∧ Fold.Q78.IsContinuum K ∧ Disjoint H K ∧
      A ∩ B = H ∪ K := by
  sorry

/-- **Ingram, Lemma 2.** Suppose `A ∩ B` is the union of two disjoint continua `H`, `K`, and
`A ∪ B` is atriodic. Then `H` and `K` are terminal subcontinua of `A`, and `A` is irreducible
about `H ∪ K`. -/
theorem ingram_lemma2 {A B H K : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K)
    (hHK : Disjoint H K) (hAB : A ∩ B = H ∪ K) (hat : IsAtriodic (A ∪ B)) :
    IsTerminalSub A H ∧ IsTerminalSub A K ∧ IrreducibleAbout A (H ∪ K) := by
  sorry

/-- **Ingram, Lemma 3.** Suppose `A ∩ B` is the union of two disjoint continua `K`, `L`, and
`A ∪ B` is atriodic. If `H ⊆ A ∪ B` is a continuum that meets `A ∖ K` but not `L`, then `H ∩ A`
is a continuum. -/
theorem ingram_lemma3 {A B K L H : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hK : Fold.Q78.IsContinuum K) (hL : Fold.Q78.IsContinuum L)
    (hKL : Disjoint K L) (hAB : A ∩ B = K ∪ L) (hat : IsAtriodic (A ∪ B))
    (hH : Fold.Q78.IsContinuum H) (hHAB : H ⊆ A ∪ B) (hHA : (H ∩ (A \ K)).Nonempty)
    (hHL : Disjoint H L) : Fold.Q78.IsContinuum (H ∩ A) := by
  sorry

/-! ### Ingram's Theorem 1 -/

/-- **Ingram, Theorem 1.** If `H` and `K` are disjoint terminal subcontinua of the chainable
continuum `M`, `M` is irreducible about `H ∪ K`, and `ε > 0`, then there is an `ε`-chain
covering `M` whose first link has a point of `H` outside the closure of the other links, and
whose last link has a point of `K` outside the closure of the other links. (Same end-link
convention as `fugate_lemma1`. Ingram's proof uses Fugate's Lemma 1 and Cook's regular-chain
theorem; `exists_taut_epsChain` exists.) -/
theorem ingram_theorem1 {M H K : Set S} (hM : IsSnakeLike M) (hHt : IsTerminalSub M H)
    (hKt : IsTerminalSub M K) (hHK : Disjoint H K) (hirr : IrreducibleAbout M (H ∪ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (D : Chain S n) (hn : 0 < n), IsEpsChain D ε ∧ M ⊆ D.union ∧
      (H ∩ (D.link ⟨0, hn⟩ \ closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ 0), D.link j))).Nonempty ∧
      (K ∩ (D.link ⟨n - 1, by omega⟩ \
        closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ n - 1), D.link j))).Nonempty := by
  sorry

/-! ### Ingram's Theorem 2(2), sufficiency, and (∗) -/

/-- **Ingram, Theorem 2(2), sufficiency.** If `Y`, `A` are chainable continua that meet,
`Y ∪ A` is atriodic, and `Y ∩ A` is not connected, then `Y ∪ A` is circle-like. Ingram's
construction is in COMMISSION-batch132.md §3.5. -/
theorem ingram_theorem2_circleLike {Y A : Set S} (hY : IsSnakeLike Y) (hA : IsSnakeLike A)
    (hne : (Y ∩ A).Nonempty) (hat : IsAtriodic (Y ∪ A)) (hnc : ¬ IsConnected (Y ∩ A)) :
    IsCircleLike (Y ∪ A) := by
  sorry

/-- **(∗) holds.** From `ingram_theorem2_circleLike`, `isSnakeLike_of_subset_circleLike` and
`isUnicoherent_of_isSnakeLike`. (Or by a direct route; report.) -/
theorem ingramStar_holds : IngramStar S := by
  sorry

/-- **Fugate 1966, Corollary 1** (p. 467), as stated, every clause. A finite chain of
snake-like continua, consecutive ones meeting: the union is snake-like iff it is atriodic and
unicoherent. Fugate states it without proof. Proved from Theorem 1 and (∗)
(`fugate_cor1_of_ingramStar`, `ingramStar_holds`). (∗) rests on Ingram 1968, which postdates
Fugate 1966. The sorried declaration of the same name in `Fugate66.lean` is deleted in this
batch (COMMISSION-batch132.md §2). -/
theorem fugate_cor1 {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  fugate_cor1_of_ingramStar ingramStar_holds A hA hmeet

/-- **(U) holds.** -/
theorem fugateU_holds : FugateU S := fugateU_of_ingramStar ingramStar_holds

end HPC.Plane
