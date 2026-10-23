import HPC.Plane.LastLink99

/-!
# Batch 100: Fugate 1966 — terminal subcontinua, Lemma 1 in general, Lemma 3, Theorem 1 (gluing),
# Corollaries 1–2

Skeleton (save as `HPC/Plane/Fugate66.lean`; add `import HPC.Plane.Fugate66` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded.

Source: J. B. Fugate, *Decomposable chainable continua*, Trans. Amer. Math. Soc. 123 (1966),
460–468. Definitions 3–5, Lemmas 1–4, Theorem 1, Corollaries 1–2 (COMMISSION-batch100.md §1
transcribes them). `IsAtriodic`, `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsTriod` are
batch 92's (Bing's definitions, over a compact metric space `S`); Fugate's triod (Definition 1:
`X = A ∪ B ∪ D` with `A ∩ B = B ∩ D = A ∩ D = A ∩ B ∩ D` a proper subset of each) is recorded as
`IsFugateTriod` and compared.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Definitions -/

/-- **Fugate, Definition 4.** `A` is a *terminal subcontinuum* of `M`: for subcontinua `K`, `L` of
`M` both meeting `A`, `K ⊆ A ∪ L` or `L ⊆ K ∪ A`. (Degenerate `A = {p}`: Bing's condition B.) -/
def IsTerminalSub (M A : Set S) : Prop :=
  Fold.Q78.IsContinuum A ∧ A ⊆ M ∧
    ∀ K L : Set S, Fold.Q78.IsContinuum K → Fold.Q78.IsContinuum L → K ⊆ M → L ⊆ M →
      (K ∩ A).Nonempty → (L ∩ A).Nonempty → K ⊆ A ∪ L ∨ L ⊆ K ∪ A

theorem isTerminalSub_singleton_iff (M : Set S) (p : S) (hM : Fold.Q78.IsContinuum M) :
    IsTerminalSub M {p} ↔ CondB M p := by
  sorry

/-- **Fugate, Definition 1** (a triod, Sorgenfrey's form). -/
def IsFugateTriod (X : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ ∃ A B D : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧
    Fold.Q78.IsContinuum D ∧ A ≠ X ∧ B ≠ X ∧ D ≠ X ∧ X = A ∪ B ∪ D ∧
    A ∩ B = A ∩ B ∩ D ∧ B ∩ D = A ∩ B ∩ D ∧ A ∩ D = A ∩ B ∩ D ∧
    A ∩ B ∩ D ≠ A ∧ A ∩ B ∩ D ≠ B ∧ A ∩ B ∩ D ≠ D

/-- The two notions of triod agree for continua in a compact metric space (Sorgenfrey 1944;
prove or state the direction that holds). -/
theorem isFugateTriod_iff_isTriod {X : Set S} : IsFugateTriod X ↔ IsTriod X := by
  sorry

/-- **Sorgenfrey's lemma** (Fugate's "[8, p. 440]"): three continua, pairwise intersecting, none
contained in the union of the other two — their union is a triod. (Bing's property 3 in
general form, with no `BingS` hypothesis.) -/
theorem isTriod_union_of_three {A B D : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hD : Fold.Q78.IsContinuum D)
    (hAB : (A ∩ B).Nonempty) (hBD : (B ∩ D).Nonempty) (hAD : (A ∩ D).Nonempty)
    (nA : ¬ A ⊆ B ∪ D) (nB : ¬ B ⊆ A ∪ D) (nD : ¬ D ⊆ A ∪ B) : IsTriod (A ∪ B ∪ D) := by
  sorry

/-- **Sorgenfrey: an atriodic hereditarily unicoherent continuum is irreducible** between two of
its points (used in Fugate's Lemma 3). -/
theorem exists_irreducibleBetween_of_atriodic {M : Set S} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) :
    ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween M p q := by
  sorry

/-! ## Lemma 3 -/

/-- **Fugate, Lemma 3.** In an atriodic hereditarily unicoherent continuum `M`, a subcontinuum `A`
is terminal iff for every subcontinuum `B` meeting `A`, `A ∪ B` is irreducible between two points
one of which lies in `A`. -/
theorem isTerminalSub_iff_irreducible {M A : Set S} (hM : Fold.Q78.IsContinuum M)
    (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A)
    (hAM : A ⊆ M) :
    IsTerminalSub M A ↔ ∀ B : Set S, Fold.Q78.IsContinuum B → B ⊆ M → (B ∩ A).Nonempty →
      ∃ p q : S, p ∈ A ∧ IsIrreducibleBetween (A ∪ B) p q := by
  sorry

/-! ## Lemma 1 (general) and Lemma 2 -/

/-- **Fugate, Lemma 1** (Bing's Theorem 10 for terminal subcontinua). `M` atriodic, hereditarily
unicoherent; `A` terminal in `M`; `E` a chain covering `M`. Then there is a chain `F` covering
`M`, refining `E`, whose last link meets `A` outside the closure of the previous link. (Tautness
is omitted here; see `IsTaut` below.) -/
theorem fugate_lemma1 {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hat : IsAtriodic M)
    (hhu : IsHereditarilyUnicoherent M) (hA : IsTerminalSub M A) {m : ℕ} (E : Chain S m)
    (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (hn : 0 < n), M ⊆ F.union ∧ F.Refines E ∧
      (A ∩ (F.link ⟨n - 1, by omega⟩ \ closure (⋃ j : Fin n, ⋃ (_ : j.val ≠ n - 1), F.link j))).Nonempty := by
  sorry

/-- `A` is *contained exactly* in the subchain `F(s..n−1)` (Fugate, Definition 5): `A` lies in its
union, in no proper subchain's union, and misses the closure of the other links. -/
def ContainedExactly {n : ℕ} (F : Chain S n) (A : Set S) (s : ℕ) : Prop :=
  s < n ∧ A ⊆ ⋃ (i : Fin n) (_ : s ≤ i.val), F.link i ∧
    (∀ s' : ℕ, s < s' → ¬ A ⊆ ⋃ (i : Fin n) (_ : s' ≤ i.val), F.link i) ∧
    (A ∩ closure (⋃ (i : Fin n) (_ : i.val < s), F.link i)) = ∅

/-- **Fugate, Lemma 2**: Lemma 1 with the conclusion in the exact-containment form. -/
theorem fugate_lemma2 {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hat : IsAtriodic M)
    (hhu : IsHereditarilyUnicoherent M) (hA : IsTerminalSub M A) {m : ℕ} (E : Chain S m)
    (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧ ContainedExactly F A s := by
  sorry

/-! ## Theorem 1 and its corollaries -/

/-- **Fugate, Theorem 1 (the gluing).** `A`, `B` snake-like with `A ∩ B ≠ ∅`: `A ∪ B` is snake-like
iff it is atriodic and unicoherent. (Necessity is batch 96's; the content is sufficiency: Claim 1
makes `A ∩ B` terminal in both via Sorgenfrey's lemma, Lemma 4 fits the chains, and the
two-case construction of the `ε`-chain follows.) -/
theorem fugate_theorem1 {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) :
    IsSnakeLike (A ∪ B) ↔ IsAtriodic (A ∪ B) ∧ IsUnicoherent (A ∪ B) := by
  sorry

/-- **Corollary 1.** A finite chain of snake-like continua, consecutive ones meeting: the union is
snake-like iff atriodic and unicoherent. -/
theorem fugate_cor1 {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) := by
  sorry

/-- **Corollary 2.** A decomposable unicoherent continuum all of whose proper subcontinua are
snake-like is snake-like. -/
theorem fugate_cor2 {M : Set S} (hM : Fold.Q78.IsContinuum M) (hu : IsUnicoherent M)
    (hdec : ∃ A B : Set S, Fold.Q78.IsContinuum A ∧ Fold.Q78.IsContinuum B ∧ A ≠ M ∧ B ≠ M ∧
      A ∪ B = M)
    (hsub : ∀ K ⊆ M, Fold.Q78.IsContinuum K → K ≠ M → IsSnakeLike K) : IsSnakeLike M := by
  sorry

/-! ## Tautness (Fugate §2, Barrett) — optional -/

/-- A chain is *taut* when nonadjacent links are at positive distance. -/
def IsTaut {n : ℕ} (F : Chain S n) : Prop :=
  ∀ i j : Fin n, 1 < (i.val : ℤ) - j.val ∨ 1 < (j.val : ℤ) - i.val → 0 < infDist' (F.link i) (F.link j)
where infDist' (U V : Set S) : ℝ := ⨅ (x : U) (y : V), dist x.1 y.1

/-- **Barrett's Proposition 1** (as used by Fugate): a snake-like continuum has, for each `ε`, a
taut `ε`-chain covering it with every link meeting it. Optional; needed only if Lemma 4 is done
with tautness as Fugate writes it. -/
theorem exists_taut_epsChain {M : Set S} (hM : IsSnakeLike M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (F : Chain S n), IsEpsChain F ε ∧ M ⊆ F.union ∧ IsTaut F ∧
      ∀ i, (F.link i ∩ M).Nonempty := by
  sorry

end HPC.Plane
