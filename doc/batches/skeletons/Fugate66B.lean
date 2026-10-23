import HPC.Plane.Fugate66Lemma1

/-!
# Batch 101: Fugate 1966, Lemma 2 (corrected), Miller's theorem, Lemma 4, Theorem 1 (sufficiency),
# Corollary 1

Skeleton (save as `HPC/Plane/Fugate66B.lean`; add `import HPC.Plane.Fugate66B` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. Nothing in an existing file is to be edited; if `fugate_theorem1_sufficiency'`
closes, batch 100's `fugate_theorem1_sufficiency`, `fugate_theorem1`, `fugate_cor2` keep their
`sorry` until the pruning pass (import order), and the report says so.

Source: Fugate 1966, pp. 463–467, transcribed in COMMISSION-batch101.md §1 from the scan.
Chains are 0-indexed here: Fugate's `E(1,m)` is `E.link 0 … E.link (m−1)`.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Definition 5, corrected -/

/-- **Fugate, Definition 5.** `A` is *contained exactly* in the subchain `F(j..k)`:
(1) `A ⊆ F*(j..k)`; (2) `A` lies in no proper subchain of `F(j..k)` — equivalently `A` meets
`F_j` and `A` meets `F_k` (and `j ≤ k`); (3) `A` misses the closures of `F*(0..j−1)` and
`F*(k+1..n−1)`. Batch 100's `ContainedExactly` omitted the second half of (2). -/
def ContainedExactly' {n : ℕ} (F : Chain S n) (A : Set S) (j k : ℕ) : Prop :=
  j ≤ k ∧ k < n ∧ A ⊆ ⋃ (i : Fin n) (_ : j ≤ i.val ∧ i.val ≤ k), F.link i ∧
    (A ∩ F.link ⟨j, by omega⟩).Nonempty ∧ (A ∩ F.link ⟨k, by omega⟩).Nonempty ∧
    A ∩ closure (⋃ (i : Fin n) (_ : i.val < j), F.link i) = ∅ ∧
    A ∩ closure (⋃ (i : Fin n) (_ : k < i.val), F.link i) = ∅

/-- **Lemma 2, corrected**: `A ⊆ᵉ F*(s..n−1)` with `A` meeting the last link. Fugate: from Lemma 1
(`A` meets `F_n − Cl F_{n−1}`), take the least `s` with `A ⊆ F*(s..n−1)`; if `Cl F_{s−1}` meets
`A`, separate `A` from `M − F*(s..n−1)` by disjoint open `Y ⊇ A`, `W ⊇ M − F*(s..n−1)` and cut
the earlier links down to `F_i ∩ W`. -/
theorem fugate_lemma2' {M A : Set S} (hM : Fold.Q78.IsContinuum M) (hA : IsTerminalSub M A)
    {m : ℕ} (E : Chain S m) (hE : M ⊆ E.union) :
    ∃ (n : ℕ) (F : Chain S n) (s : ℕ), M ⊆ F.union ∧ F.Refines E ∧
      ContainedExactly' F A s (n - 1) := by
  sorry

/-! ## Miller's theorem (Fugate's "[6, Theorem 1.5, p. 180]") -/

/-- **Miller 1950, Theorem 1.5, as Fugate uses it.** If `A`, `B` are continua, `A ∪ B` is
unicoherent, and `D ⊆ A ∪ B` is a subcontinuum that is not unicoherent, then `D ⊆ A` or
`D ⊆ B`. Prove, or refute and state the hypotheses that make it true (the disk cut in two
half-disks, with a circle straddling the cut, is a candidate refutation of the bare statement;
Miller's hypotheses may include that `A ∩ B` is connected or that `A`, `B` are hereditarily
unicoherent). -/
theorem miller_1_5 {A B D : Set S} (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hu : IsUnicoherent (A ∪ B)) (hD : Fold.Q78.IsContinuum D) (hDAB : D ⊆ A ∪ B)
    (hDnu : ¬ IsUnicoherent D) : D ⊆ A ∨ D ⊆ B := by
  sorry

/-- **What Theorem 1 needs from Miller**: `A`, `B` snake-like (hence hereditarily unicoherent),
`A ∪ B` unicoherent ⇒ `A ∪ B` hereditarily unicoherent. Prove (from `miller_1_5` or directly), or
refute. -/
theorem hu_union_of_snakeLike {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) (hu : IsUnicoherent (A ∪ B)) :
    IsHereditarilyUnicoherent (A ∪ B) := by
  sorry

/-! ## Lemma 4 -/

/-- **Fugate, Lemma 4 (the fitting).** `A`, `B` snake-like, `A ∩ B ≠ ∅`, `A ∩ B` terminal in both.
For every `ε > 0` there are `ε`-chains `E = E(0..m−1)` covering `A` and `F = F(0..n−1)` covering
`B` and indices `j ≤ m−1`, `k ≤ n−1`, `t` with `j ≤ t ≤ m−1`, such that
1. both are taut `ε`-chains covering `A`, `B`;
2. `A ∩ B ⊆ᵉ E*(j..m−1)` and `A ∩ B ⊆ᵉ F*(k..n−1)`;
3. `F(k..n−1)` is a closed refinement of `E(j..m−1)` (closure of each link in some link);
4. `Cl E*(0..j−1) ∩ F* = ∅`;
5. `Cl F*(0..k−2) ∩ E* = ∅`;
6. `Cl F_{k−1} ∩ A = ∅`, `Cl F_{k−1} ∩ E* ⊆ E_t`, and `Cl F_{k−1}` meets no other link of `E`.
(Tautness as batch 100's `IsTaut`; `k ≥ 1` is implicit in (5)–(6) — if `k = 0` the clauses
about `F_{k−1}` are vacuous; record how the edge case is handled.) -/
theorem fugate_lemma4 {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) (hTA : IsTerminalSub A (A ∩ B)) (hTB : IsTerminalSub B (A ∩ B))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (E : Chain S m) (F : Chain S n) (j k t : ℕ),
      IsEpsChain E ε ∧ IsEpsChain F ε ∧ IsTaut E ∧ IsTaut F ∧ A ⊆ E.union ∧ B ⊆ F.union ∧
      ContainedExactly' E (A ∩ B) j (m - 1) ∧ ContainedExactly' F (A ∩ B) k (n - 1) ∧
      (∀ i : Fin n, k ≤ i.val → ∃ i' : Fin m, j ≤ i'.val ∧ closure (F.link i) ⊆ E.link i') ∧
      Disjoint (closure (⋃ (i : Fin m) (_ : i.val < j), E.link i)) F.union ∧
      Disjoint (closure (⋃ (i : Fin n) (_ : i.val + 2 ≤ k), F.link i)) E.union ∧
      (1 ≤ k → j ≤ t ∧ t < m ∧
        Disjoint (closure (F.link ⟨k - 1, by omega⟩)) A ∧
        closure (F.link ⟨k - 1, by omega⟩) ∩ E.union ⊆ E.link ⟨t, by omega⟩ ∧
        ∀ i : Fin m, i.val ≠ t → Disjoint (closure (F.link ⟨k - 1, by omega⟩)) (E.link i)) := by
  sorry

/-! ## Theorem 1, sufficiency -/

/-- **Fugate, Theorem 1 (sufficiency)**, from Lemma 4 by the two-case construction of p. 466–467. -/
theorem fugate_theorem1_sufficiency' {A B : Set S} (hA : IsSnakeLike A) (hB : IsSnakeLike B)
    (hAB : (A ∩ B).Nonempty) (hat : IsAtriodic (A ∪ B)) (hu : IsUnicoherent (A ∪ B)) :
    IsSnakeLike (A ∪ B) := by
  sorry

/-! ## Corollary 1 -/

/-- **Corollary 1, with the hypothesis Fugate's induction needs.** State and prove the version that
holds: with the whole union *hereditarily* unicoherent the induction through Theorem 1 runs; if
Fugate's weaker hypothesis (unicoherent) suffices by Miller's theorem, prove that instead and
record it. -/
theorem fugate_cor1' {k : ℕ} (A : Fin (k + 1) → Set S) (hA : ∀ i, IsSnakeLike (A i))
    (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty)
    (hat : IsAtriodic (⋃ i, A i)) (hhu : IsHereditarilyUnicoherent (⋃ i, A i)) :
    IsSnakeLike (⋃ i, A i) := by
  sorry

end HPC.Plane
