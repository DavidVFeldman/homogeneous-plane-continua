import HPC.Plane.Fugate66Cor1

/-!
# Batch 132, Part I: Fugate's Corollary 1 from Theorem 1 and the property (∗)

Skeleton. Save as `HPC/Plane/Fugate66Cor1Proof.lean`, add `import HPC.Plane.Fugate66Cor1Proof` at
the end of the root `HPC.lean`. Every `sorry` is a work item; shapes may be adjusted with the
change recorded.

The argument is `doc/notes/fugate-cor1-proof.md` (uploaded with this commission). It is a hand
proof, never checked before this batch. The property (∗) (`IngramStar`) is a hypothesis here and
is proved in Part II (`HPC/Plane/Ingram68.lean`) from Ingram 1968, Theorem 2(2), and Nadler 12.51.

## The argument

Strong induction on the number of pieces. Let `p` be least with `U_p = A₀ ∪ ⋯ ∪ A_p` not
unicoherent; then `1 ≤ p < k`. Put `Y = U_{p−1}` (chainable), `A = A_p`, `C = Y ∪ A`,
`B = A_{p+1} ∪ ⋯ ∪ A_k`. Then `Y ∩ A` is not connected; write `Y ∩ A = H ⊔ K`.

* Unicoherence of `X` applied to `X = Y ∪ (A ∪ B)` and `X = (Y ∪ B) ∪ A` makes
  `M₁ = Y ∩ (A ∪ B)` and `M₂ = A ∩ (Y ∪ B)` continua with `M₁ ∩ M₂ = H ⊔ K`. So `M₁ ∪ M₂ ⊆ C`
  is not unicoherent, and by (∗) `M₁ ∪ M₂ = C`. Hence `X = Y ∪ B = A ∪ B`.
* Unicoherence of `X` on these two decompositions makes `Y ∩ B` and `A ∩ B` continua meeting in
  `(H ∩ B) ⊔ (K ∩ B)`, both parts nonempty. So `C ∩ B` is not unicoherent, and by (∗)
  `C ∩ B = C`, i.e. `C ⊆ B` (`subset_of_unicoherent_absorb`).
* So `X = B`, a chain of fewer pieces. By induction `X` is chainable, hence hereditarily
  unicoherent, contradicting `C ⊆ X`.

`subset_of_unicoherent_absorb` uses no chainability and no atriodicity: only the unicoherence of
`Y ∪ A ∪ B` and (∗) for `Y ∪ A`.
-/

namespace HPC.Plane

open Set

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **The property (∗)** (Ingram 1968, Theorem 2(2), with Nadler 12.51). Suppose `Y` and `A` are
chainable and meet, `Y ∪ A` is atriodic, and `Y ∩ A` is not connected. Then every proper
subcontinuum of `Y ∪ A` is unicoherent. Proved in Part II as `ingramStar_holds`. -/
def IngramStar (S : Type*) [MetricSpace S] [CompactSpace S] : Prop :=
  ∀ Y A : Set S, IsSnakeLike Y → IsSnakeLike A → (Y ∩ A).Nonempty → IsAtriodic (Y ∪ A) →
    ¬ IsConnected (Y ∩ A) →
    ∀ M ⊆ Y ∪ A, Fold.Q78.IsContinuum M → M ≠ Y ∪ A → IsUnicoherent M

/-- A nonempty compact set that is not connected splits into two disjoint nonempty closed sets.
(`isPreconnected_iff_subset_of_disjoint_fun`, `exists_separated_of_not_isPreconnected`, or
directly.) -/
theorem exists_split_of_not_isConnected {T : Set S} (hT : IsClosed T) (hne : T.Nonempty)
    (hT' : ¬ IsConnected T) :
    ∃ H K : Set S, IsClosed H ∧ IsClosed K ∧ H.Nonempty ∧ K.Nonempty ∧ Disjoint H K ∧
      T = H ∪ K := by
  sorry

/-- A continuum that is the union of two continua meeting in a disconnected set is not
unicoherent. -/
theorem not_isUnicoherent_of_split {P Q : Set S} (hP : Fold.Q78.IsContinuum P)
    (hQ : Fold.Q78.IsContinuum Q) (hPQ : ¬ IsConnected (P ∩ Q)) : ¬ IsUnicoherent (P ∪ Q) := by
  sorry

/-- **Steps 3–5 of the proof: absorption.** Suppose `Y`, `A`, `B` are continua, `A` meets `B`,
`Y ∩ A` is nonempty and not connected, and `Y ∪ A ∪ B` is unicoherent. Suppose also that every
proper subcontinuum of `Y ∪ A` is unicoherent. Then `Y ∪ A ⊆ B`.

Proof (fugate-cor1-proof.md, Steps 3–5).
* `M₁ := Y ∩ (A ∪ B)` is connected, from `X = Y ∪ (A ∪ B)`. Each part of the split
  `Y ∩ A = H ⊔ K` meets `B`. So `Y ∪ B` is a continuum, and `M₂ := A ∩ (Y ∪ B)` is connected,
  from `X = (Y ∪ B) ∪ A`.
* `M₁ ∩ M₂ = Y ∩ A` is not connected (`not_isUnicoherent_of_split`), so `M₁ ∪ M₂ = Y ∪ A`.
  Hence `X = Y ∪ B = A ∪ B`.
* `Y ∩ B` and `A ∩ B` are connected and meet in the disconnected set `Y ∩ A ∩ B`. So
  `(Y ∪ A) ∩ B` is not unicoherent, hence equals `Y ∪ A`. -/
theorem subset_of_unicoherent_absorb {Y A B : Set S}
    (hY : Fold.Q78.IsContinuum Y) (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAB : (A ∩ B).Nonempty) (hYAne : (Y ∩ A).Nonempty) (hYA : ¬ IsConnected (Y ∩ A))
    (hX : IsUnicoherent (Y ∪ A ∪ B))
    (hstar : ∀ M ⊆ Y ∪ A, Fold.Q78.IsContinuum M → M ≠ Y ∪ A → IsUnicoherent M) :
    Y ∪ A ⊆ B := by
  sorry

/-- **Step 1: the partial unions.** If every partial union `A₀ ∪ ⋯ ∪ A_q` with `q ≤ p` is
unicoherent, then `A₀ ∪ ⋯ ∪ A_p` is hereditarily unicoherent (`isHereditarilyUnicoherent_union`,
induction on `q`). State it with the partial-union function you find convenient; `fugate_cor1'`
uses `U p := ⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l`. -/
theorem isHereditarilyUnicoherent_partial {k : ℕ} (A : Fin (k + 1) → Set S)
    (hA : ∀ i, IsSnakeLike (A i)) (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty)
    {p : ℕ} (hp : p ≤ k)
    (hu : ∀ q ≤ p, IsUnicoherent (⋃ (l : Fin (k + 1)) (_ : l.val ≤ q), A l)) :
    IsHereditarilyUnicoherent (⋃ (l : Fin (k + 1)) (_ : l.val ≤ p), A l) := by
  sorry

/-- **Corollary 1, sufficiency, under (∗).** Strong induction on `k`, Steps 1–6 of
fugate-cor1-proof.md. For the induction, a tail `A_{p+1}, …, A_k` is re-indexed as a chain
`Fin (k - p) → Set S`. -/
theorem fugateCor1Sufficiency_of_ingramStar (hstar : IngramStar S) : FugateCor1Sufficiency S := by
  sorry

/-- **Corollary 1 as stated, under (∗).** -/
theorem fugate_cor1_of_ingramStar (hstar : IngramStar S) {k : ℕ} (A : Fin (k + 1) → Set S)
    (hA : ∀ i, IsSnakeLike (A i)) (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  ⟨fugate_cor1_necessity A, fun h =>
    fugateCor1Sufficiency_of_ingramStar hstar k A hA hmeet h.1 h.2⟩

/-- **(U) holds under (∗)** (`fugateU_iff_cor1Sufficiency`). -/
theorem fugateU_of_ingramStar (hstar : IngramStar S) : FugateU S :=
  fugateU_iff_cor1Sufficiency.mpr (fugateCor1Sufficiency_of_ingramStar hstar)

end HPC.Plane
