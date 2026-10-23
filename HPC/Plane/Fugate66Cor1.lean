import HPC.Plane.Fugate66B

/-!
# Batch 124: Fugate's Corollary 1 as stated — the condition (U)

Over a compact metric space `S` (the setting of `fugate_cor1`). Fugate (1966, p. 467) states
Corollary 1 without proof; the induction through Theorem 1 that he
presumably intends needs every partial union `A₀ ∪ ⋯ ∪ A_p` to be unicoherent. Condition (U) of
COMMISSION-batch124 §2, in its equivalent form "the whole union is hereditarily unicoherent", is
stated here as an open `Prop` (`FugateU`), and shown to be *equivalent* to the sufficiency half
of Corollary 1 as stated (`fugateU_iff_cor1Sufficiency`): (U) is exactly what is missing, no more.
`fugate_cor1` itself keeps its `sorry` in `HPC/Plane/Fugate66.lean`; `fugate_cor1_of_fugateU`
closes it under (U). The analysis of (U) (open, with the obstruction) is in REPORT-batch124 §Q4.
-/

namespace HPC.Plane

open Set

variable (S : Type*) [MetricSpace S] [CompactSpace S]

/-- **Condition (U)** (open): a finite chain of snake-like continua in `S`, consecutive ones
meeting, whose union is atriodic and unicoherent, has a hereditarily unicoherent union
(equivalently, by `isHereditarilyUnicoherent_union` and induction, every partial union
`A₀ ∪ ⋯ ∪ A_p` is unicoherent). -/
def FugateU : Prop :=
  ∀ (k : ℕ) (A : Fin (k + 1) → Set S), (∀ i, IsSnakeLike (A i)) →
    (∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) →
    IsAtriodic (⋃ i, A i) → IsUnicoherent (⋃ i, A i) → IsHereditarilyUnicoherent (⋃ i, A i)

/-- **The sufficiency half of Fugate's Corollary 1 as stated** (open). -/
def FugateCor1Sufficiency : Prop :=
  ∀ (k : ℕ) (A : Fin (k + 1) → Set S), (∀ i, IsSnakeLike (A i)) →
    (∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) →
    IsAtriodic (⋃ i, A i) → IsUnicoherent (⋃ i, A i) → IsSnakeLike (⋃ i, A i)

variable {S}

/-- **(U) is exactly the missing step.** Under (U), `fugate_cor1'` gives the corollary; conversely a
snake-like union is hereditarily unicoherent (`isHereditarilyUnicoherent_of_isSnakeLike`). -/
theorem fugateU_iff_cor1Sufficiency : FugateU S ↔ FugateCor1Sufficiency S :=
  ⟨fun hU k A hA hmeet hat hu => fugate_cor1' A hA hmeet hat (hU k A hA hmeet hat hu),
    fun hC k A hA hmeet hat hu =>
      isHereditarilyUnicoherent_of_isSnakeLike (hC k A hA hmeet hat hu)⟩

/-- **Corollary 1 as stated, under (U).** -/
theorem fugate_cor1_of_fugateU (hU : FugateU S) {k : ℕ} (A : Fin (k + 1) → Set S)
    (hA : ∀ i, IsSnakeLike (A i)) (hmeet : ∀ i : Fin k, (A i.castSucc ∩ A i.succ).Nonempty) :
    IsSnakeLike (⋃ i, A i) ↔ IsAtriodic (⋃ i, A i) ∧ IsUnicoherent (⋃ i, A i) :=
  ⟨fugate_cor1_necessity A, fun h =>
    fugateU_iff_cor1Sufficiency.mp hU k A hA hmeet h.1 h.2⟩

end HPC.Plane
