import HPC.Plane.Sorgenfrey

/-!
# Batch 104: Bing's Theorem 11 (Duke 1951) by Fugate 1969, Case II

Skeleton (save as `HPC/Plane/Theorem11B.lean`; add `import HPC.Plane.Theorem11B` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. Nothing in an existing file is to be edited; `theorem11_1951_of_T10'`
(`Layers51.lean`) keeps its `sorry` by import order and `theorem11_1951` here is the sorry-free
form (pruning list).

Source: J. B. Fugate, *A characterization of chainable continua*, Canad. J. Math. 21 (1969),
383–393: Lemma 3, Lemma 4, Theorem 2 Case II (COMMISSION-batch104.md §1 transcribes them).
Fugate's arc structure `f : M → [0,1]` is replaced by the two sides of an element (batch 96) and
Theorem 8 (a). `IsTerminalSub` is batch 100's (Fugate's Definition 1 = Definition 4 of 1966).
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Fugate 1969, Lemmas 3 and 4 (hereditarily decomposable case) -/

/-- **Lemma 3.** `M` atriodic, hereditarily unicoherent; `K` terminal in `M`; `K = A ∪ B` with
`A`, `B` proper subcontinua of `K`. Then `A` or `B` is terminal in `M`. (Proof via Lemma 2 =
`isTerminalSub_iff_irreducible'`.) -/
theorem isTerminalSub_of_union_terminal {M K A B : Set S} (hM : Fold.Q78.IsContinuum M)
    (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) (hK : IsTerminalSub M K)
    (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B) (hAK : A ≠ K) (hBK : B ≠ K)
    (hAB : A ∪ B = K) : IsTerminalSub M A ∨ IsTerminalSub M B := by
  sorry

/-- Terminality is inductive: the intersection of a decreasing sequence of terminal subcontinua
is terminal (Lemma 4's "Property P is inductive"). -/
theorem isTerminalSub_iInter {M : Set S} (hM : Fold.Q78.IsContinuum M) {N : ℕ → Set S}
    (hN : ∀ n, IsTerminalSub M (N n)) (hanti : Antitone N) : IsTerminalSub M (⋂ n, N n) := by
  sorry

/-- **Lemma 4, hereditarily decomposable case.** A terminal subcontinuum `K` of an atriodic,
hereditarily unicoherent, hereditarily decomposable `M` contains a terminal point of `M`
(condition B). -/
theorem exists_terminal_point_of_isTerminalSub {M K : Set S} (hM : Fold.Q78.IsContinuum M)
    (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) (hhd : IsHereditarilyDecomposable M)
    (hK : IsTerminalSub M K) : ∃ μ ∈ K, CondB M μ := by
  sorry

/-! ## The two halves of a `BingS` space at an interior element -/

/-- With `g' = bingElt r` interior and sides `U`, `V` (batch 96): `A = U ∪ g'`, `B = V ∪ g'`,
and `C = closure V` (Fugate's `Cl(B − A)`); `A ∪ C = univ`, `A ∩ C ⊆ g'`, and `A ∩ C` is
terminal in `A` and in `C` (Remark 1 for `M = A ∪ C`). -/
theorem halves_terminal (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    Fold.Q78.IsContinuum (closure V) ∧ (U ∪ bingElt r) ∪ closure V = univ ∧
      (U ∪ bingElt r) ∩ closure V ⊆ bingElt r ∧
      IsTerminalSub (U ∪ bingElt r) ((U ∪ bingElt r) ∩ closure V) ∧
      IsTerminalSub (closure V) ((U ∪ bingElt r) ∩ closure V) := by
  sorry

/-- **Claim 1 (Fugate, p. 391).** A subcontinuum `Q` of `C = closure V` meeting `A ∩ C` and not
contained in it contains `A ∩ C`. (Fugate: via `f⁻¹[½, f(s)]`; here via the elements between `g'`
and the element of a point of `Q` in `V`, Theorem 8 (a) and the sides.) -/
theorem claim1_contains_inter (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) {Q : Set S} (hQ : Fold.Q78.IsContinuum Q)
    (hQC : Q ⊆ closure V) (hmeet : (Q ∩ (U ∪ bingElt r) ∩ closure V).Nonempty)
    (hnot : ¬ Q ⊆ (U ∪ bingElt r) ∩ closure V) :
    (U ∪ bingElt r) ∩ closure V ⊆ Q := by
  sorry

/-- **The terminal point of both halves** (Fugate: Lemma 4 applied to `A ∩ C` in `A`, then "`K` is
a terminal subcontinuum of `Cl(B − A)`" via Claim 1 and a triod): there is `μ ∈ A ∩ C` with
`CondB A μ` and `CondB C μ`. -/
theorem exists_mu (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    ∃ μ ∈ (U ∪ bingElt r) ∩ closure V, CondB (U ∪ bingElt r) μ ∧ CondB (closure V) μ := by
  sorry

/-! ## Claim 2 and the amalgamation -/

/-- **Claim 2 + the chain (Fugate, p. 392), abstracted.** `A`, `C` continua with `A ∪ C = M`;
`μ ∈ A ∩ C`; Claim 1 holds for `C` relative to `A` (every subcontinuum of `C` meeting `A ∩ C` and
not inside it contains `A ∩ C`); `E` an `ε`-chain covering `A` with `μ` in the last link and in the
closure of no other; `F` likewise for `C`; `M` hereditarily unicoherent. Then `M` is covered by an
`ε`-chain (links of diameter `< ε` after shrinking the middle links as needed; state the mesh
actually obtained, e.g. from `ε/2`-chains `E`, `F`). -/
theorem epsCoverable_of_halves {M A C : Set S} (hM : Fold.Q78.IsContinuum M)
    (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A)
    (hC : Fold.Q78.IsContinuum C) (hAC : A ∪ C = M) {μ : S} (hμ : μ ∈ A ∩ C)
    (hclaim1 : ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q)
    {ε : ℝ} (hε : 0 < ε)
    (hE : ∃ (x : ℕ) (E : Chain S x) (hx : 0 < x), IsEpsChain E (ε / 2) ∧ A ⊆ E.union ∧
      μ ∈ E.link ⟨x - 1, by omega⟩ ∧ ∀ j : Fin x, j.val ≠ x - 1 → μ ∉ closure (E.link j))
    (hF : ∃ (y : ℕ) (F : Chain S y) (hy : 0 < y), IsEpsChain F (ε / 2) ∧ C ⊆ F.union ∧
      μ ∈ F.link ⟨y - 1, by omega⟩ ∧ ∀ j : Fin y, j.val ≠ y - 1 → μ ∉ closure (F.link j)) :
    EpsCoverable M ε := by
  sorry

/-! ## Theorem 11 -/

/-- **Bing 1951, Theorem 11 (sufficiency), by Fugate 1969 Case II.** -/
theorem theorem11_1951 (hS : BingS S) : IsSnakeLike (univ : Set S) := by
  sorry

/-- **Theorem 11 as stated by Bing**: for a compact nondegenerate hereditarily decomposable
continuum, snake-like ⇔ atriodic and hereditarily unicoherent. -/
theorem theorem11_1951_iff [ConnectedSpace S] [Nontrivial S]
    (hd : IsHereditarilyDecomposable (univ : Set S)) :
    IsSnakeLike (univ : Set S) ↔
      IsAtriodic (univ : Set S) ∧ IsHereditarilyUnicoherent (univ : Set S) := by
  sorry

end HPC.Plane
