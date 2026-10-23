import HPC.Plane.Theorem9B

/-!
# Batch 96: Bing 1951 Theorem 11 — the easy half, and reconnaissance on the hard half

Skeleton (save as `HPC/Plane/Theorem11.lean`; add `import HPC.Plane.Theorem11` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded.

Theorem 11 (p. 660): *necessary and sufficient conditions that a compact hereditarily decomposable
continuum be snake-like are that it be atriodic and hereditarily unicoherent.*

§1 is the necessity ("it is easy to see"). §2 sets up Bing's minimal counterexample and the
structure his proof of sufficiency needs; §3 is sufficiency, conditional on `theorem10_1951`.
-/

namespace HPC.Plane

open Set Topology

variable {X : Type*} [MetricSpace X]

/-! ## §1. Necessity: snake-like ⇒ atriodic and hereditarily unicoherent (Nadler 12.2–12.5) -/

/-- A subcontinuum of a snake-like continuum is snake-like (Nadler 12.5; Bing uses it without
comment). -/
theorem isSnakeLike_of_subcontinuum {M K : Set X} (hM : IsSnakeLike M) (hK : Fold.Q78.IsContinuum K)
    (hKM : K ⊆ M) : IsSnakeLike K := by
  sorry

/-- A snake-like continuum is unicoherent (Nadler 12.2). -/
theorem isUnicoherent_of_isSnakeLike {M : Set X} (hM : IsSnakeLike M) : IsUnicoherent M := by
  sorry

/-- A snake-like continuum is hereditarily unicoherent. -/
theorem isHereditarilyUnicoherent_of_isSnakeLike {M : Set X} (hM : IsSnakeLike M) :
    IsHereditarilyUnicoherent M := by
  sorry

/-- A snake-like continuum is atriodic (Nadler 12.4: a triod is not chainable). -/
theorem isAtriodic_of_isSnakeLike {M : Set X} (hM : IsSnakeLike M) : IsAtriodic M := by
  sorry

/-! ## §2. The hard half: structure -/

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- `M` is covered by some `ε`-chain. -/
def EpsCoverable (M : Set X) (ε : ℝ) : Prop :=
  ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

/-- **Bing's minimal counterexample.** If a continuum is not `ε`-coverable, it contains a
subcontinuum which is not `ε`-coverable but all of whose proper subcontinua are (Zorn; batch 90's
`isClosed_notCoverable` is the closedness). -/
theorem exists_minimal_notCoverable {M : Set X} (hM : Fold.Q78.IsContinuum M) {ε : ℝ}
    (hε : 0 < ε) (hnot : ¬ EpsCoverable M ε) :
    ∃ S' ⊆ M, Fold.Q78.IsContinuum S' ∧ ¬ EpsCoverable S' ε ∧
      ∀ K ⊆ S', Fold.Q78.IsContinuum K → K ≠ S' → EpsCoverable K ε := by
  sorry

/-- **The two sides of an element** (property 2 gives at most two components of `S ∖ g`; (a)
gives at least two for an interior element). For an element `g = bingElt r` that is not an end
element, `S ∖ g` has exactly two components, and every other element lies in one of them. Stated as
the existence of the two open sides. -/
theorem exists_two_sides (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) :
    ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (bingElt r)ᶜ ∧
      IsConnected U ∧ IsConnected V := by
  sorry

/-- **Bing's `H` and `K`**: `g'` together with all elements on one side. With `U`, `V` the two
sides of `g' = bingElt r`: `H = U ∪ g'`, `K = V ∪ g'` are continua, `H ∪ K = S`, `H ∩ K = g'`,
and both are proper. -/
theorem sides_continua (hS : BingS S) {r : S} (hr : ¬ IsEndElt r) {U V : Set S}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcov : U ∪ V = (bingElt r)ᶜ)
    (hUc : IsConnected U) (hVc : IsConnected V) :
    Fold.Q78.IsContinuum (U ∪ bingElt r) ∧ Fold.Q78.IsContinuum (V ∪ bingElt r) ∧
      U ∪ bingElt r ≠ univ ∧ V ∪ bingElt r ≠ univ := by
  sorry

/-- **Q-deg. A degenerate interior element exists.** (Bing's "uncountable collection `G'`"
sentence; expected route: Kuratowski — the union of the nondegenerate elements is of first
category in `S`, so by Baire some element is a point, and by Theorem 8 (b)/(a) it can be taken
distinct from the two end elements. Prove, or state the obstruction.) -/
theorem exists_degenerate_interior_elt (hS : BingS S) :
    ∃ p : S, bingElt p = {p} ∧ ¬ IsEndElt p := by
  sorry

/-- **Q-A. Condition A on the sides.** If `g' = {p'}` is a degenerate interior element with sides
`U`, `V`, then `p'` satisfies condition A for `H = U ∪ {p'}` (and symmetrically for `K`). Bing:
"`p'` satisfies condition A for `M` equal to either `H` or `K`" — unargued; here for the
degenerate case. -/
theorem condA_side (hS : BingS S) {p : S} (hp : bingElt p = {p}) (hpe : ¬ IsEndElt p)
    {U V : Set S} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcov : U ∪ V = (bingElt p)ᶜ) (hUc : IsConnected U) (hVc : IsConnected V) :
    CondA (U ∪ {p}) p := by
  sorry

/-- **Q-sep. The separation sentence, degenerate case.** With `g' = {p'}` and `N` an open
neighbourhood of `p'`, `S ∖ N` is the union of the two disjoint closed sets `H ∖ N` and `K ∖ N`.
(Immediate; recorded because the nondegenerate case fails, see `not_separation_of_accumulates`.) -/
theorem separation_of_degenerate {p : S} {U V : Set S} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcov : U ∪ V = {p}ᶜ) {N : Set S} (hN : IsOpen N) (hpN : p ∈ N) :
    IsClosed ((U ∪ {p}) \ N) ∧ IsClosed ((V ∪ {p}) \ N) ∧
      Disjoint ((U ∪ {p}) \ N) ((V ∪ {p}) \ N) ∧
      ((U ∪ {p}) \ N) ∪ ((V ∪ {p}) \ N) = Nᶜ := by
  sorry

/-- **The nondegenerate branch of Bing's proof cannot work as written.** If `g'` is nondegenerate
and `K ∖ g'` accumulates at every point of `g'` (as it does when `g'` is a two-sided limit of
elements), then for an open `N ∌ some point of g'` there is no pair of separated sets `H'`, `K'`
with `H' ∪ K' = S ∖ N`, `H ∖ N ⊆ H'`, `K ∖ (g' ∪ N) ⊆ K'`. Pure point-set statement, no `BingS`. -/
theorem not_separation_of_accumulates {g H K N : Set S} (hHK : H ∩ K = g)
    (hacc : ∀ x ∈ g, x ∈ closure (K \ g)) (hN : IsOpen N) (hgN : ¬ g ⊆ N) :
    ¬ ∃ H' K' : Set S, H' ∪ K' = Nᶜ ∧ Disjoint (closure H') K' ∧ Disjoint H' (closure K') ∧
      H \ N ⊆ H' ∧ K \ (g ∪ N) ⊆ K' := by
  sorry

/-! ## §3. Sufficiency, conditional on Theorem 10 -/

/-- **Amalgamation of two chains at a common end point** (Bing's displayed chain
`H'·h₁, …, H'·h_{m−1}, (H'·h_m) ∪ N ∪ (K'·k₁), K'·k₂, …, K'·k_n`). If `H ∩ K = {p}`,
`H ∪ K = S`, `h` is an `ε`-chain covering `H` with `p ∈ h_m ∖ cl h_{m−1}` and in no other link's
closure, `k` an `ε`-chain covering `K` with `p ∈ k₁ ∖ cl k₂` and in no other link's closure, then
`S` is covered by an `ε`-chain. (Links of the displayed chain must be open; `H ∖ N` and `K ∖ N`
are the separated pieces; the middle link has diameter `< ε` once `N` is small.) -/
theorem epsCoverable_amalgam {H K : Set S} (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) {p : S} (hHK : H ∩ K = {p}) (hcov : H ∪ K = univ) {ε : ℝ}
    (hε : 0 < ε)
    (hh : ∃ (m : ℕ) (h : Chain S m) (hm : 0 < m), IsEpsChain h ε ∧ H ⊆ h.union ∧
      p ∈ h.link ⟨m - 1, by omega⟩ ∧ ∀ j : Fin m, j.val ≠ m - 1 → p ∉ closure (h.link j))
    (hk : ∃ (n : ℕ) (k : Chain S n) (hn : 0 < n), IsEpsChain k ε ∧ K ⊆ k.union ∧
      p ∈ k.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (k.link j)) :
    EpsCoverable (univ : Set S) ε := by
  sorry

/-- **Theorem 11, sufficiency, from Theorem 10 as a hypothesis.** A compact hereditarily
decomposable, atriodic, hereditarily unicoherent continuum is snake-like. The hypothesis `hT10` is
the statement of `theorem10_1951` (`EndPoints51.lean`), which is still open; when it closes, this
becomes unconditional. -/
theorem theorem11_1951_of_T10
    (hT10 : ∀ {M : Set S}, Fold.Q78.IsContinuum M → ∀ {m : ℕ} (D : Chain S m), M ⊆ D.union →
      ∀ {p : S}, CondA M p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
        p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j))
    (hS : BingS S) : IsSnakeLike (univ : Set S) := by
  sorry

/-- **Theorem 11 as an equivalence**, for a compact nondegenerate hereditarily decomposable
continuum, conditional as above. -/
theorem theorem11_1951_iff_of_T10
    (hT10 : ∀ {M : Set S}, Fold.Q78.IsContinuum M → ∀ {m : ℕ} (D : Chain S m), M ⊆ D.union →
      ∀ {p : S}, CondA M p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
        p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j))
    [ConnectedSpace S] [Nontrivial S] (hd : IsHereditarilyDecomposable (univ : Set S)) :
    IsSnakeLike (univ : Set S) ↔
      IsAtriodic (univ : Set S) ∧ IsHereditarilyUnicoherent (univ : Set S) := by
  sorry

end HPC.Plane
