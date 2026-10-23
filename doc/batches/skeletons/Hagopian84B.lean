import HPC.Hagopian.Hagopian76AC

/-!
# Batch 186 skeleton: Hagopian 1984 III — the quotient package; Lemmas 12–16

Save as `HPC/Hagopian/Hagopian84B.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian84B` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; record each shape in the report. Unproved items are
commented out with an `OPEN` note, as before. Every theorem with a named `Prop` or structure among
its hypotheses gets a non-vacuity note.

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 339–344. Route: commission 186.
Indexing: the links `L 0, …, L 4` are the paper's `L₁, …, L₅`, and `midUnion L = L 1 ∪ L 2 ∪ L 3`
is `⋃𝔏′`. Lemmas 12–16 keep the shapes of the commented-out blocks of `Hagopian84A.lean`; delete
those blocks when the statements are proved here, leaving one-line pointers.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §2. The quotient package -/

section Package

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§2.1, a Jones decomposition** (what Theorem 1 of 1984 produces with `N = M`): upper
semicontinuous; connected classes, none equal to `M`; respected by every `δ`-homeomorphism for some
`δ > 0`; and an arc of classes (a compact `C` with a continuous surjection `c` onto `[0, 1]` whose
fibres are the traces of the classes). -/
structure IsJonesDecomp84 (r : Setoid M) : Prop where
  usc : IsUSCDecomp r
  conn : ∀ x, IsConnected (cls r x)
  proper : ∀ x, cls r x ≠ univ
  invariant : ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∀ x y, r x y → r (h x) (h y)
  arc : ∃ (C : Set M) (c : C → unitInterval), IsCompact C ∧ Continuous c ∧
    Function.Surjective c ∧ ∀ x y : C, c x = c y ↔ r x y

/-- **§2.1, the reduction**: `Hagopian84Decomp` from Jones decompositions (route: commission 186
§2.2). Non-vacuity note required. -/
theorem hagopian84Decomp_of_package
    (hP : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
      ¬ IsDecomposableSpace M → ¬ IsHereditarilyIndecomposable (univ : Set M) →
        ∃ r : Setoid M, IsJonesDecomp84 r) :
    Hagopian84Decomp := by
  sorry

/-- **§2.2, homogeneity**: finite compositions of `δ`-homeomorphisms act transitively on `M`
(the orbits are open by `hagopian84_lemma1`, and `M` is connected). This replaces the chain of
points `vᵢ` of p. 344. -/
theorem exists_comp_small_homeo (hX : IsHomogeneous M) {δ : ℝ} (hδ : 0 < δ)
    (Q : (M ≃ₜ M) → Prop) (hQ : ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → Q h)
    (hQt : ∀ f g, Q f → Q g → Q (f.trans g)) (x y : M) : ∃ h, Q h ∧ h x = y := by
  sorry

end Package

/-! ## §3. Lemmas 12 and 13: the chain -/

section Chain

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- `W(S, δ)` (p. 339): the points `h(x)` with `x ∈ S` and `h` a `δ`-homeomorphism. Open by
`hagopian84_lemma1`. -/
def WsetOf (S : Set M) (δ : ℝ) : Set M := ⋃ x ∈ S, Wset84 x δ

/-- The links of the proof of Lemma 13 (p. 339): `L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`, the paper's
`Lᵢ₊₁ = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`. -/
def chainLinks84 {E : Set M} (k : E → unitInterval) (x : Fin 16 → unitInterval) (δ : ℝ) :
    Fin 5 → Set M :=
  fun i => WsetOf (layerSet k (Icc (x ⟨3 * i.val, by have := i.isLt; omega⟩)
    (x ⟨3 * i.val + 3, by have := i.isLt; omega⟩))) δ

/-- **§3.1 step 4(a), folds** (combinatorics; the reduction "By (1), (2), and (3), there exist
numbers `r`, `s`, and `t` …" of p. 340, with its mirror case). Five open subsets of `[0, 1]`,
non-adjacent ones disjoint, covering, with `0 ∈ V 0 \ V 1` and `1 ∈ V 4 \ V 3`. If one of them is
not an interval, there is a fold. -/
theorem exists_fold {V : Fin 5 → Set unitInterval} (hV : ∀ i, IsOpen (V i))
    (hcov : ∀ u, ∃ i, u ∈ V i) (hdisj : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j))
    (h0 : (0 : unitInterval) ∈ V 0 \ V 1) (h1 : (1 : unitInterval) ∈ V 4 \ V 3)
    (hnc : ∃ i, ¬ (V i).OrdConnected) :
    ∃ r s t : unitInterval, r < s ∧ s < t ∧ ∃ p q : Fin 5, ((p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p) ∧
      s ∈ V p ∧ r ∈ V q \ V p ∧ t ∈ V q \ V p := by
  sorry

/-- **§3.1 steps 1–4** (pp. 339–340): for `x` and `δ` as printed, `chainLinks84 k x δ` is a normal
chain in `M∖A`, and for every `δ`-homeomorphism `h`, `h[E]` runs straight through it ((1)–(6), with
(5) read with `h`; the fold of step 4 excluded geometrically). *Shape left to you.* -/
theorem chainLinks84_runsStraight : True := by
  sorry

/-- **§3.1 step 5, regularity** (p. 340, "Since `M` is atriodic, it follows from (6) and Lemma 6
that `Cl K` is an essential subcontinuum of `h[E]` that runs straight through `𝔏`"): the chain is
regular, and the closure of each component of its `midUnion` is an essential subcontinuum of a
`δ`-translate of `E`. *Shape left to you.* -/
theorem chainLinks84_regular : True := by
  sorry

/-- **§3.2, Lemma 12** (p. 339). Shape of the commented-out block of `Hagopian84A.lean`. Adding to
the conclusion "every component of `midUnion P` is a component of `midUnion L`" is allowed. -/
theorem hagopian84_lemma12 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {L : Fin 5 → Set M} (hL : IsChain5 L)
    (hn : IsNormal5 L) (hr : IsRegular5 L) (hs : RunsStraight k L)
    (h0 : layer k 0 ⊆ L 0 \ closure (L 1)) (h1 : layer k 1 ⊆ L 4 \ closure (L 3)) :
    ∃ P, IsOrderedRefinement5 P L ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P := by
  sorry

/-- **§3.1, Lemma 13** (pp. 339–341). Shape of the commented-out block of `Hagopian84A.lean`. -/
theorem hagopian84_lemma13 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) {A B : Set M}
    (hA : IsClosed A) (hAE : Disjoint A E) (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ P, IsChain5 P ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P ∧
      (⋃ i, P i) ⊆ Aᶜ ∧ closure (P 0 ∪ P 4) ⊆ B ∧
      ∀ x ∈ midUnion P, ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) ∧
        ∃ g : (h '' E) → unitInterval, IsMinimalAdmissible (h '' E) g ∧
          IsEssential84 g (closure (connectedComponentIn (midUnion P) x)) := by
  sorry

end Chain

/-! ## §4. Lemmas 14 and 15; the arc -/

section Delta

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4.1** (p. 341: "Note that since `𝒫` is regular, `Δ(𝒫)` is a decomposition of
`(⋃𝒫)∖Cl(P₁ ∪ P₅)`"). -/
theorem delta5_partition (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P) :
    ⋃₀ Delta5 P = (⋃ i, P i) \ closure (P 0 ∪ P 4) ∧
      ∀ Z ∈ Delta5 P, ∀ Z' ∈ Delta5 P, (Z ∩ Z').Nonempty → Z = Z' := by
  sorry

/-- **§4.1, positivity** (unargued: the `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)` of Lemmas 14 and 15 is
positive). -/
theorem delta5_dist_pos (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ η > 0, ∀ z ∈ ⋃₀ Delta5 P, ∀ y : M, y ∉ midUnion P → η ≤ dist z y := by
  sorry

/-- **§4.2, Lemma 14** (p. 341). Shape of the commented-out block, with normality added (the
chains of Lemma 13 are normal). -/
theorem hagopian84_lemma14 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∀ Z ∈ Delta5 P, ∀ z ∈ Z, ∀ ε > 0, ∃ δ > 0, ∀ Z' ∈ Delta5 P, ∀ z' ∈ Z', dist z z' < δ →
      Z ⊆ thickening ε Z' ∧ Z' ⊆ thickening ε Z := by
  sorry

/-- **§4.3, Lemma 15** (p. 341). Shape of the commented-out block, with normality added; `ε` may
be smaller than Hagopian's (commission 186 §4.3). -/
theorem hagopian84_lemma15 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ ε > 0, ∀ Z ∈ Delta5 P, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) → h '' Z ∈ Omega5 P := by
  sorry

/-- **§4.4, the arc** (p. 344: "Since `M/𝔇` is an atriodic homogeneous continuum that contains an
arc", unargued): the closure of a component of `midUnion P` has a closed interval of layers in
`Δ(𝒫)`. -/
theorem exists_interval_in_delta (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P) {x : M}
    (hx : x ∈ midUnion P) {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    (hcs : RunsStraight c P) :
    ∃ a b : unitInterval, a < b ∧ ∀ t ∈ Icc a b, layer c t ∈ Delta5 P := by
  sorry

end Delta

/-! ## §5. Lemma 16 -/

section Lemma16

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§5, Lemma 16** (pp. 341–342). Shape of the commented-out block of `Hagopian84A.lean`. If the
printed proof resists, prove instead that no layer of `F` contains the closure of a component of
`midUnion P` (commission 186 §5), and say so. -/
theorem hagopian84_lemma16 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hf : IsFree5 P) (hr : IsRegular5 P) {x : M}
    (hx : x ∈ midUnion P) {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c) {F : Set M}
    {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hKF : closure (connectedComponentIn (midUnion P) x) ⊆ F) (hd0 : layer d 0 = layer c 0)
    (t : unitInterval) (i : ℕ) (hi3 : i + 2 < 5) :
    ¬ ((layer d t ∩ P ⟨i, by omega⟩).Nonempty ∧ (layer d t ∩ P ⟨i + 1, by omega⟩).Nonempty ∧
      (layer d t ∩ P ⟨i + 2, hi3⟩).Nonempty) := by
  sorry

end Lemma16

end HPC.Hagopian
