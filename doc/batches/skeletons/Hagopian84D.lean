import HPC.Hagopian.Hagopian84C

/-!
# Batch 188 skeleton: Hagopian 1984 V — the decomposition `𝔇`; claims (5)–(6); `hagopian84_decomp`

Save as `HPC/Hagopian/Hagopian84D.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian84D` at the end of `HPC.lean`. Every `sorry` is a work item. Unproved
items are commented out with an `OPEN` note, as before. Every theorem with a named `Prop` or
structure among its hypotheses gets a non-vacuity note.

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 343–344. Route: commission 188.
Indexing as in `Hagopian84B.lean`: links `P 0, …, P 4` (the paper's `P₁, …, P₅`), `P 2` is the
paper's `P₃`, `midUnion P = ⋃𝒫′`. A *strand* is the closure of a component of `midUnion P`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §2. The transfer lemma -/

section Transfer

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§2, the transfer lemma** (replaces "by (2), (3), and Lemma 7" and "by (3) and Lemma 7",
p. 344). `𝒫` a normal regular chain; `Q` a free normal regular chain whose union misses `Cl P 2`
(Hagopian's (2)). A member `Z` of `Ω(𝒫)` through a point `z` of `midUnion Q` is the layer through
`z` of the strand of `Q` through `z`. Route: commission 188 §2 (Lemma 16′ for `Q`, applied to the
piece of the strand of `Z` between `Z` and a layer inside `P 2`). -/
theorem omega_layer_of_mem_mid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    (h2 : (⋃ i, Q i) ⊆ (closure (P 2))ᶜ) {Z : Set M} (hZ : Z ∈ Omega5 P) {z : M} (hzZ : z ∈ Z)
    (hz : z ∈ midUnion Q) :
    ∃ c' : closure (connectedComponentIn (midUnion Q) z) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion Q) z)) c' ∧
        ∃ t, Z = layer c' t := by
  sorry

/-- **§2, second part**: if moreover `z ∉ Cl(Q 0 ∪ Q 4)`, then `Z ∈ Δ(Q)`
(`strand_layer_mem_delta` for `Q`). -/
theorem omega_mem_delta_of_mem_mid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    (h2 : (⋃ i, Q i) ⊆ (closure (P 2))ᶜ) {Z : Set M} (hZ : Z ∈ Omega5 P) {z : M} (hzZ : z ∈ Z)
    (hz : z ∈ midUnion Q) (hz0 : z ∉ closure (Q 0 ∪ Q 4)) : Z ∈ Delta5 Q := by
  sorry

end Transfer

/-! ## §3. The data, `𝔇`, disjointness -/

/-- **§3.1, the data of p. 343 after the finite subcover** (`hagopian84_cover`): the chain `𝒫`
(Lemma 13), finitely many `Zᵢ ∈ Ω(𝒫)∖Δ(𝒫)` (`S`) with their chains `𝒫(Zᵢ)` (`Q`), and the cover.
A structure standing for constructed data: non-vacuity note required (discharged by
`exists_coverData84`). -/
structure CoverData84 (M : Set Pt) [CompactSpace M] [ConnectedSpace M] where
  P : Fin 5 → Set M
  hP : IsChain5 P
  hPf : IsFree5 P
  hPn : IsNormal5 P
  hPr : IsRegular5 P
  S : Finset (Set M)
  Q : Set M → Fin 5 → Set M
  hQ : ∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P ∧ IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧
    IsNormal5 (Q Z) ∧ IsRegular5 (Q Z) ∧ Z ∈ Delta5 (Q Z) ∧ (⋃ i, Q Z i) ⊆ (closure (P 2))ᶜ ∧
    closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P
  cover : ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z)

section Decomp

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3.1**: the data exist (a type λ continuum by `hagopian75_exists_typeA'`; Lemma 13 with
`ε = 1`, `A = ∅`, `B = M`; `hagopian84_cover`). -/
theorem exists_coverData84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (hH : ¬ IsHereditarilyIndecomposable (univ : Set M)) : Nonempty (CoverData84 M) := by
  sorry

/-- **§3.2, `𝔇`** (p. 343: "For convenience we define `𝒫(Z₀)` to be `𝒫`"; "Let `𝔇` be
`⋃{Δ(𝒫(Zᵢ)): 0 ≤ i ≤ n}`"). -/
def CoverData84.members (D : CoverData84 M) : Set (Set M) :=
  Delta5 D.P ∪ ⋃ Z ∈ D.S, Delta5 (D.Q Z)

/-- **§3.3**: every point lies in a member. -/
theorem CoverData84.exists_mem (D : CoverData84 M) (y : M) : ∃ A ∈ D.members, y ∈ A := by
  sorry

/-- **§3.4, disjointness** (pp. 343–344: "We must show that `𝔇` is a decomposition of `M`. Since
`𝒞` covers `M`, it suffices to show that the elements of `𝔇` are disjoint."). Route: commission
188 §3.4 (cases (a)–(c); §2 in place of Lemma 7; Lemma 3 as printed in the last case). -/
theorem CoverData84.members_disjoint (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {A B : Set M} (hA : A ∈ D.members) (hB : B ∈ D.members)
    (hAB : (A ∩ B).Nonempty) : A = B := by
  sorry

/-- **§3.5, the relation**: `x ~ y` iff some member of `𝔇` contains both. -/
def CoverData84.rel (D : CoverData84 M) (x y : M) : Prop :=
  ∃ A ∈ D.members, x ∈ A ∧ y ∈ A

/-- **§3.5**: the relation is an equivalence (3.3 and 3.4). -/
def CoverData84.setoid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : Setoid M where
  r := D.rel
  iseqv := by
    sorry

/-- **§3.5**: the class of `x` is the member through `x`. -/
theorem CoverData84.cls_eq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {x : M} {A : Set M} (hA : A ∈ D.members) (hx : x ∈ A) :
    cls (D.setoid hX hi) x = A := by
  sorry

/-! ## §4. Claims (5) and (6) -/

/-- **§4.1, claim (5) for `i = 0`** (p. 344: "(5) for each integer `i` (`0 ≤ i ≤ n`),
`Ω(𝒫(Zᵢ)) ⊂ 𝔇`"), in full. -/
theorem CoverData84.omega_subset_members (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : Omega5 D.P ⊆ D.members := by
  sorry

/-- **§4.2, claim (5) for `i ≥ 1`**, for members inside `⋃𝒫(Zᵢ)′`. -/
theorem CoverData84.omega_mem_members (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) {Z : Set M} (hZS : Z ∈ D.S) {W : Set M} (hW : W ∈ Omega5 (D.Q Z))
    (hWm : W ⊆ midUnion (D.Q Z)) : W ∈ D.members := by
  sorry

/-- **§4.3, claim (6)** (p. 344: "(6) if `Z ∈ 𝔇` and `h` is a δ-homeomorphism of `M` onto `M`, then
`h[Z] ∈ 𝔇`"). `δ` also below the `η` of `delta5_dist_pos` for each chain (commission 188 §4.3). -/
theorem CoverData84.invariant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∀ A ∈ D.members, h '' A ∈ D.members := by
  sorry

/-! ## §5. The package -/

/-- **§5.1–§5.5**: `𝔇` is a Jones decomposition (usc from Lemma 14; connected, proper classes;
invariance from (6); the arc from `exists_interval_in_delta`). -/
theorem CoverData84.isJonesDecomp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    (D : CoverData84 M) : IsJonesDecomp84 (D.setoid hX hi) := by
  sorry

open Classical in
/-- **§5.8, the printed closedness of `⋃𝔅`** (p. 343: "it follows that `⋃𝔅` is a closed open subset
of `M`. Hence `𝔅` covers `M`"): for any choice as in `exists_finite_cover84`, `⋃𝔅 = M`. -/
theorem sUnion_cover84_eq_univ {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) (hr : IsRegular5 P) (Q : Set M → Fin 5 → Set M)
    (hQ : ∀ Z ∈ Omega5 P, Z ∉ Delta5 P → IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsRegular5 (Q Z) ∧
      Z ∈ Delta5 (Q Z) ∧ closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P) :
    ⋃₀ Delta5 P ∪ (⋃ Z ∈ Omega5 P \ Delta5 P, ⋃₀ Delta5 (Q Z)) = univ := by
  sorry

end Decomp

/-- **§5.6, Theorem 1 of 1984 with `N = M`, in the form used** (`Hagopian84Decomp`). -/
theorem hagopian84_decomp : Hagopian84Decomp := by
  refine hagopian84Decomp_of_package ?_
  intro M _ _ hX hi hH
  exact ⟨_, (Classical.choice (exists_coverData84 hX hi hH)).isJonesDecomp hX hi⟩

/-- **§5.7, Theorem 1 of 1976 on the 1984 route**, from the arc step alone. -/
theorem hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) : Hagopian76Thm1 :=
  hagopian76_theorem1_of_jones hagopian84_decomp hA

end HPC.Hagopian
