import HPC.Hagopian.H76Lemma2
import HPC.Hagopian.H76Lemma4
import HPC.Hagopian.H76Lemma4Ext
import HPC.Hagopian.H76NoMax
import HPC.Hagopian.H76Lemma4Layers
import HPC.Hagopian.H76Lemma8
import HPC.Hagopian.H76Cons

/-!
# Batch 156 skeleton: Hagopian 1976, §2 (Lemmas 2–8) and the consequences of Theorem 1

Batch 156 (`doc/batches/COMMISSION-batch156.md`). Supporting proofs are in `H76*.lean`. Items
that remain open are commented out (no `sorry`), each with an `OPEN (batch 156)` note; their
obstructions are in `OPEN.md`. Shape changes are recorded at the statement and in
`doc/batches/REPORT-batch156.md`.

Source: C. L. Hagopian, *Indecomposable homogeneous plane continua are hereditarily
indecomposable*, Trans. AMS 224 (1976), 339–350 (`doc/sources/hagopian1976.pdf`), read from page
images at 200 dpi. Here `[5]` is Hagopian 1975 (`HPC/Hagopian/Hagopian75.lean`) and `[14]` is
Thomas 1966 (not in hand).

§2 (p. 340): "In this section `M` is an indecomposable homogeneous continuum in `R²` and `E` is a
type A′ subcontinuum of `M`. Let `k : E → [0, 1]` be the quotient map associated with the minimal
admissible decomposition of `E` [5, Lemma 3]. Hereafter, we shall refer to this decomposition as
simply *the decomposition* of `E`." In the skeleton, "the decomposition" is an admissible map whose
layers have void interior (`IsMinimalAdmissible`); by `hagopian75_lemma3_unique` its layers are
determined by `E`.

Lemma 9 and Theorem 1 (the quotient `R²/S`, decomposable accessibility, Properties 1–4) are for
batch 157.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! The definitions (p. 340) and `Hagopian76Thm1` are in `H76Defs.lean`, verbatim. -/

/-! ## §2. Lemmas 2–8 -/

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- **Lemma 2** (p. 340). "Suppose `ε` is a given positive number and `x` is a point of `M`. Then
`{y ∈ M: an ε-homeomorphism of M onto M takes x to y}` is an open subset of `M` that contains `x`
[5, Lemma 4 (proof)]." -/
theorem hagopian76_lemma2 (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    IsOpen {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} ∧
      x ∈ {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} := by
  exact lemma2_aux hX hε x

omit [CompactSpace M] [ConnectedSpace M] in
/-- **End sets** (p. 340): "No proper subcontinuum of `E` intersects both `X` and `Z` [14, Theorem
8, p. 14]." (`admissible_end_sets'`, batch 155, in this setting.) -/
theorem hagopian76_end_sets {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {K : Set M} (hKE : K ⊆ E) (hK : Fold.Q78.IsContinuum K) (h0 : (K ∩ layer k 0).Nonempty)
    (h1 : (K ∩ layer k 1).Nonempty) : K = E := by
  exact end_sets_aux hE hKE hK h0 h1

/-- **Lemma 3** (p. 340). "Let `Y` be an element of the decomposition of `E` distinct from the end
sets `X` and `Z` of `E`. Let `F` be a type A′ subcontinuum of `M` with end sets `T` and `V`, and let
`U` be an element of the decomposition of `F` distinct from `T` and `V`. Suppose `h` is a
homeomorphism of `M` onto `M` such that `U ∩ h[Y] ≠ ∅` and `U ∩ h[X ∪ Z] = ∅ = h[Y] ∩ (T ∪ V)`.
Then `h[Y] = U`." Proof: "This lemma follows from the argument presented in paragraphs 9 through 11
in the proof of Theorem 1 of [5]." The printed hypotheses carry no `ε`, unlike
`hagopian75_layer_invariant`; record what replaces it.

*What replaces `ε`:* the hypothesis `h[Y] ∩ (T ∪ V) = ∅`. With it the 1975 ¶9 triod puts `h[Y]` inside
`F`; then `J = F ∩ h[E]` is a continuum, and with `[γ, δ] = k(h⁻¹[J])`: if `γ = s` (or `δ = s`), the
continuum `h k⁻¹[[0, s]]` (or `h k⁻¹[[s, 1]]`) meets `F` only in `h[Y]`, so by the same triod it lies in
`F`, which puts `h[X]` (or `h[Z]`) in `h[Y]`; if `γ < s < δ` and `h[Y] ≠ U`, `h[Y]` contains an open
subset of `F`, and the 1975 ¶10 argument (a neighbourhood meeting `h[E]` only in `h[Y]`) gives `Y`
nonvoid interior in `E`. So `h[Y] ⊆ U`; the same for `h⁻¹`, `U`, `Y` (using `U ∩ h[X ∪ Z] = ∅`) gives
`U ⊆ h[Y]`. The 1975 argument goes through; Lemma 3 holds as printed. See `H76Lemma3.lean`.

*Shape change:* `hu0 : 0 < u` and `hu1 : u < 1` are dropped (not used: `U` meets `h[Y]`, which misses
`T ∪ V`, so `U` is neither end set). -/
theorem hagopian76_lemma3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) {s u : unitInterval} (hs0 : 0 < s) (hs1 : s < 1)
    (h : M ≃ₜ M) (h1 : (layer d u ∩ h '' layer k s).Nonempty)
    (h2 : Disjoint (layer d u) (h '' (layer k 0 ∪ layer k 1)))
    (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1)) :
    h '' layer k s = layer d u :=
  lemma3_aux (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hF hs0 hs1 h h1 h2 h3

-- `hagopian76_lemma4_layers` (D1): re-rendered as printed in `Hagopian76B.lean` (open, batch 157; see `OPEN.md`).

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Lemma 4, first paragraph, corrected** (the part implied by minimality). `s` is the largest value
of `d` on `E`; `d⁻¹[0, s) ⊆ E ⊆ d⁻¹[[0, s]]` (Hagopian: "`d[E] = [0, s]`" and "for each positive number
`r` less than `s`, the set `d⁻¹(r)` is in `E`"); every element of the decomposition of `E` lies in an
element of the decomposition of `F`; and an element of the decomposition of `E` lying in `d⁻¹(u)` with
`u < s` is `d⁻¹(u)`.

*Shape change* from `hagopian76_lemma4_layers` (commented out above): `layerSet d (Icc 0 s) = E` is
weakened to the two inclusions, and "`∀ t ≠ 1, ∃ u, k⁻¹(t) = d⁻¹(u)`" to the last two clauses. The
hypotheses `hX`, `hi` are not used (only minimality is). -/
theorem hagopian76_lemma4_layers' {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Ico 0 s) ⊆ E ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (∀ t, ∃ u, layer k t ⊆ layer d u) ∧
      ∀ t u, u < s → layer k t ⊆ layer d u → layer k t = layer d u :=
  lemma4_layers_aux hE hF hEF hX0

/-- **Lemma 4, linear order** (the first half of `hagopian76_lemma4`). The proof is Hagopian's triod
(`ext_chain`, `H76Lemma4.lean`); the first paragraph is not needed. -/
theorem hagopian76_lemma4_chain (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} :=
  fun _ hF _ hH _ => ext_chain (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hF hH

/-- **Lemma 4, the countable form, from "no maximal element".** Given the second half of
`hagopian76_lemma4` as the hypothesis `hnomax`, the sequence of `hagopian76_lemma4_seq` exists: a
nonempty chain of closed sets with no largest element in a second-countable space has a strictly
increasing cofinal sequence (`exists_strictMono_seq_of_chain`). -/
theorem hagopian76_lemma4_seq_of_noMax (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hnomax : ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
      ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  exists_strictMono_seq_of_chain (hagopian76_lemma4_chain hX hi hE)
    (fun _ ⟨_, _, ⟨⟨_, _, hab⟩, _, _⟩, _⟩ => hab.1.1.isClosed) ⟨E, subset_rfl, k, hE, rfl⟩ hnomax

/-- **Lemma 4, "no maximal element", given the branching continuum.** Hagopian's step "it is a
proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]`" splits into (1) a continuum
`C` (his piece of `h⁻¹[F]`) with `∅ ≠ C ∩ F ⊆ d⁻¹(1)` and `C ⊄ F`, and (2) a proper extension of `F`
inside `F ∪ C`. Step (2) is proved (`ext_of_branch`, `H76Lemma4Ext.lean`: an irreducible continuum
from `X` to a point of `C ∖ F` contains `F`, is of type A′ by Kuratowski's criterion and the 1975 ¶2
argument, and its end layer at `X` is `X`). Step (1) is the hypothesis `hbranch`; it is the open part
of D2 (`OPEN.md`). With it, Lemma 4 holds as printed. -/
theorem hagopian76_lemma4_of_branch (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hbranch : ∀ (F : Set M) (d : F → unitInterval), E ⊆ F → IsMinimalAdmissible F d →
      layer d 0 = layer k 0 → ∃ C : Set M, Fold.Q78.IsContinuum C ∧ (C ∩ F).Nonempty ∧
        C ∩ F ⊆ layer d 1 ∧ ¬ C ⊆ F) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H :=
  lemma4_of_branch hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hbranch

/-- **Lemma 4, the countable form, given the branching continuum** (from
`hagopian76_lemma4_of_branch` and `exists_strictMono_seq_of_chain`). -/
theorem hagopian76_lemma4_seq_of_branch (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hbranch : ∀ (F : Set M) (d : F → unitInterval), E ⊆ F → IsMinimalAdmissible F d →
      layer d 0 = layer k 0 → ∃ C : Set M, Fold.Q78.IsContinuum C ∧ (C ∩ F).Nonempty ∧
        C ∩ F ⊆ layer d 1 ∧ ¬ C ⊆ F) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  lemma4_seq_of_branch hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hbranch

/-- **Lemma 4** (p. 340). "The collection `𝓕` of extensions of `E` away from the end set `X` is
linearly ordered by inclusion and does not have a maximal element." Proof (p. 341): "If `H` is an
element of `𝓕`, then `F ⊂ H` or `H ⊂ F`; for otherwise, the continuum `H ∩ d⁻¹[[s, 1]]` (Lemma 1)
would separate `F ∪ H` into three nonempty disjoint open sets"; and, for no maximal element, "it is
a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)".

The linear order is `ext_chain` (`H76Lemma4.lean`). "No maximal element" is
`exists_proper_extension` (`H76NoMax.lean`); the step Hagopian leaves unargued (how a proper
extension inside `F ∪ h⁻¹[F]` is obtained) is supplied there by a case analysis on how `h⁻¹[F]`
meets `F` (see `OPEN.md`, batch 156, item D2, now closed). -/
theorem hagopian76_lemma4 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H :=
  lemma4_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE

/-- **Lemma 4, the countable form used in Lemma 6** (p. 342). "Since `M` is second countable, there
exists a monotone strictly increasing sequence `{Fᵢ}` of elements of `𝓕` such that
`R(X, E) = ⋃ Fᵢ` (Lemma 4)." -/
theorem hagopian76_lemma4_seq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  lemma4_seq_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE

-- `hagopian76_lemma5`: proved in batch 158, `Hagopian76C.lean`.

/- OPEN (batch 156): `hagopian76_closure_extUnion` — depends on Lemmas 4 and 5. See `OPEN.md`, batch 156, item F.

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343): "We complete this proof by showing that
`Cl R(X, E) = Cl R(E)` … (see the second paragraph in the proof of Theorem 1 of [5])." -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_lemma6` — depends on Lemmas 4 and 5. See `OPEN.md`, batch 156, item F.

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_Rset_composant` — depends on Lemma 6. See `OPEN.md`, batch 156, item F.

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343, unnumbered). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_essential_typeA'` — depends on Lemma 5. See `OPEN.md`, batch 156, item F.

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343,
unnumbered). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_lemma7` — depends on Lemmas 5 and 6. See `OPEN.md`, batch 156, item G.

/-- **Lemma 7** (p. 343). "For each positive number `ε`, there exists a positive number `δ` such
that if `h` is a `δ`-homeomorphism of `M` onto `M`, then `h[R(E)]` has the following property. If
`H` is a continuum essential to `h[R(E)]` with end sets `T` and `V` such that `ρ(T, V) < δ` and if
there exists an element `U` of the decomposition of `H` such that `ρ(T, U) > ε`, then each point of
`R(E)` is within `ε` of `H`." Shape: "essential to `h[R(E)]`" is read as `h⁻¹[H]` essential to
`R(E)`; `ρ` between sets is the infimum distance (attained, the sets being compact). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry
-/

/-- **Lemma 8** (p. 344). "Every chain in `R²` that follows `E` has an ordered refinement that
follows `E` and is free relative to `M`." Proof: "Since `M` is atriodic, there exist open sets `A`
and `B` in `G₁` and `Gₙ`, respectively, such that `E` is a component of `M − (A ∪ B)`." Then Moore
1962 Theorem 44, p. 15, gives disjoint open `C ⊃ E` and `D ⊃ M − St G` with
`C ∪ D ⊃ M − (A ∪ B)`, and `L₁ = G₁`, `Lₙ = Gₙ`, `Lᵢ = C ∩ Gᵢ`. -/
theorem hagopian76_lemma8 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {n : ℕ} (G : Fin (n + 1) → Set Pt)
    (hG : IsPlaneChain G) (hGE : Follows G k) :
    ∃ L : Fin (n + 1) → Set Pt, IsOrderedRefinement L G ∧ Follows L k ∧ IsFree M L := by
  exact lemma8_aux (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE G hG hGE

end Section2

/-! ## Theorem 1 as a statement, and its consequences -/

section Consequences

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Hagopian 1976, Theorem 2** (p. 349). "Every homogeneous plane continuum that does not separate
the plane is hereditarily indecomposable." Proof: "Since every homogeneous nonseparating plane
continuum is indecomposable [4], [6], this theorem follows immediately from Theorem 1." Here [4] is
Gordh 1975 and [6] Jones 1951; the repository route is `jones55_two_domains'` (a decomposable
homogeneous plane continuum has two complementary domains). -/
theorem hagopian76_theorem2 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hns : ¬ SeparatesPlane M) : IsHereditarilyIndecomposable (univ : Set M) := by
  exact hagopian76_theorem2_aux h1 hX hns

/-- **Hagopian 1975, Corollary** (p. 39). "If `M` is a homogeneous indecomposable plane continuum,
then no subcontinuum of `M` is hereditarily decomposable." (Nondegenerate subcontinua: Hagopian's
continua are nondegenerate.) -/
theorem hagopian75_corollary (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {H : Set M} (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) :
    ¬ IsHereditarilyDecomposable H := by
  exact hagopian75_corollary_aux h1 hX hi hH hnd

/-- **Hagopian 1975, Theorem 1** (p. 38), as printed: "Suppose `M` is a homogeneous indecomposable
plane continuum and `A` is a decomposable subcontinuum of `M`. Then `A` contains a homogeneous
indecomposable continuum." From Theorem 1 of 1976 the hypothesis is impossible. -/
theorem hagopian75_theorem1 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {A : Set M} (hA : Fold.Q78.IsContinuum A)
    (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ Y ⊆ A, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y := by
  exact absurd (h1 M hX hi A (subset_univ _) hA) hAd

/-- **Hagopian 1975, Theorem 2** (p. 39). "The simple closed curve is the only homogeneous plane
continuum that has a hereditarily decomposable subcontinuum." Proof (p. 40): the Corollary, Jones's
decomposition [Jones 1955, Theorem 2], and "if `H` meets more than one element of `G`, then `H`
contains an element of `G` [Jones 1955, Theorem 1]" (`jones55_c`). -/
theorem hagopian75_theorem2 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {H : Set M}
    (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) (hHd : IsHereditarilyDecomposable H) :
    Nonempty (M ≃ₜ Circle) := by
  exact hagopian75_theorem2_aux h1 hX hH hnd hHd

/-- **Bing 1960 for plane continua** (Canad. J. Math. 12, title theorem): "A simple closed curve is
the only homogeneous bounded plane continuum that contains an arc." An arc is hereditarily
decomposable, so this is `hagopian75_theorem2`. -/
theorem bing60_plane (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {α : Set M}
    (hα : Nonempty (α ≃ₜ unitInterval)) : Nonempty (M ≃ₜ Circle) := by
  exact bing60_plane_aux h1 hX hα

end Consequences

end HPC.Hagopian
