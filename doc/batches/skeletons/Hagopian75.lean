import HPC.Jones.Jones49F
import HPC.Effros.Effros
import HPC.Plane.Atriodic51Defs
import HPC.Plane.EndPoints51
import HPC.PseudoArc.Theorem14
import HPC.Moore.M25Plane

/-!
# Batch 155 skeleton: Hagopian 1975, *Homogeneous plane continua*, §§2–5 (Lemmas 1–4; the
type A′ subcontinuum; the invariance and homogeneity of interior layers)

Save as `HPC/Hagopian/Hagopian75.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian75` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may
be adjusted, each change recorded at the statement and in the report.

Source: C. L. Hagopian, *Homogeneous plane continua*, Houston J. Math. 1 (1975), 35–41
(`doc/sources/hagopian1975.pdf`), read from page images at 200 dpi. Hagopian's *continuum* is
nondegenerate (p. 35).

Other sources:
* Moore, *Foundations of point set theory*, rev. ed. 1962 (`doc/sources/moore1962-excerpts.pdf`:
  pp. 15, 49–50, 58–59, 156, 172–175, 214–223), Theorems 135–139 (composants), Theorem 22 p. 175
  (Janiszewski), Theorem 84 p. 222 (triods).
* Kuratowski, *Topology* Vol. 2 (1968), §48, pp. 190–220 (`doc/sources/kuratowski2-s48.pdf`):
  irreducible continua, layers, Theorems VII.1–6. This replaces Thomas 1966 (Rozprawy Mat. 50),
  which is not in hand.

**Use downstream.** Hagopian 1976 (Trans. AMS 224) cites this paper's Lemma 1, Lemma 3, the proof of
Lemma 4, paragraphs 1–3 of the proof of Theorem 1 (a type A′ subcontinuum exists) and paragraphs
9–11 (the invariance of an interior layer). Paragraph 4 of that proof (a nondegenerate layer exists)
cites Bing 1960 (Canad. J. Math. 12), which 1976 does not use; it is isolated here as a hypothesis.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## §2–3. Definitions -/

section Defs

variable {X : Type*} [MetricSpace X]

/-- A *triod* in an arbitrary metric space: the definition of `HPC.Plane.IsTriod` (Bing 1951 §1)
without the ambient compactness. Hagopian (p. 35): "a continuum `T` … contains a subcontinuum `Z`
such that `T − Z` is the union of three nonempty disjoint open sets". -/
def IsTriodSet (T : Set X) : Prop :=
  Fold.Q78.IsContinuum T ∧ ∃ Z : Set X, Fold.Q78.IsContinuum Z ∧ Z ⊆ T ∧
    ∃ A B C : Set X, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ T \ Z = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C)

/-- The quotient map of an *admissible decomposition* (p. 36), in map form: a continuous map of `E`
onto `[0, 1]` with connected fibres. (Hagopian: "an upper semi-continuous decomposition whose
elements are connected sets and whose quotient space is the unit interval".) -/
def IsAdmissibleMap (E : Set X) (k : E → unitInterval) : Prop :=
  Continuous k ∧ Function.Surjective k ∧ ∀ t, IsConnected (k ⁻¹' {t})

/-- **Type A** (Thomas, via Hagopian p. 36): irreducible between two of its points, with an
admissible decomposition. -/
def IsTypeA (E : Set X) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧ ∃ k : E → unitInterval, IsAdmissibleMap E k

/-- **Type A′** (p. 36): type A, with an admissible decomposition each of whose elements has void
interior relative to `E`. -/
def IsTypeA' (E : Set X) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧
    ∃ k : E → unitInterval, IsAdmissibleMap E k ∧ ∀ t, interior (k ⁻¹' {t}) = ∅

/-- The layer `k⁻¹(s)`, as a subset of the ambient space. -/
def layer {E : Set X} (k : E → unitInterval) (s : unitInterval) : Set X :=
  Subtype.val '' (k ⁻¹' {s})

/-- **The map form is the decomposition form.** For an admissible map, the fibre relation's
quotient space is homeomorphic to `[0, 1]` (closed map of a compact space onto a Hausdorff space),
and the fibre decomposition is upper semicontinuous. Record the argument; this justifies the
definitions above against Hagopian's wording. -/
theorem admissible_quotient_homeomorph {E : Set X} (hE : IsCompact E) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) :
    Nonempty (Quotient (Setoid.ker k) ≃ₜ unitInterval) := by
  sorry

end Defs

/-! ## Composants (Moore 1962, Theorems 135–139, pp. 58–59) -/

section Composants

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Moore Theorem 135.** Every composant of a nondegenerate compact continuum is dense. -/
theorem composant_dense [Nontrivial X] (x : X) : Dense (Jones.composant x) := by
  sorry

/-- **Moore Theorem 138.** Two composants of an indecomposable continuum are equal or disjoint.
(Reuse `HPC/PseudoArc/Theorem13.lean` if it applies.) -/
theorem composant_eq_or_disjoint (hi : ¬ IsDecomposableSpace X) (x y : X) :
    Jones.composant x = Jones.composant y ∨ Disjoint (Jones.composant x) (Jones.composant y) := by
  sorry

/-- **Moore Theorems 136–137.** A composant of an indecomposable continuum is a countable union of
proper subcontinua, each nowhere dense; so it is meagre. -/
theorem composant_isMeagre [Nontrivial X] (hi : ¬ IsDecomposableSpace X) (x : X) :
    IsMeagre (Jones.composant x) := by
  sorry

/-- **Moore Theorem 139.** An indecomposable nondegenerate compact continuum has uncountably many
composants. -/
theorem uncountable_composants [Nontrivial X] (hi : ¬ IsDecomposableSpace X) :
    (range (Jones.composant : X → Set X)).Uncountable := by
  sorry

end Composants

/-! ## Moore's triod theorem (Moore 1962, Theorem 84, p. 222) -/

/-- **Moore's triod theorem**, in the form Lemma 1 uses: the plane does not contain uncountably
many mutually exclusive triods. Moore's proof runs through his Chapter IV, Theorems 73, 76, 78, 79
(pp. 217–221). Any proof will do; record the route. -/
theorem moore_triod_theorem {ι : Type*} (T : ι → Set Pt) (hT : ∀ i, IsTriodSet (T i))
    (hd : Pairwise (Disjoint on T)) : Countable ι := by
  sorry

/-! ## §2. Lemma 1 -/

section Lemma1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 1** (p. 36). "If `M` is a homogeneous indecomposable plane continuum, then `M` is
atriodic and hereditarily unicoherent." Proof, first paragraph: composants (Moore 138, 139); "Since
`M` is homogeneous, it follows that each of its composants contains a triod"; Moore 84. Second
paragraph: "Note that `F` separates the plane [Moore 22, p. 175]. Since the plane is separable and
`M` has uncountably many composants, there exists a proper subcontinuum of `M` having two
complementary domains that intersect `M`. This contradicts the fact that each composant is dense in
`M` [Moore 135]." (No nondegeneracy hypothesis: for a point both conclusions hold vacuously. Add
`[Nontrivial M]` if the proof wants it, and record it.) -/
theorem hagopian75_lemma1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) :
    IsAtriodic (univ : Set M) ∧ IsHereditarilyUnicoherent (univ : Set M) := by
  sorry

end Lemma1

/-! ## §3. Lemmas 2 and 3: type A′ continua -/

section TypeA

variable {X : Type*} [MetricSpace X]

/-- **Lemma 2** (pp. 36–37). "Let `M` be a continuum that is irreducible between a pair of points.
A necessary and sufficient condition that `M` be of type A′ is that every subcontinuum of `M` with
nonvoid interior be decomposable [Kuratowski Vol. 2, Theorem 3, p. 216] [Thomas, Theorem 10,
p. 15]." Kuratowski's Theorem 3 is about the order type of his family `D`; the passage to a
monotone map onto `[0, 1]` with nowhere dense layers goes through his §48 IV and VII, Theorems 4–5.
Record how. -/
theorem hagopian75_lemma2 {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b) (hab : a ≠ b) :
    IsTypeA' E ↔ ∀ K ⊆ E, Fold.Q78.IsContinuum K →
      (interior (Subtype.val ⁻¹' K : Set E)).Nonempty → ¬ Fold.Q78.IsIndecomposable K := by
  sorry

/-- **End sets** (used in Hagopian 1976 §2, citing Thomas Theorem 8, p. 14). For an admissible map
of a continuum irreducible between `a` and `b`, `a` and `b` lie in the two end layers; and a
subcontinuum meeting both end layers is all of `E`. -/
theorem admissible_end_sets {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b) (hab : a ≠ b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) :
    ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
      ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty → (K ∩ layer k 1).Nonempty →
        K = E := by
  sorry

/-- **The interval lemma** (used in paragraph 9 of Theorem 1: "Since `E` is irreducible between `b`
and `c`, each element of `H = {k⁻¹(u) : d < u < e}` is in `hᵢ[Y]`"). A subcontinuum of `E` meeting
the layers over `d` and `e` contains every layer strictly between. -/
theorem layer_subset_of_meets {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) {K : Set X} (hKE : K ⊆ E)
    (hK : Fold.Q78.IsContinuum K) {d e u : unitInterval} (hd : (K ∩ layer k d).Nonempty)
    (he : (K ∩ layer k e).Nonempty) (hdu : d < u) (hue : u < e) : layer k u ⊆ K := by
  sorry

/-- **Lemma 3** (p. 37), in the form used: for a type A′ continuum, an admissible map whose layers
have void interior is the *minimal* admissible decomposition: each of its layers lies in a layer of
every admissible map. (Printed for type A, citing Thomas Theorems 3 and 6, pp. 8 and 10; Thomas is
not in hand. Kuratowski §48 VII, Theorems 4–5, give the type A′ case.) -/
theorem hagopian75_lemma3 {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    {k' : E → unitInterval} (hk' : IsAdmissibleMap E k') :
    ∀ t, ∃ t', k ⁻¹' {t} ⊆ k' ⁻¹' {t'} := by
  sorry

/-- **Uniqueness.** Two admissible maps of a type A′ continuum whose layers have void interior have
the same layers. So the decomposition is intrinsic, and a homeomorphism carries it to the
decomposition of the image (as paragraph 10 of Theorem 1 uses). -/
theorem hagopian75_lemma3_unique {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k k' : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hk' : IsAdmissibleMap E k') (hk'0 : ∀ t, interior (k' ⁻¹' {t}) = ∅) :
    ∀ x y : E, k x = k y ↔ k' x = k' y := by
  sorry

/-- **Paragraph 4, the alternative** (Thomas Theorem 21, p. 29; Kuratowski §48 VII, Theorem 6): if
every interior layer of a type A′ continuum is degenerate, the continuum is an arc. -/
theorem arc_of_degenerate_layers {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b)
    (hab : a ≠ b) {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hdeg : ∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton) :
    Nonempty (E ≃ₜ unitInterval) := by
  sorry

end TypeA

/-! ## §4. Lemma 4 -/

/-- **Lemma 4** (p. 37). "Suppose `M` is a homogeneous continuum, `ε` is a given positive number,
and `x` is a point of `M`. Then `x` belongs to an open subset `W` of `M` having the following
property. For each pair `y, z` of points of `W` there exists a homeomorphism `h` of `M` onto `M`
such that `h(y) = z` and `ρ(v, h(v)) < ε` for all `v` belonging to `M`." From
`HPC.Effros.effros_homogeneous`. -/
theorem hagopian75_lemma4 {Y : Type*} [MetricSpace Y] [CompactSpace Y] (hX : IsHomogeneous Y)
    {ε : ℝ} (hε : 0 < ε) (x : Y) :
    ∃ W : Set Y, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, ∀ z ∈ W,
      ∃ h : Y ≃ₜ Y, h y = z ∧ ∀ v, dist v (h v) < ε := by
  sorry

/-! ## §5. Theorem 1, paragraphs 1–3 and 5–13 -/

section Theorem1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Theorem 1, paragraph 2** (p. 38). "The continuum `E` does not have an indecomposable
subcontinuum with nonvoid interior (relative to `E`)." The steps quoted: "Since `M` is hereditarily
unicoherent and `I` is indecomposable, `I` is contained in `E ∩ B` or `E ∩ C`"; "Let `F` be the
c-component of `E − Q`"; "`F` meets only one composant of `I`"; "Let `x` be a boundary point of `Q`
that belongs to `F`"; the homeomorphisms `f`, `g` with (1)–(3) by Lemma 4; "Note that `F`, `f[F]`, and
`g[F]` are mutually disjoint. It follows that `B ∪ F ∪ f[F] ∪ g[F]` is a triod, which contradicts
Lemma 1." -/
theorem hagopian75_no_indecomposable_interior (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {B C E : Set M} {b c : M} (hB : Fold.Q78.IsContinuum B)
    (hC : Fold.Q78.IsContinuum C) (hb : b ∈ B \ C) (hc : c ∈ C \ B)
    (hE : IsIrreducibleBetween E b c) (hEBC : E ⊆ B ∪ C) :
    ∀ I ⊆ E, Fold.Q78.IsContinuum I → (interior (Subtype.val ⁻¹' I : Set E)).Nonempty →
      ¬ Fold.Q78.IsIndecomposable I := by
  sorry

/-- **Theorem 1, paragraphs 1–3** (p. 38), the part Hagopian 1976 cites ("[5, Theorem 1
(paragraphs 1, 2, and 3 of proof)]"): a decomposable subcontinuum of a homogeneous indecomposable
plane continuum contains a continuum of type A′. -/
theorem hagopian75_exists_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {A : Set M} (hA : Fold.Q78.IsContinuum A) (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ E ⊆ A, IsTypeA' E := by
  sorry

/-- **Theorem 1, paragraphs 9–11** (p. 39), the part Hagopian 1976 Lemma 3 cites. Let `E ⊆ M` be of
type A′ with layers `k⁻¹(u)` of void interior, `0 < r < s < t < 1`, and `ε` at most the distance
from `k⁻¹[[r, t]]` to `k⁻¹(0) ∪ k⁻¹(1)`. A homeomorphism of `M` moving no point by `ε` or more,
whose image of the layer `Y = k⁻¹(s)` meets `Y`, maps `Y` onto `Y`. Quoted steps: "`hᵢ[Y] ⊂
hᵢk⁻¹[[r,t]] ⊂ E`"; "each element of `H` … is in `hᵢ[Y]`"; "the closure of `R ∪ T` does not meet an
element of `H`. Hence `hᵢ[Y]` contains a nonempty open subset of `hᵢ[E]`"; "Using the same
argument, one can show that if `Y` is not contained in `hᵢ[Y]`, then `Y` has nonvoid interior
relative to `E`". -/
theorem hagopian75_layer_invariant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {r s t : unitInterval}
    (hr0 : 0 < r) (hrs : r < s) (hst : s < t) (ht1 : t < 1) {ε : ℝ}
    (hε : ∀ u v : E, r ≤ k u → k u ≤ t → (k v = 0 ∨ k v = 1) → ε ≤ dist u v)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε) (hY : (h '' layer k s ∩ layer k s).Nonempty) :
    h '' layer k s = layer k s := by
  sorry

/-- **Theorem 1, paragraphs 5–8 and 12** (p. 39): every interior layer of a type A′ subcontinuum of
`M` is homogeneous (chain of Lemma 4 neighbourhoods from `q` to `p` in `Y`, then
`hagopian75_layer_invariant` for each link). Paragraph 4's nondegeneracy is not needed here. -/
theorem hagopian75_layer_homogeneous (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {s : unitInterval}
    (hs0 : 0 < s) (hs1 : s < 1) : IsHomogeneous (layer k s) := by
  sorry

/-- **Theorem 1, paragraph 13** (p. 39). "Since `Y` is a unicoherent homogeneous plane continuum, it
is indecomposable [Jones 1955, Theorem 2]." From `jones55_theorem2'`: a decomposable homogeneous
plane continuum maps onto a circle with connected fibres, so it is not unicoherent. -/
theorem indecomposable_of_unicoherent_homogeneous {N : Set Pt} [CompactSpace N] [ConnectedSpace N]
    (hX : IsHomogeneous N) (hu : IsUnicoherent (univ : Set N)) : ¬ IsDecomposableSpace N := by
  sorry

/-- **Theorem 1 with paragraph 4 as a hypothesis** (p. 38). "Suppose `M` is a homogeneous
indecomposable plane continuum and `A` is a decomposable subcontinuum of `M`. Then `A` contains a
homogeneous indecomposable continuum." Paragraph 4 ("There exists a number `s` (`0 < s < 1`) such
that `k⁻¹(s)` is not degenerate; for otherwise, `E` would contain an arc [Thomas 21] and `M` would be
a simple closed curve [Bing 1960]") is the hypothesis `hnd`. -/
theorem hagopian75_theorem1_of_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hnd : ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ (layer k s).Nontrivial) :
    ∃ Y ⊆ E, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y := by
  sorry

end Theorem1

end HPC.Hagopian
