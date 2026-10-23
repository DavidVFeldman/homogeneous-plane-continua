import HPC.Hagopian.H75Transfer
import HPC.Hagopian.H75Composants
import HPC.Hagopian.H75Jones
import HPC.Hagopian.H75Thm1C
import HPC.Hagopian.H75Counter
import HPC.Hagopian.H75MooreB
import HPC.Hagopian.H75Sine

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

/-- **The map form is the decomposition form.** For an admissible map, the fibre relation's
quotient space is homeomorphic to `[0, 1]` (closed map of a compact space onto a Hausdorff space),
and the fibre decomposition is upper semicontinuous. Record the argument; this justifies the
definitions above against Hagopian's wording.

*The argument, both directions* (only map ⇒ decomposition is formalized):
* **Map ⇒ decomposition.** Let `k` be admissible. Its fibres are closed in the compact `E`, hence
  compact (Hagopian's elements are compact sets, p. 36), and connected; they partition `E`. `k` is a
  closed map (compact to Hausdorff), so for `Q` open the union of the fibres inside `Q` is
  `E ∖ k⁻¹(k(E ∖ Q))`, open: the decomposition is upper semicontinuous. The induced bijection of the
  quotient onto `[0, 1]` is continuous from a compact space to a Hausdorff one, hence a homeomorphism
  (the proof below).
* **Decomposition ⇒ map.** Let `D` be an upper semicontinuous decomposition of `E` into connected
  (compact) elements and `φ` a homeomorphism of the quotient space onto `[0, 1]`. With `π` the quotient
  map, `k = φ ∘ π` is continuous (Hagopian's quotient topology makes `π` continuous by definition) and
  onto, and its fibres are exactly the elements of `D`, which are connected. So `k` is admissible, and
  the elements of `D` are the layers `k⁻¹(t)`; void interior of elements is the same condition in both
  forms. -/
theorem admissible_quotient_homeomorph {E : Set X} (hE : IsCompact E) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) :
    Nonempty (Quotient (Setoid.ker k) ≃ₜ unitInterval) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE
  set e := Setoid.quotientKerEquivOfSurjective k hk.2.1
  have hc : Continuous e := continuous_quot_lift _ hk.1
  exact ⟨hc.homeoOfEquivCompactToT2⟩

end Defs

/-! ## Composants (Moore 1962, Theorems 135–139, pp. 58–59) -/

section Composants

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Moore Theorem 135.** Every composant of a nondegenerate compact continuum is dense. -/
theorem composant_dense [Nontrivial X] (x : X) : Dense (Jones.composant x) :=
  composant_dense' x

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Moore Theorem 138.** Two composants of an indecomposable continuum are equal or disjoint.
(Reuse `HPC/PseudoArc/Theorem13.lean` if it applies.)

*Shape change (generalization):* the section's `[CompactSpace X] [ConnectedSpace X]` are omitted
(not used: the argument is the decomposition `K ∪ L` of a union of two proper subcontinua). -/
theorem composant_eq_or_disjoint (hi : ¬ IsDecomposableSpace X) (x y : X) :
    Jones.composant x = Jones.composant y ∨ Disjoint (Jones.composant x) (Jones.composant y) :=
  composant_eq_or_disjoint' hi x y

/-- **Moore Theorems 136–137.** A composant of an indecomposable continuum is a countable union of
proper subcontinua, each nowhere dense; so it is meagre. -/
theorem composant_isMeagre [Nontrivial X] (hi : ¬ IsDecomposableSpace X) (x : X) :
    IsMeagre (Jones.composant x) :=
  composant_isMeagre' hi x

/-- **Moore Theorem 139.** An indecomposable nondegenerate compact continuum has uncountably many
composants.

*Shape change:* the skeleton's conclusion `(range (Jones.composant : X → Set X)).Uncountable` does
not elaborate (Mathlib has no `Set.Uncountable`); it is stated as `¬ (range …).Countable`. -/
theorem uncountable_composants [Nontrivial X] (hi : ¬ IsDecomposableSpace X) :
    ¬ (range (Jones.composant : X → Set X)).Countable :=
  uncountable_composants' hi

end Composants

/-! ## Moore's triod theorem (Moore 1962, Theorem 84, p. 222) -/

open Function in
/-- **Moore's triod theorem**, in the form Lemma 1 uses: the plane does not contain uncountably
many mutually exclusive triods. Moore's proof runs through his Chapter IV, Theorems 73, 76, 78, 79
(pp. 217–221). Any proof will do; record the route.

*Route* (`H75MooreA.lean`, `H75MooreB.lean`): Moore's own two cases.
* Cores separating the plane (Moore 73, `countable_of_separating`): two triods sharing a small
  ball `Q` (off both cores) and a point `o` in a complementary domain of each core not containing
  `Q` would have equal complementary domains at `o`, whose frontier lies in both (disjoint) cores.
* Non-separating cores (Moore 79, 78, 76, `countable_of_nonseparating`): each core is enclosed by
  a simple closed polygon (`enclose_holds`) whose closed inside misses a point of each leg; a
  countable pigeonhole gives uncountably many triods with cores inside one polygon `J`; each
  contains a continuum in the closed inside meeting `J` on all three legs (boundary bumping); `J` is
  parametrized by `[0, 2)` (`exists_loop_param`), and two triods whose three boundary points lie in
  the same three disjoint rational parameter intervals contradict the interlacing lemma
  (`interlace`, Moore's Theorem 76 proved from Janiszewski's theorem, with no cross-cut).

Statement verbatim. The supporting lemmas take the proposition `MooreTriodStatement` as a
hypothesis `hmoore`; the theorems below discharge it with `mooreTriodStatement`. (`open Function in`
makes the skeleton's notation `Disjoint on T` available.) -/
theorem moore_triod_theorem {ι : Type*} (T : ι → Set Pt) (hT : ∀ i, IsTriodSet (T i))
    (hd : Pairwise (Disjoint on T)) : Countable ι :=
  moore_triod_theorem' T hT hd

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
`[Nontrivial M]` if the proof wants it, and record it.)

Statement verbatim. No nondegeneracy hypothesis is needed. Atriodicity uses Moore's triod theorem
(`mooreTriodStatement`); hereditary unicoherence does not (`hagopian75_lemma1_hu`). -/
theorem hagopian75_lemma1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) :
    IsAtriodic (univ : Set M) ∧ IsHereditarilyUnicoherent (univ : Set M) :=
  ⟨atriodic_of_homogeneous_indecomposable mooreTriodStatement hX hi,
    hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi⟩

/-- **Lemma 1, second paragraph**, unconditionally: a homogeneous indecomposable plane continuum is
hereditarily unicoherent. (Moore 22 by Borsuk's theorem; the "separable" step by disjointness of the
complementary domains missing `M`; the density step by Baire and Moore 138; see `H75Lemma1.lean`.) -/
theorem hagopian75_lemma1_hu (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) :
    IsHereditarilyUnicoherent (univ : Set M) :=
  hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi

end Lemma1

/-! ## §3. Lemmas 2 and 3: type A′ continua -/

section TypeA

variable {X : Type*} [MetricSpace X]

/-- **Lemma 2** (pp. 36–37). "Let `M` be a continuum that is irreducible between a pair of points.
A necessary and sufficient condition that `M` be of type A′ is that every subcontinuum of `M` with
nonvoid interior be decomposable [Kuratowski Vol. 2, Theorem 3, p. 216] [Thomas, Theorem 10,
p. 15]." Kuratowski's Theorem 3 is about the order type of his family `D`; the passage to a
monotone map onto `[0, 1]` with nowhere dense layers goes through his §48 IV and VII, Theorems 4–5.
Record how.

*How:* Kuratowski's family `D` (§48 III; `IsDElt`) is a chain (`IsDElt.chain`) without jumps when
every subcontinuum with interior is decomposable (`IsDElt.exists_between`, the content of VII
Theorem 1); a countable basis gives a countable subfamily dense in `D` (`exists_countable_dense_D`),
which is order-isomorphic to `ℚ ∩ (0, 1)` (Cantor); indexing by it gives a scale `q ↦ D_q`
(`exists_scale`), and `k(y) = inf {q : y ∈ D_q}` is continuous, onto, with connected fibres of void
interior (`scaleMap_spec`, the content of §48 IV and VII Theorems 4–5). Theorem 3 ("`D` has the order
type of the interval") is replaced by the order type of the countable dense part.

*Shape change:* the hypothesis `hab : a ≠ b` is dropped (not used: for `a = b` both sides fail). -/
theorem hagopian75_lemma2 {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b) :
    IsTypeA' E ↔ ∀ K ⊆ E, Fold.Q78.IsContinuum K →
      (interior (Subtype.val ⁻¹' K : Set E)).Nonempty → ¬ Fold.Q78.IsIndecomposable K := by
  constructor
  · rintro ⟨-, k, hk, hk0⟩ K hKE hK hint
    exact not_isIndecomposable_of_typeA' hE hk hk0 hKE hK hint
  · exact isTypeA'_of_decomposable hE

/-! **End sets** (used in Hagopian 1976 §2, citing Thomas Theorem 8, p. 14). For an admissible map
of a continuum irreducible between `a` and `b`, `a` and `b` lie in the two end layers; and a
subcontinuum meeting both end layers is all of `E`.

**Refuted as stated** (`not_admissible_end_sets`, `H75Counter.lean`): the second half fails without
the type A′ condition. On `E = [0, 2] ⊆ ℝ`, irreducible between `0` and `2`, the map
`k(x) = max 0 (x − 1)` is admissible with end layer `k⁻¹(0) = [0, 1]`, and `K = [1, 2]` meets both end
layers. The statement is kept, commented out; `admissible_end_sets'` below adds `hk0`. -/
/-
theorem admissible_end_sets {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b) (hab : a ≠ b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) :
    ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
      ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty → (K ∩ layer k 1).Nonempty →
        K = E := by
  sorry
-/

/-- **End sets, corrected.** *Shape change:* the type A′ hypothesis `hk0` is added (it is satisfied
wherever Hagopian 1976 uses end sets: the map of a type A′ continuum); `hab` is dropped (not used).
The first half holds for every admissible map (`end_layers`). -/
theorem admissible_end_sets' {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) :
    ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
      ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty → (K ∩ layer k 1).Nonempty →
        K = E :=
  ⟨end_layers hE hk, fun _ hKE hK h0 h1 => eq_of_meets_ends hE hk hk0 hKE hK h0 h1⟩

/-- **The interval lemma** (used in paragraph 9 of Theorem 1: "Since `E` is irreducible between `b`
and `c`, each element of `H = {k⁻¹(u) : d < u < e}` is in `hᵢ[Y]`"). A subcontinuum of `E` meeting
the layers over `d` and `e` contains every layer strictly between. -/
theorem layer_subset_of_meets {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) {K : Set X} (hKE : K ⊆ E)
    (hK : Fold.Q78.IsContinuum K) {d e u : unitInterval} (hd : (K ∩ layer k d).Nonempty)
    (he : (K ∩ layer k e).Nonempty) (hdu : d < u) (hue : u < e) : layer k u ⊆ K := by
  obtain ⟨a, b, hab⟩ := hE
  exact layer_subset_of_meets' hab hk hKE hK hd he hdu hue

/-- **Lemma 3** (p. 37), in the form used: for a type A′ continuum, an admissible map whose layers
have void interior is the *minimal* admissible decomposition: each of its layers lies in a layer of
every admissible map. (Printed for type A, citing Thomas Theorems 3 and 6, pp. 8 and 10; Thomas is
not in hand. Kuratowski §48 VII, Theorems 4–5, give the type A′ case.) -/
theorem hagopian75_lemma3 {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    {k' : E → unitInterval} (hk' : IsAdmissibleMap E k') :
    ∀ t, ∃ t', k ⁻¹' {t} ⊆ k' ⁻¹' {t'} := by
  obtain ⟨a, b, hab⟩ := hE
  exact fibre_subset_fibre hab hk hk0 hk'

/-- **Uniqueness.** Two admissible maps of a type A′ continuum whose layers have void interior have
the same layers. So the decomposition is intrinsic, and a homeomorphism carries it to the
decomposition of the image (as paragraph 10 of Theorem 1 uses). -/
theorem hagopian75_lemma3_unique {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k k' : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hk' : IsAdmissibleMap E k') (hk'0 : ∀ t, interior (k' ⁻¹' {t}) = ∅) :
    ∀ x y : E, k x = k y ↔ k' x = k' y := by
  obtain ⟨a, b, hab⟩ := hE
  exact fibre_eq_iff hab hk hk0 hk' hk'0

/-! **Paragraph 4, the alternative** (Thomas Theorem 21, p. 29; Kuratowski §48 VII, Theorem 6): if
every interior layer of a type A′ continuum is degenerate, the continuum is an arc.

**Refuted as stated** (`not_arc_of_degenerate_layers`, `H75Sine.lean`): the `sin (1/x)`-continuum
`E = {(x, sin (1/x)) : 0 < x ≤ 1} ∪ ({0} × [−1, 1])` is irreducible between `(1, sin 1)` and `(0, 0)`,
the projection `k(x, y) = x` is admissible, its layers have void interior, and its interior layers
are points; but `E` is not an arc — the end layer `k⁻¹(0)` is not degenerate. What Hagopian uses
("`E` would contain an arc") is proved as `exists_arc_of_degenerate_layers`, and the arc conclusion
under degeneracy of *all* layers as `arc_of_degenerate_layers'` (`H75Counter.lean`). The printed
statement is kept, commented out. -/
/-
theorem arc_of_degenerate_layers {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b)
    (hab : a ≠ b) {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hdeg : ∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton) :
    Nonempty (E ≃ₜ unitInterval) := by
  sorry
-/

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
  obtain ⟨δ, hδ, hh⟩ := HPC.Effros.effros_homogeneous hX hε
  refine ⟨ball x (δ / 2), isOpen_ball, mem_ball_self (half_pos hδ), fun y hy z hz => ?_⟩
  have hyz : dist y z < δ := by
    have := dist_triangle_right y z x
    rw [mem_ball] at hy hz
    linarith
  obtain ⟨h, hyz', hmove⟩ := hh y z hyz
  exact ⟨h, hyz', fun v => by rw [dist_comm]; exact hmove v⟩

/-! ## §5. Theorem 1, paragraphs 1–3 and 5–13 -/

section Theorem1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Theorem 1, paragraph 2** (p. 38). "The continuum `E` does not have an indecomposable
subcontinuum with nonvoid interior (relative to `E`)." The steps quoted: "Since `M` is hereditarily
unicoherent and `I` is indecomposable, `I` is contained in `E ∩ B` or `E ∩ C`"; "Let `F` be the
c-component of `E − Q`"; "`F` meets only one composant of `I`"; "Let `x` be a boundary point of `Q`
that belongs to `F`"; the homeomorphisms `f`, `g` with (1)–(3) by Lemma 4; "Note that `F`, `f[F]`, and
`g[F]` are mutually disjoint. It follows that `B ∪ F ∪ f[F] ∪ g[F]` is a triod, which contradicts
Lemma 1." The argument written out (core `B`, the three pieces, their disjointness, the choice of
`f`, `g`) is in `H75Thm1A.lean`.

Statement verbatim. -/
theorem hagopian75_no_indecomposable_interior (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {B C E : Set M} {b c : M} (hB : Fold.Q78.IsContinuum B)
    (hC : Fold.Q78.IsContinuum C) (hb : b ∈ B \ C) (hc : c ∈ C \ B)
    (hE : IsIrreducibleBetween E b c) (hEBC : E ⊆ B ∪ C) :
    ∀ I ⊆ E, Fold.Q78.IsContinuum I → (interior (Subtype.val ⁻¹' I : Set E)).Nonempty →
      ¬ Fold.Q78.IsIndecomposable I :=
  no_indecomposable_interior_aux hX (hagopian75_lemma1_hu hX hi)
    (hagopian75_lemma1 hX hi).1 hB hC hb hc hE hEBC

/-- **Theorem 1, paragraphs 1–3** (p. 38), the part Hagopian 1976 cites ("[5, Theorem 1
(paragraphs 1, 2, and 3 of proof)]"): a decomposable subcontinuum of a homogeneous indecomposable
plane continuum contains a continuum of type A′.

Statement verbatim. -/
theorem hagopian75_exists_typeA' (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {A : Set M} (hA : Fold.Q78.IsContinuum A)
    (hAd : ¬ Fold.Q78.IsIndecomposable A) : ∃ E ⊆ A, IsTypeA' E :=
  exists_typeA'_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hA hAd

/-- **Theorem 1, paragraphs 9–11** (p. 39), the part Hagopian 1976 Lemma 3 cites. Let `E ⊆ M` be of
type A′ with layers `k⁻¹(u)` of void interior, `0 < r < s < t < 1`, and `ε` at most the distance
from `k⁻¹[[r, t]]` to `k⁻¹(0) ∪ k⁻¹(1)`. A homeomorphism of `M` moving no point by `ε` or more,
whose image of the layer `Y = k⁻¹(s)` meets `Y`, maps `Y` onto `Y`. Quoted steps: "`hᵢ[Y] ⊂
hᵢk⁻¹[[r,t]] ⊂ E`"; "each element of `H` … is in `hᵢ[Y]`"; "the closure of `R ∪ T` does not meet an
element of `H`. Hence `hᵢ[Y]` contains a nonempty open subset of `hᵢ[E]`"; "Using the same
argument, one can show that if `Y` is not contained in `hᵢ[Y]`, then `Y` has nonvoid interior
relative to `E`". The argument written out is in `H75Thm1B.lean`; the "same argument" of
paragraph 11 is paragraph 10 applied to `h⁻¹`.

*Shape change:* `hr0 : 0 < r` and `ht1 : t < 1` are dropped (not
used: `ε > 0` already forces `k⁻¹[r, t]` to miss the end layers). -/
theorem hagopian75_layer_invariant (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {r s t : unitInterval}
    (hrs : r < s) (hst : s < t) {ε : ℝ}
    (hε : ∀ u v : E, r ≤ k u → k u ≤ t → (k v = 0 ∨ k v = 1) → ε ≤ dist u v)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε) (hY : (h '' layer k s ∩ layer k s).Nonempty) :
    h '' layer k s = layer k s :=
  hagopian75_layer_invariant_aux (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE
    hk hk0 hrs hst hε h hh hY

/-- **Theorem 1, paragraphs 5–8 and 12** (p. 39): every interior layer of a type A′ subcontinuum of
`M` is homogeneous (chain of Lemma 4 neighbourhoods from `q` to `p` in `Y`, then
`hagopian75_layer_invariant` for each link). Paragraph 4's nondegeneracy is not needed here.

Statement verbatim. -/
theorem hagopian75_layer_homogeneous (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {s : unitInterval}
    (hs0 : 0 < s) (hs1 : s < 1) : IsHomogeneous (layer k s) :=
  layer_homogeneous_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hk hk0
    hs0 hs1

/-- **Theorem 1, paragraph 13** (p. 39). "Since `Y` is a unicoherent homogeneous plane continuum, it
is indecomposable [Jones 1955, Theorem 2]." From `jones55_theorem2'`: a decomposable homogeneous
plane continuum maps onto a circle with connected fibres, so it is not unicoherent. -/
theorem indecomposable_of_unicoherent_homogeneous {N : Set Pt} [CompactSpace N] [ConnectedSpace N]
    (hX : IsHomogeneous N) (hu : IsUnicoherent (univ : Set N)) : ¬ IsDecomposableSpace N :=
  indecomposable_of_unicoherent_homogeneous_aux hX hu

/-- **Theorem 1 with paragraph 4 as a hypothesis** (p. 38). "Suppose `M` is a homogeneous
indecomposable plane continuum and `A` is a decomposable subcontinuum of `M`. Then `A` contains a
homogeneous indecomposable continuum." Paragraph 4 ("There exists a number `s` (`0 < s < 1`) such
that `k⁻¹(s)` is not degenerate; for otherwise, `E` would contain an arc [Thomas 21] and `M` would be
a simple closed curve [Bing 1960]") is the hypothesis `hnd`.

Statement verbatim. -/
theorem hagopian75_theorem1_of_layer (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hnd : ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ (layer k s).Nontrivial) :
    ∃ Y ⊆ E, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y :=
  theorem1_of_layer_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hk hk0
    hnd

end Theorem1

end HPC.Hagopian
