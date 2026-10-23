import HPC

/-!
# Batch 135: Jones 1948 (non-aposyndetic continua), complete; Jones 1951, the Lemma (and Theorem 1)

Skeleton. Save as `HPC/Jones/Jones48.lean` (new directory), and add `import HPC.Jones.Jones48` at
the end of the root `HPC.lean`. Change `import HPC` above to the specific imports needed (at least
the file defining `Fold.Q78.IsContinuum`, plus `Plane/Atriodic51Defs.lean` and
`Plane/Arcs48.lean`). Every `sorry` is a work item. Shapes may be adjusted, with each change
recorded. Splitting into several files is expected.

## Sources (save under `doc/sources/`)

* F. B. Jones, *Concerning non-aposyndetic continua*, Amer. J. Math. 70 (1948), 403–413
  (`jones1948.pdf`).
* F. B. Jones, *Certain homogeneous unicoherent indecomposable continua*, Proc. AMS 2 (1951),
  855–859 (`jones1951.pdf`).

The statements below are transcribed from page images. Proofs are as printed in the PDFs; see
COMMISSION-batch135.md §3 for the places where Jones gives no proof or only a sketch.

## Convention: the continuum is the whole space

Jones's `M` is the whole space `X`: a compact connected metric space. "Open subset of `M`" is
"open set". A subcontinuum of a subcontinuum is handled by the subtype. This is the setting that
Parts D–H use (Effros: `HPC.Effros.effros_homogeneous`).
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### Definitions (Jones 1948, §1) -/

/-- **`X` is aposyndetic at `x` with respect to `y`** (Jones 1941, 1948 p. 404). There are a
continuum `H` and an open set `U` with `X − y ⊇ H ⊇ U ∋ x`. -/
def AposAt (x y : X) : Prop :=
  ∃ H U : Set X, Fold.Q78.IsContinuum H ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ H ∧ y ∉ H

/-- `X` is **aposyndetic at `x`**: aposyndetic at `x` with respect to every other point. -/
def AposyndeticAt (x : X) : Prop := ∀ y, y ≠ x → AposAt x y

/-- `X` is **aposyndetic**: aposyndetic at each of its points. -/
def IsAposyndetic (X : Type*) [MetricSpace X] : Prop := ∀ x y : X, x ≠ y → AposAt x y

/-- `X` is **totally non-aposyndetic**: non-aposyndetic at each of its points. -/
def TotallyNonAposyndetic (X : Type*) [MetricSpace X] : Prop :=
  ∀ x : X, ¬ AposyndeticAt x

/-- `X` is **semi-locally-connected at `x`** (Whyburn 1939). For each open `U ∋ x` there is an
open `V` with `U ⊇ V ∋ x` such that `X − U` is contained in the union of finitely many components
of `X − V`. -/
def SemiLocConnAt (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
    ∃ F : Finset X, (↑F : Set X) ⊆ Vᶜ ∧ Uᶜ ⊆ ⋃ c ∈ F, connectedComponentIn Vᶜ c

/-- **`p` cuts `x` from `y`** (Jones 1948, p. 403). `x`, `y` are distinct points other than `p`,
and every subcontinuum containing `x` and `y` contains `p`. -/
def CutsPts (p x y : X) : Prop :=
  x ≠ p ∧ y ≠ p ∧ x ≠ y ∧
    ∀ K : Set X, Fold.Q78.IsContinuum K → x ∈ K → y ∈ K → p ∈ K

/-- `p` is a **weak cut point**: it cuts some `x` from some `y`. -/
def IsWeakCutPoint (p : X) : Prop := ∃ x y, CutsPts p x y

/-- `p` is a **strong cut point** (separating point): `X − p` is not connected. -/
def IsStrongCutPoint (p : X) : Prop := ¬ IsConnected ({p}ᶜ : Set X)

/-- The **composant** of `x`: the union of the proper subcontinua containing `x`. -/
def composant (x : X) : Set X :=
  {y | ∃ K : Set X, Fold.Q78.IsContinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}

/-- `X` is **decomposable**: the union of two proper subcontinua. -/
def IsDecomposableSpace (X : Type*) [MetricSpace X] : Prop :=
  ∃ H K : Set X, Fold.Q78.IsContinuum H ∧ Fold.Q78.IsContinuum K ∧ H ≠ univ ∧ K ≠ univ ∧
    H ∪ K = univ

/-! ### Jones 1948, §1 -/

variable [ConnectedSpace X]

/-- **Theorem 0.** `X` is semi-locally-connected at `p` iff it is aposyndetic at each point of
`X − p` with respect to `p`. ("May be established with the help of the Heine–Borel theorem.") -/
theorem theorem0 (p : X) : SemiLocConnAt p ↔ ∀ x, x ≠ p → AposAt x p := by
  sorry

/-- **Theorem 1.** Suppose `xᵢ → x` and `yᵢ → y` with `x ≠ y`, `yᵢ ≠ xᵢ`, and `X` not aposyndetic
at `xᵢ` with respect to `yᵢ`. Then `X` is not aposyndetic at `x` with respect to `y`. -/
theorem theorem1 {x y : X} (u v : ℕ → X) (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 y)) (hxy : x ≠ y) (hne : ∀ i, v i ≠ u i)
    (hna : ∀ i, ¬ AposAt (u i) (v i)) : ¬ AposAt x y := by
  sorry

/-- **Theorem 2.** The set `K` of points `y ≠ x` such that `X` is not aposyndetic at `x` with
respect to `y`, together with `x`, is closed. (No proof printed.) -/
theorem theorem2 (x : X) : IsClosed ({y | y ≠ x ∧ ¬ AposAt x y} ∪ {x}) := by
  sorry

/-- **Theorem 3.** The set `L` of points `x ≠ y` such that `X` is not aposyndetic at `x` with
respect to `y`, together with `y`, is a continuum. (No proof printed. This is Jones 1955's `L_y`,
used there as "Theorem 3 of [11]".) -/
theorem theorem3 (y : X) : Fold.Q78.IsContinuum ({x | x ≠ y ∧ ¬ AposAt x y} ∪ {y}) := by
  sorry

/-- **Theorem 4.** The set of points at which `X` is non-aposyndetic is an `F_σ`. -/
theorem theorem4 : ∃ F : ℕ → Set X, (∀ i, IsClosed (F i)) ∧
    {x : X | ¬ AposyndeticAt x} = ⋃ i, F i := by
  sorry

/-- **Theorem 5.** The set of points at which `X` is not semi-locally-connected is an `F_σ`.
("Theorem 0 and an argument similar to that used for Theorem 4.") -/
theorem theorem5 : ∃ F : ℕ → Set X, (∀ i, IsClosed (F i)) ∧
    {x : X | ¬ SemiLocConnAt x} = ⋃ i, F i := by
  sorry

/-- **Theorem 6.** Let `D` be open and nonempty, and `M₀` closed with `D ∩ M₀ = ∅`. Suppose that
for each `x ∈ D` there is `y ∈ M₀` such that `X` is not aposyndetic at `x` with respect to `y`.
Then for each `z ∉ M₀` there are `x₀ ∈ D` and `y₀ ∈ M₀` with `y₀` cutting `x₀` from `z`.
(Jones's footnote 6: `D` may meet `M₀`. "Nonempty" is implicit in the text; check whether it is
needed.) -/
theorem theorem6 {D M₀ : Set X} (hD : IsOpen D) (hDne : D.Nonempty) (hM₀ : IsClosed M₀)
    (hDM : Disjoint D M₀) (h : ∀ x ∈ D, ∃ y ∈ M₀, ¬ AposAt x y) {z : X} (hz : z ∉ M₀) :
    ∃ x₀ ∈ D, ∃ y₀ ∈ M₀, CutsPts y₀ x₀ z := by
  sorry

/-- **Theorem 7.** The product of two nondegenerate continua is aposyndetic at each of its
points. (Stated for two compact connected metric spaces, both nontrivial.) -/
theorem theorem7 (Y Z : Type*) [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nontrivial Y] [MetricSpace Z] [CompactSpace Z] [ConnectedSpace Z] [Nontrivial Z] :
    IsAposyndetic (Y × Z) := by
  sorry

/-! ### Jones 1948, §2: indecomposable continua -/

/-- **Theorem 8.** `X` is decomposable iff there are distinct `x`, `y` with `X` aposyndetic at `x`
with respect to `y`. -/
theorem theorem8 : IsDecomposableSpace X ↔ ∃ x y : X, x ≠ y ∧ AposAt x y := by
  sorry

/-- **Theorem 9.** `X` is indecomposable iff there are no distinct `x`, `y` with `X` aposyndetic
at `x` with respect to `y`. -/
theorem theorem9 : ¬ IsDecomposableSpace X ↔ ∀ x y : X, x ≠ y → ¬ AposAt x y := by
  sorry

/-- **Theorem 10.** `X` is indecomposable iff it contains an open set `D` such that `X` is not
aposyndetic at any `x ∈ D` with respect to any `y ≠ x`. **As printed, `D` may be empty, and then
the condition holds in every continuum.** `D` must be nonempty; this is a candidate ledger entry.
Prove the corrected form, and the refutation of the printed form for any decomposable
continuum. -/
theorem theorem10 [Nontrivial X] :
    ¬ IsDecomposableSpace X ↔
      ∃ D : Set X, IsOpen D ∧ D.Nonempty ∧ ∀ x ∈ D, ∀ y, y ≠ x → ¬ AposAt x y := by
  sorry

/-! ### Jones 1948, §3: cut point existence -/

/-- **Theorem 11.** Let `z ∈ X` and `D ⊆ X − z` open (nonempty). Suppose `X` is non-aposyndetic at
every point of `D`, but aposyndetic at each point of `D` with respect to `z`. Then `D` contains a
point `x`, and `X` a point `y`, such that `y` cuts `x` from `z`. -/
theorem theorem11 {z : X} {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty) (hzD : z ∉ D)
    (h1 : ∀ x ∈ D, ¬ AposyndeticAt x) (h2 : ∀ x ∈ D, AposAt x z) :
    ∃ x ∈ D, ∃ y, CutsPts y x z := by
  sorry

/-- **Theorem 12.** If `D` is open (nonempty) and `X` is non-aposyndetic at every point of `D`,
then `D` contains a point `x`, and `X` points `y`, `z`, such that `y` cuts `x` from `z`.
(Uses composants in the indecomposable case.) -/
theorem theorem12 {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty)
    (h : ∀ x ∈ D, ¬ AposyndeticAt x) : ∃ x ∈ D, ∃ y z, CutsPts y x z := by
  sorry

/-- **Corollary (p. 409).** A totally non-aposyndetic continuum contains a weak cut point. Jones
1955 cites it as "[11, p. 409]". -/
theorem totallyNonApos_exists_weakCutPoint [Nonempty X] (h : TotallyNonAposyndetic X) :
    ∃ p : X, IsWeakCutPoint p := by
  sorry

/-- **Theorem 13.** Let `D` be open (nonempty), and suppose that for each `p ∈ D` there is a point
`o ≠ p` such that `X` is not aposyndetic at `o` with respect to `p`. Then `D` contains distinct
`x`, `y`, `z` with `y` cutting `x` from `z`. (The longest proof of the paper.) -/
theorem theorem13 {D : Set X} (hD : IsOpen D) (hDne : D.Nonempty)
    (h : ∀ p ∈ D, ∃ o, o ≠ p ∧ ¬ AposAt o p) :
    ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D, CutsPts y x z := by
  sorry

/-- **Theorem 14.** If for each `p` there is `q` such that `X` is not aposyndetic at `q` with
respect to `p`, then the weak cut points are dense. ("Follows immediately from Theorem 13.") -/
theorem theorem14 (h : ∀ p : X, ∃ q, q ≠ p ∧ ¬ AposAt q p) :
    Dense {p : X | IsWeakCutPoint p} := by
  sorry

/-- **Theorem 15.** If `X` is not semi-locally-connected at any point of the open set `U`, then
the weak cut points are dense in `U`. ("May be established with the help of Theorems 0 and 13.")
-/
theorem theorem15 {U : Set X} (hU : IsOpen U) (h : ∀ x ∈ U, ¬ SemiLocConnAt x) :
    U ⊆ closure {p : X | IsWeakCutPoint p} := by
  sorry

/-- **Corollary (Theorem 15).** If `X` is semi-locally-connected at no point, then its weak cut
points are dense. -/
theorem theorem15_cor (h : ∀ x : X, ¬ SemiLocConnAt x) : Dense {p : X | IsWeakCutPoint p} := by
  sorry

/-! ### Jones 1948, §4: totally non-aposyndetic continua with only one weak cut point -/

/-- **Theorem 16.** If the nondegenerate `X` has only one weak cut point `p`, the composant of `p`
is `X`. (Jones writes "the composant of `M` containing `P`"; `P` is the cut point.) -/
theorem theorem16 [Nontrivial X] {p : X} (hp : IsWeakCutPoint p)
    (honly : ∀ q, IsWeakCutPoint q → q = p) : composant p = univ := by
  sorry

/-- **Theorem 17.** If `X` is totally non-aposyndetic with only one weak cut point `p`, then `X` is
non-aposyndetic at each point of `X − p` with respect to `p`. -/
theorem theorem17 (htn : TotallyNonAposyndetic X) {p : X} (hp : IsWeakCutPoint p)
    (honly : ∀ q, IsWeakCutPoint q → q = p) : ∀ x, x ≠ p → ¬ AposAt x p := by
  sorry

/-- **Corollary (Theorem 17).** Under the same hypotheses, `X` is not semi-locally-connected at
`p`. -/
theorem theorem17_cor [Nontrivial X] (htn : TotallyNonAposyndetic X) {p : X}
    (hp : IsWeakCutPoint p) (honly : ∀ q, IsWeakCutPoint q → q = p) : ¬ SemiLocConnAt p := by
  sorry

/-! ### Jones 1948, §5: continua containing no weak cut point -/

/-- **Theorem 18.** If `X` contains no weak cut point, the set of points at which `X` is both
aposyndetic and semi-locally-connected is a dense `G_δ`. ("May be proved with the help of
Theorems 4, 5, 12, and 15.") Jones 1949 cites it to get a point of aposyndesis. -/
theorem theorem18 (h : ∀ p : X, ¬ IsWeakCutPoint p) :
    IsGδ {x : X | AposyndeticAt x ∧ SemiLocConnAt x} ∧
      Dense {x : X | AposyndeticAt x ∧ SemiLocConnAt x} := by
  sorry

/-- **Theorem 19.** If the open set `U` (nonempty) contains no weak cut point, `U` contains a
point at which `X` is semi-locally-connected. ("Follows from Theorem 15.") -/
theorem theorem19 {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ p ∈ U, ¬ IsWeakCutPoint p) : ∃ x ∈ U, SemiLocConnAt x := by
  sorry

/-! ### Jones 1951: the Lemma, and Theorem 1 -/

/-- Jones 1951's `U_x`: the points `z ≠ x` at which `X` is aposyndetic with respect to `x`. It is
open (Jones: "It is evident"). Jones 1955's `U_x = M − L_x`. -/
def aposSet (x : X) : Set X := {z | z ≠ x ∧ AposAt z x}

theorem isOpen_aposSet (x : X) : IsOpen (aposSet x) := by
  sorry

/-- `X` is **homogeneous**. -/
def IsHomogeneous (X : Type*) [TopologicalSpace X] : Prop := ∀ x y : X, ∃ h : X ≃ₜ X, h x = y

/-- **Jones 1951, Lemma.** If `X` is homogeneous and `x ≠ y`, then `U_y` is not a proper subset of
`U_x`. (The proof runs a transfinite sequence through all countable ordinals and contradicts it:
no strictly decreasing `ω₁`-sequence of open sets exists in a second countable space. Jones 1955
uses this twice, as "the lemma of [5]".) -/
theorem jones51_lemma (hX : IsHomogeneous X) {x y : X} (hxy : x ≠ y) :
    ¬ (aposSet y ⊂ aposSet x) := by
  sorry

/-- **Jones 1951, Theorem 1.** A homogeneous, hereditarily unicoherent, compact metric continuum is
indecomposable. **Stretch item.** The last paragraph treats an upper semicontinuous decomposition
`G` "with respect to its elements as points" as a continuum `M′`. That needs the decomposition
space of a compact metric space to be compact metrizable (Moore 1925; COMMISSION-batch135.md
§2.C). It also cites Whyburn 1939, Theorem 6.21 (in an aposyndetic continuum, cut points are
separating points). Attempt it after everything else. -/
theorem jones51_theorem1 [Nontrivial X] (hX : IsHomogeneous X)
    (hhu : HPC.Plane.IsHereditarilyUnicoherent (univ : Set X)) : ¬ IsDecomposableSpace X := by
  sorry

end HPC.Jones
