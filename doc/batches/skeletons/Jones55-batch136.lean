import HPC.Jones.Jones48

/-!
# Batch 136 skeleton: decomposition spaces; Whyburn 1939 (6.2), (6.21); Jones 1951 Theorem 1;
# Jones 1955 Theorem 1

Save as `HPC/Jones/Jones55.lean` (splitting into several files under `HPC/Jones/` is expected);
add `import HPC.Jones.Jones55` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may
be adjusted (Lean syntax of `Setoid` application, instance plumbing for the quotient, etc.), each
change recorded at the statement and in the report.

Sources (in `doc/sources/`): `jones1955.pdf` (pp. 735–739), `jones1951.pdf`, `whyburn1939.pdf`
(new: G. T. Whyburn, *Semi-locally connected sets*, Amer. J. Math. 61 (1939), 733–749, §6),
`jones1941.pdf` (new: F. B. Jones, *Aposyndetic continua and certain boundary problems*, Amer. J.
Math. 63 (1941), 545–553, Theorem 4). Statements below were transcribed from page images rendered
at 200 dpi.
-/

namespace HPC.Jones

open Set Topology Filter Metric

/-! ## §1. Aposyndesis for a topological space

`AposAt` of batch 135 is stated under `[MetricSpace X]`. The quotient of §2 is first only a
topological space, so the same notion is restated for a topological space and identified with the
metric one. -/

section Top

variable {Y : Type*} [TopologicalSpace Y]

/-- `AposAt`, for a topological space. Same body as `AposAt`. -/
def AposAtT (x y : Y) : Prop :=
  ∃ H U : Set Y, Fold.Q78.IsContinuum H ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ H ∧ y ∉ H

/-- Aposyndetic, for a topological space. -/
def IsAposyndeticT (Y : Type*) [TopologicalSpace Y] : Prop := ∀ x y : Y, x ≠ y → AposAtT x y

end Top

theorem aposAtT_iff {X : Type*} [MetricSpace X] (x y : X) : AposAtT x y ↔ AposAt x y := by
  sorry

/-! ## §2. Upper semicontinuous decompositions (general; item A of the commission)

A decomposition of `X` is a `Setoid X`; its elements are the classes `cls r x = {y | r y x}`. -/

section Decomp

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The element of the decomposition containing `x`. -/
def cls (r : Setoid X) (x : X) : Set X := {y | r y x}

/-- **Upper semicontinuous decomposition into closed sets** (Moore 1925, p. 416, restated with open
sets). Each element is closed, and if an element lies in an open `U`, then so does every element
meeting some open `V` around it. -/
structure IsUSCDecomp (r : Setoid X) : Prop where
  closed : ∀ x, IsClosed (cls r x)
  usc : ∀ x U, IsOpen U → cls r x ⊆ U →
    ∃ V, IsOpen V ∧ cls r x ⊆ V ∧ ∀ z ∈ V, cls r z ⊆ U

/-- **Lower semicontinuity at an element** ("`G` is continuous at `g`" for an u.s.c. `G`): every
element near `g` comes near every point of `g`. -/
def LSCAt (r : Setoid X) (x : X) : Prop :=
  ∀ y ∈ cls r x, ∀ V, IsOpen V → y ∈ V →
    ∃ W, IsOpen W ∧ cls r x ⊆ W ∧ ∀ z ∈ W, (cls r z ∩ V).Nonempty

/-- A **continuous** decomposition: u.s.c. and l.s.c. at every element. -/
def IsContinuousDecomp (r : Setoid X) : Prop := IsUSCDecomp r ∧ ∀ x, LSCAt r x

variable {r : Setoid X}

/-- The quotient map of an u.s.c. decomposition is closed. -/
theorem isClosedMap_mk (h : IsUSCDecomp r) : IsClosedMap (Quotient.mk r) := by
  sorry

theorem t2Space_quotient (h : IsUSCDecomp r) : T2Space (Quotient r) := by
  sorry

theorem secondCountable_quotient (h : IsUSCDecomp r) :
    SecondCountableTopology (Quotient r) := by
  sorry

/-- **The decomposition space is compact metrizable.** -/
theorem metrizableSpace_quotient (h : IsUSCDecomp r) :
    TopologicalSpace.MetrizableSpace (Quotient r) := by
  sorry

/-- Monotone decompositions: preimages of subcontinua are subcontinua. -/
theorem isContinuum_preimage (h : IsUSCDecomp r) (hconn : ∀ x, IsConnected (cls r x))
    {K : Set (Quotient r)} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (Quotient.mk r ⁻¹' K) := by
  sorry

/-- **Homeomorphisms that permute the elements descend to the decomposition space.** -/
theorem exists_homeomorph_quotient (T : X ≃ₜ X) (hT : ∀ x y, r x y ↔ r (T x) (T y)) :
    ∃ S : Quotient r ≃ₜ Quotient r, ∀ x, S (Quotient.mk r x) = Quotient.mk r (T x) := by
  sorry

/-- **The theorem Jones 1955 uses without statement:** an u.s.c. decomposition of a compact metric
space into closed sets is continuous at the elements of a residual subset of the decomposition
space. (Kuratowski; Fort's theorem on semicontinuous set-valued maps.) Shape: the set of classes
at which `r` is l.s.c. is residual in `Quotient r`. -/
theorem residual_lscAt (h : IsUSCDecomp r) :
    {q : Quotient r | ∀ x, Quotient.mk r x = q → LSCAt r x} ∈ residual (Quotient r) := by
  sorry

/-- Consequence used: in a nonempty space, some element is a point of continuity. -/
theorem exists_lscAt [Nonempty X] (h : IsUSCDecomp r) : ∃ x, LSCAt r x := by
  sorry

end Decomp

/-! ## §3. Whyburn 1939 (6.2), (6.21), and Jones 1941 Theorem 4 (item B)

Whyburn's standing hypothesis (§II, p. 737): `M` metric, connected, semi-locally-connected. Here
`M` is the whole compact space `X`. -/

section Whyburn

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Jones 1941, Theorem 4 (compact case).** An aposyndetic compact continuum is
semi-locally-connected. (In a compact space "locally peripherally bicompact" holds; also immediate
from `theorem0`.) -/
theorem semiLocConn_of_isAposyndetic (h : IsAposyndetic X) (x : X) : SemiLocConnAt x := by
  sorry

/-- **Whyburn (6.1).** In a semi-locally-connected continuum, each component of `X − x` is open. -/
theorem whyburn_6_1 (h : ∀ z : X, SemiLocConnAt z) (x a : X) (ha : a ≠ x) :
    IsOpen (connectedComponentIn {x}ᶜ a) := by
  sorry

/-- **Whyburn (6.2).** If `x` does not separate `a` and `b` (they lie in one component of
`X − x`), then some continuum contains `a` and `b` and misses `x`. -/
theorem whyburn_6_2 (h : ∀ z : X, SemiLocConnAt z) {x a b : X} (ha : a ≠ x)
    (hb : b ∈ connectedComponentIn {x}ᶜ a) :
    ∃ N : Set X, Fold.Q78.IsContinuum N ∧ a ∈ N ∧ b ∈ N ∧ x ∉ N := by
  sorry

/-- **Whyburn (6.21)**, in the form Jones 1951 uses: in a semi-locally-connected continuum, if `p`
cuts `a` from `b` (every continuum through both contains `p`), then `p` separates `a` from `b`. -/
theorem whyburn_6_21 (h : ∀ z : X, SemiLocConnAt z) {p a b : X} (hc : CutsPts p a b) :
    b ∉ connectedComponentIn {p}ᶜ a := by
  sorry

end Whyburn

/-! ## §4. Jones 1951, Theorem 1 (item C) -/

/-- **Jones 1951, Theorem 1.** A homogeneous hereditarily unicoherent compact metric continuum is
indecomposable. (Nondegenerate: a point is not decomposable in the sense of
`IsDecomposableSpace`; record whether `[Nontrivial X]` is needed.) -/
theorem jones51_theorem1 {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (hX : IsHomogeneous X)
    (hhu : HPC.Plane.IsHereditarilyUnicoherent (univ : Set X)) : ¬ IsDecomposableSpace X := by
  sorry

/-! ## §5. Jones 1955, Theorem 1 (item D)

Notation (p. 736): `L_x` is `x` together with all points `y` such that `M` is not aposyndetic at `y`
with respect to `x`; `U_x = M − L_x` (this is `aposSet x`). -/

section Jones55

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- `L_x`. -/
def Lset (x : X) : Set X := insert x {y | y ≠ x ∧ ¬ AposAt y x}

theorem Lset_compl (x : X) : (Lset x)ᶜ = aposSet x := by
  sorry

/-- **`p` cuts `o` from `S`** (Jones 1955, used from (6) on): every continuum containing `o` and a
point of `S` contains `p`. The convention for `p = o` and for `o ∈ S` is to be read from the text
and recorded; `p ≠ o` is included here. -/
def CutsFrom (p o : X) (S : Set X) : Prop :=
  p ≠ o ∧ ∀ K : Set X, Fold.Q78.IsContinuum K → o ∈ K → (K ∩ S).Nonempty → p ∈ K

/-- The decomposition `G = {L_x}` as a relation. -/
def lRel (x y : X) : Prop := Lset x = Lset y

def lSetoid (X : Type*) [MetricSpace X] [CompactSpace X] [ConnectedSpace X] : Setoid X where
  r := lRel
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Each `L_x` is a continuum (p. 738: "It follows from Theorem 3 of [11] that `N_o` is a
continuum", with `N_o = M − U_o = L_o`). Jones 1948 Theorem 3 gives this for every `x`, with no
homogeneity: `theorem3`. -/
theorem jones55_isContinuum (x : X) : Fold.Q78.IsContinuum (Lset x) := by
  sorry

variable (hX : IsHomogeneous X) (hd : IsDecomposableSpace X)
include hX hd

/-- **Jones 1955, Theorem 1 (b).** The sets `L_x` are mutually exclusive: `y ∈ L_x` iff
`L_y = L_x`. -/
theorem jones55_b {x y : X} : y ∈ Lset x ↔ Lset y = Lset x := by
  sorry

/-- **Jones 1955, Theorem 1 (c).** A subcontinuum meeting `L_x` and its complement contains
`L_x`. -/
theorem jones55_c {x : X} {K : Set X} (hK : Fold.Q78.IsContinuum K) (h1 : (K ∩ Lset x).Nonempty)
    (h2 : (K \ Lset x).Nonempty) : Lset x ⊆ K := by
  sorry

/-- `G` is upper semicontinuous (p. 739). -/
theorem jones55_usc : IsUSCDecomp (lSetoid X) := by
  sorry

/-- `G` is continuous (p. 739, last sentence of the proof: residual continuity + homogeneity). -/
theorem jones55_continuous : IsContinuousDecomp (lSetoid X) := by
  sorry

/-- **Jones 1955, Theorem 1 (a).** "With respect to its elements (as points) `G` is a homogeneous,
aposyndetic, compact, metric continuum", and `G` is nondegenerate. -/
theorem jones55_a :
    CompactSpace (Quotient (lSetoid X)) ∧ ConnectedSpace (Quotient (lSetoid X)) ∧
      TopologicalSpace.MetrizableSpace (Quotient (lSetoid X)) ∧
      Nontrivial (Quotient (lSetoid X)) ∧ IsHomogeneous (Quotient (lSetoid X)) ∧
      IsAposyndeticT (Quotient (lSetoid X)) := by
  sorry

/-- Each element of `G` is homogeneous (p. 739: "So `G` is a collection of mutually exclusive,
homogeneous, nondegenerate continua … and each two elements of `G` are homeomorphic"). Stated in
the degenerate-free case of the proof: `M` not aposyndetic. -/
theorem jones55_elements (hna : ¬ IsAposyndetic X) (x y : X) :
    (Lset x).Nontrivial ∧ Nonempty (Lset x ≃ₜ Lset y) ∧
      ∀ a b : Lset x, ∃ T : Lset x ≃ₜ Lset x, T a = b := by
  sorry

end Jones55

end HPC.Jones
