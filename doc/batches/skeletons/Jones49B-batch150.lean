import HPC.Jones.Jones49A

/-!
# Batch 150 skeleton: Whyburn's cut point-order theorems; Moore 1922 (property S)

Save as `HPC/Jones/Jones49B.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49B` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources (page images, 150–200 dpi):
* Whyburn, *Analytic Topology* (1942), Ch. III §§1–3 and 8–9, pp. 41–62
  (`doc/sources/whyburn1942.pdf`, PDF pp. 55–76). Quoted below:
  * (3.2), pp. 49–50: "CUT POINT-ORDER THEOREM. All save possibly a countable number of the cut
    points of a {connected set / generalized continuum} `M` are of {potential order / order} 2 in
    `M`."
  * (8.4), p. 60: "SEPARATING POINT-ORDER THEOREM. All save a countable number of the separating
    points of any compact metric space `K` are points of order 2 of `K`."
  * (8.41), p. 61: "All save a countable number of the separating points of any locally compact
    separable metric space `L` are points of order 2 of `L`."
  * (9.2), p. 61, as in batch 149.
* R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund. Math. 3 (1922),
  232–237 (`doc/sources/moore1922.pdf`, the scan; `doc/sources/moore1922-transcription.pdf`, my
  typeset transcription with Moore's misprints kept and editorial notes in blue).
-/

namespace HPC.Jones

open Set Topology Metric

/-! ## Whyburn, Ch. III -/

section Whyburn

variable {X : Type*} [MetricSpace X]

/-- **Whyburn (3.2) for continua** (the "generalized continuum … order" reading; Whyburn's
"generalized continuum" is a locally compact connected separable metric space, Ch. I; record it).
Here for compact metric continua, which is what (8.4) uses ("the Cut Point-Order Theorem for
continua, (3.2)"). A *cut point* of `X` is a point whose complement is not connected. -/
theorem whyburn_3_2 [CompactSpace X] [ConnectedSpace X] :
    {p : X | ¬ IsConnected ({p}ᶜ : Set X) ∧ ¬ HasOrder p 2}.Countable := by
  sorry

/-- **Whyburn (8.4).** In a compact metric space, all but countably many separating points (in the
sense of `IsSepPointOf p univ`; compare (8.32)) are of order 2. -/
theorem whyburn_8_4 [CompactSpace X] :
    {p : X | IsSepPointOf p univ ∧ ¬ HasOrder p 2}.Countable := by
  sorry

/-- **Whyburn (8.41).** The same for a locally compact separable metric space. -/
theorem whyburn_8_41 [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X] :
    {p : X | IsSepPointOf p univ ∧ ¬ HasOrder p 2}.Countable := by
  sorry

/-- **Whyburn (9.2)** — the statement left open in batch 149 (`OPEN.md`), restated verbatim. -/
theorem whyburn_9_2 [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X] :
    {p : X | IsLocalSepPoint p ∧ ¬ HasOrder p 2}.Countable := by
  sorry

/-- **What Jones 1949 uses** — left open in batch 149, restated verbatim. -/
theorem jones49_some_order_two [CompactSpace X] [ConnectedSpace X] [Uncountable X]
    (hX : IsHomogeneous X) {p : X} (hp : IsLocalSepPoint p) : ∃ q : X, HasOrder q 2 := by
  sorry

end Whyburn

/-! ## Moore 1922 -/

section Moore22

open HPC.Plane

/-- **Property S** (Moore 1922, p. 232): "for every positive number `ε`, `M` is the sum of a finite
number of connected point-sets … each of diameter less than `ε`". Connected in Moore's sense
(footnote 2) admits the empty set; bounded is part of "diameter less than `ε`". -/
def PropertyS (M : Set Pt) : Prop :=
  ∀ ε > 0, ∃ s : Finset (Set Pt), (∀ A ∈ s, IsPreconnected A ∧ Bornology.IsBounded A ∧ diam A < ε) ∧
    M = ⋃ A ∈ s, A

/-- *Connected im kleinen at `P`* (p. 233): for every `ε` there is `δ` such that each point `X` of
`M` within `δ` of `P` lies with `P` in a connected subset of `M` of diameter less than `ε`. -/
def CikAt (M : Set Pt) (P : Pt) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ X ∈ M, dist X P < δ → ∃ C ⊆ M, IsPreconnected C ∧ X ∈ C ∧ P ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε

/-- *Uniformly connected im kleinen* (p. 233). -/
def UniformlyCik (M : Set Pt) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ X ∈ M, ∀ Y ∈ M, dist X Y < δ → ∃ C ⊆ M, IsPreconnected C ∧ X ∈ C ∧ Y ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε

/-- Moore's *simply connected* bounded domain (p. 235, footnote 2): "`R` contains the whole of every
bounded point-set whose boundary is a subset of `R`". -/
def MooreSimplyConnected (R : Set Pt) : Prop :=
  ∀ H : Set Pt, Bornology.IsBounded H → frontier H ⊆ R → H ⊆ R

/-- **Theorem 1** (p. 233). If `M` is uniformly connected im kleinen, then `M′` (the closure) is
connected im kleinen. -/
theorem moore22_theorem1 {M : Set Pt} (h : UniformlyCik M) : ∀ P ∈ closure M, CikAt (closure M) P := by
  sorry

/-- **Theorem 2** (p. 233). Every point-set with property S is connected im kleinen. -/
theorem moore22_theorem2 {M : Set Pt} (h : PropertyS M) : ∀ P ∈ M, CikAt M P := by
  sorry

/-- **Theorem 3** (p. 234). A bounded point-set uniformly connected im kleinen has property S. -/
theorem moore22_theorem3 {M : Set Pt} (hb : Bornology.IsBounded M) (h : UniformlyCik M) :
    PropertyS M := by
  sorry

/-- **Theorem 4** (p. 235). A simply connected bounded domain `R` has a continuous curve (a locally
connected continuum) as its boundary iff `R` has property S. -/
theorem moore22_theorem4 {R : Set Pt} (hR : IsOpen R) (hRc : IsConnected R)
    (hRb : Bornology.IsBounded R) (hsc : MooreSimplyConnected R) :
    PropertyS R ↔ (IsConnected (frontier R) ∧ LocallyConnectedSpace (frontier R)) := by
  sorry

end Moore22

end HPC.Jones
