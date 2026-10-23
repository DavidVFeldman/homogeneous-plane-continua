import HPC.Jones.Jones49E

/-!
# Batch 154 skeleton: Jones 1949, Theorems 1 and 2; Jones 1955 Theorem 2 unconditional

Save as `HPC/Jones/Jones49F.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49F` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Source: F. B. Jones, *Note on homogeneous plane continua*, Bull. AMS 55 (1949), 113–114
(`doc/sources/jones1949.pdf`), read from page images at 200 dpi.

Proof of Theorem 1 (p. 113–114), quoted in the docstrings below. "If a point of `M` is of order 2 in
`M`, then `M` is a simple closed curve [4]. So suppose that *no* point of `M` is of order 2 in `M`.
Let `G` denote the collection of all the complementary domains of `M`. Because `M` is homogeneous
and contains a non-separating point, no point of `M` separates `M`. Since `M` is aposyndetic, `M` is
semi-locally-connected [5]. Hence each element of `G` is a simple domain [6, 7]. Let the simple closed
curve `J` denote the boundary of an element `D` of `G`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane HPC.Moore.Gen

section Setting

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **The setting** (p. 113): a nondegenerate homogeneous aposyndetic compact plane continuum is
cyclic ("no point of `M` separates `M`") and semi-locally connected ("[5]", Jones 1941 Theorem 4). -/
theorem jones49_setting [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M) :
    (∀ z : M, IsConnected ({z}ᶜ : Set M)) ∧ (∀ z : M, SemiLocConnAt z) := by
  sorry

/-- **"Hence each element of `G` is a simple domain [6, 7]"** (p. 113), from Whyburn 1939
Corollary 1. -/
theorem jones49_simple_domains [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M)
    {x : Pt} (hx : x ∉ M) : Nonempty (frontier (connectedComponentIn Mᶜ x) ≃ₜ Circle) := by
  sorry

/-- **Case 1** (p. 113). "If `M − J` is connected, then each point of `M` belongs to some such
simple closed curve lying in `M`. Consequently each point of `M` belongs to the boundary of an
element of `G`. But `G` is countable. Hence `M = ΣJᵢ` …, such that for each `i`, `Jᵢ` is the boundary
of an element of `G`. Since no point of `M` is of order 2 in `M`, each point of `Jᵢ` is a limit point
of `M − Jᵢ`. This contradicts a well known theorem (Baire)." -/
theorem jones49_case1 [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M)
    (hno : ∀ q : M, ¬ HasOrder q 2) {x : Pt} (hx : x ∉ M)
    (h1 : IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    False := by
  sorry

/-- **Case 2** (p. 114). "If `M − J` is not connected, then `M − J = H + K` such that
`H·K̄ = H̄·K = 0`. There exists an arc `T` lying in the complement of `D̄` which is irreducible from
`H` to `K`. Except for its end points, `T` lies in an element `U` of `G`. Let `C` denote the boundary
of `U` and let the point `x` of `C` be one of the end points of `T`. The component `AxB` of `C − C·J`
which contains `x` is an arc-segment whose end points lie on `J`. It follows that `M − (A + B)` is
*not* connected, but `M − B` *is* connected. Hence `A` is a local separating point of `M`."
Conclusion as Jones uses it: `M` has a local separating point. -/
theorem jones49_case2 [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M) {x : Pt}
    (hx : x ∉ M)
    (h2 : ¬ IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    ∃ A : M, IsLocalSepPoint A := by
  sorry

end Setting

/-- **Jones 1949, Theorem 1** (corrected: nondegenerate). "If a compact, plane continuum `M` is both
homogeneous and aposyndetic, then `M` is a simple closed curve." -/
theorem jones49_theorem1 : Jones49Thm1 := by
  sorry

/-- **Jones 1949, Theorem 2** (p. 114). "If a homogeneous, compact, plane continuum `M` contains no
weak cut point, it is a simple closed curve." Proof: "If `M` contains no weak cut point, it is
aposyndetic at some point [9] (Jones 1948, Theorem 18). Being aposyndetic at one point, `M` must be
aposyndetic at each of its points. Hence Theorem 2 follows from Theorem 1." Record the degenerate
case (a point has no weak cut point). -/
theorem jones49_theorem2 (K : Set Pt) (hK : IsCompact K) (hKc : IsConnected K) (hn : K.Nontrivial)
    (hX : IsHomogeneous K) (hw : ∀ p : K, ¬ IsWeakCutPoint p) : Nonempty (K ≃ₜ Circle) := by
  sorry

/-! ## Jones 1955 Theorem 2 and the closing remarks, unconditional -/

section Jones55

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Jones 1955, Theorem 2**, with `h49` discharged. -/
theorem jones55_theorem2' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    IsContinuousDecomp (lSetoid M) ∧ Nonempty (Quotient (lSetoid M) ≃ₜ Circle) ∧
      ∀ x : M, IsConnected (Lset x) ∧ IsHomogeneous (Lset x) ∧
        ¬ SeparatesPlane (Subtype.val '' Lset x) := by
  sorry

theorem jones55_two_domains' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = Mᶜ := by
  sorry

theorem jones55_elements_indecomposable' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M)
    (x : M) : ¬ IsDecomposableSpace (Lset x) := by
  sorry

theorem jones55_three_domains' (hX : IsHomogeneous M) {a b c : Pt} (ha : a ∉ M) (hb : b ∉ M)
    (hc : c ∉ M) (hab : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ b)
    (hac : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ c)
    (hbc : connectedComponentIn Mᶜ b ≠ connectedComponentIn Mᶜ c) :
    ¬ IsDecomposableSpace M := by
  sorry

end Jones55

end HPC.Jones
