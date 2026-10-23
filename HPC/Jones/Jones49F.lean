import HPC.Jones.Jones49FCase1
import HPC.Jones.Jones49FCase2

/-!
# Batch 154 skeleton: Jones 1949, Theorems 1 and 2; Jones 1955 Theorem 2 unconditional

From the batch-154 skeleton (`doc/batches/skeletons/Jones49F.lean`). All items are proved; every
statement is verbatim. The proofs are in `Jones49FTheta.lean` (the θ-curve lemmas, including the
separation of `M − (A + B)`), `Jones49FLocal.lean` (local separating points), `Jones49FCase1.lean`
and `Jones49FCase2.lean`.

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
cyclic ("no point of `M` separates `M`") and semi-locally connected ("[5]", Jones 1941 Theorem 4).
*Proof:* a nondegenerate continuum has a non-cut point (`exists_two_nonCutPoints`), and a
homeomorphism of `M` carries it to any point; `semiLocConn_of_isAposyndetic`. -/
theorem jones49_setting [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M) :
    (∀ z : M, IsConnected ({z}ᶜ : Set M)) ∧ (∀ z : M, SemiLocConnAt z) := by
  refine ⟨fun z => ?_, fun z => semiLocConn_of_isAposyndetic ha z⟩
  obtain ⟨u, -, -, hu, -⟩ := exists_two_nonCutPoints (X := M)
  have hu' : IsConnected ({u}ᶜ : Set M) := not_not.mp hu
  obtain ⟨h, rfl⟩ := hX u z
  rw [← image_singleton, ← Set.image_compl_eq h.bijective]
  exact hu'.image _ h.continuous.continuousOn

/-- **"Hence each element of `G` is a simple domain [6, 7]"** (p. 113), from Whyburn 1939
Corollary 1 (`whyburn39_corollary1`, with `jones49_setting`). -/
theorem jones49_simple_domains [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M)
    {x : Pt} (hx : x ∉ M) : Nonempty (frontier (connectedComponentIn Mᶜ x) ≃ₜ Circle) := by
  obtain ⟨hcyc, hS⟩ := jones49_setting hX ha
  exact whyburn39_corollary1 (isCompact_iff_compactSpace.mpr ‹_›)
    (isConnected_iff_connectedSpace.mpr ‹_›) hS hcyc hx

/-- **Case 1** (p. 113). "If `M − J` is connected, then each point of `M` belongs to some such
simple closed curve lying in `M`. Consequently each point of `M` belongs to the boundary of an
element of `G`. But `G` is countable. Hence `M = ΣJᵢ` …, such that for each `i`, `Jᵢ` is the boundary
of an element of `G`. Since no point of `M` is of order 2 in `M`, each point of `Jᵢ` is a limit point
of `M − Jᵢ`. This contradicts a well known theorem (Baire)."

*Proof* (`jones49_case1_core`, `HPC/Jones/Jones49FCase1.lean`). Step 1: a homeomorphism `h` of `M`
carries a point of `J` to a given `p`; `J' = h(J)` is a simple closed curve with `M − J'` connected.
Step 2 (the gap): `M − J'` lies on one side of `J'` (`jordan_side`); the other side misses `M`, is
connected and has frontier `J' ⊆ M`, hence is an element of `G` with boundary `J'`
(`frontier_cc_of_jordan`). Step 3: `G` is countable (`countable_complDomains`). Step 4: Baire
(`nonempty_interior_of_iUnion_of_closed`) gives an element whose boundary `Jᵢ` contains a nonempty
open set `W` of `M`. Step 5: a point of `W` separates the open set `W − q` (`q ∈ Jᵢ`), so it is a
local separating point (`isLocalSepPoint_of_open_sub_tscc`), and some point of `M` has order 2
(`jones49_some_order_two`), against `hno`. Jones's "each point of `Jᵢ` is a limit point of
`M − Jᵢ`" is replaced by this: the order-2 point is obtained through Whyburn (9.2) rather than at the
point of `W` itself. -/
theorem jones49_case1 [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M)
    (hno : ∀ q : M, ¬ HasOrder q 2) {x : Pt} (hx : x ∉ M)
    (h1 : IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    False := by
  obtain ⟨hcyc, hS⟩ := jones49_setting hX ha
  exact jones49_case1_core hX hS hcyc hno hx h1

/-- **Case 2** (p. 114). "If `M − J` is not connected, then `M − J = H + K` such that
`H·K̄ = H̄·K = 0`. There exists an arc `T` lying in the complement of `D̄` which is irreducible from
`H` to `K`. Except for its end points, `T` lies in an element `U` of `G`. Let `C` denote the boundary
of `U` and let the point `x` of `C` be one of the end points of `T`. The component `AxB` of `C − C·J`
which contains `x` is an arc-segment whose end points lie on `J`. It follows that `M − (A + B)` is
*not* connected, but `M − B` *is* connected. Hence `A` is a local separating point of `M`."
Conclusion as Jones uses it: `M` has a local separating point.

*Proof* (`jones49_case2_core`, `HPC/Jones/Jones49FCase2.lean`; homogeneity is used only through
`jones49_setting`). If `M = J` every point is a local separating point. Otherwise `M − J = H + K`.
Step 1: an arc in the side of `J` containing `M − J`, trimmed at its last point `x` on `H̄` and the
next point `y` on `K̄`, has its interior in `Mᶜ` (`exists_domain_meeting`). Step 2: the component
`U` of `Mᶜ` containing that interior has `x ∈ H`, `y ∈ K` on its boundary `C`, a simple closed curve.
Step 3: each arc of `C` from `x` to `y` meets `J` (`H`, `K` separated). Step 4: the first points
`A`, `B` of `J` on the two arcs of `C` from `x` give `C = AxB + L'` (`exists_theta_arcs`). Step 5:
`M − (A + B)` is the union of two separated nonempty sets (`theta_separation`; see there for the
point raised in the commission). Steps 6–7: `M − B` is connected, so `A` separates it
(`isLocalSepPoint_of_separation`). -/
theorem jones49_case2 [Nontrivial M] (hX : IsHomogeneous M) (ha : IsAposyndetic M) {x : Pt}
    (hx : x ∉ M)
    (h2 : ¬ IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    ∃ A : M, IsLocalSepPoint A := by
  obtain ⟨hcyc, hS⟩ := jones49_setting hX ha
  exact jones49_case2_core hS hcyc hx h2

end Setting

/-- **Jones 1949, Theorem 1** (corrected: nondegenerate). "If a compact, plane continuum `M` is both
homogeneous and aposyndetic, then `M` is a simple closed curve."

*Proof.* If some point has order 2, `jones49_order_two`. Otherwise take `x ∉ M` (the plane is not
compact) and `J` the boundary of its complementary domain: Case 1 is contradictory and Case 2 gives a
local separating point, hence (`M` uncountable, `uncountable_of_nontrivial`) a point of order 2 by
`jones49_some_order_two`. -/
theorem jones49_theorem1 : Jones49Thm1 := by
  intro K hK hKc hKn hX ha
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKc
  haveI : Nontrivial K := Set.nontrivial_coe_sort.mpr hKn
  by_cases hord : ∃ q : K, HasOrder q 2
  · obtain ⟨q, hq⟩ := hord
    exact jones49_order_two hX hq
  push_neg at hord
  obtain ⟨x, hx⟩ : ∃ x : Pt, x ∉ K := by
    by_contra h
    push_neg at h
    exact noncompact_univ Pt (by rwa [eq_univ_of_forall h] at hK)
  by_cases h1 : IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Kᶜ x))ᶜ : Set K)
  · exact (jones49_case1 hX ha hord hx h1).elim
  · obtain ⟨A, hA⟩ := jones49_case2 hX ha hx h1
    haveI := uncountable_of_nontrivial (M := K)
    obtain ⟨q, hq⟩ := jones49_some_order_two hX hA
    exact (hord q hq).elim

/-- **Jones 1949, Theorem 2** (p. 114). "If a homogeneous, compact, plane continuum `M` contains no
weak cut point, it is a simple closed curve." Proof: "If `M` contains no weak cut point, it is
aposyndetic at some point [9] (Jones 1948, Theorem 18). Being aposyndetic at one point, `M` must be
aposyndetic at each of its points. Hence Theorem 2 follows from Theorem 1."

*Proof.* `theorem18` gives a dense, hence nonempty, set of points at which `M` is aposyndetic;
homogeneity (`aposAt_homeomorph_iff`) spreads aposyndesis to every point, and `jones49_theorem1`
applies. The degenerate case is `not_jones49_theorem2_point`. -/
theorem jones49_theorem2 (K : Set Pt) (hK : IsCompact K) (hKc : IsConnected K) (hn : K.Nontrivial)
    (hX : IsHomogeneous K) (hw : ∀ p : K, ¬ IsWeakCutPoint p) : Nonempty (K ≃ₜ Circle) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKc
  obtain ⟨-, hd⟩ := theorem18 (X := K) hw
  obtain ⟨x₀, hx₀, -⟩ := hd.nonempty
  have hap : IsAposyndetic K := by
    intro x y hxy
    obtain ⟨h, rfl⟩ := hX x₀ x
    have hne : h.symm y ≠ x₀ := fun e => hxy (by rw [← e, Homeomorph.apply_symm_apply])
    rw [← h.apply_symm_apply y]
    exact (aposAt_homeomorph_iff h).mpr (hx₀ _ hne)
  exact jones49_theorem1 K hK hKc hn hX hap

/-- **The degenerate case of Theorem 2.** A one-point continuum is homogeneous and has no weak cut
point (`CutsPts` needs two distinct points other than the cut point), but is not a simple closed
curve: the printed Theorem 2, like Theorem 1 (`not_jones49_theorem1_point`), needs `M`
nondegenerate. -/
theorem not_jones49_theorem2_point :
    ¬ ∀ K : Set Pt, IsCompact K → IsConnected K → IsHomogeneous K →
      (∀ p : K, ¬ IsWeakCutPoint p) → Nonempty (K ≃ₜ Circle) := by
  intro h
  obtain ⟨e⟩ := h {0} isCompact_singleton isConnected_singleton isHomogeneous_of_subsingleton
    fun _ ⟨x, y, hc⟩ => hc.2.2.1 (Subsingleton.elim x y)
  exact not_homeomorph_circle_of_subsingleton e

/-! ## Jones 1955 Theorem 2 and the closing remarks, unconditional -/

section Jones55

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Jones 1955, Theorem 2**, with `h49` discharged. -/
theorem jones55_theorem2' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    IsContinuousDecomp (lSetoid M) ∧ Nonempty (Quotient (lSetoid M) ≃ₜ Circle) ∧
      ∀ x : M, IsConnected (Lset x) ∧ IsHomogeneous (Lset x) ∧
        ¬ SeparatesPlane (Subtype.val '' Lset x) :=
  jones55_theorem2 jones49_theorem1 hX hd

theorem jones55_two_domains' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = Mᶜ :=
  jones55_two_domains jones49_theorem1 hX hd

theorem jones55_elements_indecomposable' (hX : IsHomogeneous M) (hd : IsDecomposableSpace M)
    (x : M) : ¬ IsDecomposableSpace (Lset x) :=
  jones55_elements_indecomposable jones49_theorem1 hX hd x

theorem jones55_three_domains' (hX : IsHomogeneous M) {a b c : Pt} (ha : a ∉ M) (hb : b ∉ M)
    (hc : c ∉ M) (hab : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ b)
    (hac : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ c)
    (hbc : connectedComponentIn Mᶜ b ≠ connectedComponentIn Mᶜ c) :
    ¬ IsDecomposableSpace M :=
  jones55_three_domains jones49_theorem1 hX ha hb hc hab hac hbc

end Jones55

end HPC.Jones
