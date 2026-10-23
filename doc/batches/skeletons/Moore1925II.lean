import HPC.Moore.M25A

/-!
# Batch 146 skeleton: Moore 1925 §I, part 2 (Theorems 5–12; Mullikin 1922 Theorem 5)

Save as `HPC/Moore/M25B.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.M25B`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change recorded
at the statement and in the report.

Sources: Moore, Trans. AMS 27 (1925), pp. 417, 420–422 (`doc/sources/moore1925.pdf`); A. M. Mullikin,
*Certain theorems relating to plane connected point sets*, Trans. AMS 24 (1922), 144–162, Theorems 4
and 5, pp. 154, 160 (`mullikin1922.pdf`, new). Transcribed from page images at 200 dpi.

**Modelling.** As in batch 145: elements are points of `Quotient r`, Moore's notions are taken in the
quotient topology (`isLimitElt_iff`, `m25_domain_iff`, `m25_boundary_iff`). "Disconnected by the
omission of `x`" is `¬ IsConnected (H \ {x})`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

/-- Moore's *simple continuous arc* from `A` to `B` (p. 417): "If `A` and `B` are two distinct
elements of `G`, and `H` is a closed, connected and bounded set of elements of `G`, and `A` and `B`
belong to `H`, and `H` is disconnected by the omission of any one of its elements except `A` and `B`,
then `H` is said to be a simple continuous arc (of elements of `G`) from `A` to `B`". -/
def IsArcElt (A B : Quotient r) (H : Set (Quotient r)) : Prop :=
  A ≠ B ∧ IsClosed H ∧ IsConnected H ∧ Bornology.IsBounded (ptsOf r H) ∧ A ∈ H ∧ B ∈ H ∧
    ∀ x ∈ H, x ≠ A → x ≠ B → ¬ IsConnected (H \ {x})

/-- Moore's *simple closed curve*, **as printed** (p. 417): "A bounded subset `H` of the set `G` is
said to be a simple closed curve (of elements of `G`) provided it is disconnected by the omission of
any two of its elements." Neither closedness nor connectedness is required. -/
def IsSCCEltPrinted (J : Set (Quotient r)) : Prop :=
  Bornology.IsBounded (ptsOf r J) ∧ ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ¬ IsConnected (J \ {x, y})

/-- The simple closed curve, **corrected**: a bounded continuum of elements with more than one
element, disconnected by the omission of any two of its elements. -/
def IsSCCElt (J : Set (Quotient r)) : Prop :=
  IsClosed J ∧ IsConnected J ∧ J.Nontrivial ∧ IsSCCEltPrinted J

/-- Moore's *complementary domain*, **as printed** (p. 417): "A domain of elements of `G` is said to
be a complementary domain of a closed set `H` of elements of `G` provided the boundary of `D` is a
subset of `H`." -/
def IsComplDomPrinted (H D : Set (Quotient r)) : Prop :=
  IsOpen D ∧ IsConnected D ∧ frontier D ⊆ H

/-! ## Two refutations deferred from batch 145 -/

/-- **Theorem 2 under the printed definitions is false** (REPORT-batch145, ledger entry 4: the
decomposition into points, `M` a closed disc, `D` the open disc minus a radius, `E` the plane minus
that radius). Here "the outer boundary" is read literally: the boundary of any unbounded
complementary domain, in the printed sense, of the boundary of `D`. -/
theorem not_m25_theorem2_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ M D E : Set (Quotient r), IsClosed M → IsConnected M → Bornology.IsBounded (ptsOf r M) →
        IsComplDomPrinted M D → Bornology.IsBounded (ptsOf r D) →
        IsComplDomPrinted (frontier D) E → ¬ Bornology.IsBounded (ptsOf r E) →
        ∀ p ∈ frontier E, IsConnected (frontier E) ∧ IsConnected (frontier E \ {p}) := by
  sorry

/-- **Theorem 10 under the printed definition of simple closed curve is false**: in the
decomposition into points, two disjoint segments form a bounded set disconnected by the omission of
any two of its elements, and it is not the union of two arcs. -/
theorem not_m25_theorem10_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ J : Set (Quotient r), IsSCCEltPrinted J → ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        ∃ a b, IsArcElt p q a ∧ IsArcElt p q b ∧ a ∪ b = J ∧ a ∩ b = {p, q} := by
  sorry

/-- **Theorem 11 under the printed definition is false** (same example: the complement of two
disjoint segments is connected). -/
theorem not_m25_theorem11_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ J : Set (Quotient r), IsSCCEltPrinted J → J.Nonempty →
        ∃ I E : Set (Quotient r), IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧
          Disjoint I E ∧ I ∪ E = Jᶜ := by
  sorry

/-! ## Mullikin 1922 -/

/-- **Mullikin 1922, Theorem 5, as printed** (p. 160): "If `M₁` and `M₂` are two closed, bounded,
connected point sets in a plane `S`, such that neither `M₁` nor `M₂` disconnects `S` and such that
`M₁` and `M₂` have in common only `K₁` and `K₂`, where `K₁` and `K₂` are mutually exclusive connected
sets, then `S − M₁ − M₂` is the sum of just two mutually exclusive, connected domains." Candidate
counterexample: `M₁ = M₂` a segment, `K₁` a half-open half of it, `K₂` the other (closed) half. Prove
the negation, or record why the printed statement is true. -/
theorem not_mullikin_theorem5_printed :
    ¬ ∀ M₁ M₂ K₁ K₂ : Set Pt, IsCompact M₁ → IsConnected M₁ → IsCompact M₂ → IsConnected M₂ →
      ¬ SeparatesPlane M₁ → ¬ SeparatesPlane M₂ → M₁ ∩ M₂ = K₁ ∪ K₂ → IsConnected K₁ →
      IsConnected K₂ → Disjoint K₁ K₂ →
      ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
        U ∪ V = (M₁ ∪ M₂)ᶜ := by
  sorry

/-- **Mullikin 1922, Theorem 5, corrected** (`K₁`, `K₂` closed). This is the form Moore uses in
Theorem 11, with `K₁ = p̄`, `K₂ = q̄`. -/
theorem mullikin_theorem5 {M₁ M₂ K₁ K₂ : Set Pt} (hM₁ : IsCompact M₁) (hM₁c : IsConnected M₁)
    (hM₂ : IsCompact M₂) (hM₂c : IsConnected M₂) (hs₁ : ¬ SeparatesPlane M₁)
    (hs₂ : ¬ SeparatesPlane M₂) (hK : M₁ ∩ M₂ = K₁ ∪ K₂) (hK₁ : IsClosed K₁) (hK₁c : IsConnected K₁)
    (hK₂ : IsClosed K₂) (hK₂c : IsConnected K₂) (hd : Disjoint K₁ K₂) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (M₁ ∪ M₂)ᶜ := by
  sorry

section M25B

variable (hG : MooreDecomp r)
include hG

/-- Sets of elements and their point sets: if `H` does not separate `G`, then `H̄` does not separate
`S` (used in Theorems 11 and 13: "neither `a` nor `b` separates `G` and therefore neither `ā` nor `b̄`
separates `S`"). -/
theorem not_separatesPlane_ptsOf {H : Set (Quotient r)} (hH : IsConnected Hᶜ) :
    ¬ SeparatesPlane (ptsOf r H) := by
  sorry

/-- **Theorem 5** (p. 420). No simple continuous arc of elements is disconnected by the omission of
either of its extremities. (No proof in the text; "for an indication of material sufficient for a
proof … see page 139 of F. A. and page 342 of" Moore 1920.) -/
theorem m25_theorem5 {A B : Quotient r} {H : Set (Quotient r)} (h : IsArcElt A B H) :
    IsConnected (H \ {A}) ∧ IsConnected (H \ {B}) := by
  sorry

/-- **Theorem 6** (p. 420). Every closed and connected subset of a simple continuous arc which
contains more than one element is itself a simple continuous arc. (No proof in the text.) -/
theorem m25_theorem6 {A B : Quotient r} {K L : Set (Quotient r)} (hK : IsArcElt A B K)
    (hLK : L ⊆ K) (hL : IsClosed L) (hLc : IsConnected L) (hLn : L.Nontrivial) :
    ∃ a b, IsArcElt a b L := by
  sorry

/-- **Theorem 7** (p. 420), **with `x` for the printed `p`** in "then `p` is a limit element of the
set `H`". If `pq` is an arc from `p` to `q`, `x ∈ pq` distinct from `p`, `q`, and `H ⊆ pq`, then `x`
is a limit element of `H` iff every arc contained in `pq`, containing `x` but not having `x` as an
extremity, contains an element of `H` other than `x`. (No proof in the text.) -/
theorem m25_theorem7 {p q x : Quotient r} {K H : Set (Quotient r)} (hK : IsArcElt p q K)
    (hx : x ∈ K) (hxp : x ≠ p) (hxq : x ≠ q) (hHK : H ⊆ K) :
    AccPt x (Filter.principal H) ↔
      ∀ a b L, IsArcElt a b L → L ⊆ K → x ∈ L → x ≠ a → x ≠ b → ∃ h ∈ H ∩ L, h ≠ x := by
  sorry

/-- **Theorem 7 as printed** ("then `p` is a limit element of the set `H`"): record whether it is
false (expected: yes, `p` an extremity and `H` clustering only at `x`). Optional. -/
theorem not_m25_theorem7_printed : True := by
  sorry

/-- **Theorem 8** (pp. 420–421). If `K` is a closed, connected and bounded set of elements and `H` a
connected proper subset of `K`, then `K − H` contains an element whose omission does not disconnect
`K`. -/
theorem m25_theorem8 {K H : Set (Quotient r)} (hK : IsClosed K) (hKc : IsConnected K)
    (hKb : Bornology.IsBounded (ptsOf r K)) (hHK : H ⊆ K) (hHc : IsConnected H) (hne : H ≠ K) :
    ∃ x ∈ K \ H, IsConnected (K \ {x}) := by
  sorry

/-- **Theorem 9** (p. 421). If `pq` is a simple continuous arc of elements, then `G − pq` is
connected. ("With the help of Theorems 2 and 6 the following theorem may be established by an
argument largely similar to that used in the proof of Lemma 8 of" P.C.S.) -/
theorem m25_theorem9 {p q : Quotient r} {K : Set (Quotient r)} (hK : IsArcElt p q K) :
    IsConnected Kᶜ := by
  sorry

/-- **Theorem 10** (p. 421), for the corrected simple closed curve. ("In view of results established
above Theorem 10 is a consequence of Theorem 4 of" Moore 1920.) -/
theorem m25_theorem10 {J : Set (Quotient r)} (hJ : IsSCCElt J) {p q : Quotient r} (hp : p ∈ J)
    (hq : q ∈ J) (hpq : p ≠ q) :
    ∃ a b, IsArcElt p q a ∧ IsArcElt p q b ∧ a ∪ b = J ∧ a ∩ b = {p, q} := by
  sorry

/-- **Theorem 11** (pp. 421–422), for the corrected simple closed curve: `G − J` is the sum of two
domains, only one of which is bounded, and `J` is the boundary of each. -/
theorem m25_theorem11 {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    ∃ I E : Set (Quotient r), IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧
      Disjoint I E ∧ I ∪ E = Jᶜ ∧ Bornology.IsBounded (ptsOf r I) ∧
      ¬ Bornology.IsBounded (ptsOf r E) ∧ frontier I = J ∧ frontier E = J := by
  sorry

/-- **Theorem 12** (p. 422). If `D₁` and `D₂` are bounded domains of elements, `D₁` has a connected
boundary, and the boundary of `D₂` is a subset of `D₁`, then `D₂ ⊆ D₁`. -/
theorem m25_theorem12 {D₁ D₂ : Set (Quotient r)} (h₁ : IsOpen D₁ ∧ IsConnected D₁)
    (h₂ : IsOpen D₂ ∧ IsConnected D₂) (hb₁ : Bornology.IsBounded (ptsOf r D₁))
    (hb₂ : Bornology.IsBounded (ptsOf r D₂)) (hB₁ : IsConnected (frontier D₁))
    (hB₂ : frontier D₂ ⊆ D₁) : D₂ ⊆ D₁ := by
  sorry

end M25B

end HPC.Moore
