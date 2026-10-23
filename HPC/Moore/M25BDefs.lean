import HPC.Moore.M25A
import HPC.Moore.CutArc

/-!
# Batch 146: Moore 1925 §I, part 2 — definitions (verbatim from the skeleton)

The skeleton is kept as `doc/batches/skeletons/Moore1925II.lean`; its four definitions are copied
here unchanged. Its theorems are proved in `M25BPts.lean` (the refutations, with the decomposition
into points), `Mullikin.lean`, `M25B5.lean` (Theorems 5–8), `M25B9.lean` (Theorems 9, 10, 12) and
`M25B11.lean` (Theorem 11), collected in `M25B.lean`.

Sources: Moore, Trans. AMS 27 (1925), pp. 417, 420–422 (`doc/sources/moore1925.pdf`); A. M. Mullikin,
Trans. AMS 24 (1922), 144–162 (`doc/sources/mullikin1922.pdf`); Moore, Trans. AMS 21 (1920),
333–347 (`doc/sources/moore1920.pdf`); Moore, PNAS 10 (1924), 170–175
(`doc/sources/moore1924-pcs.pdf`).

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

/-- A simple continuous arc of elements is a cut-point arc in the sense of `CutArc.lean`. -/
theorem IsArcElt.isCutArc {A B : Quotient r} {H : Set (Quotient r)} (h : IsArcElt A B H) :
    IsCutArc A B H := by
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hc : IsCompact (ptsOf r H) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 h.2.1) h.2.2.2.1
  rw [← image_ptsOf H]
  exact hc.image continuous_mk

/-- A closed set of elements with bounded point set is compact. -/
theorem isCompact_of_isClosed_bounded {H : Set (Quotient r)} (hH : IsClosed H)
    (hb : Bornology.IsBounded (ptsOf r H)) : IsCompact H := by
  rw [← image_ptsOf H]
  exact (Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hH) hb).image continuous_mk

/-- A cut-point arc which is closed and has bounded point set is a simple continuous arc of
elements. -/
theorem IsCutArc.isArcElt {A B : Quotient r} {H : Set (Quotient r)} (h : IsCutArc A B H)
    (hH : IsClosed H) (hb : Bornology.IsBounded (ptsOf r H)) : IsArcElt A B H :=
  ⟨h.1, hH, h.2.2.1, hb, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end HPC.Moore
