import HPC.Moore.Sec6Arc

/-!
# Moore, F.A. (1916), §6: conventions (batch 138, item A)

Verbatim from the batch-138 skeleton (`doc/batches/skeletons/MooreFA6.lean`, header and §1),
transcribed from the page images of pp. 140–150. No definition has been changed.

**Moore's conventions in §6** (implemented by the definitions below):
* "closed curve" means simple closed curve (footnote p. 141);
* `AXB` with a bar beneath means the arc minus its endpoints (footnote p. 141): `openArc`;
* "the interior of `J`": **never defined in F.A.** It is used from the proof of Theorem 23 on.
  The intended meaning is the region whose boundary is `J`. It exists by Axiom 8 and is unique
  by Theorem 21 (`existsUnique_interior`, an unnumbered gap). Here it is `IsInteriorOf J R`;
* "within `J`" means in the interior; "without `J`" means in the exterior of the interior;
* "`ACB`" is the arc from `A` to `B` through `C`; "`AXBCA`" is the closed curve formed by `AXB`
  and `ACB`;
* "`A` and `B` separate `C` and `D` on `J`" (p. 140): `SeparatesOn`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} (σ : Space S)

/-- The arc minus its endpoints (Moore's underlined `AXB`). It does not depend on the regions. -/
def openArc (A B : S) (C : Set S) : Set S := C \ {A, B}

namespace Space

/-- `R` is *the interior of* the closed curve `J`: a region with boundary `J`. -/
def IsInteriorOf (J R : Set S) : Prop := σ.IsSCC J ∧ R ∈ σ.region ∧ σ.bdry R = J

/-- `A`, `B` separate `C`, `D` on `J`, witnessed by the two arcs `C₁ = ACB` and `C₂ = ADB`. -/
def SeparatesOn (J : Set S) (A B C D : S) (C₁ C₂ : Set S) : Prop :=
  σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧
    C ∈ openArc A B C₁ ∧ D ∈ openArc A B C₂

/-- Points of the arc `K` (from `K₀` to `K₁`) in a given order: `pts` is the image of an increasing
list of parameters under a parametrization `f` with `f 0 = K₀`, `f 1 = K₁`. -/
def InOrder (K : Set S) (K₀ K₁ : S) (pts : List S) : Prop :=
  ∃ f : unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = K ∧ f 0 = K₀ ∧ f 1 = K₁ ∧
    ∃ ts : List unitInterval, ts.Pairwise (· < ·) ∧ pts = ts.map f

end Space

end HPC.Moore
