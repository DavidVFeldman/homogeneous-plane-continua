import HPC.Moore.FA7

/-!
# Moore 1919: definitions from the footnotes (batch 140)

Verbatim from the batch-140 skeleton (`doc/batches/skeletons/Moore1919AB.lean`).

Source: R. L. Moore, *Concerning a set of postulates for plane analysis situs*, Trans. AMS 20
(1919), 169–178 (`doc/sources/moore1919.pdf`).

* p. 170, †: "If `X` and `Y` are two points of a closed curve `J`, there are just two arcs that lie
  wholly on `J` and have [`X` and `Y`] as endpoints. Each of these arcs is called an *interval* of
  `J`. An interval minus its endpoints is a *segment*." (Printed "have `A` and `B` as endpoints",
  a slip for `X` and `Y`; see `LEDGER.md` §6, batch 140, check 1.)
* p. 171, ‡: "can be properly joined to `A₁`" means "is identical with `A₁` or can be joined to
  `A₁` by an arc of `L` that lies entirely within `J`".
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

/-- A *segment* of the closed curve `J` (1919, p. 170): an interval of `J` minus its endpoints. -/
def Space.IsSegmentOf (σ : Space S) (J T : Set S) : Prop :=
  ∃ X Y : S, ∃ K : Set S, σ.IsArc X Y K ∧ K ⊆ J ∧ T = openArc X Y K

/-- Two arcs *have a segment in common*: some nondegenerate sub-arc's open part lies in both. -/
def Space.ShareSegment (σ : Space S) (K K' : Set S) : Prop :=
  ∃ X Y : S, ∃ T : Set S, σ.IsArc X Y T ∧ openArc X Y T ⊆ K ∩ K'

end HPC.Moore
