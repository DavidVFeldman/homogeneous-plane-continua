import HPC.Archive.Audit50
import HPC.Archive.Audit51
import HPC.Archive.Audit55
import HPC.Archive.CeilNarrow
import HPC.Archive.ClosureFWitness
import HPC.Archive.CoverL5
import HPC.Archive.CoverL5Low
import HPC.Archive.CrossServed
import HPC.Archive.CrossValley
import HPC.Archive.DecideWitness
import HPC.Archive.Descent73
import HPC.Archive.FloorFar
import HPC.Archive.Glue76
import HPC.Archive.LinkFold
import HPC.Archive.MixedThin
import HPC.Archive.Recon86End
import HPC.Archive.Reflect
import HPC.Archive.Target73
import HPC.Archive.Target74
import HPC.Archive.Target75
import HPC.Archive.ThinSpan9
import HPC.Archive.ThreeWalksThin
import HPC.Archive.ValleyNarrow
import HPC.Archive.Most51Geom
import HPC.Archive.Recon87

/-!
# Archive: exploratory files kept compiling

Files of the Theorem-3 campaign (and reconnaissance files on other open items) on which no theorem
of the main line depends: nothing imported by `HPC.lean` imports them. They are kept compiling for
the record and are built separately with `lake build HPCArchive`. Their axiom profile is not part of
the main audit (`Axioms.lean`). See `doc/batches/REPORT-batch103.md` for the list and the reason
each file was moved here.
-/
