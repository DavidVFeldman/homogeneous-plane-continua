import HPC.Fold.Minimal2
import HPC.Fold.Zig77Main

/-!
# Bing 1948, Theorem 3 — open

This file states the goal and nothing else. Everything between it and the repository's proved
material is scaffolding built over thirty-six batches by one author, and none of that scaffolding
is required: it may be used, replaced, or ignored.

**The goal.** For a chain `E` crooked in a chain `D` in the 1948 sense, and any link of `E`, a
block consolidation of `E` whose first block contains that link and each of whose blocks lies in
three consecutive links of `D`.

**Routes already proved, any of which suffices.** Each arrow is a theorem in the repository.

```
theorem3  ⟸  S3               theorem3_of_S3            (batch 26)
S3        ⟸  S3ZigFree        s3_of_s3ZigFree           (batch 28)
S3ZigFree ⟸  S3ZigFreeInterior  s3ZigFree_of_interior   (batch 29)
theorem3  ⟸  F2PrimeOff       theorem3_of_F2PrimeOff    (batch 24)
theorem3  ⟸  F2PrimeF         theorem3_of_F2PrimeF      (batch 22)
theorem3  ⟸  F2PrimeTight     theorem3_of_F2PrimeTight  (batch 18)
```

The last three antecedents are **refuted**. `S3`, `S3ZigFree` and `S3ZigFreeInterior` are open and
have no counterexample on any corpus. A direct proof of `theorem3` that uses none of them is
equally welcome.

**What is settled and may be relied on**: the faithful interval model is exactly the class of
`(minIdx, maxIdx)` pairs of 1948-crooked chains (`isCrookedIvF_minIdx_maxIdx`, `realization`,
batch 22); Bing's Theorem 7 with minimality (`minimality`, `bingPath_length`, batches 24 and 30);
`exists_blocks_first_of_folds`, which turns a common fold of both arms onto **any** walk into the
conclusion of Theorem 3 (batch 6); `s3ZigFree_near_extreme` (batch 29); `isCrookedIvF_restrict`
and `IsCrookedIvF.isLip` (batch 30).

**What is refuted** is listed in COMMISSION.md §2 — fifty-nine `not_`/`no_` theorems in the
repository. They are the record of what cannot work, and they are the reason this file proposes
no route.

**Batch 77: closed.** No `sorry` remains in this file: the target is proved from `Z77.s3_zig`
(`HPC/Fold/Zig77Main.lean`). The history below is kept as it was.

Every `sorry` is a work item. Uncompiled.
-/

namespace HPC.Fold

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form. -/
theorem theorem3 {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 :=
  theorem3_of_S3 Z77.s3_zig hn hcr i

end HPC.Fold
