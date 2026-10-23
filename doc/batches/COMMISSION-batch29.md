# Commission: batch 29 — `S3ZigFree`

**Go!** Runs on top of the batch-28 delivery. One new file, `HPC/Fold/ZigFree.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 28

Audited clean: thirty-six earlier files identical, no forbidden tokens. **The gate worked** —
the census ran first, the family failed, and the batch stopped and reported rather than
building on it. That is exactly what the gate was for, and it cost one census instead of three
batches.

The diagnosis is right and the failure is mine: `IsZig` was read off minimal itineraries at
*interior* basepoints, and no basepoint at an extreme level was ever checked. `zig_base_lower`
and `zig_base_upper` are the correct two-line reason, and `not_s3Zig` should stay in the
repository as the record of it. Delivering `IsZigFree` and `S3ZigFree` in the same file, with
`s3_of_s3ZigFree` already proved, is the right response to finding the commissioned family
broken.

The repair is confirmed independently: with the amplitude comparison starting at `|t₂ − t₁| <
|t₃ − t₂|` — which is what `IsZigFree.amp`'s `1 ≤ j` says — there are zero failures over all
basepoints of `bing 0 n` for `n = 4 … 8`, and at span ten over the two endpoints, the eight
basepoints where `F2PrimeOff` fails, and eighty random basepoints. *(Note for whoever
re-implements this: the indexing is easy to get wrong in two different ways, and both give a
family that still fails at the endpoints. The exempted comparison is `a₁` against `a₂`, not
`a₁` alone and not `a₂` against `a₃`.)*

### One discrepancy to reconcile

Report §2 gives the maximum over basepoints of the least number of turning targets as

```
span   4  5  6  7  8  9 10 11 12
        2  2  2  3  3  3  4  4  5
```

and says this "is `⌊span/2⌋ − 1` at every span, as at spans 4–10 before". It is not: `⌊4/2⌋ − 1`
is `1`, not `2`. It also disagrees with batch 26's own exhaustive table for the same quantity,
which reads `1 1 2 2 3 3 4 4 5`, and with an independent exhaustive recomputation here, which
gives `1, 1, 2, 2, 3` at spans 4–8 (distributions at span 8: `1` at 90 basepoints, `2` at 311,
`3` at 8).

Most likely a convention shift — counting the base level as a turning target, or measuring
within the zig family rather than over free zigzags, both of which would raise the counts. **Say
which, and restate the table so that batch 26's and batch 28's numbers are the same quantity.**
The law matters: it is the argument that no family with a bounded number of turns can work, and
that argument should not rest on two incompatible tables.

## 1. What is left

`s3_of_s3ZigFree : S3ZigFree → S3` and `theorem3_of_S3` are proved. `S3ZigFree` is the only
open statement between the repository and Bing 1948 Theorem 3 in the block reading.

## 2. The ordinary item

**isZigFree_base_free.** `[L+1, H-1, L+1]` is an `IsZigFree` sequence: `bounds` from
`L + 3 ≤ H`; `len` is `3 ≤ 3`; `alt` at `j = 0` is `(H − L − 2) · (L + 1 − H + 1) < 0`; `amp` is
vacuous, since `1 ≤ j` and `j + 2 < 3` cannot both hold; `ends` is the second disjunct. It
witnesses that the exemption does what it was introduced for — a walk of the family may start
at `L + 1`, which `zig_base_lower` forbids for `IsZig`.

## 3. `s3ZigFree` — the search item

Search permitted, as batches 18–28. **A counterexample is a success; report it first**, with
the basepoint, the chain, and the faithful check.

Evidence: every basepoint of `bing 0 4` through `bing 0 12`, 4 000 random and 8 025 grid
subchains of `bing 0 12` of span at least nine, no failure (batch 28 §3), plus the independent
runs above.

The sketch is unchanged in substance from batch 28 §3, with one point now settled: the family
is closed under the step the induction needs, and it is closed at both ends. Appending a turn of
larger amplitude that reaches an extreme band gives another member, and — this is what the
exemption buys — a member may also be *prefixed* by a sweep of arbitrary amplitude, which is
what a basepoint near an extreme requires. So both directions of extension stay inside the
family.

Two constraints on any proof, from the record:

* The reversal law (once §0 is reconciled): the itinerary must acquire turns in proportion to
  the span, so a step that adds one turn must reduce the span by about two.
* No black-box extension hypothesis (batch 27 §4, and batch 28's confirmation that constraining
  the cut does not help): a statement of the form "an arbitrary walk for the middle piece
  extends" is at least as strong as `S3`, because the middle piece can be made three links long.
  The extension must be constructed with the middle's itinerary.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample to `S3ZigFree`; the reconciliation asked for in
   §0; whether `s3ZigFree` was proved and by what induction; for a partial result, which cases
   closed.

## 5. Not in this batch

The linear-time far-index check that would make `¬ F2PrimeOff` unconditional; Bing 1948
Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
