# Commission: batch 27 — the banding obstruction, and `Tracking`

**Go!** Runs on top of the batch-26 delivery. One new file, `HPC/Fold/Cut.lean`; root `HPC.lean`
updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## 0. On batch 26

Audited clean: thirty-three earlier files byte-identical, no forbidden tokens, every
commissioned statement delivered, and the two additions — `s3_near_extreme` at any span, and
`crookedIvF_cut`/`crookedIvF_cut_first` — are the right first step. The reversal law extended to
exhaustive through span twelve supersedes this project's earlier statement of it. The
reachability certificate in `SpanWitness.lean`, a bitmask propagated by `reachUpto` with
`not_foldsOnto_of_reachUpto` behind it, is better than the explicit cut the commission asked
for and should be reused. Leaving `¬ F2PrimeOff` conditional on faithfulness is correct, and
the linear-time redesign of the far-index check is noted for a later batch; nothing depends on
it.

Batch 26 §3 reports the induction stopping because two of three pieces band and the third does
not. **That is not a defect of the cut points.** It is an obstruction, and §2 makes it a
theorem.

## 1. Protocol

§§2–4 are ordinary items with proofs supplied. §5 is the search item. Census, axiom audit, no
silent weakening. **A counterexample to `LexCutExists` or to `Tracking` is a success; report it
first**, with the faithful check. A run that proves neither is legitimate.

## 2. The obstruction

`cutSeq` is `bingPath 0 8` restricted to indices `355 … 391`: thirty-seven links, span four on
levels `3 … 7`, attaining `L = 3` at indices 0 and 24 and `H = 7` at 12 and 36. It visits
`L, H, L, H` in that order. Two cut points make three pieces; four alternating extreme visits
cannot be separated into three pieces each missing one kind, so some piece carries both an `L`
and an `H` and has the full span. Exhaustively: **none of the 595 pairs `(r, r')` works.**

**cutSeq_isLip, cutSeq_bounds, cutSeq_attains.** `decide`, or `fin_cases` and `omega`.

**cutSeq_faithful.** The far-index method of batch 25 §3, which at this length is `37 × 5 × 5`
checks — three orders of magnitude below the 409-link case, so the batch-25 file's own
machinery should carry over directly, numeral and all. Verified outside Lean on the same
definitions.

**spanOn.** The sup and inf of `ρ` over an index interval. The nonemptiness side conditions hold
when `a ≤ b < n`; state them as hypotheses if that is cleaner than the `Finset` filters, and say
so.

**cutSeq_no_three_cut.** `decide` over `r, r' < 36`, with `spanOn` on a `Fin 37` sequence
computed by a `List` fold rather than a `Finset` sup' if the kernel prefers it. *(supply: the
decidable form. If `decide` will not evaluate, the certificate is per-pair and small: for each
`(r, r')` name the piece that carries both `3` and `7`, which is always the piece containing
`24` and one of `12`, `36`.)*

**no_three_banded_cut_in_general.** The existential, witnessed by `cutSeq` with `L = 3`,
`H = 7`.

## 3. The measure that survives

`LexCut ρ L H r r'`: the two outer pieces of strictly smaller span, every piece spanning at
least two levels. The middle piece is then strictly shorter than the whole, automatically, from
`1 ≤ r < r' ≤ n − 2`. So the induction measure is `(H − L, n)` lexicographically, and the
hypothesis is available for all three pieces — which it was not under batch 26's cut.

`LexCutExists` is left as an open definition, not a theorem. Evidence: across 4 715 contiguous
subchains of `bing 0 8` and `bing 0 10` of span at least four, a `LexCut` exists in every case,
and still in every case when the cut points are additionally required to sit at crookedness
witnesses — `ρ r ≥ H − 2` and `ρ r' ≤ L + 2` — which is the form the gluing will want. Requiring
every piece to span at least *three* levels fails at 2.3% of subchains, so two is the threshold
and not a taste. **Note the degenerate solution**: `r = 1`, `r' = n − 2` satisfies every clause
but the two span-at-least-two clauses on the outer pieces, which is exactly what those clauses
are there to exclude; a proof of `LexCutExists` that produces it has proved nothing.

## 4. Nothing else to prove here

`spanOn` and `LexCut` carry no theorems in this batch beyond §2. If a lemma about `spanOn` is
wanted for §5 — monotonicity in the interval, say — add it and report.

## 5. `Tracking` — the search item

`Tracking` is the gluing: the middle piece's two arms fold onto `c`, leaving off at times `uG`
and `uT`; the claim is that **one** extension of `c` serves both outer pieces.

**The one-sided version is vacuous, and the delivery must not prove it by accident.** Extend the
walk to follow the single suffix, clamped into `[L + 1, H − 1]` — a 1-Lipschitz sequence bounded
by `[L, H]` moves by at most one under that clamp — and `FoldsFrom` is satisfied, since it
constrains the walk nowhere else. The content is that a single extension serves both sides. This
is also the diagnosis of the last ten formulations: a shape chosen for one arm is a shape imposed
on the other, and every family that fixed the shape in advance was refuted as soon as the two
arms wanted different things.

**s3_of_tracking.** Induction on `(H − L, n)` lexicographically, with `LexCutExists` supplying
the cut. Base: `H ≤ L + 5`, which is `s3_span_five`; and basepoints within two of an extreme at
any span, which is `s3_near_extreme`, so `s3_of_interior` reduces to the interior. Step: take the
cut; the basepoint lies in one of the three pieces. If in an outer piece, that piece has strictly
smaller span and the induction hypothesis applies to it directly — but its own arms are not the
arms of `ρ`, so the other two pieces must be absorbed, which is `Tracking` with the roles
permuted. *(supply: the permutation, or a statement of `Tracking` symmetric enough to cover all
three positions. If the middle-piece case is the only one that goes through, deliver that and say
so.)* If in the middle piece, the induction hypothesis applies by the length drop, and `Tracking`
absorbs the two outer pieces directly.

Expect `Tracking` itself to resist; it has been the difficulty under every name this project has
given it. What would be worth more than a proof is a **counterexample**, which would say that the
itinerary cannot be built by extension at all and that the induction must construct it globally.
`S3` has no counterexample on any corpus — 11 million basepoints in batch 26 — so a
counterexample to `Tracking` refutes the method, not the theorem, and that is worth knowing
early rather than late.

## 6. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample to `LexCutExists` or `Tracking`; whether
   `cutSeq_no_three_cut` went by `decide` or by certificate; whether `s3_of_tracking` went
   through, and for which of the three positions of the basepoint; what was supplied.

## 7. Not in this batch

`LexCutExists` as a theorem; `s3`; the linear-time far-index check that would make
`¬ F2PrimeOff` unconditional; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the
D8/D9 gap.
