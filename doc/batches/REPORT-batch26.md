# Report — batch 26: `S3`, the folding statement with the itinerary existentially quantified

Files added: `HPC/Fold/Span.lean` (the commissioned file) and `HPC/Fold/SpanWitness.lean`
(the §3 counterexample), with the root imports in `HPC.lean`.
Scripts: `census-batch26.py`. Nothing else was touched.

## 1. No counterexample to `S3` was found, and none is claimed

The census scores `S3` at a basepoint by computing the **least number `k` of turning targets**
of a zigzag itinerary onto which both arms fold — base centre free in `{p−1, p, p+1}`, turning
levels free in `[L+1, H−1]`, directions alternating, `FoldsOnto` decided exactly by forward
reachability. A basepoint is a candidate counterexample only if *no* itinerary works up to the
search bound. **There was no such basepoint on any corpus.**

| corpus | basepoints | failures |
|---|---|---|
| every basepoint of `bing 0 n`, `n = 4 … 12` (exhaustive) | 23 631 | 0 |
| every basepoint of every subchain of `bing 0 8` of length ≥ 9 and span ≥ 5 | 11 045 666 | 0 |
| exhaustive faithful corpus, lengths 8, 9, 10 on six levels (251 602 members) | 221 792 | 0 |
| 178 random subchains of `bing 0 10` of length ≥ 50 and span ≥ 6 | 123 831 | 0 |
| random faithful chains, length 40 on ten levels and length 200 on fourteen levels | 5 680 | 0 |
| the eight span-ten basepoints at which `F2PrimeOff` fails | 8 | 0 |

The search bound was `k ≤ 5`, and `k ≤ 6` for `bing 0 11`, `bing 0 12` and the random
subchains of `bing 0 10`; it was always at least one above the least `k` actually found.

Two remarks on the evidence. First, the exhaustive faithful corpora at these lengths carry no
span above three: the crookedness clause of the faithful model forces a chain of span four to
be long (Bing's own `bing 0 4` has thirteen links), so the corpora that reach the interesting
spans are Bing's chains and their subchains. Second, only zigzag itineraries are searched; a
failure of the search would be evidence, not a proof, whereas a success is a genuine witness
(the fold is exhibited and checked).

### The reversal law, now exhaustive

The commission's table — max `k` over basepoints equals `⌊span/2⌋ − 1`, exhaustive for spans
4–7, sampled at 8 and 10 — is reproduced and extended, **exhaustively through span twelve**:

| span | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| max `k` over basepoints of `bing 0 span` | 1 | 1 | 2 | 2 | 3 | 3 | 4 | 4 | 5 |
| `⌊span/2⌋ − 1` | 1 | 1 | 2 | 2 | 3 | 3 | 4 | 4 | 5 |

The subchain corpora give the same maxima per span — 1, 2, 2, 3 at spans 5–8 over all
subchains of `bing 0 8`, and 2, 2, 3, 3 at spans 6–9 over random subchains of `bing 0 10` — so
the law is not an artefact of the full chains. The first basepoint attaining the maximum is 0
at spans 4 and 5, basepoint 5 at spans 6 and 7, basepoint 57 at spans 8 and 9 (the batch-25
witness), and basepoint 343 at spans 10 and 11.

The shape of the minimal itineraries is informative. At every basepoint within two of an
extreme the least `k` is 1 — a single sweep to the far extreme. In the interior the minimal
itineraries are overwhelmingly of the form `(c₀, L+1, H−1)` or `(c₀, H−1, L+1)`, that is
`k = 2` with both turns at the extreme bands; the basepoints that need more are those where the
itinerary has to turn at *interior* levels first, and the turning levels then spiral outward:
at basepoint 343 of `bing 0 10` the least itineraries are `4 → 2 → 7 → 1 → 9` and (at
basepoints 349, 351) exactly the commission's `5 → 2 → 7 → 1 → 9`, with the downward turns
`L+2, L+1` and the upward turns `H−3, H−1`.

## 2. The §3 item: `¬ F2PrimeOff` at span ten — done

`HPC/Fold/SpanWitness.lean` proves the failure of `F2PrimeOff` at basepoint 343 of `bing 0 10`.

* The census reproduces the commission's finding exactly: over all 2 379 basepoints of
  `bing 0 10`, `F2PrimeOff` fails at 343, 347, 349, 351, 2027, 2029, 2031 and 2035, all of
  level five, and nowhere else.
* The chain is carried as one natural number in base sixteen, as in batch 25, and
  `ce10_eq_bingPath` proves that the numeral *is* `bingPath 0 10`.
* The certificate is forward reachability, as the commission's first route suggests, but in
  the form that needs no explicit cut: `reachUpto` propagates the set of times a fold could
  occupy as a bitmask, `not_foldsOnto_of_reachUpto` proves that an empty set at any link
  refutes the fold, and the thirty members of the family are discharged uniformly. The set
  dies within 343 links on every member, so one bound serves for all; on the V-ladders with
  `l = 2` it dies exactly at the backward arm's last link, which is the near-miss described in
  the commission.
* Kernel cost: about two minutes for the whole file, the thirty certificates included.

**The counterexample carries faithfulness as an explicit hypothesis**, exactly as batch 25's
first form did: `not_f2PrimeOff_of_faithful (hcr : IsCrookedIvF ceSeq10 ceSeq10) : ¬ F2PrimeOff`.
The far-index check of batch 25 §3 was ported to the longer chain and does **not** evaluate. It
is `2379 × 11 × 11` far-index checks against batch 25's `409 × 9 × 9`, and counted in scan
steps 21.5 million against roughly one million; run in the kernel it consumed the whole 64 GB
of the machine and was killed after about an hour, so the port was removed rather than left in
the build. The check itself passes: run outside Lean on the same definitions it reports no
failure at any of the 2 379 indices, which is why the hypothesis is stated rather than
abandoned.

A feasible check exists, and is the natural item for a later batch. The cost is dominated by
the scans for the *next* index at which a level is met: for the levels near the extremes, which
are met only at the ends of the chain, each scan runs the length of the chain. Threading the
tables backwards — the next index at which each level is met, the next index carrying each
value, and the first completion of each ordered pair of values — makes the whole check linear,
about 300 000 updates instead of 21.5 million scan steps, at the price of proving the
invariants of the fold. Nothing about the witness needs to change.

## 3. `s3` was not proved

What is proved of it:

* `theorem3_of_S3` — Bing 1948 Theorem 3, block reading, three-link form, from `S3`;
* `s3_of_f2PrimeOff` — the batch-24/25 route is subsumed;
* `s3_span_five` — the base of the induction, every span up to five;
* `s3_near_extreme` — at *any* span, every basepoint within two of an extreme, and
  `s3_of_interior`, which reduces the statement to basepoints three or more from both extremes;
* `foldsOnto_iff_foldsFrom`, `foldsFrom_extend`, `foldsFrom_split` — the splitting machinery;
* `crookedIvF_cut` and `crookedIvF_cut_first` — the cut the inductive step rests on: between an
  index at the bottom and a later one at the top, a faithful crooked sequence comes within one
  of the top and then, after that, within one of the bottom, and taking both crossings as early
  as possible bands the two pieces (`ρ ≤ H − 3` before `r`, `ρ ≥ L + 2` between `r` and `r'`).

Where the induction stops. `crookedIvF_cut_first` delivers the first two pieces of
COMMISSION.md §4 with their bands, each of span at most `H − L − 1`: the piece up to the first
crossing `r` lives in `[L, H−2]`, and the piece from `r` to the first crossing `r'` of the
bottom band lives in `[L+1, H]`. The **third** piece is the obstruction: from `r'` to the index
attaining `H`, the sequence is bounded by nothing better than `[L, H]`, so the induction
hypothesis does not apply to it. Choosing `r'` as the *last* crossing before `b` instead bands
the third piece and unbands the middle one; no choice of two cut points bands all three, and
the two extra clauses one would need — that the sequence does not return to the bottom band
after `r'`, or not to the top band before `r` — are exactly the statements the earlier batches
refuted at span ten. The remaining route is the one the commission sketches: cut recursively,
once per two levels of span, so that the itinerary acquires the `⌊span/2⌋ − 1` turns the
census says it must have. Nothing found here contradicts `S3`.

The statement `s3`, and the unconditional `theorem3` that would follow from it, are kept at the
end of `HPC/Fold/Span.lean`, commented out, as in batches 24 and 25.

## 4. Status of the files

`HPC/Fold/Span.lean` and `HPC/Fold/SpanWitness.lean` build with no `sorry`, `admit`, `axiom`,
`native_decide` or `@[implemented_by]`, no linter warnings, and axiom profile within `propext`,
`Classical.choice`, `Quot.sound` — the `sorry` inside the commented-out block at the end of
`Span.lean` is in a comment. The four pre-existing `unused variable` warnings in earlier-batch
modules are untouched. `HPC/Fold/SpanWitness.lean` takes about two minutes to build, the
thirty kernel certificates and the identification with `bingPath 0 10` included; everything
else is fast.
