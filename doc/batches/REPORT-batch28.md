# Report: batch 28 — the increasing-amplitude family

Delivered: `HPC/Fold/Zigzag.lean` (new), `HPC.lean` (import added), `census-batch28.c` with its
output `census-batch28.log`, and this report. Nothing else was touched. The whole project
builds; the new file has no `sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]`,
no linter warnings, and every theorem in it has axiom profile inside
`propext`, `Classical.choice`, `Quot.sound`.

---

## 1. The gate: `S3Zig` fails — at every span, for a structural reason

**The §1 census was run first and it fails.** It does not fail only at span twelve: it fails at
span four and at every span, and the reason is a two-line argument rather than a numerical
accident.

**No zig sequence can begin in an extreme band.** Suppose `ts[0] = L + 1`. All entries lie in
`[L+1, H−1]`, so the first turn cannot descend, and by the alternation clause it is not
stationary: `ts[1] > ts[0]`. The second turn reverses, with strictly larger amplitude, so

```
ts[2] = ts[1] − |ts[2] − ts[1]| < ts[1] − |ts[1] − ts[0]| = ts[0] = L + 1,
```

which is outside the band. Hence `L + 2 ≤ ts[0]`, and symmetrically `ts[0] ≤ H − 2`
(`zig_base_lower`, `zig_base_upper` in the Lean file). Equivalently: the base levels that any
zig sequence can use are exactly `L+2 … H−2`; the census prints this list for every band from
`[0,4]` to `[0,12]` and it is always `2 … H−2`.

**That kills `S3Zig` at any basepoint sitting at an extreme level.** `FoldsOnto f len c` pins
`β 0 = 0` and demands `|f 0 − c 0| ≤ 1`, so the walk's *first* value must be within one of the
basepoint's level. At a basepoint with `ρ i = L` the only admissible start inside the band is
`L + 1`, and no zig walk starts there. (The base-centre clause of `S3Zig` is therefore not the
culprit: it is implied by `FoldsOnto` anyway, and deleting it changes nothing.)

**Counterexample, with basepoint and itinerary.** `cutSeq` — the 37 links of `bingPath 0 8` at
indices 355…391, span four on levels 3…7, Lipschitz, faithful, both extremes attained, all
proved in batch 27 — at **basepoint 0**, whose level is `L = 3`. The set of minimal itineraries
there is **empty**: no `IsZig 3 7 ts` at all has `ts[0] ∈ {2, 3, 4}`, since `zig_base_lower`
forces `ts[0] ≥ 5` and `zig_base_upper` forces `ts[0] ≤ 5`, i.e. `ts[0] = 5`, and `|3 − 5| = 2`.
The same happens at basepoint `0` of every `bing 0 n`, and at its last basepoint.

In Lean: `not_s3Zig : ¬ S3Zig`, via the two general lemmas
`s3Zig_fails_at_low_basepoint` and `s3Zig_fails_at_high_basepoint`.

**What the census adds beyond the counterexample.** `census-batch28.c` decides `S3Zig`
*exactly* — not by search with a cutoff, but by bitmask reachability over every zig walk of the
band, which for span `S` is exactly `2^(S−2) − 2` sequences (1 022 at span 12), each walk being
at most 56 steps and therefore one 64-bit word. One `O(n)` sweep per walk resolves all
basepoints of a chain at once, computing

```
G i = { u : the forward arm at i folds onto the walk from time u }
T i = { u : the backward arm at i folds onto the walk from time u }
```

and `i` is served iff `0 ∈ G i ∩ T i` and the walk starts within one of `ρ i`. Censused:

| corpus | basepoints | unserved at an extreme level | unserved elsewhere |
|---|---|---|---|
| `bing 0 4 … bing 0 12` (all of them, 13 861 links at span 12) | 23 661 | 2 per chain, always the two endpoints | **0** |
| 4 000 random subchains of `bing 0 12` of span ≥ 9 | — | the extreme-level ones | **0** |
| 8 025 grid subchains of `bing 0 12` (stride 97) of span ≥ 9 | — | the extreme-level ones | **0** |

So the verdict is sharp: **the family is right in the interior and impossible at the ends**,
spans eleven and twelve included. The gap the commission feared — a genuine span-twelve
counterexample of the kind that refuted the previous family — does not exist; what exists is a
boundary defect present at every span, which the earlier evidence had not caught because it
evidently did not test basepoints at the extreme levels.

## 2. The minimal turning sequences at spans 11 and 12

Maximum over basepoints of the least number of turning targets, `bing 0 n`:

| span | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| max least turns | 2 | 2 | 2 | 3 | 3 | 3 | 4 | 4 | 5 |

which is `⌊span/2⌋ − 1` at every span, as at spans 4…10 before — so the reversal law survives
into spans 11 and 12.

* **Span 11.** 124 basepoints attain 4; the first is **basepoint 343, level 5**, with twelve
  minimal itineraries, exactly `{4,5,6} → {2,3} → {7,8} → 1 → 10`. Basepoint 347 has ten of
  those twelve (all but the two with base 4 and second turn 2); basepoint 349 has the eight
  with base in `{5,6}`.
* **Span 12.** 8 basepoints attain 5; the first is **basepoint 2027, level 5**, with sixteen
  minimal itineraries, exactly `{4,5} → {7,8} → {2,3} → {9,10} → 1 → 11`; likewise at 2029.

Both end `→ L+1 → H−1` with strictly increasing amplitudes, so the *shape* the commission read
off spans 6, 8, 10 continues to hold at 11 and 12 — the family is wrong only about where a zig
is allowed to start.

## 3. The repair the data points to

Exempt the **first** amplitude from the increase condition: keep the band, the alternation, the
finish at the two extreme bands and `|t₂ − t₁| < |t₃ − t₂| < ⋯`, but let `|t₁ − t₀|` be
arbitrary. Then the admissible base levels become all of `L+1 … H−1` — a sequence may open with
a large sweep and then settle into growing amplitudes, e.g. `1 → 3 → 1` at span four — and the
census result becomes uniform with no exceptions at all:

| corpus | unserved basepoints |
|---|---|
| every basepoint of `bing 0 4 … bing 0 12` | **0** |
| 4 000 random subchains of `bing 0 12` of span ≥ 9 | **0** |
| 8 025 grid subchains of `bing 0 12` of span ≥ 9 | **0** |

and the minimal turn counts are unchanged (the table of §2 is the same for the relaxed family),
so the relaxation costs nothing in reversal count: it only fixes the boundary. That family is
stated in the file as `IsZigFree`/`S3ZigFree`, with `IsZig.isZigFree`, `s3ZigFree_of_s3Zig` and
`s3_of_s3ZigFree`; it is **neither proved nor refuted here**, and is the recommended shape for
the next formulation.

Caveat on the subchain corpora, as in earlier batches: a contiguous subchain of a faithful
crooked sequence need not itself be faithful, so those rows are evidence rather than instances
of the hypothesis. They were censused because a failure among them would have been worth
chasing; there was none. The whole-chain rows are not subject to the caveat at spans 4 and 5,
where faithfulness is proved in the project (`bing04_faithful`, `bing05_faithful`), and the
counterexample of §1 uses `cutSeq`, whose faithfulness is proved.

## 4. What is in the Lean file

Supplied (the commission left `zigWalk` as a work item):

* `stepRun a b` — the unit-step run from `a` to `b`, excluding `a`, including `b`; defined by
  recursion on `(b − a).natAbs`;
* `zigTail`, `zigLevels`, `ampSum`, and `zigWalk ts = ((zigLevels ts).length, getD …)`;
* **its length**: `zigWalk_length : (zigWalk (t :: rest)).1 = ampSum t rest + 1`, i.e. one step
  per unit of amplitude plus the starting level, on top of `stepRun_length` and
  `zigTail_length`;
* **its values**: `zigWalk_head` (time 0 is the base centre), `zigWalk_step` (`|c (u+1) − c u| =
  1`: one level per step, via `stepRun_isChain`, `zigTail_isChain`, `zigLevels_isChain`) and
  `zigWalk_mem_band` (every value lies in `[L+1, H−1]` when the turning list is a zig).

Proved:

* `IsZig`, `S3Zig` verbatim from the commission, except that `ts.get! j` is written `ts[j]!` —
  `List.get!` no longer exists in the current Lean, and `getElem!` is its spelling;
* `s3_of_s3Zig : S3Zig → S3`, immediate as expected;
* `zig_mem`, `zig_base_lower`, `zig_base_upper` — the obstruction of §1;
* `abs_sub_base_le_of_folds` — `FoldsOnto` pins the walk's first value to within one of the
  basepoint's level, so the base-centre clause of `S3Zig` is redundant; the refutation below
  goes through the folds and not through that clause, and so refutes the clause-free version
  of `S3Zig` as well;
* `zig_not_contains_offLam`, with witness `c = L+1 = 1`, `h = 3`, `L = 0`, `H = 4`. This is the
  class the commission names (`c ≤ L + 1`); the reason the witness works is `zig_base_lower`,
  not a computation on `offLam`;
* `s3Zig_fails_at_low_basepoint`, `s3Zig_fails_at_high_basepoint`, and **`not_s3Zig : ¬ S3Zig`**;
* `IsZigFree`, `S3ZigFree`, `IsZig.isZigFree`, `s3ZigFree_of_s3Zig`, `s3_of_s3ZigFree`.

Kept, commented out, with the reason: `theorem s3Zig : S3Zig`. It is false.

## 5. Not attempted

Per COMMISSION-batch28.md §5: `s3`; `LexCutExists` as a theorem; the linear-time far-index
check; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap. Also not
attempted: `S3ZigFree`, which is the natural next target and is left open.
