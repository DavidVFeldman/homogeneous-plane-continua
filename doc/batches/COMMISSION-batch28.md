# Commission: batch 28 — the increasing-amplitude family, gated on a census

**Go!** Runs on top of the batch-27 delivery. One new file, `HPC/Fold/Zigzag.lean`; root
`HPC.lean` updated. Nothing else touched. **§1 is a gate: run it before writing any Lean.**

## 0. On batch 27

Audited clean. The obstruction is delivered in full, `cutSeq_faithful` by the batch-25 far-index
method as expected, and the report's §4 is the most useful thing in it:

> `Tracking` may be instantiated at a three-point window, and then it already is `S3`.

That is correct, it is the commission's error and not the delivery's, and the delivery was right
to keep `LexCutExists` in the statement underscored rather than quietly drop it. One thing to
add, which closes the obvious repair: **requiring the cut to be a `LexCut` does not help.** Over
5 680 subchains of `bing 0 8` and `bing 0 10` of span at least four, 3 187 admit a `LexCut`
whose middle piece is exactly three links — for instance `bing 0 8` restricted to `[72, 108]`,
cut `(15, 17)`, middle `5, 4, 3`, both outer pieces banded and every piece spanning at least
two. The span-at-least-two clauses do not exclude a three-link middle, because three links can
span two levels.

The conclusion is general and worth stating once: **no hypothesis of the form "an arbitrary walk
for the middle piece extends" can be a step in a proof of `S3`**, however the cut is
constrained, because the middle piece can always be made small enough that the hypothesis
carries the whole theorem. The extension has to be constructed together with the middle's
itinerary. That is what every one of the eleven formulations has got wrong, in one way or
another.

## 1. The gate

At the basepoint of each span where the reversal count is largest, the minimal itineraries are

| span | basepoint | minimal turning sequences |
|---|---|---|
| 6 | 5 | `c₀ → 1 → 5` |
| 8 | 57 | `c₀ → {5,6} → 1 → 7` |
| 10 | 343 | `c₀ → {2,3} → {7,8} → 1 → 9` |

all ending `→ L+1 → H−1`, with strictly increasing amplitudes. `IsZig` is that shape: turning
levels in `[L+1, H−1]`, directions alternating, amplitudes strictly increasing, the last two
turns at the extreme bands in either order; base centre in `{p−1, p, p+1}`.

Evidence so far — every basepoint of `bing 0 n` for `n = 4 … 8`; the eight span-ten basepoints
where `F2PrimeOff` fails; 120 random basepoints of `bing 0 10`; 466 subchains of `bing 0 8` at
six basepoints each — **no failure**.

**Span twelve is untested**, and `bing 0 12` has 13 860 links, beyond what was available here.
This is exactly the gap that refuted the previous family: its evidence stopped at span nine and
it failed at span ten.

> **Census `S3Zig` exhaustively on `bing 0 11` and `bing 0 12`, and on subchains of `bing 0 12`
> of span ≥ 9, before any of §§2–3. If it fails, stop, report the failure with its basepoint and
> its minimal itinerary, and deliver nothing else.** A failure is the batch's result and a good
> one: it costs one census rather than three batches.

If it holds, also report the minimal turning sequences at the hardest basepoints of spans 11 and
12, which is the data the next formulation will be read off.

## 2. The family, in Lean

`IsZig`, `zigWalk`, `S3Zig`, `s3_of_s3Zig` — the last being immediate, since a zig walk is a
walk. *(supply: `zigWalk`, which the skeleton leaves as a work item — the natural definition is
a fold over the turning list emitting one level per step; state its length and its values as two
lemmas, since §3 will want them.)*

`zig_not_contains_offLam` records that the two families are genuinely different rather than one
inside the other: a one-bump walk whose peak `h` is interior has a single turn of amplitude
`h − c` followed by a descent of amplitude `h − L − 1` and an ascent of `H − L − 2`, which
violates the increasing-amplitude condition when `h − c ≥ h − L − 1`, i.e. when `c ≤ L + 1`.
Any such `c, h, L, H` witnesses it.

## 3. `s3Zig` — the search item

Search permitted, as batches 18–27. **A counterexample is a success; report it first.**

The sketch is the same induction as before, with one difference that may matter: the family is
now closed under the operation the induction needs. Appending one further turn of larger
amplitude to a zig walk is again a zig walk, provided the appended turn reaches an extreme band;
so the inductive step "extend the itinerary by one sweep" stays inside the family, which was not
true of any bounded family. Whether the extension can always be *chosen* is the content, and it
is not to be assumed as a hypothesis (§0).

The reversal law is a check on any proof: the itinerary must acquire about `⌊span/2⌋ − 1` turns,
so a step that adds one turn must reduce the span by about two.

## 4. Deliverables

1. **The §1 census, first**, with its result stated before anything else.
2. Census of whatever else was run.
3. Whatever is proved, `sorry`-free, with `#print axioms`.
4. Report: the §1 result; any counterexample to `S3Zig`; whether `s3Zig` was proved; the
   minimal turning sequences at spans 11 and 12; what was supplied.

## 5. Not in this batch

`s3`; `LexCutExists` as a theorem; the linear-time far-index check that would make
`¬ F2PrimeOff` unconditional; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the
D8/D9 gap.
