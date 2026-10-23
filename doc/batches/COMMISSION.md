# Commission: batch 76 — the extension law, and what gluing actually needs

**Go!** Runs on top of the batch-75 delivery. No new file is prescribed. This text is pasted into
the prompt and is in the archive as `COMMISSION-batch76.md`; the report names it in its first line.

## 0. On batch 75

Audited: one new file (`Target75.lean`, six theorems on `[propext, Classical.choice, Quot.sound]`),
a second correction note in `Span.lean`, nothing else changed; the repository's `sorry`s are
`s3_general` and `theorem3`.

Recorded facts. No basepoint of any span through fourteen is unserved. The batch-74 clause on
spans ten and twelve is refuted (five legs at ten, six at twelve, both witnesses re-checked); the
maxima are 3, 4, 5, 5, 6, 6, 6 at spans 8–14; both formulas offered in batch 75 are refuted, and
`⌊S/2⌋` fits from span nine on as a conjecture with six points. The extreme levels are served, at
every span, by two walks depending on the band alone, with no crookedness (`extreme_levels_two_walks`).
The thin model lags the general model by one leg at spans 9–13.

**The extension law** (batch 75 §2.1), the one uniform regularity found: at every one of 17 425
sampled basepoints with least leg count `k ≥ 3`, spans 8–14, a least walk is a walk serving the
basepoint in a sub-band of span at most `S − 3` (never `S − 1` or `S − 2`) with exactly one leg
appended at the end, run to an extreme of the full band. This is a census statement, and it is
recorded as a conjecture below.

## 1. Targets

`s3_general` remains the target. No proof is expected from this batch; it is a second
reconnaissance batch, and its purpose is to state the extension law exactly and to measure what an
induction through it would have to supply.

## 2. Questions, asked as questions

1. **A correction to §2.2, asked as a question.** `FoldsOnto f len c` gives each arm its *own*
   itinerary `β`; the two arms share only `(len, c)`. `foldsFrom_split` is applied to one arm with
   that arm's arrival time `u₁`, and to the other arm with its own. Is the column "arrival times
   meet" of batch 75 §2.2 a hypothesis of any statement in the repository — or is it stronger than
   what a two-arm gluing needs? If the latter, the obstruction named in §2.2 and §4 is not the
   obstruction, and the question that was not measured is §2.2 below.
2. **The suffixes.** At the sampled basepoints of §2.1 (spans 10–14, all leg counts `k ≥ 3`), with
   `w'` the sub-band walk folding both truncated arms and `w` its one-leg extension folding both
   whole arms: for each arm separately, take the fold of the *truncated* arm onto `w'`, read its
   arrival time `u₁` at the truncation index, and ask whether the arm's *suffix* (from that index on)
   satisfies `FoldsFrom suffix len c u₁` on `w`. Report: at how many basepoints both suffixes fold
   from their own arrival times; where one does not, whether some *other* fold of the truncated arm
   onto `w'` (a different `β`, a different arrival time) repairs it; and where none does, the
   basepoint written out. This is the datum an induction through the extension law would carry.
3. **The extension law in Lean, as a statement.** Define, as a decidable predicate on a finite pair
   and basepoint, `ExtendsSubBand ρ i L H k`: there exist `L ≤ L' ≤ ρ i ≤ H' ≤ H` with
   `H' − L' ≤ H − L − 3`, a walk `w'` with levels in `[L', H']` folding both arms truncated at their
   first exit from `[L', H']`, and a walk `w` equal to `w'` with one leg appended to `L + 1` or
   `H − 1`, folding both whole arms. Kernel-check it (`decide +kernel`, as in `Audit71.lean`) on the
   stored witnesses of batches 74 and 75 that are short enough (the 78-, 290- and 3000-link ones;
   the longer ones if the decision procedure reaches them). Then record the conjecture, as a
   commented statement with the census cited:
   `∀ S ≥ 8, every basepoint of a faithful pair of span S with least leg count ≥ 3 satisfies
   ExtendsSubBand`. No proof.
4. **Which extreme.** The appended leg runs to `H − 1` or to `L + 1`, in comparable numbers. What
   decides it — the side on which the arms first leave the sub-band? the level of the basepoint
   relative to the sub-band's middle? the last target of `w'`? A census table of the appended
   direction against those three, at spans 10–14.
5. **Why `S − 3`.** The sub-band is never of span `S − 1` or `S − 2`. Is that a fact about least
   walks (a one-leg extension from a sub-band of span `S − 1` would serve, but a shorter walk from
   a narrower sub-band serves too, so "least" hides it), or a fact about the arms (no walk of a
   sub-band of span `S − 1` or `S − 2` folds the truncated arms at all)? Measure both readings.
6. **The `⌊S/2⌋` conjecture**, recorded as a comment in `Span.lean` beside the two corrections, with
   its six data points and the caveat that each is a maximum over a finite corpus.

No opinion is offered on the answers. A route to `s3_general` is not asked for and is not to be
proposed; the report's §4 may again say what the evidence says, as evidence.

## 3. Deliverables

1. §2.3's definition and kernel checks as Lean, `sorry`-free, with `#print axioms`; the conjecture
   statements of §2.3 and §2.6 as comments.
2. The censuses of §2.2, §2.4, §2.5 under the audit protocol, over whole arms, two `FoldsOnto`
   deciders; any witness re-checked by code sharing nothing with the census.
3. Report: first line names the commission read; any unserved basepoint first, with a definition
   audit; then §1; then §2 1–6; then a one-paragraph statement of what the evidence says.

## 4. Not in this batch

Proofs at spans ten and above; a proof of `s3_general`; a replacement sufficiency statement for
the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time
far-index check; Bing's seam.
