# Commission: batch 82 — the rest of Bing 1948, part one: Theorem 3's end-link clause; Theorems 7, 8, 9 in full

**Go!** Runs on top of the batch-81 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch82.md` — this text (also pasted into the prompt);
* `Theorem7.lean` — a skeleton of three statements and one definition, all `sorry`, all work
  items. Save it as `HPC/Fold/Theorem7.lean` and add `import HPC.Fold.Theorem7` at the end of the
  root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 81

Audited: `theorem13` and its three auxiliaries proved as stated; standard axioms; the only live
`sorry` is `theorem3_end`. Recorded facts: `M`'s own connectedness had never been proved before
`isConnected_M`; the limit-superior lemma for chained sets replaces connected links; composants
are proper by Baire and a clopen boundary-bumping lemma; Bing's "By Theorem 2" in Theorem 13 is
Theorem 2 applied to `E₂` as a refinement of `D_j`.

Both results of Bing 1948 the classification uses are machine-checked. The purpose of this batch
and the next is the rest of the paper, as stated by Bing, for its own sake.

## 1. Targets

1. **`theorem3_end`** (`HPC/Fold/Theorem4.lean`), the parked fourth conclusion of Bing's Theorem 3:
   a block containing an end link of `E` that meets `D.link 0` lies in the first three links of
   `D` (mirror at the top). Batch 78 §2.1 recorded the obstacle for the jump zigzag: an arm ending
   at level `L + 1` on an up-leg from `L + 2` has walk value `L + 2` and its block reaches `L + 3`.
   Batch 78's `fold_low_end` (a fake link at level `L` appended after the end link, with the fold
   read at the *time* the fake link is reached) is the device that got around it for Theorem 4;
   whether the same device, or a final phase of the zigzag, or a post-processing of the fold at
   its last block gives the clause itself is the question. If the clause is false in the
   three-link form for the walks `s3_zig` produces but true for *some* fold, state and prove the
   existential form; if it is false for every fold (a counterexample), that is the finding.
2. **`theorem7`**: Bing's Theorem 7 in full — the crooked minimal consolidation following the
   canonical pattern. The repository has the lower bound (`minimality`, `minGap`) and the pattern
   as a level sequence (`bingPath`, `bingPath_length`); what is missing is the consolidation `F`
   itself, its crookedness in `D`, and that it follows the pattern.
3. **`theorem8`**, in the form §3 explains.
4. **`theorem9`**.

A counterexample is a success and is reported first, after a definition audit; in particular a
counterexample to Bing's Theorem 8 as literally stated (§3) is to be recorded in Lean if found.

## 2. Bing's statements and proofs (pp. 736–737), transcribed

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch82.md, 2. Bing's statements and proofs (pp. 736–737) (passage 1); batch 204.]

[Repository: Bing's `z(n)` for an `n`-link `E` is the repository's `z (n − 1)` (the repository's
`z 3 = 6`, Bing's `z(4) = 6`); Bing's `P(n)` is `bingPath 0 (n − 1)`, whose recursion
`bingPath a (b−1) ++ (bingPath (b−1) (a+1)).tail ++ (bingPath (a+1) b).tail` is the alternate
definition. The skeleton's `bingPattern` packages it; its one `sorry` is the bound
`bingPath` values lie in `[0, m−1]`, which is to be proved.]

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch82.md, 2. Bing's statements and proofs (pp. 736–737) (passage 2); batch 204.]

[The transcription of Theorem 9's proof follows the printed text; "`d_1` and `d_s` respectively"
is what the geometry requires (`D(r, s)` runs from `e_m` at `d_r` to `e_1` at `d_s`, so read
backwards it is a chain from `e_1` to `e_m`), and the report should confirm the reading.]

## 3. Facts about the text

1. **Theorem 8's "chain whose links are the sums".** Two chains `D_1`, `D_2` crooked in `E` and
   following the same pattern may have a link of `D_1` at position `i` meeting a link of `D_2` at
   position `j` with `|i − j| ≥ 2`, whenever the pattern places `i` and `j` in the same or adjacent
   links of `E` (the pattern revisits levels). Then the unions are not a chain, and the statement
   is void as written. Nothing in Bing's hypotheses excludes this. The skeleton therefore states
   Theorem 8 with the hypothesis that the unions form a chain `C`; whether a kernel-checked
   counterexample to the literal statement exists (two chains in a metric space — a finite one
   will do — crooked in a three- or four-link `E`, following `P`, with a crosswise intersection) is
   asked, and is to be recorded as `not_theorem8_literal` if found. In Theorem 9's use the two
   chains are consolidations of two subchains `D(1, r)`, `D(r, s)` of one chain, whose links meet
   only at adjacent indices of `D`, so crosswise intersections can occur only between blocks
   containing `d_{r−1}, d_r, d_{r+1}`, all of which lie in the last blocks; the report checks that
   `H` is a chain there.
2. **Theorem 7's "plus a link of `D` in `e_1`" and "may not be a chain".** `F_1` is a consolidation
   of `D(r, j)` together with one extra link in `e_1`, and Bing notes its first two links may fail to
   meet. The block reading avoids this: blocks are contiguous intervals of `D`, and `f_1` is the
   union of *all* links of `D` in `e_1` — which in general is not contiguous (`D` may return to
   `e_1`). So in the block reading `f_1` cannot be "all links in `e_1`"; it is the block of
   `D`-indices from `1` to the last link before `D` first leaves `e_1 ∪ e_2`'s neighbourhood…
   **The statement in the skeleton is the block reading**, and it may need Bing's hypotheses
   sharpened (e.g. `d_1 ⊆ e_1`, `d_n ⊆ e_n`, as in Theorem 9's hypotheses) to hold; if a
   counterexample to the block-reading `theorem7` as skeletoned exists, record it and prove the
   corrected statement. Bing's own `F` (unions of non-contiguous collections) is a consolidation
   in his sense (D6) but not a block consolidation; the repository chose block consolidations in
   batch 4 and records the reason.
3. **Theorem 7's minimality.** "No proper consolidation of `F` has these properties": a proper
   consolidation has fewer than `z(m)` links; `minimality` (a chain crooked in `E` reaching both
   ends has at least `z` links) gives it once `F` has exactly `z` links and reaches both ends. The
   skeleton asks for exactly `z (m−1)` links; the report states minimality as a corollary.
4. **Theorem 7's induction** places `F_1, F_2, F_3` and then "other elements of `D` may be placed in
   appropriate elements of `F`". Which elements are "other" (links of `D` outside `D(r, s)`, and
   inside `D(r, s)` but not in the three subchains' consolidations?) and where they go is not
   said. In the block reading with the pattern fixed, each remaining link's block is forced by
   contiguity; whether the forced placement keeps `F` crooked in `E` and following `P` is the
   claim to check.
5. **Theorem 9's `K`** is Theorem 4 applied to `H + D(s+1, n)` — a chain formed from a
   consolidation and a subchain; `theorem4_pair` / `theorem4` apply to a chain crooked in `E`,
   and `H + D(s+1, n)` is crooked in `E` by Theorem 8 (for `H`) and Theorem 2 (for the rest) —
   the report says how `H + D(s+1, n)` is made a chain in the repository's terms (a block
   consolidation of `D` with prescribed blocks on `D(1, s)` and singletons on `D(s+1, n)`).
6. **The conclusion of Theorem 9**, "any subchain of `F` whose end links contain `d_t` and `d_n`
   contains `D(r, n)`": in the block reading, every `E`-index `u ≥ r` has block `β u ≥ β t`. The
   skeleton states that. It is used in Theorem 14 (next batch) to make `X_{i,n}(P_i, R_i)` cover
   `W_i`.

## 4. Deliverables

1. `theorem3_end`, `theorem7`, `theorem8`, `theorem9`, `sorry`-free, with `#print axioms` in
   `axioms-batch82.txt`; any counterexample to a literal statement in Lean; every reshaped
   statement recorded with its reason.
2. Report: first line names the commission read; counterexamples first; then §1 1–4; then §3 1–6.

## 5. Not in this batch

Theorems 14, 15 (the next batch; they need Theorem 9, Theorem 5 and Theorem 11, plus irreducible
subcontinua); the 1951 paper.
