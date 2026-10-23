# Commission: batch 87 — Bing 1948, the two open items, continued: three-link blocks, and end-time control of folds

**Go!** Runs on top of the batch-86 delivery (batch 85, the 1951 end-point theorems, is independent
and may run before or after). One file accompanies this commission as a separate upload:

* `COMMISSION-batch87.md` — this text (also pasted into the prompt).

No skeleton. Targets are the existing `sorry`s `Description.covering_step` and `Fold.theorem3_end`;
new statements go in new files (`HPC/PseudoArc/Recon87*.lean`, `HPC/Fold/Recon87*.lean`) imported
from `HPC.lean`. Nothing else is to be replaced.

The report names the commission read in its first line.

## 0. On batch 86

Audited: eleven new theorems, standard axioms, no `sorry` outside the two targets and the parked
`theorem14`; `exists_chain_from_of_irreducible` (opposite end points of `W`, from crookedness and
irreducibility alone, with no external theorem) is the result of the batch; `coveringStep_of_folds`
reduces `covering_step` to `IsCoveringFold`; `window_of_irreducible` is Q3 (a); the special cases
of `theorem3_end` are in Lean. Two points of the report are taken up below because they change what
the next step is.

### 0.1 The Q2 refutation is in a one-link model, and the three-link reading survives it

`ModelCoveringFold` requires every block to lie in **one** coarse link (`∀ u, ∃ s, ∀ t, β t = u → ρ t
≤ s ∧ s ≤ σ t`), and `IsCoveringFold` correspondingly asks every block to lie in one link of `D_m`.
Everything else in the repository that consolidates a crooked chain — Theorem 3, Theorem 4,
`theorem4_pair`, batch 81's `exists_step` — uses blocks in **three consecutive** coarse links, and
obtains closures inside links of a shallower level `D_L` by taking the block level `m` deep
(thick readings, Lemma 3.5 of the exposition; `exists_step` does exactly this with `unionRange j
3` and a Lebesgue number). With three-link blocks the batch-86 witness is **not** a counterexample:
for the levels `0, 1, 2, 1, 0, 1` with `P'` in link `0`, `R` in link `3`, `W` meeting links `0 … 4`,
`Q'` in link `5`, the block map `β = (0, 1, 2, 3, 3, 4)` has `R`'s block `3 = {3, 4}` at levels
`{1, 0}` (window `[0, 2]`), all `W`-links in blocks `≤ 3`, `P'` alone in block `0`, `Q'` alone in the
last block, every block within a three-link window. So the model refutation is an artifact of the
one-link reading.

### 0.2 The `theorem3_end` census could not see five coarse links

A crooked sequence spanning five coarse links has at least `z(4) = 13` links (`minimality`); the
exhaustive search tried lengths `8 … 12` and found none, as it must. Lengths `13 … 16` are the
first informative ones.

## 1. Targets

1. **Q2 restated with three-link blocks.** Define `IsCoveringFold₃` (blocks in three consecutive
   links of `D_m`; the other four clauses unchanged) and `ModelCoveringFold₃` in the faithful model
   (`∀ u, ∃ j, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2`, or the repository's `unionRange` reading), and
   prove `coveringStep_of_folds₃`: `IsCoveringFold₃` at deep `m` for every `L` gives `CoveringStep`,
   the closures-in-`D_L` clause coming from a Lebesgue number as in `exists_step` (three-link
   blocks have diameter `≤ 3 ε_m`).
2. **Census for `ModelCoveringFold₃`.** Over faithful sequences `(ρ, σ)` with the window property
   (`ModelWindow`, which follows from irreducibility) and `I` an index interval `[a', c']` containing
   `A ∪ T`, `Qs` outside it at the far end: is there always a three-link time-ordering fold? Exhaust
   what is decidable (four coarse links, all lengths to `10`; five coarse links, lengths `13 … 16`;
   Bing chains); report failures as kernel-checked refutations, or the absence of failures.
3. **The end-time control lemma**, which the batch-86 report identifies as the common core of
   both open items, stated exactly and proved or refuted. In the description of `M` from `R` to
   `Q'` (Theorem 13, `exists_description_from`, `Q' ∉ composant M R`), the `W`-links of a deep level
   form an initial segment `[0, c]`, `R` is in link `0`, and `P'` in some link `p ∈ (0, c)`. Wanted: a
   three-link fold of `[0, c]` from basepoint `p` (`β p = 0`, both links of `P'` in block `0`) in which
   **the two arm ends `0` and `c` are placed at the maximal time**. Compare `theorem4_pair`, which
   places `r` at block `0` and `s` at the last block: here two ends must share the last block, with
   the basepoint in the middle. State it in the faithful model as a proposition about `(ρ, σ)` on
   `[0, c]` with basepoint `p`; decide it by census first; then prove it if no failure appears,
   or record the failing sequence and say which extra hypothesis (from irreducibility of `W`, via
   Q3 (a)–(b)) excludes it. If proved, assemble `covering_step` from it and item 1 (the piece after
   `c` climbs from the maximal time to `Q'`'s block as singletons, as `exists_step`'s tail does).
4. **`theorem3_end`** (Q5 continued): the census at five coarse links (lengths `13 … 16`) and the
   Bing chains `K = 7` with a larger node limit (1 493 undecided cases); a refutation is recorded
   in Lean if found. Otherwise the general clause remains the same end-time question as item 3
   (an end link's time), and any end-time lemma proved there is to be applied here.

Order: 1, 2, 3, 4. A refutation at any stage is reported first.

## 2. Deliverables

1. Lean: `IsCoveringFold₃`, `ModelCoveringFold₃`, `coveringStep_of_folds₃`; the end-time lemma as a
   statement, proved or refuted; `covering_step` and/or `theorem3_end` if reached; census sources
   and logs (`census-batch87-*.c`, `.log`) with the exact statement each decides.
2. `axioms-batch87.txt`.
3. Report: first line names the commission read; refutations first; then items 1–4, each
   *proved / refuted / open with the obstruction stated*; and, for every census, the statement
   decided, the ranges covered, the counts, and the undecided cases.
