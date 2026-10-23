# Commission: batch 80 — Bing's Theorem 5 (pattern following), Theorem 6, and Theorem 12 unconditional

**Go!** Runs on top of the batch-79 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch80.md` — this text (also pasted into the prompt);
* `Theorem5.lean` — a skeleton with two `sorry`s (`theorem5`, `theorem6Pos_shift`) and two
  derived theorems (`patternFollowing`, `theorem12`) whose proofs are already written against them.
  Save it as `HPC/PseudoArc/Theorem5.lean` and add `import HPC.PseudoArc.Theorem5` at the end of
  the root `HPC.lean`. Nothing else in the workspace is to be replaced.

The report names the commission read in its first line.

## 0. On batch 79

Audited: `theorem4_pair` proved with three-link windows throughout (`pair_exclusion` the new
fact), `theorem10` proved without compactness, Theorems 5, 6, 13 stated; standard axioms; the
only live `sorry` is `theorem3_end`, parked. Recorded: Theorem 12's hypothesis `PatternFollowing`
is Theorem 6 with `j > 0` for every tail (`patternFollowing_of_theorem6Pos`).

## 1. Targets

1. `theorem5`: `Theorem5Statement Δ` for every description, under `[CompactSpace X]`.
2. `theorem6Pos_shift`: Theorem 6 with `j > 0` for every tail — the hypothesis of Theorem 12.
3. Consequently `patternFollowing` and `theorem12` (already written in the skeleton) become
   unconditional: **Bing's uniqueness theorem for the pseudo-arc, machine-checked**.

A counterexample is a success and is reported first, after a definition audit. In particular: if
`Theorem5Statement` as stated in `Statements79.lean` is false or unprovable as written (see §4),
say so, state the corrected form, and prove that; `theorem6Pos_shift` and `theorem12` are what the
classification needs, and `theorem5` is the route.

## 2. Bing's statements (pp. 733–736), in his names

Fine chains `D_1, D_2, …` from `P` to `Q`; `D_{i+1}` crooked in `D_i`; closure of each link of
`D_{i+1}` a compact subset of a link of `D_i`; mesh of `D_i` at most `1/i`; `d(i)_r` the `r`-th
link of `D_i`; `D_i(a, b)` the subchain from link `a` to link `b`; `D^*` the union of the links of
`D`. A chain `E = [e_1, …, e_n]` *follows the pattern* `(1, x_1), …, (n, x_n)` in `D_1` if
`e_i ⊆ d(1)_{x_i}`.

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch80.md, 2. Bing's statements (pp. 733–736); batch 204.]

## 3. Bing's proof of Theorem 5 (pp. 734–735), transcribed

Paragraph numbers are added; nothing else is.

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch80.md, 3. Bing's proof of Theorem 5 (pp. 734–735); batch 204.]

## 4. What the transcription shows, stated as facts about the text

1. **The induction hypothesis is stronger than the statement.** In (P5) "the theorem" is applied
   with `D_2(u, v)` replaced by the collections `R+U`, `U+S+V`, `V+T` of links of `D_{m+1}`, whose
   "end links" `U^*`, `V^*` are unions of links with closures inside a single link of `D_1`, not
   single links; in (P6) with `W`, whose first "end" is the collection `W'`. So the statement that
   inducts is a generalisation: fine level `D_b` (`b ≥ 2`, here `m+1`) in place of `D_2`; a
   contiguous collection of links of `D_b` in place of `D_2(u, v)`; two end *collections* `A`, `B`
   (sub-collections at its two ends) whose closures lie in `d(1)_h`, `d(1)_k` and are disjoint, in
   place of `d(2)_u`, `d(2)_v`; the conclusion's "no interior link of `E` meets `d(2)_u + d(2)_v`"
   becoming "no interior link meets `A^* + B^*`". Whether the induction also needs the pattern to
   run *downward* (the `G` piece follows `(1, x_t), …, (r+1−t, x_r)` from `x_t` down to `h`) — that
   is, the statement for patterns from `k` to `h` as well as from `h` to `k` — or whether that is
   obtained by reversing `D_1`, is for the prover to settle. **The statement `Theorem5'` that
   inducts is the prover's to design**; `Theorem5Statement` is its special case `b = 2`,
   `A = {u}`, `B = {v}`.
2. **The elided step (P4).** "A positive integer `j` and a chain `E` can be found … we omit the
   details." What is asserted: from `F` at level `s` with the stated pattern and end properties, a
   deeper level `j` and a chain `E` following the longer pattern with `e_1 ⊆ f_1 ∪ d(2)_u`,
   `e_2 ⊆ f_1 ∪ f_2`, `e_i ⊆ f_i` for `3 ≤ i ≤ n−1`, `e_n ⊆ f_{n−1} ∪ d(2)_v`. The content is: at a
   deep level the links of `D_j` inside `f_1 ∪ d(2)_u` split into those meeting `d(2)_u`'s side and
   the rest, and the split is a chain. This has to be proved, not transcribed; it is likely the
   same mesh-and-closure argument as (P1). If it needs a hypothesis Bing does not state (e.g. that
   `d(2)_u`'s closure is disjoint from `f_2`), the report says so.
3. **(P1) uses compactness** (the closures of links of `D_2` are compact); `[CompactSpace X]` is
   assumed in the skeleton. The "five-linked subchain" formulation is Bing's way of saying: at a
   deep level, any five consecutive links have diameter of their union `< ε`.
4. **(P5)'s three-chain split** is the crookedness clause of `D_{m+1}` in `D_m` (not in `D_1`),
   read between `d(m+1)_p` (meeting `d(2)_u ⊆ d(1)_h`) and `d(m+1)_q` (meeting `d(1)_{x_t+1}`),
   with (P1) converting "links of `D_m`" into "inside a link of `D_1`". The witnesses `y`, `z` come
   from the clause; that `D_{m+1}(p, z)` avoids `d(2)_v` and stays in `D_1^*(h, x_t)` is the
   claim to check.
5. **Theorem 6 from Theorem 5** needs `d(2)_1` and `d(2)_last` to have disjoint closures inside
   `d(1)_1` and `d(1)_{x_n}`; for a chain from `P` to `Q` with `P ≠ Q` this holds once the mesh is
   below `dist P Q / 2` — so Theorem 6 may need `P ≠ Q` and a shift to a deep level, or the
   pattern `1 = x_1 ≤ … ≤ x_n` with `x_n ≥ 3`. `Theorem6PosStatement` as written has no `P ≠ Q`;
   if the proof needs it, add it and record the change (Theorem 12 already assumes `P ≠ Q`).

## 5. Deliverables

1. `theorem5`, `theorem6Pos_shift` proved, hence `patternFollowing` and `theorem12`, `sorry`-free,
   with `#print axioms` in `axioms-batch80.txt`; the generalised `Theorem5'` with a docstring giving
   its specialisation to `Theorem5Statement`; any change to the statements of `Statements79.lean`
   recorded with its reason.
2. Report: first line names the commission read; any counterexample or unprovable-as-stated
   finding first; then §1; then, for each of (P1)–(P6), what was proved as transcribed, what needed
   a hypothesis or lemma Bing does not state, and what the elided step of (P4) turned out to
   require.

## 6. Not in this batch

Theorem 13's proof (next batch: it needs Theorems 1, 2, 4 (`theorem4_pair`), 10, 12 and the
composant argument); `theorem3_end`; Theorems 8, 9, 14, 15; the 1951 reduction.
