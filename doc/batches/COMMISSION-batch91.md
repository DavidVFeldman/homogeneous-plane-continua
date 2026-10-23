# Commission: batch 91 — Bing's windows restored (Pacific Theorem 3), and a reconnaissance on Duke 1951 Theorem 10

**Go!** Runs on top of the batch-90 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch91.md` — this text (also pasted into the prompt);
* `Recon91.lean` — a skeleton of three statements, all `sorry`, all work items. Save it as
  `HPC/Plane/Recon91.lean` and add `import HPC.Plane.Recon91` at the end of the root `HPC.lean`.
  Nothing else is to be replaced. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 90, and a correction to batch 89

Batch 90 audited: the `G_δ` half of Theorem 2 and the pseudo-arc inside a tame chain proved;
density reduced to `exists_tame_chain_near`, open, with the partial constructions recorded;
standard axioms throughout.

**Correction.** Batch 89's report said that Bing's windows `D(n_{3k+1}, n_{3k+5})` for Theorem 3
are not shown by his text to form a chain, and that `n_{i+1} = n_i` is possible. Both points are
answered by two observations the text leaves to the reader (Nadler, *Continuum Theory*, 12.13,
which follows Bing's proof with Bing's windows):

* `n_{i+1} > n_i`: a point of `c(n_i) ∩ c(n_i + 1)` has a fibre meeting both links, so the maximum
  defining `n_{i+1}` is at least `n_i + 1`;
* consecutive windows meet: the windows are nonempty open sets covering the connected space
  `M'`, and non-adjacent ones are disjoint; if two consecutive windows were disjoint, the union of
  the windows up to the first and the union of those from the second on would separate `M'`.

Nonemptiness of each window follows from the definition of the `n_i` together with the fact that
a connected set meeting two links meets every link between them (Nadler 12.12;
`Chain.inter_link_nonempty_between`). So Bing's argument is complete; batch 89's replacement
windows are correct but were not needed, and its hand example (fibre intervals `[2m, 2m+3]`) cannot
arise from a monotone map, since it would contradict connectedness. Item 1 below puts Bing's own
chain into the repository so that the record does not carry a defect that is not there.

## 1. Item 1: Bing's windows (`theorem3_HIC_windows`)

State and prove Theorem 3 with Bing's chain. Setting as in `theorem3_HIC` (`Monotone51.lean`):
`f` monotone from the chainable continuum `M` onto `M'`, `ε > 0`, `δ` from uniform continuity with
`ε/5`, `C = [c(1), …, c(n)]` a `δ`-chain covering `M` with every link meeting `M`. Define
`n_1 = 1` and `n_{i+1} = max {j : some fibre meets both c(n_i) and c(j)}` while `n_i < n`, stopping
at `n_j = n`; `D(a, b) = {y ∈ M' : fibre y ⊆ c(a) ∪ ⋯ ∪ c(b)}`; the chain is
`D(n_1, n_5), D(n_4, n_8), …, D(n_{3k+1}, n_j)` with `j − 5 ≤ 3k + 1 < j − 3`, and for `j ≤ 4`
(Nadler: `m ≤ 4`) the single link `M'`, of diameter `≤ 4ε/5`. Prove: the sequence `n_i` is
strictly increasing; each window is nonempty and open; non-adjacent windows are disjoint; the
windows cover `M'`; consecutive windows meet (by connectedness); the mesh is `< ε`. Conclude
`IsSnakeLike M'` again. The statement in the skeleton is the chain-level claim; the report says
which of the six properties needed anything beyond the two observations above.

## 2. Item 2: reconnaissance on Duke 1951 Theorem 10 (`theorem10_1951`, open since batch 85)

### 2.1 The statement and Bing's proof (p. 659), again

*If `D` is a chain covering a compact continuum `M` and `p` is a point of `M` satisfying condition
A, there is a chain `E = (e_1, …, e_n)` covering `M` such that `E` is a refinement of `D` and
`e_1 − ē_2` contains `p`.*

Bing: minimal counterexample `M' ∋ p` (we suppose `M = M'`); suppose each element of `D` meets
`M`; "then `M` contains a proper subcontinuum `M''` that contains `p` and intersects each element
of `D`"; a chain `F` covering `M''`, refining `D`, with `p ∈ f_1 − f̄_2`, of least length; "the last
link of `F` intersects `M'' · (d_1 + d_m)` or else a chain with fewer links than `F` with the
required properties covers `M''`"; then the surgery with `N`, the component of `M − N` containing
`p`, the separation `H + K`, and the displayed chain `E`.

Batch 85 confirmed the Zorn step, the trimming to links meeting `M`, the inclusion of the
component of `p` in `M''` (via condition B), the clopen separation, and that the displayed `E` is a
(weak) chain covering `M` and refining `D`; it left the "fewer links" sentence unestablished and
"did not check in detail" the existence of `M''`.

### 2.2 The existence of `M''` — a question, with a candidate counterexample to the step

For a *decomposable* `M` irreducible from `p` to `q`, a point `x ≠ q` need not lie in any proper
subcontinuum through `p`: the terminal layer of an irreducible continuum can be nondegenerate.
Candidate: `M` = the closure of the graph of `sin(1/x)` on `(0, 1]` together with its limit bar
`{0} × [−1, 1]`; `p = (1, sin 1)`, the free end of the curve. Then:

* `p` satisfies condition A: a nondegenerate subcontinuum of `M` containing `p` is either an arc
  of the curve from `p` (irreducible from `p` to its other end) or all of `M` (any subcontinuum
  containing `p` and a point of the bar, or a point of the curve near the bar together with the
  bar's limit, is all of `M`), and `M` is irreducible from `p` to every point of the bar;
* for a point `x` of the bar, no proper subcontinuum of `M` contains `p` and `x`;
* a chain `D` covering `M` can have a link that meets `M` only inside the bar (small links near
  the far end of the bar). Then **no proper subcontinuum through `p` meets every link of `D`**, and
  Bing's `M''` does not exist.

**Q1.** Prove or refute, in Lean: for `M` a compact continuum, `p ∈ M` satisfying condition A,
`D` a chain covering `M` with every link meeting `M`, there is a proper subcontinuum `M'' ∋ p`
meeting every link of `D` (`exists_proper_meeting_all_links` in the skeleton). If the `sin(1/x)`
example refutes it, record the refutation (the continuum is in Mathlib's reach: the graph is a
continuous image of `(0, 1]`, its closure is compact and connected; irreducibility from `p` to bar
points needs that a subcontinuum containing `p` and a bar point contains the bar — a limit-set
argument — and that a subcontinuum of the curve not meeting the bar is an arc of the curve).
The refutation of the *step* is not a refutation of Theorem 10.

**Q2.** If Q1 is refuted: does Theorem 10 hold for the `sin(1/x)` continuum and the chain `D` of
Q1 directly (a chain from `p` along the curve, ending in the bar, refining `D`)? If it does, Bing's
*statement* survives this example and only his proof is incomplete; if some `D` defeats it, the
theorem as stated is false and the report records the counterexample and whatever weaker form
holds (for instance with `M` hereditarily decomposable *and* the hypothesis of Theorem 11, which is
where Bing uses it).

**Q3.** The "fewer links" sentence. Batch 85: deleting `f_j` can lose points of `M''` that lie in no
other link. Is there a different minimality — least number of links among chains covering `M''`
that refine `D`, start at `p`, *and whose last link meets `d_1 ∪ d_m`* — that is nonempty when
`M''` exists? Or does the sentence need the structure of `M''` (which Bing never fixed)? State what
is proved.

**Q4.** Strongest form established. Possibilities, in decreasing strength: Theorem 10 as stated;
Theorem 10 under "every link of `D` meets a proper subcontinuum through `p`" (the step as a
hypothesis); Theorem 10 for hereditarily decomposable `M`; Theorem 10 for `M` with `p` an end point
in Bing's sense (circular for Theorem 13 but still a statement). Prove the strongest reached and
state the dependence of `endPoint_of_condA` (batch 85) on it.

Report Q1–Q4 in order, each *proved / refuted / open with the obstruction stated*.

## 3. Item 3: the ledger

Append to the module docstring of `HPC/Plane/Monotone51Comb.lean` (or a `-- Note` at its head)
that Bing's windows are valid (item 1) and that the replacement there is an alternative, not a
repair. No other file is to be edited.

## 4. Deliverables

1. `theorem3_HIC_windows`, `exists_proper_meeting_all_links` (proved or refuted, the refutation in
   Lean), `theorem10_1951` or its strongest proved form; `#print axioms` in `axioms-batch91.txt`.
2. Report: first line names the commission read; refutations first; item 1; Q1–Q4; item 3.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`.

## 5. Next

Duke 1951 §4 (Theorems 8, 9, 11), with Nadler Chapters VI, XI and XII.1–5 as the reference for
definitions (separation ordering, irreducible continua, triods; subcontinua of arc-like continua,
hereditary unicoherence, atriodicity).
