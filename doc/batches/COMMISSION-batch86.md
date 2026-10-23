# Commission: batch 86 — Bing 1948, the two open items: `covering_step` (Theorem 14) and `theorem3_end`

**Go!** Runs on top of the latest delivery (batch 84; or batch 85 if it has been run — the two are
independent). One file accompanies this commission as a separate upload:

* `COMMISSION-batch86.md` — this text (also pasted into the prompt).

No skeleton: the targets are the existing `sorry`s `Description.covering_step`
(`HPC/PseudoArc/Theorem14.lean`) and `Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`). New supporting
statements go in new files under `HPC/PseudoArc/` or `HPC/Fold/`, imported from `HPC.lean`. Nothing
else is to be replaced. If either target is refuted, the refutation is recorded in Lean and the
target's docstring says so; the statement itself stays.

The report names the commission read in its first line.

## 0. Status of Bing 1948 in the repository

Machine-checked, standard axioms: Theorems 1–13 (3 without its end-link clause), Theorem 15 from
Theorem 14 (`theorem15_of_theorem14`), the existence and uniqueness of irreducible subcontinua,
and — via Bing 1951 Theorem 4 — a description in the plane (`Plane.pseudoArc_exists`). Open:

1. `covering_step`, to which Theorem 14 (and so Theorem 15) was reduced in batch 83;
2. `theorem3_end`, the fourth conclusion of Bing's Theorem 3, parked since batch 78.

This batch is a **reconnaissance** on both: the deliverable is either a proof, or a
kernel-checked counterexample, or a precise account of what stands in the way — as
propositions where possible. Item 1 comes first; item 2 is taken up only when item 1 is settled
one way or the other, or exhausted.

## 1. `covering_step`

### 1.1 The statement (batch 83)

`CoveringStep Δ P' Q' R W`: for every `L` there are `k > L` and a consolidation `F` of `D_k`
(`F.IsConsolidationOf (Δ.D k)`) such that `F` is a chain from `P'` to `Q'`, the closure of every link
of `F` lies in a link of `D_L`, every link of `F` has diameter `≤ 1/(L+1)`, and `CoversUpTo F P' R W`:
for some index `b`, `F.sub 0 b` is a chain from `P'` to `R` and `W ⊆ F.span 0 b`.

Hypotheses: `Δ : Description X P Q` in a compact `X`, `P ≠ Q`; `P', Q', R ∈ M`; `R ∈ composant M P'`;
`Q' ∉ composant M P'`; `P' ≠ R`; `W ⊆ M` irreducible between `P'` and `R`.

Proved in batch 83 and available: `W ≠ M`, `Q' ∉ W`, `Q' ∉ composant M R`; `W` lies in every closed
connected subset of `M` through `P'` and `R`; `W` is the Hausdorff limit of the spans of the
subchains `D_k(P', R)` (`subset_thickening_span`, `span_subset_cthickening`);
`exists_description_covering_of_step` (the assembly, so `covering_step` is all that Theorem 14's
first paragraph needs).

Recorded in batch 83 §2.4 as not working: Theorem 4 / `theorem4_pair` on the subchain from `P'` to
`R` (it does not reach the end link containing `Q'`); concatenating a chain of `W` with a chain
from `R` to `Q'` (adjacency fails where the second passes near `W` away from `R`); block maps read
off an intermediate level's pattern (they reproduce that level's folds).

### 1.2 Why the statement is not obvious

Bing's chains are consolidations `D_k/β` of a deep level, and in the repository a block map is
surjective and 1-Lipschitz with fibres that need **not** be contiguous (`IsBlockMap`). So the
folds of Part II (an itinerary `β` from fine indices to *times*, a walk `c` from times to coarse
levels, each fine link placed at a time whose level is within one of the link's own level) are
block maps, and every block is small because all its fine links sit in one three-link coarse
window. This is the only mechanism the repository has for a consolidation that is not monotone,
and non-monotonicity is forced: batch 83 observed that a *monotone* block map sends every fine
link after `R`'s to a block at or after `R`'s, while `W` does follow folds of `D_k` past `R`'s
link (the subchain `D_k(P', R)` read as an index interval does not cover `W`).

In those terms `covering_step` asks for a fold of `D_k` onto `D_L` in which **every fine link
meeting `W` is placed at a time no later than the time of `R`**, `R`'s links are placed at that
time and no other link containing `R` exists, `P'` is placed at time `0` alone and `Q'` at the last
time alone.

### 1.3 Questions, in order

**Q1 (falsity?).** Is `covering_step` false? A counterexample would be a description (the
unit-interval-like ones of batch 80's refutations are too degenerate: `W` must be a proper
nondegenerate subcontinuum with `R` in the composant of `P'` and `Q'` outside it — so `M` must be
indecomposable, hence built from crooked chains). The report says whether a finite-level
obstruction can be exhibited: a coarse `D_L`, a crooked `D_k`, points `P', R, Q'` and a candidate
`W` (the closure of the union of a subchain's links at a deeper level, say) for which *no*
block map of `D_k` with three-link blocks has `CoversUpTo` — a finite search over block maps of a
finite pattern, decidable, as in the census work of batches 16–76. Even a negative result at one
level (no `k` up to a bound) is worth recording; a positive one (a block map exists at every level
examined) is evidence for Q2.

**Q2 (the time-ordering fold).** Fix `L`, `k`, the level sequence `ρ` of `D_k` in `D_L`, the index
interval `[a, c]` of fine links meeting `W` (an interval, since `W` is connected and `P' ∈ d_a`),
and `t ∈ [a, c]` with `R ∈ d_t`. Is there an itinerary–walk pair `(β, c)` in the sense of
`FoldsOnto` on the subchain `D_k(P', Q')` with `β(u) ≤ β(t)` for all `u ∈ [a, c]`, `β(u) = β(t)` for
every `u` with `R ∈ d_u`, and `β(u) > β(t)` for … (what is needed for `F.sub 0 (β t)` to be a chain
from `P'` to `R`: no link with `R` outside block `β t`, and `P'` in block `0` only)? The Part II
machinery (`Z77`) chooses the walk freely; here the constraint is on the *order* of times, not on
the walk. State the combinatorial statement exactly (in the faithful model `IsCrookedIvF`), and
prove or refute it. If it is true only under an extra hypothesis on `[a, c]` — e.g. that `ρ` on
`[a, c]` is itself crooked from the basepoint `a` with `t` reachable last — say which, and whether
the hypothesis follows from `W`'s irreducibility (Q3).

**Q3 (what irreducibility gives at a finite level).** `W` is irreducible between `P'` and `R` and
lies in `M`, which is hereditarily indecomposable (`theorem10`). Which finite-level statement
about the fine links meeting `W` follows? Candidates to prove or refute:

* (a) For `k` large, the links of `D_k` meeting `W` are exactly those of an index interval
  `[a, c]`, and *every* subchain of `D_k` from `P'` to `R` … (there is only one, `D_k(P', R) =
  D_k(a, t)`); how does `c` compare with `t`? Batch 83 showed `c > t + 1` can happen. Is
  `D_k(t, c)` — the part of `W`'s links beyond `R` — always contained, in the coarse reading
  `ρ`, in the window swept by `D_k(a, t)`? (Hausdorff convergence, `subset_thickening_span`,
  says the *points* are near; the question is about the coarse levels of the *links*.)
* (b) *Opposite end points of `W`* in the sense of Bing 1951 §5 (batch 85's `OppositeEndPoints`,
  if present; otherwise state it locally): for every `ε > 0` there is an `ε`-chain from `P'` to `R`
  covering `W`. This is a statement about `W` alone, weaker than `covering_step`. Bing 1951
  Theorem 14 gives it from "`P'` and `R` are end points of `W`", which for a subcontinuum of the
  pseudo-arc is Theorem 1 of Bing's Pacific J. Math. paper (external). Can it be proved here
  directly, from hereditary indecomposability of `M` and irreducibility of `W`? If (b) holds,
  does it help with `covering_step` — i.e. can such a `W`-chain be taken to consist of unions of
  links of a deep `D_k`, and then extended past `R` to `Q'`?

**Q4 (a weaker theorem).** If `covering_step` resists, is Theorem 14 provable in a weaker form
that Bing's proof does establish — for instance with `W` replaced by a *given* chain-cover
structure, or for `R` restricted to points for which `covering_step` holds by construction? State
the strongest form proved.

The report answers Q1–Q4 in order and stops at the first that settles the target.

## 2. `theorem3_end`

The parked statement (`HPC/Fold/Theorem4.lean`): in a fold of `E` (crooked in `D`) from basepoint
`i` produced by Theorem 3, a block containing an end link of `E` that meets `D.link 0` lies in the
first three links of `D` (mirror at the top). Batch 78 §2.1 recorded the obstacle for the jump
zigzag (an arm ending at level `L+1` on an up-leg from `L+2` has walk value `L+2`, so its block
reaches `L+3`); batch 82 §2.1 noted that for `i = 0` the identity consolidation satisfies the
clause and for `i = n − 1` the reversal does, and that the general case is unchanged.

Questions: (Q5) Is the clause true for *some* fold (existential form: for every `i` there is a
block map with `β i = 0`, three-link blocks, *and* the end-link clause)? A counterexample is a
level sequence `(ρ, σ)` in the faithful model with an end link meeting `D.link 0` for which every
three-link block map with `β i = 0` puts that end link's block outside `D.link 0 ∪ D.link 1 ∪
D.link 2` — finite, decidable per span, as in the census files. (Q6) If true, does batch 78's
`fold_low_end` (the fake link at level `L` appended after the link meeting `D.link 0`, with the cut
at the time it is reached) give it when the link meeting `D.link 0` *is* the end link? Prove, or
record the counterexample, or the obstruction.

## 3. Deliverables

1. `covering_step` proved, or refuted in Lean, or the answers to Q1–Q4 with every finite-level
   claim as a proved (or refuted) proposition; likewise `theorem3_end` with Q5–Q6.
2. `#print axioms` in `axioms-batch86.txt` for everything proved.
3. Report: first line names the commission read; counterexamples first; then Q1–Q6 in order,
   each answered *proved / refuted / open with the obstruction stated*.
