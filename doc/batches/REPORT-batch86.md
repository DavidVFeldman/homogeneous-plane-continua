Commission read: `COMMISSION-batch86.md` (batch 86 — Bing 1948, the two open items: `covering_step` (Theorem 14) and `theorem3_end`). Run on top of batch 84; batch 85 has not been run.

# Report — batch 86: reconnaissance on `covering_step` and `theorem3_end`

**Summary.**
* Neither target is proved or refuted. `Description.covering_step` (`HPC/PseudoArc/Theorem14.lean`) and `Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`) are unchanged and still `sorry`. Their docstrings are unchanged, since neither was refuted.
* New files, all imported from `HPC.lean` and all free of `sorry`:
  * `HPC/PseudoArc/Recon86.lean`
  * `HPC/PseudoArc/Recon86Model.lean`
  * `HPC/PseudoArc/Recon86Chain.lean`
  * `HPC/Fold/Recon86End.lean`
* `#print axioms` output for every new theorem is in `axioms-batch86.txt`. Each one uses only `propext`, `Classical.choice` and `Quot.sound`.
* Main new results:
  * **Q3 (b) is proved** (`Description.exists_chain_from_of_irreducible`): for every `ε > 0` there is a chain *from `P'` to `R`* (strong `IsFrom` sense) that covers `W`. Each of its links is a union of links of a single level `D_k`, and any two points of a link are within `ε`.
  * **Q2 is stated exactly** (`IsCoveringFold`), and `covering_step` is reduced to it (`coveringStep_of_folds`, proved).
  * **Q2 is refuted in the faithful model** (`model_covering_fold_refuted`), even with crookedness and the window property (Q3 (a), proved as `window_of_irreducible`) both assumed.
  * **Q5–Q6:** proved for a basepoint at an end link and for three-link `D`. The general case is open. A computer search found no counterexample; it is not kernel-checked.

## 1. Counterexamples

* **`Fold.model_covering_fold_refuted`** (`HPC/PseudoArc/Recon86Model.lean`). This refutes the combinatorial statement of Q2 when only the natural finite-level hypotheses are assumed. It is *not* a counterexample to `covering_step`.
  * **Data.** Coarse levels `0, 1, 2, 1, 0, 1` (`ρ = σ`, six links). `P'` is in link `0`, `R` in link `3`, `W` meets links `0 … 4`, and `Q'` is in link `5`.
  * **Hypotheses that hold.** The sequence is in the faithful model (`IsCrookedIvF`, checked by `decide`). The window property holds (`ModelWindow`): every `W`-link shares a coarse link with a link of `[0, 3]`.
  * **No time-ordering fold exists.** Blocks sit in a single coarse link and consecutive links here have different levels, so links `0, 1, 2` get times `0, 1, 2`. Link `3` must get time `b ≥ 2`, and it cannot share a block with link `2`, so `b = 3`. Link `4` then needs a time in `{2, 3}` (it must also be `≤ b = 3`). Both are excluded: block `2` holds level `2` and block `3` holds level `1`, while link `4` has level `0`.
  * **How to read it.** A time-ordering fold (and so `covering_step`) must use more of `W` than two things: the crookedness of the levels, and the fact that `W`'s links stay in the window swept by `D_k(P', R)`.

No counterexample to `covering_step` or to `theorem3_end` was found.

## 2. `covering_step` — Q1 to Q4

### Q1 (falsity?) — open. No finite obstruction found.

`covering_step` asks for *some* deep `k` at each `L`. So a counterexample would need an obstruction at every deep level of one fixed description. A single-level obstruction refutes nothing by itself.

What was established points towards the claim being true:
* the time-ordering fold does exist on the `W`-part alone (Q3 (b) below);
* the coarse reading of the `W`-links is controlled (Q3 (a)).

The model counterexample of §1 is combinatorial only. It is not known to come from a description with an irreducible `W`: its levels span three coarse links, so the crookedness hypothesis is vacuous there.

**Status: open. No counterexample.**

### Q2 (the time-ordering fold) — stated exactly; reduction proved; refuted in the model under crookedness and the window property

* **Statement** (`Description.IsCoveringFold Δ P' Q' R W k m q β b`, in `Recon86.lean`). `β` is a block map of `D_k` onto `q` blocks such that:
  * every block lies in one link of `D_m`;
  * every link containing `P'` is in block `0`;
  * every link containing `Q'` is in block `q − 1`;
  * every link containing `R` is in block `b`;
  * every link meeting `W` is in a block `≤ b`.
* **Reduction, proved** (`Description.coveringStep_of_folds`). Suppose that for every `L` there are `k > L`, `m > L` with `ε_m ≤ 1/(L+1)`, and such a fold. Then `CoveringStep Δ P' Q' R W` holds.
  * The consolidation is `ofBlocks β`.
  * Closures of blocks lie in links of `D_L`, because `closure (D_m link) ⊆ D_{m−1} link`.
  * Diameters are at most `ε_m`.
  * `IsFrom` and `CoversUpTo` are read off the block conditions.
  * This is the commission's "fold with every `W`-link at a time `≤ β(t)`, `R`'s links at that time, `P'` alone at `0`, `Q'` alone at the end", made exact.
* **In the faithful model** the statement is `Fold.ModelCoveringFold ρ σ A T Qs I`. It is **refuted** under crookedness together with the window property (`ModelWindow`) — §1.
  * The commission asked whether it holds "only under an extra hypothesis on `[a, c]`, e.g. that `ρ` on `[a, c]` is crooked from `a` with `t` reachable last".
  * The window hypothesis, which *does* follow from irreducibility (Q3 (a)), is **not** enough.
  * I did not find a finite-level hypothesis that is both sufficient and derivable from irreducibility.
  * The obstruction is a **turning point of the time walk**: once the fold from `P'` to `R` has used its times, a `W`-link beyond `R` whose level differs from those of the times next to `b` has nowhere to go.

**Status: statement proved equivalent in the direction needed (fold ⇒ `CoveringStep`); the crookedness-plus-window version refuted; the true version open.**

### Q3 (what irreducibility gives at a finite level)

**(a) — proved** (`Description.window_of_irreducible`, `Recon86.lean`).
* **Statement.** For every `L` there is `N` such that for `k ≥ N`, every subchain `D_k(a, b)` from `P'` to `R`, and every link `u` of `D_k` meeting `W`, there is a `v ∈ [a, b]` with `D_k.link u` and `D_k.link v` inside one link of `D_L`.
* **Proof.** A Lebesgue number of the cover of `M` by the links of `D_L`, together with batch 83's `subset_thickening_span`.
* **Also proved** (`Chain.meet_ordConnected`): the links meeting `W` form an index interval `[a', c']`.
* **What this answers.** It is the "coarse levels of the links" version of the Hausdorff convergence the commission asks about. The links beyond `R` are in the coarse window of `D_k(P', R)`.
* **What it does not give.** As Q2 shows, this is not enough to build the fold.

**(b) — proved** (`Description.exists_chain_from_of_irreducible`, `Recon86Chain.lean`).
* **Statement.** For every `ε > 0` there are a level `k` and a chain `F` with:
  * `F.IsFrom P' R`: `P'` in the first link only, `R` in the last link only;
  * `W ⊆ F.union`;
  * every link of `F` a union of links of `D_k`;
  * any two points in a link of `F` within `ε`.
  So `P'` and `R` are opposite end points of `W`, and the chain consists of unions of links of a deep `D_k`. This answers the second half of (b) positively.
* **Proof — no external theorem needed.** It uses only the crookedness of the levels and the irreducibility of `W`, through (a):
  * Take the interval `[a', c']` of `D_k`-links meeting `W`.
  * By (a) at a level `L'`, these links refine the stretch `[lo, hi]` of `D_{L'}` swept by `D_k(P', R)`. The stretch has at least three links because `dist P' R > 2 ε_{L'}`, and its first and last links are met between `P'` and `R`.
  * `D_k(a', c')` is crooked in `D_{L'}(lo, hi)` (`IsCrookedIn'.sub`, `.restrict`).
  * Theorem 4 in paired form (`theorem4_pair`) then gives a block consolidation. The (one or two) links of `P'` form the first block and those of `R` the last; every block lies in three consecutive links of `D_{L'}`.
  * The chain-level step is `Chain.exists_blocks_isFrom`: Theorem 4 read as "a chain from `A` to `B`".
* **Does it help with `covering_step`?** Only halfway.
  * It is the fold of Q2 restricted to the `W`-part `D_k(a', c')`.
  * What is missing is the extension past `R` to `Q'`. The two remaining pieces of `D_k`, before `a'` and after `c'`, are attached at the links `a' − 1` and `c' + 1`. In the `W`-fold these sit at *arbitrary* times in `[0, b]`, not at time `b`.
  * To reach `Q'` at the last time, the piece containing `Q'` has to climb through the times between its attachment time and `b`. At each of those times it shares a block with `W`-links, so it has to follow the fold of `W` back to `R` geometrically.
  * No lemma in the repository forces that. This is the exact form of batch 83's "`R` must act as a cut point at scale `η`".

**A reformulation, not formalized.** Theorem 13 gives a description of `M` from `R` to `Q'`, because `Q' ∉ composant M R` (batch 83, `not_mem_composant_of_mem_composant`). In such a description the `W`-links form an initial segment `[0, c]`, and there is only one outside piece, attached at `c`. `covering_step` would follow from a fold of `[0, c]` with three properties:
* `P'` at time `0`;
* `R` (link `0`) at the maximal time `b`;
* the attaching link `c` at time `b` too, or at a time from which the outside piece can climb.

Theorem 3 at the basepoint of `P'` produces folds of the two arms `[0, p]` and `[p, c]`. What it does not control is the *end times* of the arms, which is the same issue as `theorem3_end` (§3). So the two open items are closer than the commission's split suggests. Both ask for control of the block of an end link in a Theorem-3 fold.

### Q4 (a weaker theorem) — the strongest form proved

* Theorem 14 is not proved in any weaker form of the shape the commission suggests.
* **"`W` replaced by a given chain-cover structure".** This reduces to `coveringStep_of_folds`: `exists_description_covering` holds for every `(P', Q', R, W)` for which the time-ordering folds exist at every level. Theorem 14 itself would additionally need the alternating construction of batch 83 §2.5, items 2–5, which is not done.
* **The strongest statements proved:**
  * `exists_description_covering_of_step` ∘ `coveringStep_of_folds` (conditional on the folds);
  * the unconditional `exists_chain_from_of_irreducible` for `W` alone — Theorem 14's first paragraph without the extension to `Q'`.

## 3. `theorem3_end` — Q5 and Q6

### Q5 (the existential clause) — proved in two special cases; open in general; no counterexample found

**Proved** (`HPC/Fold/Recon86End.lean`), each with the exact conclusion of `theorem3_end`:
* `theorem3_end_of_injective`: any injective block map with `β i = 0` satisfies both the three-link clause and the end-link clause. An end link meeting `D.link 0` lies in `D.link 0` or `D.link 1`.
* `theorem3_end_at_first` (`i = 0`, `β = id`) and `theorem3_end_at_last` (`i = n − 1`, `β = Fin.rev`). This is batch 82's remark, now in Lean.
* `theorem3_end_of_three`: `k = 3`, where the first three and the last three links are all of `D`. This follows from `theorem3`.

**Search — computational only, not kernel-checked, not a proof.** I wrote an exact decision procedure in the faithful model:
* **What it decides:** whether there is a block map with `β i = 0`, every block's intervals meeting a common window `[j, j+2]`, and the end-link clause.
* **How the clause is read:** it fires when an end link meets `D_0` (resp. `D_{k−1}`) by the meeting table of `linkRect_meet_strip_iff`. In the realized chain of `Faithful.lean`, "block ⊆ first three links" is exactly "every member has `ρ ≤ 2`".
* **Results:**
  * All faithful sequences spanning exactly four coarse links, of length `6 … 10`, every basepoint (95 808 sequences): no failure (`census-batch86-exhaustive.c`, `.log`). The same enumeration over exactly five coarse links finds no faithful sequence at lengths `8 … 12` (the lengths tried), so it cannot reach the interesting cases.
  * Every subchain of the Bing chains `bpath(0, K−1)` for `K = 5, 6, 7` that has an end link on an extreme coarse link, every interior basepoint (28 691 cases in all): no failure. 1 498 cases were left undecided by the search's node limit (5 at `K = 6`, 1 493 at `K = 7`) (`census-batch86-bing.c`, `.log`).
* **Status:** consistent with Q5 being true. Not a proof, and not a Lean artifact.

**Where the general argument stops.**
* A fold violates the clause at an end link `E_0 ⊆ D_1` meeting `D_0` only when `E_0`'s time has window `[1, 3]` and some other link of that block is at level `3`. This matches batch 78's jump zigzag.
* **Repairs that do not work in general:**
  * Re-timing `E_0` alone (`β 0 ∈ β 1 ± 1`) fails when `β 1`'s block also has a window reaching level `3`.
  * Giving `E_0` a private time needs `β 1` to be the maximum.
  * Appending fake level-`0` links beyond `E_0` keeps the sequence crooked, since `E_0` already meets `D_0`. But the fake tail can leave `E_0`'s time without ever visiting it.
* **Status: open, obstruction stated.**

### Q6 (`fold_low_end`) — not attempted

I did not re-open batch 78's `fold_low_end` construction. Q5 is not settled in general, and the reformulation of §2 (Q3 (b)) suggests the more useful statement is a general "end-time control" lemma for Theorem-3 folds, serving both open items. **Status: open.**

## 4. Deliverables checklist

1. `covering_step`: not proved, not refuted. Q1–Q4 answered above, with Q2 and Q3 as proved propositions and the model refutation for Q2. `theorem3_end`: not proved, not refuted. Q5 proved in the settled cases, with search evidence (not kernel-checked) for the rest; Q6 open.
2. `axioms-batch86.txt`: `#print axioms` for all eleven new theorems (standard axioms only).
3. This report. Its first line names the commission; counterexamples come first (§1); then Q1–Q6 in order.

## 5. New declarations

| Declaration | File | Status |
|---|---|---|
| `Chain.meet_ordConnected` | `HPC/PseudoArc/Recon86.lean` | proved |
| `Description.IsCoveringFold` (def) | `HPC/PseudoArc/Recon86.lean` | — |
| `Description.coveringStep_of_folds` | `HPC/PseudoArc/Recon86.lean` | proved |
| `Description.window_of_irreducible` | `HPC/PseudoArc/Recon86.lean` | proved |
| `Fold.ModelCoveringFold`, `Fold.ModelWindow` (defs) | `HPC/PseudoArc/Recon86Model.lean` | — |
| `Fold.model_covering_fold_refuted` | `HPC/PseudoArc/Recon86Model.lean` | proved |
| `Chain.mem_ofBlocks_link`, `Chain.dist_le_of_near` | `HPC/PseudoArc/Recon86Chain.lean` | proved |
| `Chain.exists_blocks_isFrom` | `HPC/PseudoArc/Recon86Chain.lean` | proved |
| `Description.exists_chain_from_of_irreducible` | `HPC/PseudoArc/Recon86Chain.lean` | proved |
| `Fold.theorem3_end_of_injective`, `_at_first`, `_at_last`, `_of_three` | `HPC/Fold/Recon86End.lean` | proved |
