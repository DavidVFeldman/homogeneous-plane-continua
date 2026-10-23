# Commission: batch 123 — closing `theorem3_end`; Bing's Theorem 4 in his two-link form; the only-clauses; the ledger for Theorem 3

**Go!** Runs on top of the batch-122 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch123.md` — this text (also pasted into the prompt);
* `Theorem4Two.lean` — a skeleton (two `sorry`s as work items, two `def … : Prop`). Save it as
  `HPC/Fold/Theorem4Two.lean`, add `import HPC.Fold.Theorem4Two` at the end of the root
  `HPC.lean`. Shapes may be adjusted with the change recorded.

Existing files to be edited in this batch, and only these: `HPC/Fold/Theorem4.lean` (item 1),
whatever file receives the bridge lemmas (item 1), `HPC.lean`, `Axioms.lean`/`axioms.txt`,
`LEDGER.md`, `OPEN.md`, `README.md` (item 4). The report names the commission read in its first
line; items *proved / refuted / open with the obstruction stated*.

## 0. On batch 122

Audited and accepted: `bing_main`, `theorem3Block_holds`, `theorem3_end'`, all standard axioms;
the three repairs to Bing's text recorded in my notes; housekeeping as asked. Nothing refuted.

## 1. Close `theorem3_end`

Replace the `sorry` of `HPC.Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`) by the proof. The import
chain forbids `Theorem4.lean` importing `Recon122.lean` (which imports `Recon121` → `Theorem4`), so
move the bridge from the model to chains — `bHyp_of_crooked`, `chain_of_bconcl`,
`theorem3Block_holds` and the proof of `theorem3EndStmt_holds`/`theorem3_end'` — into a new file
`HPC/Fold/Theorem3Bing.lean` that imports `Recon122General` and the chain library but not
`Theorem4`; `Theorem4.lean` imports it; `Recon122.lean` keeps its names as aliases of the moved
theorems (or re-exports), so nothing downstream breaks. `theorem3_end` keeps its statement
verbatim and its docstring gains one line ("proved in batch 123 from `Theorem3Bing`"). Remove the
"-- OPEN" marker. In `Axioms.lean`, `theorem3_end` moves from "Open targets" to the Bing 1948
group. Expected: `sorryAx` in exactly one line, `fugate_cor1`. Also state and prove, in
`Theorem3Bing.lean`, `theorem3_bing`: Theorem 3 as printed without the only-clause, as a theorem
about chains with explicit arguments (the unfolding of `Theorem3Block`), so the README can name
one theorem.

## 2. Theorem 4, two-link form (`theorem4_two`, `theorem4_of_two`)

Bing's half-page proof is transcribed in the skeleton's header. From `Theorem3Block` (or in the
model, from `BConcl` on `D(1, h)` and on `D(k, n)` reversed): H on D(1, h) with d_r first, G on
D(k, n) with d_s first, h_u and g_v the blocks of d_h and d_k (⊆ e₁ + e₂ and ⊆ e_{m−1} + e_m for
m ≥ 5, by the end clause and because a link meeting e₁ is not inside e_{m−1} + e_m), F =
H(1, u−1) ⌢ (level groups of D′ from the bottom) ⌢ G(v−1, 1) reversed. The seam analysis of
REPORT-batch121 §Q4 (general case) applies at both cuts: h_{u−1}'s links are interior to D(1, h)
and their neighbours lie in H(1, u), so h_{u−1} meets only h_{u−2} and the bottom group; likewise
g_{v−1}. The level groups are consecutive and nonempty because D(h, k) ⊆ D′ runs from level ≤ 1 to
level ≥ m − 2 with steps ≤ 1. Small m (Bing: "m ≤ 4 is easily established") by the level grouping
directly. Report where Bing's text needed more than it says (I expect: the nonemptiness of the
level groups; the two seams; the case h > k by reversal; the degenerate cases r = s or h = k).

## 3. The only-clauses (reconnaissance inside the batch; the Props `OnlyIn`, `Theorem4Literal`)

Bing's "contained in only the first link of F" is open for general chains (REPORT-batch122 §Q3:
it can fail only when `E.link i` is covered by its two neighbours lying in another block;
automatic for realized chains; `only_clause_not_automatic`). Settle it, for Theorem 3 (the open
implication `Theorem3Strong → Theorem3LiteralOr`) and for Theorem 4 (`Theorem4Literal`):
(a) proved — a repair of the block map when an interior basepoint is covered by its neighbours
(say, moving one neighbour into the basepoint's block when the window allows, and showing the
window always allows it or that the other neighbour can be moved instead); or (b) refuted — a
chain, crooked in the 1948 sense, with an interior basepoint covered by its two neighbours such
that *every* block map with the two-link windows and the end clause puts both neighbours outside
the basepoint's block (the model with a "covering" relation added as data would let the census
look; a realization needs rectangles that are not the faithful ones, since those have the clause
automatically); or (c) open with the obstruction. A refutation goes to `LEDGER.md` §1 as "Bing
1948, Theorem 3 as printed (the only-clause)" — it would be the only false clause in the theorem.
Proofs go into `Theorem3Bing.lean`/`Theorem4Two.lean`; no new `sorry` beyond the skeleton's two.

## 4. Ledger, OPEN, README

* `LEDGER.md` §1: replace the batch-121 row "Theorem 3, Bing's proof, special case" by a row that
  says: statement proved (`theorem3_bing`, two-link form, end clause, "or" reading; only-clause
  per item 3), proof as written fails in its special case (certificate `seam_every_H_fails`),
  repaired by three changes none of which is in the text — (1) the level groups read bottom-
  anchored (`cbotG`), (2) an explicit grouping at five coarse links (`special_five`), (3) the
  branch d_i ∈ D(h, k) by the induction hypothesis on D(h, k) inside E(2, r−1) (`special_middle`);
  REPORT-batch121 §Q4, REPORT-batch122. Keep the row on the respective reading as it is.
* `OPEN.md`: item 1 closed and moved to the Closed-items table (with `theorem3_bing`,
  `theorem3_end`, batch 123); one live item remains (`fugate_cor1`); the only-clause enters as a
  live item only if item 3 ends open.
* `README.md`: Bing 1948 "Theorems 1–15; Theorem 3 in Bing's two-link form with its end clause
  (`theorem3_bing`; the only-clause: per item 3); Theorem 4 in the two-link form (`theorem4_two`)
  and the three-link form (`theorem4`)"; batch count 123; the sentence about `theorem3_end`'s
  `sorry` removed.

## 5. Deliverables

1. Items 1–3; `#print axioms` in `axioms-batch123.txt`; `axioms.txt` regenerated (`sorryAx` in one
   line, or two if item 2 is left open — say which).
2. Report: first line names the commission read; items in order; item 3's verdict; the ledger
   notes for Theorem 4 (what Bing's half page needed); the usual notes-file housekeeping.
3. Not attempted: `fugate_cor1`, `treeLike_nonseparating`, `PlaneFacts`.
