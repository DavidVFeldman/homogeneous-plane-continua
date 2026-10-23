# Commission: batch 125 — `jct` part I (crossing parity); Theorem 4 as printed for `k ≥ 4`

**Go!** Runs on top of the batch-124 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch125.md` — this text (also pasted into the prompt);
* `Jct1.lean` — a skeleton, `sorry`s as work items. Save it as `HPC/Plane/Jct1.lean`, add
  `import HPC.Plane.Jct1` at the end of the root `HPC.lean`. Shapes may be adjusted with the change
  recorded. No existing file is to be edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group
  "Jordan curve theorem for polygons (batch 125)" and the Bing 1948 group for Theorem 4),
  `OPEN.md`/`README.md`/`LEDGER.md` if item 2 closes `Theorem4LiteralGe4`.

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 124

Audited and accepted in full: Theorem 3 as printed proved in every clause (`theorem3_literal`),
Theorem 4 as printed refuted at `m = 3` with `r < s` (ledger), `FugateU ↔ Cor1Sufficiency`, and
the survey. 482 declarations, `sorryAx` in one line. The survey's plan is adopted: `jct` by parity
(this batch and the next), then polygonal Janiszewski by mod-2 cycles, then `enclose`;
`treeLike_nonseparating` and (U) stay open problems unless a field is added, which David decides.

## 1. `jct`, part I: the crossing parity (`Jct1.lean`, namespace `HPC.Plane`)

The design is the half-open east-ray rule, defined for **every** `x ∉ Γ` without general position
(`CrossesEast`, `crossCount`, `parity`); the skeleton's docstrings carry the arguments. Items:

1. `crossesEast_comm`, `not_crossesEast_of_mem`, `crossesEast_locallyConstant_of_ne` — the single-
   edge facts.
2. **The vertex rule.** This is the content of part I. At a height equal to that of a vertex the
   indicators of the two edges at that vertex change, and the half-open convention makes their
   *sum mod 2* locally constant; horizontal edges are never counted and pass the rule along a
   horizontal run to the next non-horizontal edges. The skeleton leaves the exact statement to you
   (`vertex_rule_placeholder` is a marker, delete it): a lemma about maximal horizontal runs of the
   polygon is probably the cleanest. Record the statement you proved.
3. `parity_locallyConstant`, `parity_eq_of_isPreconnected`.
4. `parity_far`, `parity_eq_zero_of_far` (the complement of a large sup-metric ball is connected:
   `isConnected_compl_closedBall_pt`, `Tree7Star`).
5. `exists_parity_flip` (at *some* interior point of a non-horizontal edge; move along the edge if
   needed to avoid vertex heights of other edges), `exists_nonhorizontal_edge`,
   `polygon_separates`.

Everything here is for `IsSimpleVertices v`; where simplicity is not needed (items 1, 4), say so
and drop it. Part II (batch 126) will need: the odd set and the even set are each connected
(consistent one-sided strips along `Γ`, the `sides_of_split` argument without the split
hypothesis), and `frontier` of each is `Γ` (in particular the flip across *horizontal* edges, via
the strips). If, while proving part I, a cleaner route to part II appears (for instance a
different normal form of the parity that flips across every edge directly), say so in the report;
do not start part II.

## 2. Theorem 4 as printed, `k ≥ 4` (`theorem4_literal_ge4`, `theorem4LiteralGe4_holds`)

REPORT-batch124 Q3 describes what is needed: the pair form (`theorem3_pair` / `pair_main` in the
model) applied at both ends of `two_core` at once — companions of `d_r` and `d_s` sharing a coarse
link, in the first resp. last block; `onlyIn_of_neighbour` and `onlyIn_of_no_common` then give the
only-clauses, as in `theorem3_literal`. The `K = 4` grouping is new; the companions coincide only
when `K = 4` and `s = r + 2`. Proved / refuted / open; if refuted, the ledger row of batch 124 is
extended; if proved, `Theorem4LiteralGe4` closes (OPEN item 2 → closed items; README).

## 3. Deliverables

1. Items 1–2; `#print axioms` in `axioms-batch125.txt`; `axioms.txt` regenerated (`sorryAx` in one
   line).
2. Report: first line names the commission read; the vertex-rule statement actually proved; item 2's
   verdict; the notes for part II.
3. Not attempted: part II of `jct`; `enclose`; `janiszewski`; `fugate_cor1`;
   `treeLike_nonseparating`.
