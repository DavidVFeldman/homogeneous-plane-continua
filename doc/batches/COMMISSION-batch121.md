# Commission: batch 121 — reconnaissance on `theorem3_end` and on Bing's Theorem 3 as printed

**Go!** Runs on top of the batch-120 delivery. No skeleton. One file accompanies this commission,
`COMMISSION-batch121.md` (also pasted into the prompt). Lean work goes in a new file
`HPC/Fold/Recon121.lean` (import it at the end of `HPC.lean`); open statements are to be recorded
there as `def … : Prop` (which compiles without `sorryAx`), never as new `sorry`s. No existing file
is to be edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group "Reconnaissance, batch 121"),
and — only if a refutation is found — `LEDGER.md` §1 and `OPEN.md` item 1.

The report names the commission read in its first line and answers each question *proved /
refuted / open with the obstruction stated*.

## 0. On batch 120

Audited: `theorem7_1951` proved, nothing refuted, README/OPEN as asked; 413 declarations,
`sorryAx` in two. The two false steps in my degenerate-case docstring are recorded.

## 1. The situation

`HPC.Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`, `sorry` since batch 78, nothing depends on it)
is a **hybrid**: the three-link form of Theorem 3 (`theorem3`, proved) plus a *three-link* end
clause. Bing's Theorem 3 as printed (p. 732) is stronger on both counts. Transcribed from the scan:

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch121.md, Theorem 3 and its proof; batch 204.]

What the repository knows (OPEN.md item 1; REPORT-batch86/87; notes §§2, 24, 26, 59, 85, 86, 97,
98):

* A consolidation in Bing's sense *is* a block map: if d_t and d_{t+1} lie in links f_u, f_{u'}
  then f_u ∩ f_{u'} ⊇ d_t ∩ d_{t+1} ≠ ∅, so |u − u'| ≤ 1. The block reading is faithful.
* The **two-link** form of the main clause (S₂: fibres of a 1-Lipschitz β with ρ-range ≤ 1) is
  neither proved nor refuted. It fails in the *sequence* model (ρ alone, batch 24), but those
  witnesses are not chains; in the *faithful* model (ρ, σ) and on Bing's own chains P(0,4)–P(0,6)
  it holds at every basepoint tested (notes §§26, 28). The three-link form is what `theorem3`
  proves, and §2 of the notes records that only the mesh bound downstream is affected.
* The **three-link end clause** (`theorem3_end`): proved for injective block maps, for a
  basepoint at an end link, and for k = 3 (`Recon86End`); exhaustive model census K = 4, n ≤ 13;
  K = 5, n = 13..16; Bing K ≤ 7 — no failure (REPORT-batch87 §5); the general case open, the
  obstruction being control of the block of an end link ("end-time control"); three repairs of
  the Z77 zigzag shown not to work in general (REPORT-batch86 §3).
* **Bing's induction has a seam problem** (notes §59, my analysis, never certified): in the
  special case, h_{u−1} must meet the top level-group of D′ and nothing else, but h_{u−1} is
  only known to lie in two adjacent links of E somewhere below h_u ⊆ e_{r−2} + e_{r−1}; and
  d_{k+1}, adjacent to d_k ⊆ e₂, may lie in e₃ and meet two level-groups. The literal
  construction, executed by a program on P(0,4) at basepoint 6, failed (notes §28), though a
  two-link schedule exists there.

## 2. Questions

**Q1 — Bing's statement in Lean.** Record, as `def`s in `Recon121.lean`,
(a) `Theorem3Literal : Prop` — Bing's Theorem 3 as printed in the block reading: for every
`E` 1948-crooked in `D` (any `k`) and every `i`, a block map `β` with `β i = 0`, every block in
`D.unionRange j 2` for some `j`, and the two-link end clause (an end link meeting `D.link 0` has
its block in `D.unionRange 0 2`; meeting `D.link (k−1)`, in `D.unionRange (k−2) 2`); also the
clause "d_i is contained in *only* the first link of F", stated as `∀ u ≠ β i, ¬ E.link i ⊆
(E.ofBlocks β).link u` — say whether it is automatic for block consolidations or an extra
condition (it is not automatic if a link can lie in the union of other links; is that possible in
a chain?);
(b) `Theorem3EndTwo : Prop` — the proved three-link `theorem3` plus the *two-link* end clause;
(c) the implications among `Theorem3Literal`, `Theorem3EndTwo`, the statement of `theorem3_end`
and `theorem3`, as proved theorems (`Theorem3Literal → Theorem3EndTwo → theorem3_end`-statement →
`theorem3`-statement), so the audit shows how the open items relate.

**Q2 — Does the model census bear on general chains?** The decision procedure of batches 86–87
reads the end-clause hypothesis "`E.link t ∩ D.link 0` nonempty" through the *forced* meeting table
(`linkRect_meet_strip_iff`): link t meets strip j iff j ∈ [ρ u, σ u] for some u within one of t.
A general chain can have an end link `E_0 ⊆ D_1` that meets `D_0` although no neighbour has
ρ ≤ 0; such meetings are not forced, so the census never sees that instance of the hypothesis. Is
this a real gap? Specifically: (a) is there a reduction — given `E` crooked in `D` with `E_0`
meeting `D_0`, a modified pair `(ρ̃, σ)` in the faithful model (say `ρ̃ 0 = 0`) whose realized chain
satisfies `theorem3_end` iff the original does, or at least whose conclusion transfers back
(blocks with `ρ̃ ≤ 2` give `E`-blocks inside `D.unionRange 0 3`)? (b) the same question for
`IsCrookedIn'` itself: do extra (unforced) meetings in a general chain impose constraints beyond
`IsCrookedIvF`, so that the general-chain class is *smaller* than the faithful model (good: the
census over-covers) or do they only enlarge the hypothesis of the end clause (bad: under-covers)?
State the answer as a Lean theorem if it is a theorem (`theorem3_end_of_model : (∀ faithful
(ρ, σ), model clause) → ∀ chains, theorem3_end-statement`, or its failure).

**Q3 — The two-link forms, census.** Run the batch-87 census machinery for (a) S₂ (Bing's main
clause, no end clause) and (b) `Theorem3Literal` (both clauses), over the same corpus (K = 4,
n ≤ 13; K = 5, n ≤ 16; Bing's chains K ≤ 7), with the Q2 caveat stated. Any failure becomes a Lean
refutation through `realization` (a `native_decide` certificate as in `Census87Checks`, flagged in
the audit as before), entered in LEDGER §1 as "Bing 1948, Theorem 3 as printed". No failure:
report the counts.

**Q4 — Bing's proof, the seam.** Execute Bing's special-case construction literally — H from the
induction hypothesis (any H satisfying the IH's conclusion), h_u the first link containing d_h,
F := H(1, u−1) ⌢ (level-groups of D′, top to bottom) ⌢ D(k+1, n) — and decide whether F is always
a chain satisfying the clauses. Expected: not always; a certificate is a concrete crooked chain
(from the corpus or from `realization`) and an H satisfying the IH on D(1, h) for which F is not a
chain, or violates "two adjacent links" or the end clause. The two seams I see: h_{u−1} is known
only to lie in two adjacent links of E and to meet h_u ⊆ e_{r−2} + e_{r−1}, so it may lie in
e_{r−4} + e_{r−3} and meet two level-groups; and d_{k+1} ⊆ e₃ meets the groups e₁ + e₂ and
e₃∖e₂. If the construction can be read so that it works (a choice of H, or of the grouping, that
Bing left implicit and that always exists), say so and prove the reading if it is cheap; if the
reading needs exactly the end-time control that is open, say that. Also check the general case:
Bing writes "any link of F containing an end link of D(h, k)" where H is meant (typo), and the
regrouping has the same seam at h_{u−1}.

**Q5 — Assessment.** With Q1–Q4 in hand: is Bing's Theorem 3 as printed (i) proved, (ii) refuted,
or (iii) open; is the three-link end clause (`theorem3_end`) (i)/(ii)/(iii); and is Bing's *proof*
of Theorem 3 complete as written (the seam), with a Lean certificate if not. If both statements are
open, say what a proof would need in one paragraph — a statement, not a route — and whether
`theorem3_end` should remain the audited open target or be replaced by `Theorem3Literal` (my
inclination: keep `theorem3_end` as the sorry'd target, since nothing in the build depends on it,
and record `Theorem3Literal` as the Prop; David decides).

Not in scope: proving either open statement, unless Q2 or Q4 makes one of them fall out. No new
`sorry`. `fugate_cor1`, `treeLike_nonseparating`, `PlaneFacts` untouched.

## 3. Deliverables

1. `HPC/Fold/Recon121.lean`: the `def`s of Q1, the implications of Q1(c), any Lean theorems from
   Q2, any refutation certificates from Q3/Q4 (native_decide flagged); `#print axioms` in
   `axioms-batch121.txt`; `axioms.txt` regenerated (`sorryAx` stays at two).
2. Report: first line names the commission read; Q1–Q5 in order; census tables as in
   REPORT-batch87 §5; the ledger text for Theorem 3 (whichever of: refutation of the statement;
   defect in the proof with certificate; open with no counterexample).
3. `OPEN.md` item 1 updated only if its status changes.
