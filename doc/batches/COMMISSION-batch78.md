# Commission: batch 78 — Bing's Theorem 4, from Theorem 3 with the end-link clause

**Go!** Runs on top of the batch-77 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch78.md` — this text (also pasted into the prompt);
* `Theorem4.lean` — a skeleton of two statements, both `sorry`, both work items. Save it as
  `HPC/Fold/Theorem4.lean` in the workspace and add the line `import HPC.Fold.Theorem4` at the end
  of the root `HPC.lean`. Nothing else in the workspace is to be replaced.

The report names the commission read in its first line.

## 0. On batch 77

Audited: `theorem3` and `s3_general` closed by `Z77.s3_zig`; statements unchanged; axiom audit
`[propext, Classical.choice, Quot.sound]` throughout (`axioms-batch77.txt`); no live `sorry` in the
repository before this batch adds two.

## 1. What Bing proves, and where Theorem 4 sits

Bing 1948 (Duke Math. J. 15, 729–742). His fine chain is `D = [d_1, …, d_n]`, his coarse chain
`E = [e_1, …, e_m]`; the repository's names are exchanged (fine `E`, coarse `D`). Below, Bing's
text is quoted in his names and the Lean is in the repository's.

**Theorem 3 (Bing, p. 732).** *If the chain `D` is crooked in the chain `E = [e_1, …, e_m]` and
`d_i` is a particular link of `D`, then there is a chain `F` such that `F` is a consolidation of
`D`, `d_i` is contained in only the first link of `F`, each link of `F` is a subset of the sum of
two adjacent links of `E`, and any link of `F` containing an end link of `D` which intersects
`e_1` or `e_m` is a subset of `e_1 + e_2` or `e_{m−1} + e_m`.*

The repository's `theorem3` (three-link form) has the first three conclusions and **not the
fourth**, the end-link clause. Theorem 4 needs it.

**Theorem 4 (Bing, p. 733).** *If `D = [d_1, …, d_n]` is a chain crooked in the chain
`E = [e_1, …, e_m]` and `D(r, s)` is a subchain of `D` such that a link of `D(r, s)` intersects
`e_1` and a link of `D(r, s)` intersects `e_m`, then there is a chain `F` such that `F` is a
consolidation of `D`, each element of `F` is a subset of the sum of two adjacent links of `E`,
`d_r` is contained in only the first link of `F`, and `d_s` is contained in only the last.*

[Quotation moved to doc/sources/transcriptions/bing48.md, §doc/batches/COMMISSION-batch78.md, Bing's proof of Theorem 4; batch 204.]

**Where Theorem 4 is used.** Theorem 13 (homogeneity, p. 740) applies it twice per step to get
chains from `R` to `S` that consolidate a fine chain of the description with small mesh; its
conclusion is consumed only through "each link in the sum of two adjacent links" (mesh) and
"`d_r` in only the first link, `d_s` in only the last" (a chain from `R` to `S`). Theorems 5, 6
(pattern following) and 10–12 do not use it. Theorems 7, 8, 9 feed only Theorems 14, 15.

## 2. Targets

1. `theorem3_end` (`Theorem4.lean`): `theorem3` with the end-link clause, three-link form.
2. `theorem4` (`Theorem4.lean`): Theorem 4 in the block reading, three-link form, from
   `theorem3_end` by Bing's splice.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 3. The splice in the block reading, and what it needs

Write `ρ(t)` for the least index of a link of `D` containing `E.link t` (`Refines.minIdx`), band
`[L, H]`. Take `h` the first index in `[r, s]` whose link meets `D.link 0` (so `ρ(h) ≤ L + 1`), `k`
the first whose link meets `D.link (k−1)` (`ρ(k) ≥ H − 1`); Bing's convention `h < k` is one
orientation, the other is the mirror. `theorem3_end` at basepoint `r` on the subchain `E.sub 0 h`
(crookedness restricts to subchains: `IsCrookedIn'.sub`) gives blocks `H_0, H_1, …` with `r` in
`H_0` and the block `H_u ∋ h` inside `D.unionRange 0 3`; at basepoint `s` on `E.sub k (n−1)`
reversed, blocks `G_0, G_1, …` with `s` in `G_0` and `G_v ∋ k` inside the top three links. The
middle `D'` — every link of `E` in neither `H_0 ∪ … ∪ H_{u−1}` nor `G_0 ∪ … ∪ G_{v−1}` — is a
contiguous stretch of `E` (a prefix and a suffix are removed), contains `h` and `k`, and is
consolidated by level: group `0` = links of `D'` with `ρ ≤ L + 2`, group `j` = links at level
exactly `L + 2 + j` for the interior levels, last group = links with `ρ ≥ H − 2`. The schedule
is `β'(t) = ` the `H`-block index on the prefix, `u − 1 + 1 + ` the group index on `D'`, and the
reversed `G`-index at the end. Facts to be checked in the proof, each a Lipschitz or containment
statement: consecutive groups meet because `ρ` is 1-Lipschitz on the contiguous `D'`; the block
`H_{u−1}` is adjacent in `E`-index only to the first link of `H_u`, and `H_u ⊆ D.unionRange 0 3`
puts that link in group `0`; every group lies in three consecutive links of `D`; `β'` is
surjective because it is 1-Lipschitz with `β'(r) = 0`; `β'(s)` is the last value.

**The end-link clause is what makes `H_u` land in group 0.** Without it `H_u` may contain a link
at level `L + 3`, adjacent to `H_{u−1}`, which the level grouping would place two times later.

## 4. Questions, asked as questions

1. **The end-link clause from the jump zigzag.** In level terms the clause is: for the terminal
   index `h` of an arm, `ρ(h) ≤ L + 1` implies the walk value at the arm's itinerary position
   `c(β(h)) ≤ L + 1` (mirror at `H`). Checked against `Z77`: on a down-leg `a → t` with the arm
   finished (Proposition 5.5 (2) of the exposition) the arm at `L + 1` forces `t ≤ L − 1` and the
   walk value is `L + 1`; at a passage the value is `t ≤ L`; but an arm at level `L + 1` **on an
   up-leg from `b = L + 2`** (reached after a down phase with turning level `L + 2` and passage at
   `L + 3`) sits at leg position `0` with walk value `L + 2`, and its block reaches level `L + 3`.
   So the clause does not follow from `s3_zig` as it stands. Whether it follows from a modified
   zigzag — a final phase added for a terminal link, a different choice at the down phase that
   precedes the arm's end, or a post-processing of the fold — or whether Theorem 4's splice can be
   rearranged to tolerate `c(β(h)) = L + 2` (say by dissolving `H_{u−1}` as well, or by taking
   `h` to be the first index at level exactly `L` when one exists in `[r, s]`), is the question.
   Either resolution is acceptable; the statement `theorem4` is the target, `theorem3_end` is one
   route to it and is itself worth having because it is what Bing proves.
2. **Meets versus lies in.** Bing's hypotheses say a link *intersects* `e_1`; the level sequence
   records only containment (`ρ`, `σ`). The skeleton states the hypotheses with `Nonempty`
   intersections and the end clause's antecedent likewise. The proof reads them through
   `minIdx_near_of_inter` (`ρ(h) ≤ L + 1`). If a cleaner formulation is `ρ(h) ≤ L + 1` directly,
   both may be stated with the implication between them proved.
3. **A chain from `R` to `S`.** Theorem 13 takes `D_k(R, S)`, "the subchain of `D_k` from `R` to
   `S`", and needs Theorem 4's `F` to be a chain from `R` to `S` (Bing's definition, p. 729: `R`
   in the first link and no other). If `R` lies in two adjacent links `d_r, d_{r+1}` of the fine
   chain, `d_r` in only the first block does not put `R` in only the first block. Is the
   conclusion `β'(r) = 0` enough for Theorem 13's use, or does Theorem 13 need `β'(r) = β'(r+1)
   = 0` when `R ∈ d_r ∩ d_{r+1}` (equivalently, the freedom to choose `r` so that `R` lies in
   `d_r` alone)? A statement of Theorem 13's hypothesis on the subchain, in Lean, settles it; no
   proof of Theorem 13 is asked.
4. **Theorem 10.** Every subcontinuum of `M` is indecomposable (p. 737–738, from the definition of
   crooked alone). Not a target; the report may state it in Lean against `Description` if the
   vocabulary (subcontinuum, indecomposable) is already in scope, and say what is missing if not.

No opinion is offered on §4.1 beyond the fact recorded there.

## 5. Deliverables

1. `theorem4` and, if obtained, `theorem3_end`, `sorry`-free, with `#print axioms` in a file
   `axioms-batch78.txt`; the skeleton's statements may be reshaped as §4.2 allows, with every
   change recorded.
2. Report: first line names the commission read; any counterexample first; then §2; then §4 1–4.

## 6. Not in this batch

Theorem 5 (pattern following) and Theorem 6 — the next batch; Theorem 13's proof; Theorems 8, 9,
14, 15; the 1951 reduction; anything about spans, walks or censuses of the Theorem-3 campaign.
