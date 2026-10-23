# Commission: batch 114 — the covering step of Bing 1948, Theorem 14, by Lehner's Lemma 3

**Go!** Runs on top of the batch-113 delivery (or of 112, if 113 is not yet in: the files are
independent). Three files accompany this commission as separate uploads, not an archive:

* `COMMISSION-batch114.md` — this text (also pasted into the prompt);
* `Lehner.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/PseudoArc/Lehner.lean` and add `import HPC.PseudoArc.Lehner` at the end of the root
  `HPC.lean`. Existing files to be edited: `HPC/PseudoArc/Theorem14.lean` — **delete** the open
  `covering_step` (with its `-- OPEN` marker) and `exists_description_covering`, which the new
  file restates under the same names with proofs (the names of the namespaces must match what
  `Axioms.lean` prints: `HPC.Description.covering_step`, `HPC.Description.exists_description_covering`;
  adjust the skeleton's namespaces to the repository's, and likewise `CoveringStep`); `theorem14`
  stays in `Theorem14.lean`, still `sorry` (its remaining work is batch 115, see §4);
  `Axioms.lean`/`axioms.txt` (`covering_step` leaves *Open targets*, `exists_description_covering`
  leaves *Consequences*; both go to the Bing 1948 group); `OPEN.md` item 2 closed ("item 2: closed
  in batch 114", numbers of the other items unchanged); `README.md` one line if it mentions the
  covering step;
* `lehner1961.pdf` — the paper. Read pp. 369–370 (definitions: chain, "chain from P to Q",
  consolidation, subchain `D(i, j)`, `D(P, Q)`, `D*`, mesh, Lebesgue number, crooked, pattern),
  p. 375 (Theorem 2, Theorem 3, Lemma 3) and p. 376 (the proof of Lemma 3 for `n = 2`) from the
  scan; the transcription below is mine, the page is the authority.

The report names the commission read in its first line.

## 0. On batch 113

(Audited separately when it arrives; nothing here depends on it.)

## 1. The source

**Lehner's definitions (p. 370).** A chain `D = [d_1, …, d_m]`: open sets, `d_i ∩ d_j ≠ ∅ iff
|i − j| ≤ 1`, and the closure of `d_i` meets the closure of `d_j` only if `|i − j| ≤ 1` (the
repository's `Chain` has only the first clause; where the proof below uses closures, say so).
"If `P` and `Q` are points that belong to `d_1` and `d_m` respectively but to no other links, `D`
is a chain from `P` to `Q`" (= `IsFrom`). `D(i, j)` is the subchain with end links `d_i`, `d_j`;
`d_P` the link containing `P` when it lies in exactly one; `D(P, Q)` the subchain from `d_P` to
`d_Q`; `D*` the union. Crooked (p. 370) is Bing's definition (= `IsCrookedIn'`). Mesh, Lebesgue
number as usual.

**Theorem 2 (Moise).** The pseudo-arc is homeomorphic to each of its nondegenerate subcontinua.
(Used only as: a nondegenerate subcontinuum of a pseudo-arc is a pseudo-arc.)

**Theorem 3 (Bing).** If the pseudo-arc `M` is irreducible between `P` and `Q` there is a
sequence of chains `D_1, D_2, …` from `P` to `Q` such that each `D_i` is a consolidation of some
`W_m`, `D_{i+1}` is crooked in `D_i`, the mesh of `D_i` is less than `1/i`, and any link of `D_i`
that contains a link of `D_{i+1}` also contains the closure of that link.

[Quotation moved to doc/sources/transcriptions/lehner61.md, §doc/batches/COMMISSION-batch114.md, Lemma 3 and its proof (pp. 375–376); batch 204.]

**Mapping to the repository.** `M = Δ.M` with its description `Δ` (Lehner's `W_m = Δ.D m`).
`H_1 = W`, `P_1 = P'`, `Q_1 = R`. `H_2` is to be *chosen*: a nondegenerate proper subcontinuum
irreducible between some `P_2` and `Q_2 = Q'` — take any `P_2 ≠ Q'` in the composant of `Q'`
(composants are dense) and `exists_irreducible` inside a proper subcontinuum containing both; then
`H_2 ⊆ composant Q'`, so `H_1 ∩ H_2 = ∅` and `M` is irreducible between them (a continuum meeting
both composants is `M`). The chain `D` of the lemma is the `F` of `CoveringStep`: from `P'` to
`Q'`; a consolidation of `G = Δ'.D j`, itself a consolidation of some `Δ.D k`
(`exists_description_consolidating`, `IsConsolidationOf.trans`); `D(P_1, Q_1) = [d_1, …, d_{m_1}]`
contains `H_1 = W` and is a chain from `P'` to `R` (= `CoversUpTo`); mesh `≤ max(mesh E_1, mesh
E_2, mesh G) < ε`; closures inside links of `Δ.D L` by taking `ε` below the Lebesgue number of
`Δ.D L` on the compact `Δ.M` with a margin (the links of `D` lie in links of `E_1`, `E_2` or are
links of `G`; `E_i` from `exists_epsChain_of_irreducible` at mesh `ε`).

## 2. Items

1. `isPseudoArc_of_subcontinuum`, `not_mem_composant_of_irreducible`,
   `exists_epsChain_of_irreducible`, `IsConsolidationOf.trans`, `exists_description_consolidating`.
   For the `ε`-chain of `W`: `isPseudoArc_of_description` makes `Δ.M` a pseudo-arc,
   `isPseudoArc_of_subcontinuum` makes `W` one, `exists_description_of_chainable_HI` on `W` gives
   a description from `P'` to `R` (its end points are in different composants of `W` by
   `not_mem_composant_of_irreducible`), and a deep level is the chain — with the links that miss
   `W` removed if the repository's descriptions allow such links (then renumber; the result is
   still a chain from `P'` to `R` since `W` is connected and contains both). `E_1* ∩ E_2* = ∅`:
   every link of `E_i` meets `H_i` and has diameter `< ε < dist(H_1, H_2)/2`.
2. **`lehner_lemma3_two`.** Points to settle, in order:
   * the indices `r_1, s_1, t_1` and the inequalities `5 ≤ r_1 ≤ s_1 ≤ t_1 − 3`: `r_1 ≥ 5` because
     `F(1, 4)` meets `H_1` (at `P'`), hence lies in one link of `E_1`, which contains `P'`, hence
     is `e(1)_1`, which does not contain `R` (`m_1 ≥ 2`); `s_1 ≤ t_1 − 3` by the 4-link property at
     `f_{s_1}`; `r_1 ≤ s_1` trivially. State what "`F(1, t_1)` is contained in `E_1`" means (each
     link of `F(1, t_1)` inside some link of `E_1`) and check it is monotone in `t_1`;
   * the symmetric indices on the `H_2` side, and `t_1 + 1 < t_2` (the links of `F` in `E_1*` and
     in `E_2*` are disjoint families, and `F` is a chain);
   * crookedness of `G` in `F` applied to `g_1 ⊆ f_1` (as `P' ∈ g_1 ∩ f_1`: the hypothesis of
     `IsCrookedIn'` is that `g_1` *meets* `f_1`) and `g_{w_1}` meeting `f_{t_1}`, with
     `1 + 2 < t_1`: the `Between` form gives `x_1 ≤ y_1` in `[1, w_1]` with `g_{x_1} ⊆ f_{t_1 − 1}`,
     `g_{y_1} ⊆ f_2`. Note Lehner's `y_1 > x_1` is strict; the repository's `Between` may allow
     equality — if `x_1 = y_1` then `f_{t_1−1} ∩ f_2 ≠ ∅`, impossible for `t_1 ≥ 5`;
   * `H_1 ⊆ G(1, x_1)*`: `H_1` is connected, contains `P' ∈ g_1`, and misses `g_{x_1}`; the links
     of `G` meeting `H_1` form an interval of indices (links are open, `H_1` connected) containing
     `1` and not `x_1`;
   * the link `g_{z_1}` between `g_{x_1}` and `g_{y_1}` inside `f_{r_1}`: the index of the `F`-link
     containing each `G`-link (closure in a link of `F`; choose one) changes by at most one along
     `G` (adjacent `G`-links meet, so their `F`-links meet or coincide — if a `G`-link lies in two
     `F`-links the choice must be made consistently; say how), so some `G`-link between `x_1` and
     `y_1` lies in `f_{r_1}` (discrete intermediate value); `f_{r_1} ⊆ e(1)_{m_1}` because `f_{r_1}`
     lies in a link of `E_1` (`r_1 ≤ t_1`) and contains `R`, which is only in `e(1)_{m_1}`;
   * the chain `D`: `d_i := ⋃ {g_l : l ≤ z_1, g_l ⊆ e(1)_i}` for `i ≤ m_1` — with an assignment
     of each `g_l` (`l ≤ z_1`) to exactly one `i` (a link may lie in two adjacent links of `E_1`;
     choose so that consecutive `G`-links go to the same or adjacent `i`, and `g_{z_1}` to `m_1`);
     the middle links `g_{z_1+1}, …, g_{z_2−1}` unchanged; the last `m_2` links from `G(z_2, v)` and
     `E_2`. Verify: links open; adjacent links meet (the consolidated parts: for each `i < m_1` some
     consecutive pair of `G`-links is assigned to `i, i+1`; junction `d_{m_1} ⊇ g_{z_1}` meets
     `g_{z_1+1}`); nonadjacent links disjoint (within the consolidated part because `E_1` is a chain
     and the pieces lie in its links; between the parts because `G` is a chain; `d_{m_1 − 1}` misses
     `g_{z_1 + 1}` since its `G`-links have index `≤ z_1 − 1` — check that `g_{z_1}` is not
     assigned to `m_1 − 1`); `IsFrom P' Q'` (`P'` only in `g_1 ⊆ d_1`; `Q'` only in `g_v`); the
     consolidation relation; mesh; `CoversUpTo`: `W ⊆ G(1, x_1)* ⊆ d_1 ∪ ⋯ ∪ d_{m_1}` and
     `[d_1, …, d_{m_1}]` is from `P'` to `R` (`R ∈ e(1)_{m_1}` only, and `R ∈ G(1, x_1)*`);
   * closures inside links of `Δ.D L`: choose `ε` and `j` so that every link of `D` has closure of
     diameter below the Lebesgue number of `Δ.D L` (as a cover of the compact `Δ.M`; the links of
     `D` lie in `Δ.M`? — if not, intersect or argue with `closure_subset` of `Δ'`).
   Record every place where Lehner's one page needs a fact he does not state (the two-link
   ambiguity, the strictness of `y_1 > x_1`, `m_1 ≥ 2`, the closure condition).
3. `covering_step`, `exists_description_covering` (one line each); the moves and the audit.

Report each item *proved / refuted / open with the obstruction stated*; refutations first; the
ledger of Lehner's proof.

## 3. Deliverables

1. Items 1–3; `#print axioms` in `axioms-batch114.txt`; `axioms.txt` regenerated. Expected
   `sorryAx`: the count drops by two (`covering_step`, `exists_description_covering`); `theorem14`
   and `theorem15` remain.
2. Report: first line names the commission read; items in order; the ledger.
3. Not attempted: `theorem14` itself (batch 115), `theorem3_end`, `fugate_cor1`.

## 4. Next

Batch 115: `theorem14` from two covering descriptions — Bing's alternating construction
(COMMISSION-batch83.md §2, §3.4: the base rung, the point `A`, three applications of Theorem 5,
`Y_{1,2}` as a chain, Theorem 11 with the tracking clause), now that the covering descriptions
exist on both sides; alternatively Lehner's Theorem 6 (`n = 2`, `H_{1,2} = {Q_1}` made nondegenerate
by his device on p. 387), whose proof is §§5–6 of the paper.
