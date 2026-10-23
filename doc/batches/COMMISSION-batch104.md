# Commission: batch 104 — Bing's Theorem 11 (Duke 1951) by Fugate 1969, Case II

**Go!** Runs on top of the batch-102 delivery (or of batch 103's pruned tree, if that has run;
names are the same). Two files accompany this commission as separate uploads, not an archive:

* `COMMISSION-batch104.md` — this text (also pasted into the prompt);
* `Theorem11B.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Theorem11B.lean` and add `import HPC.Plane.Theorem11B` at the end of the root
  `HPC.lean`. No existing file is to be edited. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 102 and the correction this commission carries

Audited: Sorgenfrey's theorem and Nadler 11.25–11.35 proved; 11.28 as transcribed refuted
(`U − H ≠ ∅` needed); Fugate 1966 complete.

**Correction to batches 96–98.** Bing's sentence "`S − N` is the sum of two mutually separated
sets `H'` and `K'` such that `H'` contains `H − N` and `k₁, …, k_n` covers `K'`" does *not*
require `K' ⊇ K − g' − N`; batch 96's `not_separation_of_accumulates'` refutes a statement with
that extra clause, which was mine. Read with the implicit "`h₁, …, h_m` covers `H'`" (needed for
Bing's displayed chain in any case), the sentence asserts a separation of `S − N` with
`H − N ⊆ H' ⊆ h*` and `K' ⊇ S − h*`, which is exactly Claim 2 of Fugate 1969 (below), and it holds
in the organ (batch 98's `good_layer_terminal`). What Bing left unargued is this Claim 2 and the
choice of a point `p'` for which it holds; Fugate 1969 supplies both, choosing `Cl(B − A)` in
place of `K` and a terminal point of both halves in place of `p'`. So Theorem 11 is proved by
Fugate's Case II along Bing's own lines; the defects ledger for Theorem 11 is to be rewritten
accordingly (the report records what was used).

## 1. The source (Fugate 1969, pp. 384–392)

**Definition 1** = Fugate 1966 Definition 4 (`IsTerminalSub`). **Remark 1** = batch 100's
`inter_isTerminalSub_of_union`. **Lemma 1** = Fugate 1966 Lemma 2 (`fugate_lemma2'`);
**Lemma 2** = Fugate 1966 Lemma 3 (`isTerminalSub_iff_irreducible'`).

[Quotation moved to doc/sources/transcriptions/fugate69.md, §doc/batches/COMMISSION-batch104.md, 1. The text (Lemmas 3, 4; Theorem 2, Case II); batch 204.]

## 2. Items (the skeleton, in order)

1. **Lemma 3** (`isTerminalSub_of_union_terminal`), with the glosses resolved.
2. **Inductiveness** (`isTerminalSub_iInter`) and **Lemma 4, HD case**
   (`exists_terminal_point_of_isTerminalSub`): Brouwer reduction (batch 93's
   `exists_minimal_of_seq`) on "terminal in `M`, inside `K`"; a minimal terminal subcontinuum of
   a hereditarily decomposable `M` is a point by Lemma 3.
3. **The halves** (`halves_terminal`): `A = U ∪ g'`, `C = closure V` with `U`, `V` the sides of
   `g'` (batch 96's `exists_two_sides`, `sides_continua`); `closure V` is a continuum; `A ∪ C =
   univ` (since `V ∪ g' ∪ U = univ`); `A ∩ C ⊆ g'` (`U` and `V` are disjoint open, so
   `closure V ∩ U = ∅`); terminality from `inter_isTerminalSub_of_union` applied to `A ∪ C`
   (hypotheses: `A`, `C` hereditarily unicoherent — subcontinua of `S`; `A ∪ C = univ` atriodic
   and unicoherent — `BingS`).
4. **Claim 1** (`claim1_contains_inter`). Fugate's `f` is replaced as follows. For `t ∈ Q ∖ A`
   (so `t ∈ V`), `g_t = bingElt t` lies in `V`; the set `W(s) := g' ∪ g_s ∪ (V ∩ U_s)`, where
   `U_s` is the side of `g_s` containing `g'`, is "the elements between `g'` and `g_s`
   inclusive" — a continuum (it is `(closure of the region between) ∪ the two elements`; prove
   via the sides and Nadler 6.3, or via `W(s) = closure V ∩ (U_s ∪ g_s)`… — choose and record).
   Fugate's `s` with `½ < f(s) < f(t)`: an element `g_s` separating `g'` from `g_t` (Theorem 8
   (a) applied to `g'`, `g_s`, `g_t` for `s ∈ V' ∩ V` near `p`, where `V'` is the open set about
   `p`; the elements through points of `V'` near `p` are near `g'`… — the step "there is
   `s ∈ V ∩ f⁻¹(0, f(t)) ∩ (B − A)`" uses that `p ∈ Cl(B − A)` and that elements near `g'` lie
   between `g'` and `g_t`; prove it from upper semicontinuity (`bingElt_usc`) and (a): elements
   through points close to `p` lie in a small neighbourhood of `g'`, hence are separated from
   `g_t` by `g'` or lie between — state the lemma used). Then `Cl(B − A) ∩ f⁻¹[½, f(s)]` is
   `closure V ∩ W(s)`, and the triod-free argument is Fugate's.
5. **`exists_mu`**: Lemma 4 (HD) applied to `A ∩ C` in `A` gives a terminal point `μ` of `A` in
   `A ∩ C`; the paragraph "`K` is a terminal subcontinuum of `Cl(B − A)`" with `K = {μ}` gives
   `CondB C μ` (via Claim 1 and `isTriod_union_of_three`, batch 100, whose hereditary
   unicoherence hypothesis is `BingS`).
6. **Claim 2 and the chain** (`epsCoverable_of_halves`): chains from `fugate_lemma1` (batch 100)
   applied to `{μ}` (= condition B, `isTerminalSub_singleton_iff`) in `A` and in `C`, refining
   `ε/2`-chains from `ε/2`-coverability of the proper subcontinua `A`, `C` (minimal
   counterexample at scale `ε/2`? — no: the minimal counterexample is at scale `ε`; so take
   `E'`, `F'` to be `ε`-chains and shrink only `U`; Fugate's chain has links `E_i ∩ S`,
   `(F_y ∩ T) ∪ U` — the last has diameter `≤ diam F_y + diam U`; handle the mesh as batch 96
   did (separate small link for `U`, or `ε/2` throughout and a minimal counterexample at `ε/2`;
   choose, and state the statement actually proved, adjusting the skeleton's `ε/2`). The
   separation of `M − U` is Moore's theorem for the closed sets `A − U` and `M − E*`
   (`exists_closed_split_of_no_connected`, batch 101) with Claim 2; openness and adjacency as in
   batch 96's `epsCoverable_amalgam_gen` (trimming lemma `isSnakeLike_of_weak`, batch 101).
7. **Theorem 11** (`theorem11_1951`, `theorem11_1951_iff`): the minimal counterexample
   (`exists_minimal_notCoverable`), `BingS` on it (`bingS_subcontinuum`), an interior element
   (two end elements exist, `exists_two_endElts`; any third element is interior; existence of a
   third: elements are nowhere dense, so `S'` is not the union of two of them), the halves,
   `exists_mu`, Claim 2, contradiction. Necessity from batch 96.

Report each item *proved / refuted / open with the obstruction stated*; refutations first; the
ledger of Fugate's Case II (the glosses above and any others).

## 3. Deliverables

1. Items 1–7; `#print axioms` in `axioms-batch104.txt`, including `theorem11_1951`.
2. Report: first line names the commission read; items in order; the ledger.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
   `isArc_of_separatesPairs`; Fugate 1969 Case I, Lemmas 5–7, Theorem 3.

## 4. Next

The pruning pass (batch 103) if not yet run; then the defects ledger document.
