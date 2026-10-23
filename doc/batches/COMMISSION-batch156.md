# Commission: batch 156 — Part E, Hagopian 1976 I: §2, Lemmas 2–8; the consequences of Theorem 1

**Go!** This batch runs on top of the batch-155 delivery. Three files come with it, as separate
uploads:

* `COMMISSION-batch156.md`: this text, also pasted into the prompt.
* `Hagopian76A.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76A.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76A` at the end of `HPC.lean`.
* `hagopian1976.pdf`, for `doc/sources/`: C. L. Hagopian, *Indecomposable homogeneous plane
  continua are hereditarily indecomposable*, Trans. AMS 224 (1976), 339–350.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 §2 (batch 156)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 155

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** All statements are verbatim except four shape changes, each recorded:
  * `¬ … .Countable` for the nonexistent `Set.Uncountable`;
  * `hab` dropped in `hagopian75_lemma2`;
  * `hr0`, `ht1` dropped in `hagopian75_layer_invariant`;
  * `open Function in` before `moore_triod_theorem`.
* **Audit.** `axioms.txt` has 1286 lines, with `sorryAx` in none. There are 161 new theorems, all
  on the standard three axioms. Nothing is open.

**Accepted.**
* **Moore's triod theorem**, proved by his own two cases.
* **Lemma 1.** My sketch of the "separable" step is confirmed and is what you formalized.
* **Lemma 2 sufficiency** by a countable dense subfamily of Kuratowski's `D`, Cantor's theorem and
  `k(y) = inf {q : y ∈ D_q}`.
* **Theorem 1 ¶2.** The triod has core `B`, and `f(x)`, `g(x)` are taken in composants of `I` other
  than that of `x`.
* **¶¶9–11** by invariance of relative interior.
* **The two refutations.** `admissible_end_sets` and `arc_of_degenerate_layers` were my renderings
  of Thomas Theorems 8 and 21, not Hagopian's sentences. Both errors are mine, and the ledger
  records them under Part C (commission statements refuted).
  * The first needs the type A′ map: on `[0, 2]`, `max 0 (x − 1)` is admissible.
  * The second needs all layers degenerate: the `sin (1/x)` continuum is a counterexample.
* **No defect of Hagopian 1975.** The ledger records fifteen checks, most of them unargued but
  true. The counts stay at 21 false as printed and 14 defective proofs.

## 1. Where this sits

| batch | content |
|---|---|
| **156 (this one)** | Hagopian 1976 §2: Lemmas 2–8; Theorem 1 as a statement `Hagopian76Thm1`, with Theorem 2, the 1975 Theorem 1, Corollary and Theorem 2, and Bing 1960 for the plane derived from it |
| 157 | Lemma 9 and the quotient `R²/S` (Moore 1925 Theorem 22, `m25_theorem22`); decomposable accessibility (Bing 1960, p. 215); Theorem 1 set-up and Property 1 |
| 158– | Theorem 1: Properties 2–4 and the induction ("Following Bing [2, p. 225]"); discharge of `Hagopian76Thm1` |

Theorem 1 cites Mazurkiewicz 1929 (Fund. Math. 14; inaccessible composants). It is not yet in
hand and is requested for batch 157.

## 2. Items

**A. Definitions:** `IsMinimalAdmissible`, `layerSet`, `IsExtensionAway`, `extUnion` (`R(X, E)`),
`Rset` (`R(E)`), `IsEssential`, `toPt`, `IsPlaneChain`, `Follows`, `IsFree`,
`IsOrderedRefinement`.
* The end set of an extension is normalized to the layer over `0`.
* "Essential to `h[R(E)]`" in Lemma 7 is read as "`h⁻¹[H]` essential to `R(E)`". If that reading
  loses something, say so.

**B. `hagopian76_lemma2`** (from `hagopian75_lemma4`) and **`hagopian76_end_sets`** (from
`admissible_end_sets'`).

**C. `hagopian76_lemma3`.** Hagopian's proof is "follows from the argument presented in paragraphs
9 through 11 in the proof of Theorem 1 of [5]". The 1975 argument uses `ε` to keep `hk⁻¹[[r, t]]`
off the end sets. Lemma 3 has instead `U ∩ h[X ∪ Z] = ∅ = h[Y] ∩ (T ∪ V)`.
* Say whether the 1975 argument goes through with these hypotheses.
* If it does not, say whether Lemma 3 is still true as printed.
* If Lemma 3 is false, give the configuration and the corrected form that 1976 actually uses. Its
  uses are Lemma 5, and Property 3 on p. 347 ("By Lemmas 2 and 3, a homeomorphism `g` …").

**D. Lemma 4.** Prove `hagopian76_lemma4_layers` (the first paragraph), `hagopian76_lemma4`, and
`hagopian76_lemma4_seq`.
* Two steps of the main proof need writing out:
  * the triod "`H ∩ d⁻¹[[s, 1]]` would separate `F ∪ H` into three nonempty disjoint open sets";
  * "it is a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)".
* **The sequence form.** "Since `M` is second countable, there exists a monotone strictly increasing
  sequence `{Fᵢ}` … such that `R(X, E) = ⋃ Fᵢ`". A chain of closed sets with no maximum need not
  have a countable cofinal subfamily in general. Here it does: in a second-countable space, a
  strictly increasing well-ordered family of closed sets is countable, and any chain has a cofinal
  well-ordered subchain. Write out whichever argument you use.

**E. `hagopian76_lemma5`** (the decomposition is continuous), as `IsContinuousDecomp (Setoid.ker k)`.
The steps:
* "Since `A` is upper semicontinuous, `Y` contains `L`";
* "There exists a type A′ continuum `F` in `R(E)` that is the union of two extensions of `E` such
  that the end sets `T` and `V` of `F` miss `E` (Lemma 4)". The union of an extension away from `X`
  and one away from `Z` is of type A′; check this;
* "each element of `A` that is not an end set of `E` is an element of `B`";
* the choice of `h` and `i` with (1)–(3);
* Lemma 3.

**F. Lemma 6.** `hagopian76_closure_extUnion`, `hagopian76_lemma6`, and the two unnumbered claims
after it: `hagopian76_Rset_composant` ("Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`")
and `hagopian76_essential_typeA'`. Lemma 6 is the longest proof in §2. Its steps (pp. 341–343):
1. "`B` contains `X`" ("Since `E` is irreducible and `M` is hereditarily unicoherent, and since `X`
   does not have interior relative to `E`").
2. "The sets `X` and `C` are disjoint."
3. "Note that `B − C` is contained in `K`."
4. The sequence `{Fᵢ}`, the points `zᵢ`, and `c`.
5. "`c` belongs to `Cl R(X, E) − R(X, E)`", via the `δ`-homeomorphism `f` and "`f[L]` is a subset of
   `R(X, E)`".
6. `ε₁`, `h₁`, `N`, and "The sets `N` and `h₁⁻¹[N]` are disjoint" ("no element `Y` of the
   decomposition of `N` has the property that `h₁⁻¹[Y]` contains `N`"; "`R(E)` contains a continuum
   whose intersection with `C` is not connected").
7. `ε₂`, `h₂`, `P`, and the triod `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]`.
8. `Cl R(X, E) = Cl R(E)`, by the 1975 ¶2 triod argument
   (`hagopian75_no_indecomposable_interior` and its proof).

**G. `hagopian76_lemma7`.** The steps:
* the limit points `t`, `u`, `p` and the balls `A`, `B`;
* "By Lemma 2, an integer `i` and a homeomorphism `f` of `M` onto `M` exist such that a continuum
  `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`";
* `ε′` and `g`;
* "Note that `g[F] ∪ Hⱼ` is a triod in `M`".

**H. `hagopian76_lemma8`.** The steps:
* "Since `M` is atriodic, there exist open sets `A` and `B` in `G₁` and `Gₙ`, respectively, such
  that `E` is a component of `M − (A ∪ B)`";
* Moore 1962 Theorem 44, p. 15 (in `doc/sources/moore1962-excerpts.pdf`);
* the check that `{G₁, C ∩ G₂, …, C ∩ Gₙ₋₁, Gₙ}` is a chain, follows `E`, and is free.

If `n` is small (one or two links), say what happens.

**I. Consequences of Theorem 1**, each from the hypothesis `h1 : Hagopian76Thm1`:
* `hagopian76_theorem2`. The repository route is `jones55_two_domains'`, so Gordh 1975 and Jones
  1951 are not needed. Confirm this.
* `hagopian75_corollary`, `hagopian75_theorem1`, `hagopian75_theorem2` (using `jones55_theorem2'`,
  `jones55_elements_indecomposable'` and `jones55_c`).
* `bing60_plane`.

When `Hagopian76Thm1` is proved, these become unconditional. So do Hagopian 1975 Theorem 1,
Corollary and Theorem 2 as printed, and Bing 1960 for bounded plane continua.

## 3. Places to check (candidate ledger entries)

All are from page images, pp. 339–344 and 349.

1. **p. 339:** "A *continuum* is a nondegenerate compact connected metric space." Type A′ is defined
   again here with "a monotone upper semicontinuous decomposition" (1975 said "connected sets").
   Record that the two definitions agree.
2. **p. 340:** "No proper subcontinuum of `E` intersects both `X` and `Z` [14, Theorem 8, p. 14]."
   This is true for the decomposition (type A′ map). Record that it fails for an arbitrary
   admissible map, by `not_admissible_end_sets`.
3. **p. 340, Lemma 3:** the hypotheses differ from those of the cited 1975 argument (item C).
4. **p. 341, Lemma 4:**
   * "Since the decompositions of `E` and `F` are minimal, each element of the decomposition of `E`
     (except possibly `k⁻¹(1)`) is an element of the decomposition of `F`";
   * the triod `H ∩ d⁻¹[[s, 1]]`;
   * "a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]`".
5. **p. 341, Lemma 5:** the union of two extensions is of type A′ with end sets missing `E`; "Each
   element of `A` that is not an end set of `E` is an element of `B`"; the choice (1)–(3).
6. **p. 342, Lemma 6:** "Since `M` is second countable, there exists a monotone strictly increasing
   sequence". Record the argument.
7. **pp. 342–343, Lemma 6:** steps 1–8 of item F, each recorded.
8. **p. 343:** "Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`" and "every continuum
   essential to `R(E)` is of type A′ (Lemma 5)". Both are unnumbered.
9. **pp. 343–344, Lemma 7:** the homeomorphism `f` and the triod `g[F] ∪ Hⱼ`.
10. **p. 344, Lemma 8:** the open sets `A`, `B`, and the final sentence.
11. **p. 349, Theorem 2:** "[4], [6]". Record the repository route.
12. **p. 339, abstract:** "every homogeneous plane continuum that has a hereditarily decomposable
    subcontinuum is a simple closed curve". This is 1975 Theorem 2 (item I).

## 4. Deliverables

1. Items A–I.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch156.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 157 (Lemma 9 and Theorem 1 up to Property 1, pp. 344–346). Say how
     each step goes with what is available:
     * the equivalence relation `S` and "we can assume that the quotient space `R²/S` is `R²`
       [12]" (`m25_theorem22`; check `MooreDecomp`: the elements are the layers of `E` and points,
       nonseparating because "no proper subcontinuum of `M` separates `R²` [5, Lemma 1 (second
       paragraph of proof)]");
     * that `π[E]` is an arc;
     * "decomposably accessible from a side" (Bing 1960, p. 215, to be supplied) and a Lean shape
       for "abut on the same side of the arc `π[E]`";
     * Lemma 9's chain `G` with `π[Gᵢ]` open disks, and Moore 1962 Theorem 28, p. 156;
     * "Since `M` is homogeneous, we can assume without loss of generality that `k⁻¹[(0, 1)]` is
       accessible from `R² − M`";
     * Property 1.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`; sources go to
   `doc/sources/`. Nothing goes at the root.
