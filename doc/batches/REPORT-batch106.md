Commission read: `COMMISSION-batch106.md` — batch 106, Duke 1951 Theorem 12 (B ⇒ A), Theorem 13 in full, and the "two end points" claim.

# Report, batch 106

**Refutations: none.** All six items of the skeleton are proved, with no `sorry`, and no
statement was changed. `lake build HPC` succeeds (8286 jobs). It reports exactly the five existing
`declaration uses sorry` warnings: `theorem3_end`, `covering_step`, `theorem14`,
`exists_tame_chain_near` and `fugate_cor1`. None of them comes from the new file.

## 0. Files

* `HPC/Plane/Thm12B.lean`: the skeleton, saved as asked. Its proofs are filled in, and its
  docstring header now says that every item is proved and no statement changed.
* `HPC.lean`: `import HPC.Plane.Thm12B` is added as the last line.
* `HPC/Plane/Theorem11B.lean`: the stale docstring sentence naming the deleted
  `theorem11_1951_of_T10'` (commission §0) now says it was deleted in batch 105. This is a
  docstring-only change.
* `Axioms.lean`: six lines are added to the Duke group, after Theorem 14. `axioms.txt` was
  regenerated.
* `README.md`: **unchanged**. Its summary of the Duke paper does not list Theorem 12 as half
  done; it mentions only Theorem 11. The commission's condition does not apply.
* Filing:
  * the commission is now `doc/batches/COMMISSION-batch106.md`;
  * the uploaded skeleton is `doc/batches/skeletons/Thm12B.lean`;
  * the newer notes upload replaces `doc/theorems-3-4-scheduling.md`;
  * the audit script and its output are `doc/batches/audits/Axioms106.lean` and
    `doc/batches/audits/axioms-batch106.txt`;
  * the pre-edit audit is kept as `doc/batches/audits/axioms-before-batch106.txt`.

## 1. Item 1: `condA_of_condB`, `theorem12_1951`

`condA_of_condB` follows the commission's replacement route exactly. Let `W ⊆ M` be a nondegenerate
subcontinuum through `p`.

1. `W` is snake-like (`isSnakeLike_of_subcontinuum`). Hence it is atriodic and hereditarily
   unicoherent (`isAtriodic_of_isSnakeLike`, `isHereditarilyUnicoherent_of_isSnakeLike`).
2. Condition B for `M` at `p` restricts to condition B for `W` at `p`. This is immediate, since
   subcontinua of `W` are subcontinua of `M`.
3. By `isTerminalSub_singleton_iff`, `{p}` is a terminal subcontinuum of `W`.
4. `isTerminalSub_iff_irreducible` (⇒), with `B := W`, gives `p' ∈ {p}` and `q` such that
   `{p} ∪ W` is irreducible between `p'` and `q`. Here `p' = p` and `{p} ∪ W = W`.
5. Then `q ≠ p`. If `q = p`, irreducibility applied to the subcontinuum `{p}` gives `{p} = W`,
   which contradicts nondegeneracy.

`theorem12_1951` combines this with batch 85's `condB_of_condA`.

## 2. Item 2: `theorem13_1951`, `theorem13_1951'`

* `theorem13_1951`: (⇒) is `condB_of_endPoint` followed by `condA_of_condB`; (⇐) is
  `endPoint_of_condA` (batch 99, through Theorem 10).
* `theorem13_1951'` is `theorem13_1951` followed by `theorem12_1951`.

## 3. Item 3: `exists_two_endPoints_irreducible`, `exists_oppositeEndPoints_of_hd`

`exists_two_endPoints_irreducible` follows the commission's route:

1. `BingS S` is assembled from the instances `ConnectedSpace S` and `Nontrivial S`, from the
   necessity half of Theorem 11 (`isAtriodic_of_isSnakeLike`,
   `isHereditarilyUnicoherent_of_isSnakeLike`), and from `hd`.
2. `exists_two_endElts` gives `a`, `b` with `bingElt a ≠ bingElt b`, both end elements.
3. `theorem9_1951` gives condition-A points `p ∈ bingElt a` and `q ∈ bingElt b`.
4. `p ≠ q`, because distinct elements are disjoint (`bingElt_disjoint`).
5. `p` and `q` are end points by `endPoint_of_condA`.
6. `S` is irreducible between `p` and `q`. A subcontinuum `K` containing both meets the two end
   elements `bingElt p = bingElt a` and `bingElt q = bingElt b`, so `K = univ` by
   `bingElt_irreducible` (Theorem 8 (c)). The end-element hypotheses are moved from `a`, `b` to
   `p`, `q` with `IsEndElt.of_eq`.

`exists_oppositeEndPoints_of_hd` then applies `theorem14_1951`.

## 4. Item 4: audit and ledger notes

**Audit.**
* `axioms.txt` has **235 lines**: the 229 lines from before plus the 6 new ones.
* The diff against `axioms-before-batch106.txt` consists only of the six added lines.
* `sorryAx` appears in exactly **9** lines, as before.
* All six new declarations depend only on `[propext, Classical.choice, Quot.sound]`
  (`axioms-batch106.txt`).

**Ledger notes** (for `LEDGER.md`; not edited this batch, since the commission lists no edit to it).

1. *Theorem 12, B ⇒ A: route taken.* Bing cites "Theorem 5 of [4]" (Amer. J. Math. 70, 1948),
   which is not available here. The citation is replaced by Sorgenfrey's theorem through Fugate's
   Lemma 3 (⇒) (`isTerminalSub_iff_irreducible`). This is the route taken, not a defect in Bing's
   proof.
   * The replacement needs `M'` to be atriodic and hereditarily unicoherent. It therefore proves
     Theorem 12 for snake-like `M` only, which is the setting of the skeleton and of §5 of the
     paper.
   * Bing's own argument, through [4], does not visibly use snake-likeness. This is recorded as
     a restriction of the formal statement, not of the paper.
2. *Theorem 12, B ⇒ A: one step left implicit.* Bing's argument shows that `M'` is irreducible
   from `p` to `q`, but condition A also requires `q ≠ p`. In the formal route this follows from
   nondegeneracy, because irreducible between `p` and `p` forces `M' = {p}`. In Bing's text it
   is built into "`q` of `M' − p`".
3. *Theorem 13: slip in the text.* "The sufficiency follows from Theorems 10, 11, and 12."
   Theorem 11 plays no role; Theorems 10 and 12 are what is used (`endPoint_of_condA` rests on
   Theorem 10, and condition B is converted through Theorem 12).
4. *The unnumbered claim (p. 661): steps the text leaves out.*
   * "From Theorems 8, 9, and 13" also needs the following:
     * the existence of two distinct end elements (Moore's non-cut-point theorem in the
       decomposition space, `exists_two_endElts`);
     * the fact that `S` satisfies the standing hypotheses of §4 (atriodic and hereditarily
       unicoherent: the necessity half of Theorem 11), with hereditary decomposability as the
       only extra assumption;
     * disjointness of distinct elements, for `p ≠ q`.
   * Of Theorem 13 only the sufficiency half for condition A is used.
   * Irreducibility between the two end points is Theorem 8 (c) applied directly.
   * Bing's next sentence (opposite end points) is Theorem 14 (`theorem14_1951`).

## 5. Not attempted

The five open targets.
