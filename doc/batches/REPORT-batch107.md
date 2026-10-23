Commission read: `COMMISSION-batch107.md` — batch 107, Duke 1951 Theorem 5 (uncountably many disjoint plane copies of a snake-like continuum).

# Report, batch 107

**Refutations first: one.** The skeleton's `squeeze_stdRect_subset`
(`closure (squeeze b '' stdRect j) ⊆ stdRect j`) is **false as stated**, for every `b` and `j`.
The squeezes fix the first coordinate, so the closure of the image contains
`(2j, (1/2 + c)/3)` on the left side of the rectangle, and `stdRect j` is open. The negation is
proved (`not_squeeze_stdRect_subset`). The statement is commented out in place with the reason, and
replaced by `squeeze_image_stdRect_subset` (`squeeze b '' stdRect j ⊆ stdRect j`, no closure),
which is all the construction needs: the "closure inside" requirement of the tree step comes from
`t4_step` itself, applied to the squeezed stage. The commission's phrase "closures inside
`stdRect j`" is wrong for the same reason; nothing downstream used it.

Everything else is **proved**, with no `sorry`. `lake build HPC` succeeds (8287 jobs) and reports
exactly the five existing `declaration uses sorry` warnings (`theorem3_end`, `covering_step`,
`theorem14`, `exists_tame_chain_near`, `fugate_cor1`). None comes from the new file. The only
`sorry` text in `HPC/Plane/Thm5.lean` is inside the commented-out false statement.

## 0. Files

* `HPC/Plane/Thm5.lean`: the skeleton, saved as asked, all proofs filled in. Header updated to list
  the two shape changes.
* `HPC.lean`: `import HPC.Plane.Thm5` added as the last line.
* `HPC/Plane/T4.lean`: **not edited.** The factored homeomorphism argument lives in `Thm5.lean`
  (see item 3), so no refactoring of `T4.lean` was needed and `exists_homeomorph_tN` is untouched.
* `Axioms.lean`: two lines (plus a comment) added to the Duke group, after Theorem 4.
  `axioms.txt` regenerated.
* Filing: commission → `doc/batches/COMMISSION-batch107.md`; skeleton →
  `doc/batches/skeletons/Thm5.lean`; the newer notes upload (`theorems-3-4-scheduling(14).md`)
  replaces `doc/theorems-3-4-scheduling.md`; audit script and output →
  `doc/batches/audits/Axioms107.lean`, `doc/batches/audits/axioms-batch107.txt`; pre-edit audit →
  `doc/batches/audits/axioms-before-batch107.txt`.

## 1. Item 1: squeezes — proved (with the refutation above)

* `squeeze b : Pt ≃ₜ Pt`, `(x, y) ↦ (x, (y + c_b)/3)` with `c_false = 1/2`, `c_true = 7/4`
  (`squeezeShift`); inverse `(x, y) ↦ (x, 3y − c_b)`.
* `squeeze_snd_bounds`: `[0, 1]` goes into `[1/6, 11/12]`.
* `squeeze_image_stdRect_subset` (corrected form of `squeeze_stdRect_subset`) and
  `squeeze_image_zone_subset` (each zone into itself; needed for the zone clause, item 2).
* `squeeze_disjoint`: as stated. The `y`-ranges `(1/6, 1/2)` and `(7/12, 11/12)` are disjoint.
* `not_squeeze_stdRect_subset`: the refutation.

## 2. Item 2: `t4_step_branch` — proved, shape changed

Route as commissioned. `t4_step` is applied to `⟨S.m, S.C, (squeeze b).trans S.Φ, S.hm, S.hC⟩`.
Its tame chain is `S.Φ '' (squeeze b '' stdRect j)`, which gives the new inclusion clause.

**Shape change: the zone clause is kept**, in the form
`diam (link t) ≤ ε ∨ ∃ k < S.m, link t ⊆ S.Φ '' zone k`. It is needed for the mesh estimate of
the plane chains (`glink_diam`): the inclusion clause alone only bounds a new link by an old one,
which does not make the mesh tend to `0`. It transfers from `t4_step` because
`(squeeze b).trans S.Φ '' zone k = S.Φ '' (squeeze b '' zone k) ⊆ S.Φ '' zone k`
(`squeeze_image_zone_subset`).

## 3. Item 3: the tree — proved

* `branchNext S c i` (new auxiliary definition): the stage chosen by `t4_step_branch` from `S` with
  bit `c` and `ε = 1/2^i`. `tstageTree b 0` is the base stage of `T4.lean`
  (`exists_t4_base`); `tstageTree b (i+1) = branchNext (tstageTree b i) (b i) i`. The auxiliary
  definition makes `tstageTree_prefix` a plain rewrite. Rewriting directly under the
  `Classical.choose` gives a motive that is not type correct.
* `tstageTree_prefix`: induction on `i`.
* **Factoring of `exists_homeomorph_tN`.** `TStep S S' ε` bundles the six clauses of `t4_step`.
  For any `T : ℕ → TStage M` with `(T 0).Φ = refl`, base chain mesh `< 1`, and
  `TStep (T i) (T (i+1)) (1/2^i)` for all `i`, the section `Generic` of `Thm5.lean` proves
  `gzone_diam`, `glink_diam`, `gC_diam`, `isCompact_gN`, `gchain_meets` and
  `exists_homeomorph_gN : Nonempty (M ≃ₜ gN T)`. These are line-for-line the proofs of
  `tzone_diam` … `exists_homeomorph_tN` in `T4.lean`, with `tstage_spec i` replaced by the
  hypothesis. `T4.lean` was not refactored: the commission allowed it, but it was not needed.
  `exists_homeomorph_tN` and its statement are unchanged.
* `tstageTree_tstep`: the tree satisfies `TStep`, using `squeeze_image_stdRect_subset` to weaken
  the squeezed inclusion to the plain one.
* `exists_homeomorph_tNb` is `exists_homeomorph_gN` applied to the tree. `isContinuum_tNb` takes
  compactness from `isCompact_gN` and connectedness as the image of `M`, as in `theorem4_of`.

## 4. Item 4: `tNb_disjoint` — proved

Route as commissioned. `i := Nat.find` of the first differing bit. `tstageTree_prefix` makes the
level-`i` stages equal. A common point lies in a level-`(i+1)` link of each branch, hence in
`S.Φ '' (squeeze (b i) '' stdRect s)` and `S.Φ '' (squeeze (b' i) '' stdRect s')`
(`tstageTree_squeeze`). Injectivity of `S.Φ` and `squeeze_disjoint` (in either order) then give a
contradiction.

## 5. Item 5: Theorem 5 — proved

* `theorem5_1951`: `W := tNb`, as stated.
* `theorem5_1951_uncountable`: `𝒲 := range W`. `W` is injective, since the sets are disjoint and
  nonempty (continua are connected, hence nonempty). If `range W` were countable, its preimage
  `univ` under the injective `W` would be countable (`Set.Countable.preimage`,
  `Set.countable_univ_iff`), so `ℕ → Bool` would be countable. That contradicts
  `not_countable_nat_bool`, which is proved from `Cardinal.mk_le_aleph0_iff`, `Cardinal.mk_pi`,
  `Cardinal.mk_fintype` and `Cardinal.cantor` (`ℵ₀ < 2^ℵ₀`).

## 6. Audit

* `axioms.txt` has **237 lines** (235 + 2). The diff against `axioms-before-batch107.txt` is
  exactly the two new lines. `sorryAx` appears in exactly **9** lines, as before.
* All 13 declarations in `axioms-batch107.txt`, including the refutation
  `not_squeeze_stdRect_subset`, depend only on `[propext, Classical.choice, Quot.sound]`. The
  refutation is not added to the `Refutations` group of `Axioms.lean`, because the commission
  allows edits to the Duke group only. If it should be listed there, adding it would make
  `axioms.txt` 238 lines.

## 7. Ledger notes (for `LEDGER.md`; not edited)

1. *Moore [10] replaced.* Bing's one-sentence proof is replaced by the branching Theorem-4
   construction. Steps the sentence hides beyond Moore's theorem:
   * the planar copy must be built so that the `ε`-chains of rectangle interiors can be split;
     here this is the squeeze into two strips;
   * the slowness/zone estimate must survive the squeeze, which it does because the squeezes
     preserve zones;
   * the homeomorphism argument must apply uniformly to every branch (the factored
     `exists_homeomorph_gN`);
   * uncountability needs injectivity of `W`, which comes from disjointness plus nonemptiness.
2. *Skeleton slip.* `squeeze_stdRect_subset` (with closure) is false. The squeezes do not shrink in
   `x`. The construction uses only the version without closure.

## 8. Not attempted

The five open targets.
