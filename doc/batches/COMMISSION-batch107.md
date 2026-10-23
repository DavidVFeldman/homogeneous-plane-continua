# Commission: batch 107 — Duke 1951 Theorem 5: uncountably many disjoint plane copies

**Go!** Runs on top of the batch-106 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch107.md` — this text (also pasted into the prompt);
* `Thm5.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Thm5.lean` and add
  `import HPC.Plane.Thm5` at the end of the root `HPC.lean`. No existing file is to be edited,
  except: `Axioms.lean` (Duke group) and `axioms.txt`; and `T4.lean` may be *refactored without
  changing any statement* if `exists_homeomorph_tN` has to be generalized (item 3) — in that
  case the old theorem stays, proved from the general one, and the report says so. Shapes may be
  adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 106

Audited: Theorem 12 (B ⇒ A), Theorem 13 in both forms, the unnumbered "two end points" claim and
its opposite-end-points form, all proved; 235 declarations, `sorryAx` in 9. Two ledger notes to
carry forward: (i) the formal Theorem 12 is for snake-like `M` — Bing's statement in §5 is for an
arbitrary compact continuum and his proof through [4] does not use snake-likeness; the general
case reduces to [4]'s Theorem 5 ("for `p` in a nondegenerate continuum `M'` there is `q ≠ p` such
that the union of the continua in `M' − q` containing `p` is dense in `M'`"), which is not
available (the paper is requested); (ii) Bing's "Theorems 10, 11, and 12" for Theorem 13 should
read "10 and 12".

## 1. The text (p. 655)

**Theorem 5.** *If `M` is a snake-like continuum, there is an uncountable collection `W` of
mutually exclusive continua in the plane such that each element of `W` is homeomorphic with `M`.*

*Proof.* "The planar continuum we described in Theorem 4 which was homeomorphic with `M` had the
property that for each positive number `ε`, it is covered by an `ε`-chain whose elements are the
interiors of rectangles. Hence, it follows from Theorem 1 of [10] that there is an uncountable
collection of mutually exclusive plane continua each homeomorphic with `M`."

[10] is R. L. Moore (not available). Replacement: run the construction of Theorem 4 along a
binary tree, as the skeleton's header describes. Bing's hypothesis "covered by `ε`-chains of
rectangle interiors" is exactly what the tree uses: the squeezes are affine maps of the plane
preserving each standard rectangle, so each branch is again a Theorem-4 construction.

## 2. Items

1. **Squeezes** (`squeeze`, `squeeze_stdRect_subset`, `squeeze_disjoint`). Affine homeomorphisms
   of `Pt = ℝ × ℝ`; `squeeze false` sends `y` to `(y + 1/2)/3 ∈ (1/6, 1/2)`,
   `squeeze true` to `(y + 7/4)/3 ∈ (7/12, 11/12)`; both fix `x`. The images of `stdRect j` have
   closures inside `stdRect j`, and the lower image of any rectangle misses the upper image of
   any rectangle (disjoint `y`-ranges).
2. **Branching step** (`t4_step_branch`). Compose `S.Φ` with `squeeze b` to get the stage
   `⟨S.m, S.C, (squeeze b).trans S.Φ, …⟩`, whose tame chain is `S.Φ '' (squeeze b '' stdRect j)`,
   then apply `t4_step` to it. Every clause of `t4_step` transfers; the new inclusion is the
   second clause. (The zone clause of `t4_step` — `diam ≤ ε ∨ ⊆ S.Φ '' zone k` — is dropped from
   the skeleton's statement; if the homeomorphism argument of item 3 needs it, keep it and
   record.)
3. **The tree** (`tstageTree`, `tstageTree_prefix`, `tNb`, `isContinuum_tNb`,
   `exists_homeomorph_tNb`). Define the stages by recursion on `i` with the bit `b i` and
   `ε = 8 / 2^i` as in `tstage`; prefix-dependence by induction. `exists_homeomorph_tN` is proved
   for the specific sequence `tstage`; its argument (nested closures, surjective block maps,
   mesh → 0 on both sides, then Bing 1948 Theorem 11 `MatchingCovers.exists_homeomorph`) applies
   to any sequence of stages with the `t4_step` properties. Factor it as a lemma over such a
   sequence (the refactoring permitted above) and apply it to `tstageTree b`.
4. **Disjointness** (`tNb_disjoint`). Let `i` be the least index with `b i ≠ b' i`. By
   `tstageTree_prefix` the stages at level `i` agree, say `S`; the level-`(i+1)` tame chains lie in
   `S.Φ '' (squeeze (b i) '' stdRect _)` and `S.Φ '' (squeeze (b' i) '' stdRect _)` respectively,
   which are disjoint by `squeeze_disjoint` and injectivity of `S.Φ`; `tNb b` lies in the union
   of its level-`(i+1)` chain.
5. **Theorem 5** (`theorem5_1951`, `theorem5_1951_uncountable`): `W := tNb`; uncountability of
   `range W` from injectivity (disjoint nonempty sets) and `Cardinal.not_countable_of …` for
   `ℕ → Bool` (Mathlib: `Cantor`/`not_countable` for `ℕ → Bool`; state what is used).

Report each item *proved / refuted / open with the obstruction stated*; refutations first;
record any place where Bing's one-sentence proof hides a step beyond Moore's theorem.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch107.txt`; `axioms.txt` regenerated (expected 237
   lines, `sorryAx` in 9).
2. Report: first line names the commission read; items in order; the refactoring of `T4.lean`, if
   any, with the statement-equality check.
3. Not attempted: the five open targets.

## 4. Next

The density lemma `exists_tame_chain_near` in the plane: a simple polygonal arc Hausdorff-near
any plane continuum (tracing a spanning tree of the grid squares meeting it) and a tame chain
around a simple polygonal arc.
