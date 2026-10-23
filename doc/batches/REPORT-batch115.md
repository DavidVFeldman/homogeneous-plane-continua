Commission read: COMMISSION-batch115.md (batch 115 — Bing 1948, Theorem 14: the alternating construction with the position of `R` carried).

# Report, batch 115

**Outcome.** Every item is proved; nothing is refuted. `HPC.Description.theorem14` (Bing 1948,
Theorem 14) and `HPC.Description.theorem15` (Theorem 15) are proved, with their statements unchanged,
and have moved from `HPC/PseudoArc/Theorem14.lean` to `HPC/PseudoArc/Thm14.lean`. OPEN.md item 3 is
closed. `axioms.txt` is regenerated (316 lines, up from 309); `sorryAx` appears in exactly two lines, `theorem3_end` and
`fugate_cor1`. `theorem3_end` and `fugate_cor1` were not attempted.

## Refutations

None. One skeleton field did not typecheck (`TRung.follow`, below); it was replaced by what the
construction actually uses.

## Items

1. **The `A`-covering description — proved.** (`CoversUpToA`, `CoveringStepA`, `covering_stepA`,
   `exists_description_of_steps'`, `exists_description_coveringA`.)
   `covering_stepA` is `lehner_lemma3_twoA` (`Lehner.lean`), which is `lehner_lemma3_two`'s proof
   extended; `lehner_lemma3_two` (statement unchanged) is now derived from it. Instead of a
   four-link window, the proof shows directly that the second link `f_2` of Lehner's `F` lies in the
   link `e_1` of `E` containing `P'`: `f_2` is within `3/(L_1+1)` of `P'`, below the Lebesgue number
   `l_1` of `E` on `W`, so `f_2 ⊆ ball P' l_1 ⊆` some link of `E`, which contains `P'` and so is
   `e_1`. `LehnerCore.indices` now takes that fact as a hypothesis and returns Lehner's `y_1`
   (`z_1 < y_1 < w_1`, `g_{y_1} ⊆ f_2 ⊆ e_1`, every link of `G` up to `y_1` in a link of `E`).
   `blocks` also returns the shape of the chain after `z_1` (the block of `g_l`, `l > z_1`, is `g_l`
   alone, at index `m − 1 + (l − z_1)`) and that `R` lies in block `m − 1`. `core` combines these
   into the index `a` of the block of `g_{y_1}`. The span up to `a` consists of links lying in links
   of `E`, each meeting `W` with diameter `< ε ≤ 1/(L+1)`; the link `a` lies in `e_1 ∋ P'`.
   `exists_description_of_steps'` repeats the proof of `exists_description_of_steps` and records
   `L = lev i ≥ i`. `exists_description_coveringA` uses `1/(L+1) ≤ 1/(i+1)`.

2. **Tracked patterns — proved.** (`IsTrackedPattern`, `Carries`,
   `exists_trackedPattern_of_refines`.) The key step is a general lemma,
   `Chain.exists_link_le_of_subset_span`: a set lying in `C.link j` and in `C.span a ρ` lies in a
   link of index `≤ ρ`. If `j > ρ`, each of its points lies in `C.link j` and in some link `≤ ρ`,
   which then has to be `ρ`. The pattern is `ρ` at the `R`-index `b` of `D`, the index from that
   lemma before `b`, and any refining index after `b`. A map like this is a pattern whenever `D`
   follows it and both chains run from `P` to `Q`. Shape change: the hypothesis `0 < η` was unused
   and is removed.

3. **The three-piece follower — proved.** (`exists_tracked_follower`.) See *Theorem 5 with an
   arbitrary coarse chain* and *The gluing* below. A deep level `D_a` (`a > lv`) is chosen with
   `ε_a` and `1/(a+1)` below a quarter of `min(r_0, r_1, r_2, δ_1, dist P R, dist P Q)`. Here
   `ball P r_0 ⊆ c_0`, `ball R r_1 ⊆ c_ρ`, `ball Q r_2 ⊆ c_{N−1}`, and
   `thickening δ_1 W ⊆ C.span 0 ρ` (this needs `W` compact). From this:
   * the closures of `d_0`, `d_{ρ_a}`, `d_α`, `d_{last}` lie in small closed balls about `P`, `R`,
     `P`, `Q`, and so in `c_0`, `c_ρ`, `c_0`, `c_{N−1}`, pairwise disjoint as needed;
   * `ρ_a ≥ 1`, `ρ_a + 2 ≤ α`, `α + 1 < n_a`, all by distances;
   * every link of `D_a(0..α)` lies in a link of `C` of index `≤ ρ` (tightness, item 2's lemma).

   Theorem 5 (`theorem5_gen`) is applied three times:
   * to `C` on `D_a(0..ρ_a)` with `x|[0, ρ']`;
   * to the *reversed* chain `C.reverse` on `D_a(ρ_a..α)` with `t ↦ rev (x (ρ' − t))`, a pattern
     from `rev ρ` up to `rev 0`;
   * to `C` on `D_a(α..last)` with `x`.

   Each application holds for every deep enough level, so all three use one common level `j > a`.
   `Chain.threePiece` glues the results. Shape changes:
   * hypotheses `IsCompact W` and `0 < ρ` are added;
   * the conclusion is stated as `Δ.TCanFollow R W lv (Δ.D lv) ρ`, which is the skeleton's
     conclusion quantified over `N'`, `x`, `ρ'`.

4. **Tracked rungs — proved.** (`TRung`, `TRung.exists_base`, `TRung.exists_next`,
   `exists_homeomorph_tracked`.)
   * Shape change: the skeleton's field `follow : (C₁ = Δ₁.D lv₁ ∧ …) ∨ …` does not typecheck.
     `C₁ : Chain X N` and `Δ₁.D lv₁ : Chain X (Δ₁.n lv₁)` have different types. It is replaced by
     `Δ₁.TCanFollow R₁ W₁ lv₁ C₁ ρ` (resp. side 2), which is what the construction uses of the
     following side. It is supplied by item 3 whenever the side is a level.
   * The refining half-step is factored out as `exists_tracked_refinement`. It takes a level `D_c`
     deep enough that `ε_c ≤ δ`, `ε_c < r_R` (where `ball R r_R ⊆ C.link ρ`) and `ε_c < dist P R`,
     and that `thickening (1/(c+1)) W ⊆ C.span 0 ρ`. It then applies item 2. The new `R`-index is
     positive (`Carries.pos_of_lt`).
   * Base rung (the commission asks which pattern is used): the follower is applied to `Δ₂` with an
     explicit pattern, not the identity.
     - Take a level `b` of `Δ₂` with `ε_b < dist P₂ R₂`, so that `ρ_b ≥ 1`.
     - Take a level `a` of `Δ₁` with `ε_a < 1/2`, `ε_a < dist P₁ R₁ / (ρ_b + 2)` and
       `ε_a < dist R₁ Q₁ / (n_b + 1)`. This gives `ρ_a > ρ_b` and `n_a − ρ_a > n_b`, by the chain
       distance bound.
     - The pattern is `y t = min t ρ_b` for `t ≤ ρ_a` and `min (ρ_b + t − ρ_a) (n_b − 1)` after.
       It tracks `ρ_a ↦ ρ_b`.
   * The homeomorphism is `Description.exists_homeomorph`'s construction on `TRung`s. `R` is tracked
     by the index sequence `k ↦ ρ_k` through the tracking clause of `MatchingCovers.exists_homeomorph`.
   * Shape change: hypotheses `P_i ≠ R_i`, `R₁ ≠ Q₁` and `IsCompact W_i` are added. All of them are
     available in Theorem 14.

5. **`theorem14`, `theorem15` — proved.** `W_i` comes from `exists_irreducible` inside a proper
   subcontinuum through `P_i` and `R_i`. `P_i ≠ Q_i` holds because `{P_i}` is a proper subcontinuum
   (`R_i ≠ P_i` lies in `M`), and `R_i ≠ Q_i` because of the composants. Then come the two
   `A`-covering descriptions and `exists_homeomorph_tracked`. The result is transported along
   `Δ'_i.M = Δ.M` by `Homeomorph.setCongr`. `theorem15` is `theorem15_of_theorem14` with
   `theorem14`, as before.

## Theorem 5 with an arbitrary coarse chain (replacing the thinned description)

The commission asked for a *thinned description* (`C, D_a, D_{a+1}, …`). It is not needed and was
not built. The proof of `theorem5_of` never uses that Bing's `D_1` is a level of the description, or
that it runs from `P` to `Q`. It uses only that `D_1` is a chain of open sets into which the stretch
of `D_2` fits, and whose links `h`, `k` contain the closures of `d(2)_u`, `d(2)_v`.
`Description.theorem5_gen` (`HPC/PseudoArc/T5Gen.lean`) is that proof with the coarse chain `C`
arbitrary and `D_2` any level `Δ.D i`. It differs from Theorem 5 in three ways:

* it holds for every deep enough level (`∀ᶠ j in atTop`), so three applications can share one level;
* it allows `C` to be reversed. This is needed because the stretch `R → A` runs from `c_ρ` down to
  `c_0`, and `IsPatternFromTo` requires `h ≤ k`;
* it records two *end clauses*: the links of `D_j` in the stretch that meet `d(2)_u` lie in the first
  link of `E`, and those that meet `d(2)_v` lie in the last.

The end clauses are read off the construction of `T5.assemble`, whose conclusion was extended for
this (`T5Chain.lean`): near `d(2)_u` the lift is `0`, near `d(2)_v` it is `N + 1`. Theorem 5's own
clause (interior links miss `d(2)_u ∪ d(2)_v`) only places such links in *an* end link. When
`ρ = 1`, `c_0` and `c_ρ` meet, and the clause alone does not decide which end.

## The gluing (`Chain.threePiece`, `HPC/PseudoArc/T14Glue.lean`)

Link `n` of `E` is `E_3(n) ∪ E_1(n) ∪ E_2(ρ' − n)` for `n ≤ ρ'`, and `E_3(n)` beyond.

* **Cross-intersections.** A point of a link of `E_1` and of a link of `E_2` lies in `d_{ρ_a}`: the
  two links of `D_j` through it lie in links `s ≤ ρ_a ≤ s'` of `D_a` that meet. By the end clauses it
  then lies in `E_1(ρ')` and in `E_2(0)`, so both indices are in `{ρ' − 1, ρ'}`. In the same way,
  `E_2` meets `E_3` only in `d_α`, where both indices are `≤ 1`. `E_1` and `E_3` do not meet, because
  `α ≥ ρ_a + 2`.
* **`E` is from `P` to `Q`.**
  - `P` lies in `E_1(0)` (end clause at `d_0`).
  - `P` lies in no other link: interior links of `E_1` miss `d_0`; `E_1(ρ') ⊆ c_ρ ∌ P`; and `P`
    lies in no link of `D_a` in the other two stretches.
  - For `Q`, the same argument uses `E_3` and `c_0 ∌ Q`.
* **`E` carries `(P, R, W)` at `ρ'`.**
  - `R` lies in `E_1(ρ')` or `E_2(0)`.
  - `R` is not in `E_1(0) ⊆ c_0` or `E_2(ρ') ⊆ c_0` (since `R ∉ c_0`), not in interior links (end
    clauses), and not in `E_3`.
  - `W` lies in the span of `D_a(0..ρ_a)`. The link of `D_j` through a point of `W` lies in a link of
    `D_a` of index `≤ ρ_a + 1 ≤ α`, so it is in the first two stretches, and so in links `≤ ρ'`.
* **The rest.** `E` follows `x`, and `E` is a consolidation of `D_j`.

## Ledger

**Assertions of Bing's sketch that needed Lehner's tightness** (with the return point):

1. The return point `A` exists, and `X_{1,j}(P_1, A)` lies in `Y_{1,1}(P_1, R_1)`. Here this is the
   index `α` of `CoversUpToA`, with `D_a(0..α)` inside `thickening (1/(a+1)) W ⊆ C.span 0 ρ`.
   Without tightness, a deep level's stretch `P → A` can leave `C(0..ρ)`.
2. The closure of `x(1,j)_A` lies in `y(1,1)_{P_1}`: `d_α ⊆ ball P (1/(a+1))`.
3. The finer covering part refines the coarser (`Y_{2,2}(P_2, R_2) ⊆ Y_{2,1}(P_2, R_2)`). This is
   tightness at the refining level (`hthick` in `exists_trackedPattern_of_refines`), together with
   the overlap lemma `exists_link_le_of_subset_span`.
4. The patterns of the two sides track the `R`-indices with values `≤ ρ` on the covering part. This
   is `IsTrackedPattern`, obtained from 3.
5. The stretch `R → A` can follow the reversed covering pattern within Theorem 5's value constraints,
   because every link of `D_a(ρ_a..α)` lies in a link of `C` of index `≤ ρ` (from 1).

**Steps of the three-piece assembly that the sketch leaves out:**

1. Theorem 5 is needed with a *decreasing* pattern on the stretch `R → A`. Reversing the coarse
   chain only (`C.reverse`) reduces it to the increasing case. This is possible because the proof
   does not need the coarse chain to run from `P` to `Q`.
2. The three applications of Theorem 5 must land at a common level. Theorem 5 holds at every deep
   enough level.
3. The links of `D_j` meeting a junction link of `D_a` lie in the correct end link of each piece.
   This is a clause of Theorem 5's construction, not of its statement.
4. Gluing: `E_1(n) ∪ E_2(ρ' − n) ∪ E_3(n)` is a chain. Cross-intersections happen only at the
   junction links. The stretches `P → R` and `A → Q` are disjoint, because `α ≥ ρ_a + 2`.
5. `E` runs from `P` to `Q`, and `P`, `R` occupy only the links `0` and `ρ'` of `E(0..ρ')`. This uses
   `R ∉ c_0` (that is, `ρ ≥ 1`), `P ∉ c_ρ` and `Q ∉ c_0`.
6. `W` lies in `E(0..ρ')`. This uses `W ⊆ D_a(0..ρ_a)` and the adjacency in `D_a`.
7. The deep level's junction links: `ρ_a ≥ 1`, `ρ_a + 2 ≤ α < n_a − 1`. The closures of
   `d_0`, `d_{ρ_a}`, `d_α`, `d_{last}` lie in `c_0`, `c_ρ`, `c_0`, `c_{N−1}`, and the needed pairs are
   disjoint. All of this holds once `ε_a` and `1/(a+1)` are small compared with `dist P R`,
   `dist P Q` and the radii of balls about `P`, `R`, `Q` inside those links.
8. The base rung needs a pattern from a fine level of `Δ₁` to a coarse level of `Δ₂` tracking the
   `R`-indices. It exists once the fine level has more links before and after its `R`-link. This
   uses `P₁ ≠ R₁ ≠ Q₁` and the chain distance bound.
9. The new `R`-index of every rung is positive (mesh below `dist P R`). The follower needs this.

## Files

* **New:**
  - `HPC/PseudoArc/Thm14.lean`: the skeleton, all proved, with `theorem14` and `theorem15` moved
    here;
  - `HPC/PseudoArc/T5Gen.lean`: `theorem5_gen`;
  - `HPC/PseudoArc/T14Glue.lean`: `Chain.threePiece`.
* **Edited, statements of existing results unchanged:**
  - `HPC/PseudoArc/T5Chain.lean`: two conjuncts added to `T5.assemble`'s conclusion;
    `T5Main.lean` destructures them;
  - `HPC/PseudoArc/LehnerCore.lean`: `indices` takes one more hypothesis and returns `y_1`;
    `blocks` and `core` return more;
  - `HPC/PseudoArc/Lehner.lean`: `lehner_lemma3_twoA` added; `lehner_lemma3_two` is derived
    from it.
* **Commission edits:**
  - `HPC/PseudoArc/Theorem14.lean`: the open `theorem14` (with its `-- OPEN` marker) and
    `theorem15` are deleted, and a note is left in their place;
  - `HPC.lean`: `import HPC.PseudoArc.Thm14`;
  - `Axioms.lean` / `axioms.txt`: both statements are moved into the Bing 1948 group, and the new
    batch-115 results are added there; the group *Consequences of open targets* is now empty;
  - `OPEN.md`: item 3 closed; other numbers unchanged;
  - `README.md` does not mention Theorem 14 or 15 as open, so it is not edited.
* **Filed:**
  - the commission: `doc/batches/COMMISSION-batch115.md`;
  - the skeleton: `doc/batches/skeletons/Thm14.lean`;
  - the previous audit: `doc/batches/audits/axioms-before-batch115.txt`;
  - this batch's audit: `doc/batches/audits/axioms-batch115.txt`.

## Verification

`lake build HPC HPCArchive HPCCensus` succeeds. The only `sorry` warnings of the main build are the
two remaining open targets, `theorem3_end` (`HPC/Fold/Theorem4.lean`) and `fugate_cor1`. The new
files contain no `sorry`. `#print axioms` for the batch-115 statements is in
`doc/batches/audits/axioms-batch115.txt`: all depend only on `propext`, `Classical.choice` and
`Quot.sound`.
