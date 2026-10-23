# Commission: batch 115 — Bing 1948, Theorem 14: the alternating construction with the position of `R` carried

**Go!** Runs on top of the batch-114 delivery. Three files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch115.md` — this text (also pasted into the prompt);
* `Thm14.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/PseudoArc/Thm14.lean`
  and add `import HPC.PseudoArc.Thm14` at the end of the root `HPC.lean`. Existing files to be
  edited only if the last item is proved: `HPC/PseudoArc/Theorem14.lean` (delete the open
  `theorem14` with its `-- OPEN` marker and `theorem15`, which the new file restates under the
  same names, `HPC.Description.theorem14`, `HPC.Description.theorem15`, with proofs — `theorem15`
  by `theorem15_of_theorem14` as now); `Axioms.lean`/`axioms.txt` (both out of the open groups into
  the Bing 1948 group); `OPEN.md` (item 3 closed; other numbers unchanged); `README.md` (one line
  if Theorem 14 or 15 is mentioned as open). If the last item is not proved, nothing moves;
* `lehner1961.pdf` — for reference (p. 376), not needed for the work.

The report names the commission read in its first line.

## 0. On batch 114

Audited: every item proved, no refutation; `sorryAx` in 4. The simplifications over Lehner (no
`H_2`, `E_2`; two steps of Theorem 13 instead of a second description; the minimal containing
index; `t_1 = s_1 + 2`) and the eleven ledger notes are accepted. One of them matters here: the
construction's first blocks and the following links of `G` up to `g_{y_1}` all lie in links of the
`ε`-chain `E` of `W` — this batch uses that.

## 1. The route

Bing's proof of Theorem 14 (COMMISSION-batch83.md §2 transcribes it) is the alternating
construction of Theorem 12 run on two covering descriptions, with Theorem 5 applied three times
per half-step on the following side, on the stretches `P → R`, `R → A` and `A → Q` of a deep
level, `A` being a point beyond `R` where the level has come back into the first link of the
coarse chain. Batch 83 found two unproved assertions in the sketch: that such a point `A` exists
with the stretch `P → A` lying inside the coarse covering part (`X_{1,j}(P_1, A) ⊆
Y_{1,1}(P_1, R_1)`, closure of `x(1,j)_A` in `y(1,1)_{P_1}`), and that the finer covering part
refines the coarser one (`Y_{2,2}(P_2, R_2)` inside `Y_{2,1}(P_2, R_2)`). Neither holds for an
arbitrary covering description. Both hold for the description Lehner's construction produces,
because its covering part, and the links after it up to the return into `f_2 ⊆ e_1`, are made of
links of an `ε`-chain of `W` — they lie within `ε` of `W`, and `e_1` lies within `ε` of `P`.
Since the coarse covering part is an open set containing the compact `W`, and the coarse first
link an open set containing `P`, the fine ones lie inside them once `ε` is small.

So: (i) strengthen the covering step to record tightness and the return point (`CoveringStepA`),
prove it from Lehner's construction, and carry it to every level (`exists_description_coveringA`,
through a variant of `exists_description_of_steps` whose carried property may depend on the
level `L` of the step); (ii) show that a tight fine level refines the coarse chain by a pattern
that tracks the `R`-indices and stays `≤ ρ` on the covering part (`exists_trackedPattern_of_refines`);
(iii) the three-piece follower (`exists_tracked_follower`): Theorem 5 three times, with the
tracked pattern's value constraints met by tightness; (iv) the tracked rungs and Theorem 11 with
its tracking clause (`TRung`, `exists_homeomorph_tracked`); (v) `theorem14`, `theorem15`.

Theorem 5 is `Theorem5Statement` (levels `0`, `1` and a deep `j` of a description, with the
value constraint `h ≤ x t ≤ k`, the end links' closures in `d(1)_h`, `d(1)_k`, disjoint, and the
clause that no interior link of the result meets the end links `d(2)_u ∪ d(2)_v`). To apply it
with the coarse chain `C = Δ.D lv` and a deeper level `Δ.D a` in the roles of levels `0` and `1`,
a *thinned description* is needed (levels `Δ.D lv, Δ.D a, Δ.D (a+1), …`): crookedness of `Δ.D a`
in `Δ.D lv` is `isCrookedIn'_of_refines` with Theorem 1 as in batch 114, closures and mesh by
transitivity. If the repository already has such a construction (`Description.shift` is the
tail; look for a thinning), use it; otherwise build it and record it.

## 2. Items

1. **The `A`-covering description** (`CoversUpToA`, `CoveringStepA`, `covering_stepA`,
   `exists_description_of_steps'`, `exists_description_coveringA`). In `lehner_lemma3_two`'s
   construction, take the window condition with four links (every link of `F` within three links
   of a link meeting `W` lies in a link of `E`), so that `F(1,4)` lies in one link of `E`, which
   is `e_1` as it contains `P'`; then `g_{y_1} ⊆ f_2 ⊆ e_1 ⊆ ball P' ε`. The blocks `d_1 … d_{m_1}`
   lie in links of `E`, and the links `g_{z_1+1}, …, g_{y_1}` lie in links of `F(1, t_1 − 1)`,
   hence in links of `E` (`y_1 < w_1`); every link of `E` meets `W` and has diameter `< ε`; so the
   span up to `a := m_1 + (y_1 − z_1)` lies in `thickening ε W`. With `ε ≤ 1/(L+1)` this is
   `CoversUpToA … (1/(L+1))`. If `LehnerCore.indices` does not expose `y_1`, extend it (the file
   may be edited for that, recorded). `exists_description_of_steps'`: the proof of
   `exists_description_of_steps` with `G L N F`; the level `i` is produced by the step at
   `L = lev i ≥ i`. Then `exists_description_coveringA` with `G L N F := CoversUpToA F P' R W
   (1/(L+1))` and `1/(L+1) ≤ 1/(i+1)` (thickenings and balls are monotone in the radius).
2. **Tracked patterns** (`IsTrackedPattern`, `Carries`, `exists_trackedPattern_of_refines`).
   `Chain.refineIdx` gives some pattern; modify it on the links of `D(0..ρ_D)`: such a link lies
   in `thickening η W ⊆ C.span 0 ρ` and in `C.link j`; if `j > ρ` then `j = ρ + 1` (chain) and the
   link lies in `C.link (ρ+1) ∩ C.span 0 ρ ⊆ C.link ρ`; so assign `ρ`. The link of `R` is assigned
   `ρ` by `hRlink`. Check the modified map is still a pattern (consecutive values differ by `≤ 1`:
   two meeting links of `D` lie in meeting links of `C`; the modification only moves values from
   `ρ + 1` down to `ρ`, and a neighbour's value is in `{ρ, ρ ± 1}` either way — verify the case
   where a neighbour was assigned `ρ + 2`: impossible, since it meets a link inside `C.link ρ`).
   `Carries D P R W ρ_D` from `CoversUpToA`.
3. **The three-piece follower** (`exists_tracked_follower`). Choose the deep level `D_a` (`a >
   lv`) with: `1/(a+1)` so small that `thickening (1/(a+1)) W ⊆ C.span 0 ρ`,
   `ball P (1/(a+1)) ⊆ C.link 0` with closure, and the links of `D_a` containing `R` have closure
   inside `C.link ρ` (mesh small, `R` interior to the open `C.link ρ`); let `ρ_a ≤ α_a` be the
   indices of `CoversUpToA (Δ.D a)`. Then apply `Theorem5Statement` to the thinned description
   `(C, D_a, …)` three times, at a common deep level `b` (take the maximum of the three `j`s,
   then the `IsConsolidationOn` conclusions are for `Δ.D b` after re-deriving at the deeper level,
   or apply the three with the same `w` and take `j := max` if the statement allows; say what was
   done):
   * stretch `u = 0, v = ρ_a`, `h = 0, k = ρ`, pattern `x|[0, ρ']` (an `IsPatternFromTo` from `0`
     to `ρ` with values in `[0, ρ]` by `IsTrackedPattern`); links of `D_a(0..ρ_a)` lie in links of
     `C` with index `≤ ρ` (tightness and the overlap argument of item 2); closures of the end links
     in `C.link 0`, `C.link ρ`, disjoint (`ρ ≥ 1`; if `ρ = 0` then `R ∈ C.link 0` — exclude by
     choosing the base rung's mesh below `dist P R`, so that `R ∉ C.link 0` and `ρ ≥ 1`; likewise
     `ρ' ≥ 1`);
   * stretch `u = ρ_a, v = α_a`, `h = 0, k = ρ`, pattern `t ↦ x (ρ' − t)` on `ρ' + 1` links (from
     `ρ` to `0`, values in `[0, ρ]`), the end links' closures in `C.link ρ` and `C.link 0`;
   * stretch `u = α_a, v = last`, `h = 0, k = N − 1`, pattern `x` (from `0` to `N − 1`).
   Assemble `E` with `N'` links: `E n := E_1 n ∪ E_2 (ρ' − n) ∪ E_3 n` for `n ≤ ρ'` and `E_3 n`
   for `n > ρ'` (with `E_1`, `E_2` of `ρ' + 1` links and `E_3` of `N'` links; indices as `Fin`).
   Prove: links open; `E` is a chain (within each piece by Theorem 5; across pieces: two links of
   `D_b` from different stretches meet only if they lie in the same or adjacent links of `D_a`,
   hence one of them in a junction link of `D_a` (`ρ_a` or `α_a`), and Theorem 5's end clause puts
   the links of `D_b` inside a junction link into the end link of the piece — index `ρ'` for the
   first junction on both sides, index `0` for the second on both sides; stretches `1` and `3` do
   not meet when `α_a ≥ ρ_a + 2`, which holds once `C.link 0` and `C.link ρ` are disjoint);
   `E.IsFrom P Q`; `E.IsConsolidationOf (Δ.D b)`; `E.FollowsPattern x C`; `Carries E P R W ρ'`
   (`W ⊆ D_b(0..ρ_b)* ⊆ D_a(0..ρ_a)*`-links of index `≤ ρ_a` by tightness at level `b`, all
   consolidated into `E_1`; `R` only in the junction link `ρ'`).
4. **Tracked rungs** (`TRung`, `TRung.exists_base`, `TRung.exists_next`,
   `exists_homeomorph_tracked`): `Rung.exists_base`, `Rung.exists_next`, and the body of
   `Description.exists_homeomorph` with `TRung`; the half-step is item 2 on the consolidated side
   (its refining level `D_c` chosen deep enough for `hthick` and `hRlink`) and item 3 on the level
   side; the new `ρ'` is the `R`-index of `D_c`. The final homeomorphism tracks `R` by the index
   sequence `k ↦ ρ_k` (`Tracks₁`, `Tracks₂`: `R_i ∈ C_i.link ρ_k` at every rung).
5. **`theorem14`, `theorem15`.** For each `i`, `W_i := ` an irreducible subcontinuum between
   `P_i` and `R_i` (`exists_irreducible` in a proper subcontinuum containing both, which exists
   since `R_i ∈ composant P_i`), `exists_description_coveringA` for `Δ` at `(P_i, Q_i, R_i, W_i)`,
   `exists_homeomorph_tracked`, and the transport along `Δ'.M = Δ.M` (as `theorem15_of_theorem14`
   does with `homImage`).

Report each item *proved / refuted / open with the obstruction stated*; refutations first; the
ledger: every assertion of Bing's sketch that needed Lehner's tightness, and every step of the
three-piece assembly that the sketch leaves out. Item 3 is the long one; if it is not finished,
leave it `sorry` with the partial results, prove 4–5 from it, do not move the open target, and
state the obstruction.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch115.txt`; `axioms.txt` regenerated (`sorryAx` in 2
   if everything is proved: `theorem3_end`, `fugate_cor1`).
2. Report: first line names the commission read; items in order; the ledger; the thinning
   construction, if new.
3. Not attempted: `theorem3_end`, `fugate_cor1`.

## 4. Next

Housekeeping (prose remnants in `BandN.lean`, `Most51.lean`, `Most51Geom.lean`; README batch
count); then Duke Theorems 6–7 on the polygonal interface, or Fugate's Corollary 1.
