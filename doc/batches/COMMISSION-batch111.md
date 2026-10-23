# Commission: batch 111 — housekeeping after the density lemma

**Go!** Runs on top of the batch-110 delivery. One file accompanies this commission:
`COMMISSION-batch111.md` (this text, also pasted into the prompt). No skeleton. This is a
housekeeping batch like 103 and 105: existing files *are* to be edited, exactly as listed; no
new mathematics except item 1(b), which is a one-line restatement. The report names the
commission read in its first line and lists every file touched.

## 0. On batch 110

Audited: every item proved, no refutation. The edge splice with the invariant (a′), (b), (c′),
length `L = 26N − 2`, the simplification in `squaresMeeting_connected` (one corner square
suffices), and the dropped unused hypotheses are all accepted. `theorem2_HIC_plane` and
`theorem2_1951_plane` are checked for every two-dimensional real inner product space; 280
declarations, `sorryAx` in 9.

## 1. The open lemma, restated in the form actually needed

(a) **Delete** `exists_tame_chain_near` (`HPC/Plane/Most51.lean`), together with its two
consequences `dense_pseudoArcs` and `theorem2_HIC` (the general-`E` statements proved from it).
Reason, for `LEDGER.md` §2 (deleted statements that are not refuted): it was the batch-90
skeleton's own intermediate, asking for a *homeomorphism of `E`* carrying the standard boxes
onto the links, which is more than `exists_pseudoArc_in_tameChain` uses (batch 109); the
batch-90 obstruction was an obstruction to that excess. `IsTameChain`, `GeomLemma`,
`exists_pseudoArc_in_tameChain`, `geomLemma'_of_geomLemma`, `dense_pseudoArcs_of`,
`theorem2_HIC_of` stay (proved). `HPC/Archive/Most51Geom.lean` stays in the archive; fix its
header if it names the deleted theorem.

(b) **Add**, in `HPC/Plane/LatticeCycle.lean` after the plane theorems, the open statement in the
weak form, marked `-- OPEN (see OPEN.md)`:

```lean
/-- **The density lemma in dimension `≥ 2`** (Bing 1951 (Pacific), §3, for Euclidean `n`-space
and Hilbert space). Proved for `finrank ℝ E = 2` (`geomLemma'_of_finrank_two`); open otherwise.
Expected route: a self-avoiding lattice cycle through the cubes meeting `g` in `ℤⁿ` (the splice
of `LatticeCycleAux.lean` with an `n`-cube loop that has a middle pair on each of the `2n` faces),
the band of `Band.lean` with a normal field that may twist along straight stretches; Hilbert
space by projecting `g` onto a finite-dimensional subspace within `ε`. -/
theorem geomLemma'_of_two_le_rank [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    GeomLemma' E := by
  sorry

theorem dense_pseudoArcs [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  dense_pseudoArcs_of' (geomLemma'_of_two_le_rank hdim)

theorem theorem2_HIC [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  theorem2_HIC_of' (geomLemma'_of_two_le_rank hdim)

theorem theorem2_1951 [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsSnakeLike (K.1 : Set E)} := ...
```

So the names `dense_pseudoArcs`, `theorem2_HIC` survive with the same statements, now through the
weak open lemma; `theorem2_1951` (Duke Theorem 2, general `E`) is new and conditional in the same
way. `sorryAx` count stays 9 (one open target replaced by one open target; three consequences
instead of two — say the exact count).

(c) **`OPEN.md` item 4** rewritten for `geomLemma'_of_two_le_rank`: statement; depends on it:
`dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951`; known: the plane case is proved
(`geomLemma'_of_finrank_two`, batches 109–110), with the route of (b) for dimension `≥ 3` and
Hilbert space; the batch-90 partial results in the archive; the former statement deleted (§2 of
the ledger).

## 2. Audit groups

* `Axioms.lean`: in the *Open targets* group replace `exists_tame_chain_near` by
  `geomLemma'_of_two_le_rank`; in *Consequences of open targets* list `dense_pseudoArcs`,
  `theorem2_HIC`, `theorem2_1951`. Move the four skeleton refutations
  `not_squeeze_stdRect_subset` (batch 107), `stripSet_zero_ne`, `stretchTri_subset_ball_false`,
  `stretchTri_subset_thickening_false` (batch 109) from wherever they are into the *Refutations
  (ledger certificates)* group. Regenerate `axioms.txt`; report the line count and the nine
  `sorryAx` lines by name.
* `LEDGER.md` §1: four entries for those skeleton refutations (what was claimed, why false, the
  certificate), marked as commission slips, not the sources'. §2: the three deleted statements
  of item 1(a).

## 3. Documentation

* `README.md`: the paper list — add to the Pacific line "Theorem 2 in the plane"; add a line for
  Bing 1948 (Amer. J. Math.) Theorem 5 and Corollary 2; add Duke Theorem 2 in the plane and
  Theorem 5; the batch count ("105 batches") updated to 111; the layout table's `doc/sources/`
  entry mentions the arcs paper. Keep the sentence that `axioms.txt` is the only claim.
* `doc/theorems-3-4-scheduling.md`: replace by the newest upload (`theorems-3-4-scheduling(16).md`
  if no newer one is uploaded with this commission; the copy uploaded with this commission is
  newer — use it), and **delete** the stray root copies `theorems-3-4-scheduling(15).md`,
  `theorems-3-4-scheduling(16).md`.
* `HPC/Plane/Most51.lean` header: update the batch-90 paragraph to say what is now proved and
  where (plane: `LatticeCycle.lean`; general: open `geomLemma'_of_two_le_rank`).

## 4. Deliverables

1. `lake build HPC` clean except the five `sorry` warnings (`theorem3_end`, `covering_step`,
   `theorem14`, `geomLemma'_of_two_le_rank`, `fugate_cor1`); `HPCArchive` and `HPCCensus` still
   build (say so, or what broke and was fixed).
2. `axioms-batch111.txt` for every declaration touched; `axioms.txt` regenerated.
3. Report: files touched, line counts, the `sorryAx` names.

## 5. Next

Either Duke Theorems 6–7 on a polygonal-Jordan-curve-theorem interface, or Theorem 2 in dimension
`≥ 3` and Hilbert space by the route of 1(b). To be decided.
